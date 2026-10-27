module

public import CFSG.RankThree.PartOne.S10.PlaneContract
import CFSG.RankThree.PartOne.S10.PlaneSemidirect
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
import CFSG.RankThree.PartOne.S10.FaithfulPlaneTwoActionOnPrimeGroup
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven

namespace PlaneQuotient

variable {B S D Q : Type} [Group B] [Group S] [Group D] [Group Q] [MulDistribMulAction B S]
  [MulDistribMulAction B Q] {β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D}

structure ActionQuotient (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D)
    (Q : Type) [Group Q] [MulDistribMulAction B Q] where
  π : S →* Q
  fn : Q →* MulAut D
  smul_map : ∀ (b : B) (s : S), π (b • s) = b • π s
  surj : Function.Surjective π
  fn_inj : Function.Injective fn
  fn_map : ∀ s : S, fn (π s) = β (SemidirectProduct.inl s)

namespace ActionQuotient

variable (𝒬 : ActionQuotient β Q)

noncomputable def barHom : (Q ⋊[MulDistribMulAction.toMulAut B Q] B) →* MulAut D :=
  SemidirectProduct.lift 𝒬.fn (β.comp SemidirectProduct.inr) fun b => by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨s, rfl⟩ := 𝒬.surj q
    change 𝒬.fn (b • 𝒬.π s) = β (SemidirectProduct.inr b) * 𝒬.fn (𝒬.π s) *
      (β (SemidirectProduct.inr b))⁻¹
    rw [← 𝒬.smul_map, 𝒬.fn_map, 𝒬.fn_map, ← PlaneSemidirect.conj_inr_inl b s, map_mul, map_mul,
      map_inv]

def proj : (S ⋊[MulDistribMulAction.toMulAut B S] B) →*
    (Q ⋊[MulDistribMulAction.toMulAut B Q] B) :=
  SemidirectProduct.map 𝒬.π (MonoidHom.id B) fun b => MonoidHom.ext fun s => 𝒬.smul_map b s

theorem barHom_inl (q : Q) : 𝒬.barHom (SemidirectProduct.inl q) = 𝒬.fn q :=
  SemidirectProduct.lift_inl _ _ _ q

theorem barHom_inr (b : B) : 𝒬.barHom (SemidirectProduct.inr b) = β (SemidirectProduct.inr b) :=
  SemidirectProduct.lift_inr _ _ _ b

theorem barHom_proj (k : S ⋊[MulDistribMulAction.toMulAut B S] B) : 𝒬.barHom (𝒬.proj k) = β k := by
  have h : 𝒬.barHom.comp 𝒬.proj = β := by
    refine SemidirectProduct.hom_ext (MonoidHom.ext fun s => ?_) (MonoidHom.ext fun b => ?_)
    · change 𝒬.barHom (𝒬.proj (SemidirectProduct.inl s)) = β (SemidirectProduct.inl s)
      rw [proj, SemidirectProduct.map_inl, barHom_inl, 𝒬.fn_map]
    · change 𝒬.barHom (𝒬.proj (SemidirectProduct.inr b)) = β (SemidirectProduct.inr b)
      rw [proj, SemidirectProduct.map_inr, barHom_inr]
      rfl
  exact DFunLike.congr_fun h k

theorem barHom_injective {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite B] [Finite Q]
    (hBp : IsPGroup p B) (hQ : IsPGroup 2 Q)
    (hfaith : ∀ c : B, (∀ q : Q, c • q = q) → c = 1) : Function.Injective 𝒬.barHom := by
  have hker : IsPGroup p 𝒬.barHom.ker := by
    refine hBp.of_injective (SemidirectProduct.rightHom.comp 𝒬.barHom.ker.subtype) ?_
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hx1
    have hx1' : SemidirectProduct.rightHom x = 1 := hx1
    have hx0 : x ∈ (SemidirectProduct.inl :
        Q →* Q ⋊[MulDistribMulAction.toMulAut B Q] B).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hx1'
    obtain ⟨q, rfl⟩ := hx0
    have hq : 𝒬.fn q = 1 := by
      rw [← barHom_inl]
      exact hx
    have hq1 : q = 1 := 𝒬.fn_inj (hq.trans (map_one 𝒬.fn).symm)
    subst hq1
    exact Subtype.ext (map_one _)
  have hbot := PlaneSemidirect.eq_bot_of_normal_isPGroup hp hp2 hBp hQ hfaith 𝒬.barHom.ker hker
  exact (MonoidHom.ker_eq_bot_iff _).mp hbot

theorem evenRank_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite B] [Finite S] [Finite D]
    [Finite Q] (hBp : IsPGroup p B) (hDp : IsPGroup p D) (hS : IsPGroup 2 S) (hQ : IsPGroup 2 Q) :
    evenRank (D ⋊[𝒬.barHom] (Q ⋊[MulDistribMulAction.toMulAut B Q] B)) ≤
      evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) := by
  have : Fact p.Prime := ⟨hp⟩
  let πG : (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) →*
      (D ⋊[𝒬.barHom] (Q ⋊[MulDistribMulAction.toMulAut B Q] B)) :=
    SemidirectProduct.map (MonoidHom.id D) 𝒬.proj fun k => MonoidHom.ext fun d => by
      change β k d = 𝒬.barHom (𝒬.proj k) d
      rw [barHom_proj]
  have hπG : Function.Surjective πG := by
    rintro ⟨d, ⟨q, b⟩⟩
    obtain ⟨s, rfl⟩ := 𝒬.surj q
    exact ⟨⟨d, ⟨s, b⟩⟩, rfl⟩
  let θ : S →* D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
    SemidirectProduct.inr.comp SemidirectProduct.inl
  have hker : πG.ker ≤ θ.range := by
    rintro ⟨d, ⟨s, b⟩⟩ hx
    have h := MonoidHom.mem_ker.mp hx
    have h1 : d = 1 := congrArg SemidirectProduct.left h
    have h2 : (⟨𝒬.π s, b⟩ : Q ⋊[MulDistribMulAction.toMulAut B Q] B) = 1 :=
      congrArg SemidirectProduct.right h
    have h3 : b = 1 := congrArg SemidirectProduct.right h2
    subst h1 h3
    exact ⟨s, rfl⟩
  have hθ2 : IsPGroup 2 θ.range := hS.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hk2 : IsPGroup 2 πG.ker := hθ2.to_le hker
  have hNcop : ¬ p ∣ Nat.card πG.ker := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hk2
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hlr : localRank p (D ⋊[𝒬.barHom] (Q ⋊[MulDistribMulAction.toMulAut B Q] B)) ≤
      localRank p (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) := by
    let e := QuotientGroup.quotientKerEquivOfSurjective πG hπG
    exact (PlaneAux.localRank_le_of_injective hp e.symm.toMonoidHom e.symm.injective).trans
      (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 πG.ker hNcop)
  refine PlaneAux.evenRank_le_of_localRank_le_of_card hp ?_
    (hlr.trans (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2))
  intro r hr hrd
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hDp
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hBp
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hQ
  rw [SemidirectProduct.card, SemidirectProduct.card, ha, hb, hc] at hrd
  rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))

end ActionQuotient

section Kernel

variable {B S D : Type} [Group B] [Group S] [Group D] [MulDistribMulAction B S]
  (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D)

theorem smul_mem_ker (b : B) {s : S} (hs : s ∈ (β.comp SemidirectProduct.inl).ker) :
    b • s ∈ (β.comp SemidirectProduct.inl).ker := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs ⊢
  rw [← PlaneSemidirect.conj_inr_inl b s, map_mul, map_mul, map_inv, hs, mul_one, mul_inv_cancel]

theorem isInvariant_ker :
    IsInvariant B S (β.comp SemidirectProduct.inl).ker :=
  ⟨fun b s => ⟨smul_mem_ker β b, fun h => by
    have := smul_mem_ker β b⁻¹ h
    rwa [inv_smul_smul] at this⟩⟩

@[instance_reducible] noncomputable def quotAction :
    MulDistribMulAction B (S ⧸ (β.comp SemidirectProduct.inl).ker) :=
  quotientMulDistribMulAction (A := B) (G := S) _ (isInvariant_ker β)

theorem exists_centralizing_of_quotient {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) [Finite B] [Finite S]
    [Finite D] (hB : IsElementaryAbelian p B) (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S)
    (hDp : IsPGroup p D)
    (he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3) :
    ∃ c : B, c ≠ 1 ∧ ∀ s : S, s⁻¹ * (c • s) ∈ (β.comp SemidirectProduct.inl).ker := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hBp : IsPGroup p B := IsPGroup.of_card (n := 2) hBcard
  by_contra hcon
  push Not at hcon
  let := quotAction β
  have : MulAction.QuotientAction B (β.comp SemidirectProduct.inl).ker :=
    quotientAction_of_isInvariant _ (isInvariant_ker β)
  let 𝒬 : ActionQuotient β (S ⧸ (β.comp SemidirectProduct.inl).ker) :=
    { π := QuotientGroup.mk' _
      fn := QuotientGroup.kerLift _
      smul_map := fun b s => rfl
      surj := QuotientGroup.mk'_surjective _
      fn_inj := QuotientGroup.kerLift_injective _
      fn_map := fun s => rfl }
  have hQ2 : IsPGroup 2 (S ⧸ (β.comp SemidirectProduct.inl).ker) := hS.to_quotient _
  have hfaith : ∀ c : B, (∀ q : S ⧸ (β.comp SemidirectProduct.inl).ker, c • q = q) → c = 1 := by
    intro c hc
    by_contra hc1
    obtain ⟨s, hs⟩ := hcon c hc1
    apply hs
    have h : (QuotientGroup.mk (c • s) : S ⧸ (β.comp SemidirectProduct.inl).ker) =
        QuotientGroup.mk s := hc (QuotientGroup.mk s)
    rw [QuotientGroup.eq] at h
    simpa using Subgroup.inv_mem _ h
  have h3 := faithful_plane_two_action_on_defining_prime_group_rank_obstruction p hp hp3 B
    (S ⧸ (β.comp SemidirectProduct.inl).ker) hB hBcard hQ2 hfaith D hDp 𝒬.barHom
    (𝒬.barHom_injective hp hp2 hBp hQ2 hfaith)
  have h4 := 𝒬.evenRank_le hp hp2 hBp hDp hS hQ2
  omega

end Kernel

end PlaneQuotient

end CFSG.RankThree.PartOne
