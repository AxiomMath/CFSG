module

public import CFSG.RankThree.PartOne.S10.PlaneContract
import CFSG.RankThree.PartOne.S10.PlaneRestriction
import CFSG.RankThree.PartOne.S10.PlaneFactorCases
import CFSG.RankThree.PartOne.S10.PlaneCoreBounds
import CFSG.RankThree.PartOne.S10.PlaneFrattiniAction
import CFSG.RankThree.PartOne.S10.PlaneQuotientStep
import CFSG.GroupTheory.ThompsonAxB
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace PlaneCommutator

@[expose] def Claim (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (B S : Type) [Group B] [Group S] [Finite B] [Finite S]
    [MulDistribMulAction B S], IsElementaryAbelian p B → Nat.card B = p ^ 2 → IsPGroup 2 S →
    (∀ c : B, (∀ s : S, c • s = s) → c = 1) →
    ∀ (D : Type) [Group D] [Finite D], IsPGroup p D → Nat.card D * Nat.card S = n →
    ∀ β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D,
      (∃ y ∈ actionCommutator B (⊤ : Subgroup S), ∃ d : D,
        β (SemidirectProduct.inl y) d ≠ d) →
      3 < evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B))

variable {p : ℕ} {B S D : Type} [Group B] [Group S] [Group D] [Finite B] [Finite S] [Finite D]
  [MulDistribMulAction B S]

theorem core (hp : p.Prime) (hp3 : 3 < p) (IH : ∀ m < Nat.card D * Nat.card S, Claim m)
    (hB : IsElementaryAbelian p B) (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S)
    (hfaith : ∀ c : B, (∀ s : S, c • s = s) → c = 1) (hDp : IsPGroup p D)
    (hDexp : ∀ x : D, x ^ p = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (hSc : actionCommutator B (⊤ : Subgroup S) = ⊤)
    (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D)
    (hnt : ∃ (y : S) (d : D), β (SemidirectProduct.inl y) d ≠ d)
    (he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hBp : IsPGroup p B := IsPGroup.of_card (n := 2) hBcard
  have hBcomm : ∀ x y : B, x * y = y * x := fun x y => hB.is_comm.comm x y
  obtain ⟨c, hc1, hcR⟩ := PlaneQuotient.exists_centralizing_of_quotient β hp hp3 hB hBcard hS hDp he
  have hmul : ∀ s : S, β (SemidirectProduct.inl s) * β (SemidirectProduct.inr c) =
      β (SemidirectProduct.inr c) * β (SemidirectProduct.inl s) := by
    intro s
    have h1 : β (SemidirectProduct.inl (c • s)) = β (SemidirectProduct.inl s) := by
      have hr : β (SemidirectProduct.inl (s⁻¹ * (c • s))) = 1 := MonoidHom.mem_ker.mp (hcR s)
      have hcs : c • s = s * (s⁻¹ * (c • s)) := by group
      rw [hcs, map_mul, map_mul, hr, mul_one]
    have h2 := PlaneSemidirect.conj_inr_inl c s
    have h3 : (SemidirectProduct.inr c : S ⋊[MulDistribMulAction.toMulAut B S] B) *
        SemidirectProduct.inl s =
        SemidirectProduct.inl (c • s) * SemidirectProduct.inr c := by
      rw [← h2]
      group
    calc β (SemidirectProduct.inl s) * β (SemidirectProduct.inr c) =
          β (SemidirectProduct.inl (c • s)) * β (SemidirectProduct.inr c) := by rw [h1]
      _ = β (SemidirectProduct.inl (c • s) * SemidirectProduct.inr c) := (map_mul _ _ _).symm
      _ = β (SemidirectProduct.inr c * SemidirectProduct.inl s) := by rw [h3]
      _ = β (SemidirectProduct.inr c) * β (SemidirectProduct.inl s) := map_mul _ _ _
  have hcomm : ∀ (s : S) (d : D), β (SemidirectProduct.inl s) (β (SemidirectProduct.inr c) d) =
      β (SemidirectProduct.inr c) (β (SemidirectProduct.inl s) d) := fun s d => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hmul s]
  let F : Subgroup D := MonoidHom.eqLocus (β (SemidirectProduct.inr c)).toMonoidHom
    (MonoidHom.id D)
  have hFmem : ∀ d : D, d ∈ F ↔ β (SemidirectProduct.inr c) d = d := fun d => Iff.rfl
  have hFinv : ∀ k : S ⋊[MulDistribMulAction.toMulAut B S] B, ∀ d ∈ F, β k d ∈ F := by
    intro k d hd
    rw [hFmem] at hd
    rw [← SemidirectProduct.inl_left_mul_inr_right k, map_mul, MulAut.mul_apply, hFmem]
    have h1 : β (SemidirectProduct.inr c) (β (SemidirectProduct.inr k.right) d) =
        β (SemidirectProduct.inr k.right) d := by
      rw [← MulAut.mul_apply, ← map_mul, ← map_mul, hBcomm c k.right, map_mul, map_mul,
        MulAut.mul_apply, hd]
    rw [← hcomm, h1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFtop : F = ⊤ := by
    by_contra hFne
    have hcardlt : Nat.card F < Nat.card D :=
      lt_of_le_of_ne (Subgroup.card_le_card_group F) fun h =>
        hFne ((Subgroup.card_eq_iff_eq_top F).mp h)
    have hFp : IsPGroup p F := hDp.to_subgroup F
    by_cases hntF : ∃ (y : S) (d : F),
        PlaneSemidirect.restrictHom β F hFinv (SemidirectProduct.inl y) d ≠ d
    · obtain ⟨y, d, hd⟩ := hntF
      have h3 := IH (Nat.card F * Nat.card S)
        (Nat.mul_lt_mul_of_pos_right hcardlt Nat.card_pos) p hp hp3 B S hB hBcard hS hfaith F hFp
        rfl (PlaneSemidirect.restrictHom β F hFinv)
        ⟨y, by rw [hSc]; exact Subgroup.mem_top y, d, hd⟩
      have h4 := PlaneRestrict.evenRank_restrict_le β F hFinv
      omega
    · push Not at hntF
      have hA : ¬ p ∣ Nat.card S := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
        rw [hn]
        intro h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      have hall := CFSG.GroupTheory.thompson_A_times_B (p := p) hDp hA
        (hBp.to_subgroup (Subgroup.zpowers c)) (β.comp SemidirectProduct.inl)
        ((β.comp SemidirectProduct.inr).comp (Subgroup.zpowers c).subtype)
        (fun a b => by
          obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp b.2
          change β (SemidirectProduct.inl a) * β (SemidirectProduct.inr (b : B)) =
            β (SemidirectProduct.inr (b : B)) * β (SemidirectProduct.inl a)
          rw [← hm, map_zpow, map_zpow]
          exact (Commute.zpow_right (show Commute (β (SemidirectProduct.inl a))
            (β (SemidirectProduct.inr c)) from hmul a) m).eq)
        (fun a r hr => by
          have hrF : r ∈ F := hr ⟨c, Subgroup.mem_zpowers c⟩
          exact congrArg Subtype.val (hntF a ⟨r, hrF⟩))
      obtain ⟨y, d, hyd⟩ := hnt
      exact hyd (by rw [show β (SemidirectProduct.inl y) = 1 from hall y]; rfl)
  have hcD : ∀ d : D, β (SemidirectProduct.inr c) d = d := fun d => by
    have hd : d ∈ F := by
      rw [hFtop]
      exact Subgroup.mem_top d
    exact hd
  let U : Subgroup S := Subgroup.closure {x | ∃ h : S, x = h⁻¹ * (c • h)}
  have hUR : U ≤ (β.comp SemidirectProduct.inl).ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨h, rfl⟩
    exact hcR h
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hc1
    refine hfaith c fun s => ?_
    have hmem : s⁻¹ * (c • s) ∈ U := Subgroup.subset_closure ⟨s, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  have hcU : ∀ u ∈ U, c • u ∈ U := by
    have hle : U ≤ U.comap (MulDistribMulAction.toMonoidHom S c) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨h, rfl⟩
      show c • (h⁻¹ * (c • h)) ∈ U
      rw [smul_mul', smul_inv']
      exact Subgroup.subset_closure ⟨c • h, rfl⟩
    exact fun u hu => hle hu
  have hcp : c ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p B) c
  have hrank : ∀ E : Subgroup D, IsElementaryAbelian p E → ∀ k : ℕ, Nat.card E = p ^ k →
      k ≤ 2 := by
    intro E hE k hk
    have h5 := PlaneSemidirect.succ_le_evenRank_of_normalizes β hp hp2 hS hUne hE
      (fun u hu e _ => by
        have := DFunLike.congr_fun (MonoidHom.mem_ker.mp (hUR hu)) e
        simpa using this) hc1 hcp (fun e _ => hcD e) hcU hk
    omega
  have hV := PlaneCore.card_frattini_quotient_le hp hDp hDexp hDcl hrank
  obtain ⟨y, d, hyd⟩ := hnt
  have h1 := PlaneFrattini.acts_trivially_of_small_frattini hp hp3 hBp hS hDp hV hSc β y
  exact hyd (by rw [h1]; rfl)

theorem claim_all (n : ℕ) : Claim n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro p hp hp3 B S _ _ _ _ _ hB hBcard hS hfaith D _ _ hDp hn β hnt
    by_contra hcon
    have he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3 :=
      not_lt.mp hcon
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp2 : p ≠ 2 := by omega
    obtain ⟨y₀, hy₀S, d₀, hy₀⟩ := hnt
    have hDnt : Nontrivial D := ⟨⟨β (SemidirectProduct.inl y₀) d₀, d₀, hy₀⟩⟩
    obtain ⟨D₀, hchar, -, hcl, hexp, hfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hDp
    have hinv : ∀ k : S ⋊[MulDistribMulAction.toMulAut B S] B, ∀ d ∈ D₀, β k d ∈ D₀ :=
      fun k d hd => Subgroup.characteristic_iff_le_comap.mp hchar (β k) hd
    let β₀ := PlaneSemidirect.restrictHom β D₀ hinv
    have hnt₀ : ∃ y ∈ actionCommutator B (⊤ : Subgroup S), ∃ d : D₀,
        β₀ (SemidirectProduct.inl y) d ≠ d := by
      by_contra h
      push Not at h
      have hmem : β (SemidirectProduct.inl y₀) ∈ fixingSubgroup (MulAut D) (D₀ : Set D) := by
        rw [mem_fixingSubgroup_iff (MulAut D)]
        intro x hx
        exact congrArg Subtype.val (h y₀ hy₀S ⟨x, hx⟩)
      obtain ⟨m, hm⟩ := hfix ⟨β (SemidirectProduct.inl y₀), hmem⟩
      obtain ⟨k, hk⟩ := hS y₀
      have h1 : β (SemidirectProduct.inl y₀) = 1 :=
        PlaneFrattini.eq_one_of_pow_eq_one hp hp2 (congrArg Subtype.val hm)
          (by rw [← map_pow, ← map_pow, hk, map_one, map_one])
      exact hy₀ (by rw [h1]; rfl)
    have hD₀p : IsPGroup p D₀ := hDp.to_subgroup D₀
    have hD₀exp : ∀ x : D₀, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
    have hD₀cl : commutator D₀ ≤ Subgroup.center D₀ :=
      PlaneCore.commutator_le_center_of_critical hcl
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Subgroup S, S₁ = actionCommutator B (⊤ : Subgroup S) := ⟨_, rfl⟩
    have hS₁inv : IsActionInvariant B S₁ := fun b s hs => by
      rw [hS₁] at hs ⊢
      exact smul_mem_actionCommutator_top hs b
    let := PlaneFactorCases.invAction S₁ hS₁inv
    have hsmul : ∀ (b : B) (x : S₁), ((b • x : S₁) : S) = b • (x : S) := fun _ _ => rfl
    have hBodd : ¬ 2 ∣ Nat.card B := by
      rw [hBcard]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h)).symm
    obtain ⟨hfac, hS₁c'⟩ := coprime_pgroup_commutator_factorization (A := B) Nat.prime_two hS hBodd
    have hS₁c : actionCommutator B S₁ = S₁ := by
      rw [hS₁]
      exact hS₁c'
    have hfaith₁ : ∀ c : B, (∀ s : S₁, c • s = s) → c = 1 := by
      intro c hc
      refine hfaith c fun s => ?_
      obtain ⟨d, hd, f, hf, rfl⟩ := hfac s
      have h1 : c • d = d := congrArg Subtype.val (hc ⟨d, hS₁ ▸ hd⟩)
      have h2 : c • f = f := hf c
      rw [smul_mul', h1, h2]
    have hSc₁ : actionCommutator B (⊤ : Subgroup S₁) = ⊤ := by
      apply Subgroup.map_injective S₁.subtype_injective
      rw [PlaneRestrict.map_actionCommutator_subtype S₁ hsmul, hS₁c, Subgroup.map_top,
        Subgroup.range_subtype]
    let ι₁ : (S₁ ⋊[MulDistribMulAction.toMulAut B S₁] B) →*
        (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
      SemidirectProduct.map S₁.subtype (MonoidHom.id B) fun b => MonoidHom.ext fun x => rfl
    have hι₁ : Function.Injective ι₁ := by
      intro x y hxy
      have hl : (ι₁ x).left = (ι₁ y).left := congrArg SemidirectProduct.left hxy
      have hr : (ι₁ x).right = (ι₁ y).right := congrArg SemidirectProduct.right hxy
      exact SemidirectProduct.ext (S₁.subtype_injective hl) hr
    let β₁ := β₀.comp ι₁
    have hnt₁ : ∃ (y : S₁) (d : D₀), β₁ (SemidirectProduct.inl y) d ≠ d := by
      obtain ⟨y, hy, d, hd⟩ := hnt₀
      exact ⟨⟨y, hS₁ ▸ hy⟩, d, hd⟩
    have he₁ : evenRank (D₀ ⋊[β₁] (S₁ ⋊[MulDistribMulAction.toMulAut B S₁] B)) ≤ 3 := by
      have h1 := PlaneRestrict.evenRank_le_of_embedding (β := β₀) (β' := β₁)
        (MonoidHom.id D₀) ι₁ Function.injective_id hι₁ fun k => MonoidHom.ext fun d => rfl
      have h2 : evenRank (D₀ ⋊[β₀] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤
          evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) :=
        PlaneRestrict.evenRank_restrict_le β D₀ hinv
      omega
    have hcard₁ : Nat.card D₀ * Nat.card S₁ ≤ n := by
      rw [← hn]
      exact Nat.mul_le_mul (Subgroup.card_le_card_group D₀) (Subgroup.card_le_card_group S₁)
    exact core hp hp3 (fun m hm => IH m (lt_of_lt_of_le hm hcard₁)) hB hBcard
      (hS.to_subgroup S₁) hfaith₁ hD₀p hD₀exp hD₀cl hSc₁ β₁ hnt₁ he₁

end PlaneCommutator

theorem nontrivial_plane_two_commutator_action_on_prime_group_rank_obstruction :
    ∀ (p : ℕ), p.Prime → 3 < p → ∀ (B S : Type) [Group B] [Group S] [Finite B] [Finite S]
      [MulDistribMulAction B S], IsElementaryAbelian p B → Nat.card B = p ^ 2 → IsPGroup 2 S →
      (∀ c : B, (∀ s : S, c • s = s) → c = 1) →
      ∀ (D : Type) [Group D] [Finite D], IsPGroup p D →
      ∀ β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D,
        (∃ y ∈ actionCommutator B (⊤ : Subgroup S), ∃ d : D,
          β (SemidirectProduct.inl y) d ≠ d) →
        3 < evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) := by
  intro p hp hp3 B S _ _ _ _ _ hB hBcard hS hfaith D _ _ hDp β hnt
  exact PlaneCommutator.claim_all _ p hp hp3 B S hB hBcard hS hfaith D hDp rfl β hnt

end CFSG.RankThree.PartOne
