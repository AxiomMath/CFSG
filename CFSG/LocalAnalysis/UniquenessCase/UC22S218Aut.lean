module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
import CFSG.GroupTheory.PRankLeOneOfIsCyclic
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin.H13.Sec53F.BA (BorelAutData isSylowTwoOf_top_map)

variable {Y : Type} [Group Y] {n E : ℕ} {U H : Subgroup Y} {F : Subgroup (MulAut Y)}

theorem exists_conj_mul_of_borel [Finite Y] (D : BorelAutData U H F) (α : MulAut Y) :
    ∃ y : Y, ∃ σ ∈ F, α = MulAut.conj y * σ := by
  obtain ⟨k, -, hk⟩ := D.sylow.exists_conj (isSylowTwoOf_top_map D.sylow α)
  have hstab : ∀ x : Y, ((MulAut.conj k)⁻¹ * α) x ∈ U ↔ x ∈ U := by
    intro x
    have h1 : α x ∈ U.map (MulAut.conj k).toMonoidHom ↔ (MulAut.conj k).symm (α x) ∈ U :=
      Subgroup.mem_map_equiv
    rw [← hk] at h1
    exact h1.symm.trans (CFSG.Quasithin.H13.Sec53F.BA.mem_map_equiv_iff' α U x)
  obtain ⟨g, -, σ, hσ, hβ⟩ := D.normal_form _ hstab
  refine ⟨k * g, σ, hσ, ?_⟩
  rw [map_mul, mul_assoc, ← hβ, mul_inv_cancel_left]

open scoped IsMulCommutative in
theorem FieldBorelData.exists_injective_zpowers [Finite Y] (D : FieldBorelData n E U H F) :
    ∃ (e : ℕ) (u : (ZMod e)ˣ), e ∣ E ∧ ((u : (ZMod e)ˣ) : ZMod e) = 2 ∧
      ∃ κ : ↥F →* ↥(Subgroup.zpowers u), Function.Injective κ := by
  classical
  have : IsMulCommutative ↥H := ⟨⟨fun a b => Subtype.ext (D.borel.H_comm _ a.2 _ b.2)⟩⟩
  obtain ⟨h₀, hh₀⟩ := Monoid.exists_orderOf_eq_exponent (G := ↥H) Monoid.ExponentExists.of_finite
  set e := Monoid.exponent ↥H with he
  have hodd : Odd e := by
    by_contra hev
    have h2 : 2 ∣ e := by
      rcases Nat.even_or_odd e with h | h
      · exact even_iff_two_dvd.1 h
      · exact absurd h hev
    obtain ⟨m, hm⟩ := h2
    have hepos : 0 < e := Monoid.exponent_pos.2 Monoid.ExponentExists.of_finite
    have hmpos : 0 < m := by omega
    set x : ↥H := h₀ ^ m with hx
    have hx2 : x ^ 2 = 1 := by
      rw [hx, ← pow_mul, mul_comm, ← hm, ← hh₀]
      exact pow_orderOf_eq_one h₀
    have hx1 : x ≠ 1 := by
      rw [hx]
      exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hh₀]; omega)
    have hxN : (x : Y) ∈ normalizer (U : Set Y) := D.borel.H_le x.2
    have hxU : (x : Y) ∈ U :=
      D.borel.mem_U_of_pow (x : Y) hxN (a := 1) (by simpa using congrArg Subtype.val hx2)
    exact hx1 (Subtype.ext (D.borel.U_inf_H _ hxU x.2))
  have hcop : Nat.Coprime 2 e := Nat.coprime_two_left.2 hodd
  let u₂ : (ZMod e)ˣ := ZMod.unitOfCoprime 2 hcop
  have hu₂ : ∀ k : ℕ, ((u₂ ^ k : (ZMod e)ˣ) : ZMod e) = ((2 ^ k : ℕ) : ZMod e) := fun k => by
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
    push_cast
    rfl
  let j : ↥F → ℕ := fun σ => Classical.choose (D.pow σ σ.2)
  have hj : ∀ (σ : ↥F), ∀ h ∈ H, (σ : MulAut Y) h = h ^ 2 ^ j σ := fun σ =>
    Classical.choose_spec (D.pow σ σ.2)
  have key : ∀ a b : ℕ, (∀ h ∈ H, h ^ 2 ^ a = h ^ 2 ^ b) → u₂ ^ a = u₂ ^ b := by
    intro a b hab
    have h1 : h₀ ^ 2 ^ a = h₀ ^ 2 ^ b := Subtype.ext (hab _ h₀.2)
    have h2 : 2 ^ a ≡ 2 ^ b [MOD e] := by
      rw [← hh₀]
      exact pow_eq_pow_iff_modEq.1 h1
    apply Units.ext
    rw [hu₂, hu₂]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  let κ : ↥F →* (ZMod e)ˣ :=
    { toFun := fun σ => u₂ ^ j σ
      map_one' := (key _ 0 fun h hh => by
        have := hj 1 h hh
        rw [OneMemClass.coe_one, MulAut.one_apply] at this
        rw [← this]
        simp).trans (pow_zero u₂)
      map_mul' := fun σ τ => by
        show u₂ ^ j (σ * τ) = u₂ ^ j σ * u₂ ^ j τ
        rw [← pow_add]
        refine key _ _ fun h hh => ?_
        have h1 := hj (σ * τ) h hh
        rw [Subgroup.coe_mul, MulAut.mul_apply, hj τ h hh, map_pow, hj σ h hh,
          ← pow_mul, ← pow_add] at h1
        exact h1.symm ▸ rfl }
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : u₂ ^ j σ = 1 := hσ
    have h2 : 2 ^ j σ ≡ 1 [MOD e] := by
      have h3 : ((2 ^ j σ : ℕ) : ZMod e) = ((1 : ℕ) : ZMod e) := by
        rw [← hu₂, h1]
        simp
      exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h3
    have hfix : ∀ h ∈ H, (σ : MulAut Y) h = h := by
      intro h hh
      rw [hj σ h hh]
      have hdvd : orderOf (⟨h, hh⟩ : ↥H) ∣ e := Monoid.order_dvd_exponent _
      have h3 : 2 ^ j σ ≡ 1 [MOD orderOf (⟨h, hh⟩ : ↥H)] := h2.of_dvd hdvd
      have h4 := pow_eq_pow_iff_modEq.2 h3
      rw [pow_one] at h4
      exact congrArg Subtype.val h4
    exact Subtype.ext (D.borel.F_faithful σ σ.2 hfix)
  let κ' : ↥F →* ↥(Subgroup.zpowers u₂) :=
    κ.codRestrict (Subgroup.zpowers u₂) fun σ => Subgroup.pow_mem _ (Subgroup.mem_zpowers u₂) _
  refine ⟨e, u₂, Monoid.exponent_dvd_of_forall_pow_eq_one fun h => Subtype.ext (D.exp h h.2), ?_,
    κ', fun a b hab => hκ (congrArg Subtype.val hab)⟩
  exact (ZMod.coe_unitOfCoprime (n := e) 2 hcop).trans Nat.cast_ofNat

theorem FieldBorelData.isCyclic_F [Finite Y] (D : FieldBorelData n E U H F) : IsCyclic ↥F := by
  obtain ⟨e, u, -, -, κ, hκ⟩ := D.exists_injective_zpowers
  have : IsCyclic ↥(Subgroup.zpowers u) := inferInstance
  exact isCyclic_of_injective κ hκ

theorem FieldBorelData.card_F_dvd [Finite Y] {m : ℕ} (D : FieldBorelData n (2 ^ m - 1) U H F) :
    Nat.card ↥F ∣ m := by
  obtain ⟨e, u, he, hu, κ, hκ⟩ := D.exists_injective_zpowers
  have h1 : Nat.card ↥F ∣ Nat.card ↥(Subgroup.zpowers u) := Subgroup.card_dvd_of_injective κ hκ
  rw [Nat.card_zpowers] at h1
  refine h1.trans (orderOf_dvd_of_pow_eq_one (Units.ext ?_))
  have h2 : ((2 ^ m - 1 : ℕ) : ZMod e) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 he
  rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    sub_eq_zero] at h2
  rw [Units.val_pow_eq_pow_val, hu, Units.val_one, h2]

theorem FieldBorel.center_eq_one (h : FieldBorel Y n E) :
    ∀ y : Y, (∀ x : Y, y * x = x * y) → y = 1 := by
  obtain ⟨U, H, F, D⟩ := h
  exact D.borel.center

private instance normal_range_mulAut_conj (Y : Type) [Group Y] :
    ((MulAut.conj : Y →* MulAut Y).range).Normal :=
  ⟨by
    rintro _ ⟨y, rfl⟩ g
    refine ⟨g y, ?_⟩
    ext x
    simp [MulAut.conj_apply]⟩

private theorem pRank_mulAut_le_aux [Finite Y] (D : BorelAutData U H F) {p : ℕ} (hp : p.Prime) :
    Function.Surjective
        ((QuotientGroup.mk' (MulAut.conj : Y →* MulAut Y).range).comp F.subtype) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) +
        CFSG.Open.pRank p
          (⊤ : Subgroup (MulAut Y ⧸ (MulAut.conj : Y →* MulAut Y).range)) := by
  refine ⟨?_, ?_⟩
  · intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, σ, hσ, rfl⟩ := exists_conj_mul_of_borel D α
    refine ⟨⟨σ, hσ⟩, ?_⟩
    have hmem : MulAut.conj y ∈ (MulAut.conj : Y →* MulAut Y).range :=
      MonoidHom.mem_range.2 ⟨y, rfl⟩
    have h1 : QuotientGroup.mk' (MulAut.conj : Y →* MulAut Y).range (MulAut.conj y) = 1 :=
      (QuotientGroup.eq_one_iff (MulAut.conj y)).2 hmem
    show QuotientGroup.mk' _ σ = QuotientGroup.mk' _ (MulAut.conj y * σ)
    rw [map_mul, h1, one_mul]
  · have h1 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hp
      (QuotientGroup.mk' (MulAut.conj : Y →* MulAut Y).range) ⊤
    rw [QuotientGroup.ker_mk', top_inf_eq] at h1
    have h2 : CFSG.Open.pRank p (MulAut.conj : Y →* MulAut Y).range =
        CFSG.Open.pRank p (⊤ : Subgroup Y) := by
      rw [show (MulAut.conj : Y →* MulAut Y).range = (⊤ : Subgroup Y).map
        (MulAut.conj : Y →* MulAut Y) from MonoidHom.range_eq_map _]
      exact CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
        D.conj_injective ⊤
    have h3 := CFSG.SectionRank.pRank_mono hp.one_lt
      (le_top : (⊤ : Subgroup (MulAut Y)).map
        (QuotientGroup.mk' (MulAut.conj : Y →* MulAut Y).range) ≤ ⊤)
    omega

theorem pRank_mulAut_le_of_fieldBorel [Finite Y] (hFB : FieldBorel Y n E) {p : ℕ}
    (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) + 1 := by
  obtain ⟨U, H, F, D⟩ := hFB
  obtain ⟨hsurj, hle⟩ := pRank_mulAut_le_aux D.borel hp
  have := D.isCyclic_F
  have hcyc : IsCyclic (MulAut Y ⧸ (MulAut.conj : Y →* MulAut Y).range) :=
    isCyclic_of_surjective _ hsurj
  have h3 := CFSG.pRank_le_one_of_isCyclic hp hcyc
  omega

theorem pRank_eq_zero_of_not_dvd_card {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card Q) (H : Subgroup Q) : CFSG.Open.pRank p H = 0 := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  by_contra hk
  apply h
  have h1 : p ^ CFSG.Open.pRank p H ∣ Nat.card Q := hE ▸ Subgroup.card_subgroup_dvd_card E
  exact (dvd_pow_self p hk).trans h1

theorem pRank_mulAut_le_of_fieldBorel_of_not_dvd [Finite Y] {m : ℕ}
    (hFB : FieldBorel Y n (2 ^ m - 1)) {p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  obtain ⟨U, H, F, D⟩ := hFB
  obtain ⟨hsurj, hle⟩ := pRank_mulAut_le_aux D.borel hp
  have hcard : Nat.card (MulAut Y ⧸ (MulAut.conj : Y →* MulAut Y).range) ∣ Nat.card ↥F :=
    Subgroup.card_dvd_of_surjective hsurj
  have h0 := pRank_eq_zero_of_not_dvd_card hp
    (fun hd => hpm ((hd.trans hcard).trans D.card_F_dvd))
    (⊤ : Subgroup (MulAut Y ⧸ (MulAut.conj : Y →* MulAut Y).range))
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
