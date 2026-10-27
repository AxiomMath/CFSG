module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Hyp5_1_14

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem exists_outerHom :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
      (β : ↥(Subgroup.normalizer (oTwoUpper H : Set G)) →* Q),
      Nat.card Q = 12 ∧ Group.IsSolvable Q ∧
      (∀ k (hk : k ∈ oTwoUpper H), β ⟨k, Subgroup.le_normalizer hk⟩ = 1) ∧
      ∀ g, β g = 1 → ∃ k ∈ oTwoUpper H, (g : G) * k⁻¹ ∈ centralizerModO2 (oTwoUpper H) := by
  set K := oTwoUpper H with hKdef
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel h.l34
  have : CharP k 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card (n := 2)
      (by rw [hk]; norm_num)
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hk hΨ
  have hcardT : Nat.card (kˣ ⋊[LinearThreeFourOuter.inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) = 12 := by
    rw [SemidirectProduct.card, LinearThreeFourOuter.card_units_eq_three hk, Nat.card_prod]
    simp
  have hfin : Finite (kˣ ⋊[LinearThreeFourOuter.inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; norm_num)
  refine ⟨_, inferInstance, hfin, Ψ.comp ((MulAut.congr e).toMonoidHom.comp (quotConjAut K)),
    hcardT, ?_, ?_, ?_⟩
  ·
    have : Group.IsSolvable kˣ := Group.isSolvable_of_comm mul_comm
    have : Group.IsSolvable (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
      Group.isSolvable_of_comm mul_comm
    refine Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      fun x hx => ?_
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hx
  ·
    intro x hx
    show Ψ (MulAut.congr e (quotConjAut K ⟨x, Subgroup.le_normalizer hx⟩)) = 1
    have h1 := quotConjAut_of_mem (X := K) ⟨x, hx⟩
    rw [h1, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
    have h2 : MulAut.conj (e (QuotientGroup.mk ⟨x, hx⟩)) ∈ Ψ.ker := by
      rw [hker]
      exact ⟨_, rfl⟩
    exact h2
  ·
    intro g hg
    have hmem : MulAut.congr e (quotConjAut K g) ∈ Ψ.ker := hg
    rw [hker] at hmem
    obtain ⟨x', hx'⟩ := hmem
    have hq : quotConjAut K g = MulAut.conj (e.symm x') := by
      apply (MulAut.congr e).injective
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]
      exact hx'.symm
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm x')
    refine ⟨y, y.2, ?_⟩
    have h2 : quotConjAut K (g * ⟨y, Subgroup.le_normalizer y.2⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hq, quotConjAut_of_mem, ← hy, mul_inv_cancel]
    exact mem_centralizerModO2_of_quotConjAut_eq_one h2

theorem isSolvable_range_and_not_nine_dvd
    (hsolv : Group.IsSolvable ↥(centralizerModO2 (oTwoUpper H)))
    (h3 : ¬ 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H))) {X : Type} [Group X]
    (α : ↥(Subgroup.normalizer (oTwoUpper H : Set G)) →* X)
    (hα : ∀ k (hk : k ∈ oTwoUpper H), α ⟨k, Subgroup.le_normalizer hk⟩ = 1) :
    Group.IsSolvable ↥α.range ∧ ¬ 9 ∣ Nat.card ↥α.range := by
  obtain ⟨Q, _, _, β, hcard, hQsolv, hβK, hβ⟩ := h.exists_outerHom
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := Subgroup.le_normalizer
  let K' : Subgroup ↥(Subgroup.normalizer (oTwoUpper H : Set G)) :=
    (oTwoUpper H).subgroupOf (Subgroup.normalizer (oTwoUpper H : Set G))
  have : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr le_rfl
  have hKker : ∀ x ∈ K', α x = 1 ∧ β x = 1 := fun x hx =>
    ⟨hα (x : G) hx, hβK (x : G) hx⟩
  let αbar : ↥(Subgroup.normalizer (oTwoUpper H : Set G)) ⧸ K' →* ↥α.range :=
    QuotientGroup.lift K' α.rangeRestrict fun x hx => Subtype.ext (hKker x hx).1
  have hαs : Function.Surjective αbar := by
    intro y
    obtain ⟨x, hx⟩ := α.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk x, hx⟩
  let βbar : ↥(Subgroup.normalizer (oTwoUpper H : Set G)) ⧸ K' →* Q :=
    QuotientGroup.lift K' β fun x hx => (hKker x hx).2
  have hCMp : centralizerModO2 (oTwoUpper H) ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    centralizerModO2_le_normalizer (oTwoUpper H)
  let C' : Subgroup ↥(Subgroup.normalizer (oTwoUpper H : Set G)) :=
    (centralizerModO2 (oTwoUpper H)).subgroupOf (Subgroup.normalizer (oTwoUpper H : Set G))
  have hC'solv : Group.IsSolvable ↥C' := by
    have := hsolv
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hCMp).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hCMp).symm.surjective
  let f : ↥C' →* ↥(Subgroup.normalizer (oTwoUpper H : Set G)) ⧸ K' :=
    (QuotientGroup.mk' K').comp C'.subtype
  have hfg : ∀ x, βbar x = 1 → x ∈ f.range := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk, hgk⟩ := hβ g hx
      refine ⟨⟨g * ⟨k, hKN hk⟩⁻¹, hgk⟩, ?_⟩
      show QuotientGroup.mk (g * ⟨k, hKN hk⟩⁻¹) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      have : (g * ⟨k, hKN hk⟩⁻¹)⁻¹ * g = ⟨k, hKN hk⟩ := by group
      rw [this]
      exact hk
  have hQ₀solv : Group.IsSolvable (↥(Subgroup.normalizer (oTwoUpper H : Set G)) ⧸ K') :=
    Group.isSolvable_of_ker_le_range f βbar hfg
  refine ⟨Group.isSolvable_of_surjective hαs, fun h9 => h3 ?_⟩
  have h1 : Nat.card ↥α.range ∣ Nat.card (↥(Subgroup.normalizer (oTwoUpper H : Set G)) ⧸ K') :=
    Subgroup.card_dvd_of_surjective hαs
  have h2 : Nat.card ↥βbar.ker ∣ Nat.card ↥C' :=
    (Subgroup.card_dvd_of_le fun x hx => hfg x hx).trans (Subgroup.card_range_dvd f)
  have h3' : Nat.card ↥βbar.range ∣ 12 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card (↥(Subgroup.normalizer (oTwoUpper H : Set G)) ⧸ K') ∣
      Nat.card ↥C' * 12 := by
    rw [← Subgroup.card_ker_mul_card_range βbar]
    exact Nat.mul_dvd_mul h2 h3'
  have h5 : Nat.card ↥C' = Nat.card ↥(centralizerModO2 (oTwoUpper H)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCMp).toEquiv
  have h9' := (h9.trans h1).trans h4
  rw [h5] at h9'
  omega

end Hyp5_1_14

end CFSG.Quasithin.H13
