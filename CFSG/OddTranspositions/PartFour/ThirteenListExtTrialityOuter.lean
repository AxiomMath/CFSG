module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityDefs

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace ExtSetting

variable {G : Type} [Group G] {t : G} {M : Subgroup G} [M.Normal]

theorem not_mem (h : ExtSetting G t M) : t ∉ M := by
  intro ht
  have hD : {x : G | IsConj t x} ⊆ M := by
    intro x hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    exact ‹M.Normal›.conj_mem t ht c
  have htop : M = ⊤ := h.setup.eq_top_of_subset M hD
  have hidx := h.index
  rw [htop, Subgroup.index_top] at hidx
  omega

theorem mk_ne_one (h : ExtSetting G t M) :
    ∀ d ∈ {x : G | IsConj t x}, QuotientGroup.mk' M d ≠ 1 := by
  intro d hd h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨c, rfl⟩ := isConj_iff.mp hd
  apply h.not_mem
  have := ‹M.Normal›.conj_mem _ h1 c⁻¹
  simpa [mul_assoc] using this

theorem setup_quotient (h : ExtSetting G t M) :
    Asc72.Setup (G ⧸ M) (QuotientGroup.mk' M '' {x : G | IsConj t x}) :=
  h.setup.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M) h.mk_ne_one

theorem index_le_two_of_image_eq (h : ExtSetting G t M)
    (himg : QuotientGroup.mk' M '' {x : G | IsConj t x} = {QuotientGroup.mk' M t}) :
    M.index ≤ 2 := by
  have hgen := h.setup_quotient.gen
  rw [himg, ← Subgroup.zpowers_eq_closure] at hgen
  have ht2 : orderOf t = 2 := h.setup.oddT.1 t (IsConj.refl t)
  have hdvd : orderOf (QuotientGroup.mk' M t) ∣ 2 := by
    rw [← ht2]
    exact orderOf_map_dvd _ _
  rw [Subgroup.index_eq_card, ← Subgroup.card_top, ← hgen, Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem not_isPGroup_quotient [Finite G] (h : ExtSetting G t M) : ¬ IsPGroup 2 (G ⧸ M) := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (G ⧸ M)))
  have hStop : (S : Subgroup (G ⧸ M)) = ⊤ :=
    (S.is_maximal' (hP.to_subgroup ⊤) le_top).symm
  have hW := h.width S
  change (QuotientGroup.mk' M '' {x : G | IsConj t x} ∩
    ((S : Subgroup (G ⧸ M)) : Set (G ⧸ M))).ncard = 1 at hW
  rw [hStop, Subgroup.coe_top, Set.inter_univ, Set.ncard_eq_one] at hW
  obtain ⟨d, hd⟩ := hW
  have hmem : QuotientGroup.mk' M t ∈ QuotientGroup.mk' M '' {x : G | IsConj t x} :=
    ⟨t, IsConj.refl t, rfl⟩
  rw [hd, Set.mem_singleton_iff] at hmem
  have hidx := h.index_le_two_of_image_eq (by rw [hd, hmem])
  have := h.index
  omega

theorem not_comm_quotient (h : ExtSetting G t M) : ¬ ∀ a b : G ⧸ M, a * b = b * a := by
  intro hc
  have himg : QuotientGroup.mk' M '' {x : G | IsConj t x} = {QuotientGroup.mk' M t} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.mp hx
      rw [Set.mem_singleton_iff, map_mul, map_mul, map_inv, hc (QuotientGroup.mk' M c)]
      group
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨t, IsConj.refl t, hy.symm⟩
  have hidx := h.index_le_two_of_image_eq himg
  have := h.index
  omega

@[expose] noncomputable def outerHomG (M : Subgroup G) [M.Normal] : G →* Outer ↥M :=
  (QuotientGroup.mk' (inner ↥M)).comp MulAut.conjNormal

theorem ker_outerHomG (hcent : Subgroup.centralizer (M : Set G) = ⊥) :
    (outerHomG M).ker = M := by
  ext g
  rw [MonoidHom.mem_ker, outerHomG, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    have hc : (m : G)⁻¹ * g ∈ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut ↥M => ((φ ⟨x, hx⟩ : ↥M) : G)) hm
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        MulAut.conjNormal_apply] at h1
      have h2 : (m : G) * x * (m : G)⁻¹ = g * x * g⁻¹ := h1
      calc x * ((m : G)⁻¹ * g) = (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * g := by group
        _ = (m : G)⁻¹ * (g * x * g⁻¹) * g := by rw [h2]
        _ = (m : G)⁻¹ * g * x := by group
    rw [hcent, Subgroup.mem_bot] at hc
    have : g = m := by
      rw [← mul_one (m : G), ← hc]
      group
    rw [this]
    exact m.2
  · intro hg
    exact ⟨⟨g, hg⟩, (MulAut.conjNormal_val (h := ⟨g, hg⟩)).symm⟩

@[expose] noncomputable def outerHom (hcent : Subgroup.centralizer (M : Set G) = ⊥) :
    G ⧸ M →* Outer ↥M :=
  (QuotientGroup.kerLift (outerHomG M)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_outerHomG hcent).symm).toMonoidHom

theorem outerHom_injective (hcent : Subgroup.centralizer (M : Set G) = ⊥) :
    Function.Injective (outerHom hcent) := by
  intro a b hab
  have h1 : QuotientGroup.kerLift (outerHomG M)
      (QuotientGroup.quotientMulEquivOfEq (ker_outerHomG hcent).symm a) =
      QuotientGroup.kerLift (outerHomG M)
        (QuotientGroup.quotientMulEquivOfEq (ker_outerHomG hcent).symm b) := hab
  exact (QuotientGroup.quotientMulEquivOfEq (ker_outerHomG hcent).symm).injective
    (QuotientGroup.kerLift_injective _ h1)

theorem not_isPGroup_outer [Finite G] (h : ExtSetting G t M) : ¬ IsPGroup 2 (Outer ↥M) :=
  fun hP => h.not_isPGroup_quotient (hP.of_injective _ (outerHom_injective h.centralizer))

theorem not_comm_outer (h : ExtSetting G t M) : ¬ ∀ a b : Outer ↥M, a * b = b * a := by
  intro hc
  apply h.not_comm_quotient
  intro a b
  apply outerHom_injective h.centralizer
  rw [map_mul, map_mul, hc]

end ExtSetting

end CFSG.OddTranspositions.PartFour
