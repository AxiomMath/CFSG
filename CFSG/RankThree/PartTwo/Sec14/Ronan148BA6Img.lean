module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Sylow
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem subgroupOf_map_subtype_eq {M : Subgroup G} (X : Subgroup ↥M) :
    (X.map M.subtype).subgroupOf M = X := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem exists_le_img148_eq {U : Subgroup G}
    {E : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hEU : E ≤ img148 A Y U) (hE : IsPGroup 3 E) :
    ∃ P : Subgroup G, P ≤ U ∧ IsPGroup 3 P ∧ img148 A Y P = E ∧ Nat.card P = Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'U, hP'p, hP'E, hP'c⟩ := exists_le_map_eq_of_le_map
    (Main148.not_three_dvd_card_ker148 (A := A) (Y := Y)) hEU hE
  refine ⟨P'.map (Y ⊔ A).subtype, fun x hx => ?_, hP'p.map _, ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hx
    exact hP'U hy
  · rw [img148, subgroupOf_map_subtype_eq]
    exact hP'E
  · rw [Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective, hP'c]

theorem exists_conj_eq_of_img148_eq {F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ Y ⊔ A) (h₂ : F₂ ≤ Y ⊔ A)
    (hp : IsPGroup 3 F₁) (hcard : Nat.card F₂ = Nat.card F₁)
    (h : img148 A Y F₁ = img148 A Y F₂) :
    ∃ κ ∈ pPrimeCoreOf 3 Y, F₂ = F₁.map (MulAut.conj κ).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp' : IsPGroup 3 (F₁.subgroupOf (Y ⊔ A)) :=
    hp.comap_of_injective (Y ⊔ A).subtype (Y ⊔ A).subtype_injective
  have hc' : Nat.card (F₂.subgroupOf (Y ⊔ A)) = Nat.card (F₁.subgroupOf (Y ⊔ A)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv, hcard]
  obtain ⟨n, hn, hnP⟩ := exists_mem_map_conj_eq_of_map_eq
    (Main148.not_three_dvd_card_ker148 (A := A) (Y := Y)) hp' hc' h
  refine ⟨n, Subgroup.mem_subgroupOf.mp hn, ?_⟩
  have e₂ : F₂ = (F₂.subgroupOf (Y ⊔ A)).map (Y ⊔ A).subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left h₂]
  rw [e₂, hnP]
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, Subgroup.mem_subgroupOf.mp hv, by simp [MulAut.conj_apply]⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨MulAut.conj n ⟨v, h₁ hv⟩, ⟨⟨v, h₁ hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]

theorem eq_of_mk'_eq_of_isPGroup {F : Subgroup G} (hF : IsPGroup 3 F) {x y : G} (hx : x ∈ F)
    (hy : y ∈ F) (hxM : x ∈ Y ⊔ A) (hyM : y ∈ Y ⊔ A)
    (h : QuotientGroup.mk' (ker148 A Y) ⟨x, hxM⟩ = QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩) :
    x = y := by
  have hN := mk'_ker148_eq_iff.mp h
  obtain ⟨k, hk⟩ := hF ⟨x⁻¹ * y, F.mul_mem (F.inv_mem hx) hy⟩
  have hk' : (x⁻¹ * y) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 := eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) hN hk'
  calc x = x * (x⁻¹ * y) := by rw [h1, mul_one]
    _ = y := by group

omit [Finite G] in
theorem img148_map_conj {X : Subgroup G} (hX : X ≤ Y ⊔ A) {y : G} (hy : y ∈ Y ⊔ A) :
    img148 A Y (X.map (MulAut.conj y).toMonoidHom) =
      (img148 A Y X).map (MulAut.conj (QuotientGroup.mk' (ker148 A Y) ⟨y, hy⟩)).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨g, hg, ⟨x, hx, hxg⟩, rfl⟩ := mem_img148_iff.mp hz
    have hxM : x ∈ Y ⊔ A := hX hx
    refine ⟨QuotientGroup.mk' (ker148 A Y) ⟨x, hxM⟩, mem_img148_iff.mpr ⟨x, hxM, hx, rfl⟩, ?_⟩
    simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hxg ⊢
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [hxg])
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hxM, hx, rfl⟩ := mem_img148_iff.mp hw
    have hyx : y * x * y⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hy hxM) ((Y ⊔ A).inv_mem hy)
    refine mem_img148_iff.mpr ⟨y * x * y⁻¹, hyx, ⟨x, hx, rfl⟩, ?_⟩
    simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl

omit [Finite G] in
theorem img148_zpowers {a : G} (ha : a ∈ Y ⊔ A) :
    img148 A Y (Subgroup.zpowers a) =
      Subgroup.zpowers (QuotientGroup.mk' (ker148 A Y) ⟨a, ha⟩) := by
  ext z
  constructor
  · intro hz
    obtain ⟨g, hg, hga, rfl⟩ := mem_img148_iff.mp hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
  · intro hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine mem_img148_iff.mpr ⟨a ^ k, (Y ⊔ A).zpow_mem ha k, Subgroup.zpow_mem_zpowers a k, ?_⟩
    rw [← map_zpow]
    rfl

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
