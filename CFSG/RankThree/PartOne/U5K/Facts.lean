module

public import CFSG.RankThree.PartOne.U5K.ThompsonMap

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)

variable {G : Type} [Group G] [Finite G]

structure U5Facts (f p : ℕ) (I T : Subgroup G)
    (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) : Prop where
  inj : ∀ t ∈ T, ∀ ht : t ∈ Subgroup.normalizer (I : Set G), U5Act I e ⟨t, ht⟩ = 1 → t = 1
  model : U5ModelAt f p (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T)
  image_S : rm (Subgroup.normalizer (I : Set G)) (U5Act I e) (pushingUpS T) =
    pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T)
  image_Z : rm (Subgroup.normalizer (I : Set G)) (U5Act I e) (zOf (pushingUpS T)) =
    zOf (pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T))
  S_le : pushingUpS T ≤ I
  lift : ∀ a ∈ U5Inn f ⊓ Subgroup.normalizer
      (pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T) :
        Set (MulAut (projSU 5 2 f))),
    ∃ (y : G) (hy : y ∈ Subgroup.normalizer (I : Set G)), y ∈ I ∧
      y ∈ Subgroup.normalizer (pushingUpS T : Set G) ∧ U5Act I e ⟨y, hy⟩ = a

omit [Finite G] in
theorem U5_surj (f : ℕ) (I : Subgroup G) (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) :
    ∀ a ∈ U5Inn f, ∃ i : ↥(Subgroup.normalizer (I : Set G)), (i : G) ∈ I ∧ U5Act I e i = a := by
  rintro a ⟨z, rfl⟩
  obtain ⟨i, hi, h⟩ := exists_mem_U5Act_eq_conj I e z
  exact ⟨⟨i, I.le_normalizer hi⟩, hi, h⟩

omit [Finite G] in
theorem U5Inn_le_range (f : ℕ) (I : Subgroup G) (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) :
    U5Inn f ≤ (U5Act I e).range := fun a ha => by
  obtain ⟨i, -, hi⟩ := U5_surj f I e a ha
  exact ⟨i, hi⟩

theorem u5Facts (hM : U5Model) {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpf : p ∣ 2 ^ f + 1) {I T : Subgroup G} (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)
    (hT : IsSylowOf 2 T (Subgroup.normalizer (I : Set G)))
    (hodd : ¬ 2 ∣ Nat.card (U5Act I e).ker) : U5Facts f p I T e := by
  have hTN : T ≤ Subgroup.normalizer (I : Set G) := hT.1
  have hinj : ∀ t ∈ T, ∀ ht : t ∈ Subgroup.normalizer (I : Set G), U5Act I e ⟨t, ht⟩ = 1 → t = 1 :=
    fun t htT htN h => eq_one_of_isPGroup_two hodd hT.2.1 htT htN h
  have hsyl := isSylowOf_rm (ρ := U5Act I e) hT
  have hmodel := hM f hf p hp hp5 hpf _ _ (U5Inn_le_range f I e) hsyl
  obtain ⟨hS, -⟩ := rm_pushingUpS (ρ := U5Act I e) hTN hinj
  have hZ := rm_zOf (ρ := U5Act I e) hTN hinj
  have hIN : I ≤ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer
  have hInorm : (I.subgroupOf (Subgroup.normalizer (I : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIN).2 le_rfl
  have hSN : pushingUpS T ≤ Subgroup.normalizer (I : Set G) := (pushingUpS_le T).trans hTN
  have hS2 : IsPGroup 2 (pushingUpS T) := hT.2.1.to_le (pushingUpS_le T)
  have hSI : pushingUpS T ≤ I :=
    le_of_rm_le (ρ := U5Act I e) hInorm (U5_surj f I e) hodd hSN hS2
      (hS ▸ hmodel.le_inn)
  refine ⟨hinj, hmodel, hS, hZ, hSI, ?_⟩
  intro a ha
  have ha' : a ∈ U5Inn f ⊓ Subgroup.normalizer
      (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) (pushingUpS T) :
        Set (MulAut (projSU 5 2 f))) := by
    rw [hS]
    exact ha
  exact exists_lift (ρ := U5Act I e) hInorm hIN (U5_surj f I e) hodd hS2 hSI ha'

end CFSG.RankThree.PartOne.U5K
