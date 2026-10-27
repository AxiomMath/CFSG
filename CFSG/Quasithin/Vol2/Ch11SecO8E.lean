module

public import CFSG.Quasithin.Vol2.Ch11SecO8C
public import CFSG.Quasithin.Vol2.Ch11SecO8D
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFull

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Quasithin CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

namespace O8S

variable {W : Type} [CommGroup W] {Hs Ks : Subgroup (MulAut W)} {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def img (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F))
    (B : Subgroup (MulAut W)) : Subgroup (Gamma F) :=
  (B.subgroupOf Hs).map (phi hn hF hHN e)

theorem isElemAbelian2_closure {S : Set (MulAut W)} (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hs : ∀ a ∈ S, a ^ 2 = 1) : IsElemAbelian2 (Subgroup.closure S) := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      hc b hb a ha
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set (MulAut W)) :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (h1 hb) a ha).symm
  have hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (h2 hb) a ha)
  refine ⟨hcomm, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hcomm x hx y hy) 2), ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem three_le_card {G : Type*} [Group G] {K : Subgroup G} [Finite K] {a b : G} (ha : a ∈ K)
    (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card K := by
  let f : Fin 3 → K := ![1, ⟨a, ha⟩, ⟨b, hb⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;> simp_all
  simpa using Nat.card_le_card_of_injective f hf

@[expose] def ord3 [CharP F 2] : SL(2, F) :=
  ⟨!![0, 1; 1, 1], by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h2⟩

theorem ord3_pow_three [CharP F 2] : (ord3 : SL(2, F)) ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem ord3_ne_one [CharP F 2] : (ord3 : SL(2, F)) ≠ 1 := by
  intro h1
  have h2 := congrArg (fun s : SL(2, F) => s.1 0 0) h1
  simp [ord3] at h2

theorem ord3_mem_fixedSL2 [CharP F 2] (σ : RingAut F) : (ord3 : SL(2, F)) ∈ fixedSL2 σ := by
  rw [← sl2_field_fixed_iff]
  apply Subtype.ext
  rw [sl2FieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ord3]

section Rank

variable (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
  (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F))

theorem img_isElementaryAbelian {B : Subgroup (MulAut W)} (hB : IsElemAbelian2 B) :
    CFSG.IsElementaryAbelian 2 ↥(img hn hF hHN e B) := by
  apply isElementaryAbelian_of
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB.1 _ ha _ hb)
  · rintro _ ⟨a, ha, rfl⟩
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hB.2 _ ha)
    rw [← map_pow, this, map_one]

theorem phi_mem_img {B : Subgroup (MulAut W)} {b : ↥Hs} (hb : (b : MulAut W) ∈ B) :
    phi hn hF hHN e b ∈ img hn hF hHN e B :=
  Subgroup.mem_map.mpr ⟨b, Subgroup.mem_subgroupOf.mpr hb, rfl⟩

variable [Finite F] (hKH : Ks ≤ Hs) (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
  (hO : CFSG.pCore 2 ↥Hs = ⊥)

include h2 hO in
theorem card_img {B : Subgroup (MulAut W)} (hBH : B ≤ Hs) :
    Nat.card ↥(img hn hF hHN e B) = Nat.card ↥B := by
  rw [img, Subgroup.card_map_of_injective (phi_injective hn hF hHN e h2 hO)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv

include hKH h2 hO in
theorem rank_data {B : Subgroup (MulAut W)} (hBH : B ≤ Hs) (hB : IsElemAbelian2 B)
    {t : MulAut W} (htB : t ∈ B) (htK : t ∉ Ks) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧ Nat.card ↥B ≤ 2 ^ (s + 1) ∧
      Nat.card ↥B = 2 * Nat.card ↥(intersectionS (img hn hF hHN e B)) ∧
      Nat.card ↥(intersectionS (img hn hF hHN e B)) ≤ 2 ^ s ∧
      Nat.card (fixedField (phi hn hF hHN e ⟨t, hBH htB⟩).right) = 2 ^ s ∧
      ∃ x : SL(2, F), centralizerS (phi hn hF hHN e ⟨t, hBH htB⟩) =
        (fixedSL2 (phi hn hF hHN e ⟨t, hBH htB⟩).right).map (MulAut.conj x).toMonoidHom := by
  have := img_isElementaryAbelian hn hF hHN e hB
  have hout : phi hn hF hHN e ⟨t, hBH htB⟩ ∉ linearKernel F :=
    fun h => htK (mem_of_phi_mem hn hF hHN e hKH h2 hO _ h)
  obtain ⟨s, hs1, hns, -, hfix, ⟨x, -, hx⟩, -, hfac, hI, hA, -, -, -⟩ :=
    original_outer_elementary_field_conjugacy_and_rank hn hF (img hn hF hHN e B) _
      (phi_mem_img hn hF hHN e htB) hout
  rw [card_img hn hF hHN e h2 hO hBH] at hfac hA
  rw [linearIntersection_card_eq_intersectionS] at hfac hI
  exact ⟨s, hs1, hns, hA, hfac, hI, hfix, x, hx⟩

end Rank

end O8S

end CFSG.Quasithin.Vol2.Ch11.SecC
