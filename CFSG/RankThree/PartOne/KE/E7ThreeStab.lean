module

public import CFSG.RankThree.PartOne.KE.E7ThreeLattice
public import CFSG.RankThree.PartOne.KE.E7ThreeFrame
public import CFSG.RankThree.PartOne.KE.E7FourPerX
public import CFSG.RankThree.PartOne.KE.E7FourStabFive
public import CFSG.RankThree.PartOne.KE6.E8T3Stab

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice RootSpace
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (charVal charVal_single charVal_dualMatrix dualMatrix weylMatrix
  eq_of_charVal_single weylMatrix_injective weylMatrix_pow weylMatrix_one)
open scoped Matrix

@[expose] def e7Count7 (z : Fin Tag.E7.rank → ZMod 7) : ℕ :=
  (Tag.E7.artifactRoots.filter fun l => decide (charVal z (toVec Tag.E7.rank l) = 0)).length

theorem e7Count7_eq_ncard (z : Fin Tag.E7.rank → ZMod 7) :
    e7Count7 z = (rootKernel z).ncard :=
  (ncard_isRoot_and (τ := Tag.E7) (fun v => charVal z v = 0)).symm

theorem e7_image_rootKernel
    {K : Type*} [CommRing K] {z z' : Fin Tag.E7.rank → K}
    {a : WeylGroup Tag.E7} (h : ∀ x, charVal z' (a • x) = charVal z x) :
    (a • ·) '' rootKernel z = rootKernel z' := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul hα.1 a, by rw [h]; exact hα.2⟩
  · intro hβ
    refine ⟨a⁻¹ • β, ⟨IsRoot.smul hβ.1 a⁻¹, ?_⟩, smul_inv_smul a β⟩
    rw [← h, smul_inv_smul]
    exact hβ.2

theorem e7_mem_dualStab_conj {K : Type*} [CommRing K] {z z' : Fin Tag.E7.rank → K}
    {a : WeylGroup Tag.E7} (h : ∀ x, charVal z' (a • x) = charVal z x) (g : WeylGroup Tag.E7) :
    g ∈ dualWeylStabilizer z ↔ a * g * a⁻¹ ∈ dualWeylStabilizer z' := by
  simp only [mem_dualWeylStabilizer]
  constructor
  · intro hg x
    rw [mul_smul, mul_smul, h, hg, ← h, smul_inv_smul]
  · intro hg x
    have := hg (a • x)
    rw [mul_smul, mul_smul, inv_smul_smul, h, h] at this
    exact this

theorem e7Count7_transport
    {z z' : Fin Tag.E7.rank → ZMod 7} {a : WeylGroup Tag.E7}
    (h : ∀ x, charVal z' (a • x) = charVal z x) : e7Count7 z' = e7Count7 z := by
  rw [e7Count7_eq_ncard, e7Count7_eq_ncard, ← e7_image_rootKernel h]
  exact Set.ncard_image_of_injective _ (MulAction.injective a)

@[expose] def e7Wt7 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) (ZMod 7) :=
  ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod 7))ᵀ

theorem e7_eigen_count
    {z : Fin Tag.E7.rank → ZMod 7} (hz : z ≠ 0) {ρ : ZMod 7} (hρ : ρ ^ 2 + ρ + 1 = 0)
    (h : e7Wt7 *ᵥ z = ρ • z) : e7Count7 z ≤ 30 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [e7Count7_eq_ncard]
  rcases e7T3_root_kernel (p := 7) (by norm_num) hρ hz h with h0 | ⟨c, hc, hker⟩
  · have : rootKernel z = ∅ := h0
    rw [this, Set.ncard_empty]
    exact Nat.zero_le _
  · have hk : rootKernel z = {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} := hker
    have hset : {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} =
        ((c.rootList.map (toVec Tag.E7.rank)).toFinset : Set (Fin Tag.E7.rank → ℤ)) := by
      ext α
      simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map]
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, hl, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, hl, rfl⟩
    rw [hk, hset, Set.ncard_coe_finset]
    exact (List.toFinset_card_le _).trans (by rw [List.length_map]; exact e7T3_cert_size hc)

@[expose] def e7G0 : WeylGroup Tag.E7 := (coxeterSystem Tag.E7).wordProd [0, 2, 3, 4, 5, 6]

@[expose] def e7G0List : List (List ℤ) := e7wl [0, 2, 3, 4, 5, 6]

theorem weylMatrix_e7G0 :
    weylMatrix e7G0 = toMat Tag.E7.rank e7G0List :=
  weylMatrix_wordProd_e7 _

theorem e7G0_pow :
    e7G0 ^ 7 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e7G0, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7G0_ne_one :
    e7G0 ≠ 1 := by
  intro h
  have h1 := congrArg weylMatrix h
  rw [weylMatrix_e7G0, weylMatrix_one] at h1
  exact (by decide +kernel : toMat Tag.E7.rank e7G0List ≠ 1) h1

theorem orderOf_e7G0 :
    orderOf e7G0 = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_eq_prime e7G0_pow e7G0_ne_one

@[expose] def e7Gt7 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) (ZMod 7) :=
  ((toMat Tag.E7.rank e7G0List).map (Int.cast : ℤ → ZMod 7))ᵀ

@[expose] def e7T0 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) (ZMod 7) :=
  !![4, 5, 2, 0, 0, 0, 0; 5, 5, 2, 0, 0, 0, 0; 5, 5, 3, 0, 0, 0, 0; 5, 5, 3, 1, 0, 0, 0;
    5, 5, 3, 1, 1, 0, 0; 5, 5, 3, 1, 1, 1, 0; 6, 0, 5, 4, 3, 2, 1]

@[expose] def e7R0f : Matrix (Fin 7) (Fin 7) (ZMod 7) :=
  !![1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0]

@[expose] def e7R0 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) (ZMod 7) := e7R0f

theorem e7T0_mul : e7T0 * (e7Gt7 - (1 : ZMod 7) • 1) = e7R0 := by decide +kernel

theorem echelon7_aux {M T R : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) (ZMod 7)} {r : ZMod 7}
    (hTR : T * (M - r • 1) = R) {z : Fin Tag.E7.rank → ZMod 7} (h : M *ᵥ z = r • z) :
    R *ᵥ z = 0 := by
  have h0 : (M - r • 1) *ᵥ z = 0 := by
    rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  rw [← hTR, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem read7_fix {y : Fin 7 → ZMod 7} (h0 : e7R0f *ᵥ y = 0) :
    y = ![0, y 1, 0, 0, 0, 0, 0] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  have e4 := congrFun h0 4
  have e5 := congrFun h0 5
  simp [e7R0f, Matrix.mulVec, dotProduct, Fin.sum_univ_seven] at e0 e1 e2 e3 e4 e5
  funext j
  fin_cases j
  · simpa using e0
  · simp
  · simpa using e1
  · simpa using e2
  · simpa using e3
  · simpa using e4
  · simpa using e5

theorem dualMatrix_e7G0 :
    dualMatrix (ZMod 7) e7G0 = e7Gt7 := by
  unfold dualMatrix e7Gt7
  rw [weylMatrix_e7G0]

theorem e7G0_dualMatrix_fix
    {y : Fin Tag.E7.rank → ZMod 7}
    (h : e7G0 ∈ dualWeylStabilizer y) : e7Gt7 *ᵥ y = (1 : ZMod 7) • y := by
  have h1 : (dualMatrix (ZMod 7) e7G0).mulVec y = y := by
    refine eq_of_charVal_single fun j => ?_
    rw [charVal_dualMatrix, mem_dualWeylStabilizer.1 h, charVal_single]
  rw [dualMatrix_e7G0] at h1
  rw [one_smul]
  exact h1

theorem e7G0_fix
    {y : Fin Tag.E7.rank → ZMod 7}
    (h : e7G0 ∈ dualWeylStabilizer y) : y = ![0, y 1, 0, 0, 0, 0, 0] :=
  read7_fix (echelon7_aux e7T0_mul (e7G0_dualMatrix_fix h))

theorem e7_fix_count : ∀ a : ZMod 7, a ≠ 0 → e7Count7 ![0, a, 0, 0, 0, 0, 0] = 42 := by
  decide +kernel

theorem factorization_seven_e7 : (2903040 : ℕ).factorization 7 = 1 := by
  have h : (2903040 : ℕ) = 7 * 414720 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_fix_e7
    {z : Fin Tag.E7.rank → ZMod 7}
    (h7 : 7 ∣ Nat.card (dualWeylStabilizer z)) :
    ∃ (a : WeylGroup Tag.E7) (z' : Fin Tag.E7.rank → ZMod 7),
      (∀ x, charVal z' (a • x) = charVal z x) ∧ e7G0 ∈ dualWeylStabilizer z' := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype (WeylGroup Tag.E7) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hW : Nat.card (WeylGroup Tag.E7) = 2903040 :=
    (CFSG.RankThree.Chevalley.E7_weyl_length_polynomial).2
  have hfac : (Nat.card (WeylGroup Tag.E7)).factorization 7 = 1 := by
    rw [hW]
    exact factorization_seven_e7
  let P : Sylow 7 (WeylGroup Tag.E7) := Sylow.ofCard (Subgroup.zpowers (g : WeylGroup Tag.E7))
    (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg, hfac, pow_one])
  let P₀ : Sylow 7 (WeylGroup Tag.E7) := Sylow.ofCard (Subgroup.zpowers e7G0)
    (by rw [Nat.card_zpowers, orderOf_e7G0, hfac, pow_one])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E7) P₀ P
  have hmem : x * e7G0 * x⁻¹ ∈ dualWeylStabilizer z := by
    have h1 : e7G0 ∈ (P₀ : Subgroup (WeylGroup Tag.E7)) := Subgroup.mem_zpowers e7G0
    have h2 : (MulAut.conj x) e7G0 ∈ ((x • P₀ : Sylow 7 (WeylGroup Tag.E7)) :
        Subgroup (WeylGroup Tag.E7)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hx] at h2
    have h3 : (MulAut.conj x) e7G0 ∈ Subgroup.zpowers (g : WeylGroup Tag.E7) := h2
    rw [MulAut.conj_apply] at h3
    exact (Subgroup.zpowers_le.2 g.2) h3
  set z' : Fin Tag.E7.rank → ZMod 7 := fun i =>
    charVal z (x • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) with hz'
  have hz'x : ∀ y, charVal z' y = charVal z (x • y) := fun y => by
    rw [charVal_smul_eq_sum]
    rfl
  have hconj : ∀ y, charVal z' (x⁻¹ • y) = charVal z y := fun y => by
    rw [hz'x, smul_inv_smul]
  refine ⟨x⁻¹, z', hconj, ?_⟩
  have := (e7_mem_dualStab_conj hconj (x * e7G0 * x⁻¹)).1 hmem
  simpa [mul_assoc] using this

theorem charVal_zero_col_e7 (x : Fin Tag.E7.rank → ℤ) :
    charVal (0 : Fin Tag.E7.rank → ZMod 7) x = 0 := by
  simp [charVal]

theorem e7Fix_zero : (![0, 0, 0, 0, 0, 0, 0] : Fin Tag.E7.rank → ZMod 7) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem e7T3_seven_stab
    {z : Fin Tag.E7.rank → ZMod 7} (hz : z ≠ 0) {ρ : ZMod 7} (hρ : ρ ^ 2 + ρ + 1 = 0)
    (h : e7Wt7 *ᵥ z = ρ • z) : ¬ 7 ∣ Nat.card (dualWeylStabilizer z) := by
  intro h7
  obtain ⟨a, z', hz', hfix⟩ := exists_conj_fix_e7 h7
  have hcount : e7Count7 z' = e7Count7 z := e7Count7_transport hz'
  have hz'0 : z' ≠ 0 := by
    intro h0
    apply hz
    funext i
    rw [← charVal_single z i, ← hz', h0]
    exact charVal_zero_col_e7 _
  have hform := e7G0_fix hfix
  have hne : z' 1 ≠ 0 := by
    intro hcon
    apply hz'0
    rw [hform, hcon]
    exact e7Fix_zero
  have h1 := e7_fix_count (z' 1) hne
  rw [← hform] at h1
  have h2 := e7_eigen_count hz hρ h
  rw [← hcount, h1] at h2
  omega

theorem e7Wt7_of_eigencolumn {z : Fin Tag.E7.rank → ZMod 7} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (h : ((ε • e7T3W).map (Int.cast : ℤ → ZMod 7))ᵀ *ᵥ z = (q : ZMod 7) • z) :
    e7Wt7 *ᵥ z = ((ε : ZMod 7) * (q : ZMod 7)) • z := by
  rw [e7Wt7, ← e7T3W_eq]
  rcases hε with rfl | rfl
  · simpa using h
  · rw [neg_one_smul_map_transpose_mulVec] at h
    have h' : (e7T3W.map (Int.cast : ℤ → ZMod 7))ᵀ *ᵥ z = -((q : ZMod 7) • z) :=
      neg_eq_iff_eq_neg.1 h
    rw [h', Int.cast_neg, Int.cast_one, neg_one_mul]
    ext i
    change -((q : ZMod 7) * z i) = -(q : ZMod 7) * z i
    exact (neg_mul _ _).symm

theorem e7T3_dualStab_prime {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1)
    {z : Fin Tag.E7.rank → ZMod p} (hz : z ≠ 0)
    (hzM : ((ε • e7T3W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = (q : ZMod p) • z) :
    ¬ p ∣ Nat.card (dualWeylStabilizer z) := by
  obtain ⟨-, hx, -, -, -, -, hp7, -⟩ := e7T3_data hp hp3 hε hpq
  rcases hp7.lt_or_eq with h7 | h7
  · intro hdvd
    have : Fintype (WeylGroup Tag.E7) := Fintype.ofFinite _
    exact not_dvd_card_weylGroup_E hp h7 (Or.inr (Or.inl rfl))
      (hdvd.trans (Subgroup.card_subgroup_dvd_card _))
  · subst h7
    have hx' : ((ε : ZMod 7) * (q : ZMod 7)) ^ 2 + (ε : ZMod 7) * (q : ZMod 7) + 1 = 0 := hx
    exact e7T3_seven_stab hz hx' (e7Wt7_of_eigencolumn hε hzM)

section Main

variable {K : Type} [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L ℓ]

theorem e7T3_stabHyp {ε : ℤ} (F : E7ThreeFrame K L ℓ f p ε) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) :
    E7StabHyp F.n (iterateFrobenius L ℓ f) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro a hap ha1 haT
  have haF : a ∈ fixedCharTuples (ε • e7T3W) (iterateFrobenius L ℓ f) := by
    have h1 : rootDiagUnit .E7 a ∈ (fixedCharTuples (ε • e7T3W) (iterateFrobenius L ℓ f)).map
        (rootDiagUnitHom .E7 L) := by
      rw [← F.hT]
      exact haT
    obtain ⟨a', ha', ha'a⟩ := h1
    have : a' = a := rootDiagUnit_injective ha'a
    exact this ▸ ha'
  exact rootCharStabilizer_subset_closure_of_fixed (ε • e7T3W) (iterateFrobenius L ℓ f) hFr hp
    haF hap ha1 (fun z hz0 hzM =>
      (KE6.dualWeylStabilizer_eq_closure_of_card z
        (e7T3_dualStab_prime hp hp3 hε hpf hz0 hzM)).le)

end Main

end CFSG.RankThree.PartOne.KE
