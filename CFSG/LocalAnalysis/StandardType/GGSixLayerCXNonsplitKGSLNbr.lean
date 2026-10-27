module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSL
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLMark

public section

namespace CFSG.StandardType

namespace LinNonsplit

open CFSG.Assembly CFSG.RankThree.PartOne.KCLinComm Matrix LayerFacts

section Corner

variable {F : Type*} [Field F] {n : ℕ}

theorem mul_single_mul_apply (M N : Matrix (Fin n) (Fin n) F) (k l i j : Fin n) :
    (M * Matrix.single k l (1 : F) * N : Matrix (Fin n) (Fin n) F) i j = M i k * N l j := by
  classical
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem exists_eq_smul_of_commute_corner {P z : Matrix (Fin n) (Fin n) F} (hP : P ≠ 0)
    (hPz : P * z = z) (hzP : z * P = z)
    (hc : ∀ M : Matrix (Fin n) (Fin n) F, z * (P * M * P) = P * M * P * z) :
    ∃ c : F, z = c • P := by
  classical
  have key : ∀ i k l j, z i k * P l j = P i k * z l j := by
    intro i k l j
    have h := congrFun (congrFun (hc (Matrix.single k l (1 : F))) i) j
    have e1 : (z * (P * Matrix.single k l (1 : F) * P) : Matrix (Fin n) (Fin n) F) i j =
        z i k * P l j := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hzP, mul_single_mul_apply]
    have e2 : (P * Matrix.single k l (1 : F) * P * z : Matrix (Fin n) (Fin n) F) i j =
        P i k * z l j := by
      rw [Matrix.mul_assoc _ P z, hPz, mul_single_mul_apply]
    rw [← e1, ← e2, h]
  obtain ⟨l, j, hlj⟩ : ∃ l j, P l j ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Matrix.ext h)
  refine ⟨z l j / P l j, Matrix.ext fun i k => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  field_simp
  linear_combination key i k l j

variable {r : ℕ} {D : Fin r → Type*} {d : Fin r → ℕ} [∀ i, Field (D i)] [∀ i, Algebra F (D i)]

theorem algebraMap_surjective_of_corner
    (Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F)
    (hΦinj : Function.Injective Φ) {A : Matrix (Fin n) (Fin n) F}
    (hrange : ∀ X : Matrix (Fin n) (Fin n) F, X * A = A * X → X ∈ Set.range Φ)
    {b : Fin r} (hd : NeZero (d b))
    (h1 : Φ (Pi.single b 1) * A = Φ (Pi.single b 1))
    (h2 : A * Φ (Pi.single b 1) = Φ (Pi.single b 1)) :
    Function.Surjective (algebraMap F (D b)) := by
  classical
  set e : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single b 1 with he
  set P := Φ e with hP
  intro t
  set c : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single b (t • 1) with hcdef
  have hcen : ∀ w, c * w = w * c := by
    intro w
    funext i
    by_cases hi : i = b
    · subst hi
      simp [hcdef]
    · simp [hcdef, hi]
  have hec : e * c = c := by
    funext i
    by_cases hi : i = b
    · subst hi
      simp [he, hcdef]
    · simp [he, hcdef, hi]
  have hce : c * e = c := by
    funext i
    by_cases hi : i = b
    · subst hi
      simp [he, hcdef]
    · simp [he, hcdef, hi]
  have hPne : P ≠ 0 := by
    intro h
    have h0 : e = 0 := hΦinj (by rw [← hP, h, map_zero])
    have h00 := congrFun h0 b
    simp [he] at h00
  obtain ⟨c₀, hc₀⟩ := exists_eq_smul_of_commute_corner hPne (z := Φ c)
    (by rw [hP, ← map_mul, hec]) (by rw [hP, ← map_mul, hce]) fun M => by
      obtain ⟨w, hw⟩ := hrange (P * M * P) (by
        rw [Matrix.mul_assoc (P * M) P A, h1, ← Matrix.mul_assoc A (P * M) P,
          ← Matrix.mul_assoc A P M, h2])
      rw [← hw, ← map_mul, ← map_mul, hcen]
  refine ⟨c₀, ?_⟩
  have h3 : c = c₀ • e := hΦinj (by rw [hc₀, map_smul])
  have h4 := congrFun h3 b
  simp only [hcdef, he, Pi.single_eq_same, Pi.smul_apply] at h4
  have i₀ : Fin (d b) := ⟨0, Nat.pos_of_ne_zero hd.ne⟩
  have h5 := congrFun (congrFun h4 i₀) i₀
  simp [Algebra.smul_def] at h5
  exact h5.symm

theorem card_eq_of_corner
    (Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F)
    (hΦinj : Function.Injective Φ) {A : Matrix (Fin n) (Fin n) F}
    (hrange : ∀ X : Matrix (Fin n) (Fin n) F, X * A = A * X → X ∈ Set.range Φ)
    {b : Fin r} (hd : NeZero (d b))
    (h1 : Φ (Pi.single b 1) * A = Φ (Pi.single b 1))
    (h2 : A * Φ (Pi.single b 1) = Φ (Pi.single b 1)) :
    Nat.card (D b) = Nat.card F :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap F (D b)).injective,
    algebraMap_surjective_of_corner Φ hΦinj hrange hd h1 h2⟩)).symm

end Corner

section Orders

theorem card_SL_two_le {D D' : Type*} [Field D] [Field D'] [Finite D] [Finite D']
    (hDD : Nat.card D = Nat.card D') {k : ℕ} (hk : 2 ≤ k) :
    Nat.card (SpecialLinearGroup (Fin 2) D) ≤ Nat.card (SpecialLinearGroup (Fin k) D') := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), hDD]
  have hq : 1 < Nat.card D' := Finite.one_lt_card
  refine Nat.mul_le_mul (Nat.pow_le_pow_right (by omega)
    (Nat.div_le_div_right (Nat.mul_le_mul hk (by omega)))) ?_
  refine Finset.prod_le_prod_of_subset_of_one_le (Finset.Icc_subset_Icc le_rfl hk) ?_
  intro j hj _
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have := Nat.one_lt_pow (by omega : j ≠ 0) hq
  omega

theorem card_SL_le_of_eq_two {D D' : Type*} [Field D] [Field D'] [Finite D] [Finite D']
    (hDD : Nat.card D = Nat.card D') {n k : ℕ} (hn : n = 2) (hk : 2 ≤ k) :
    Nat.card (SpecialLinearGroup (Fin n) D) ≤ Nat.card (SpecialLinearGroup (Fin k) D') := by
  subst hn
  exact card_SL_two_le hDD hk

theorem seven_dvd_card_SL {D : Type*} [Field D] [Finite D] (hD : Nat.card D = 2) {k : ℕ}
    (hk : 3 ≤ k) : 7 ∣ Nat.card (SpecialLinearGroup (Fin k) D) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), hD]
  have h := Finset.dvd_prod_of_mem (fun j => 2 ^ j - 1) (Finset.mem_Icc.2 ⟨(by norm_num : 2 ≤ 3), hk⟩)
  norm_num at h
  exact h.mul_left _

end Orders

section BlockNbr

variable {m : ℕ} {F : Type} [Field F]

theorem not_ggNbrClauseFiveMarking_block {G : Type} [Group G] [Finite G] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {D₀ : Type} [Field D₀] [Finite D₀] (hD₀ : Nat.card D₀ = Nat.card F)
    (hgood : 3 ≤ n₀ ∨ ∃ s : Finset D₀, s.card = 4)
    {β : SpecialLinearGroup (Fin n₀) D₀ →* SpecialLinearGroup (Fin (m + 1)) F}
    (hβinj : Function.Injective β) {x : G} {A : GL (Fin (m + 1)) F}
    (hA : (x, A) ∈ LinFusion.ggInducedPairs ψ) {u₀ : GL (Fin n₀) D₀}
    (hconj : ∀ s t : SpecialLinearGroup (Fin n₀) D₀,
      (t : Matrix (Fin n₀) (Fin n₀) D₀) = (u₀ : Matrix (Fin n₀) (Fin n₀) D₀) *
        (s : Matrix (Fin n₀) (Fin n₀) D₀) * ((u₀⁻¹ : GL (Fin n₀) D₀) : Matrix (Fin n₀) (Fin n₀) D₀) →
      SpecialLinearGroup.toGL (β t) = A * SpecialLinearGroup.toGL (β s) * A⁻¹)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    (h7 : f = 1 → p ≠ 7)
    (hcent : n₀ = 2 → x ∈ Subgroup.centralizer ((β.range.map ψ : Subgroup G) : Set G)) :
    ¬ GGNbrClauseFiveMarking p x (β.range.map ψ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
  have hD₀' : Nat.card D₀ = 2 ^ f := hD₀.trans hF
  have hrange : (ψ.comp β).range = β.range.map ψ := MonoidHom.range_comp ψ β
  have hker' : (ψ.comp β).ker ≤ Subgroup.center (SpecialLinearGroup (Fin (k + 1)) D₀) := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro t
    have hβs : β s ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := hker hs
    apply hβinj
    rw [map_mul, map_mul, Subgroup.mem_center_iff.mp hβs (β t)]
  have hu : (x, u₀) ∈ LinFusion.ggInducedPairs (ψ.comp β) := by
    intro s
    show x * ψ (β s) * x⁻¹ = ψ (β (InnerDiagA.conjSL u₀ s))
    rw [LinFusion.mem_ggInducedPairs.mp hA (β s)]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [LayerFacts.toGL_conjSL, hconj s _ (InnerDiagA.coe_conjSL u₀ s)]
  have hk1 : k = 1 → 2 ≤ f := by
    intro hk1
    rcases hgood with h | ⟨s, hs⟩
    · omega
    · have h4 : 4 ≤ Nat.card D₀ := by
        have := Fintype.ofFinite D₀
        rw [Nat.card_eq_fintype_card, ← hs]
        exact Finset.card_le_univ s
      rw [hD₀'] at h4
      by_contra hf2
      obtain rfl : f = 1 := by omega
      norm_num at h4
  rw [← hrange]
  exact not_ggNbrClauseFiveMarking_sl (by omega) hf hD₀' hk1 hker' hp hp2 hq1 hq2 h7 hu
    (fun hk => hrange ▸ hcent (by omega))

end BlockNbr

end LinNonsplit

end CFSG.StandardType
