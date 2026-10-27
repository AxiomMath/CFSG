module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_8_d

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_commutes_conj_of_commutator_centralizes_pre
    {x n y d : G} (hd : d = ⁅x, n⁆) (hxy : x * y = y * x)
    (hdz : d * (n * y * n⁻¹) = (n * y * n⁻¹) * d) :
    x * (n * y * n⁻¹) = (n * y * n⁻¹) * x := by
  subst d
  have hxn : x * n = ⁅x, n⁆ * n * x := by
    simp [commutatorElement_def, mul_assoc]
  have hxni : x * n⁻¹ = n⁻¹ * ⁅x, n⁆⁻¹ * x := by
    simp [commutatorElement_def, mul_assoc]
  calc
    x * (n * y * n⁻¹) = (x * n) * y * n⁻¹ := by simp [mul_assoc]
    _ = (⁅x, n⁆ * n * x) * y * n⁻¹ := by rw [hxn]
    _ = ⁅x, n⁆ * n * (x * y) * n⁻¹ := by simp [mul_assoc]
    _ = ⁅x, n⁆ * n * (y * x) * n⁻¹ := by rw [hxy]
    _ = ⁅x, n⁆ * n * y * (x * n⁻¹) := by simp [mul_assoc]
    _ = ⁅x, n⁆ * n * y * (n⁻¹ * ⁅x, n⁆⁻¹ * x) := by rw [hxni]
    _ = (⁅x, n⁆ * (n * y * n⁻¹) * ⁅x, n⁆⁻¹) * x := by simp [mul_assoc]
    _ = (n * y * n⁻¹) * x := by
      rw [show ⁅x, n⁆ * (n * y * n⁻¹) * ⁅x, n⁆⁻¹ = n * y * n⁻¹ by
        calc
          ⁅x, n⁆ * (n * y * n⁻¹) * ⁅x, n⁆⁻¹ =
              ((n * y * n⁻¹) * ⁅x, n⁆) * ⁅x, n⁆⁻¹ := by rw [hdz]
          _ = n * y * n⁻¹ := mul_inv_cancel_right (n * y * n⁻¹) ⁅x, n⁆]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_commutatorElement_mul_right_eq_of_central_pre
    {s d x : G} (hsd : s * d = d * s)
    (hcommd : ⁅s, x⁆ * d = d * ⁅s, x⁆) :
    ⁅s, d * x⁆ = ⁅s, x⁆ := by
  calc
    ⁅s, d * x⁆ = (s * d) * x * s⁻¹ * x⁻¹ * d⁻¹ := by
      simp [commutatorElement_def, mul_assoc]
    _ = (d * s) * x * s⁻¹ * x⁻¹ * d⁻¹ := by rw [hsd]
    _ = d * ⁅s, x⁆ * d⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = ⁅s, x⁆ := by
      rw [← hcommd]
      simp [mul_assoc]

/-- Lemma 12.8(f). -/
public theorem CFSG.lemma_12_8_f
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∀ X : Subgroup G, X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      section10NormalIn (subgroupCentralizerIn (S : Subgroup G) X)
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      section10NormalIn (⁅(S : Subgroup G), X⁆)
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) := by
  classical
  intro X hXN'
  let N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let C : Subgroup G := Subgroup.centralizer ((S : Subgroup G) : Set G)
  have hXN : X ≤ N := by simpa [N] using hXN'
  have h8c :=
    lemma_12_8_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have hD_le_C : ambientDerivedSubgroup N ≤ C := by
    simpa [N, C] using h8c.2.1.trans h8c.2.2.1
  have hS_le_N : (S : Subgroup G) ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := (S : Subgroup G)))
  have hSX_le_S : ⁅(S : Subgroup G), X⁆ ≤ (S : Subgroup G) := by
    simpa [N] using
      section12_commutator_le_left_of_le_normalizer_pre
        (G := G) (K := (S : Subgroup G)) (A := X) hXN
  have hCSX_le_N : subgroupCentralizerIn (S : Subgroup G) X ≤ N := by
    intro y hy
    exact hS_le_N
      ((show subgroupCentralizerIn (S : Subgroup G) X ≤ (S : Subgroup G) from inf_le_left) hy)
  have hSX_le_N : ⁅(S : Subgroup G), X⁆ ≤ N := hSX_le_S.trans hS_le_N
  have hconj_C {n y : G} (hn : n ∈ N)
      (hy : y ∈ subgroupCentralizerIn (S : Subgroup G) X) :
      n * y * n⁻¹ ∈ subgroupCentralizerIn (S : Subgroup G) X := by
    rcases (by simpa [subgroupCentralizerIn] using hy) with ⟨hyS, hyC⟩
    have hzS : n * y * n⁻¹ ∈ (S : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (by simpa [N] using hn) y).1 hyS
    have hzC : n * y * n⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxN : x ∈ N := hXN hx
      let d : G := ⁅x, n⁆
      have hdD : d ∈ ambientDerivedSubgroup N := by
        have hdcomm : d ∈ ⁅N, N⁆ :=
          Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := N) hxN hn
        simpa [d, section12_ambientDerivedSubgroup_eq_commutator] using hdcomm
      have hdC : d ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        simpa [C] using hD_le_C hdD
      have hxy : x * y = y * x :=
        (Subgroup.mem_centralizer_iff.mp hyC) x hx
      have hdz : d * (n * y * n⁻¹) = (n * y * n⁻¹) * d :=
        ((Subgroup.mem_centralizer_iff.mp hdC) (n * y * n⁻¹) hzS).symm
      exact section12_commutes_conj_of_commutator_centralizes_pre
        (G := G) (x := x) (n := n) (y := y) (d := d) rfl hxy hdz
    simpa [subgroupCentralizerIn] using ⟨hzS, hzC⟩
  have hCSX_norm_N :
      N ≤ Subgroup.normalizer (subgroupCentralizerIn (S : Subgroup G) X : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj_C hn
    · intro hy
      have hy' := hconj_C (N.inv_mem hn) hy
      simpa [mul_assoc] using hy'
  have hconj_SX {n y : G} (hn : n ∈ N) (hy : y ∈ ⁅(S : Subgroup G), X⁆) :
      n * y * n⁻¹ ∈ ⁅(S : Subgroup G), X⁆ := by
    let T : Set G := {g : G | ∃ s ∈ (S : Subgroup G), ∃ x ∈ X, ⁅s, x⁆ = g}
    have hyT : y ∈ Subgroup.closure T := by
      simpa [Subgroup.commutator_def, T] using hy
    have hgen : ∀ z, z ∈ T → n * z * n⁻¹ ∈ Subgroup.closure T := by
      intro z hz
      rcases hz with ⟨s, hsS, x, hxX, rfl⟩
      have hnsS : n * s * n⁻¹ ∈ (S : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp (by simpa [N] using hn) s).1 hsS
      have hxN : x ∈ N := hXN hxX
      let d : G := ⁅n, x⁆
      have hdD : d ∈ ambientDerivedSubgroup N := by
        have hdcomm : d ∈ ⁅N, N⁆ :=
          Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := N) hn hxN
        simpa [d, section12_ambientDerivedSubgroup_eq_commutator] using hdcomm
      have hdC : d ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        simpa [C] using hD_le_C hdD
      have hnx : n * x * n⁻¹ = d * x := by
        simp [d, commutatorElement_def, mul_assoc]
      have hs'd : (n * s * n⁻¹) * d = d * (n * s * n⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hdC) (n * s * n⁻¹) hnsS
      have hcomm_sx_S : ⁅n * s * n⁻¹, x⁆ ∈ (S : Subgroup G) :=
        hSX_le_S (Subgroup.commutator_mem_commutator (H₁ := (S : Subgroup G))
          (H₂ := X) hnsS hxX)
      have hcommd : ⁅n * s * n⁻¹, x⁆ * d = d * ⁅n * s * n⁻¹, x⁆ :=
        (Subgroup.mem_centralizer_iff.mp hdC) ⁅n * s * n⁻¹, x⁆ hcomm_sx_S
      have heq : ⁅n * s * n⁻¹, d * x⁆ = ⁅n * s * n⁻¹, x⁆ :=
        section12_commutatorElement_mul_right_eq_of_central_pre
          (G := G) hs'd hcommd
      have hconj_eq :
          n * ⁅s, x⁆ * n⁻¹ = ⁅n * s * n⁻¹, x⁆ := by
        calc
          n * ⁅s, x⁆ * n⁻¹ = ⁅n * s * n⁻¹, n * x * n⁻¹⁆ := by
            rw [conjugate_commutatorElement]
          _ = ⁅n * s * n⁻¹, d * x⁆ := by rw [hnx]
          _ = ⁅n * s * n⁻¹, x⁆ := heq
      rw [hconj_eq]
      exact Subgroup.subset_closure ⟨n * s * n⁻¹, hnsS, x, hxX, rfl⟩
    have hclosed : n * y * n⁻¹ ∈ Subgroup.closure T :=
      Subgroup.closure_induction (k := T)
        (p := fun z _hz => n * z * n⁻¹ ∈ Subgroup.closure T)
        (mem := hgen) (one := by simp)
        (mul := by
          intro a b _ha _hb ha hb
          simpa [mul_assoc] using (Subgroup.closure T).mul_mem ha hb)
        (inv := by
          intro a _ha ha
          simpa [mul_assoc] using (Subgroup.closure T).inv_mem ha)
        hyT
    simpa [Subgroup.commutator_def, T] using hclosed
  have hSX_norm_N :
      N ≤ Subgroup.normalizer ((⁅(S : Subgroup G), X⁆ : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj_SX hn
    · intro hy
      have hy' := hconj_SX (N.inv_mem hn) hy
      simpa [mul_assoc] using hy'
  have hCSX_normalIn :
      section10NormalIn (subgroupCentralizerIn (S : Subgroup G) X) N := by
    refine ⟨hCSX_le_N, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := subgroupCentralizerIn (S : Subgroup G) X) (K := N) hCSX_le_N).2 hCSX_norm_N
  have hSX_normalIn : section10NormalIn (⁅(S : Subgroup G), X⁆) N := by
    refine ⟨hSX_le_N, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := ⁅(S : Subgroup G), X⁆) (K := N) hSX_le_N).2 hSX_norm_N
  exact ⟨by simpa [N] using hCSX_normalIn, by simpa [N] using hSX_normalIn⟩


end Section12
