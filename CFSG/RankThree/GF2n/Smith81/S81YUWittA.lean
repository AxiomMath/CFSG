module

public import CFSG.RankThree.GF2n.Smith81.S81XUWitt
public import CFSG.RankThree.GF2n.Smith81.S81YGenDef

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  Matrix exteriorPower
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.RootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

private theorem u6w2_inv_mul (g : SUid σ 6) :
    (((g⁻¹ : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
  rw [Subgroup.coe_inv]
  exact Units.inv_mul _

theorem u6_witt_two (hσ : IsUnitaryInvolution σ) {u u' : Fin 3 → Fin 6 → F}
    (hu : ιMulti F 3 u ≠ 0) (hiu : ∀ i j, ∑ k, σ (u i k) * u j k = 0)
    (hu' : ιMulti F 3 u' ≠ 0) (hiu' : ∀ i j, ∑ k, σ (u' i k) * u' j k = 0) :
    ∃ h : SUid σ 6, ∃ l : F, l ≠ 0 ∧
      ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (u 0) = l • u' 0 ∧
      ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (u 1) = u' 1 ∧
      ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (u 2) = u' 2 := by
  obtain ⟨g₁, l₁, hl₁, h₁0, h₁1, h₁2⟩ := u6_exists_su_of_ti hσ hu hiu
  obtain ⟨g₂, l₂, hl₂, h₂0, h₂1, h₂2⟩ := u6_exists_su_of_ti hσ hu' hiu'
  have hN : ∀ x : Fin 6 → F,
      (((g₁⁻¹ : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec
        (((g₁ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, u6w2_inv_mul g₁, Matrix.one_mulVec]
  have hA1 : (((g₁⁻¹ : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (u 1) =
      e3uT0Vec 1 := by
    rw [← h₁1]
    exact hN _
  have hA2 : (((g₁⁻¹ : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (u 2) =
      e3uT0Vec 2 := by
    rw [← h₁2]
    exact hN _
  have hB0 : (((g₁⁻¹ : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (u 0) =
      l₁⁻¹ • e3uT0Vec 0 := by
    have h := hN (e3uT0Vec 0)
    rw [h₁0, Matrix.mulVec_smul] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hl₁, one_smul]
  refine ⟨g₂ * g₁⁻¹, l₁⁻¹ * l₂, mul_ne_zero (inv_ne_zero hl₁) hl₂, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hB0, Matrix.mulVec_smul, h₂0,
      smul_smul]
  · rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hA1, h₂1]
  · rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hA2, h₂2]

private theorem ordered_basis_core {v : Fin 3 → Fin 6 → F} (hv : LinearIndependent F v)
    {a : Fin 6 → F} {α : Fin 3 → F} (hα : ∑ l, α l • v l = a) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hcov : ∀ l, l = i ∨ l = j ∨ l = k)
    (hi : α i ≠ 0) :
    LinearIndependent F ![v j, a, v k] ∧ ∀ l, v l ∈ Submodule.span F {v j, a, v k} := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, k} := by
    ext l
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcov l
  have hdec : ∀ f : Fin 3 → Fin 6 → F, ∑ l, f l = f i + (f j + f k) := by
    intro f
    rw [huniv, Finset.sum_insert (show i ∉ ({j, k} : Finset (Fin 3)) by simp [hij, hik]),
      Finset.sum_pair hjk]
  have hsum : α i • v i + (α j • v j + α k • v k) = a := by
    have h : ∑ l, α l • v l = α i • v i + (α j • v j + α k • v k) :=
      hdec (fun l => α l • v l)
    exact h.symm.trans hα
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • v j + g 1 • a + g 2 • v k = 0 := by
      simpa [Fin.sum_univ_three] using hg
    rw [← hsum] at hg'
    obtain ⟨c, hc_def⟩ : ∃ c : Fin 3 → F,
        c = fun l => g 1 * α l + (if l = j then g 0 else 0) + (if l = k then g 2 else 0) :=
      ⟨_, rfl⟩
    have hci : c i = g 1 * α i := by
      rw [hc_def]
      simp [hij, hik]
    have hcj : c j = g 1 * α j + g 0 := by
      rw [hc_def]
      simp [hjk]
    have hck : c k = g 1 * α k + g 2 := by
      rw [hc_def]
      simp [Ne.symm hjk]
    have hcsum : ∑ l, c l • v l = 0 := by
      have hd : ∑ l, c l • v l = c i • v i + (c j • v j + c k • v k) :=
        hdec (fun l => c l • v l)
      rw [hd, hci, hcj, hck]
      linear_combination (norm := module) hg'
    have hcl := Fintype.linearIndependent_iff.mp hv c hcsum
    have hg1 : g 1 = 0 := by
      have h1 : g 1 * α i = 0 := by
        rw [← hci]
        exact hcl i
      exact (mul_eq_zero.mp h1).resolve_right hi
    have hg0 : g 0 = 0 := by
      have h1 : g 1 * α j + g 0 = 0 := by
        rw [← hcj]
        exact hcl j
      rwa [hg1, zero_mul, zero_add] at h1
    have hg2 : g 2 = 0 := by
      have h1 : g 1 * α k + g 2 = 0 := by
        rw [← hck]
        exact hcl k
      rwa [hg1, zero_mul, zero_add] at h1
    intro l
    fin_cases l <;> simp [hg0, hg1, hg2]
  · have hmem_a : a ∈ Submodule.span F ({v j, a, v k} : Set (Fin 6 → F)) :=
      Submodule.subset_span (by simp)
    have hmem_j : v j ∈ Submodule.span F ({v j, a, v k} : Set (Fin 6 → F)) :=
      Submodule.subset_span (by simp)
    have hmem_k : v k ∈ Submodule.span F ({v j, a, v k} : Set (Fin 6 → F)) :=
      Submodule.subset_span (by simp)
    have hvi : v i = (α i)⁻¹ • (a - α j • v j - α k • v k) := by
      rw [← hsum]
      have h' : α i • v i + (α j • v j + α k • v k) - α j • v j - α k • v k = α i • v i := by
        abel
      rw [h', inv_smul_smul₀ hi]
    intro l
    rcases hcov l with h | h | h
    · rw [h, hvi]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.sub_mem _ hmem_a (Submodule.smul_mem _ _ hmem_j)) (Submodule.smul_mem _ _ hmem_k))
    · rw [h]
      exact hmem_j
    · rw [h]
      exact hmem_k

theorem exists_ordered_basis {v : Fin 3 → Fin 6 → F} (hv : LinearIndependent F v)
    {a : Fin 6 → F} (ha : a ≠ 0) (hav : a ∈ Submodule.span F (Set.range v)) :
    ∃ X Y : Fin 6 → F, X ∈ Submodule.span F (Set.range v) ∧ Y ∈ Submodule.span F (Set.range v) ∧
      LinearIndependent F ![X, a, Y] ∧ ∀ i, v i ∈ Submodule.span F {X, a, Y} := by
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hav
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 3, α i₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply ha
    rw [← hα]
    simp [hcon]
  have hperm : ∀ i : Fin 3, i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 ∧
      ∀ l : Fin 3, l = i ∨ l = i + 1 ∨ l = i + 2 := by
    decide
  obtain ⟨h1, h2, h3, h4⟩ := hperm i₀
  obtain ⟨hli, hspan⟩ := ordered_basis_core hv hα h1 h2 h3 h4 hi₀
  exact ⟨v (i₀ + 1), v (i₀ + 2), Submodule.subset_span (Set.mem_range_self _),
    Submodule.subset_span (Set.mem_range_self _), hli, hspan⟩

end CFSG.RankThree.GF2n.Smith81.RootGenU
