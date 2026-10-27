module

public import CFSG.Quasithin.Background.SmithB49Act
public import CFSG.Quasithin.Background.SmithB49Fox

public section

namespace CFSG.Quasithin.B5.B49

open Matrix CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln
open scoped Kronecker

@[expose] def relsD4 : Fin 5 → List (Fin 2) :=
  ![
    [0, 0],
    [1, 1, 1, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]]

@[expose] def actD4 : Fin 2 → List ℕ :=
  ![
    [51, 34, 68, 136, 48, 32, 64, 128, 768, 512, 1024, 2048, 12288, 8192, 16384, 32768],
    [32768, 4096, 8192, 16384, 8, 1, 2, 4, 128, 16, 32, 64, 2048, 256, 512, 1024]]

@[expose] def certPD4 : Fin 2 → List ℕ :=
  ![
    [2, 4, 4096, 16391, 16391, 2, 4, 8, 8, 256, 2, 4, 4, 4096, 16391, 2],
    [32, 64, 4, 80, 64, 0, 0, 0, 256, 0, 1024, 2048, 66, 0, 88, 33]]

@[expose] def certCD4 : Fin 2 → Fin 5 → List ℕ :=
  ![
    ![
      [0, 0, 0, 0, 260, 16, 4, 8, 0, 256, 16, 260, 0, 4096, 0, 16],
      [0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2],
      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![
      [0, 0, 0, 0, 0, 0, 0, 268, 0, 272, 0, 0, 0, 268, 272, 0],
      [0, 0, 0, 0, 0, 0, 0, 14, 0, 9, 0, 0, 2, 10, 1, 1],
      [0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 4, 2, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0]]]

@[expose] def certFD4 : Fin 2 → List ℕ :=
  ![
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def certED4 : Fin 2 → List ℕ :=
  ![
    [16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def fD4 : Fin 2 → ℕ := ![18433, 0]

@[expose] def fvD4 (j : Fin 2) : Fin 4 × Fin 4 → ZMod 2 :=
  fun p => bitZ (fD4 j) (finProdFinEquiv p)

theorem actD4_spec (i : Fin 2) : decM finProdFinEquiv (actD4 i) = mats4 i ⊗ₖ mats4 i := by
  fin_cases i <;> decide +kernel

theorem relsD4_spec : ∀ r, wordEvalB 4 mats4B (relsD4 r) = bone 4 := by
  decide +kernel

theorem certD4_bits : ∀ j l, certL (4 * 4) actD4 certPD4 certFD4 certED4 j l =
    certR (4 * 4) actD4 relsD4 certCD4 j l := by
  decide +kernel

theorem certFD4_eq : ∀ j : Fin 2, decM finProdFinEquiv (certFD4 j) =
    Matrix.of fun p q => if q = (0, 0) then fvD4 j p else 0 := by
  decide +kernel

theorem certFD4_mulVec (j : Fin 2) (y : Fin 4 × Fin 4 → ZMod 2) :
    decM finProdFinEquiv (certFD4 j) *ᵥ y = y (0, 0) • fvD4 j := by
  rw [certFD4_eq]
  funext p
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem muK_sgen4_dmat (i : Fin 2) (v : Fin 4 × Fin 4 → ZMod 2) :
    muK (dmatHom 4) (sgen4 i) v = decM finProdFinEquiv (actD4 i) *ᵥ v := by
  rw [muK_apply, krM_sgen4_dmat, actD4_spec]

theorem h1D4 {c : ↥(StatedSL 4 (ZMod 2)) → (Fin 4 × Fin 4 → ZMod 2)}
    (hc : c ∈ Z1A (muK (dmatHom 4))) :
    c ∈ B1A (muK (dmatHom 4)) ∨
      ∃ x, ∀ j, (c - coboundaryA (muK (dmatHom 4)) x) (sgen4 j) = fvD4 j := by
  obtain ⟨x, y, hxy⟩ := exists_of_cert muK_sgen4_dmat (rels := relsD4)
    (fun r => wordEval_sgen4_eq_one (relsD4_spec r))
    (fun l => decM finProdFinEquiv (certPD4 l)) (fun j => decM finProdFinEquiv (certFD4 j))
    (fun l => decM finProdFinEquiv (certED4 l)) (fun j r => decM finProdFinEquiv (certCD4 j r))
    (cert_of_bits finProdFinEquiv actD4 certPD4 certFD4 certED4 relsD4 certCD4 certD4_bits) hc
  simp only [certFD4_mulVec] at hxy
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (y (0, 0)) with h0 | h1
  · left
    have hf' : c - coboundaryA (muK (dmatHom 4)) x ∈ Z1A (muK (dmatHom 4)) :=
      sub_mem hc (B1A_le_Z1A _ ⟨x, rfl⟩)
    have h0' := eq_zero_of_vanish_closure hf' closure_sgen4 (by
      rintro _ ⟨i, rfl⟩
      rw [hxy i, h0, zero_smul]
      rfl)
    have e : c = coboundaryA (muK (dmatHom 4)) x := sub_eq_zero.mp h0'
    rw [e]
    exact ⟨x, rfl⟩
  · right
    exact ⟨x, fun j => by rw [hxy j, h1, one_smul]⟩

@[expose] def qi (a : Fin 2) : Fin 4 := ⟨a, by omega⟩

@[expose] def qj (b : Fin 2) : Fin 4 := ⟨b + 2, by omega⟩

@[expose] def FmD4 : Fin 2 → Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![![!![1, 1, 0, 1; 1, 0, 0, 1; 0, 0, 0, 0; 1, 1, 0, 0],
      !![1, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 0]],
    ![!![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0],
      !![0, 1, 1, 0; 1, 1, 1, 0; 1, 1, 0, 0; 0, 0, 0, 0]]]

theorem cocD4_tw : ∀ a b : Fin 2,
    ∑ l, decM finProdFinEquiv (foxDB (4 * 4) actD4 (tw4 (qi a) (qj b)) l) *ᵥ fvD4 l =
      (FmD4 a b).vec := by
  decide +kernel

theorem offD4_check : ∀ (a b : ZMod 2) (x : Fin 4 → ZMod 2),
    (∀ i j : Fin 2, FmD4 i j *ᵥ ![0, 0, a, b] = (transvection (qi i) (qj j) 1 - 1) *ᵥ x) →
      a = 0 ∧ b = 0 := by
  decide +kernel

end CFSG.Quasithin.B5.B49
