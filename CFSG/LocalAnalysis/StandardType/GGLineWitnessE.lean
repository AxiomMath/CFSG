module

public import CFSG.LocalAnalysis.StandardType.GGLineWitnessData
public import CFSG.LocalAnalysis.StandardType.GGLatticeWitnessE
public import CFSG.LocalAnalysis.StandardType.GGLatticeWitnessF4

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lwle_line_E6_k2_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 6) (2 : Fin 6))) 6 lwe_E6R [] 6
      [2, 3, 0, 2, 6, 4, 5, 3, 4, 2, 3] 1 1 = true := by
  decide +kernel

private theorem lwle_line_E6_k3_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 6) (3 : Fin 6))) 6 lwe_E6R [] 6
      [3, 4, 2, 3, 6, 5, 4, 3] 1 0 = true := by
  decide +kernel

private theorem lwle_line_E6_k4_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 6) (4 : Fin 6))) 6 lwe_E6R [] 6
      [4, 5, 3, 4, 6, 2, 3, 4, 1, 3, 2] 0 1 = true := by
  decide +kernel

theorem ggLineTest_E6_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} (e : Fin 6 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)
    (hc : c = e 2 ∨ c = e 3 ∨ c = e 4) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    GGLineTest (ggAttachCartan C c) p := by
  rcases hc with hc | hc | hc
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 6) 2 (by decide) lwe_E6R [] 6
        [2, 3, 0, 2, 6, 4, 5, 3, 4, 2, 3] 1 1 lwe_E6R_closed lwe_cell_E6_k2_u0
        lwle_line_E6_k2_u0 hp h5)
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 6) 3 (by decide) lwe_E6R [] 6
        [3, 4, 2, 3, 6, 5, 4, 3] 1 0 lwe_E6R_closed lwe_cell_E6_k3_u0 lwle_line_E6_k3_u0
        hp h5)
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 6) 4 (by decide) lwe_E6R [] 6
        [4, 5, 3, 4, 6, 2, 3, 4, 1, 3, 2] 0 1 lwe_E6R_closed lwe_cell_E6_k4_u0
        lwle_line_E6_k4_u0 hp h5)

private theorem lwle_line_E7_k2_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (2 : Fin 7))) 7 lwe_E7R [] 7
      [2, 3, 0, 2, 7, 4, 5, 3, 4, 2, 3] 1 1 = true := by
  decide +kernel

private theorem lwle_line_E7_k3_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (3 : Fin 7))) 7 lwe_E7R [] 7
      [3, 4, 2, 3, 7, 5, 4, 3] 1 0 = true := by
  decide +kernel

private theorem lwle_line_E7_k5_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (5 : Fin 7))) 7 lwe_E7R [] 7
      [5, 6, 4, 5, 7, 3, 4, 5, 2, 3, 4, 1, 3, 2] 0 1 = true := by
  decide +kernel

theorem ggLineTest_E7_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} (e : Fin 7 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j)
    (hc : c = e 2 ∨ c = e 3 ∨ c = e 5) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    GGLineTest (ggAttachCartan C c) p := by
  rcases hc with hc | hc | hc
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 7) 2 (by decide) lwe_E7R [] 7
        [2, 3, 0, 2, 7, 4, 5, 3, 4, 2, 3] 1 1 lwe_E7R_closed lwe_cell_E7_k2_u0
        lwle_line_E7_k2_u0 hp h5)
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 7) 3 (by decide) lwe_E7R [] 7
        [3, 4, 2, 3, 7, 5, 4, 3] 1 0 lwe_E7R_closed lwe_cell_E7_k3_u0 lwle_line_E7_k3_u0
        hp h5)
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 7) 5 (by decide) lwe_E7R [] 7
        [5, 6, 4, 5, 7, 3, 4, 5, 2, 3, 4, 1, 3, 2] 0 1 lwe_E7R_closed lwe_cell_E7_k5_u0
        lwle_line_E7_k5_u0 hp h5)

private theorem lwle_line_E7_k1_u1 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (1 : Fin 7))) 7 lwe_E7R [] 7
      [1, 3, 4, 2, 3, 1, 7, 5, 6, 4, 5, 3, 4, 1, 3, 2] 0 0 = true := by
  decide +kernel

theorem ggLineTest_E7_cell_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} (e : Fin 7 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) (hb : b = e 1)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : GGLineTest (ggAttachCartan C b) p := by
  exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hb)
    (ggLineTest_of_data (CartanMatrix.E 7) 1 (by decide) lwe_E7R [] 7
      [1, 3, 4, 2, 3, 1, 7, 5, 6, 4, 5, 3, 4, 1, 3, 2] 0 0 lwe_E7R_closed lwe_cell_E7_k1_u1
      lwle_line_E7_k1_u1 hp h5)

private theorem lwle_line_E8_k2_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (2 : Fin 8))) 8 lwe_E8R [] 8
      [2, 3, 0, 2, 8, 4, 5, 3, 4, 2, 3] 1 1 = true := by
  decide +kernel

private theorem lwle_line_E8_k3_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (3 : Fin 8))) 8 lwe_E8R [] 8
      [3, 4, 1, 3, 8, 5, 4, 3] 2 0 = true := by
  decide +kernel

private theorem lwle_line_E8_k6_u0 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (6 : Fin 8))) 8 lwe_E8R [] 8
      [6, 7, 5, 6, 8, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2] 0 1 = true := by
  decide +kernel

theorem ggLineTest_E8_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} (e : Fin 8 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j)
    (hc : c = e 2 ∨ c = e 3 ∨ c = e 6) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    GGLineTest (ggAttachCartan C c) p := by
  rcases hc with hc | hc | hc
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 8) 2 (by decide) lwe_E8R [] 8
        [2, 3, 0, 2, 8, 4, 5, 3, 4, 2, 3] 1 1 lwe_E8R_closed lwe_cell_E8_k2_u0
        lwle_line_E8_k2_u0 hp h5)
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 8) 3 (by decide) lwe_E8R [] 8
        [3, 4, 1, 3, 8, 5, 4, 3] 2 0 lwe_E8R_closed lwe_cell_E8_k3_u0 lwle_line_E8_k3_u0
        hp h5)
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggLineTest_of_data (CartanMatrix.E 8) 6 (by decide) lwe_E8R [] 8
        [6, 7, 5, 6, 8, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2] 0 1 lwe_E8R_closed lwe_cell_E8_k6_u0
        lwle_line_E8_k6_u0 hp h5)

private theorem lwle_line_E8_k0_u1 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (0 : Fin 8))) 8 lwe_E8R [] 8
      [0, 2, 3, 4, 1, 3, 2, 0, 8, 5, 6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2] 0 0 = true := by
  decide +kernel

private theorem lwle_line_E8_k1_u1 :
    ggLWlinedata (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (1 : Fin 8))) 8 lwe_E8R [] 8
      [1, 3, 4, 2, 3, 1, 8, 5, 6, 4, 5, 3, 4, 1, 3, 2] 0 0 = true := by
  decide +kernel

theorem ggLineTest_E8_cell_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} (e : Fin 8 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j)
    (hb : b = e 0 ∨ b = e 1) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    GGLineTest (ggAttachCartan C b) p := by
  rcases hb with hb | hb
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hb)
      (ggLineTest_of_data (CartanMatrix.E 8) 0 (by decide) lwe_E8R [] 8
        [0, 2, 3, 4, 1, 3, 2, 0, 8, 5, 6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2] 0 0
        lwe_E8R_closed lwe_cell_E8_k0_u1 lwle_line_E8_k0_u1 hp h5)
  · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hb)
      (ggLineTest_of_data (CartanMatrix.E 8) 1 (by decide) lwe_E8R [] 8
        [1, 3, 4, 2, 3, 1, 8, 5, 6, 4, 5, 3, 4, 1, 3, 2] 0 0 lwe_E8R_closed lwe_cell_E8_k1_u1
        lwle_line_E8_k1_u1 hp h5)

private theorem lwle_line_F4_k1 :
    ggLWlinedata (ggLWmat (ggAttachCartan CartanMatrix.F₄ (1 : Fin 4))) 4 lwf_F4R [4, 2] 1
      [1, 4, 3, 1, 2, 1] 0 0 = true := by
  decide +kernel

private theorem lwle_line_F4_k2 :
    ggLWlinedata (ggLWmat (ggAttachCartan CartanMatrix.F₄ (2 : Fin 4))) 4 lwf_F4R [4, 3] 2
      [4, 2, 1, 2, 4, 0, 1] 2 1 = true := by
  decide +kernel

private theorem lwle_line_F4T_k1 :
    ggLWlinedata (ggLWmat (ggAttachCartan (Matrix.transpose CartanMatrix.F₄) (1 : Fin 4))) 4
      lwf_F4TR [4, 2] 1 [1, 4, 3, 1, 2, 1] 0 0 = true := by
  decide +kernel

private theorem lwle_line_F4T_k2 :
    ggLWlinedata (ggLWmat (ggAttachCartan (Matrix.transpose CartanMatrix.F₄) (2 : Fin 4))) 4
      lwf_F4TR [4, 3] 2 [4, 2, 1, 2, 4, 0, 1] 2 1 = true := by
  decide +kernel

theorem ggLineTest_F4_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} (e : Fin 4 ≃ Λ)
    (hC : (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i))
    (hc : c = e 1 ∨ c = e 2) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    GGLineTest (ggAttachCartan C c) p := by
  rcases hC with hC | hC
  · rcases hc with hc | hc
    · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
        (ggLineTest_of_data CartanMatrix.F₄ (1 : Fin 4) (by decide) lwf_F4R [4, 2] 1
          [1, 4, 3, 1, 2, 1] 0 0 lwf_F4R_closed lwf_cell_F4_k1 lwle_line_F4_k1 hp h5)
    · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC hc)
        (ggLineTest_of_data CartanMatrix.F₄ (2 : Fin 4) (by decide) lwf_F4R [4, 3] 2
          [4, 2, 1, 2, 4, 0, 1] 2 1 lwf_F4R_closed lwf_cell_F4_k2 lwle_line_F4_k2 hp h5)
  · have hC' : ∀ i j, C (e i) (e j) = (Matrix.transpose CartanMatrix.F₄) i j := by
      intro i j
      rw [Matrix.transpose_apply]
      exact hC i j
    rcases hc with hc | hc
    · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC' hc)
        (ggLineTest_of_data (Matrix.transpose CartanMatrix.F₄) (1 : Fin 4) (by decide)
          lwf_F4TR [4, 2] 1 [1, 4, 3, 1, 2, 1] 0 0 lwf_F4TR_closed lwf_cell_F4T_k1
          lwle_line_F4T_k1 hp h5)
    · exact ggLineTest_of_equiv e (ggAttachCartan_map_equiv e hC' hc)
        (ggLineTest_of_data (Matrix.transpose CartanMatrix.F₄) (2 : Fin 4) (by decide)
          lwf_F4TR [4, 3] 2 [4, 2, 1, 2, 4, 0, 1] 2 1 lwf_F4TR_closed lwf_cell_F4T_k2
          lwle_line_F4T_k2 hp h5)

end CFSG.StandardType
