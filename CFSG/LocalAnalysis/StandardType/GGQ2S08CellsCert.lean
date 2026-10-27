module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellsShape
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertD6
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertD9
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertA4
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellsFull
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertB4
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertB5
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertB6
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertB7
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertB8
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertF4
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertD4Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertD5Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertD6Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertD8Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertA9
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertE8
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwA5b
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwA5c
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwA8b
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwA8c
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwE6b
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwE6d
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwE6a
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertTwE6c

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

theorem ggQ2s08_coords_twA5d {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeD) (e : Fin 5 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 5 i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 5, (κ M.xV = oneN 5 ∨ κ M.xV = -oneN 5) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = d6cS i v := by
  have hA : AlphOK d6cGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeD M hShape e (CartanMatrix.A 5) hC
    (fun k => (letAt d6cGens k).1) (fun k => (letAt d6cGens k).2) (by decide +kernel)
    ![![1, 1, 1, 1, 1], ![0, 1, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 0, 1, 1], ![0, 0, 0, 0, 1]]
    (by decide +kernel) d6cS (fun k v => letLin_letAt_apply hA k v) ![1, 2, 0, 1, 2]
    (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.A 5) ![1, 2, 0, 1, 2] 0 1
      ![![0, 0, 0, 0, 0], ![2, 0, 0, 0, 0], ![1, 2, 0, 0, 0], ![0, 1, 2, 0, 0], ![2, 0, 1, 2, 0]]
      (by decide +kernel))
    (oneN 5) (by decide +kernel)

theorem ggQ2s08_cell_twA5d (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 5 .d :=
  ggQ2s08_cell_of_label (t := .twA) (r := 5) (s := .d) hLB hP hΓi hTBN (CartanMatrix.A 5)
    (fun M labL htag hrank hWeyl => ggQ2s08_lab_twA 5 M labL htag hrank hWeyl) d6cS (oneN 5)
    (fun M hShape e hC => ggQ2s08_coords_twA5d M hShape e hC)
    (fun A Mg hT r hr hrR hrx t ht htR htx => d6c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twA8d {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeD) (e : Fin 8 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.A 8) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 8, (κ M.xV = oneN 8 ∨ κ M.xV = -oneN 8) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = d9cS i v := by
  have hA : AlphOK d9cGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeD M hShape e (CartanMatrix.A 8) hC (fun k => (letAt d9cGens k).1)
    (fun k => (letAt d9cGens k).2) (by decide +kernel)
    ![![1, 1, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1, 1], ![0, 0, 0,
      1, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 1,
      1], ![0, 0, 0, 0, 0, 0, 0, 1]]
    (by decide +kernel) d9cS (fun k v => letLin_letAt_apply hA k v)
    ![1, 2, 0, 1, 2, 0, 1, 2] (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.A 8) ![1, 2, 0, 1, 2, 0, 1, 2] 0 1
      ![![0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0], ![0, 1,
        2, 0, 0, 0, 0, 0], ![2, 0, 1, 2, 0, 0, 0, 0], ![1, 2, 0, 1, 2, 0, 0, 0], ![0, 1, 2, 0, 1,
        2, 0, 0], ![2, 0, 1, 2, 0, 1, 2, 0]]
      (by decide +kernel))
    (oneN 8) (by decide +kernel)

theorem ggQ2s08_cell_twA8d (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 8 .d :=
  ggQ2s08_cell_of_label (t := .twA) (r := 8) (s := .d) hLB hP hΓi hTBN (CartanMatrix.A 8)
    (fun M labL htag hrank hWeyl => ggQ2s08_lab_twA 8 M labL htag hrank hWeyl) d9cS (oneN 8)
    (fun M hShape e hC => ggQ2s08_coords_twA8d M hShape e hC)
    (fun A Mg hT r hr hrR hrx t ht htR htx => d9c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem a4cS_eq : a4cS = aFullS 5 := by
  funext k
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun (ZMod 3) (Fin 5)).ext fun j => ?_)
  rw [Pi.basisFun_apply]
  revert k j
  decide +kernel

theorem ggQ2s08_cell_twA4 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 4 .full :=
  ggQ2s08_cellA4_of_test hLB hP hΓi hTBN (a4cS_eq ▸ fun A Mg hT r hr hrR hrx t ht htR htx =>
    a4c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_cell_BC (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {t : LargeEvenLieTag} {r : ℕ}
    (ht : t = .B ∨ t = .C) (hr4 : 4 ≤ r) (hr8 : r ≤ 8) : GGQ2S08Cell t r .full :=
  ggQ2s08_cellBC_of_test hLB hP hΓi hTBN hr4 hr8 (by
    interval_cases r
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => b4c_test A Mg hT r hr hrR hrx t ht htR htx
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => b5c_test A Mg hT r hr hrR hrx t ht htR htx
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => b6c_test A Mg hT r hr hrR hrx t ht htR htx
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => b7c_test A Mg hT r hr hrR hrx t ht htR htx
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => b8c_test A Mg hT r hr hrR hrx t ht htR htx) ht

theorem ggQ2s08_cell_D (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {t : LargeEvenLieTag} {r : ℕ}
    (ht : t = .D ∨ t = .twD) (hr : r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 8) : GGQ2S08Cell t r .full :=
  ggQ2s08_cellD_of_test hLB hP hΓi hTBN (by rcases hr with rfl | rfl | rfl | rfl <;> norm_num)
    (by rcases hr with rfl | rfl | rfl | rfl <;> norm_num) (by
    rcases hr with rfl | rfl | rfl | rfl
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => d4f_test A Mg hT r hr hrR hrx t ht htR htx
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => d5f_test A Mg hT r hr hrR hrx t ht htR htx
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => d6f_test A Mg hT r hr hrR hrx t ht htR htx
    · exact fun A Mg hT r hr hrR hrx t ht htR htx => d8f_test A Mg hT r hr hrR hrx t ht htR htx) ht

theorem ggQ2s08_coords_twA8a {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA) (e : Fin 8 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.A 8) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 9, (κ M.xV = oneN 9 ∨ κ M.xV = -oneN 9) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = a9cS i v := by
  have hA : AlphOK a9cGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeA M hShape (n := 9) rfl e (CartanMatrix.A 8) hC (fun k => (letAt
    a9cGens k).1) (fun k => (letAt a9cGens k).2)
    (by decide +kernel) 0 ![1, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) ![2, 1, 0, 2, 1, 0, 2, 1]
    (by decide +kernel) (by decide) ![1, 2, 0, 1, 2, 0, 1, 2] (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.A 8) ![1, 2, 0, 1, 2, 0, 1, 2] 0 1
      ![![0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0], ![0, 1,
        2, 0, 0, 0, 0, 0], ![2, 0, 1, 2, 0, 0, 0, 0], ![1, 2, 0, 1, 2, 0, 0, 0], ![0, 1, 2, 0, 1,
        2, 0, 0], ![2, 0, 1, 2, 0, 1, 2, 0]]
      (by decide +kernel))
    (oneN 9) (by decide +kernel)
    (fun k o => Option.elim o (![![1], ![1], ![1], ![1], ![1], ![1], ![1], ![1], ![1]] k 0)
      fun j => ![![0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0, 0, 0],
        ![2, 2, 2, 0, 0, 0, 0, 0], ![2, 2, 2, 2, 0, 0, 0, 0], ![2, 2, 2, 2, 2, 0, 0, 0], ![2, 2,
        2, 2, 2, 2, 0, 0], ![2, 2, 2, 2, 2, 2, 2, 0], ![2, 2, 2, 2, 2, 2, 2, 2]] k j)
    (by decide +kernel) a9cS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twA8a (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 8 .a :=
  ggQ2s08_cell_of_label (t := .twA) (r := 8) (s := .a) hLB hP hΓi hTBN (CartanMatrix.A 8)
    (fun M labL htag hrank hWeyl => ggQ2s08_lab_twA 8 M labL htag hrank hWeyl) a9cS (oneN 9)
    (fun M hShape e hC => ggQ2s08_coords_twA8a M hShape e hC)
    (fun A Mg hT r hr hrR hrx t ht htR htx => a9c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twA5b {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeB) (e : Fin 5 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.A 5) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 5, κ M.xV = xLast 4 ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = a5bS i v := by
  have hA : AlphOK a5bGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeB M hShape e (CartanMatrix.A 5) hC (fun k => (letAt a5bGens k).1)
    (fun k => (letAt a5bGens k).2) (by decide +kernel)
    (xLast 4) (by decide +kernel) 0 ![2, 1, 0, 2, 1] (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.A 5) ![2, 1, 0, 2, 1] 0 2
      ![![0, 0, 0, 0, 0], ![2, 0, 0, 0, 0], ![1, 2, 0, 0, 0], ![0, 1, 2, 0, 0], ![2, 0, 1, 2, 0]]
      (by decide +kernel))
    (by decide +kernel) ![![0, 2, 1, 0, 2], ![0, 1, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0]] (by decide +kernel)
    a5bS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twA5b (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 5 .b :=
  ggQ2s08_cell_of_label (t := .twA) (r := 5) (s := .b) hLB hP hΓi hTBN (CartanMatrix.A 5)
    (fun M labL htag hrank hWeyl => ggQ2s08_lab_twA 5 M labL htag hrank hWeyl) a5bS (xLast 4)
    (fun M hShape e hC => (ggQ2s08_coords_twA5b M hShape e hC).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
    (fun A Mg hT r hr hrR hrx t ht htR htx => a5b_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twA5c {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeC) (e : Fin 5 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.A 5) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 6, κ M.xV = xLast 5 ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = a5cS i v := by
  have hA : AlphOK a5cGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeC M hShape e (CartanMatrix.A 5) hC (fun k => (letAt a5cGens k).2)
    ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 0], ![1, 1,
      1, 1, 1, 0]] (fun k => (letAt a5cGens k).1)
    ![0, 0, 0, 0, 0, 1] (xLast 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) a5cS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twA5c (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 5 .c :=
  ggQ2s08_cell_of_label (t := .twA) (r := 5) (s := .c) hLB hP hΓi hTBN (CartanMatrix.A 5)
    (fun M labL htag hrank hWeyl => ggQ2s08_lab_twA 5 M labL htag hrank hWeyl) a5cS (xLast 5)
    (fun M hShape e hC => (ggQ2s08_coords_twA5c M hShape e hC).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
    (fun A Mg hT r hr hrR hrx t ht htR htx => a5c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twA8b {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeB) (e : Fin 8 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.A 8) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 8, κ M.xV = xLast 7 ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = a8bS i v := by
  have hA : AlphOK a8bGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeB M hShape e (CartanMatrix.A 8) hC (fun k => (letAt a8bGens k).1)
    (fun k => (letAt a8bGens k).2) (by decide +kernel)
    (xLast 7) (by decide +kernel) 0 ![2, 1, 0, 2, 1, 0, 2, 1] (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.A 8) ![2, 1, 0, 2, 1, 0, 2, 1] 0 2
      ![![0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0], ![0, 1,
        2, 0, 0, 0, 0, 0], ![2, 0, 1, 2, 0, 0, 0, 0], ![1, 2, 0, 1, 2, 0, 0, 0], ![0, 1, 2, 0, 1,
        2, 0, 0], ![2, 0, 1, 2, 0, 1, 2, 0]]
      (by decide +kernel))
    (by decide +kernel) ![![0, 2, 1, 0, 2, 1, 0, 2], ![0, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1,
      1, 1, 1], ![0, 0, 0, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 1, 1], ![1, 0, 0, 0, 0, 0, 0, 0]] (by decide +kernel)
    a8bS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twA8b (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 8 .b :=
  ggQ2s08_cell_of_label (t := .twA) (r := 8) (s := .b) hLB hP hΓi hTBN (CartanMatrix.A 8)
    (fun M labL htag hrank hWeyl => ggQ2s08_lab_twA 8 M labL htag hrank hWeyl) a8bS (xLast 7)
    (fun M hShape e hC => (ggQ2s08_coords_twA8b M hShape e hC).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
    (fun A Mg hT r hr hrR hrx t ht htR htx => a8b_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twA8c {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeC) (e : Fin 8 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.A 8) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 9, κ M.xV = xLast 8 ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = a8cS i v := by
  have hA : AlphOK a8cGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeC M hShape e (CartanMatrix.A 8) hC (fun k => (letAt a8cGens k).2)
    ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0],
      ![1, 1, 1, 1, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0],
      ![1, 1, 1, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0]] (fun k => (letAt a8cGens k).1)
    ![0, 0, 0, 0, 0, 0, 0, 0, 1] (xLast 8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) a8cS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twA8c (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twA 8 .c :=
  ggQ2s08_cell_of_label (t := .twA) (r := 8) (s := .c) hLB hP hΓi hTBN (CartanMatrix.A 8)
    (fun M labL htag hrank hWeyl => ggQ2s08_lab_twA 8 M labL htag hrank hWeyl) a8cS (xLast 8)
    (fun M hShape e hC => (ggQ2s08_coords_twA8c M hShape e hC).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
    (fun A Mg hT r hr hrR hrx t ht htR htx => a8c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twE6b {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.E₆) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 6, κ M.xV = xLast 5 ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = e6bS i v := by
  have hA : AlphOK e6bGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeB M hShape e (CartanMatrix.E₆) hC (fun k => (letAt e6bGens k).1)
    (fun k => (letAt e6bGens k).2) (by decide +kernel)
    (xLast 5) (by decide +kernel) 0 ![2, 0, 1, 0, 2, 1] (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.E₆) ![2, 0, 1, 0, 2, 1] 0 2
      ![![0, 0, 0, 0, 0, 0], ![2, 2, 1, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0], ![1,
        1, 0, 2, 0, 0], ![1, 2, 1, 1, 2, 0]]
      (by decide +kernel))
    (by decide +kernel) ![![0, 2, 2, 1, 1, 1], ![0, 2, 1, 1, 2, 0], ![0, 2, 0, 1, 2, 0], ![0, 2,
      0, 0, 2, 0], ![0, 2, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0]] (by decide +kernel)
    e6bS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twE6b (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twE6 0 .b :=
  ggQ2s08_cell_of_label (t := .twE6) (r := 0) (s := .b) hLB hP hΓi hTBN CartanMatrix.E₆
    (fun M labL htag _ hWeyl => ggQ2s08_lab_twE6 M labL htag hWeyl) e6bS (xLast 5)
    (fun M hShape e hC => (ggQ2s08_coords_twE6b M hShape e hC).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
    (fun A Mg hT r hr hrR hrx t ht htR htx => e6b_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twE6d {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeD) (e : Fin 6 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.E₆) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 6, (κ M.xV = xLast 5 ∨ κ M.xV = -xLast 5) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = e6dS i v := by
  have hA : AlphOK e6dGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeD M hShape e (CartanMatrix.E₆) hC (fun k => (letAt e6dGens k).1)
    (fun k => (letAt e6dGens k).2) (by decide +kernel)
    ![![1, 2, 1, 1, 2, 0], ![0, 2, 1, 1, 2, 0], ![0, 2, 0, 1, 2, 0], ![0, 2, 0, 0, 2, 0], ![0, 2,
      0, 0, 1, 0], ![2, 0, 1, 0, 2, 1]]
    (by decide +kernel) e6dS (fun k v => letLin_letAt_apply hA k v)
    ![2, 0, 1, 0, 2, 1] (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.E₆) ![2, 0, 1, 0, 2, 1] 0 2
      ![![0, 0, 0, 0, 0, 0], ![2, 2, 1, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0], ![1,
        1, 0, 2, 0, 0], ![1, 2, 1, 1, 2, 0]]
      (by decide +kernel))
    (xLast 5) (by decide +kernel)

theorem ggQ2s08_cell_twE6d (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twE6 0 .d :=
  ggQ2s08_cell_of_label (t := .twE6) (r := 0) (s := .d) hLB hP hΓi hTBN CartanMatrix.E₆
    (fun M labL htag _ hWeyl => ggQ2s08_lab_twE6 M labL htag hWeyl) e6dS (xLast 5)
    (fun M hShape e hC => ggQ2s08_coords_twE6d M hShape e hC)
    (fun A Mg hT r hr hrR hrx t ht htR htx => e6d_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twE6a {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA) (e : Fin 6 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.E₆) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 7, (κ M.xV = xLast2 5 ∨ κ M.xV = -xLast2 5) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = e6aS i v := by
  have hA : AlphOK e6aGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeA M hShape (n := 7) rfl e (CartanMatrix.E₆) hC (fun k => (letAt
    e6aGens k).1) (fun k => (letAt e6aGens k).2)
    (by decide +kernel) 0 ![1, 0, 0, 0, 0, 1, 0] (by decide +kernel) ![2, 0, 1, 0, 2, 1]
    (by decide +kernel) (by decide) ![2, 0, 1, 0, 2, 1] (by decide +kernel) (by decide)
    (ggQ2S08_ker_of_cert (CartanMatrix.E₆) ![2, 0, 1, 0, 2, 1] 0 2
      ![![0, 0, 0, 0, 0, 0], ![2, 2, 1, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0], ![1,
        1, 0, 2, 0, 0], ![1, 2, 1, 1, 2, 0]]
      (by decide +kernel))
    (xLast2 5) (by decide +kernel)
    (fun k o => Option.elim o (![![0], ![0], ![0], ![0], ![0], ![1], ![0]] k 0)
      fun j => ![![1, 2, 1, 1, 2, 0], ![0, 2, 1, 1, 2, 0], ![0, 2, 0, 1, 2, 0], ![0, 2, 0, 0, 2,
        0], ![0, 2, 0, 0, 1, 0], ![2, 1, 2, 2, 1, 0], ![2, 0, 1, 0, 2, 1]] k j)
    (by decide +kernel) e6aS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twE6a (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twE6 0 .a :=
  ggQ2s08_cell_of_label (t := .twE6) (r := 0) (s := .a) hLB hP hΓi hTBN CartanMatrix.E₆
    (fun M labL htag _ hWeyl => ggQ2s08_lab_twE6 M labL htag hWeyl) e6aS (xLast2 5)
    (fun M hShape e hC => ggQ2s08_coords_twE6a M hShape e hC)
    (fun A Mg hT r hr hrR hrx t ht htR htx => e6a_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_coords_twE6c {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeC) (e : Fin 6 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = (CartanMatrix.E₆) i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn 7, κ M.xV = xLast2 5 ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = e6cS i v := by
  have hA : AlphOK e6cGens := AlphOK.of_all (by decide +kernel)
  exact ggQ2LDatum_coords_shapeC M hShape e (CartanMatrix.E₆) hC (fun k => (letAt e6cGens k).2)
    ![![1, 0, 0, 0, 0, 2, 0], ![2, 2, 2, 2, 2, 0, 0], ![1, 1, 0, 0, 0, 1, 0], ![1, 1, 1, 0, 0, 0,
      0], ![2, 2, 2, 2, 1, 2, 0], ![0, 0, 0, 0, 0, 1, 0]] (fun k => (letAt e6cGens k).1)
    ![0, 0, 0, 0, 0, 0, 1] (xLast2 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) e6cS (fun k v => letLin_letAt_apply hA k v)

theorem ggQ2s08_cell_twE6c (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .twE6 0 .c :=
  ggQ2s08_cell_of_label (t := .twE6) (r := 0) (s := .c) hLB hP hΓi hTBN CartanMatrix.E₆
    (fun M labL htag _ hWeyl => ggQ2s08_lab_twE6 M labL htag hWeyl) e6cS (xLast2 5)
    (fun M hShape e hC =>
      (ggQ2s08_coords_twE6c M hShape e hC).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
    (fun A Mg hT r hr hrR hrx t ht htR htx => e6c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_cell_F4 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .F4 0 .full :=
  ggQ2s08_cellF4_of_test hLB hP hΓi hTBN
    (fun A Mg hT r hr hrR hrx t ht htR htx => f4c_test A Mg hT r hr hrR hrx t ht htR htx)

theorem ggQ2s08_cell_E8 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08Cell .E8 0 .full :=
  ggQ2s08_cellE8_of_test hLB hP hΓi hTBN
    (fun A Mg hT r hr hrR hrx t ht htR htx => e8f_test A Mg hT r hr hrR hrx t ht htR htx)

end CFSG.StandardType

end
