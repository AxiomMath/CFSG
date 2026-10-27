module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGForkClassify
public import CFSG.LocalAnalysis.StandardType.GGPZWeylB
public import CFSG.LocalAnalysis.StandardType.GGForkCells

open CFSG.StandardType
open CFSG.LieType.RootSystem

public section

namespace CFSG.StandardType

noncomputable section

set_option autoImplicit false

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

omit [Fintype Λ] [DecidableEq Λ] in
theorem side_card_A3 {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.A 3 i j) :
    Nat.card ML.Group = 24 := by
  let C0 : Matrix (Fin 3) (Fin 3) ℤ := Matrix.reindex e.symm e.symm CL
  have hC0 : C0 = CartanMatrix.A 3 := by
    funext i j
    simpa [C0, Matrix.reindex_apply] using hCe i j
  have hC0' : GGIntCartan (ML.reindex e.symm) C0 := hCL.reindex (e := e.symm)
  rw [hC0] at hC0'
  have hFT : TauCeti.IsFiniteType (CartanMatrix.A 3) :=
    TauCeti.isFiniteType_cartanMatrix_A 3
  have hcoh : coxeterMatrix hFT = ML.reindex e.symm :=
    coxeterMatrix_eq_of_ggIntCartan hFT hC0'
  have hstd : coxeterMatrix hFT = CoxeterMatrix.A 3 :=
    coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_A 3)
  have hML : ML.reindex e.symm = CoxeterMatrix.A 3 := hcoh.symm.trans hstd
  calc
    Nat.card ML.Group = Nat.card (ML.reindex e.symm).Group :=
      (Nat.card_congr (ML.reindexGroupEquiv e.symm).toEquiv).symm
    _ = Nat.card (CoxeterMatrix.A 3).Group := by rw [hML]
    _ = 24 := by rw [l05nK3a_card_coxeterA 3]; norm_num

omit [Fintype Λ] [DecidableEq Λ] in
theorem side_card_B3 {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.B 3 i j) :
    Nat.card ML.Group = 48 := by
  let C0 : Matrix (Fin 3) (Fin 3) ℤ := Matrix.reindex e.symm e.symm CL
  have hC0 : C0 = CartanMatrix.B 3 := by
    funext i j
    simpa [C0, Matrix.reindex_apply] using hCe i j
  have hC0' : GGIntCartan (ML.reindex e.symm) C0 := hCL.reindex (e := e.symm)
  rw [hC0] at hC0'
  have hFT : TauCeti.IsFiniteType (CartanMatrix.B 3) :=
    TauCeti.isFiniteType_cartanMatrix_B 3
  have hcoh : coxeterMatrix hFT = ML.reindex e.symm :=
    coxeterMatrix_eq_of_ggIntCartan hFT hC0'
  have hstd : coxeterMatrix hFT = CoxeterMatrix.B 3 :=
    coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_B 3)
  have hML : ML.reindex e.symm = CoxeterMatrix.B 3 := hcoh.symm.trans hstd
  calc
    Nat.card ML.Group = Nat.card (ML.reindex e.symm).Group :=
      (Nat.card_congr (ML.reindexGroupEquiv e.symm).toEquiv).symm
    _ = Nat.card (CoxeterMatrix.B 3).Group := by rw [hML]
    _ = 48 := by rw [ggCoxeterB_card 3 (by norm_num)]; norm_num

omit [Fintype Λ] [DecidableEq Λ] in
theorem side_card_C3 {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.C 3 i j) :
    Nat.card ML.Group = 48 := by
  let C0 : Matrix (Fin 3) (Fin 3) ℤ := Matrix.reindex e.symm e.symm CL
  have hC0 : C0 = CartanMatrix.C 3 := by
    funext i j
    simpa [C0, Matrix.reindex_apply] using hCe i j
  have hC0' : GGIntCartan (ML.reindex e.symm) C0 := hCL.reindex (e := e.symm)
  rw [hC0] at hC0'
  have hFT : TauCeti.IsFiniteType (CartanMatrix.C 3) :=
    TauCeti.isFiniteType_cartanMatrix_C 3
  have hcoh : coxeterMatrix hFT = ML.reindex e.symm :=
    coxeterMatrix_eq_of_ggIntCartan hFT hC0'
  have hstd : coxeterMatrix hFT = CoxeterMatrix.B 3 :=
    coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_C 3)
  have hML : ML.reindex e.symm = CoxeterMatrix.B 3 := hcoh.symm.trans hstd
  calc
    Nat.card ML.Group = Nat.card (ML.reindex e.symm).Group :=
      (Nat.card_congr (ML.reindexGroupEquiv e.symm).toEquiv).symm
    _ = Nat.card (CoxeterMatrix.B 3).Group := by rw [hML]
    _ = 48 := by rw [ggCoxeterB_card 3 (by norm_num)]; norm_num

end
end CFSG.StandardType

namespace CFSG.StandardType

noncomputable section

@[expose] def ggResQTwoLOrder : GGResQTwoResidual → ℕ
  | .A3b0c1w12 | .A3b0c1w21 | .A3b0c2w12 | .A3b0c2w21
  | .A3b2c0w12 | .A3b2c0w21 | .A3b2c1w12 | .A3b2c1w21 => 24
  | _ => 48

theorem ggResQTwoResidual_L_order
    {G : Type} [Group G] {Bs L : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL)
    {tag : GGResQTwoResidual} {C : Matrix (Fin 3) (Fin 3) ℤ}
    {ib ic : Fin 3} {e₁ e₂ : ℤ} {u v : ZMod 3} {e : Fin 3 ≃ Λ}
    (hshape : GGResQTwoResidualShape tag 3 C ib ic e₁ e₂ u v)
    (hCe : ∀ i j, CL (e i) (e j) = C i j)
    (fL : ML.Group ≃* ↥(ggAutomizer L Bs)) :
    Nat.card (ggAutomizer L Bs) = ggResQTwoLOrder tag := by
  have hcard : Nat.card (ggAutomizer L Bs) = Nat.card ML.Group :=
    (Nat.card_congr fL.toEquiv).symm
  rw [hcard]
  cases tag <;>
    simp only [ggResQTwoResidualShape_three, ggResQTwoResidualData] at hshape <;>
    obtain ⟨rfl, -, -, -, -, -, -⟩ := hshape <;>
    simp only [ggResQTwoLOrder] <;>
    first
      | exact side_card_A3 hCL e hCe
      | exact side_card_B3 hCL e hCe
      | exact side_card_C3 hCL e hCe

theorem ggResQTwoResidual_three_dvd_L_order
    {G : Type} [Group G] {Bs L : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL)
    {tag : GGResQTwoResidual} {C : Matrix (Fin 3) (Fin 3) ℤ}
    {ib ic : Fin 3} {e₁ e₂ : ℤ} {u v : ZMod 3} {e : Fin 3 ≃ Λ}
    (hshape : GGResQTwoResidualShape tag 3 C ib ic e₁ e₂ u v)
    (hCe : ∀ i j, CL (e i) (e j) = C i j)
    (fL : ML.Group ≃* ↥(ggAutomizer L Bs)) :
    3 ∣ Nat.card (ggAutomizer L Bs) := by
  rw [ggResQTwoResidual_L_order hCL hshape hCe fL]
  cases tag <;> decide

end
end CFSG.StandardType

namespace CFSG.StandardType

noncomputable section

theorem side_card_K_of_doubleBond
    {G : Type} [Group G] {Bs K : Subgroup G}
    {ΛK : Type} [Fintype ΛK] [DecidableEq ΛK]
    {MK : CoxeterMatrix ΛK} {CK : Matrix ΛK ΛK ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hcard : Fintype.card ΛK = 3)
    (hdouble : ∃ i j : ΛK, i ≠ j ∧ CK i j * CK j i = 2)
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs)) :
    Nat.card (ggAutomizer K Bs) = 48 := by
  have hcardg : Nat.card (ggAutomizer K Bs) = Nat.card MK.Group :=
    (Nat.card_congr fK.toEquiv).symm
  rw [hcardg]
  rcases ggIntCartan_models hWK hCK with
    ⟨n, e, hn, hA | ⟨hn2, hB | hC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ |
      ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  ·
    exfalso
    obtain ⟨i, j, hij, hprod⟩ := hdouble
    have h3 : n = 3 := by
      have hc := Fintype.card_congr e
      rw [Fintype.card_fin, hcard] at hc
      omega
    subst h3
    have hAbd : ∀ a b : Fin 3, CartanMatrix.A 3 a b * CartanMatrix.A 3 b a ≠ 2 := by
      decide
    apply hAbd
    rw [← hA (e.symm i) (e.symm j), ← hA (e.symm j) (e.symm i)]
    simpa using hprod
  ·
    have h3 : n = 3 := by
      have hc := Fintype.card_congr e
      rw [Fintype.card_fin, hcard] at hc
      omega
    subst h3
    exact side_card_B3 hCK e hB
  ·
    have h3 : n = 3 := by
      have hc := Fintype.card_congr e
      rw [Fintype.card_fin, hcard] at hc
      omega
    subst h3
    exact side_card_C3 hCK e hC
  ·
    exfalso
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at hc
    omega
  ·
    exfalso
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at hc
    omega
  ·
    exfalso
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at hc
    omega
  ·
    exfalso
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at hc
    omega
  ·
    exfalso
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at hc
    omega
  ·
    exfalso
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at hc
    omega

end
end CFSG.StandardType

namespace CFSG.StandardType

noncomputable section

@[expose] def ggResQTwoIsA3 : GGResQTwoResidual → Bool
  | .A3b0c1w12 | .A3b0c1w21 | .A3b0c2w12 | .A3b0c2w21
  | .A3b2c0w12 | .A3b2c0w21 | .A3b2c1w12 | .A3b2c1w21 => true
  | _ => false

lemma ggResQTwoA3_ic_ne_ib (tag : GGResQTwoResidual) (htag : ggResQTwoIsA3 tag = true) :
    (ggResQTwoResidualData tag).ic ≠ (ggResQTwoResidualData tag).ib := by
  cases tag <;> simp [ggResQTwoIsA3, ggResQTwoResidualData] at htag ⊢

lemma ggResQTwoA3_e1_mul_e2 (tag : GGResQTwoResidual) (htag : ggResQTwoIsA3 tag = true) :
    (ggResQTwoResidualData tag).e₁ * (ggResQTwoResidualData tag).e₂ = 2 := by
  cases tag <;> simp [ggResQTwoIsA3, ggResQTwoResidualData] at htag ⊢

lemma ggResQTwoA3_doubleBond
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {tag : GGResQTwoResidual} {C : Matrix (Fin 3) (Fin 3) ℤ}
    {ib ic : Fin 3} {e₁ e₂ : ℤ} {u v : ZMod 3} {e : Fin 3 ≃ Λ}
    (htag : ggResQTwoIsA3 tag = true)
    (hshape : GGResQTwoResidualShape tag 3 C ib ic e₁ e₂ u v)
    (hib : e ib = b)
    (hrow : ∀ (j : Fin 3) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin 3) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0) :
    ∃ i j : Option {i : Λ // i ≠ b}, i ≠ j ∧ CK i j * CK j i = 2 := by
  obtain ⟨-, rfl, rfl, rfl, rfl, -, -⟩ := hshape
  have hicne : (ggResQTwoResidualData tag).ic ≠ (ggResQTwoResidualData tag).ib :=
    ggResQTwoA3_ic_ne_ib tag htag
  have hne : e (ggResQTwoResidualData tag).ic ≠ b := fun he =>
    hicne (e.injective (he.trans hib.symm))
  refine ⟨none, some ⟨e (ggResQTwoResidualData tag).ic, hne⟩, by simp, ?_⟩
  rw [hrow (ggResQTwoResidualData tag).ic hne, hcol (ggResQTwoResidualData tag).ic hne]
  simpa using ggResQTwoA3_e1_mul_e2 tag htag

end
end CFSG.StandardType

namespace CFSG.StandardType

noncomputable section

theorem ggResQTwoResidual_A3_K_order
    {G : Type} [Group G] {Bs K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {tag : GGResQTwoResidual} {C : Matrix (Fin 3) (Fin 3) ℤ}
    {ib ic : Fin 3} {e₁ e₂ : ℤ} {u v : ZMod 3} {e : Fin 3 ≃ Λ}
    (htag : ggResQTwoIsA3 tag = true)
    (hshape : GGResQTwoResidualShape tag 3 C ib ic e₁ e₂ u v)
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hib : e ib = b)
    (hrow : ∀ (j : Fin 3) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin 3) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs)) :
    Nat.card (ggAutomizer K Bs) = 48 := by
  have hcardK : Fintype.card (Option {i : Λ // i ≠ b}) = 3 := by
    have h := Fintype.card_congr (ggResIKIdx e hib)
    simpa using h.symm
  exact side_card_K_of_doubleBond hWK hCK hcardK
    (ggResQTwoA3_doubleBond htag hshape hib hrow hcol) fK

end
end CFSG.StandardType

namespace CFSG.StandardType

noncomputable section

theorem ggResQTwo_actual_residual_h3A
    {G : Type} [Group G] [Finite G]
    {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell) :
    3 ∣ Nat.card (ggAutomizer L Bs) := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    _hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ, hcell⟩ := hD
  obtain ⟨n, C, ib, ic, e1, e2, e, tag, hCe, hib, hrow, hcol, hdiagK, hshape⟩ := hcell
  have hn : n = 3 :=
    ggResQTwoResidualShape_n_eq_three tag n C ib ic e1 e2
      (α none (h (some b))) (α (some b) (h none)) hshape
  subst hn
  exact ggResQTwoResidual_three_dvd_L_order hCL hshape hCe fL

end
end CFSG.StandardType
