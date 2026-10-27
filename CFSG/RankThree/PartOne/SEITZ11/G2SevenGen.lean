module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenBlock
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenUnitary
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenFrame

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

section Scale

variable {L : Type} [Field L]

@[expose] def Dm (n2 n6 : L) (h2 : n2 ≠ 0) (h6 : n6 ≠ 0) : GL (Fin 3) L :=
  ⟨Matrix.diagonal ![n2, 1, n6], Matrix.diagonal ![n2⁻¹, 1, n6⁻¹], by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h2, h6], by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h2, h6]⟩

theorem coe_Dm (n2 n6 : L) (h2 : n2 ≠ 0) (h6 : n6 ≠ 0) :
    ((Dm n2 n6 h2 h6 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![n2, 1, n6] :=
  rfl

theorem coe_Dm_inv (n2 n6 : L) (h2 : n2 ≠ 0) (h6 : n6 ≠ 0) :
    (((Dm n2 n6 h2 h6)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![n2⁻¹, 1, n6⁻¹] :=
  rfl

theorem blk_theta0 (M : Matrix (Fin 2) (Fin 2) L) :
    blk (theta0 M) = !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, eV, theta0]

theorem blk_theta2 (y0 : L) (M : Matrix (Fin 2) (Fin 2) L) :
    blk (theta2 y0 M) =
      !![1, 0, 0; 0, M 0 0, -(M 0 1 * y0 ^ 3); 0, -(M 1 0 * (y0 ^ 3)⁻¹), M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, eV, theta2]

theorem scale_blk_theta0 (n2 n6 : L) (h2 : n2 ≠ 0) (h6 : n6 ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) L) :
    (Dm n2 n6 h2 h6 : Matrix (Fin 3) (Fin 3) L) *
      !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1] * ((Dm n2 n6 h2 h6)⁻¹ : GL (Fin 3) L) =
    !![M 0 0, n2 * M 0 1, 0; n2⁻¹ * M 1 0, M 1 1, 0; 0, 0, 1] := by
  rw [coe_Dm, coe_Dm_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, h6] <;> field_simp

theorem scale_blk_theta2 (n2 n6 : L) (h2 : n2 ≠ 0) (h6 : n6 ≠ 0) (y0 : L)
    (M : Matrix (Fin 2) (Fin 2) L) :
    (Dm n2 n6 h2 h6 : Matrix (Fin 3) (Fin 3) L) *
      !![1, 0, 0; 0, M 0 0, -(M 0 1 * y0 ^ 3); 0, -(M 1 0 * (y0 ^ 3)⁻¹), M 1 1] *
      ((Dm n2 n6 h2 h6)⁻¹ : GL (Fin 3) L) =
    !![1, 0, 0; 0, M 0 0, -(M 0 1 * y0 ^ 3 * n6⁻¹);
      0, -(n6 * (M 1 0 * (y0 ^ 3)⁻¹)), M 1 1] := by
  rw [coe_Dm, coe_Dm_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, h2]
  all_goals field_simp

end Scale

section Nu

variable {L : Type} [Field L]

@[expose] def nuSL (y0 : L) (hy : y0 ≠ 0) : SL2 L :=
  ⟨!![0, y0; -y0⁻¹, 0], by simp [Matrix.det_fin_two, hy]⟩

@[expose] def mkSL (a b c d : L) (h : a * d - b * c = 1) : SL2 L :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem coe_nuSL (y0 : L) (hy : y0 ≠ 0) :
    ((nuSL y0 hy : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![0, y0; -y0⁻¹, 0] := rfl

theorem coe_nuSL_inv (y0 : L) (hy : y0 ≠ 0) :
    (((nuSL y0 hy)⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![0, -y0; y0⁻¹, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_nuSL, Matrix.adjugate_fin_two]
  simp

end Nu

section FrameDataSec

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

structure FrameData (L : Type) [Field L] [Finite L] (p f : ℕ) [Fact p.Prime]
    [CharP L p] where
  κ0 : L
  κ1 : L
  n2 : L
  n6 : L
  y0 : L
  hκ0 : κ0 ≠ 0
  hκ1 : κ1 ≠ 0
  hκ0σ : unitaryInvolution L p f κ0 = κ0
  hκ1σ : unitaryInvolution L p f κ1 = κ1
  hn2 : unitaryInvolution L p f n2 * n2 = -κ0
  hy0 : unitaryInvolution L p f y0 * y0 = -κ1⁻¹
  hn6 : unitaryInvolution L p f n6 * n6 = (κ0 * κ1 ^ 3)⁻¹

namespace FrameData

variable (Fr : FrameData L p f)

theorem n2_ne : Fr.n2 ≠ 0 := fun h => by
  have := Fr.hn2
  rw [h, mul_zero] at this
  exact Fr.hκ0 (neg_eq_zero.1 this.symm)

theorem y0_ne : Fr.y0 ≠ 0 := fun h => by
  have := Fr.hy0
  rw [h, mul_zero] at this
  exact inv_ne_zero Fr.hκ1 (neg_eq_zero.1 this.symm)

theorem n6_ne : Fr.n6 ≠ 0 := fun h => by
  have := Fr.hn6
  rw [h, mul_zero] at this
  exact inv_ne_zero (mul_ne_zero Fr.hκ0 (pow_ne_zero 3 Fr.hκ1)) this.symm

theorem κ1σy0 : Fr.κ1 * unitaryInvolution L p f Fr.y0 = -Fr.y0⁻¹ := by
  have h := Fr.hy0
  have := Fr.y0_ne
  have := Fr.hκ1
  field_simp at h ⊢
  linear_combination h

end FrameData

end FrameDataSec

section ShapeSec

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

@[expose] def ShapeP (κ : L) (M : SL2 L) : Prop :=
  (M : Matrix (Fin 2) (Fin 2) L) 1 1 =
      unitaryInvolution L p f ((M : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
    (M : Matrix (Fin 2) (Fin 2) L) 1 0 =
      κ * unitaryInvolution L p f ((M : Matrix (Fin 2) (Fin 2) L) 0 1)

theorem shapeP_nu (Fr : FrameData L p f) :
    ShapeP (p := p) (f := f) Fr.κ1 (nuSL Fr.y0 Fr.y0_ne) := by
  refine ⟨(map_zero _).symm, Fr.κ1σy0.symm⟩

theorem exists_frame (hL : Nat.card L = (p ^ f) ^ 2) {κ0 κ1 : L} (h0 : κ0 ≠ 0) (h1 : κ1 ≠ 0)
    (h0σ : unitaryInvolution L p f κ0 = κ0) (h1σ : unitaryInvolution L p f κ1 = κ1) :
    ∃ Fr : FrameData L p f, Fr.κ0 = κ0 ∧ Fr.κ1 = κ1 := by
  have hσ := isUnitaryInvolution_unitaryInvolution hL
  obtain ⟨n2, hn2⟩ := hσ.exists_norm (d := -κ0) (by rw [map_neg, h0σ])
  obtain ⟨y0, hy0⟩ := hσ.exists_norm (d := -κ1⁻¹) (by rw [map_neg, map_inv₀, h1σ])
  obtain ⟨n6, hn6⟩ := hσ.exists_norm (d := (κ0 * κ1 ^ 3)⁻¹)
    (by rw [map_inv₀, map_mul, map_pow, h0σ, h1σ])
  exact ⟨⟨κ0, κ1, n2, n6, y0, h0, h1, h0σ, h1σ, hn2, hy0, hn6⟩, rfl, rfl⟩

end ShapeSec

section Gens

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

abbrev rA (M : SL2 L) : adjointGroup Tag.G2 L := rhoG L (Pi.single ia 1) M

abbrev rB (M : SL2 L) : adjointGroup Tag.G2 L := rhoG L (Pi.single ib 1) M

@[expose] def genSet (p f : ℕ) [Fact p.Prime] [CharP L p] (κ0 κ1 : L) :
    Set (adjointGroup Tag.G2 L) :=
  {g | ∃ M : SL2 L, ShapeP (p := p) (f := f) κ0 M ∧ g = rA M} ∪
    {g | ∃ M : SL2 L, ShapeP (p := p) (f := f) κ1 M ∧ g = rB M}

@[expose] def HA (p f : ℕ) [Fact p.Prime] [CharP L p] (κ0 κ1 : L) :
    Subgroup (adjointGroup Tag.G2 L) :=
  Subgroup.closure (genSet p f κ0 κ1)

theorem rA_mem {κ0 κ1 : L} {M : SL2 L} (h : ShapeP (p := p) (f := f) κ0 M) :
    rA M ∈ HA p f κ0 κ1 :=
  Subgroup.subset_closure (Or.inl ⟨M, h, rfl⟩)

theorem rB_mem {κ0 κ1 : L} {M : SL2 L} (h : ShapeP (p := p) (f := f) κ1 M) :
    rB M ∈ HA p f κ0 κ1 :=
  Subgroup.subset_closure (Or.inr ⟨M, h, rfl⟩)

end Gens

section GenLemmas

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

theorem mat_rA (M : SL2 L) :
    ((rep7 L (rA M) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) =
      theta0 (M : Matrix (Fin 2) (Fin 2) L) := phi7_a_eq L M

theorem mat_rB (M : SL2 L) :
    ((rep7 L (rB M) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) =
      theta1 (M : Matrix (Fin 2) (Fin 2) L) := phi7_b_eq L M

theorem rep7_rA_mem (M : SL2 L) : rep7 L (rA M) ∈ BDGrp L := by
  refine ⟨by rw [mat_rA]; exact isBD_theta0 _, ?_⟩
  have h : (rep7 L (rA M))⁻¹ = rep7 L (rA M⁻¹) := by rw [← map_inv, ← map_inv]
  rw [h, mat_rA]
  exact isBD_theta0 _

theorem psi_rA (Fr : FrameData L p f) (M : SL2 L) :
    ((psi (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) ⟨rep7 L (rA M), rep7_rA_mem M⟩ : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) =
      !![(M : Matrix (Fin 2) (Fin 2) L) 0 0, Fr.n2 * (M : Matrix (Fin 2) (Fin 2) L) 0 1, 0;
        Fr.n2⁻¹ * (M : Matrix (Fin 2) (Fin 2) L) 1 0, (M : Matrix (Fin 2) (Fin 2) L) 1 1, 0;
        0, 0, 1] := by
  rw [coe_psi]
  change (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne : Matrix (Fin 3) (Fin 3) L) *
      blk ((rep7 L (rA M) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *
        ((Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne)⁻¹ : GL (Fin 3) L) = _
  rw [mat_rA, blk_theta0]
  exact scale_blk_theta0 _ _ _ _ _

@[expose] def sB (Fr : FrameData L p f) (M : SL2 L) : adjointGroup Tag.G2 L :=
  rB (nuSL Fr.y0 Fr.y0_ne) * rA M * (rB (nuSL Fr.y0 Fr.y0_ne))⁻¹

theorem sB_inv (Fr : FrameData L p f) (M : SL2 L) : (sB Fr M)⁻¹ = sB Fr M⁻¹ := by
  simp [sB, map_inv, _root_.mul_inv_rev, mul_assoc]

theorem mat_sB (Fr : FrameData L p f) (M : SL2 L) :
    ((rep7 L (sB Fr M) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) =
      theta2 Fr.y0 (M : Matrix (Fin 2) (Fin 2) L) := by
  have h1 : ((rep7 L (rB (nuSL Fr.y0 Fr.y0_ne)) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) =
      theta1 !![0, Fr.y0; -Fr.y0⁻¹, 0] := by rw [mat_rB, coe_nuSL]
  have h2 : ((rep7 L ((rB (nuSL Fr.y0 Fr.y0_ne))⁻¹) : GL (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) = theta1 !![0, -Fr.y0; Fr.y0⁻¹, 0] := by
    rw [← map_inv (rhoG L (Pi.single ib 1)) (nuSL Fr.y0 Fr.y0_ne)]
    exact (mat_rB (nuSL Fr.y0 Fr.y0_ne)⁻¹).trans (by rw [coe_nuSL_inv])
  rw [sB, map_mul, map_mul, Units.val_mul, Units.val_mul, h1, h2, mat_rA]
  exact theta1_conj Fr.y0_ne _

theorem rep7_sB_mem (Fr : FrameData L p f) (M : SL2 L) : rep7 L (sB Fr M) ∈ BDGrp L := by
  refine ⟨by rw [mat_sB]; exact isBD_theta2 _ _, ?_⟩
  rw [← map_inv, sB_inv, mat_sB]
  exact isBD_theta2 _ _

theorem psi_sB (Fr : FrameData L p f) (M : SL2 L) :
    ((psi (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) ⟨rep7 L (sB Fr M), rep7_sB_mem Fr M⟩ :
      GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      !![1, 0, 0;
        0, (M : Matrix (Fin 2) (Fin 2) L) 0 0,
          -((M : Matrix (Fin 2) (Fin 2) L) 0 1 * Fr.y0 ^ 3 * Fr.n6⁻¹);
        0, -(Fr.n6 * ((M : Matrix (Fin 2) (Fin 2) L) 1 0 * (Fr.y0 ^ 3)⁻¹)),
          (M : Matrix (Fin 2) (Fin 2) L) 1 1] := by
  rw [coe_psi]
  change (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne : Matrix (Fin 3) (Fin 3) L) *
      blk ((rep7 L (sB Fr M) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *
        ((Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne)⁻¹ : GL (Fin 3) L) = _
  rw [mat_sB, blk_theta2]
  exact scale_blk_theta2 _ _ _ _ _ _

end GenLemmas

section Pre

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

theorem exists_pre12 (Fr : FrameData L p f) (U : SUid (unitaryInvolution L p f) 2) :
    ∃ s ∈ HA p f Fr.κ0 Fr.κ1, ∃ hQ : rep7 L s ∈ BDGrp L,
      psi (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) ⟨rep7 L s, hQ⟩ =
        ((embSUid (unitaryInvolution L p f) 2 U : SUid (unitaryInvolution L p f) 3) :
          GL (Fin 3) L) := by
  obtain ⟨h11, h10⟩ := su2_entries U
  have hdet := (mem_SUid.1 U.2).1
  set X := ((U : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) with hX
  rw [Matrix.det_fin_two, h11, h10] at hdet
  have hn2 := Fr.n2_ne
  have hσn2 : unitaryInvolution L p f Fr.n2 ≠ 0 := (map_ne_zero _).mpr hn2
  have hdet' : X 0 0 * unitaryInvolution L p f (X 0 0) -
      X 0 1 / Fr.n2 * (-unitaryInvolution L p f (X 0 1) * Fr.n2) = 1 := by
    field_simp
    linear_combination hdet
  set M : SL2 L := mkSL (X 0 0) (X 0 1 / Fr.n2) (-unitaryInvolution L p f (X 0 1) * Fr.n2)
    (unitaryInvolution L p f (X 0 0)) hdet' with hM
  have hshape : ShapeP (p := p) (f := f) Fr.κ0 M := by
    refine ⟨rfl, ?_⟩
    change -unitaryInvolution L p f (X 0 1) * Fr.n2 =
      Fr.κ0 * unitaryInvolution L p f (X 0 1 / Fr.n2)
    rw [map_div₀]
    field_simp
    linear_combination (-unitaryInvolution L p f (X 0 1)) * Fr.hn2
  refine ⟨rA M, rA_mem hshape, rep7_rA_mem M, ?_⟩
  refine Units.ext ?_
  rw [psi_rA, coe_embSUid, ← hX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, hM, mkSL, h11, h10] <;> (try field_simp)

theorem exists_pre23 (Fr : FrameData L p f) (U : SUid (unitaryInvolution L p f) 2) :
    ∃ s ∈ HA p f Fr.κ0 Fr.κ1, ∃ hQ : rep7 L s ∈ BDGrp L,
      psi (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) ⟨rep7 L s, hQ⟩ =
        ((embSUid (unitaryInvolution L p f) 0 U : SUid (unitaryInvolution L p f) 3) :
          GL (Fin 3) L) := by
  obtain ⟨h11, h10⟩ := su2_entries U
  have hdet := (mem_SUid.1 U.2).1
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) L,
      X = ((U : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := ⟨_, rfl⟩
  rw [← hX] at hdet h11 h10
  rw [Matrix.det_fin_two, h11, h10] at hdet
  have hn6 := Fr.n6_ne
  have hy0 := Fr.y0_ne
  have hkey : (unitaryInvolution L p f Fr.y0 * Fr.y0) ^ 3 =
      -Fr.κ0 * (unitaryInvolution L p f Fr.n6 * Fr.n6) := by
    rw [Fr.hy0, Fr.hn6]
    have := Fr.hκ0
    have := Fr.hκ1
    field_simp
  have hdet' : X 0 0 * unitaryInvolution L p f (X 0 0) -
      -(X 0 1 * Fr.n6 * (Fr.y0 ^ 3)⁻¹) *
        (unitaryInvolution L p f (X 0 1) * Fr.y0 ^ 3 * Fr.n6⁻¹) = 1 := by
    field_simp
    linear_combination hdet
  set M : SL2 L := mkSL (X 0 0) (-(X 0 1 * Fr.n6 * (Fr.y0 ^ 3)⁻¹))
    (unitaryInvolution L p f (X 0 1) * Fr.y0 ^ 3 * Fr.n6⁻¹) (unitaryInvolution L p f (X 0 0))
    hdet' with hM
  have hshape : ShapeP (p := p) (f := f) Fr.κ0 M := by
    refine ⟨rfl, ?_⟩
    change unitaryInvolution L p f (X 0 1) * Fr.y0 ^ 3 * Fr.n6⁻¹ =
      Fr.κ0 * unitaryInvolution L p f (-(X 0 1 * Fr.n6 * (Fr.y0 ^ 3)⁻¹))
    have hσy : unitaryInvolution L p f Fr.y0 ≠ 0 := (map_ne_zero _).mpr hy0
    have hσn : unitaryInvolution L p f Fr.n6 ≠ 0 := (map_ne_zero _).mpr hn6
    rw [map_neg, map_mul, map_mul, map_inv₀, map_pow]
    field_simp
    linear_combination (unitaryInvolution L p f (X 0 1)) * hkey
  refine ⟨sB Fr M, ?_, rep7_sB_mem Fr M, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (rB_mem (shapeP_nu Fr)) (rA_mem hshape))
      (Subgroup.inv_mem _ (rB_mem (shapeP_nu Fr)))
  refine Units.ext ?_
  rw [psi_sB, coe_embSUid, ← hX]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair, hM, mkSL, h11, h10, hn6, hy0]
  all_goals field_simp

end Pre

section Count

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

@[expose] def QG (L : Type) [Field L] [Finite L] : Subgroup (adjointGroup Tag.G2 L) :=
  (BDGrp L).comap (rep7 L)

@[expose] def phiQ (D : GL (Fin 3) L) : QG L →* GL (Fin 3) L :=
  (psi D).comp ((rep7 L).subgroupComap (BDGrp L))

theorem phiQ_apply (D : GL (Fin 3) L) (s : adjointGroup Tag.G2 L) (hQ : rep7 L s ∈ BDGrp L) :
    phiQ D ⟨s, hQ⟩ = psi D ⟨rep7 L s, hQ⟩ := rfl

@[expose] def WH (Fr : FrameData L p f) : Subgroup (QG L) :=
  (HA p f Fr.κ0 Fr.κ1).comap (QG L).subtype ⊓
    (SUid (unitaryInvolution L p f) 3).comap (phiQ (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne))

@[expose] def psiW (Fr : FrameData L p f) : WH Fr →* Su L p f 3 :=
  ((phiQ (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne)).comp (WH Fr).subtype).codRestrict
    (SUid (unitaryInvolution L p f) 3) fun w => w.2.2

theorem coe_psiW (Fr : FrameData L p f) (w : WH Fr) :
    ((psiW Fr w : Su L p f 3) : GL (Fin 3) L) =
      phiQ (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) w.1 := rfl

theorem psiW_surj (Fr : FrameData L p f) (hL : Nat.card L = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) :
    Function.Surjective (psiW Fr) := by
  refine surj_of_blocks hL hq (psiW Fr) ?_ ?_
  · intro U
    obtain ⟨s, hsH, hQ, hφ⟩ := exists_pre12 Fr U
    have hmem : phiQ (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) ⟨s, hQ⟩ ∈
        SUid (unitaryInvolution L p f) 3 := by
      rw [phiQ_apply, hφ]
      exact (embSUid (unitaryInvolution L p f) 2 U).2
    exact ⟨⟨⟨s, hQ⟩, hsH, hmem⟩, Subtype.ext hφ⟩
  · intro U
    obtain ⟨s, hsH, hQ, hφ⟩ := exists_pre23 Fr U
    have hmem : phiQ (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) ⟨s, hQ⟩ ∈
        SUid (unitaryInvolution L p f) 3 := by
      rw [phiQ_apply, hφ]
      exact (embSUid (unitaryInvolution L p f) 0 U).2
    exact ⟨⟨⟨s, hQ⟩, hsH, hmem⟩, Subtype.ext hφ⟩

theorem card_WH (Fr : FrameData L p f) (hL : Nat.card L = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) :
    (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) ≤ Nat.card (WH Fr) := by
  rw [← su3_card hL]
  exact Nat.card_le_card_of_surjective _ (psiW_surj Fr hL hq)

end Count

section OrbitStab

variable {G : Type*} [Group G] {L : Type*} [Field L]

@[expose, instance_reducible] def actOf (ρ : G →* GL (Fin 7) L) : MulAction G (Fin 7 → L) where
  smul g v := (ρ g : Matrix (Fin 7) (Fin 7) L) *ᵥ v
  one_smul v := by
    show ((ρ 1 : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *ᵥ v = v
    simp
  mul_smul g h v := by
    show ((ρ (g * h) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *ᵥ v =
      ((ρ g : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *ᵥ
        (((ρ h : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *ᵥ v)
    simp [Matrix.mulVec_mulVec]

theorem card_eq_orbit_stab [Finite G] (ρ : G →* GL (Fin 7) L) (w : Fin 7 → L) :
    Nat.card G = (Set.range fun g : G => (ρ g : Matrix (Fin 7) (Fin 7) L) *ᵥ w).ncard *
      Nat.card {g : G // (ρ g : Matrix (Fin 7) (Fin 7) L) *ᵥ w = w} := by
  let _ := actOf ρ
  have e := MulAction.orbitProdStabilizerEquivGroup G w
  rw [← Nat.card_congr e, Nat.card_prod]
  rfl

end OrbitStab

section Index

theorem eq_of_le_of_card_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    (h : Nat.card K < 2 * Nat.card H) : H = K := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  have e : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [e] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx0 : (H.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : (H.subgroupOf K).index = 1 := by
    by_contra hne
    have : 2 ≤ (H.subgroupOf K).index := by omega
    nlinarith
  have : H.subgroupOf K = ⊤ := Subgroup.index_eq_one.1 hidx
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 this)

end Index

section Orbit

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

theorem orbitVec (M : SL2 L) (k : Fin 7) :
    (((rep7 L (rB M) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *ᵥ
      (Pi.single 0 1 : Fin 7 → L)) k = theta1 (M : Matrix (Fin 2) (Fin 2) L) k 0 := by
  rw [mat_rB, Matrix.mulVec_single_one, Matrix.col_apply]

theorem act_pr (Fr : FrameData L p f) (w : WH Fr) (v : Fin 7 → L) :
    (((rep7 L ((w.1 : QG L) : adjointGroup Tag.G2 L) : GL (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) *ᵥ v) 0 = v 0 ∧
    ((Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *ᵥ
        (fun m => (((rep7 L ((w.1 : QG L) : adjointGroup Tag.G2 L) : GL (Fin 7) L) :
          Matrix (Fin 7) (Fin 7) L) *ᵥ v) (eV m)) =
      ((phiQ (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) w.1 : GL (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L) *ᵥ
        (((Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *ᵥ
          fun m => v (eV m)) := by
  set D := Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne with hD
  have hBD := (mem_BDGrp.1 (w.1).2).1
  refine ⟨mulVec_zero hBD v, ?_⟩
  have h1 : (fun m => (((rep7 L ((w.1 : QG L) : adjointGroup Tag.G2 L) : GL (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) *ᵥ v) (eV m)) =
      blk (((rep7 L ((w.1 : QG L) : adjointGroup Tag.G2 L) : GL (Fin 7) L) :
        Matrix (Fin 7) (Fin 7) L)) *ᵥ fun m => v (eV m) := funext fun m => mulVec_eV hBD v m
  have h2 : ((phiQ D w.1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (D : Matrix (Fin 3) (Fin 3) L) * blk (((rep7 L ((w.1 : QG L) : adjointGroup Tag.G2 L) :
        GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L)) *
        ((D⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) :=
    coe_psi D ⟨rep7 L ((w.1 : QG L) : adjointGroup Tag.G2 L), w.1.2⟩
  have h3 : ((D⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
      (D : Matrix (Fin 3) (Fin 3) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1, h2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
    h3, Matrix.mul_one]

theorem pairSet_subset (Fr : FrameData L p f) (hL : Nat.card L = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    (h2 : (2 : L) ≠ 0) :
    pairSet (unitaryInvolution L p f) Fr.κ1 ⊆
      (fun v : Fin 7 → L => (v 0, ((Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne : GL (Fin 3) L) :
          Matrix (Fin 3) (Fin 3) L) *ᵥ fun m => v (eV m))) ''
        Set.range (fun g : HA p f Fr.κ0 Fr.κ1 =>
          ((rep7 L (g : adjointGroup Tag.G2 L) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *ᵥ
            (Pi.single 0 1 : Fin 7 → L)) := by
  rintro ⟨b, x'⟩ ⟨hb, hb2, hx⟩
  have hσ : IsUnitaryInvolution (unitaryInvolution L p f) :=
    isUnitaryInvolution_unitaryInvolution hL
  have hσ2 : unitaryInvolution L p f 2 = 2 := map_ofNat _ 2
  have hκ := Fr.hκ1
  have hκσ := Fr.hκ1σ
  obtain ⟨y, hy⟩ := hσ.exists_norm (d := (b - 1) / (2 * Fr.κ1))
    (by rw [map_div₀, map_sub, hb, map_one, map_mul, hσ2, hκσ])
  obtain ⟨x, hx0⟩ := hσ.exists_norm (d := (b + 1) / 2)
    (by rw [map_div₀, map_add, hb, map_one, hσ2])
  have e1 : x * unitaryInvolution L p f x = (b + 1) / 2 := by rw [mul_comm]; exact hx0
  have e2 : y * unitaryInvolution L p f y = (b - 1) / (2 * Fr.κ1) := by rw [mul_comm]; exact hy
  have hdet : x * unitaryInvolution L p f x - y * (Fr.κ1 * unitaryInvolution L p f y) = 1 := by
    calc x * unitaryInvolution L p f x - y * (Fr.κ1 * unitaryInvolution L p f y)
        = x * unitaryInvolution L p f x - Fr.κ1 * (y * unitaryInvolution L p f y) := by ring
      _ = (b + 1) / 2 - Fr.κ1 * ((b - 1) / (2 * Fr.κ1)) := by rw [e1, e2]
      _ = 1 := by field_simp; ring
  set M : SL2 L := mkSL x y (Fr.κ1 * unitaryInvolution L p f y) (unitaryInvolution L p f x) hdet
    with hM
  have hshape : ShapeP (p := p) (f := f) Fr.κ1 M := ⟨rfl, rfl⟩
  have hgH : rB M ∈ HA p f Fr.κ0 Fr.κ1 := rB_mem hshape
  set v : Fin 7 → L := ((rep7 L (rB M) : GL (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) *ᵥ
    (Pi.single 0 1 : Fin 7 → L) with hv
  have hv0 : v 0 = b := by
    have : v 0 = x * unitaryInvolution L p f x + y * (Fr.κ1 * unitaryInvolution L p f y) := by
      rw [hv, orbitVec]
      simp [theta1, hM, mkSL]
    rw [this, e1, ← mul_assoc, mul_comm y, mul_assoc, e2]
    field_simp
    ring
  have hv1 : v (eV 1) = 2 * (x * y) := by
    rw [hv, orbitVec]
    simp [theta1, hM, mkSL, eV]
  have hv2 : v (eV 0) = 0 := by
    rw [hv, orbitVec]
    simp [theta1, hM, mkSL, eV]
  have hv3 : v (eV 2) = 0 := by
    rw [hv, orbitVec]
    simp [theta1, hM, mkSL, eV]
  set u : Fin 3 → L := ![0, 2 * (x * y), 0] with hu
  have hDv : ((Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *ᵥ
      (fun m => v (eV m)) = u := by
    rw [coe_Dm]
    ext i
    rw [Matrix.mulVec_diagonal]
    fin_cases i
    · simp [hv2, hu]
    · simp [hv1, hu]
    · simp [hv3, hu]
  have hc : herm (unitaryInvolution L p f) u u = (b ^ 2 - 1) / Fr.κ1 := by
    have : herm (unitaryInvolution L p f) u u =
        unitaryInvolution L p f (2 * (x * y)) * (2 * (x * y)) := by
      simp [herm, hu, Fin.sum_univ_three]
    rw [this]
    simp only [map_mul, hσ2]
    have : 2 * (unitaryInvolution L p f x * unitaryInvolution L p f y) * (2 * (x * y)) =
        4 * ((x * unitaryInvolution L p f x) * (y * unitaryInvolution L p f y)) := by ring
    rw [this, e1, e2]
    field_simp
    ring
  have hc0 : herm (unitaryInvolution L p f) u u ≠ 0 := by
    rw [hc]
    exact div_ne_zero (sub_ne_zero.2 hb2) hκ
  have hx'c : herm (unitaryInvolution L p f) x' x' = herm (unitaryInvolution L p f) u u := by
    rw [hc]
    exact hx
  obtain ⟨U, hU⟩ := su3_trans hL h2 hx'c.symm hc0
  obtain ⟨w, hw⟩ := psiW_surj Fr hL hq U
  have hφ : ((phiQ (Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne) w.1 : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) = ((U : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
    rw [← coe_psiW, hw]
  refine ⟨_, ⟨⟨(w.1 : adjointGroup Tag.G2 L) * rB M, Subgroup.mul_mem _ w.2.1 hgH⟩, rfl⟩, ?_⟩
  obtain ⟨hz, hmid⟩ := act_pr Fr w v
  have hact : ((rep7 L ((w.1 : adjointGroup Tag.G2 L) * rB M) : GL (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) *ᵥ (Pi.single 0 1 : Fin 7 → L) =
      ((rep7 L ((w.1 : QG L) : adjointGroup Tag.G2 L) : GL (Fin 7) L) :
        Matrix (Fin 7) (Fin 7) L) *ᵥ v := by
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  refine Prod.ext ?_ ?_
  · change (((rep7 L ((w.1 : adjointGroup Tag.G2 L) * rB M) : GL (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) *ᵥ (Pi.single 0 1 : Fin 7 → L)) 0 = b
    rw [hact, hz, hv0]
  · change ((Dm Fr.n2 Fr.n6 Fr.n2_ne Fr.n6_ne : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *ᵥ
      (fun m => (((rep7 L ((w.1 : adjointGroup Tag.G2 L) * rB M) : GL (Fin 7) L) :
        Matrix (Fin 7) (Fin 7) L) *ᵥ (Pi.single 0 1 : Fin 7 → L)) (eV m)) = x'
    rw [hact, hmid, hDv, hφ, hU]

theorem card_HA_lower (Fr : FrameData L p f) (hL : Nat.card L = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    (h2 : (2 : L) ≠ 0) :
    (p ^ f - 2) * ((p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1)) *
        ((p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) ≤
      Nat.card (HA p f Fr.κ0 Fr.κ1) := by
  have key := card_eq_orbit_stab ((rep7 L).comp (HA p f Fr.κ0 Fr.κ1).subtype)
    (Pi.single 0 1 : Fin 7 → L)
  have h1 : (pairSet (unitaryInvolution L p f) Fr.κ1).ncard ≤
      (Set.range fun g : HA p f Fr.κ0 Fr.κ1 =>
        (((rep7 L).comp (HA p f Fr.κ0 Fr.κ1).subtype g : GL (Fin 7) L) :
          Matrix (Fin 7) (Fin 7) L) *ᵥ (Pi.single 0 1 : Fin 7 → L)).ncard :=
    (Set.ncard_le_ncard (pairSet_subset Fr hL hq h2) (Set.toFinite _)).trans
      (Set.ncard_image_le (Set.toFinite _))
  have h3 : (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) ≤
      Nat.card {g : HA p f Fr.κ0 Fr.κ1 //
        (((rep7 L).comp (HA p f Fr.κ0 Fr.κ1).subtype g : GL (Fin 7) L) :
          Matrix (Fin 7) (Fin 7) L) *ᵥ (Pi.single 0 1 : Fin 7 → L) = Pi.single 0 1} := by
    refine (card_WH Fr hL hq).trans (Nat.card_le_card_of_injective
      (fun w : WH Fr => ⟨⟨((w.1 : QG L) : adjointGroup Tag.G2 L), w.2.1⟩,
        mulVec_w0 (mem_BDGrp.1 (w.1).2).1⟩) ?_)
    intro a b hab
    have := congrArg (fun z => ((z.1 : HA p f Fr.κ0 Fr.κ1) : adjointGroup Tag.G2 L)) hab
    exact Subtype.ext (Subtype.ext this)
  rw [key]
  exact Nat.mul_le_mul ((pairSet_ncard hL Fr.hκ1 Fr.hκ1σ).trans h1) h3

end Orbit

section Final

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

theorem generation_core (hL : Nat.card L = (p ^ f) ^ 2) (hq5 : 5 ≤ p ^ f) (h2 : (2 : L) ≠ 0)
    {Γ : Subgroup (ModGL Tag.G2 L)} (hΓ : Γ ≤ adjointGroup Tag.G2 L)
    (hcard : Nat.card Γ = CFSG.Open.ordG2 (p ^ f)) {κ0 κ1 : L} (h0 : κ0 ≠ 0) (h1 : κ1 ≠ 0)
    (h0σ : unitaryInvolution L p f κ0 = κ0) (h1σ : unitaryInvolution L p f κ1 = κ1)
    (hA : ∀ M : SL2 L, ShapeP (p := p) (f := f) κ0 M →
      rootSL2 Tag.G2 L (Pi.single ia 1) M ∈ Γ)
    (hB : ∀ M : SL2 L, ShapeP (p := p) (f := f) κ1 M →
      rootSL2 Tag.G2 L (Pi.single ib 1) M ∈ Γ) :
    Γ ≤ ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
      rootRankOneGroup Tag.G2 L α.1 ⊓ Γ := by
  obtain ⟨Fr, rfl, rfl⟩ := exists_frame hL h0 h1 h0σ h1σ
  have hq : p ^ f ≠ 2 := by omega
  have hle : HA p f Fr.κ0 Fr.κ1 ≤ Γ.subgroupOf (adjointGroup Tag.G2 L) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨M, hM, rfl⟩ | ⟨M, hM, rfl⟩)
    · exact hA M hM
    · exact hB M hM
  have hcardΓ : Nat.card (Γ.subgroupOf (adjointGroup Tag.G2 L)) = Nat.card Γ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv
  have hlt : Nat.card (Γ.subgroupOf (adjointGroup Tag.G2 L)) <
      2 * Nat.card (HA p f Fr.κ0 Fr.κ1) := by
    rw [hcardΓ, hcard, CFSG.Open.ordG2]
    have h3 := arith_ineq hq5
    have h4 := card_HA_lower Fr hL hq h2
    calc _ < 2 * ((p ^ f - 2) * ((p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1))) *
          ((p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := h3
      _ = 2 * ((p ^ f - 2) * ((p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1)) *
          ((p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1))) := by rw [mul_assoc 2]
      _ ≤ _ := Nat.mul_le_mul_left 2 h4
  have heq := eq_of_le_of_card_lt hle hlt
  have hmap : (HA p f Fr.κ0 Fr.κ1).map (adjointGroup Tag.G2 L).subtype ≤
      ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
        rootRankOneGroup Tag.G2 L α.1 ⊓ Γ := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨M, hM, rfl⟩ | ⟨M, hM, rfl⟩)
    · exact Subgroup.mem_iSup_of_mem (⟨Pi.single ia 1, isRoot_single _ ia⟩ :
        {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α}) ⟨⟨M, rfl⟩, hA M hM⟩
    · exact Subgroup.mem_iSup_of_mem (⟨Pi.single ib 1, isRoot_single _ ib⟩ :
        {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α}) ⟨⟨M, rfl⟩, hB M hM⟩
  intro γ hγ
  have hmem : (⟨γ, hΓ hγ⟩ : adjointGroup Tag.G2 L) ∈ HA p f Fr.κ0 Fr.κ1 := by
    rw [heq]
    exact hγ
  exact hmap ⟨_, hmem, rfl⟩

end Final

section Main

open CFSG.RankThree.Chevalley CFSG.RankThree.QuadraticSL2 in
theorem g2_qplus_generation {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    (hq5 : 5 ≤ Nat.card K) (K₂ : Type) [Field K₂] [Algebra K K₂]
    (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K)
    {g z : ModGL Tag.G2 K₂} (hg : g ∈ adjointGroup Tag.G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup Tag.G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom Tag.G2 K₂ ⟨z, hz⟩ • v = -v) :
    ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
      rootRankOneGroup Tag.G2 K₂ α.1 ⊓ conjEntrywiseImage K g = conjEntrywiseImage K g := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  obtain ⟨hσσ, -⟩ := exists_frobenius_eq_neg hdeg σ hσ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hpn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hcardK : Nat.card K = (ringChar K) ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hpn
  have : CharP K₂ (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K K₂).injective _
  have hL : Nat.card K₂ = ((ringChar K) ^ (n : ℕ)) ^ 2 := by
    rw [natCard_eq_sq_of_finrank_eq_two hdeg, hcardK]
  have hσu : unitaryInvolution K₂ (ringChar K) (n : ℕ) = σ :=
    RingEquiv.ext fun c => by rw [unitaryInvolution_apply, hσ, hcardK]
  have hodd₂ : Odd (Nat.card K₂) := by
    rw [natCard_eq_sq_of_finrank_eq_two hdeg]
    exact hK.pow
  have h2 : (2 : K₂) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_natCard hodd₂)
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hzz := twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hσσ hzdef
  have hΓA : conjEntrywiseImage K g ≤ adjointGroup Tag.G2 K₂ := by
    rw [hΓ]
    exact inf_le_left
  have hcard : Nat.card (conjEntrywiseImage K g) = CFSG.Open.ordG2 (Nat.card K) := by
    rw [natCard_conjEntrywiseImage, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  rw [hcardK] at hcard hq5
  obtain ⟨κ0, hκ0, hκ0σ, hfixA⟩ := exists_shape σ hσσ hz hw hzz (isRoot_single Tag.G2 ia)
  obtain ⟨κ1, hκ1, hκ1σ, hfixB⟩ := exists_shape σ hσσ hz hw hzz (isRoot_single Tag.G2 ib)
  refine le_antisymm (iSup_le fun α => inf_le_right) ?_
  refine generation_core hL hq5 h2 hΓA hcard hκ0 hκ1 (by rw [hσu]; exact hκ0σ)
    (by rw [hσu]; exact hκ1σ) (fun M hM => ?_) (fun M hM => ?_)
  · simp only [ShapeP, hσu] at hM
    exact rootSL2_shape_mem σ hΓ (hfixA M hM.1 hM.2)
  · simp only [ShapeP, hσu] at hM
    exact rootSL2_shape_mem σ hΓ (hfixB M hM.1 hM.2)

end Main

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
