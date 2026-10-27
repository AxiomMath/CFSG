module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofTorus
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofNormal

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem conjM'_mul (hπ : π = false → UnitaryFieldData p f K) {g h : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hh : h ∈ glPi π 3 (p ^ f) K) :
    Res8Hess.conjM' hπ (mul_mem hg hh) = Res8Hess.conjM' hπ hg * Res8Hess.conjM' hπ hh := by
  ext m
  rw [MulAut.mul_apply, Res8Hess.coe_conjM', Res8Hess.coe_conjM', Res8Hess.coe_conjM', map_mul]
  group

theorem conjM'_one (hπ : π = false → UnitaryFieldData p f K) :
    Res8Hess.conjM' hπ (one_mem (glPi π 3 (p ^ f) K)) = 1 := by
  ext m
  rw [MulAut.one_apply, Res8Hess.coe_conjM', map_one, one_mul, inv_one, mul_one]

theorem conjM'_eq_conj (hπ : π = false → UnitaryFieldData p f K) (x : slPi π 3 (p ^ f) K) :
    Res8Hess.conjM' hπ (slPi_le_glPi hπ x.2) = MulAut.conj (projOf (slPi π 3 (p ^ f) K) x) := by
  ext m
  rw [Res8Hess.coe_conjM', MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_projOf]

@[expose] def normGU [Finite K] (hπ : π = false → UnitaryFieldData p f K)
    (N : Subgroup (projImage (slPi π 3 (p ^ f) K))) : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ hg : g ∈ glPi π 3 (p ^ f) K, N.map (Res8Hess.conjM' hπ hg).toMonoidHom ≤ N}
  mul_mem' := by
    rintro a b ⟨ha, hNa⟩ ⟨hb, hNb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [conjM'_mul hπ ha hb]
    rintro _ ⟨x, hx, rfl⟩
    exact hNa ⟨_, hNb ⟨x, hx, rfl⟩, rfl⟩
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    rw [conjM'_one hπ]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  inv_mem' := by
    rintro a ⟨ha, hNa⟩
    refine ⟨inv_mem ha, ?_⟩
    have := finite_pgl (K := K)
    rw [L3PGL.conjM'_inv hπ ha]
    exact L3PGL.map_le_of_map_symm_le (by rwa [MulEquiv.symm_symm])

variable [Finite K] (hπ : π = false → UnitaryFieldData p f K)
  {N : Subgroup (projImage (slPi π 3 (p ^ f) K))}

theorem map_le_of_mem_normGU {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hgN : g ∈ normGU hπ N) : N.map (Res8Hess.conjM' hπ hg).toMonoidHom ≤ N := by
  obtain ⟨hg', h⟩ := hgN
  exact h

theorem mem_normGU_of_projOf_mem {x : slPi π 3 (p ^ f) K}
    (hx : projOf (slPi π 3 (p ^ f) K) x ∈ N) : (x : GL (Fin 3) K) ∈ normGU hπ N := by
  refine ⟨slPi_le_glPi hπ x.2, ?_⟩
  rw [conjM'_eq_conj hπ x]
  rintro _ ⟨y, hy, rfl⟩
  exact N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)

theorem scalar_mem_normGU {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ glPi π 3 (p ^ f) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ normGU hπ N := by
  refine ⟨hc, ?_⟩
  have h1 : ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 :=
    mk_eq_one_iff_mem_statedScalars.mpr ⟨c, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  have e : Res8Hess.conjM' hπ hc y = y := by
    apply Subtype.ext
    rw [Res8Hess.coe_conjM', h1, one_mul, inv_one, mul_one]
  change Res8Hess.conjM' hπ hc y ∈ N
  rw [e]
  exact hy

variable {τ : K} (hτ : τ ^ 3 = 1) {β : K} {cβ : GL (Fin 3) K}
  (hcβ : cβ ∈ glPi π 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi π 3 (p ^ f) K)

theorem cβ_mem_normGU :
    cβ ∈ normGU hπ (sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd))) :=
  ⟨hcβ, L3PGL.map_sSup_invSet142_le.1⟩

theorem d_mem_normGU :
    diagTau hτ ∈
      normGU hπ (sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd))) :=
  ⟨hd, L3PGL.map_sSup_invSet142_le.2⟩

omit [Finite K] in
theorem heisC_mul_d₁ (β : K) {τu : Kˣ} (hτu : (τu : K) = τ) :
    heisC β * ((diagUnits 1 τu 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((diagUnits 1 τu 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (heisC β * ((diagTau hτ ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [Units.val_pow_eq_pow_val, coe_diagUnits, coe_diagTau, hτu]
  have h4 : τ ^ 4 = τ := by rw [show τ ^ 4 = τ ^ 3 * τ by ring, hτ, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, Matrix.mul_apply, sq, Matrix.diagonal_apply] <;>
    first | ring1 | linear_combination (-2 : K) * hτ | linear_combination (-τ) * hτ |
      linear_combination hτ | linear_combination (-1 : K) * hτ

theorem d₁_mem_normGU (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) {τu : Kˣ}
    (hτu : (τu : K) = τ) (hD₁ : diagUnits 1 τu 1 ∈ glPi π 3 (p ^ f) K) :
    diagUnits 1 τu 1 ∈
      normGU hπ (sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd))) := by
  refine ⟨hD₁, ?_⟩
  set S := invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd) with hS
  have hc' : cβ * diagTau hτ ^ 2 ∈ glPi π 3 (p ^ f) K := mul_mem hcβ (pow_mem hd 2)
  have hyg : ProjGenLinGroup.mk (cβ * diagUnits 1 τu 1) =
      ProjGenLinGroup.mk (diagUnits 1 τu 1 * (cβ * diagTau hτ ^ 2)) := by
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hcβm]
    exact heisC_mul_d₁ hτ β hτu
  have hsg : ProjGenLinGroup.mk (diagTau hτ * diagUnits 1 τu 1) =
      ProjGenLinGroup.mk (diagUnits 1 τu 1 * diagTau hτ) := by
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagTau_eq_diagonal,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup (L3PGL.map_conjM'_mem_invSet142 hπ hcβ hd hc' hd hD₁ hyg hsg ?_)
  obtain ⟨h3, hXc, hXd⟩ := hX
  refine ⟨h3, ?_, hXd⟩
  have e : Res8Hess.conjM' hπ hc' = Res8Hess.conjM' hπ hcβ *
      (Res8Hess.conjM' hπ hd * Res8Hess.conjM' hπ hd) := by
    rw [← conjM'_mul hπ hd hd, ← conjM'_mul hπ hcβ (mul_mem hd hd)]
    congr 1
    rw [sq]
  rw [e]
  rintro _ ⟨x, hx, rfl⟩
  exact hXc ⟨_, hXd ⟨_, hXd ⟨x, hx, rfl⟩, rfl⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec14.L3PGLU
