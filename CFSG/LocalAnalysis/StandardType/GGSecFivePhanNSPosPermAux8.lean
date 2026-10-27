module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem ggNSPosPA_mem_diagonalTorus_of_isDiag {K : Type} [Field K] {n : ℕ} {g : GL (Fin n) K}
    (hg : ggIsDiagMat g) : g ∈ TauCeti.diagonalTorus K n := by
  obtain ⟨d, hd⟩ := hg
  rw [TauCeti.mem_diagonalTorus_iff, hd]
  exact Matrix.isDiag_diagonal d

@[expose] noncomputable def ggNSPosPA_diagUnits {K : Type} [Field K] {n : ℕ} {g : GL (Fin n) K}
    (hmem : g ∈ TauCeti.diagonalTorus K n) : Fin n → Kˣ :=
  (TauCeti.diagonalTorusEquiv K n).symm ⟨g, hmem⟩

theorem ggNSPosPA_diagGL_diagUnits {K : Type} [Field K] {n : ℕ} {g : GL (Fin n) K}
    (hmem : g ∈ TauCeti.diagonalTorus K n) :
    TauCeti.diagGL (ggNSPosPA_diagUnits hmem) = g := by
  have h1 := TauCeti.coe_diagonalTorusEquiv_apply
    ((TauCeti.diagonalTorusEquiv K n).symm (⟨g, hmem⟩ : TauCeti.diagonalTorus K n))
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1.symm

@[expose] noncomputable def ggNSPosPA_lift {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {Bs : Subgroup G} (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (s : ↥Bs) : GL (Fin n) K :=
  Classical.choose (hd s s.2)

theorem ggNSPosPA_lift_diag {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {Bs : Subgroup G} (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (s : ↥Bs) : ggIsDiagMat (ggNSPosPA_lift hd s) :=
  (Classical.choose_spec (hd s s.2)).1

theorem ggNSPosPA_lift_induces {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {Bs : Subgroup G} (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (s : ↥Bs) :
    GGInducesUnitary (p := 2) (f := f) ψ (s : G) (ggNSPosPA_lift hd s) :=
  (Classical.choose_spec (hd s s.2)).2

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

@[expose] noncomputable def ggNSPosPA_liftUnits {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} {Bs : Subgroup G}
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (s : ↥Bs) : Fin n → Kˣ :=
  ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag (ggNSPosPA_lift_diag hd s))

theorem ggNSPosPA_diagGL_liftUnits {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} {Bs : Subgroup G}
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (s : ↥Bs) :
    TauCeti.diagGL (ggNSPosPA_liftUnits hd s) = ggNSPosPA_lift hd s :=
  ggNSPosPA_diagGL_diagUnits _

@[expose] def ggNSPosPA_ratioOfUnits {K : Type} [Field K] {n : ℕ} (u : Fin n → Kˣ) (a b : Fin n) : Kˣ :=
  u a * (u b)⁻¹

theorem ggNSPosPA_ratioOfUnits_mul {K : Type} [Field K] {n : ℕ} (u v : Fin n → Kˣ)
    (a b : Fin n) :
    ggNSPosPA_ratioOfUnits (u * v) a b =
      ggNSPosPA_ratioOfUnits u a b * ggNSPosPA_ratioOfUnits v a b := by
  apply Units.ext
  simp only [ggNSPosPA_ratioOfUnits, Pi.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

theorem ggNSPosPA_ratio_wd {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) {s : ↥Bs} {g1 g2 : GL (Fin n) K}
    (h1 : ggIsDiagMat g1) (hi1 : GGInducesUnitary (p := 2) (f := f) ψ (s : G) g1)
    (h2 : ggIsDiagMat g2) (hi2 : GGInducesUnitary (p := 2) (f := f) ψ (s : G) g2) (a b : Fin n) :
    ggNSPosPA_ratioOfUnits
        (ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag h1)) a b =
      ggNSPosPA_ratioOfUnits
        (ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag h2)) a b := by
  set u1 := ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag h1)
  set u2 := ggNSPosPA_diagUnits (ggNSPosPA_mem_diagonalTorus_of_isDiag h2)
  have hg1 : TauCeti.diagGL u1 = g1 := ggNSPosPA_diagGL_diagUnits _
  have hg2 : TauCeti.diagGL u2 = g2 := ggNSPosPA_diagGL_diagUnits _
  have hzU : ggIsUnitaryMat (p := 2) (f := f) (g1⁻¹ * g2) :=
    ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv hi1.1) hi2.1
  have hzt := ggNSPosPA_conj_inv_mul_of_same_action (ψ := ψ) hi1 hi2
  obtain ⟨c, hc⟩ := ggNSPosPA_scalar_of_conj_trivial h hzU hzt
  have hzdiag : (g1⁻¹ * g2 : GL (Fin n) K) = TauCeti.diagGL (u1⁻¹ * u2) := by
    rw [← hg1, ← hg2, ← map_inv, ← map_mul]
  have hci : ∀ i, (((u1 i)⁻¹ * u2 i : Kˣ) : K) = c := by
    intro i
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hc
    rw [hzdiag, TauCeti.diagGL_apply] at h2
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, if_pos rfl, if_true,
      Units.val_mul, Units.val_inv_eq_inv_val] at h2
    exact h2
  have hci' : (u1 a)⁻¹ * u2 a = (u1 b)⁻¹ * u2 b := by
    apply Units.ext
    rw [hci a, hci b]
  have key : u1 a * (u1 b)⁻¹ = u2 a * (u2 b)⁻¹ := by
    have h1' : u2 a = u1 a * (u1 b)⁻¹ * u2 b := by
      calc u2 a = u1 a * ((u1 a)⁻¹ * u2 a) := by group
        _ = u1 a * ((u1 b)⁻¹ * u2 b) := by rw [hci']
        _ = u1 a * (u1 b)⁻¹ * u2 b := by group
    rw [h1']
    group
  simpa only [ggNSPosPA_ratioOfUnits, u1, u2] using key

end CFSG.StandardType

end
