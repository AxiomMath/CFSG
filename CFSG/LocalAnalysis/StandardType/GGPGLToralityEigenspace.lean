module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6ElemAux
public import CFSG.Assembly.GL83LieDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

open CFSG.LinearAlgebra
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.Open

variable {K : Type*} [Field K] {n m : ℕ} {G : Subgroup (GL (Fin n) K)}

theorem commute_of_isProjElem_of_finrank_eigenspace
    (hG : IsProjElem 3 G) {E : GL (Fin n) K} (hEG : E ∈ G) {c : K} (hc : c ≠ 0)
    (hm : Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' (E : Matrix (Fin n) (Fin n) K)) c) = m)
    (hn : n < 2 * m) :
    ∀ g ∈ G, g * E = E * g := by
  intro g hg
  by_contra hge
  obtain ⟨u, hu⟩ := hG.comm_scalar g hg E hEG
  have hu1 : u ≠ 1 := by
    intro h1
    exact hge (by simpa [h1] using hu)
  have hconj : g * E * g⁻¹ = GeneralLinearGroup.scalar (Fin n) u * E := by
    rw [hu]
    group
  have hdim : Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' (E : Matrix (Fin n) (Fin n) K)) (((u : K))⁻¹ * c)) = m := by
    rw [finrank_eigenspace_eq_of_conj hconj c]
    exact hm
  have hcne : c ≠ ((u : K))⁻¹ * c := by
    intro h
    have h1 : (1 : K) = ((u : K))⁻¹ := mul_right_cancel₀ hc (by simpa using h)
    exact hu1 (Units.ext (inv_eq_one.mp h1.symm))
  have hdisj : Disjoint
      (Module.End.eigenspace (Matrix.toLin' (E : Matrix (Fin n) (Fin n) K)) c)
      (Module.End.eigenspace (Matrix.toLin' (E : Matrix (Fin n) (Fin n) K))
        (((u : K))⁻¹ * c)) :=
    (Module.End.eigenspaces_iSupIndep
      (Matrix.toLin' (E : Matrix (Fin n) (Fin n) K))).pairwiseDisjoint hcne
  have hsum : m + m ≤ n := by
    have h := Submodule.finrank_add_finrank_le_of_disjoint hdisj
    rwa [hm, hdim, Module.finrank_fin_fun] at h
  omega

theorem pairwise_commute_of_isProjElem_of_eigenspace
    (hG : IsProjElem 3 G) {E : GL (Fin n) K} (hEG : E ∈ G) {c : K} (hc : c ≠ 0)
    (hm : Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' (E : Matrix (Fin n) (Fin n) K)) c) = m)
    (hn : n < 2 * m) (hm3 : ¬ 3 ∣ m) :
    ∀ g ∈ G, ∀ h ∈ G, g * h = h * g := by
  have hEcomm : ∀ g ∈ G, g * E = E * g :=
    commute_of_isProjElem_of_finrank_eigenspace hG hEG hc hm hn
  have hmle : m ≤ n := by
    have h := Submodule.finrank_le (s := Module.End.eigenspace
      (Matrix.toLin' (E : Matrix (Fin n) (Fin n) K)) c)
    rwa [hm, Module.finrank_fin_fun] at h
  have hnpos : 0 < n := by
    have hmpos : 0 < m := by omega
    omega
  have : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  intro g hg h hh
  obtain ⟨κ, hκ⟩ := hG.comm_scalar g hg h hh
  have hκ3 : κ ^ 3 = 1 := by
    rw [← commChar_eq hG hg (x := ⟨h, hh⟩) hκ]
    exact commChar_pow_eq_one hG hg ⟨h, hh⟩
  have hκ1 : κ = 1 := by
    by_contra hκne
    have hcomm : g * h * g⁻¹ * h⁻¹ = GeneralLinearGroup.scalar (Fin n) κ := by
      rw [hκ]
      group
    have h3 := KSFourU.three_dvd_eigenDim g h E κ hκ3 hκne hcomm
      (hEcomm g hg) (hEcomm h hh) c
    have hdim : KSFourU.eigenDim (E : Matrix (Fin n) (Fin n) K) c = m := by
      rw [KSFourU.eigenDim, ← Module.End.one_eq_id, ← Module.End.eigenspace_def]
      exact hm
    exact hm3 (hdim ▸ h3)
  simpa [hκ1] using hκ

theorem pairwise_commute_of_isElemAbelian_comap_map_of_eigenspace_four
    {K : Type} [Field K] {H : Type} [Group H]
    {N : Subgroup (GL (Fin 6) K)}
    (hNscal : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 6) u ∈ N)
    {ρ : N →* H}
    (hρscal : ∀ u : Kˣ, ρ ⟨GeneralLinearGroup.scalar (Fin 6) u, hNscal u⟩ = 1)
    (hker : ρ.ker ≤ (CFSG.Assembly.LargeEvenScalars (Fin 6) K).subgroupOf N)
    {X : Subgroup H} (hX : IsElemAbelian 3 X)
    {E : GL (Fin 6) K} (hE : E ∈ (X.comap ρ).map N.subtype)
    {c : K} (hc : c ≠ 0)
    (hm : Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' (E : Matrix (Fin 6) (Fin 6) K)) c) = 4) :
    ∀ g ∈ (X.comap ρ).map N.subtype, ∀ h ∈ (X.comap ρ).map N.subtype,
      g * h = h * g := by
  have hker' : ∀ x : N, ρ x = 1 → ∃ u : Kˣ,
      (x : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) u := by
    intro x hx
    have hxker : x ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have hxsub : x ∈ (CFSG.Assembly.LargeEvenScalars (Fin 6) K).subgroupOf N :=
      hker hxker
    have hxrange : (x : GL (Fin 6) K) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin 6)).range := by
      rw [← CFSG.Assembly.largeEvenScalars_def]
      exact Subgroup.mem_subgroupOf.mp hxsub
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hxrange
    exact ⟨u, hu.symm⟩
  have hG : IsProjElem 3 ((X.comap ρ).map N.subtype) :=
    isProjElem_comap_map_subtype hNscal hρscal hker' hX
  exact pairwise_commute_of_isProjElem_of_eigenspace
    (G := (X.comap ρ).map N.subtype) (m := 4) hG hE hc hm
    (by norm_num) (by norm_num)

theorem three_dvd_card_fiber_of_isBlockDiag_of_scalar_commutator
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {w : ι → β} {g h : GL ι K} {κ : Kˣ}
    (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1)
    (hg : IsBlockDiag w (g : Matrix ι ι K))
    (hh : IsBlockDiag w (h : Matrix ι ι K))
    (hcomm : (g : Matrix ι ι K) * (h : Matrix ι ι K) =
      Matrix.scalar ι (κ : K) * ((h : Matrix ι ι K) * (g : Matrix ι ι K)))
    (b : β) : 3 ∣ Fintype.card {i // w i = b} := by
  classical
  have hblockscal : IsBlockDiag w (Matrix.scalar ι (κ : K)) := by
    intro i j hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · exact absurd (h ▸ rfl) hij
    · simp [h]
  have hblockcomm : (g : Matrix ι ι K).toSquareBlock w b * (h : Matrix ι ι K).toSquareBlock w b =
      Matrix.scalar {i // w i = b} (κ : K) *
        ((h : Matrix ι ι K).toSquareBlock w b * (g : Matrix ι ι K).toSquareBlock w b) := by
    have heq := congrArg (fun X : Matrix ι ι K => X.toSquareBlock w b) hcomm
    rw [toSquareBlock_mul_of_isBlockDiag hg (h : Matrix ι ι K) b,
      toSquareBlock_mul_of_isBlockDiag hblockscal
        ((h : Matrix ι ι K) * (g : Matrix ι ι K)) b,
      toSquareBlock_mul_of_isBlockDiag hh (g : Matrix ι ι K) b,
      toSquareBlock_scalar] at heq
    exact heq
  have hdetg : ((g : Matrix ι ι K).toSquareBlock w b).det ≠ 0 := by
    refine Matrix.det_ne_zero_of_right_inverse
      (B := (((g⁻¹ : GL ι K) : Matrix ι ι K)).toSquareBlock w b) ?_
    rw [← toSquareBlock_mul_of_isBlockDiag hg ((g⁻¹ : GL ι K) : Matrix ι ι K) b]
    have h1 : (g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1, toSquareBlock_one]
  have hdeth : ((h : Matrix ι ι K).toSquareBlock w b).det ≠ 0 := by
    refine Matrix.det_ne_zero_of_right_inverse
      (B := (((h⁻¹ : GL ι K) : Matrix ι ι K)).toSquareBlock w b) ?_
    rw [← toSquareBlock_mul_of_isBlockDiag hh ((h⁻¹ : GL ι K) : Matrix ι ι K) b]
    have h1 : (h : Matrix ι ι K) * ((h⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1, toSquareBlock_one]
  have hdet_eq : ((g : Matrix ι ι K).toSquareBlock w b).det *
        ((h : Matrix ι ι K).toSquareBlock w b).det =
      (κ : K) ^ Fintype.card {i // w i = b} *
        (((h : Matrix ι ι K).toSquareBlock w b).det *
          ((g : Matrix ι ι K).toSquareBlock w b).det) := by
    have hdet := congrArg Matrix.det hblockcomm
    simpa only [Matrix.det_mul, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ] using hdet
  have hpowK : (κ : K) ^ Fintype.card {i // w i = b} = 1 := by
    have hprodne : ((g : Matrix ι ι K).toSquareBlock w b).det *
        ((h : Matrix ι ι K).toSquareBlock w b).det ≠ 0 := mul_ne_zero hdetg hdeth
    have hdet := hdet_eq
    rw [mul_comm (((h : Matrix ι ι K).toSquareBlock w b).det)
      (((g : Matrix ι ι K).toSquareBlock w b).det)] at hdet
    have hone : (1 : K) * (((g : Matrix ι ι K).toSquareBlock w b).det *
        ((h : Matrix ι ι K).toSquareBlock w b).det) =
        (κ : K) ^ Fintype.card {i // w i = b} *
          (((g : Matrix ι ι K).toSquareBlock w b).det *
            ((h : Matrix ι ι K).toSquareBlock w b).det) := by
      rw [one_mul]
      exact hdet
    exact ((mul_right_cancel₀ hprodne) hone).symm
  have hpowU : κ ^ Fintype.card {i // w i = b} = 1 := Units.ext (by simpa using hpowK)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf κ = 3 := orderOf_eq_prime hκ3 hκ1
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hpowU

theorem card_projImage_le_pow_weightClasses
    [Finite K] {E : Subgroup (GL (Fin n) K)} [Finite E]
    {A : GL (Fin n) K} (w : Fin n → E → K) (i₀ : Fin n)
    (hE3 : ∀ e ∈ E, (e : GL (Fin n) K) ^ 3 = 1)
    (hdiag : ∀ e : E, conjMatrix A (e : GL (Fin n) K) = diagonal (fun i => w i e)) :
    Nat.card (CFSG.PGLModel.projImage E) ≤
      3 ^ (Nat.card (Set.range w) - 1) := by
  classical
  have hne : ∀ (e : E) (i : Fin n), w i e ≠ 0 := by
    intro e i
    have h := diag_ne_zero_of_eq_diagonal (D := A * (e : GL (Fin n) K) * A⁻¹)
      (by simpa [conjMatrix] using hdiag e) i
    simpa using h
  let δu : E →* (Fin n → Kˣ) :=
  { toFun := fun e i => Units.mk0 (w i e) (hne e i)
    map_one' := by
      ext i
      have h : (diagonal (fun i => w i (1 : E)) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← hdiag (1 : E)]
        simpa using conjMatrix_one A
      have h1 := congrFun (congrFun h i) i
      simpa [Matrix.diagonal_apply_eq] using h1
    map_mul' := by
      intro x y
      ext i
      simp only [Pi.mul_apply, Units.val_mul, Units.val_mk0]
      have h : (diagonal (fun i => w i (x * y)) : Matrix (Fin n) (Fin n) K) =
          diagonal (fun i => w i x * w i y) := by
        rw [← hdiag (x * y), Subgroup.coe_mul, conjMatrix_mul, hdiag x, hdiag y,
          diagonal_mul_diagonal]
      have h1 := congrFun (congrFun h i) i
      simpa [Matrix.diagonal_apply_eq] using h1 }
  have hδpow : ∀ (e : E) (i : Fin n), δu e i ^ 3 = 1 := by
    intro e i
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    change w i e ^ 3 = 1
    have h : (1 : Matrix (Fin n) (Fin n) K) = diagonal (fun i => w i e ^ 3) := by
      have h := conjMatrix_pow A (e : GL (Fin n) K) 3
      rw [hE3 (e : GL (Fin n) K) e.2, conjMatrix_one, hdiag e, diagonal_pow] at h
      exact h
    have h1 := congrFun (congrFun h i) i
    simpa [Matrix.diagonal_apply_eq] using h1.symm
  have hδpowK : ∀ (e : E) (i : Fin n), ((δu e i : Kˣ) : K) ^ 3 = 1 :=
    fun e i => by simpa using congrArg (fun u : Kˣ => (u : K)) (hδpow e i)
  let T : Finset (E → K) := (Finset.univ.image w).erase (w i₀)
  have hrep_ex : ∀ b : T, ∃ i : Fin n, w i = (b : E → K) := by
    intro b
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase b.2)
    exact ⟨i, hi⟩
  choose rep hrep using hrep_ex
  let ψ : E →* (T → rootsOfUnity 3 K) :=
  { toFun := fun e b =>
      ⟨δu e (rep b) / δu e i₀, by
        rw [mem_rootsOfUnity]
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_one]
        rw [div_pow, hδpowK e (rep b), hδpowK e i₀]
        simp⟩
    map_one' := by
      ext b
      simp only [Units.val_div_eq_div_val]
      rw [map_one δu]
      simp
    map_mul' := by
      intro x y
      ext b
      simp only [Units.val_div_eq_div_val, Units.val_mul, Subgroup.coe_mul, Pi.mul_apply]
      rw [map_mul δu x y]
      simp only [Pi.mul_apply, Units.val_mul]
      group }
  have hψker : ψ.ker = (GeneralLinearGroup.scalar (Fin n)).range.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hconst : ∀ i : Fin n, δu e i = δu e i₀ := by
        intro i
        by_cases hi : w i = w i₀
        · apply Units.ext
          change w i e = w i₀ e
          exact congrFun hi e
        · have hmem : w i ∈ T :=
            Finset.mem_erase.mpr ⟨hi, Finset.mem_image_of_mem w (Finset.mem_univ i)⟩
          have hb := congrFun h ⟨w i, hmem⟩
          have hb1 : δu e (rep ⟨w i, hmem⟩) / δu e i₀ = 1 := by
            have hval := congrArg (fun x : rootsOfUnity 3 K => (x : Kˣ)) hb
            simpa [ψ] using hval
          have hrep_eq : w (rep ⟨w i, hmem⟩) = w i := hrep ⟨w i, hmem⟩
          have heq1 : δu e i = δu e (rep ⟨w i, hmem⟩) := by
            apply Units.ext
            change w i e = w (rep ⟨w i, hmem⟩) e
            exact (congrFun hrep_eq e).symm
          exact heq1.trans (div_eq_one.mp hb1)
      rw [MonoidHom.mem_range]
      refine ⟨δu e i₀, ?_⟩
      have hdiag_eq : (A * (e : GL (Fin n) K) * A⁻¹ : GL (Fin n) K) =
          GeneralLinearGroup.scalar (Fin n) (δu e i₀) := by
        apply Units.ext
        have hmat : ((A * (e : GL (Fin n) K) * A⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = diagonal (fun i => w i e) := by
          simpa [conjMatrix] using hdiag e
        rw [hmat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          show (fun i : Fin n => w i e) = (fun _ => ((δu e i₀ : Kˣ) : K)) from
            funext fun i => by
              rw [show ((δu e i₀ : Kˣ) : K) = w i₀ e from rfl]
              exact congrArg (fun u : Kˣ => (u : K)) (hconst i)]
      have hcomm : Commute (A⁻¹ : GL (Fin n) K)
          (GeneralLinearGroup.scalar (Fin n) (δu e i₀)) :=
        ((commute_scalar (δu e i₀) A).symm).inv_left
      exact (calc (e : GL (Fin n) K)
          = A⁻¹ * (A * (e : GL (Fin n) K) * A⁻¹) * A := by group
        _ = A⁻¹ * GeneralLinearGroup.scalar (Fin n) (δu e i₀) * A := by rw [hdiag_eq]
        _ = (GeneralLinearGroup.scalar (Fin n) (δu e i₀) * A⁻¹) * A := by rw [hcomm.eq]
        _ = GeneralLinearGroup.scalar (Fin n) (δu e i₀) := by
            rw [mul_assoc, inv_mul_cancel, mul_one]).symm
    · intro hN
      rw [MonoidHom.mem_range] at hN
      obtain ⟨u, hu⟩ := hN
      have hδu_eq : ∀ i : Fin n, δu e i = u := by
        intro i
        apply Units.ext
        have hconj : A * (e : GL (Fin n) K) * A⁻¹ =
            GeneralLinearGroup.scalar (Fin n) u := by
          rw [← hu, ← scalar_mul_comm u A, mul_assoc, mul_inv_cancel, mul_one]
        have hmat : ((A * (e : GL (Fin n) K) * A⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = diagonal (fun i => w i e) := by
          simpa [conjMatrix] using hdiag e
        have h := congrArg (fun x : GL (Fin n) K =>
          ((x : Matrix (Fin n) (Fin n) K) i i)) hconj
        rw [hmat] at h
        change w i e = (u : K)
        simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
          using h
      apply funext
      intro b
      apply Subtype.ext
      change δu e (rep b) / δu e i₀ = 1
      rw [hδu_eq (rep b), hδu_eq i₀]
      simp
  let φ : E →* CFSG.PGLModel.projImage E :=
  { toFun := fun e => ⟨ProjGenLinGroup.mk (e : GL (Fin n) K),
      Subgroup.mem_map_of_mem (ProjGenLinGroup.mk : GL (Fin n) K →* ProjGenLinGroup (Fin n) K) e.2⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      simp }
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφker : φ.ker = (GeneralLinearGroup.scalar (Fin n)).range.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ProjGenLinGroup.mk (e : GL (Fin n) K) = 1 := by
        exact congrArg Subtype.val h
      rwa [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    · intro h
      apply Subtype.ext
      change ProjGenLinGroup.mk (e : GL (Fin n) K) = 1
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
      exact h
  have hprojcard : Nat.card (CFSG.PGLModel.projImage E) = Nat.card ψ.range := by
    have hφrange : Nat.card φ.range = Nat.card (CFSG.PGLModel.projImage E) := by
      rw [MonoidHom.range_eq_top.2 hφsurj, Subgroup.card_top]
    have hquotφ : Nat.card (E ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h1 : Nat.card (CFSG.PGLModel.projImage E) = Nat.card (E ⧸ φ.ker) :=
      hφrange.symm.trans hquotφ.symm
    calc Nat.card (CFSG.PGLModel.projImage E) = Nat.card (E ⧸ φ.ker) := h1
      _ = Nat.card (E ⧸ ψ.ker) := by rw [hφker, hψker]
      _ = Nat.card ψ.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hTcard : Nat.card T = (Finset.univ.image w).card - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe,
      show T = (Finset.univ.image w).erase (w i₀) from rfl,
      Finset.card_erase_of_mem (Finset.mem_image_of_mem w (Finset.mem_univ i₀))]
  have hrange_card : Nat.card (Set.range w) = (Finset.univ.image w).card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card (Set.range w) (Set.finite_range w),
      Set.Finite.toFinset_range w (Set.finite_range w)]
  calc Nat.card (CFSG.PGLModel.projImage E)
      = Nat.card ψ.range := hprojcard
    _ ≤ Nat.card (T → rootsOfUnity 3 K) := Subgroup.card_le_card_group _
    _ = Nat.card (rootsOfUnity 3 K) ^ Nat.card T := Nat.card_fun
    _ ≤ 3 ^ Nat.card T := Nat.pow_le_pow_left (card_rootsOfUnity K 3) _
    _ = 3 ^ ((Finset.univ.image w).card - 1) := by rw [hTcard]
    _ = 3 ^ (Nat.card (Set.range w) - 1) := by rw [hrange_card]

theorem pairwise_commute_of_isProjElem_of_projective_card_ge
    [Finite K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {G : Subgroup (GL (Fin n) K)} (hG : IsProjElem 3 G)
    {E : Subgroup (GL (Fin n) K)} [Finite E] (hEG : E ≤ G)
    (hE : IsElemAbelian 3 E)
    (hcent : ∀ e ∈ E, ∀ g ∈ G, e * g = g * e)
    (hcard : 27 ≤ Nat.card (CFSG.PGLModel.projImage E))
    (hn : n < 12) :
    ∀ g ∈ G, ∀ h ∈ G, g * h = h * g := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    intro g hg h hh
    apply Units.ext
    exact Subsingleton.elim _ _
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  let i₀ : Fin n := ⟨0, hnpos⟩
  have : NeZero 3 := ⟨by norm_num⟩
  have : Finite (E : Set (GL (Fin n) K)) := ‹Finite E›
  obtain ⟨A, hA⟩ := exists_conj_diagonal hζ (E : Set (GL (Fin n) K))
    (fun x hx y hy => by
      simpa using hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    (fun x hx => hE.2 x hx)
  let w : Fin n → E → K := fun i e => conjMatrix A (e : GL (Fin n) K) i i
  have hdiag : ∀ e : E, conjMatrix A (e : GL (Fin n) K) = diagonal (fun i => w i e) := by
    intro e
    exact eq_diagonal_of_offDiag_eq_zero (hA (e : GL (Fin n) K) e.2)
  have hbound := card_projImage_le_pow_weightClasses w i₀ hE.2 hdiag
  have h3s : 3 ≤ Nat.card (Set.range w) - 1 := by
    have h27 : 27 ≤ 3 ^ (Nat.card (Set.range w) - 1) := hcard.trans hbound
    have h3 : (3 : ℕ) ^ 3 ≤ 3 ^ (Nat.card (Set.range w) - 1) := by
      calc (3 : ℕ) ^ 3 = 27 := by norm_num
        _ ≤ 3 ^ (Nat.card (Set.range w) - 1) := h27
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3
  have hrange_card : Nat.card (Set.range w) = (Finset.univ.image w).card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card (Set.range w) (Set.finite_range w),
      Set.Finite.toFinset_range w (Set.finite_range w)]
  have hs4 : 4 ≤ (Finset.univ.image w).card := by omega
  have hblock_of_mem : ∀ x ∈ G, IsBlockDiag w ((A * x * A⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) := by
    intro x hx i j hij
    obtain ⟨e, he⟩ : ∃ e : E, w i e ≠ w j e := by
      by_contra hcon
      push Not at hcon
      exact hij (funext hcon)
    have hcommMat : conjMatrix A x * diagonal (fun k => w k e) =
        diagonal (fun k => w k e) * conjMatrix A x := by
      rw [show diagonal (fun k => w k e) = conjMatrix A (e : GL (Fin n) K) from
          (hdiag e).symm,
        ← conjMatrix_mul, ← conjMatrix_mul, hcent e e.2 x hx]
    have hcommMat' : ((A * x * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        diagonal (fun k => w k e) =
        diagonal (fun k => w k e) * ((A * x * A⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
      simpa [conjMatrix] using hcommMat
    exact isBlockDiag_of_commute_diagonal hcommMat' i j he
  intro g hg h hh
  by_contra hne
  obtain ⟨κ, hκ⟩ := hG.comm_scalar g hg h hh
  have hκ1 : κ ≠ 1 := by
    intro h1
    exact hne (by simpa [h1] using hκ)
  have hκ3 : κ ^ 3 = 1 := by
    have : Nonempty (Fin n) := ⟨i₀⟩
    rw [← commChar_eq hG hg (x := ⟨h, hh⟩) hκ]
    exact commChar_pow_eq_one hG hg ⟨h, hh⟩
  let g' : GL (Fin n) K := A * g * A⁻¹
  let h' : GL (Fin n) K := A * h * A⁻¹
  have hblockg' : IsBlockDiag w ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa [g'] using hblock_of_mem g hg
  have hblockh' : IsBlockDiag w ((h' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa [h'] using hblock_of_mem h hh
  have hκconj : conjMatrix A (g : GL (Fin n) K) * conjMatrix A (h : GL (Fin n) K) =
      Matrix.scalar (Fin n) (κ : K) *
        (conjMatrix A (h : GL (Fin n) K) * conjMatrix A (g : GL (Fin n) K)) := by
    calc conjMatrix A (g : GL (Fin n) K) * conjMatrix A (h : GL (Fin n) K)
        = conjMatrix A ((g : GL (Fin n) K) * (h : GL (Fin n) K)) :=
            (conjMatrix_mul A g h).symm
      _ = conjMatrix A (GeneralLinearGroup.scalar (Fin n) κ *
            ((h : GL (Fin n) K) * (g : GL (Fin n) K))) := by rw [hκ]
      _ = conjMatrix A (GeneralLinearGroup.scalar (Fin n) κ) *
            conjMatrix A ((h : GL (Fin n) K) * (g : GL (Fin n) K)) :=
            conjMatrix_mul A _ _
      _ = Matrix.scalar (Fin n) (κ : K) *
            (conjMatrix A (h : GL (Fin n) K) * conjMatrix A (g : GL (Fin n) K)) := by
            rw [conjMatrix_scalar, conjMatrix_mul]
  have hκconj' : (g' : Matrix (Fin n) (Fin n) K) * (h' : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) (κ : K) *
        ((h' : Matrix (Fin n) (Fin n) K) * (g' : Matrix (Fin n) (Fin n) K)) := by
    simpa [conjMatrix, g', h'] using hκconj
  have hdvd : ∀ b : E → K, 3 ∣ Fintype.card {i // w i = b} := by
    intro b
    exact three_dvd_card_fiber_of_isBlockDiag_of_scalar_commutator
      (w := w) (g := g') (h := h') (κ := κ) hκ3 hκ1 hblockg' hblockh' hκconj' b
  have hfib : ∀ b ∈ Finset.univ.image w, 3 ≤ Fintype.card {i // w i = b} := by
    intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    exact Nat.le_of_dvd (Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩) (hdvd (w i))
  have hsum : Fintype.card (Fin n) =
      ∑ b ∈ Finset.univ.image w, Fintype.card {i // w i = b} := by
    rw [← Finset.card_univ (α := Fin n), Finset.card_eq_sum_card_image w Finset.univ]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Fintype.card_subtype]
  have hsumge : 12 ≤ ∑ b ∈ Finset.univ.image w, Fintype.card {i // w i = b} := by
    calc 12 = 4 * 3 := by norm_num
      _ ≤ (Finset.univ.image w).card * 3 := Nat.mul_le_mul_right 3 hs4
      _ = ∑ b ∈ Finset.univ.image w, 3 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ b ∈ Finset.univ.image w, Fintype.card {i // w i = b} :=
          Finset.sum_le_sum hfib
  have hn12 : 12 ≤ n := by
    rw [← Fintype.card_fin n, hsum]
    exact hsumge
  omega

section CentralCubeTorality

variable {G E : Subgroup (GL (Fin n) K)}

theorem isToral_of_central_cube [Finite K] (hpK : 3 ∣ Nat.card K - 1)
    (hG : IsProjElem 3 G)
    (hcent : ∀ h ∈ G, h ^ 3 = 1 → ∀ x ∈ G, x * h = h * x)
    (hall : ∀ x ∈ G, ∃ c : Kˣ,
      x ^ 3 = GeneralLinearGroup.scalar (Fin n) (c ^ 3)) :
    IsToral G := by
  classical
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd (p := 3) (by norm_num) hpK
  let H₁ : Set (GL (Fin n) K) := {y | y ∈ G ∧ y ^ 3 = 1}
  have hH₁fin : Finite H₁ := Subtype.finite
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal hζ H₁
    (fun x hx y hy => hcent y hy.1 hy.2 x hx.1) (fun x hx => hx.2)
  refine ⟨A₀, fun x hx i j hij => ?_⟩
  obtain ⟨c, hc⟩ := hall x hx
  let y : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) c⁻¹ * x
  have hyH : y ∈ H₁ :=
    ⟨G.mul_mem (hG.scalar_mem c⁻¹) hx, pow_eq_one_of_pow_eq_scalar_pow hc⟩
  have hxy : x = GeneralLinearGroup.scalar (Fin n) c * y := by
    dsimp only [y]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hxy]
  change conjMatrix A₀ (GeneralLinearGroup.scalar (Fin n) c * y) i j = 0
  rw [conjMatrix_scalar_mul, Matrix.smul_apply,
    show conjMatrix A₀ y i j = 0 from hA₀ y hyH i j hij, smul_zero]

theorem isToral_of_E27_central [Finite K] (hpK : 3 ∣ Nat.card K - 1)
    [Finite E] (hG : IsProjElem 3 G) (hEG : E ≤ G)
    (hE : IsElemAbelian 3 E)
    (hcent : ∀ e ∈ E, ∀ g ∈ G, e * g = g * e)
    (hcard : 27 ≤ Nat.card (CFSG.PGLModel.projImage E))
    (hn : n < 12) :
    IsToral G := by
  classical
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd (p := 3) (by norm_num) hpK
  have hcommG : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g :=
    pairwise_commute_of_isProjElem_of_projective_card_ge (K := K) (n := n)
      hζ hG hEG hE hcent hcard hn
  by_cases hn0 : n = 0
  · subst n
    exact ⟨1, fun _ _ i => isEmptyElim i⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  let i₀ : Fin n := ⟨0, hnpos⟩
  haveI : Finite (E : Set (GL (Fin n) K)) := ‹Finite E›
  obtain ⟨A, hA⟩ := exists_conj_diagonal hζ (E : Set (GL (Fin n) K))
    (fun x hx y hy => by
      simpa using hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    (fun x hx => hE.2 x hx)
  let w : Fin n → E → K := fun i e => conjMatrix A (e : GL (Fin n) K) i i
  have hdiag : ∀ e : E,
      conjMatrix A (e : GL (Fin n) K) = diagonal (fun i => w i e) := by
    intro e
    exact eq_diagonal_of_offDiag_eq_zero (hA (e : GL (Fin n) K) e.2)
  have hbound := card_projImage_le_pow_weightClasses w i₀ hE.2 hdiag
  have h3s : 3 ≤ Nat.card (Set.range w) - 1 := by
    have h27 : 27 ≤ 3 ^ (Nat.card (Set.range w) - 1) := hcard.trans hbound
    have h3 : (3 : ℕ) ^ 3 ≤ 3 ^ (Nat.card (Set.range w) - 1) := by
      calc (3 : ℕ) ^ 3 = 27 := by norm_num
        _ ≤ 3 ^ (Nat.card (Set.range w) - 1) := h27
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3
  have hrange_card : Nat.card (Set.range w) = (Finset.univ.image w).card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card (Set.range w) (Set.finite_range w),
      Set.Finite.toFinset_range w (Set.finite_range w)]
  have hs4 : 4 ≤ (Finset.univ.image w).card := by omega
  have hblock_of_mem : ∀ x ∈ G, IsBlockDiag w (conjMatrix A x) := by
    intro x hx i j hij
    obtain ⟨e, he⟩ : ∃ e : E, w i e ≠ w j e := by
      by_contra hcon
      push Not at hcon
      exact hij (funext hcon)
    have hcommMat : conjMatrix A x * diagonal (fun k => w k e) =
        diagonal (fun k => w k e) * conjMatrix A x := by
      rw [show diagonal (fun k => w k e) = conjMatrix A (e : GL (Fin n) K) from
          (hdiag e).symm,
        ← conjMatrix_mul, ← conjMatrix_mul, hcent e e.2 x hx]
    exact isBlockDiag_of_commute_diagonal hcommMat i j he
  have hnoNoncube : ∀ (x : GL (Fin n) K) (c : Kˣ), x ∈ G →
      x ^ 3 = GeneralLinearGroup.scalar (Fin n) c →
      (¬ ∃ d : Kˣ, d ^ 3 = c) → False := by
    intro x c hx hc hnc
    have hblockx := hblock_of_mem x hx
    have hconjpow : conjMatrix A x ^ 3 = Matrix.scalar (Fin n) (c : K) := by
      rw [← conjMatrix_pow, hc, conjMatrix_scalar]
    have hdvd : ∀ b : E → K, 3 ∣ Fintype.card {i : Fin n // w i = b} := by
      intro b
      by_contra hnd
      have hM : ((conjMatrix A x).toSquareBlock w b) ^ 3 =
          Matrix.scalar {i : Fin n // w i = b} (c : K) := by
        rw [← toSquareBlock_pow_of_isBlockDiag hblockx b 3, hconjpow, toSquareBlock_scalar]
      obtain ⟨d, hd⟩ := exists_pow_eq_of_pow_eq_scalar (p := 3) (K := K)
        (M := (conjMatrix A x).toSquareBlock w b) (μ := c) (by norm_num) hM hnd
      exact hnc ⟨d, hd⟩
    have hfib : ∀ b ∈ Finset.univ.image w,
        3 ≤ Fintype.card {i : Fin n // w i = b} := by
      intro b hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
      exact Nat.le_of_dvd (Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩) (hdvd (w i))
    have hsum : Fintype.card (Fin n) =
        ∑ b ∈ Finset.univ.image w, Fintype.card {i : Fin n // w i = b} := by
      rw [← Finset.card_univ (α := Fin n), Finset.card_eq_sum_card_image w Finset.univ]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Fintype.card_subtype]
    have hsumge : 12 ≤
        ∑ b ∈ Finset.univ.image w, Fintype.card {i : Fin n // w i = b} := by
      calc 12 = 4 * 3 := by norm_num
        _ ≤ (Finset.univ.image w).card * 3 := Nat.mul_le_mul_right 3 hs4
        _ = ∑ _b ∈ Finset.univ.image w, 3 := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ b ∈ Finset.univ.image w,
              Fintype.card {i : Fin n // w i = b} :=
            Finset.sum_le_sum hfib
    have hn12 : 12 ≤ n := by
      rw [← Fintype.card_fin n, hsum]
      exact hsumge
    omega
  have hcube_all : ∀ x ∈ G, ∃ d : Kˣ,
      x ^ 3 = GeneralLinearGroup.scalar (Fin n) (d ^ 3) := by
    intro x hx
    obtain ⟨c, hc⟩ := hG.pow_scalar x hx
    have hc_cube : ∃ d : Kˣ, d ^ 3 = c := by
      by_contra hnc
      exact hnoNoncube x c hx hc hnc
    obtain ⟨d, hd⟩ := hc_cube
    exact ⟨d, by rw [hc, hd]⟩
  exact isToral_of_central_cube hpK hG
    (fun h hh h3 x hx => (hcommG h hh x hx).symm) hcube_all

end CentralCubeTorality

end CFSG.StandardType.TypeA.PGLTor

end
