module

public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.RankThree.PartOne.KSP6.Fix
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public section

namespace CFSG.RankThree.PartOne.KSP6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank

section Basic

variable {K : Type} [Field K]

@[expose] def mat (g : StatedSp 3 K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  ((g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)

theorem mat_mul (g h : StatedSp 3 K) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : StatedSp 3 K) = 1 := rfl

theorem mat_inj {g h : StatedSp 3 K} (e : mat g = mat h) : g = h :=
  SymplecticTorusWeyl.statedSp_ext e

theorem mat_mul_inv (g : StatedSp 3 K) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem siegel_le_unipotent : siegelRadicalSp 3 K ≤ unipotent 3 K := by
  intro g hg
  obtain ⟨B, hB, hgB⟩ := mem_siegelRadicalSp.1 hg
  refine ⟨1, B, isUnitriangular_one, hB, ?_⟩
  rw [hgB]
  simp [blockMat]

theorem fromBlocks_one_eq_blockMat (B : Matrix (Fin 3) (Fin 3) K) :
    (fromBlocks 1 B 0 1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = blockMat 1 B := by
  simp [blockMat]

theorem isUnit_det_one_fin3 : IsUnit (1 : Matrix (Fin 3) (Fin 3) K).det := by simp

theorem blockMat_mul_siegel {A C : Matrix (Fin 3) (Fin 3) K} (hA : IsUnit A.det)
    (B : Matrix (Fin 3) (Fin 3) K) :
    blockMat A C * fromBlocks 1 B 0 1 = fromBlocks 1 (A * B * Aᵀ) 0 1 * blockMat A C := by
  have key : A⁻¹ * (A * B * Aᵀ) * A⁻¹ᵀ = B := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul A hA,
      Matrix.transpose_one, Matrix.mul_one]
  rw [fromBlocks_one_eq_blockMat, fromBlocks_one_eq_blockMat, blockMat_mul isUnit_det_one_fin3,
    blockMat_mul hA, key, Matrix.mul_one, Matrix.one_mul, inv_one, Matrix.transpose_one,
    Matrix.mul_one, Matrix.one_mul, add_comm]

theorem fix_of_comm {u z : StatedSp 3 K} {A C B : Matrix (Fin 3) (Fin 3) K} (hA : IsUnit A.det)
    (hu : mat u = blockMat A C) (hz : mat z = fromBlocks 1 B 0 1) (h : u * z = z * u) :
    A * B * Aᵀ = B := by
  have hcomm := congrArg mat h
  rw [mat_mul, mat_mul, hz, hu, blockMat_mul_siegel hA, ← hu] at hcomm
  have h2 := congrArg (· * mat u⁻¹) hcomm
  simp only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] at h2
  have h3 := (fromBlocks_inj.1 h2).2.1
  rwa [Matrix.mul_assoc]

theorem isUnitriangular_ut3 (a b c : K) : IsUnitriangular (ut3 a b c) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [ut3] at hij ⊢
  · fin_cases i <;> simp [ut3]

theorem exists_siegel_elt {B : Matrix (Fin 3) (Fin 3) K} (hB : Bᵀ = B) :
    ∃ v : StatedSp 3 K, v ∈ siegelRadicalSp 3 K ∧ mat v = fromBlocks 1 B 0 1 :=
  ⟨_, ⟨Multiplicative.ofAdd ⟨B, hB⟩, rfl⟩, rfl⟩

theorem eq_siegel_of_comm {g : StatedSp 3 K} (hg : g ∈ unipotent 3 K)
    (h : ∀ v ∈ siegelRadicalSp 3 K, g * v = v * g) : g ∈ siegelRadicalSp 3 K := by
  obtain ⟨A, C, hA, hC, hgm⟩ := hg
  have hdet : IsUnit A.det := hA.isUnit_det
  have hgm' : mat g = blockMat A C := hgm
  have hcol : ∀ i : Fin 3, A * Matrix.single i i (1 : K) * Aᵀ = Matrix.single i i 1 := by
    intro i
    obtain ⟨v, hv, hvm⟩ := exists_siegel_elt (B := Matrix.single i i (1 : K)) (by simp)
    have hcomm := congrArg mat (h v hv)
    rw [mat_mul, mat_mul, hvm] at hcomm
    rw [hgm', blockMat_mul_siegel hdet] at hcomm
    rw [← hgm'] at hcomm
    have h2 := congrArg (· * mat g⁻¹) hcomm
    simp only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] at h2
    have h3 := (fromBlocks_inj.1 h2).2.1
    rwa [Matrix.mul_assoc]
  have hA1 : A = 1 := by
    ext j i
    by_cases hji : j = i
    · subst hji
      rw [hA.2 j, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hji]
      have h1 := congrFun (congrFun (hcol i) j) j
      revert h1 hji
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single_apply,
        Matrix.transpose_apply, Fin.sum_univ_three]
  refine mem_siegelRadicalSp.2 ⟨C, hC, ?_⟩
  show mat g = fromBlocks 1 C 0 1
  rw [hgm', hA1]
  simp [blockMat]

end Basic

section TopLeft

variable {K : Type} [Field K]

@[expose] def topLeft (g : StatedSp 3 K) : Matrix (Fin 3) (Fin 3) K := (mat g).toBlocks₁₁

theorem topLeft_of_blockMat {g : StatedSp 3 K} {A C : Matrix (Fin 3) (Fin 3) K}
    (hg : mat g = blockMat A C) : topLeft g = A := by
  simp [topLeft, hg, blockMat]

theorem topLeft_one : topLeft (1 : StatedSp 3 K) = 1 := by
  rw [topLeft, mat_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

theorem topLeft_mul {g h : StatedSp 3 K} (hg : g ∈ unipotent 3 K) (hh : h ∈ unipotent 3 K) :
    topLeft (g * h) = topLeft g * topLeft h := by
  obtain ⟨A, C, hA, hC, hgm⟩ := hg
  obtain ⟨D, E, hD, hE, hhm⟩ := hh
  have hgm' : mat g = blockMat A C := hgm
  have hhm' : mat h = blockMat D E := hhm
  have hgh : mat (g * h) = blockMat (A * D) (E + D⁻¹ * C * D⁻¹ᵀ) := by
    rw [mat_mul, hgm', hhm', blockMat_mul hD.isUnit_det]
  rw [topLeft_of_blockMat hgh, topLeft_of_blockMat hgm', topLeft_of_blockMat hhm']

@[expose] def piU : ↥(unipotent 3 K) →* Matrix (Fin 3) (Fin 3) K where
  toFun g := topLeft g.1
  map_one' := topLeft_one
  map_mul' g h := topLeft_mul g.2 h.2

theorem topLeft_eq_one_iff {g : StatedSp 3 K} (hg : g ∈ unipotent 3 K) :
    topLeft g = 1 ↔ g ∈ siegelRadicalSp 3 K := by
  constructor
  · intro h1
    obtain ⟨A, C, hA, hC, hgm⟩ := hg
    have hgm' : mat g = blockMat A C := hgm
    rw [topLeft_of_blockMat hgm'] at h1
    refine mem_siegelRadicalSp.2 ⟨C, hC, ?_⟩
    show mat g = fromBlocks 1 C 0 1
    rw [hgm', h1]
    simp [blockMat]
  · intro h
    obtain ⟨B, hB, hgB⟩ := mem_siegelRadicalSp.1 h
    have : mat g = blockMat 1 B := by
      rw [← fromBlocks_one_eq_blockMat]
      exact hgB
    exact topLeft_of_blockMat this

theorem exists_ut3_of_mem {g : StatedSp 3 K} (hg : g ∈ unipotent 3 K) :
    ∃ a b c : K, topLeft g = ut3 a b c := by
  obtain ⟨A, C, hA, hC, hgm⟩ := hg
  have hgm' : mat g = blockMat A C := hgm
  rw [topLeft_of_blockMat hgm']
  have h10 : A 1 0 = 0 := hA.1 (show (0 : Fin 3) < 1 by decide)
  have h20 : A 2 0 = 0 := hA.1 (show (0 : Fin 3) < 2 by decide)
  have h21 : A 2 1 = 0 := hA.1 (show (1 : Fin 3) < 2 by decide)
  refine ⟨A 0 1, A 1 2, A 0 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ut3, h10, h20, h21, hA.2 0, hA.2 1, hA.2 2]

end TopLeft

section Offender

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem offender_bound_sp (F : Subgroup (StatedSp 3 K)) (hFU : F ≤ unipotent 3 K)
    (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hFs : ∀ x ∈ F, x ^ 2 = 1)
    (hFV : ¬ F ≤ siegelRadicalSp 3 K) :
    (F ⊓ siegelRadicalSp 3 K).relIndex F *
      Nat.card ↥(siegelRadicalSp 3 K ⊓ Subgroup.centralizer (F : Set (StatedSp 3 K))) ≤
        Nat.card K ^ 5 := by
  classical
  let φ : ↥F →* (Matrix (Fin 3) (Fin 3) K)ˣ := (piU.comp (Subgroup.inclusion hFU)).toHomUnits
  have hφ : ∀ g : ↥F, ((φ g : (Matrix (Fin 3) (Fin 3) K)ˣ) : Matrix (Fin 3) (Fin 3) K) =
      topLeft g.1 := fun g => rfl
  have hker : φ.ker = (F ⊓ siegelRadicalSp 3 K).subgroupOf F := by
    ext g
    rw [MonoidHom.mem_ker, Units.ext_iff, hφ, Units.val_one, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, ← topLeft_eq_one_iff (hFU g.2)]
    simp [g.2]
  have hidx : (F ⊓ siegelRadicalSp 3 K).relIndex F = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  let H : Set (Matrix (Fin 3) (Fin 3) K) := {A | ∃ g ∈ F, topLeft g = A}
  have hHcard : Nat.card φ.range ≤ Nat.card H := by
    refine Nat.card_le_card_of_injective
      (fun u : φ.range => (⟨(u.1 : Matrix (Fin 3) (Fin 3) K), ?_⟩ : H)) ?_
    · obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 u.2
      exact ⟨g.1, g.2, by rw [← hg, hφ]⟩
    · intro u w h
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val h
  have hHU : ∀ A ∈ H, ∃ a b c, A = ut3 a b c := by
    rintro A ⟨g, hg, rfl⟩
    obtain ⟨a, b, c, h⟩ := exists_ut3_of_mem (hFU hg)
    exact ⟨a, b, c, h⟩
  have hHsq : ∀ A ∈ H, A * A = 1 := by
    rintro A ⟨g, hg, rfl⟩
    rw [← topLeft_mul (hFU hg) (hFU hg), ← sq, hFs g hg, topLeft_one]
  have hHcomm : ∀ A ∈ H, ∀ B ∈ H, A * B = B * A := by
    rintro A ⟨g, hg, rfl⟩ B ⟨h, hh, rfl⟩
    rw [← topLeft_mul (hFU hg) (hFU hh), ← topLeft_mul (hFU hh) (hFU hg), hFc g hg h hh]
  have hHne : ∃ A ∈ H, A ≠ 1 := by
    obtain ⟨g, hg, hgV⟩ := Set.not_subset.1 hFV
    exact ⟨topLeft g, ⟨g, hg, rfl⟩, fun h1 => hgV ((topLeft_eq_one_iff (hFU hg)).1 h1)⟩
  have hFixcard : Nat.card ↥(siegelRadicalSp 3 K ⊓
      Subgroup.centralizer (F : Set (StatedSp 3 K))) ≤ Nat.card (FixSet H) := by
    have key : ∀ v : ↥(siegelRadicalSp 3 K ⊓ Subgroup.centralizer (F : Set (StatedSp 3 K))),
        ∃ B : Matrix (Fin 3) (Fin 3) K, Bᵀ = B ∧ mat v.1 = fromBlocks 1 B 0 1 ∧
          ∀ A ∈ H, A * B * Aᵀ = B := by
      intro v
      obtain ⟨B, hB, hvB⟩ := mem_siegelRadicalSp.1 v.2.1
      have hvB' : mat v.1 = fromBlocks 1 B 0 1 := hvB
      refine ⟨B, hB, hvB', ?_⟩
      rintro A ⟨g, hg, rfl⟩
      obtain ⟨A', C, hA', hC, hgm⟩ := hFU hg
      have hgm' : mat g = blockMat A' C := hgm
      rw [topLeft_of_blockMat hgm']
      have hcomm := congrArg mat (Subgroup.mem_centralizer_iff.1 v.2.2 g hg)
      rw [mat_mul, mat_mul, hvB', hgm', blockMat_mul_siegel hA'.isUnit_det, ← hgm'] at hcomm
      have h2 := congrArg (· * mat g⁻¹) hcomm
      simp only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] at h2
      have h3 := (fromBlocks_inj.1 h2).2.1
      rwa [Matrix.mul_assoc]
    choose Bof hBsym hBmat hBfix using key
    refine Nat.card_le_card_of_injective
      (fun v => (⟨Bof v, hBsym v, hBfix v⟩ : FixSet H)) ?_
    intro v w h
    apply Subtype.ext
    apply mat_inj
    have h' : Bof v = Bof w := congrArg Subtype.val h
    rw [hBmat v, hBmat w, h']
  rw [hidx]
  calc Nat.card φ.range * Nat.card ↥(siegelRadicalSp 3 K ⊓
        Subgroup.centralizer (F : Set (StatedSp 3 K))) ≤ Nat.card H * Nat.card (FixSet H) :=
      Nat.mul_le_mul hHcard hFixcard
    _ ≤ Nat.card K ^ 5 := card_mul_card_fix_le H hHU hHsq hHcomm hHne

end Offender

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_card_eq_two_pow : ∃ f : ℕ, Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem card_siegel : Nat.card (siegelRadicalSp 3 K) = Nat.card K ^ 6 := by
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow (K := K)
  rw [(siegel_radical_sp Nat.prime_two hf 3).2, hf, ← pow_mul]

theorem siegel_elemAbelian :
    (∀ x ∈ siegelRadicalSp 3 K, ∀ y ∈ siegelRadicalSp 3 K, x * y = y * x) ∧
      ∀ x ∈ siegelRadicalSp 3 K, x ^ 2 = 1 := by
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow (K := K)
  obtain ⟨hc, hs⟩ := (siegel_radical_sp Nat.prime_two hf 3).1
  exact ⟨fun x hx y hy => congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩), hs⟩

theorem siegel_char {β : MulAut (StatedSp 3 K)}
    (hU : ∀ u ∈ unipotent 3 K, β u ∈ unipotent 3 K) :
    ∀ v ∈ siegelRadicalSp 3 K, β v ∈ siegelRadicalSp 3 K := by
  set V := siegelRadicalSp 3 K with hVdef
  set F : Subgroup (StatedSp 3 K) := V.map β.toMonoidHom with hF
  have hFU : F ≤ unipotent 3 K := by
    rintro _ ⟨v, hv, rfl⟩
    exact hU v (siegel_le_unipotent hv)
  obtain ⟨hVc, hVs⟩ := siegel_elemAbelian (K := K)
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    show β v * β w = β w * β v
    rw [← map_mul, ← map_mul, hVc v hv w hw]
  have hFs : ∀ x ∈ F, x ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    show β v ^ 2 = 1
    rw [← map_pow, hVs v hv, map_one]
  have hFcard : Nat.card F = Nat.card K ^ 6 := by
    rw [hF, Subgroup.card_map_of_injective β.injective, card_siegel]
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hβv⟩ := hcon
  have hFV : ¬ F ≤ V := fun h => hβv (h ⟨v, hv, rfl⟩)
  have h1 := offender_bound_sp F hFU hFc hFs hFV
  have h2 : Nat.card F = (F ⊓ V).relIndex F * Nat.card ↥(F ⊓ V) := by
    have := Subgroup.relIndex_mul_card (F ⊓ V) F
    rw [inf_eq_left.mpr (inf_le_left : F ⊓ V ≤ F)] at this
    exact this.symm
  have h3 : Nat.card ↥(F ⊓ V) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set (StatedSp 3 K))) :=
    Subgroup.card_le_of_le fun x hx =>
      ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun y hy => hFc y hy x hx.1⟩
  have h4 : Nat.card F ≤ Nat.card K ^ 5 := by
    calc Nat.card F = (F ⊓ V).relIndex F * Nat.card ↥(F ⊓ V) := h2
      _ ≤ (F ⊓ V).relIndex F * Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set (StatedSp 3 K))) :=
          Nat.mul_le_mul_left _ h3
      _ ≤ Nat.card K ^ 5 := h1
  rw [hFcard] at h4
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have : Nat.card K ^ 5 < Nat.card K ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

end Card

end CFSG.RankThree.PartOne.KSP6
