module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesMatrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}

@[expose] def blockScalarHom {κ : Type*} (β : ι → κ) : (κ → Kˣ) →* GL ι K :=
  TauCeti.diagGL.comp {
    toFun := fun f i => f (β i)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

@[simp] theorem blockScalarHom_coe {κ : Type*} (β : ι → κ) (f : κ → Kˣ) :
    (blockScalarHom β f : Matrix ι ι K) = diagonal (fun i => (f (β i) : K)) := by
  change (TauCeti.diagGL (fun i => f (β i)) : Matrix ι ι K) = _
  exact TauCeti.diagGL_coe _

@[expose] def blockPowCoords {κ : Type*} (p : ℕ) (j₀ : κ) : Subgroup (κ → Kˣ) where
  carrier := {f | ∀ j, f j ^ p = f j₀ ^ p}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg j
    simp only [Pi.mul_apply, mul_pow, hf j, hg j]
  inv_mem' := by
    intro f hf j
    simp only [Pi.inv_apply, inv_pow, hf j]

@[expose] def CentralBlockModel.scalarBlocks {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) : (Fin D.numBlocks → Kˣ) →* GL ι K :=
  (MulAut.conj D.basis⁻¹).toMonoidHom.comp (blockScalarHom D.block)

theorem CentralBlockModel.scalarBlocks_apply {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) (f : Fin D.numBlocks → Kˣ) :
    D.scalarBlocks f = D.basis⁻¹ * blockScalarHom D.block f * D.basis := by
  simp only [CentralBlockModel.scalarBlocks, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem CentralBlockModel.scalarBlocks_injective {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) : Function.Injective D.scalarBlocks := by
  intro f g hfg
  have hdiag : blockScalarHom D.block f = blockScalarHom D.block g :=
    (MulAut.conj D.basis⁻¹).injective hfg
  have hfun : (fun i => f (D.block i)) = (fun i => g (D.block i)) :=
    TauCeti.diagGL_injective hdiag
  funext b
  obtain ⟨i, rfl⟩ := D.block_surjective b
  exact congrFun hfun i

theorem CentralBlockModel.scalarBlocks_const {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) (u : Kˣ) :
    D.scalarBlocks (fun _ => u) = GeneralLinearGroup.scalar ι u := by
  rw [D.scalarBlocks_apply]
  have hdiag : blockScalarHom D.block (fun _ => u) = GeneralLinearGroup.scalar ι u :=
    TauCeti.diagGL_const u
  rw [hdiag, ← scalar_mul_comm u D.basis⁻¹, mul_assoc, inv_mul_cancel, mul_one]

@[expose] def CentralBlockModel.blockKernelGroup {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) : Subgroup (GL ι K) :=
  (blockPowCoords p (D.block D.point)).map D.scalarBlocks

theorem CentralBlockModel.kernel_le_blockKernelGroup {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) : D.kernel ≤ D.blockKernelGroup := by
  classical
  intro x hx
  obtain ⟨δ, hδ, hconst, hpow⟩ := D.kernel_diagonal x hx
  have hδne : ∀ i, δ i ≠ 0 := diag_ne_zero_of_eq_diagonal
    (D := D.basis * x * D.basis⁻¹) (by simpa only [conjMatrix, Units.val_mul] using hδ)
  let idx : Fin D.numBlocks → ι := fun j => Classical.choose (D.block_surjective j)
  have hidx : ∀ j, D.block (idx j) = j := fun j => Classical.choose_spec (D.block_surjective j)
  let f : Fin D.numBlocks → Kˣ := fun j => Units.mk0 (δ (idx j)) (hδne _)
  have hfδ : ∀ i, (f (D.block i) : K) = δ i := by
    intro i
    change δ (idx (D.block i)) = δ i
    exact hconst _ _ (hidx _)
  have hf : f ∈ blockPowCoords p (D.block D.point) := by
    intro j
    apply Units.ext
    simpa [f] using (hpow (idx j)).trans (hpow (idx (D.block D.point))).symm
  have heq : blockScalarHom D.block f = D.basis * x * D.basis⁻¹ := by
    apply Units.ext
    rw [blockScalarHom_coe]
    change diagonal (fun i => (f (D.block i) : K)) = conjMatrix D.basis x
    rw [hδ]
    exact congrArg diagonal (funext hfδ)
  change x ∈ (blockPowCoords p (D.block D.point)).map D.scalarBlocks
  refine Subgroup.mem_map.mpr ⟨f, hf, ?_⟩
  rw [D.scalarBlocks_apply, heq]
  group

theorem CentralBlockModel.commute_scalarBlocks {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) {x : GL ι K} (hx : x ∈ G)
    (f : Fin D.numBlocks → Kˣ) : Commute x (D.scalarBlocks f) := by
  have hraw : Commute (MulAut.conj D.basis x) (blockScalarHom D.block f) := by
    apply Units.ext
    simp only [Units.val_mul, blockScalarHom_coe, MulAut.conj_apply]
    change conjMatrix D.basis x * diagonal (fun i => (f (D.block i) : K)) =
      diagonal (fun i => (f (D.block i) : K)) * conjMatrix D.basis x
    exact CFSG.RankThree.PartTwo.Sec21.Tables.commute_diagonal_of_isBlockDiag
      (fun i j hij => by rw [hij]) (D.isBlockDiag x hx)
  have hx : MulAut.conj D.basis⁻¹ (MulAut.conj D.basis x) = x := by
    simp only [MulAut.conj_apply, inv_inv]
    group
  have hm := hraw.map (MulAut.conj D.basis⁻¹).toMonoidHom
  change Commute (MulAut.conj D.basis⁻¹ (MulAut.conj D.basis x)) (D.scalarBlocks f) at hm
  rwa [hx] at hm

theorem CentralBlockModel.exists_normalized_kernel_coords
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    (hG : IsProjElem p G) {H : Type*} [Group H] (c : GL ι K →* H)
    (hc : ∀ u : Kˣ, c (GeneralLinearGroup.scalar ι u) = 1)
    (b : Fin D.numBlocks) {y : GL ι K} (hy : y ∈ D.kernel) :
    ∃ f : Fin D.numBlocks → Kˣ, f b = 1 ∧ (∀ j, f j ^ p = 1) ∧
      D.scalarBlocks f ∈ D.kernel ∧ c (D.scalarBlocks f) = c y := by
  classical
  obtain ⟨f, hf, he⟩ := Subgroup.mem_map.mp (D.kernel_le_blockKernelGroup hy)
  let g : Fin D.numBlocks → Kˣ := fun j => (f b)⁻¹ * f j
  have hgbase : g b = 1 := by simp [g]
  have hgp : ∀ j, g j ^ p = 1 := by
    intro j
    change ((f b)⁻¹ * f j) ^ p = 1
    rw [mul_pow, inv_pow, (hf j).trans (hf b).symm, inv_mul_cancel]
  have hg : g = (fun _ => (f b)⁻¹) * f := rfl
  have hge : D.scalarBlocks g = GeneralLinearGroup.scalar ι (f b)⁻¹ * y := by
    rw [hg, map_mul, D.scalarBlocks_const, he]
  have hscalar : GeneralLinearGroup.scalar ι (f b)⁻¹ ∈ D.kernel := by
    apply (D.kernel_mem_iff _ (hG.scalar_mem _)).mpr
    exact ⟨(f b)⁻¹, by rw [map_pow]⟩
  refine ⟨g, hgbase, hgp, ?_, ?_⟩
  · rw [hge]
    exact D.kernel.mul_mem hscalar hy
  · rw [hge, map_mul, hc, one_mul]

theorem CentralBlockModel.exists_scalarBlocks_pow_of_pow_eq_one [NeZero p]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {z : GL ι K} (hz : z ∈ G)
    (hzp : z ^ p = 1) :
    ∃ r : Fin D.numBlocks → ℕ, (∀ j, r j < p) ∧
      D.scalarBlocks (fun j => ζ ^ r j) = z := by
  classical
  have hzker : z ∈ D.kernel := (D.kernel_mem_iff z hz).mpr ⟨1, by simpa using hzp⟩
  have hzblock := D.kernel_le_blockKernelGroup hzker
  change z ∈ (blockPowCoords p (D.block D.point)).map D.scalarBlocks at hzblock
  obtain ⟨f, -, hfz⟩ := Subgroup.mem_map.mp hzblock
  have hfp : f ^ p = 1 := by
    apply D.scalarBlocks_injective
    rw [map_pow, hfz, hzp, map_one]
  have hfjp (j : Fin D.numBlocks) : f j ^ p = 1 := by
    simpa only [Pi.pow_apply, Pi.one_apply] using congrFun hfp j
  choose r hr hroot using fun j =>
    hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (f j)).mpr (hfjp j))
  refine ⟨r, hr, ?_⟩
  calc D.scalarBlocks (fun j => ζ ^ r j) = D.scalarBlocks f :=
      congrArg D.scalarBlocks (funext hroot)
    _ = z := hfz

theorem CentralBlockModel.exists_blockRoot_word_of_pow_eq_one [NeZero p]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {z : GL ι K} (hz : z ∈ G)
    (hzp : z ^ p = 1) :
    ∃ w : List (Fin D.numBlocks),
      (w.map fun b => D.scalarBlocks (fun j => if b = j then ζ else 1)).prod = z := by
  classical
  obtain ⟨r, -, hr⟩ := D.exists_scalarBlocks_pow_of_pow_eq_one hζ hz hzp
  let v : Fin D.numBlocks → Fin D.numBlocks → Kˣ :=
    fun b j => if b = j then ζ else 1
  let w := (List.ofFn fun j : Fin D.numBlocks => List.replicate (r j) j).flatten
  have hw : (w.map v).prod = fun j => ζ ^ r j := by
    simp only [w, List.map_flatten, List.map_ofFn, Function.comp_def,
      List.map_replicate, List.prod_flatten, List.prod_replicate, List.prod_ofFn]
    funext j
    simp [v, Finset.prod_apply, Pi.pow_apply, Finset.prod_ite_eq']
  refine ⟨w, ?_⟩
  calc (w.map fun b => D.scalarBlocks (v b)).prod =
        D.scalarBlocks (w.map v).prod := by
          rw [map_list_prod, List.map_map]
          rfl
    _ = D.scalarBlocks (fun j => ζ ^ r j) := congrArg D.scalarBlocks hw
    _ = z := hr

theorem CentralBlockModel.card_blockKernelGroup_le [Finite K] [NeZero p]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G) :
    Nat.card D.blockKernelGroup ≤ p ^ (D.numBlocks - 1) * (Nat.card K - 1) := by
  classical
  have hdiag : ∀ x ∈ D.blockKernelGroup, ∃ δ : ι → K,
      conjMatrix D.basis x = diagonal δ ∧
        (∀ i j, D.block i = D.block j → δ i = δ j) ∧
          ∀ i, δ i ^ p = δ D.point ^ p := by
    rintro x ⟨f, hf, rfl⟩
    refine ⟨fun i => (f (D.block i) : K), ?_, ?_, ?_⟩
    · have hc : D.basis * D.scalarBlocks f * D.basis⁻¹ = blockScalarHom D.block f := by
        rw [D.scalarBlocks_apply]
        group
      calc conjMatrix D.basis (D.scalarBlocks f)
          = ((D.basis * D.scalarBlocks f * D.basis⁻¹ : GL ι K) : Matrix ι ι K) := by
              simp only [conjMatrix, Units.val_mul]
        _ = (blockScalarHom D.block f : Matrix ι ι K) :=
          congrArg (fun a : GL ι K => (a : Matrix ι ι K)) hc
        _ = _ := blockScalarHom_coe _ _
    · intro i j hij
      change (f (D.block i) : K) = (f (D.block j) : K)
      rw [hij]
    · intro i
      simpa using congrArg (fun a : Kˣ => (a : K)) (hf (D.block i))
  have hcount := card_le_of_diag (p := p) D.basis D.block D.point hdiag
  have himage : Finset.univ.image D.block = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro b
    obtain ⟨i, rfl⟩ := D.block_surjective b
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  rw [himage, Finset.card_univ, Fintype.card_fin] at hcount
  simpa only [mul_comm] using hcount

theorem CentralBlockModel.kernel_eq_blockKernelGroup [Finite K] [NeZero p]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    (hcard : p ^ (D.numBlocks - 1) * (Nat.card K - 1) ≤ Nat.card D.kernel) :
    D.kernel = D.blockKernelGroup :=
  Subgroup.eq_of_le_of_card_ge D.kernel_le_blockKernelGroup
    (D.card_blockKernelGroup_le.trans hcard)

theorem CentralBlockModel.scalarBlocks_mem_kernel [Finite K] [NeZero p]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    (hcard : p ^ (D.numBlocks - 1) * (Nat.card K - 1) ≤ Nat.card D.kernel)
    {f : Fin D.numBlocks → Kˣ} (hf : ∀ j, f j ^ p = f (D.block D.point) ^ p) :
    D.scalarBlocks f ∈ D.kernel := by
  rw [D.kernel_eq_blockKernelGroup hcard]
  exact Subgroup.mem_map.mpr ⟨f, hf, rfl⟩

end CFSG.StandardType.TypeA.PGLTor
