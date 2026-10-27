module

public import CFSG.RankThree.SubgroupLists.MitchellQOne
public import CFSG.RankThree.SubgroupLists.SymplecticSkewElations
public import Certificates.Certificate113

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K K' : Type} [Field K] [Field K']

@[expose] noncomputable def frameHom (φ : K →+* K') (k : GL V₄ K') : GL V₄ K →* GL V₄ K' :=
  (MulAut.conj k⁻¹).toMonoidHom.comp (mapGL φ)

theorem frameHom_apply (φ : K →+* K') (k : GL V₄ K') (g : GL V₄ K) :
    frameHom φ k g = k⁻¹ * mapGL φ g * k := by
  simp [frameHom, MulAut.conj_apply]

theorem frameHom_injective (φ : K →+* K') (k : GL V₄ K') : Function.Injective (frameHom φ k) := by
  intro x y h
  rw [frameHom_apply, frameHom_apply] at h
  apply mapGL_injective φ
  simpa using h

@[expose] noncomputable def frameMat (φ : K →+* K') (k : GL V₄ K') (Z : Matrix V₄ V₄ K) :
    Matrix V₄ V₄ K' :=
  ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') * Z.map φ * (k : Matrix V₄ V₄ K')

theorem coe_frameHom (φ : K →+* K') (k : GL V₄ K') (g : GL V₄ K) :
    ((frameHom φ k g : GL V₄ K') : Matrix V₄ V₄ K') = frameMat φ k (g : Matrix V₄ V₄ K) := by
  rw [frameHom_apply, Units.val_mul, Units.val_mul, coe_mapGL]
  rfl

theorem frameMat_mul (φ : K →+* K') (k : GL V₄ K') (Z Y : Matrix V₄ V₄ K) :
    frameMat φ k (Z * Y) = frameMat φ k Z * frameMat φ k Y := by
  have hkk : (k : Matrix V₄ V₄ K') * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [frameMat, Matrix.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (k : Matrix V₄ V₄ K') ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K'), hkk,
    Matrix.one_mul]

theorem frameMat_smul (φ : K →+* K') (k : GL V₄ K') (c : K) (Z : Matrix V₄ V₄ K) :
    frameMat φ k (c • Z) = φ c • frameMat φ k Z := by
  have e : (c • Z).map φ = φ c • Z.map φ := by
    ext i j
    simp
  rw [frameMat, frameMat, e, Matrix.mul_smul, Matrix.smul_mul]

theorem frameMat_one (φ : K →+* K') (k : GL V₄ K') : frameMat φ k 1 = 1 := by
  rw [frameMat, Matrix.map_one φ φ.map_zero φ.map_one, Matrix.mul_one, ← Units.val_mul,
    inv_mul_cancel, Units.val_one]

theorem frameMat_injective (φ : K →+* K') (k : GL V₄ K') :
    Function.Injective (frameMat φ k) := by
  intro Z Y h
  have hkk : (k : Matrix V₄ V₄ K') * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm : Z.map φ = Y.map φ := by
    have := congrArg (fun M => (k : Matrix V₄ V₄ K') * M * ((k⁻¹ : GL V₄ K') : Matrix V₄ V₄ K')) h
    simpa [frameMat, ← Matrix.mul_assoc, hkk, Matrix.mul_assoc] using this
  ext i j
  exact φ.injective (by simpa using congrFun (congrFun hm i) j)

variable (h2 : (2 : K') ≠ 0)

theorem frameMat_mem_cliffSpace (φ : K →+* K') {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    {Z : Matrix V₄ V₄ K} (hZ : Z ∈ (cliffSpace : Submodule K _)) :
    frameMat φ k Z ∈ (cliffSpace : Submodule K' _) := by
  have := conj_mem_cliffSpace (g := k⁻¹) (inv_mem hk) (map_mem_cliffSpace φ hZ)
  rwa [inv_inv] at this

include h2 in
theorem cliffB_frameMat (φ : K →+* K') (k : GL V₄ K') {Z Y : Matrix V₄ V₄ K}
    (hZ : Z ∈ (cliffSpace : Submodule K _)) (hY : Y ∈ (cliffSpace : Submodule K _)) :
    cliffB (frameMat φ k Z) (frameMat φ k Y) = φ (cliffB Z Y) := by
  have := cliffB_conj h2 k⁻¹ (map_mem_cliffSpace φ hZ) (map_mem_cliffSpace φ hY)
  rw [inv_inv] at this
  rw [frameMat, frameMat, this, cliffB_map]

theorem frameHom_mem_statedSp (φ : K →+* K') {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    {g : GL V₄ K} (hg : g ∈ StatedSp 2 K) : frameHom φ k g ∈ StatedSp 2 K' := by
  rw [frameHom_apply]
  exact mul_mem (mul_mem (inv_mem hk) (map_mem_statedSp φ hg)) hk

theorem isSqZero_frameHom_iff (φ : K →+* K') (k : GL V₄ K') {g : GL V₄ K} :
    IsSqZero (frameHom φ k g) ↔ IsSqZero g := by
  rw [frameHom_apply]
  constructor
  · intro h
    have := isSqZero_conj h k
    rw [show k * (k⁻¹ * mapGL φ g * k) * k⁻¹ = mapGL φ g by group] at this
    exact (isSqZero_map_iff φ).mp this
  · intro h
    have := isSqZero_conj ((isSqZero_map_iff φ).mpr h) k⁻¹
    simpa using this

theorem frameHom_neg_one (φ : K →+* K') (k : GL V₄ K') :
    frameHom φ k (-1) = -1 := by
  rw [frameHom_apply, mapGL_neg_one]
  simp

theorem isNCInv_frameHom (φ : K →+* K') {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    {d : GL V₄ K} (hd : IsNCInv d) : IsNCInv (frameHom φ k d) := by
  obtain ⟨hS, hdd, h1, hm⟩ := hd
  refine ⟨frameHom_mem_statedSp φ hk hS, by rw [← map_mul, hdd, map_one], fun h => h1 ?_,
    fun h => hm ?_⟩
  · apply frameHom_injective φ k
    rw [h, map_one]
  · apply frameHom_injective φ k
    rw [h, frameHom_neg_one]

@[expose] noncomputable def frameGroup (φ : K →+* K') (k : GL V₄ K') (G : Subgroup (GL V₄ K)) :
    Subgroup (GL V₄ K') :=
  G.map (frameHom φ k)

theorem frameGroup_le (φ : K →+* K') {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K')
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) : frameGroup φ k G ≤ StatedSp 2 K' := by
  rintro _ ⟨g, hg, rfl⟩
  exact frameHom_mem_statedSp φ hk (hGS hg)

theorem frameGroup_U0 (φ : K →+* K') (k : GL V₄ K') {G : Subgroup (GL V₄ K)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) :
    ∀ x ∈ frameGroup φ k G, IsSqZero x → x = 1 := by
  rintro _ ⟨g, hg, rfl⟩ hsq
  rw [hU0 g hg ((isSqZero_frameHom_iff φ k).mp hsq), map_one]

theorem frameGroup_neg (φ : K →+* K') (k : GL V₄ K') {G : Subgroup (GL V₄ K)}
    (hneg : (-1 : GL V₄ K) ∈ G) : (-1 : GL V₄ K') ∈ frameGroup φ k G :=
  ⟨-1, hneg, frameHom_neg_one φ k⟩

theorem mem_frameGroup (φ : K →+* K') (k : GL V₄ K') {G : Subgroup (GL V₄ K)} {g : GL V₄ K}
    (hg : g ∈ G) : frameHom φ k g ∈ frameGroup φ k G :=
  Subgroup.mem_map_of_mem _ hg

theorem exists_frame [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {u : Matrix V₄ V₄ K} (hu : u ∈ (cliffSpace : Submodule K _)) (hQ : cliffB u u ≠ 0) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' p) (φ : K →+* K')
      (k : GL V₄ K') (s : K'), k ∈ StatedSp 2 K' ∧ s ≠ 0 ∧ frameMat φ k u = s • tStdMat := by
  obtain ⟨K', iF, iFin, iCh, φ, u', hu', s, hs, hu's⟩ := exists_isNCInv_smul_map hp2 hu hQ
  have h2' : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  obtain ⟨h, hhS, hh⟩ := exists_conj_eq_tStd h2' hu'
  refine ⟨K', iF, iFin, iCh, φ, h, s⁻¹, hhS, inv_ne_zero hs, ?_⟩
  have hu'm : u.map φ = s⁻¹ • (u' : Matrix V₄ V₄ K') := by
    rw [hu's, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have htm : (u' : Matrix V₄ V₄ K') =
      (h : Matrix V₄ V₄ K') * tStdMat * ((h⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') := by
    rw [← hh, Units.val_mul, Units.val_mul, coe_tStd]
  have hhh : ((h⁻¹ : GL V₄ K') : Matrix V₄ V₄ K') * (h : Matrix V₄ V₄ K') = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [frameMat, hu'm, htm, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [← Matrix.mul_assoc]
  rw [hhh, Matrix.one_mul, Matrix.mul_assoc, hhh, Matrix.mul_one]

end CFSG.RankThree.SubgroupLists
