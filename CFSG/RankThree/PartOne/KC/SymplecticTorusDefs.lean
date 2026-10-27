module

public import CFSG.RankThree.PartOne.KC.SymplecticSemi
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spXg (x : StatedSp r K) : gsp r K := ⟨x, statedSp_le_gsp x.2⟩

variable (r K) in
@[expose] noncomputable def gspLin :
    gsp r K →* LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (gsp r K).subtype

theorem gspLin_injective : Function.Injective (gspLin r K) := fun _ _ h =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective h)

theorem gspLin_apply (A : gsp r K) (v : Fin r ⊕ Fin r → K) :
    ((gspLin r K A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) v =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v := rfl

theorem gspLin_spXg (x : StatedSp r K) : gspLin r K (spXg x) = spLin r K x := rfl

variable (r K) in
@[expose] noncomputable def gspLE :
    gsp r K →* ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin r ⊕ Fin r → K)).toMonoidHom.comp
    (gspLin r K)

theorem gspLE_apply (A : gsp r K) (v : Fin r ⊕ Fin r → K) :
    gspLE r K A v = ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v :=
  rfl

theorem gspLE_injective : Function.Injective (gspLE r K) := fun _ _ h =>
  gspLin_injective (Units.ext (LinearMap.ext fun v => LinearEquiv.congr_fun h v))

@[expose] noncomputable def spEquiv (x : StatedSp r K) : (Fin r ⊕ Fin r → K) ≃ₗ[K]
    (Fin r ⊕ Fin r → K) :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (spLin r K x)

theorem spEquiv_toLinearMap (x : StatedSp r K) : (spEquiv x).toLinearMap = spEnd x := rfl

theorem spEquiv_apply (x : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spEquiv x v = ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v :=
  rfl

section Center

variable {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def centerSim (x : LinearMap.GeneralLinearGroup K V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | ∃ hz : (g : Module.End K V) ∈ commutant (x : Module.End K V),
    (⟨(g : Module.End K V), hz⟩ : commutant (x : Module.End K V)) ∈
      Subalgebra.center K (commutant (x : Module.End K V))}
  one_mem' := by
    have hz : ((1 : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∈
        commutant (x : Module.End K V) := one_mem _
    exact ⟨hz, Subalgebra.one_mem _⟩
  mul_mem' := by
    rintro g g' ⟨hz, hc⟩ ⟨hz', hc'⟩
    have hzz : ((g * g' : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∈
        commutant (x : Module.End K V) := by
      rw [Units.val_mul]
      exact mul_mem hz hz'
    exact ⟨hzz, Subalgebra.mul_mem _ hc hc'⟩
  inv_mem' := by
    rintro g ⟨hz, hc⟩
    have hgc : Commute ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (x : Module.End K V) := (mem_commutant _).mp hz
    have hzz : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∈
        commutant (x : Module.End K V) := (mem_commutant _).mpr (Commute.units_inv_left hgc)
    refine ⟨hzz, Subalgebra.mem_center_iff.mpr fun r => ?_⟩
    have h1 := Subalgebra.mem_center_iff.mp hc r
    have h2 : Commute ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (r : Module.End K V) := by
      have := congrArg Subtype.val h1
      exact this.symm
    exact Subtype.ext (Commute.units_inv_left h2).symm.eq

theorem mem_centerSim {x g : LinearMap.GeneralLinearGroup K V} :
    g ∈ centerSim x ↔ ∃ hz : (g : Module.End K V) ∈ commutant (x : Module.End K V),
      (⟨(g : Module.End K V), hz⟩ : commutant (x : Module.End K V)) ∈
        Subalgebra.center K (commutant (x : Module.End K V)) := Iff.rfl

theorem commute_of_mem_centerSim {x g m : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ centerSim x) (hm : Commute (m : Module.End K V) (x : Module.End K V)) :
    Commute g m := by
  obtain ⟨hz, hc⟩ := hg
  have hmc : (m : Module.End K V) ∈ commutant (x : Module.End K V) := (mem_commutant _).mpr hm
  have h1 := Subalgebra.mem_center_iff.mp hc ⟨(m : Module.End K V), hmc⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (congrArg Subtype.val h1).symm

theorem smul_mem_centerSim {x g : LinearMap.GeneralLinearGroup K V} (c : K)
    (hc : ∀ v, (g : Module.End K V) v = c • v) : g ∈ centerSim x := by
  have hg' : (g : Module.End K V) = algebraMap K (Module.End K V) c :=
    LinearMap.ext fun v => by simp [hc v, Module.algebraMap_end_apply]
  refine ⟨?_, ?_⟩
  · rw [hg']
    exact Subalgebra.algebraMap_mem _ c
  · refine Subalgebra.mem_center_iff.mpr fun r => ?_
    apply Subtype.ext
    change (r : Module.End K V) * (g : Module.End K V) = (g : Module.End K V) * (r : Module.End K V)
    rw [hg']
    exact (Algebra.commutes c _).symm

end Center

@[expose] noncomputable def spCenterUnits (x : StatedSp r K) : Subgroup (gsp r K) :=
  (centerSim (spLin r K x)).comap (gspLin r K)

theorem mem_spCenterUnits {x : StatedSp r K} {A : gsp r K} :
    A ∈ spCenterUnits x ↔ ∃ hz : ((gspLin r K A : LinearMap.GeneralLinearGroup K
        (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) ∈ commutant (spEnd x),
      (⟨((gspLin r K A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)), hz⟩ : commutant (spEnd x)) ∈
        Subalgebra.center K (commutant (spEnd x)) := Iff.rfl

section Kernel

variable [Finite K]

theorem conjAut_ker_central (hr : 1 ≤ r) {u : gsp r K} (hu : u ∈ (conjAut r K).ker)
    (g : gsp r K) : Commute u g := by
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hr u).mp hu
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (commute_scalar_gl c (g : GL (Fin r ⊕ Fin r) K)).eq

omit [Finite K] in
theorem map_ker_multiplier [NeZero r] :
    ((multiplier r K).ker).map (conjAut r K) =
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range := by
  ext α
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hA' : (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
      rw [ker_multiplier] at hA
      exact hA
    refine ⟨SymplecticFlag.proj r K ⟨A, hA'⟩, ?_⟩
    rw [← conjAut_statedSp]
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective y
    refine ⟨spXg g, ?_, conjAut_statedSp g⟩
    show spXg g ∈ (multiplier r K).ker
    rw [MonoidHom.mem_ker, multiplier_eq (spXg g) (μ := 1)]
    have := SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
    rw [Units.val_one, one_smul]
    exact this

theorem conjAut_range_inf_centralizer_eq_map (hr : 1 ≤ r) {p : ℕ} (hp : Odd p)
    {x : StatedSp r K} (hxp : x ^ p = 1) :
    (conjAut r K).range ⊓ Subgroup.centralizer ({conjAut r K (spXg x)} :
        Set (MulAut (StatedProj (StatedSp r K)))) =
      (Subgroup.centralizer ({spXg x} : Set (gsp r K))).map (conjAut r K) := by
  have hXp : (spXg x) ^ p = 1 := Subtype.ext (by
    have := congrArg (fun y : StatedSp r K => (y : GL (Fin r ⊕ Fin r) K)) hxp
    simpa [spXg] using this)
  ext y
  constructor
  · rintro ⟨⟨A, rfl⟩, hy⟩
    refine ⟨A, ?_, rfl⟩
    have hcomm : conjAut r K A * conjAut r K (spXg x) = conjAut r K (spXg x) * conjAut r K A :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    have hg : spPsi r K ⟨A, 1⟩ * conjAut r K (spXg x) * (spPsi r K ⟨A, 1⟩)⁻¹ =
        conjAut r K (spXg x) := by
      rw [spPsi_mk, map_one, mul_one, hcomm, mul_inv_cancel_right]
    have h1 := sp_semilin_conj_eq_self hr hp x.2 hXp ⟨A, 1⟩ hg
    change A * gspAut r K 1 (spXg x) * A⁻¹ = spXg x at h1
    rw [gspAut_apply, SteinbergBY.gspFieldMap_one] at h1
    show A ∈ Subgroup.centralizer ({spXg x} : Set (gsp r K))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc A * spXg x = A * spXg x * A⁻¹ * A := by group
      _ = spXg x * A := by rw [h1]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨⟨A, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hA]

end Kernel

end CFSG.RankThree.PartOne.KCSpComm
