module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdCore
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdBlock
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUnitaryRoot

public section

namespace CFSG.StandardType.IOneUDvdR

open scoped commutatorElement

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover
  CFSG.StandardType.UnitTB CFSG.StandardType.TableBUE CFSG.StandardType.SmallU
  CFSG.LocalAnalysis.ComponentInitial

section Block

variable {K : Type} [Field K] {n d : ℕ}

theorem comm_mem_blockSU_of_centSU {σ : Fin d → Kˣ} {S : Finset (Fin d)} (hτ : IsNodeOn σ S)
    {g g' : ↥(unitarySU 2 n K d)}
    (hg : (g : GL (Fin d) K) * diagHom d σ = diagHom d σ * g)
    (hg' : (g' : GL (Fin d) K) * diagHom d σ = diagHom d σ * g') :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSU S := by
  have hdiag : ∀ h : GL (Fin d) K, h * diagHom d σ = diagHom d σ * h →
      ∀ i ∉ S, DiagAt i (h : Matrix (Fin d) (Fin d) K) := by
    intro h hh i hi
    exact ⟨fun j hj => entry_eq_zero_of_commute hh (hτ.2 i hi j hj).symm,
      fun j hj => entry_eq_zero_of_commute hh (hτ.2 i hi j hj)⟩
  have hc1 : (g : GL (Fin d) K) * diagHom d σ = diagHom d σ * g := hg
  have hc2 : (g' : GL (Fin d) K) * diagHom d σ = diagHom d σ * g' := hg'
  have hc3 : ((g : GL (Fin d) K))⁻¹ * diagHom d σ = diagHom d σ * ((g : GL (Fin d) K))⁻¹ :=
    Commute.inv_left (show Commute (g : GL (Fin d) K) (diagHom d σ) from hc1)
  have hc4 : ((g' : GL (Fin d) K))⁻¹ * diagHom d σ = diagHom d σ * ((g' : GL (Fin d) K))⁻¹ :=
    Commute.inv_left (show Commute (g' : GL (Fin d) K) (diagHom d σ) from hc2)
  have key : ∀ i ∉ S, DiagAt i (((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) :
      GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ∧
      (((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) i i = 1 := by
    intro i hi
    have d1 := hdiag _ hc1 i hi
    have d2 := hdiag _ hc2 i hi
    have d3 := hdiag _ hc3 i hi
    have d4 := hdiag _ hc4 i hi
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at d3 d4 ⊢
    refine ⟨((d1.mul d2).mul d3).mul d4, ?_⟩
    rw [(((d1.mul d2)).mul d3).mul_apply d4, (d1.mul d2).mul_apply d3, d1.mul_apply d2]
    have e1 : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← d1.mul_apply d3, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    have e2 : ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g' : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← d2.mul_apply d4, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    linear_combination (((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g' : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) * e1 + e2
  rw [mem_blockSU]
  intro i j hij
  rcases hij with hi | hj
  · obtain ⟨hd, h1⟩ := key i hi
    by_cases hji : j = i
    · subst hji
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.1 j hji, Matrix.one_apply_ne (Ne.symm hji)]
  · obtain ⟨hd, h1⟩ := key j hj
    by_cases hij' : i = j
    · subst hij'
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.2 i hij', Matrix.one_apply_ne hij']

theorem layer_eq_block_of_isNodeOn {L' : Type} [Group L'] [Finite K]
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ) {a : MulAut L'}
    {σ : Fin d → Kˣ} (ha : ActsU φ a σ) {S : Finset (Fin d)} (hτ : IsNodeOn σ S)
    (hbig : BigOK n S) :
    LargeEvenLayer (ggFix a) = (blockSU S).map φ ∧
      IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
  have heig : ∀ i ∈ S, ∀ j, j ∈ S ↔ σ j = σ i := by
    intro i hi j
    constructor
    · intro hj
      exact hτ.1 j hj i hi
    · intro hj
      by_contra hjS
      have hij : i ≠ j := fun h => hjS (h ▸ hi)
      exact (hτ.2 j hjS i hij) hj.symm
  have hq := isQuasisimple_block hM hbig
  have hc := isComponentOf_block hM ha heig hq
  have hsub : ∀ K' : Subgroup L', IsComponentOf K' (ggFix a) → K' ≤ (blockSU S).map φ := by
    intro K' hK'
    have hKH : K' ≤ ggFix a := hK'.1
    have hperf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.mpr hK'.2.2.1)
    have hcent : ⁅K', K'⁆ ≤ cent0 φ (diagHom d σ) :=
      Subgroup.commutator_le.mpr fun x hx y hy => comm_mem_cent0 hM ha (hKH hx) (hKH hy)
    have hKcent : K' ≤ cent0 φ (diagHom d σ) := (le_of_eq hperf.symm).trans hcent
    have hcomm : ⁅K', K'⁆ ≤ (blockSU S).map φ := by
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (hKcent hx)
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp (hKcent hy)
      exact Subgroup.mem_map.mpr ⟨⁅g, g'⁆,
        comm_mem_blockSU_of_centSU hτ (mem_centSU.mp hg) (mem_centSU.mp hg'),
        map_commutatorElement φ g g'⟩
    exact (le_of_eq hperf.symm).trans hcomm
  have hle : LargeEvenLayer (ggFix a) ≤ (blockSU S).map φ := sSup_le hsub
  have hge : (blockSU S).map φ ≤ LargeEvenLayer (ggFix a) := le_sSup hc
  have heq : LargeEvenLayer (ggFix a) = (blockSU S).map φ := le_antisymm hle hge
  exact ⟨heq, by rw [heq]; exact hc⟩

end Block

section Injective

variable {K : Type} [Field K] {n d : ℕ}

theorem eq_one_of_projMk_eq_one_of_block {S : Finset (Fin d)} (hS : S ≠ Finset.univ)
    {x : ↥(unitarySU 2 n K d)} (hx : x ∈ blockSU S)
    (hπ : LargeEvenProjMk (unitarySU 2 n K d) x = 1) : x = 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin d, i₀ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hS (Finset.eq_univ_of_forall hcon)
  have hz : (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    have h1 := hπ
    rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, largeEvenScalars_def] at h1
    exact h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  have h2 := congrFun (congrFun (congrArg
    (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hu) i₀) i₀
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h2
  have h3 := (mem_blockSU.mp hx) i₀ i₀ (Or.inl hi₀)
  have hu1' : (u : K) = 1 := by
    rw [h2, h3, Matrix.one_apply_eq]
  have hu1 : u = 1 := Units.ext hu1'
  apply Subtype.ext
  rw [Subgroup.coe_one, ← hu, hu1, map_one]

theorem projMk_eq_one_of_center {x : ↥(unitarySU 2 n K d)}
    (hx : (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K)) :
    LargeEvenProjMk (unitarySU 2 n K d) x = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
  show (QuotientGroup.mk x : LargeEvenProj (unitarySU 2 n K d)) = 1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, largeEvenScalars_def]
  exact hx

theorem psi_phi_eq_one_of_block {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥)
    {S : Finset (Fin d)} (hS : S ≠ Finset.univ) {x : ↥(unitarySU 2 n K d)}
    (hx : x ∈ blockSU S) (hψx : ψ (φ x) = 1) : x = 1 := by
  apply eq_one_of_projMk_eq_one_of_block hS hx
  have hc : φ x ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hψx)
  have hcomm : ∀ r : LargeEvenProj (unitarySU 2 n K d),
      LargeEvenProjMk (unitarySU 2 n K d) x * r = r * LargeEvenProjMk (unitarySU 2 n K d) x := by
    intro r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ r
    have hxg : φ (x * g) = φ (g * x) := by
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp hc (φ g)).symm
    have hk : φ (x * g * (g * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, hxg, mul_inv_cancel]
    have hP := projMk_eq_one_of_center (mem_center_of_ker hM hk)
    rw [map_mul, map_mul, map_inv] at hP
    exact mul_inv_eq_one.mp hP
  have hPx : LargeEvenProjMk (unitarySU 2 n K d) x ∈
      Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) :=
    Subgroup.mem_center_iff.mpr fun r => (hcomm r).symm
  rw [hZ, Subgroup.mem_bot] at hPx
  exact hPx

end Injective

section BigLayer

variable {K : Type} [Field K] {n d : ℕ}

theorem bigLayer_map_of_block {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} {S : Finset (Fin d)}
    (hinj : ∀ x ∈ blockSU (K := K) (n := n) S, ψ (φ x) = 1 → x = 1)
    (hbig : 25920 < Nat.card (blockSU (K := K) (n := n) S)) :
    GGBigLayer ((Subgroup.map φ (blockSU (K := K) (n := n) S)).map ψ) := by
  refine Or.inr ?_
  rw [Subgroup.map_map]
  let g : ↥(blockSU (K := K) (n := n) S) →* LargeEvenProj (unitarySU 2 n K d) :=
    (ψ.comp φ).comp (blockSU (K := K) (n := n) S).subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h1
    apply Subtype.ext
    exact hinj x hx h1
  have hr : g.range = (blockSU (K := K) (n := n) S).map (ψ.comp φ) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card ↥((blockSU (K := K) (n := n) S).map (ψ.comp φ)) =
      Nat.card ↥(blockSU (K := K) (n := n) S) := by
    rw [← hr]
    exact (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm
  rw [hcard]
  exact hbig

end BigLayer

end CFSG.StandardType.IOneUDvdR

end
