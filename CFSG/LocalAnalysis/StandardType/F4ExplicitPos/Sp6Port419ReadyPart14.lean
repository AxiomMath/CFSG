module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart4

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section

namespace CFSG.StandardType.F4ExplicitPos.OrbitKernel
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.LieCore

theorem map_le_centralizer_singleton_of_fixed
    {G : Type*} [Group G] (F : G →* G) {y : G}
    (hy : F y = y) {H : Subgroup G}
    (hH : H ≤ Subgroup.centralizer ({y} : Set G)) :
    H.map F ≤ Subgroup.centralizer ({y} : Set G) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : w * y = y * w := by
    have := hH hw
    rwa [Subgroup.mem_centralizer_singleton_iff] at this
  have h := congrArg F hcomm
  simpa only [map_mul, hy] using h

theorem rootSpan_ratOrbit_le_centralizer_of_fixed
    {τ : Tag} {L : Type} [Field L]
    (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ)
    {y : ModGL τ L} (hyF : D.step y = y)
    (hΨC : rootSpan τ L Ψ ≤
      Subgroup.centralizer ({y} : Set (ModGL τ L))) :
    rootSpan τ L (ratOrbit (fun u => ρ u) Ψ) ≤
      Subgroup.centralizer ({y} : Set (ModGL τ L)) := by
  have hstep : ∀ H : Subgroup (ModGL τ L),
      H ≤ Subgroup.centralizer ({y} : Set (ModGL τ L)) →
      H.map D.step ≤ Subgroup.centralizer ({y} : Set (ModGL τ L)) :=
    fun H hH => map_le_centralizer_singleton_of_fixed D.step hyF hH
  have hisRoot : ∀ k : ℕ, ∀ δ : Fin τ.rank → ℤ, δ ∈ Ψ →
      IsRoot τ ((fun u => ρ u)^[k] δ) := by
    intro k
    induction k with
    | zero =>
      intro δ hδ
      simpa using hΨ δ hδ
    | succ k ih =>
      intro δ hδ
      rw [Function.iterate_succ_apply']
      exact (hρ.isRoot_iff _).mpr (ih δ hδ)
  have hroot : ∀ k : ℕ, ∀ δ : Fin τ.rank → ℤ, δ ∈ Ψ →
      rootSubgroup τ L ((fun u => ρ u)^[k] δ) ≤
        Subgroup.centralizer ({y} : Set (ModGL τ L)) := by
    intro k
    induction k with
    | zero =>
      intro δ hδ
      exact (le_iSup₂_of_le δ hδ le_rfl).trans hΨC
    | succ k ih =>
      intro δ hδ
      rw [Function.iterate_succ_apply']
      rw [← hρ.map_rootSubgroup ((fun u => ρ u)^[k] δ) (hisRoot k δ hδ)]
      exact hstep _ (ih δ hδ)
  refine iSup_le fun α => iSup_le fun hα => ?_
  obtain ⟨k, δ, hδ, rfl⟩ := hα
  exact hroot k δ hδ

theorem subgroup_le_centralizer_of_le_orbitSpan
    {τ : Tag} {L : Type} [Field L]
    (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ)
    {K : Subgroup (ModGL τ L)}
    (hK : K ≤ rootSpan τ L (ratOrbit (fun u => ρ u) Ψ))
    {y : ModGL τ L} (hyF : D.step y = y)
    (hΨC : rootSpan τ L Ψ ≤
      Subgroup.centralizer ({y} : Set (ModGL τ L))) :
    K ≤ Subgroup.centralizer ({y} : Set (ModGL τ L)) :=
  hK.trans (rootSpan_ratOrbit_le_centralizer_of_fixed D ρ hρ hΨ hyF hΨC)

theorem rootSpan_rationalRoots_le_centralizer_of_fixed
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (i : KernelComponent χ) {y : ModGL τ L}
    (hyF : S.D.step y = y)
    (hiC : rootSpan τ L (componentRoots χ i) ≤
      Subgroup.centralizer ({y} : Set (ModGL τ L))) :
    rootSpan τ L (rationalRoots S.ρ χ i) ≤
      Subgroup.centralizer ({y} : Set (ModGL τ L)) :=
  rootSpan_ratOrbit_le_centralizer_of_fixed S.D S.ρ S.frob
    (fun γ hγ => isRoot_of_mem_componentRoots hγ) hyF hiC

theorem mem_centralizer_of_mem_centralizer_rootSpan
    {τ : Tag} {L : Type} [Field L]
    (D : LangDatum τ L) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ)
    {K : Subgroup (ModGL τ L)} (hK : K ≤ rootSpan τ L (ratOrbit (fun u => ρ u) Ψ))
    {y : ModGL τ L} (hyF : D.step y = y)
    (hy : y ∈ Subgroup.centralizer (rootSpan τ L Ψ : Set (ModGL τ L))) :
    y ∈ Subgroup.centralizer (K : Set (ModGL τ L)) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro k hk
  have hΨC : rootSpan τ L Ψ ≤ Subgroup.centralizer ({y} : Set (ModGL τ L)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hy z hz
  have hKc : k ∈ Subgroup.centralizer ({y} : Set (ModGL τ L)) :=
    subgroup_le_centralizer_of_le_orbitSpan D ρ hρ hΨ hK hyF hΨC hk
  rwa [Subgroup.mem_centralizer_singleton_iff] at hKc

theorem card_range_le_of_ker_le
    {B U V : Type*} [Group B] [Finite B] [Group U] [Group V]
    (γ : B →* U) (δ : B →* V) (hker : γ.ker ≤ δ.ker) :
    Nat.card δ.range ≤ Nat.card γ.range := by
  have : Finite (B ⧸ γ.ker) :=
    Finite.of_surjective (QuotientGroup.mk' γ.ker) (QuotientGroup.mk'_surjective γ.ker)
  have hψ : (QuotientGroup.lift γ.ker δ hker).range = δ.range := by
    ext v
    constructor
    · intro hv
      obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hv
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective γ.ker q
      exact MonoidHom.mem_range.mpr
        ⟨b, (QuotientGroup.lift_mk' (N := γ.ker) (φ := δ) hker b).symm⟩
    · intro hv
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hv
      exact MonoidHom.mem_range.mpr
        ⟨QuotientGroup.mk' γ.ker b,
          (QuotientGroup.lift_mk' (N := γ.ker) (φ := δ) hker b).trans hb⟩
  calc
    Nat.card δ.range = Nat.card (QuotientGroup.lift γ.ker δ hker).range := by rw [hψ]
    _ ≤ Nat.card (B ⧸ γ.ker) := Finite.card_range_le (QuotientGroup.lift γ.ker δ hker)
    _ = Nat.card γ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange γ).toEquiv

end CFSG.StandardType.F4ExplicitPos.OrbitKernel

end

public section

namespace CFSG.StandardType.F4ExplicitPos.ProjectiveRank

open Matrix CFSG.Open

variable {K L : Type} [Field K] [Field L]

theorem exists_isPrimitiveRoot_units_of_isAlgClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {p : ℕ} (hp : p.Prime) (hpΩ : (p : Ω) ≠ 0) :
    ∃ ζ : Ωˣ, IsPrimitiveRoot ζ p := by
  have : NeZero (p : Ω) := ⟨hpΩ⟩
  have : HasEnoughRootsOfUnity Ω p := IsSepClosed.hasEnoughRootsOfUnity Ω p
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  exact ⟨(hζ₀.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.mp (by
    rw [IsUnit.unit_spec]
    exact hζ₀)⟩

theorem mem_range_glMap_of_entries {n : ℕ} (φ : K →+* L) (hφ : Function.Injective φ)
    {g : GL (Fin n) L}
    (hM : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ Set.range φ)
    (hMi : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Set.range φ) :
    g ∈ (Matrix.GeneralLinearGroup.map φ).range := by
  classical
  let M : Matrix (Fin n) (Fin n) K := fun i j => Classical.choose (hM i j)
  let N : Matrix (Fin n) (Fin n) K := fun i j => Classical.choose (hMi i j)
  have hMmap : M.map φ = (g : Matrix (Fin n) (Fin n) L) := by
    ext i j
    rw [Matrix.map_apply]
    exact Classical.choose_spec (hM i j)
  have hNmap : N.map φ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j
    rw [Matrix.map_apply]
    exact Classical.choose_spec (hMi i j)
  have hMN : M * N = 1 := by
    apply Matrix.map_injective hφ
    change (M * N).map (⇑φ) = (1 : Matrix (Fin n) (Fin n) K).map (⇑φ)
    rw [Matrix.map_mul, hMmap, hNmap, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact (Matrix.map_one φ (map_zero φ) (map_one φ)).symm
  have hNM : N * M = 1 := by
    apply Matrix.map_injective hφ
    change (N * M).map (⇑φ) = (1 : Matrix (Fin n) (Fin n) K).map (⇑φ)
    rw [Matrix.map_mul, hNmap, hMmap, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact (Matrix.map_one φ (map_zero φ) (map_one φ)).symm
  let h : GL (Fin n) K := Units.mk M N hMN hNM
  have hmap : Matrix.GeneralLinearGroup.map φ h = g := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_map_apply]
    change M.map φ = (g : Matrix (Fin n) (Fin n) L)
    exact hMmap
  exact MonoidHom.mem_range.mpr ⟨h, hmap⟩

theorem mem_center_of_map_mem_statedScalars (φ : K →+* L) (hφ : Function.Injective φ)
    {n : ℕ} (hn : 0 < n) {A : GL (Fin n) K}
    (h : Matrix.GeneralLinearGroup.map φ A ∈ StatedScalars (Fin n) L) :
    A ∈ Subgroup.center (GL (Fin n) K) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
  obtain ⟨c, hc⟩ := h
  have hentry : ∀ i j, φ ((A : Matrix (Fin n) (Fin n) K) i j) =
      if i = j then (c : L) else 0 := by
    intro i j
    have hthis := congrArg (fun M : GL (Fin n) L =>
      (M : Matrix (Fin n) (Fin n) L) i j) hc
    simp only [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map_apply] at hthis
    exact hthis.symm
  have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i j hij
    apply hφ
    rw [hentry i j, if_neg hij, map_zero]
  have hdiag : ∀ i, (A : Matrix (Fin n) (Fin n) K) i i =
      (A : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩ := by
    intro i
    apply hφ
    rw [hentry i i, hentry ⟨0, hn⟩ ⟨0, hn⟩, if_pos rfl, if_pos rfl]
  have hA0 : (A : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩ ≠ 0 := by
    intro h0
    have hzero : (A : Matrix (Fin n) (Fin n) K) = 0 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [hdiag i, h0]
        simp
      · rw [hoff i j hij]
        simp
    exact A.isUnit.ne_zero hzero
  refine ⟨Units.mk0 ((A : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hA0, ?_⟩
  ext i j
  simp only [Matrix.GeneralLinearGroup.scalar]
  by_cases hij : i = j
  · subst hij
    simp [hdiag]
  · simp [hij, hoff i j hij]

end CFSG.StandardType.F4ExplicitPos.ProjectiveRank
end
end
end
end
end
end
end

end
