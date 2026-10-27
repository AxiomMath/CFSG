module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcE6
public import CFSG.LieType.Chevalley.ExactNormalFormE
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

namespace KGE6

section InnerDiag

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def innDiag : Subgroup (MulAut (adjointGroup .E6 K)) :=
  (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
    (rootDiagAutHom .E6 K).range

theorem mem_innDiag_iff {δ : MulAut (adjointGroup .E6 K)} :
    δ ∈ innDiag K ↔ ∃ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ),
      δ = MulAut.conj g * rootDiagAutHom .E6 K a := by
  haveI : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range.Normal :=
    RootCentExc.normal_range_mulAutConj
  change δ ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
    (rootDiagAutHom .E6 K).range ↔ _
  rw [Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨g, hg, z, hz, rfl⟩
    obtain ⟨g', rfl⟩ := hg
    obtain ⟨a, rfl⟩ := hz
    exact ⟨g', a, rfl⟩
  · rintro ⟨g, a, rfl⟩
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, rootDiagAutHom .E6 K a, ⟨a, rfl⟩, rfl⟩

theorem conj_mem_innDiag (g : adjointGroup .E6 K) : MulAut.conj g ∈ innDiag K :=
  Subgroup.mem_sup_left ⟨g, rfl⟩

end InnerDiag

section ExactNormal

variable {K : Type} [Field K]

local instance : NeZero (exactE .E6) := ⟨by decide⟩

theorem rootDiagAutHom_eq_exactNormalAut (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom .E6 K a = exactNormalAut .E6 K a (RingEquiv.refl K)
      ((0 : Fin (exactE .E6)) : ℕ) := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change ((rootDiagAut .E6 K a) g : ModGL .E6 K) =
    ((exactNormalAut .E6 K a (RingEquiv.refl K)
      ((0 : Fin (exactE .E6)) : ℕ)) g : ModGL .E6 K)
  have h0 : ((0 : Fin (exactE .E6)) : ℕ) = 0 := rfl
  rw [coe_rootDiagAut, coe_exactNormalAut, h0, exactQ_zero]
  have hid : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom)
      (g : ModGL .E6 K) = (g : ModGL .E6 K) := Units.ext (entrywise_id _)
  rw [hid, mul_one, inv_one, mul_one]

end ExactNormal

section Action

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mem_innDiag_conj {G : Type} [Group G]
    {ψ : e6Data_valid.minGroup K →* G}
    (hker : ψ.ker ≤ Subgroup.center (e6Data_valid.minGroup K))
    {ψbar : adjointGroup .E6 K →* G} (hinj : Function.Injective ψbar)
    (hcomp : ∀ x, ψbar (e6Isogeny K x) = ψ x)
    {y : G} (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G))
    (hy : GGPsiInnerDiag (e6Datum K) ψ y) :
    ∃ δ ∈ innDiag K, ∀ u : adjointGroup .E6 K, y⁻¹ * ψbar u * y = ψbar (δ u) := by
  have hπker : (e6Isogeny K).ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      rw [← hcomp x, hx, map_one]
    · intro hx
      apply hinj
      rw [hcomp x, hx, map_one]
  obtain ⟨a, ha⟩ := RootCentExc.exists_param_E6 ψ hker hπker hyN hy
  set Θ := AutSt.modelEquiv ψ (e6Isogeny K) (e6Isogeny_surjective K) hπker with hΘ
  set κ := ψ.range.normalizerMonoidHom with hκ
  obtain ⟨g', hg'⟩ := ha
  have hκeq : κ ⟨y, hyN⟩ =
      MulAut.conj g' * MulAut.congr Θ (rootDiagAutHom .E6 K a) := by
    rw [hg']
    have hXY : ((MulAut.congr Θ).toMonoidHom.comp (rootDiagAutHom .E6 K)) a =
        MulAut.congr Θ (rootDiagAutHom .E6 K a) := rfl
    rw [hXY]
    group
  refine ⟨(rootDiagAutHom .E6 K a)⁻¹ * MulAut.conj (Θ.symm g')⁻¹, ?_, fun u => ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_)
      (Subgroup.mem_sup_left ⟨(Θ.symm g')⁻¹, rfl⟩)
    exact Subgroup.mem_sup_right ⟨a, rfl⟩
  · have hδ : MulAut.congr Θ ((rootDiagAutHom .E6 K a)⁻¹ *
        MulAut.conj (Θ.symm g')⁻¹) = (κ ⟨y, hyN⟩)⁻¹ := by
      rw [map_mul, map_inv, AutSt.congr_conj, map_inv, MulEquiv.apply_symm_apply, hκeq,
        map_inv]
      group
    have hκcoe : ∀ (m : Subgroup.normalizer (ψ.range : Set G)) (x : ψ.range),
        ((κ m x : ψ.range) : G) = (m : G) * (x : G) * (m : G)⁻¹ := fun _ _ => rfl
    have hκinvcoe : ∀ (m : Subgroup.normalizer (ψ.range : Set G)) (x : ψ.range),
        (((κ m)⁻¹ x : ψ.range) : G) = (m : G)⁻¹ * (x : G) * (m : G) := by
      intro m x
      rw [← map_inv, hκcoe, Subgroup.coe_inv, inv_inv]
    have hΘeq : ∀ u : adjointGroup .E6 K, ((Θ u : ψ.range) : G) = ψbar u := by
      intro u
      obtain ⟨v, rfl⟩ := e6Isogeny_surjective K u
      rw [AutSt.modelEquiv_apply, ← hcomp]
    have hstep : ∀ u : adjointGroup .E6 K,
        ((κ ⟨y, hyN⟩)⁻¹ (Θ u) : ψ.range) = Θ
          (((rootDiagAutHom .E6 K a)⁻¹ * MulAut.conj (Θ.symm g')⁻¹) u) := by
      intro u
      simp only [← hδ, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    calc y⁻¹ * ψbar u * y
        = y⁻¹ * (Θ u : G) * y := by rw [hΘeq u]
      _ = ((κ ⟨y, hyN⟩)⁻¹ (Θ u) : G) := by
            rw [hκinvcoe]
      _ = ((Θ (((rootDiagAutHom .E6 K a)⁻¹ * MulAut.conj (Θ.symm g')⁻¹) u) : ψ.range) : G) :=
            by rw [hstep u]
      _ = ψbar (((rootDiagAutHom .E6 K a)⁻¹ * MulAut.conj (Θ.symm g')⁻¹) u) := hΘeq _

end Action

section Propagation

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem of_conj {τ : Tag} {P : adjointGroup τ K → Prop}
    (hP : ∀ g z : adjointGroup τ K, P z → P (g * z * g⁻¹))
    {z g : adjointGroup τ K} (h : P (g * z * g⁻¹)) : P z := by
  have h' := hP g⁻¹ (g * z * g⁻¹) h
  change P (g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹) at h'
  rwa [show g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z by group] at h'

section Adj

private theorem iff_of_adj {τ : Tag} {P : adjointGroup τ K → Prop}
    (hP : ∀ g z : adjointGroup τ K, P z → P (g * z * g⁻¹))
    (h2 : (2 : K) = 0) (F : RootOperatorFamily τ) {j k : Fin τ.rank}
    (h1 : τ.cartan k j = -1) (h1' : τ.cartan j k = -1) :
    P (xPar F (Pi.single j 1) (1 : K)) ↔ P (xPar F (Pi.single k 1) (1 : K)) := by
  obtain ⟨g, hg⟩ := RootCentExc.exists_conj_xPar_single_of_adj h2 F h1 h1'
  constructor
  · intro h
    rw [← hg]
    exact hP g _ h
  · intro h
    rw [← hg] at h
    exact of_conj hP h

end Adj

section OfMem

theorem of_mem_rootGroup_of_conj {τ : Tag} {P : adjointGroup τ K → Prop}
    (hP : ∀ g z : adjointGroup τ K, P z → P (g * z * g⁻¹))
    (F : RootOperatorFamily τ) (hs : ∀ j, P (xPar F (Pi.single j 1) (1 : K)))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {z : adjointGroup τ K}
    (hz : z ∈ rootGroup F K γ) (hz1 : z ≠ 1) : P z := by
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hγ hz hz1
  have h := hs j
  rw [← hg] at h
  exact of_conj hP h

private theorem exists_single {τ : Tag} {P : adjointGroup τ K → Prop}
    (hP : ∀ g z : adjointGroup τ K, P z → P (g * z * g⁻¹))
    (F : RootOperatorFamily τ) {θ : Fin τ.rank → ℤ} {i₀ : Fin τ.rank}
    (hd : RootCentExc.HighRootData τ θ i₀) (h : P (xPar F θ (1 : K))) :
    ∃ j, P (xPar F (Pi.single j 1) (1 : K)) := by
  have hx1 : xPar F θ (1 : K) ≠ 1 := by
    intro h'
    rw [← xPar_zero (F := F) θ] at h'
    exact one_ne_zero (xPar_injective hd.maxHeight.1 h')
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hd.maxHeight.1
    (xPar_mem hd.maxHeight.1 (1 : K)) hx1
  refine ⟨j, ?_⟩
  rw [← hg]
  exact hP g _ h

end OfMem

section Singles

theorem single_E6_of_conj {P : adjointGroup .E6 K → Prop}
    (hP : ∀ g z : adjointGroup .E6 K, P z → P (g * z * g⁻¹))
    (F : RootOperatorFamily .E6) (hθ : P (xPar F RootCentExc.e6HighRoot (1 : K)))
    (j : Fin Tag.E6.rank) : P (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Q : Fin Tag.E6.rank → Prop :=
    fun j => P (xPar F (Pi.single j 1) (1 : K)) with hQ
  have step : ∀ a b : Fin Tag.E6.rank, Tag.cartan .E6 b a = -1 → Tag.cartan .E6 a b = -1 →
      (Q b ↔ Q ⟨0, by decide⟩) → (Q a ↔ Q ⟨0, by decide⟩) :=
    fun a b h h' hb => (iff_of_adj hP h2 F h h').trans hb
  have h0 : ∀ j, Q j ↔ Q ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
        (by decide) Iff.rfl)
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨4, by decide⟩ (by decide) (by decide) (step _ ⟨3, by decide⟩ (by decide)
        (by decide) (step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩
          (by decide) (by decide) Iff.rfl)))
  obtain ⟨j₁, hj₁⟩ := exists_single hP F RootCentExc.highRootData_E6 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

end Singles

end Propagation

end KGE6

end CFSG.StandardType
