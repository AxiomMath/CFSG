module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsOrthBlock
import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthSelfDual
import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthFixed
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly Polynomial CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

private theorem orthTLift_center_eq_bot {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Subgroup.center (ProjOrthDerived Q) = ⊥ := by
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (ProjOrthDerived Q)) with h | h
  · exact h
  · exfalso
    obtain ⟨c, e, hce⟩ := hnonab
    exact hce (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top e) c)

private theorem orthTLift_liftA
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q)) :
    ∃ (Â : Subgroup (orthDerived Q)) (x : orthDerived Q),
      x ∈ Â ∧ Nat.card Â = Nat.card Ā ∧
      (∀ a ∈ Â, a ^ 3 = 1) ∧ (∀ a ∈ Â, ∀ b ∈ Â, a * b = b * a) ∧
      (∀ a ∈ Â, (a : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      (MulAut.conj ((x : orthDerived Q) : ProjOrthDerived Q) = δ') ∧
      (∀ a : MulAut (ProjOrthDerived Q), a ∈ Ā ↔
        ∃ b ∈ Â, MulAut.conj ((b : orthDerived Q) : ProjOrthDerived Q) = a) := by
  classical
  have hV : Nontrivial V := by
    obtain ⟨U, hU, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by omega) (Submodule.finrank_le U))
  have hscal : (CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q) = ⊥ :=
    CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  set π : orthDerived Q →* ProjOrthDerived Q := QuotientGroup.mk' _ with hπ
  have hker : π.ker = ⊥ := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hscal
  have hπinj : Function.Injective π := by
    intro a b hab
    have hmem : a * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    rw [hker] at hmem
    have h1 : a * b⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc a = a * b⁻¹ * b := by group
      _ = 1 * b := by rw [h1]
      _ = b := one_mul b
  let e : orthDerived Q ≃* ProjOrthDerived Q :=
    MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective _⟩
  obtain ⟨-, hcenter, -, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterΩ : Subgroup.center (orthDerived Q) = ⊥ := by
    rw [hcenter, hscal]
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    have hzc : e.symm z ∈ Subgroup.center (orthDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hz (e y)
    rw [hcenterΩ] at hzc
    have h1 : e.symm z = 1 := Subgroup.mem_bot.mp hzc
    have h2 := congrArg e h1
    simpa using h2
  have hconj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
    intro a b hab
    have h1 : MulAut.conj (b⁻¹ * a) = 1 := by
      rw [map_mul, map_inv, ← hab, inv_mul_cancel]
    have hc : b⁻¹ * a ∈ Subgroup.center (ProjOrthDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun f : MulAut (ProjOrthDerived Q) => f x) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * (b⁻¹ * a) = ((b⁻¹ * a) * x * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [hx]
        _ = (b⁻¹ * a) * x := by group
    have hz : b⁻¹ * a = 1 := Subgroup.mem_bot.mp (hcenterT ▸ hc)
    calc a = b * (b⁻¹ * a) := by group
      _ = b * 1 := by rw [hz]
      _ = b := mul_one b
  have hĀle : Ā ≤ (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range :=
    fun a ha => hĀI a ha
  let B : Subgroup (ProjOrthDerived Q) :=
    Ā.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))
  have hBmap : B.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = Ā :=
    Subgroup.map_comap_eq_self hĀle
  have hcardB : Nat.card B = Nat.card Ā := by
    have h := Subgroup.card_map_of_injective (K := B) hconj
    rw [hBmap] at h
    exact h.symm
  let Â : Subgroup (orthDerived Q) := B.map e.symm.toMonoidHom
  have hcardÂ : Nat.card Â = Nat.card Ā :=
    (Subgroup.card_map_of_injective (K := B) e.symm.injective).trans hcardB
  obtain ⟨t, ht⟩ := hĀI δ' hR.mem
  have htB : t ∈ B := Subgroup.mem_comap.mpr (ht ▸ hR.mem)
  have hxmem : e.symm t ∈ Â := Subgroup.mem_map.mpr ⟨t, htB, rfl⟩
  refine ⟨Â, e.symm t, hxmem, hcardÂ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hb3 : b ^ 3 = 1 :=
      hconj (by rw [map_pow, hR.elem.2 (MulAut.conj b) hb, map_one])
    rw [← map_pow, hb3, map_one]
  ·
    intro a ha b hb
    obtain ⟨b1, hb1, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b2, hb2, rfl⟩ := Subgroup.mem_map.mp hb
    have hcomm : b1 * b2 = b2 * b1 := by
      have h1 : MulAut.conj (b1 * b2 * b1⁻¹ * b2⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [CFSG.Open.IsElemAbelian.comm hR.elem hb1 hb2]
        group
      have h2 : b1 * b2 * b1⁻¹ * b2⁻¹ = 1 := hconj (by simpa using h1)
      calc b1 * b2 = (b1 * b2 * b1⁻¹ * b2⁻¹) * (b2 * b1) := by group
        _ = 1 * (b2 * b1) := by rw [h2]
        _ = b2 * b1 := one_mul _
    rw [← map_mul, ← map_mul, hcomm]
  ·
    intro a ha
    exact CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2
  ·
    have hcoe : ((e.symm t : orthDerived Q) : ProjOrthDerived Q) = t := e.apply_symm_apply t
    rw [hcoe, ht]
  ·
    intro a
    constructor
    · intro ha
      obtain ⟨t, ht⟩ := hĀI a ha
      have htB : t ∈ B := Subgroup.mem_comap.mpr (ht ▸ ha)
      refine ⟨e.symm t, Subgroup.mem_map.mpr ⟨t, htB, rfl⟩, ?_⟩
      have hcoe : ((e.symm t : orthDerived Q) : ProjOrthDerived Q) = t := e.apply_symm_apply t
      rw [hcoe, ht]
    · rintro ⟨b, hb, rfl⟩
      change MulAut.conj (e b) ∈ Ā
      obtain ⟨t, htB, hb⟩ := Subgroup.mem_map.mp hb
      have hbB : e b ∈ B := by
        rw [← hb]
        change e (e.symm t) ∈ B
        rw [e.apply_symm_apply]
        exact htB
      exact Subgroup.mem_comap.mp hbB

private theorem orthTLift_rho_injective {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    [Nontrivial V]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Function.Injective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) :
      orthDerived Q →* ProjOrthDerived Q) := by
  have hscal : (CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q) = ⊥ :=
    CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  intro a b hab
  have hmem : a * b⁻¹ ∈ (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) :
      orthDerived Q →* ProjOrthDerived Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  rw [QuotientGroup.ker_mk', hscal, Subgroup.mem_bot] at hmem
  calc a = a * b⁻¹ * b := by group
    _ = 1 * b := by rw [hmem]
    _ = b := one_mul b

private theorem orthTLift_conj_injective {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
  have hc := orthTLift_center_eq_bot hQ hT
  intro a b hab
  have h1 : MulAut.conj (b⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, ← hab, inv_mul_cancel]
  have hmem : b⁻¹ * a ∈ Subgroup.center (ProjOrthDerived Q) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut (ProjOrthDerived Q) => f x) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * (b⁻¹ * a) = ((b⁻¹ * a) * x * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [hx]
      _ = (b⁻¹ * a) * x := by group
  have hz : b⁻¹ * a = 1 := Subgroup.mem_bot.mp (hc ▸ hmem)
  calc a = b * (b⁻¹ * a) := by group
    _ = b * 1 := by rw [hz]
    _ = b := mul_one b

private theorem orthTLift_fixSubgroup_conj_eq_centralizer {G : Type*} [Group G] (t : G) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj t) =
      Subgroup.centralizer ({t} : Set G) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem orthTLift_centralizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    [Nontrivial V]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (x : orthDerived Q) :
    Subgroup.centralizer ({(QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x)} :
      Set (ProjOrthDerived Q)) = centralizerImage Q (x : V ≃ₗ[K] V) := by
  rw [← CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x]
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      ((scalars K V).subgroupOf (orthDerived Q)) g
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    refine orthTLift_rho_injective hQ ?_
    rw [map_mul, map_mul]
    exact hg
  · rintro g ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    simpa only [map_mul] using congrArg
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) hy'

private theorem orthTLift_comp_iff {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : orthDerived Q} {δ' : MulAut (ProjOrthDerived Q)}
    (hδ : δ' = MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x))
    {L : Subgroup (ProjOrthDerived Q)} :
    CFSG.Assembly.IsComponentOf L (ggAutFixedSubgroup δ') ↔
      CFSG.Open.IsComponentOf L
        (Subgroup.centralizer
          ({(QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x)} :
            Set (ProjOrthDerived Q))) := by
  rw [CFSG.Assembly.isComponentOf_iff_open]
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ' =
      ggAutFixedSubgroup δ' := by ext y; rfl
  rw [← hfix, hδ, orthTLift_fixSubgroup_conj_eq_centralizer]

private theorem orthTLift_block_comp {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : orthDerived Q} {h : K[X]}
    (hh : h ∈ primaryFactors ((x : V ≃ₗ[K] V).toLinearMap)) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) :
    CFSG.Open.IsComponentOf (componentImage Q (x : V ≃ₗ[K] V) h)
      (centralizerImage Q (x : V ≃ₗ[K] V)) := by
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isComponentOf_of_normal_normal
    componentImage_le_centralizerImage le_rfl normal_componentImage
    (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
    (isQuasisimple_map_projective ?_ hq)
  exact specialBlock_le_orthDerived_of_perfect hq.1
    ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))

private theorem orthTLift_fixed_comp {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : orthDerived Q} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFsup : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn : (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal) :
    CFSG.Open.IsComponentOf
      ((F.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
      (centralizerImage Q (x : V ≃ₗ[K] V)) := by
  have hFΩ : F ≤ orthDerived Q := hFsup.trans hx.supportedFixedDerived_le_orthDerived
  have hCle : (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ≤
      fixedComponentImage Q (x : V ≃ₗ[K] V) :=
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      (hFsup (Subgroup.mem_subgroupOf.mp hg))
  have hconj := map_conj_mem
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
    (F := F.subgroupOf (orthDerived Q))
    (F' := (supportedFixedDerived Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q))
    (fun a b ha hb => by
      have := (Subgroup.normal_subgroupOf_iff hFsup).mp hFn (a : V ≃ₗ[K] V) (b : V ≃ₗ[K] V)
        (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb)
      exact Subgroup.mem_subgroupOf.mpr this)
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isComponentOf_of_normal_normal
    hCle fixedComponentImage_le_centralizerImage ?_ hx.normal_fixedComponentImage
    (isQuasisimple_map_projective hFΩ hFq)
  rw [Subgroup.normal_subgroupOf_iff hCle]
  intro g k hg hk
  exact hconj g k hg hk

private theorem orthTLift_uniq {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    [Nontrivial V]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : orthDerived Q}
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hδ : δ' = MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x)) :
    ∀ L : Subgroup (ProjOrthDerived Q),
      CFSG.Open.IsComponentOf L (centralizerImage Q (x : V ≃ₗ[K] V)) → L = J' := by
  intro L hL
  refine hR.uniq L ((orthTLift_comp_iff (x := x) hδ (L := L)).2 ?_)
  rwa [orthTLift_centralizer hQ x]

private theorem orthTLift_ker {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    [Nontrivial V]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    {Â : Subgroup (orthDerived Q)} {x : orthDerived Q}
    (hconjδ : MulAut.conj ((x : orthDerived Q) : ProjOrthDerived Q) = δ')
    (hmap : ∀ a : MulAut (ProjOrthDerived Q), a ∈ Ā ↔
      ∃ b ∈ Â, MulAut.conj ((b : orthDerived Q) : ProjOrthDerived Q) = a)
    {y : orthDerived Q} (hy : y ∈ Â)
    (hcent : ∀ g ∈ J', ((y : orthDerived Q) : ProjOrthDerived Q) * g =
      g * ((y : orthDerived Q) : ProjOrthDerived Q)) :
    y ∈ Subgroup.zpowers x := by
  have hmemĀ : MulAut.conj ((y : orthDerived Q) : ProjOrthDerived Q) ∈ Ā :=
    (hmap _).2 ⟨y, hy, rfl⟩
  have hfix : ∀ g ∈ J', MulAut.conj ((y : orthDerived Q) : ProjOrthDerived Q) g = g := by
    intro g hg
    rw [MulAut.conj_apply, hcent g hg]
    group
  have hzp : MulAut.conj ((y : orthDerived Q) : ProjOrthDerived Q) ∈
      Subgroup.zpowers (MulAut.conj ((x : orthDerived Q) : ProjOrthDerived Q)) := by
    rw [hconjδ]
    exact hR.ker _ hmemĀ hfix
  rw [Subgroup.mem_zpowers_iff] at hzp ⊢
  obtain ⟨n, hn⟩ := hzp
  refine ⟨n, ?_⟩
  refine orthTLift_rho_injective hQ ?_
  refine orthTLift_conj_injective hQ hT ?_
  rw [map_zpow, map_zpow]
  exact hn

theorem orthT_lift {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q)) :
    ∃ (x : ↥(orthDerived Q)) (Â : Subgroup ↥(orthDerived Q)),
      MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) = δ' ∧
      OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) ∧ x ≠ 1 ∧ x ∈ Â ∧ CFSG.Open.IsElemAbelian 3 Â ∧
      Nat.card Â = Nat.card Ā ∧
      (∀ y ∈ Â, MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y) ∈ Ā) ∧
      (∀ y ∈ Â, (∀ g ∈ J', QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y * g =
          g * QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y) → y ∈ Subgroup.zpowers x) ∧
      (∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) →
          componentImage Q (x : V ≃ₗ[K] V) h = J') ∧
      (∀ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F →
        F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) →
        (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal →
          (F.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) = J') ∧
      ((∃ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧
          CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
          J' = componentImage Q (x : V ≃ₗ[K] V) h) ∨
        ∃ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F ∧
          F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
          (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
          J' = (F.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) := by
  classical
  have hV : Nontrivial V := by
    obtain ⟨U, hU, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by omega) (Submodule.finrank_le U))
  haveI : Nontrivial V := hV
  obtain ⟨Â, x, hxÂ, hcard, hexp, hcomm, -, hconj, hmap⟩ :=
    orthTLift_liftA hQ hT hR hĀI
  have hx3 : x ^ 3 = 1 := hexp x hxÂ
  have hJ : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({(QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x)} :
        Set (ProjOrthDerived Q))) :=
    (orthTLift_comp_iff (x := x) hconj.symm (L := J')).1 hR.comp
  have hpℓ : (3 : ℕ) ≠ ringChar K := by
    rw [ringChar.eq K 2]
    decide
  obtain ⟨x₀, hx₀ρ, hx₀odd, hx₀cases⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.orth_component_named
      Nat.prime_three (by decide) hQ hT hpℓ
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x)
      (by rw [← map_pow, hx3, map_one]) J' hJ
  have hx0x : x₀ = x := orthTLift_rho_injective hQ hx₀ρ
  subst x₀
  refine ⟨x, Â, hconj, hx₀odd, ?_, hxÂ, ?_, hcard, ?_, ?_, ?_, ?_, hx₀cases⟩
  · intro hx1
    apply hR.ne_one
    rw [← hconj, hx1]
    simp
  · refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext ?_), fun a ha => ?_⟩
    · exact hcomm a.1 a.2 b.1 b.2
    · exact hexp a ha
  · intro y hy
    exact (hmap (MulAut.conj ((y : orthDerived Q) : ProjOrthDerived Q))).2 ⟨y, hy, rfl⟩
  · intro y hy hcent
    exact orthTLift_ker hQ hT hR hconj hmap hy hcent
  · intro h hh hne hq
    exact orthTLift_uniq hQ hR hconj.symm (componentImage Q (x : V ≃ₗ[K] V) h)
      (orthTLift_block_comp hh hne hq)
  · intro F hFq hFsup hFn
    exact orthTLift_uniq hQ hR hconj.symm
      ((F.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
      (orthTLift_fixed_comp hx₀odd hFq hFsup hFn)

end CFSG.StandardType.TablePThreeKG

end
