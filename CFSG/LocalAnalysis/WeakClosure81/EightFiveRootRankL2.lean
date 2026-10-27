module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenL2
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

@[expose] def L2IrreducibleRank : Prop :=
  ∀ (Y : Type) [Group Y] (n : ℕ), 2 ≤ n → IsL2Gp Y n →
    ∀ (F : Type) [AddCommGroup F] [Module (ZMod 2) F] [Finite F] (σ : Y →* LGL 2 F),
      IsChiefFactor σ ⊤ ⊥ → ∀ t : Y, t * t = 1 → σ t ≠ 1 → n ≤ modCommRank (σ t)

private theorem w85g_card_subgroupOf_center_dvd {X : Type} [Group X] :
    Nat.card ((Subgroup.center X).subgroupOf (commutator X)) ∣
      Nat.card (Subgroup.center X) := by
  have he : ((Subgroup.center X).subgroupOf (commutator X)) ≃
      ((commutator X).subgroupOf (Subgroup.center X)) :=
    { toFun := fun c => ⟨⟨(c.1 : X), c.2⟩, c.1.2⟩
      invFun := fun z => ⟨⟨(z.1 : X), z.2⟩, z.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr he]
  exact Subgroup.card_subgroup_dvd_card ((commutator X).subgroupOf (Subgroup.center X))

theorem isL2Gp_commutator {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsL2Gp (X ⧸ Subgroup.center X) n) (hodd : Odd (Nat.card (Subgroup.center X))) :
    IsL2Gp ↥(commutator X) n := by
  have hperf : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    ⟨commutator_eq_top_of_isL2Gp hn hX⟩
  have hsup : commutator X ⊔ Subgroup.center X = ⊤ :=
    CFSG.RankThree.PartOne.U5K.commutator_sup_center_eq_top hperf
  haveI : Group.IsPerfect ↥(commutator X) :=
    CFSG.RankThree.PartOne.U5K.isPerfect_commutator hperf
  have hXkeep := hX
  obtain ⟨F, _, _, hcard, ⟨e₀⟩⟩ := hX
  let e2 : Matrix.SpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (center_specialLinear_two_eq_bot hcard).symm)
  let e3 := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  have eX : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSL 2 F) := e₀.trans (e2.trans e3)
  let f : ↥(commutator X) →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp (commutator X).subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ commutator X ⊔ Subgroup.center X := by rw [hsup]; trivial
    rw [Subgroup.mem_sup_of_normal_right] at hx
    obtain ⟨c, hc, z, hz, hcz⟩ := hx
    refine ⟨⟨c, hc⟩, ?_⟩
    change (QuotientGroup.mk' (Subgroup.center X)) c =
      (QuotientGroup.mk' (Subgroup.center X)) x
    have hz1 : (QuotientGroup.mk' (Subgroup.center X)) z = 1 :=
      (QuotientGroup.eq_one_iff z).2 hz
    rw [← hcz, map_mul, hz1, mul_one]
  have hker : f.ker = (Subgroup.center X).subgroupOf (commutator X) := by
    change ((QuotientGroup.mk' (Subgroup.center X)).comp (commutator X).subtype).ker =
      (Subgroup.center X).subgroupOf (commutator X)
    rw [← MonoidHom.comap_ker (QuotientGroup.mk' (Subgroup.center X)) (commutator X).subtype,
      QuotientGroup.ker_mk' (Subgroup.center X)]
    rfl
  have hDleZ : (Subgroup.center X).subgroupOf (commutator X) ≤
      Subgroup.center ↥(commutator X) :=
    Subgroup.comap_center_le_center (f := (commutator X).subtype)
      (commutator X).subtype_injective
  haveI : ((Subgroup.center X).subgroupOf (commutator X)).Normal :=
    Subgroup.Normal.subgroupOf inferInstance (commutator X)
  have hDp : IsPGroup 2 ((Subgroup.center X).subgroupOf (commutator X)) :=
    isPGroup_two_of_mulEquiv_stated_psl_two_even
      ((Subgroup.center X).subgroupOf (commutator X)) hDleZ hn hcard
      (((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans eX)
  have hDdvd := w85g_card_subgroupOf_center_dvd (X := X)
  have hDodd : Odd (Nat.card ((Subgroup.center X).subgroupOf (commutator X))) :=
    Odd.of_dvd_nat hodd hDdvd
  have hDbot : (Subgroup.center X).subgroupOf (commutator X) = ⊥ := by
    rw [← Subgroup.card_eq_one]
    rcases hDp.card_eq_or_dvd with h1 | h2
    · exact h1
    · exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hDodd)
  have eC : ↥(commutator X) ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hDbot).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
          (QuotientGroup.quotientKerEquivOfSurjective f hf)))
  exact isL2Gp_of_mulEquiv hXkeep eC.symm

theorem l2RootCommutatorRank_of_irreducible (hSt : L2IrreducibleRank) : L2RootCommutatorRank := by
  intro G _ _ K I n hI hK hC X _ φ hφ hX v hv hv1
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exact (by omega : n ≤ 1).trans (one_le_rk_commutator hI hK hC hφ hv1)
  · have hS : IsSimpleGroup (X ⧸ Subgroup.center X) := isSimpleGroup_of_isL2Gp hge hX
    have hperf : Group.IsPerfect (X ⧸ Subgroup.center X) :=
      ⟨commutator_eq_top_of_isL2Gp hge hX⟩
    haveI : Finite X := Finite.of_surjective φ hφ.surjective
    have hvc : φ v ∉ Subgroup.center X := bar_involution_not_mem_center hφ hv hv1
    obtain ⟨hvX, F, _, _, _, σ, hσ, hσ1, hrank⟩ :=
      exists_irreducible_section_of_bar hI hK hC hφ hS hperf hv hvc
    have hY : IsL2Gp ↥(commutator X) n := isL2Gp_commutator hge hX (bar_odd_card_center hφ)
    have ht : (⟨φ v, hvX⟩ : ↥(commutator X)) * ⟨φ v, hvX⟩ = 1 := by
      apply Subtype.ext
      change φ v * φ v = 1
      rw [← map_mul]
      have hvv : v * v = 1 := Subtype.ext hv
      rw [hvv, map_one]
    exact (hSt _ n hge hY F σ hσ ⟨φ v, hvX⟩ ht hσ1).trans hrank

end CFSG.LocalAnalysis.WeakClosure81

end
