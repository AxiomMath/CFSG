module

public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12

public section

namespace CFSG.Quasithin.H13.Prop711

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped commutatorElement

theorem not_isPerfect_statedSU_three_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) : ¬ Group.IsPerfect (StatedSU 3 (2 ^ 1) K) := by
  intro hP
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_refl 1, by rw [hK]; norm_num⟩
  have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two h rfl
  have := Fintype.ofFinite (StatedSU 3 (2 ^ 1) K)
  have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  have : Nontrivial (StatedSU 3 (2 ^ 1) K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem not_isPerfect_statedSp_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ¬ Group.IsPerfect (StatedSp 2 K) := by
  intro hP
  set f : StatedSp 2 K →* Equiv.Perm (Fin 6) :=
    CFSG.ComponentClassification.PresentationLocal.omegaPerm.comp
      (CFSG.SeitzReduction.F4Pilot.sp4EquivSympFour hK).toMonoidHom with hf
  have hfs : Function.Surjective f :=
    CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective.comp
      (CFSG.SeitzReduction.F4Pilot.sp4EquivSympFour hK).surjective
  obtain ⟨g, hg⟩ := hfs (Equiv.swap 0 1)
  have h1 : Equiv.Perm.sign (f g) = -1 := by
    rw [hg, Equiv.Perm.sign_swap (by decide)]
  have h2 : (Equiv.Perm.sign.comp f) g = 1 := by
    have hker : commutator (StatedSp 2 K) ≤ (Equiv.Perm.sign.comp f).ker :=
      Abelianization.commutator_subset_ker _
    have hg' : g ∈ commutator (StatedSp 2 K) := by
      rw [hP.commutator_eq_top]
      exact Subgroup.mem_top g
    exact hker hg'
  rw [MonoidHom.comp_apply, h1] at h2
  exact absurd h2 (by decide)

theorem nonempty_mulEquiv_m12
    {X : Type} [Group X]
    {N : Subgroup X} (hN : N.Normal) (hperf : Group.IsPerfect ↥N) (hne : N ≠ ⊥)
    (e : X ≃* MulAut NativeSporadic.M12) : Nonempty (↥N ≃* NativeSporadic.M12) := by
  have hsimp : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have : Finite NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
  have hZ := CFSG.Sporadic.Schreier.m12_center_eq_bot'
  set c : NativeSporadic.M12 →* MulAut NativeSporadic.M12 := MulAut.conj with hc
  have hcinj : Function.Injective c := by
    intro g g' h
    have hcen : g'⁻¹ * g ∈ Subgroup.center NativeSporadic.M12 :=
      Subgroup.mem_center_iff.2 fun x => by
        have hx := congrArg (fun φ : MulAut NativeSporadic.M12 => φ x) h
        simp only [hc, MulAut.conj_apply] at hx
        calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
          _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
          _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    exact (inv_mul_eq_one.mp hcen).symm
  set Inn := c.range with hInn
  have hInnN : Inn.Normal := by
    refine ⟨fun x hx a => ?_⟩
    obtain ⟨g, rfl⟩ := hx
    refine ⟨a g, ?_⟩
    ext y
    simp only [hc, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv]
  have eInn : NativeSporadic.M12 ≃* ↥Inn := MonoidHom.ofInjective hcinj
  have hcardInn : Nat.card ↥Inn = Nat.card NativeSporadic.M12 :=
    (Nat.card_congr eInn.toEquiv).symm
  have hAut := CFSG.Sporadic.Schreier.m12_mulAut_card
  have hpos : 0 < Nat.card NativeSporadic.M12 := Nat.card_pos
  have hidx : Inn.index ≤ 2 := by
    have h1 := Inn.card_mul_index
    rw [hcardInn] at h1
    by_contra h2
    push Not at h2
    have : Nat.card NativeSporadic.M12 * 3 ≤ Nat.card NativeSporadic.M12 * Inn.index :=
      Nat.mul_le_mul_left _ h2
    omega
  have hQcomm : ∀ a b : MulAut NativeSporadic.M12 ⧸ Inn, a * b = b * a := by
    have hQcard : Nat.card (MulAut NativeSporadic.M12 ⧸ Inn) ≤ 2 := by
      rw [← Subgroup.index]
      exact hidx
    intro a b
    rcases Nat.lt_or_ge (Nat.card (MulAut NativeSporadic.M12 ⧸ Inn)) 2 with h | h
    · have : Subsingleton (MulAut NativeSporadic.M12 ⧸ Inn) := by
        rw [← Finite.card_le_one_iff_subsingleton]
        omega
      exact Subsingleton.elim _ _
    · have h2 : Nat.card (MulAut NativeSporadic.M12 ⧸ Inn) = 2 := by omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic (MulAut NativeSporadic.M12 ⧸ Inn) := isCyclic_of_prime_card h2
      exact (IsCyclic.isMulCommutative (α := MulAut NativeSporadic.M12 ⧸ Inn)).is_comm.comm a b
  have hcommInn : commutator (MulAut NativeSporadic.M12) ≤ Inn := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : ((⁅a, b⁆ : MulAut NativeSporadic.M12) : MulAut NativeSporadic.M12 ⧸ Inn) = 1 := by
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hQcomm (a : MulAut NativeSporadic.M12 ⧸ Inn)]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  set N' := N.map e.toMonoidHom with hN'
  have hN'N : N'.Normal := hN.map _ e.surjective
  have hN'perf : ⁅N', N'⁆ = N' := by
    have h1 : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.mp hperf
    rw [hN', ← Subgroup.map_commutator, h1]
  have hN'Inn : N' ≤ Inn := by
    rw [← hN'perf]
    exact (Subgroup.commutator_mono le_top le_top).trans hcommInn
  have hInnS : IsSimpleGroup ↥Inn := eInn.symm.isSimpleGroup
  have hnorm : (N'.subgroupOf Inn).Normal := Subgroup.Normal.subgroupOf hN'N Inn
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exfalso
    apply hne
    have h1 : N' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hN'Inn hx⟩ : ↥Inn) ∈ N'.subgroupOf Inn := hx
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    rw [hN', Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1
    exact h1
  · have heq : N' = Inn := by
      refine le_antisymm hN'Inn fun x hx => ?_
      have : (⟨x, hx⟩ : ↥Inn) ∈ N'.subgroupOf Inn := by rw [h]; exact Subgroup.mem_top _
      exact this
    exact ⟨((N.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr heq)).trans eInn.symm⟩

end CFSG.Quasithin.H13.Prop711
