module

public import CFSG.StronglyEmbedded.BenderCentre
public import CFSG.RankThree.GF2n.Stroth80.Sec93OutBender
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

private theorem isElemAbelian_map_center {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card (Subgroup.center X))) (E : Subgroup X) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map (QuotientGroup.mk' (Subgroup.center X))) ∧
      Nat.card (E.map (QuotientGroup.mk' (Subgroup.center X))) = Nat.card E := by
  set π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hπ
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : X) ∈ Subgroup.center X := by
      have := hx
      simpa [hπ, QuotientGroup.eq_one_iff] using this
    have h1 : orderOf (x : X) ∣ 2 := orderOf_dvd_of_pow_eq_one (hE.2 x x.2)
    have h2 : orderOf (x : X) ∣ Nat.card (Subgroup.center X) := by
      have := orderOf_dvd_natCard (⟨x, hxZ⟩ : Subgroup.center X)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center X)) :=
      Nat.coprime_two_left.mpr hodd
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff] at this
    exact Subtype.ext this
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    show π a * π b = π b * π a
    rw [← map_mul, ← map_mul]
    exact congrArg (fun z : E => π z) this
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    simp [hE.2 a ha]
  · have e : E ≃* E.map π :=
      (MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))
    exact (Nat.card_congr e.toEquiv).symm

private theorem card_le_two_pow_of_isElemAbelian_psu3 {K : Type} [Group K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (e : K ≃* ↥(CFSG.Theory.Comparator.PSU3Model n)) (E : Subgroup K)
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ n := by
  have hK : CFSG.BenderSuzuki.IsBenderGroup K := .isPSU3 n hn e
  obtain ⟨S, hES⟩ := CFSG.StronglyEmbedded.BenderCentre.exists_le_sylowCenter hK hE
  calc Nat.card E
      ≤ Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
          (S : Subgroup K)) := Subgroup.card_le_of_le hES
    _ = 2 ^ n := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_psu3 hn e S

private theorem nonempty_mulEquiv_psu3Model {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSUGp X 3 n) : Nonempty (X ≃* ↥(CFSG.Theory.Comparator.PSU3Model n)) := by
  have hcl : CFSG.Open.StatedClassicalModel X .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨e⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hn hcl
  exact ⟨e.trans (MulEquiv.subgroupCongr
    (show CFSG.Open.PSU3 2 n = CFSG.Theory.Comparator.PSU3Model n from rfl))⟩

theorem kFacts_rank_U3 :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n →
      IsPSUGp (X ⧸ Subgroup.center X) 3 n → Odd (Nat.card (Subgroup.center X)) →
        ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ n := by
  intro X _ _ n hn hX hodd E hE
  obtain ⟨e⟩ := nonempty_mulEquiv_psu3Model hn hX
  obtain ⟨hE', hcard⟩ := isElemAbelian_map_center hodd E hE
  rw [← hcard]
  exact card_le_two_pow_of_isElemAbelian_psu3 hn e _ hE'

private theorem exists_normal_odd_cyclic_quotient_outer {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (h : IsPSUGp X 3 n) :
    ∃ (Dd : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) (_ : Dd.Normal),
      Odd (Nat.card Dd) ∧
        IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer X ⧸ Dd) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psu3Model hn h
  have hB := CFSG.GH74.Uniqueness.Bender.BenderType.unitary n hn e
  obtain ⟨Dd, hDn, -, hd, hq, -⟩ := hB.outer_unitary
  refine ⟨Dd, hDn, ?_, hq⟩
  rw [hd]
  exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)

private theorem isElemAbelian_map_outer {X : Type} [Group X] (E : Subgroup (MulAut X))
    (hE : IsElemAbelian 2 E) (hEI : E ⊓ (MulAut.conj : X →* MulAut X).range = ⊥) :
    ∃ A : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer X),
      IsElemAbelian 2 A ∧ Nat.card A = Nat.card E := by
  set π : MulAut X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer X :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X) with hπ
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxI : (x : MulAut X) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
      have := hx
      simpa [hπ, QuotientGroup.eq_one_iff] using this
    have : (x : MulAut X) ∈ E ⊓ (MulAut.conj : X →* MulAut X).range := ⟨x.2, hxI⟩
    rw [hEI] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  refine ⟨E.map π, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    show π a * π b = π b * π a
    rw [← map_mul, ← map_mul]
    exact congrArg (fun z : E => π z) this
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    simp [hE.2 a ha]
  · have e : E ≃* E.map π :=
      (MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))
    exact (Nat.card_congr e.toEquiv).symm

theorem kFacts_rank_out_U3 :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsPSUGp X 3 n →
      ∀ E : Subgroup (MulAut X), IsElemAbelian 2 E →
        E ⊓ (MulAut.conj : X →* MulAut X).range = ⊥ → Nat.card E ≤ 2 := by
  intro X _ _ n hn hX E hE hEI
  haveI : Finite (MulAut X) := Finite.of_injective (fun f : MulAut X => (f : X → X))
    DFunLike.coe_injective
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := inferInstance
  obtain ⟨Dd, hDn, hodd, hcyc⟩ := exists_normal_odd_cyclic_quotient_outer hn hX
  obtain ⟨A, hA, hcard⟩ := isElemAbelian_map_outer E hE hEI
  have hsyl := CFSG.GH74.Uniqueness.Bender.isCyclic_sylow_of_quotient Dd hodd hcyc
  rw [← hcard]
  exact CFSG.RankThree.GF2n.Stroth80.card_le_two_of_isElemAbelian_of_cyclic_sylow hsyl A hA

end CFSG.LocalAnalysis.WeakClosure81
