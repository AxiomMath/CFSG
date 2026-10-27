module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Setting
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveU3Aut
public import CFSG.CGT.T75E.RootBender
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

theorem Setting.card_le_of_isElemAbelian (h : Setting C n)
    {A : Subgroup Q} (hA : CFSG.Open.IsElemAbelian 2 A) : Nat.card A ≤ 2 ^ (n + 1) := by
  have hAZ : A ⊓ (center ↥C).map C.subtype = ⊥ := h.inf_center_map_eq_bot hA.isPGroup
  have hker : (h.act.subgroupMap A).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff, injective_iff_map_eq_one]
    intro x hx
    have hx' : h.act (x : Q) = 1 := by
      have := congrArg Subtype.val hx
      simpa using this
    have hxZ : (x : Q) ∈ (center ↥C).map C.subtype :=
      h.mem_center_of_act_eq_one hx'
    exact Subtype.ext (Subgroup.mem_bot.mp (hAZ ▸ ⟨x.2, hxZ⟩))
  have hcard : Nat.card (A.map h.act) = Nat.card A := by
    have hinj : Function.Injective (h.act.subgroupMap A) := (MonoidHom.ker_eq_bot_iff _).mp hker
    exact (Nat.card_congr (MulEquiv.ofBijective (h.act.subgroupMap A)
      ⟨hinj, h.act.subgroupMap_surjective A⟩).toEquiv).symm
  calc Nat.card A = Nat.card (A.map h.act) := hcard.symm
    _ ≤ 2 ^ (n + 1) :=
      CFSG.LocalAnalysis.WeakClosure81.card_elemAbelian_two_aut_PSU3 h.isU3 _
        (hA.map h.act)

theorem Setting.card_le_of_le (h : Setting C n) {A : Subgroup Q} (hAC : A ≤ C)
    (hA : CFSG.Open.IsElemAbelian 2 A) : Nat.card A ≤ 2 ^ n := by
  have hAZ : A ⊓ (center ↥C).map C.subtype = ⊥ := h.inf_center_map_eq_bot hA.isPGroup
  let φ : A →* (↥C ⧸ center ↥C) :=
    (QuotientGroup.mk' (center ↥C)).comp (Subgroup.inclusion hAC)
  have hker : φ.ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff, injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : Q) ∈ (center ↥C).map C.subtype := by
      have hx' : (QuotientGroup.mk' (center ↥C)) (Subgroup.inclusion hAC x) = 1 := by
        simpa only [φ, MonoidHom.comp_apply] using hx
      have hmem : Subgroup.inclusion hAC x ∈ center ↥C :=
        (QuotientGroup.eq_one_iff _).mp hx'
      exact ⟨Subgroup.inclusion hAC x, hmem, rfl⟩
    exact Subtype.ext (Subgroup.mem_bot.mp (hAZ ▸ ⟨x.2, hxZ⟩))
  have hcard : Nat.card φ.range = Nat.card A := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even h.two_le h.isU3
  let e' : (↥C ⧸ center ↥C) ≃* CFSG.Theory.Comparator.PSU3Model n :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n))
  let ψ : A →* CFSG.Theory.Comparator.PSU3Model n := e'.toMonoidHom.comp φ
  have hcardψ : Nat.card ψ.range = Nat.card A := by
    rw [show ψ = e'.toMonoidHom.comp φ from rfl, MonoidHom.range_comp,
      Subgroup.card_map_of_injective e'.injective, hcard]
  have hsq : ∀ x ∈ ψ.range, x * x = 1 := by
    rintro x ⟨a, rfl⟩
    rw [← map_mul, ← pow_two,
      show a ^ 2 = 1 from Subtype.ext (by simpa using hA.2 (a : Q) a.2), map_one]
  calc Nat.card A = Nat.card ψ.range := hcardψ.symm
    _ ≤ 2 ^ n := CFSG.CGT.T75E.card_le_two_pow_of_sq_eq_one h.two_le ψ.range hsq

theorem Setting.relIndex_le_two (h : Setting C n)
    {A : Subgroup Q} (hA : CFSG.Open.IsElemAbelian 2 A) : C.relIndex A ≤ 2 := by
  let Y := ↥C ⧸ center ↥C
  let Outer := CFSG.ComponentClassification.OuterAutomorphisms.Outer Y
  let g : Q →* Outer :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Y)).comp h.act
  let ψ : A →* Outer := g.comp A.subtype
  have hker : ψ.ker = C.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Y))
      (h.act (a : Q)) = 1 ↔ (a : Q) ∈ C
    constructor
    · intro ha
      have hmem : h.act (a : Q) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y :=
        (QuotientGroup.eq_one_iff _).mp ha
      by_contra haC
      exact h.act_not_mem_range haC hmem
    · intro haC
      exact (QuotientGroup.eq_one_iff _).mpr
        ⟨QuotientGroup.mk ⟨(a : Q), haC⟩, (h.act_coe ⟨(a : Q), haC⟩).symm⟩
  have hcard : Nat.card (A ⧸ C.subgroupOf A) = Nat.card ψ.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hsq : ∀ x ∈ ψ.range, x * x = 1 := by
    rintro x ⟨a, rfl⟩
    rw [← map_mul, ← pow_two,
      show a ^ 2 = 1 from Subtype.ext (by simpa using hA.2 (a : Q) a.2), map_one]
  have hP : IsPGroup 2 ψ.range := fun y => ⟨1, Subtype.ext (by simpa [pow_two] using hsq y y.2)⟩
  obtain ⟨T, hAT⟩ := hP.exists_le_sylow
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even h.two_le h.isU3
  have hB : CFSG.GH74.Uniqueness.Bender.BenderType Y n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    CFSG.GH74.Uniqueness.Bender.BenderType.unitary n h.two_le
      (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n)))
  have hcyc : IsCyclic ↥(T : Subgroup Outer) := hB.isCyclic_sylow_outer T
  haveI : IsCyclic ↥(T : Subgroup Outer) := hcyc
  have hcycψ : IsCyclic ψ.range := Subgroup.isCyclic_of_le hAT
  haveI : IsCyclic ψ.range := hcycψ
  have hE : CFSG.Open.IsElemAbelian 2 ψ.range :=
    ⟨IsCyclic.isMulCommutative, fun x hx => by simpa [pow_two] using hsq x hx⟩
  have hle2 : Nat.card ψ.range ≤ 2 :=
    CFSG.RankThree.SubgroupLists.card_le_of_pow_eq_one_of_isCyclic (n := 2)
      (fun x => Subtype.ext (by simpa using hE.2 x x.2))
  calc C.relIndex A = Nat.card (A ⧸ C.subgroupOf A) := by
        rw [Subgroup.relIndex, Subgroup.index_eq_card]
    _ = Nat.card ψ.range := hcard
    _ ≤ 2 := hle2

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
