module

public import CFSG.LocalAnalysis.StandardType.GGKGWeylReflCore
public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.E6ThreeRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem adAct_add_e6 (u : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ZMod 3) :
    adAct Tag.E6 3 u (x + y) = adAct Tag.E6 3 u x + adAct Tag.E6 3 u y := by
  funext i
  simp only [adAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private noncomputable def fixAdd (u : WeylGroup Tag.E6) : AddSubgroup (Fin Tag.E6.rank → ZMod 3) where
  carrier := {x | adAct Tag.E6 3 u x = x}
  add_mem' {x y} hx hy := by
    change adAct Tag.E6 3 u (x + y) = x + y
    rw [adAct_add_e6, show adAct Tag.E6 3 u x = x from hx, show adAct Tag.E6 3 u y = y from hy]
  zero_mem' := by
    change adAct Tag.E6 3 u 0 = 0
    funext i
    simp only [adAct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  neg_mem' {x} hx := by
    change adAct Tag.E6 3 u (-x) = -x
    have h0 : adAct Tag.E6 3 u 0 = 0 := by
      funext i
      simp only [adAct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    have h := adAct_add_e6 u (-x) x
    rw [neg_add_cancel, h0, show adAct Tag.E6 3 u x = x from hx] at h
    exact (neg_eq_of_add_eq_zero_left h.symm).symm

theorem exists_root_of_adAct_refl
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    (u : WeylGroup Tag.E6) (hsq : ∀ x ∈ V, adAct Tag.E6 3 u (adAct Tag.E6 3 u x) = x)
    (hfix : Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧ adAct Tag.E6 3 u x = x} * 3 =
      Nat.card V) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧
      ∀ x ∈ V, adAct Tag.E6 3 u x = ExcSplitRootGen.excRefl (p := 3) γ x := by
  classical
  have hH : (∀ x ∈ NoOffRest.hypE6, adAct Tag.E6 3 u (adAct Tag.E6 3 u x) = x) ∧
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ NoOffRest.hypE6 ∧
        adAct Tag.E6 3 u x = x} * 3 = 3 ^ 5 := by
    rcases hV with rfl | rfl
    · refine ⟨fun x _ => hsq x (Set.mem_univ x), ?_⟩
      have hcardF : Nat.card (fixAdd u) * 3 = 3 ^ 6 := by
        have h1 : Nat.card (fixAdd u) = Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
            x ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) ∧ adAct Tag.E6 3 u x = x} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun x =>
            ⟨fun h => ⟨Set.mem_univ x, h⟩, fun h => h.2⟩)
        have h2 : Nat.card (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) = 3 ^ 6 := by
          rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
            Fintype.card_fin]
          rfl
        rw [h1, hfix, h2]
      have hindexF : (fixAdd u).index = 3 := by
        have h := (fixAdd u).index_mul_card
        rw [Nat.card_eq_fintype_card (α := Fin Tag.E6.rank → ZMod 3), Fintype.card_fun,
          ZMod.card, Fintype.card_fin] at h
        have hpos : 0 < Nat.card (fixAdd u) := Nat.card_pos
        have : (fixAdd u).index * Nat.card (fixAdd u) = 3 * Nat.card (fixAdd u) := by
          rw [h, mul_comm 3, hcardF]
          rfl
        exact Nat.eq_of_mul_eq_mul_right hpos this
      have hrel : (fixAdd u).relIndex NoOffRest.hypE6 ∣ 3 := by
        have h := AddSubgroup.relIndex_dvd_index_of_normal (fixAdd u) NoOffRest.hypE6
        rwa [hindexF] at h
      have hrelmul := (fixAdd u).relIndex_mul_card NoOffRest.hypE6
      have hcardI : Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ NoOffRest.hypE6 ∧
          adAct Tag.E6 3 u x = x} = Nat.card ↥(fixAdd u ⊓ NoOffRest.hypE6) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun x =>
          ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩)
      rcases (Nat.dvd_prime Nat.prime_three).1 hrel with h1 | h3
      ·
        exfalso
        have hle : NoOffRest.hypE6 ≤ fixAdd u := AddSubgroup.relIndex_eq_one.mp h1
        have hu1 : u = 1 :=
          TableBExc.E6Three.eq_one_of_adAct_eq_on_hypE6 fun x hx => hle hx
        have hall : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
            x ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) ∧ adAct Tag.E6 3 u x = x} =
            Nat.card (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) :=
          Nat.card_congr (Equiv.subtypeEquivRight fun x =>
            ⟨fun _ => Set.mem_univ x, fun _ => ⟨Set.mem_univ x, by rw [hu1, adAct_one]⟩⟩)
        rw [hall] at hfix
        have hpos : 0 < Nat.card (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) := Nat.card_pos
        omega
      · rw [hcardI]
        rw [h3, NoOffRest.card_hypE6] at hrelmul
        rw [inf_comm] at hrelmul ⊢
        omega
    · exact ⟨hsq, hfix.trans NoOffRest.card_hypE6⟩
  obtain ⟨γ, hγ, hγu⟩ := KGL.exists_root_of_isRefl u hH.1 hH.2
  have hu : u = rootReflection γ := by
    have h1 : u * (rootReflection γ)⁻¹ = 1 := by
      refine TableBExc.E6Three.eq_one_of_adAct_eq_on_hypE6 fun x hx => ?_
      rw [adAct_mul, rootReflection_inv hγ]
      have hx' : adAct Tag.E6 3 (rootReflection γ) x ∈ NoOffRest.hypE6 :=
        NoOffRest.adAct_mem_hypE6 _ hx
      rw [hγu _ hx', KGL.adAct_rootReflection_eq_rootRefl hγ, KGL.rootRefl_rootRefl hγ]
    exact mul_inv_eq_one.mp h1
  refine ⟨γ, hγ, fun x _ => ?_⟩
  rw [hu]
  rfl


theorem exists_root_of_isReflection_frame
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)} (hκ : Function.Injective κ)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    (hinner : ∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u : WeylGroup Tag.E6, ∀ a b : A,
        (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
          Multiplicative.toAdd (κ b) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a)))
    {φ : MulAut ↥A} (hφ : φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφr : GGIsReflection 3 φ) :
    ∃ i : {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ}, ∀ a : A,
      Multiplicative.toAdd (κ (φ a)) =
        ExcSplitRootGen.excRefl (p := 3) i.1 (Multiplicative.toAdd (κ a)) := by
  classical
  obtain ⟨g', hg'H, hg'N, hg'⟩ := mem_ggAutomizer_iff.1 hφ
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 hg'H
  obtain ⟨u, hu⟩ := hinner m hg'N
  have hact : ∀ a : A, Multiplicative.toAdd (κ (φ a)) =
      adAct Tag.E6 3 u (Multiplicative.toAdd (κ a)) := fun a => hu a (φ a) (hg' a)
  have hmemV : ∀ a : A, Multiplicative.toAdd (κ a) ∈ V := fun a =>
    (hVmem _).1 (MonoidHom.mem_range.mpr ⟨a, by rw [ofAdd_toAdd]⟩)
  have hsurjV : ∀ x ∈ V, ∃ a : A, Multiplicative.toAdd (κ a) = x := by
    intro x hx
    obtain ⟨a, ha⟩ := (hVmem x).2 hx
    exact ⟨a, (congrArg Multiplicative.toAdd ha).trans (toAdd_ofAdd x)⟩
  have hφφ : ∀ a : A, φ (φ a) = a := by
    intro a
    have h := congrArg (fun f : MulAut ↥A => f a) hφr.1
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hsq : ∀ x ∈ V, adAct Tag.E6 3 u (adAct Tag.E6 3 u x) = x := by
    intro x hx
    obtain ⟨a, rfl⟩ := hsurjV x hx
    rw [← hact, ← hact, hφφ]
  let e : A ≃ ↥V :=
    Equiv.ofBijective (fun a : A => (⟨Multiplicative.toAdd (κ a), hmemV a⟩ : ↥V))
      ⟨fun a a' h => hκ (by
          simpa only [ofAdd_toAdd] using
            congrArg Multiplicative.ofAdd (Subtype.ext_iff.mp h)),
        fun b => by
          obtain ⟨a, ha⟩ := hsurjV b.1 b.2
          exact ⟨a, Subtype.ext ha⟩⟩
  have hfixA : Nat.card {a : A // φ a = a} =
      Nat.card {x : ↥V // adAct Tag.E6 3 u (x : Fin Tag.E6.rank → ZMod 3) = x} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e fun a => ?_)
    change φ a = a ↔ adAct Tag.E6 3 u (Multiplicative.toAdd (κ a)) = Multiplicative.toAdd (κ a)
    rw [← hact]
    constructor
    · intro h
      rw [h]
    · intro h
      exact hκ (Multiplicative.toAdd.injective h)
  have hfixV : Nat.card {x : ↥V // adAct Tag.E6 3 u (x : Fin Tag.E6.rank → ZMod 3) = x} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧ adAct Tag.E6 3 u x = x} :=
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ V)
      (fun x => adAct Tag.E6 3 u x = x))
  have hfix : Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧ adAct Tag.E6 3 u x = x} * 3 =
      Nat.card V := by
    rw [← hfixV, ← hfixA, ← Nat.card_congr e]
    exact hφr.2
  obtain ⟨γ, hγ, hγu⟩ := exists_root_of_adAct_refl hV u hsq hfix
  exact ⟨⟨γ, hγ⟩, fun a => (hact a).trans (hγu _ (hmemV a))⟩

end CFSG.StandardType.E6ThreeRootGen

end
