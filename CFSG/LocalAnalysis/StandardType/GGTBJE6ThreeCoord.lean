module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Roots
public import CFSG.LocalAnalysis.StandardType.GGTBJReflPlain
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenRefl
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenCoord
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6Three_noncomm_aux
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} (i : KernelComponent χ)
    (H' : AddSubgroup (Fin Tag.E6.rank → ZMod 3))
    (hv : ∀ γ ∈ componentRoots χ i, ggTBJTwE6Vec 3 γ ∈ H')
    {V : Set (Fin Tag.E6.rank → ZMod 3)} (hH : (H' : Set (Fin Tag.E6.rank → ZMod 3)) = V)
    (hcard : 3 ^ 2 * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ∀ γ ∈ componentRoots χ i, ∑ j, (γ j : ZMod 3) * x j = 0} ≤ Nat.card V) :
    ∃ γ₁ ∈ componentRoots χ i, ∃ γ₂ ∈ componentRoots χ i, ∃ w ∈ V,
      ExcSplitRootGen.excRefl (p := 3) γ₁ (ExcSplitRootGen.excRefl (p := 3) γ₂ w) ≠
        ExcSplitRootGen.excRefl (p := 3) γ₂ (ExcSplitRootGen.excRefl (p := 3) γ₁ w) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : (3 : ℕ).Prime := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  let W : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3) :=
    AddSubgroup.toZModSubmodule (M := Fin Tag.E6.rank → ZMod 3) 3 H'
  let ι := {β : Fin Tag.E6.rank → ℤ // β ∈ componentRoots χ i}
  haveI : Nonempty ι := by
    obtain ⟨a, ha⟩ := Quotient.exists_rep i
    exact ⟨⟨a.1, ⟨a.2, ha⟩⟩⟩
  have hroot : ∀ a : ι, IsRoot Tag.E6 a.1 := fun a => isRoot_of_mem_componentRoots a.2
  have hmemW : ∀ a : ι, ggTBJTwE6Vec 3 a.1 ∈ W := fun a =>
    (AddSubgroup.mem_toZModSubmodule (M := Fin Tag.E6.rank → ZMod 3) 3).2 (hv a.1 a.2)
  let f : ι → ↥W → ZMod 3 := fun a w => ggTBJTwE6Fun 3 a.1 w.1
  let v : ι → ↥W := fun a => ⟨ggTBJTwE6Vec 3 a.1, hmemW a⟩
  have hfv : ∀ a, f a (v a) = 2 := by
    intro a
    simpa only [f, v] using ggTBJTwE6_fun_vec_self 3 (hroot a)
  have hadd : ∀ a (x y : ↥W), f a (x + y) = f a x + f a y := by
    intro a x y
    simp only [f, ggTBJTwE6Fun, Pi.add_apply, mul_add, Finset.sum_add_distrib,
      Submodule.coe_add]
  have hsmul : ∀ a (c : ZMod 3) (x : ↥W), f a (c • x) = c * f a x := by
    intro a c x
    simp only [f, ggTBJTwE6Fun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      Submodule.coe_smul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hconn : ∀ S : Set ι, S.Nonempty →
      (∀ a b, (f a (v b) ≠ 0 ∨ f b (v a) ≠ 0) → (a ∈ S ↔ b ∈ S)) → S = Set.univ := by
    intro S hSne hSclosed
    let S' : Set (Fin Tag.E6.rank → ℤ) := (fun a : ι => (a : Fin Tag.E6.rank → ℤ)) '' S
    have hS'sub : S' ⊆ componentRoots χ i := by
      rintro β ⟨a, -, rfl⟩
      exact a.2
    have hS'ne : S'.Nonempty := by
      obtain ⟨a, ha⟩ := hSne
      exact ⟨(a : Fin Tag.E6.rank → ℤ), ⟨a, ha, rfl⟩⟩
    have hS'closed : ∀ β ∈ componentRoots χ i, ∀ γ ∈ componentRoots χ i,
        ((corootPair (τ := Tag.E6) γ β : ZMod 3) ≠ 0 ∨
          (corootPair (τ := Tag.E6) β γ : ZMod 3) ≠ 0) →
        (β ∈ S' ↔ γ ∈ S') := by
      intro β hβ γ hγ hpr
      have key : ∀ (δ : Fin Tag.E6.rank → ℤ)
          (hδ : δ ∈ componentRoots χ i), (δ ∈ S' ↔ (⟨δ, hδ⟩ : ι) ∈ S) := by
        intro δ hδ
        constructor
        · rintro ⟨a, ha, hae⟩
          have hEq : a = ⟨δ, hδ⟩ := Subtype.ext hae
          rwa [hEq] at ha
        · intro h
          exact ⟨⟨δ, hδ⟩, h, rfl⟩
      rw [key β hβ, key γ hγ]
      refine hSclosed ⟨β, hβ⟩ ⟨γ, hγ⟩ ?_
      have e1 : f ⟨β, hβ⟩ (v ⟨γ, hγ⟩) = (corootPair (τ := Tag.E6) γ β : ZMod 3) := by
        simpa only [f, v] using ggTBJTwE6_fun_vec 3 (isRoot_of_mem_componentRoots hγ)
      have e2 : f ⟨γ, hγ⟩ (v ⟨β, hβ⟩) = (corootPair (τ := Tag.E6) β γ : ZMod 3) := by
        simpa only [f, v] using ggTBJTwE6_fun_vec 3 (isRoot_of_mem_componentRoots hβ)
      rw [e1, e2]
      exact hpr
    have hSuniv := ggTBJ_e6_connected hp hp2 i S' hS'sub hS'ne hS'closed
    refine Set.eq_univ_of_forall fun a => ?_
    have ha : (a : Fin Tag.E6.rank → ℤ) ∈ S' := by
      rw [hSuniv]
      exact a.2
    obtain ⟨b, hb, hba⟩ := ha
    have hEq : b = a := Subtype.ext hba
    rwa [hEq] at hb
  have hcardW : 3 ^ 2 * Nat.card {w : ↥W // ∀ a, f a w = 0} ≤ Nat.card ↥W := by
    have h1 : Nat.card {w : ↥W // ∀ a, f a w = 0} =
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ (H' : Set (Fin Tag.E6.rank → ZMod 3)) ∧
          ∀ γ ∈ componentRoots χ i, ggTBJTwE6Fun 3 γ x = 0} := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun w => ⟨w.1.1,
            (AddSubgroup.mem_toZModSubmodule
              (M := Fin Tag.E6.rank → ZMod 3) 3).1 w.1.2,
            fun γ hγ => by simpa only [f] using w.2 ⟨γ, hγ⟩⟩
          invFun := fun x => ⟨⟨x.1,
            (AddSubgroup.mem_toZModSubmodule
              (M := Fin Tag.E6.rank → ZMod 3) 3).2 x.2.1⟩,
            fun a => by simpa only [f, ggTBJTwE6Fun] using x.2.2 a.1 a.2⟩
          left_inv := fun w => Subtype.ext (Subtype.ext rfl)
          right_inv := fun x => Subtype.ext rfl }
    have h2 : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          x ∈ (H' : Set (Fin Tag.E6.rank → ZMod 3)) ∧
          ∀ γ ∈ componentRoots χ i, ggTBJTwE6Fun 3 γ x = 0} =
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
          ∀ γ ∈ componentRoots χ i, ∑ j, (γ j : ZMod 3) * x j = 0} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      simp only [hH, ggTBJTwE6Fun]
    calc 3 ^ 2 * Nat.card {w : ↥W // ∀ a, f a w = 0}
        = 3 ^ 2 * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
            ∀ γ ∈ componentRoots χ i, ∑ j, (γ j : ZMod 3) * x j = 0} := by rw [h1, h2]
      _ ≤ Nat.card V := hcard
      _ = Nat.card ↥W := by
          rw [← hH]
          exact Nat.card_congr
            (Equiv.Set.congr (AddSubgroup.coe_toZModSubmodule
              (M := Fin Tag.E6.rank → ZMod 3) (n := 3) H').symm)
  obtain ⟨a₁, a₂, w, hw⟩ :=
    exists_not_commute_reflection_plain (p := 3) hp2 f v hadd hsmul hfv hconn hcardW
  have hrefl : ∀ (a : ι) (y : Fin Tag.E6.rank → ZMod 3),
      ExcSplitRootGen.excRefl (p := 3) a.1 y =
        y - ggTBJTwE6Fun 3 a.1 y • ggTBJTwE6Vec 3 a.1 :=
    fun a y => ggTBJTwE6_excRefl_eq (p := 3) (hroot a) y
  have hwR : ExcSplitRootGen.excRefl (p := 3) a₁.1
        (ExcSplitRootGen.excRefl (p := 3) a₂.1 (w : Fin Tag.E6.rank → ZMod 3)) ≠
      ExcSplitRootGen.excRefl (p := 3) a₂.1
        (ExcSplitRootGen.excRefl (p := 3) a₁.1 (w : Fin Tag.E6.rank → ZMod 3)) := by
    intro h
    refine hw (Subtype.ext ?_)
    simpa only [f, v, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_add,
      hrefl a₂ (w : Fin Tag.E6.rank → ZMod 3), hrefl a₁ _,
      hrefl a₁ (w : Fin Tag.E6.rank → ZMod 3), hrefl a₂ _] using h
  exact ⟨a₁.1, a₁.2, a₂.1, a₂.2, (w : Fin Tag.E6.rank → ZMod 3),
    hH ▸ (AddSubgroup.mem_toZModSubmodule (M := Fin Tag.E6.rank → ZMod 3) 3).1 w.2, hwR⟩

theorem e6Three_exists_noncomm_pair
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M}
    (i : KernelComponent χ)
    (hcard : 3 ^ 2 * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ∀ γ ∈ componentRoots χ i, ∑ j, (γ j : ZMod 3) * x j = 0} ≤ Nat.card V) :
    ∃ γ₁ ∈ componentRoots χ i, ∃ γ₂ ∈ componentRoots χ i, ∃ w ∈ V,
      ExcSplitRootGen.excRefl (p := 3) γ₁ (ExcSplitRootGen.excRefl (p := 3) γ₂ w) ≠
        ExcSplitRootGen.excRefl (p := 3) γ₂ (ExcSplitRootGen.excRefl (p := 3) γ₁ w) := by
  rcases hV with rfl | rfl
  · have hv : ∀ γ ∈ componentRoots χ i, ggTBJTwE6Vec 3 γ ∈ (⊤ : AddSubgroup _) :=
      fun γ _ => AddSubgroup.mem_top _
    refine e6Three_noncomm_aux (V := Set.univ) i ⊤ hv ?_ ?_
    · simp
    · simpa only [ggTBJTwE6Fun] using hcard
  · have hv : ∀ γ ∈ componentRoots χ i, ggTBJTwE6Vec 3 γ ∈ NoOffRest.hypE6 := by
      intro γ hγ
      have hγr : IsRoot Tag.E6 γ := isRoot_of_mem_componentRoots hγ
      have hcalc : ExcSplitRootGen.excRefl (p := 3) γ (ggTBJTwE6Vec 3 γ) -
          ggTBJTwE6Vec 3 γ = ggTBJTwE6Vec 3 γ := by
        rw [ggTBJTwE6_excRefl_eq (p := 3) hγr, ggTBJTwE6_fun_vec_self 3 hγr]
        have h2 : (2 : ZMod 3) • ggTBJTwE6Vec 3 γ = -ggTBJTwE6Vec 3 γ := by
          rw [show (2 : ZMod 3) = -1 by decide]
          exact neg_one_smul (M := Fin Tag.E6.rank → ZMod 3) (ZMod 3) _
        rw [h2]
        abel
      have h := TwE6ThreeRootGen.excRefl_sub_mem_hypE6 γ (ggTBJTwE6Vec 3 γ)
      rwa [hcalc] at h
    refine e6Three_noncomm_aux (V := (NoOffRest.hypE6 : Set _)) i NoOffRest.hypE6 hv rfl ?_
    simpa only [ggTBJTwE6Fun] using hcard

theorem e6Three_isReflection_of_coord
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)} (hκinj : Function.Injective κ)
    {V : Set (Fin Tag.E6.rank → ZMod 3)} (hκV : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) {φ : MulAut ↥A}
    (hφ : ∀ a, Multiplicative.toAdd (κ (φ a)) =
      ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a))) :
    GGIsReflection 3 φ := by
  classical
  have h2 : φ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro a
    apply hκinj
    apply Multiplicative.toAdd.injective
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply,
      hφ (φ a), hφ a, ExcSplitRootGen.excRefl_excRefl hγ]
  refine ⟨h2, ?_⟩
  let toX : ↥A → {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V} :=
    fun b => ⟨Multiplicative.toAdd (κ b), (hκV _).1 ⟨b, rfl⟩⟩
  have htoXinj : Function.Injective toX := by
    intro b b' hbb'
    exact hκinj (Multiplicative.toAdd.injective (congrArg Subtype.val hbb'))
  have htoXsurj : Function.Surjective toX := by
    intro x
    obtain ⟨b, hb⟩ := (hκV x.1).2 x.2
    refine ⟨b, Subtype.ext ?_⟩
    show Multiplicative.toAdd (κ b) = x.1
    rw [hb, toAdd_ofAdd]
  let e : ↥A ≃ {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V} :=
    Equiv.ofBijective toX ⟨htoXinj, htoXsurj⟩
  have he : ∀ b, (e b).1 = Multiplicative.toAdd (κ b) := fun b => rfl
  have hfix : {b : ↥A // φ b = b} ≃
      {y : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V} //
        ExcSplitRootGen.excRefl (p := 3) γ y.1 = y.1} := by
    refine Equiv.subtypeEquiv e fun b => ?_
    constructor
    · intro hb
      rw [he, ← hφ b, hb]
    · intro hb
      apply hκinj
      apply Multiplicative.toAdd.injective
      rw [hφ b, ← he]
      exact hb
  have hfixcard : Nat.card {b : ↥A // φ b = b} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ExcSplitRootGen.excRefl (p := 3) γ x = x} := by
    rw [Nat.card_congr hfix]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ V)
      (fun x => ExcSplitRootGen.excRefl (p := 3) γ x = x))
  have hAcard : Nat.card ↥A = Nat.card V := Nat.card_congr e
  rw [hfixcard, hAcard]
  exact TwE6ThreeRootGen.card_fix_excRefl_mul_three hV hγ

end CFSG.StandardType

end
