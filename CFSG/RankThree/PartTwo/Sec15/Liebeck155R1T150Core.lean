module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Defs
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def GoodAllFor (J : Type) [Group J] {S : Type} [Group S] (C : Subgroup S) : Prop :=
  ∀ P : Subgroup S, P ≤ C → (P.subgroupOf C).IsSubnormal → Group.IsPerfect P →
    ∀ (N : Subgroup P) [N.Normal], IsEmpty (P ⧸ N ≃* J)

@[expose] def NoCfgAll (J : Type) [Group J] (S : Type) [Group S] : Prop :=
  ∀ σ : MulAut S, σ ^ 3 = 1 → σ ≠ 1 → GoodAllFor J (Sec4.autFix σ)

@[expose] def RowAllOfK150 (J X : Type) [Group J] [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → NoCfgAll J S

theorem GoodAllFor.goodFor {J : Type} [Group J] {S : Type} [Group S] {C : Subgroup S}
    (h : GoodAllFor J C) : GoodFor J C :=
  fun P hPC hsn hP _ N _ => h P hPC hsn hP N

theorem NoCfgAll.noCfgFor {J : Type} [Group J] {S : Type} [Group S] (h : NoCfgAll J S) :
    NoCfgFor J S :=
  fun σ h3 h1 => (h σ h3 h1).goodFor

theorem RowAllOfK150.rowOfK150 {J X : Type} [Group J] [Group X] (h : RowAllOfK150 J X) :
    RowOfK150 J X :=
  fun S _ _ hs hna e => (h S hs hna e).noCfgFor

section Transport

variable {J : Type} [Group J] {S G' : Type} [Group S] [Group G']

theorem GoodAllFor.of_map {C : Subgroup S} (f : S →* G') (hf : Function.Injective f)
    (h : GoodAllFor J (C.map f)) : GoodAllFor J C := by
  intro P hPC hPs hPp N hN
  have := hPp
  let eP : P ≃* P.map f := P.equivMapOfInjective f hf
  have : (N.map (eP : P →* P.map f)).Normal := hN.map _ eP.surjective
  have : Group.IsPerfect (P.map f) := Group.IsPerfect.map f
  let eC : C ≃* C.map f := C.equivMapOfInjective f hf
  have heC : ∀ x : C, ((eC x : C.map f) : G') = f x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply C f hf x
  have hsurj : Function.Surjective (eC : C →* C.map f) := eC.surjective
  have hmap := hPs.map hsurj
  have heq : (P.subgroupOf C).map (eC : C →* C.map f) = (P.map f).subgroupOf (C.map f) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxP, hxy⟩
      refine ⟨x, hxP, ?_⟩
      rw [← heC x, hxy]
    · rintro ⟨x, hxP, rfl⟩
      refine ⟨⟨x, hPC hxP⟩, hxP, Subtype.ext ?_⟩
      rw [heC]
  rw [heq] at hmap
  exact ⟨fun e => (h (P.map f) (Subgroup.map_mono hPC) hmap inferInstance
    (N.map (eP : P →* P.map f))).false ((QuotientGroup.congr N _ eP rfl).symm.trans e)⟩

theorem GoodAllFor.of_mulEquiv_centralizer (e : S ≃* G') {s : S}
    (h : GoodAllFor J (Subgroup.centralizer ({e s} : Set G'))) :
    GoodAllFor J (Subgroup.centralizer ({s} : Set S)) := by
  refine GoodAllFor.of_map e.toMonoidHom e.injective ?_
  have hm := RonanK429H.map_centralizer_singleton e.toMonoidHom e.injective s
  rw [MonoidHom.range_eq_top_of_surjective _ e.surjective, inf_top_eq] at hm
  rw [hm]
  exact h

end Transport

section Inner

variable {J : Type} [Group J] {S G' : Type} [Group S] [Group G']

theorem k150_noCfgAll_of_inner (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hgood : ∀ s : S, orderOf s = 3 → GoodAllFor J (Subgroup.centralizer ({s} : Set S))) :
    NoCfgAll J S := by
  intro σ h3 h1
  obtain ⟨s, rfl⟩ := cubeInner_of_not_three_dvd_card_outer hout σ h3
  have hs3 : s ^ 3 = 1 := by
    have h' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, h3]
    have hz : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) h'
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [this]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact h1 (map_one _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  rw [RonanK429H.autFix_conj]
  exact hgood s hso

theorem k150_noCfgAll_of_model (e : S ≃* G') (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ y : G', orderOf y = 3 → GoodAllFor J (Subgroup.centralizer ({y} : Set G'))) :
    NoCfgAll J S :=
  k150_noCfgAll_of_inner hZ hout fun s hs =>
    GoodAllFor.of_mulEquiv_centralizer e (h (e s) (by rw [MulEquiv.orderOf_eq]; exact hs))

theorem k150_rowAll_of_inner_model {X : Type} [Group X] (hout : ¬ 3 ∣ Nat.card (Outer X))
    (h : ∀ y : X, orderOf y = 3 → GoodAllFor J (Subgroup.centralizer ({y} : Set X))) :
    RowAllOfK150 J X := by
  intro S _ _ hs hna ⟨e⟩
  have := hs
  exact k150_noCfgAll_of_model e (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) h

end Inner

section Criteria

variable {J : Type} [Group J]

private theorem dvd_card_of_quotEquiv {d : ℕ} (hd : d ∣ Nat.card J) {P : Type*} [Group P]
    (N : Subgroup P) [N.Normal] (e : P ⧸ N ≃* J) : d ∣ Nat.card P := by
  refine hd.trans ?_
  rw [← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card N

theorem k150_goodAll_of_card_dvd {S : Type} [Group S] {C : Subgroup S} {M : ℕ}
    (hC : Nat.card C ∣ M) (h : ¬ Nat.card J ∣ M) : GoodAllFor J C := by
  intro P hPC _ _ N _
  exact ⟨fun e => h ((dvd_card_of_quotEquiv dvd_rfl N e).trans
    ((Subgroup.card_dvd_of_le hPC).trans hC))⟩

theorem k150_goodAll_of_not_dvd {S : Type} [Group S] {C : Subgroup S} {d : ℕ}
    (hd : d ∣ Nat.card J) (h : ¬ d ∣ Nat.card C) : GoodAllFor J C := by
  intro P hPC _ _ N _
  exact ⟨fun e => h ((dvd_card_of_quotEquiv hd N e).trans (Subgroup.card_dvd_of_le hPC))⟩

theorem k150_rowAll_of_not_dvd {X : Type} [Group X] (h : ¬ Nat.card J ∣ Nat.card X) :
    RowAllOfK150 J X := by
  intro S _ _ _ _ ⟨e⟩ σ _ _
  refine k150_goodAll_of_card_dvd (M := Nat.card S) (Subgroup.card_subgroup_dvd_card _) ?_
  rwa [Nat.card_congr e.toEquiv]

theorem k150_goodAll_of_perfect_le {S : Type} [Group S] {C E : Subgroup S}
    (hE : ∀ P : Subgroup S, P ≤ C → Group.IsPerfect P → P ≤ E)
    (h : ¬ Nat.card J ∣ Nat.card E) : GoodAllFor J C := by
  intro P hPC _ hPp N _
  exact ⟨fun e => h ((dvd_card_of_quotEquiv dvd_rfl N e).trans
    (Subgroup.card_dvd_of_le (hE P hPC hPp)))⟩

end Criteria

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
