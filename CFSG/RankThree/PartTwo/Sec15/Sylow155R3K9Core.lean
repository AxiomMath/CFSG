module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def GoodJ2 {S : Type} [Group S] (C : Subgroup S) : Prop :=
  ∀ P : Subgroup S, P ≤ C → (P.subgroupOf C).IsSubnormal → Group.IsPerfect P →
    ∀ (N : Subgroup P) [N.Normal], IsEmpty (P ⧸ N ≃* Blueprint.NativeSporadic.J2)

@[expose] def NoCfgJ2 (S : Type) [Group S] : Prop :=
  ∀ σ : MulAut S, σ ^ 3 = 1 → σ ≠ 1 → GoodJ2 (Sec4.autFix σ)

@[expose] def RowOfK9 (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → NoCfgJ2 S

section Transport

variable {S G' : Type} [Group S] [Group G']

theorem GoodJ2.of_map {C : Subgroup S} (f : S →* G') (hf : Function.Injective f)
    (h : GoodJ2 (C.map f)) : GoodJ2 C := by
  intro P hPC hPs hPp N hN
  haveI := hPp
  let eP : P ≃* P.map f := P.equivMapOfInjective f hf
  haveI : (N.map (eP : P →* P.map f)).Normal := hN.map _ eP.surjective
  haveI : Group.IsPerfect (P.map f) := Group.IsPerfect.map f
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

theorem GoodJ2.map_mulEquiv {C : Subgroup S} (φ : S ≃* G') (h : GoodJ2 C) :
    GoodJ2 (C.map φ.toMonoidHom) := by
  refine GoodJ2.of_map φ.symm.toMonoidHom φ.symm.injective ?_
  have : (C.map φ.toMonoidHom).map φ.symm.toMonoidHom = C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id C
    ext x
    simp
  rw [this]
  exact h

theorem GoodJ2.conj {P : Subgroup S} {y k : S} (hk : k ∈ P) (hy : y ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : GoodJ2 (Subgroup.centralizer ({y} : Set S) ⊓ P)) :
    GoodJ2 (Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P) := by
  have hmap : (Subgroup.centralizer ({y} : Set S) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P := by
    rw [← RonanK429H.centralizer_pow_of_pow_three hy he]
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
      calc k * z * k⁻¹ * (k * y ^ e * k⁻¹) = k * (z * y ^ e) * k⁻¹ := by group
        _ = k * (y ^ e * z) * k⁻¹ := by rw [hzc]
        _ = k * y ^ e * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hwc, hwP⟩
      refine ⟨k⁻¹ * w * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hwP) hk⟩, by group⟩
      calc k⁻¹ * w * k * y ^ e = k⁻¹ * (w * (k * y ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * y ^ e * k⁻¹) * w) * k := by rw [hwc]
        _ = y ^ e * (k⁻¹ * w * k) := by group
  rw [← hmap]
  exact h.map_mulEquiv (MulAut.conj k)

theorem GoodJ2.of_isConj {a b : S} (hab : IsConj a b)
    (h : GoodJ2 (Subgroup.centralizer ({a} : Set S))) :
    GoodJ2 (Subgroup.centralizer ({b} : Set S)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hab
  have hmap : (Subgroup.centralizer ({a} : Set S)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * a * c⁻¹} : Set S) := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      calc c * z * c⁻¹ * (c * a * c⁻¹) = c * (z * a) * c⁻¹ := by group
        _ = c * (a * z) * c⁻¹ := by rw [hz]
        _ = c * a * c⁻¹ * (c * z * c⁻¹) := by group
    · intro hw
      refine ⟨c⁻¹ * w * c, ?_, by group⟩
      calc c⁻¹ * w * c * a = c⁻¹ * (w * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * a * c⁻¹) * w) * c := by rw [hw]
        _ = a * (c⁻¹ * w * c) := by group
  rw [← hmap]
  exact h.map_mulEquiv (MulAut.conj c)

theorem GoodJ2.of_mulEquiv_centralizer (e : S ≃* G') {s : S}
    (h : GoodJ2 (Subgroup.centralizer ({e s} : Set G'))) :
    GoodJ2 (Subgroup.centralizer ({s} : Set S)) := by
  refine GoodJ2.of_map e.toMonoidHom e.injective ?_
  have hm := RonanK429H.map_centralizer_singleton e.toMonoidHom e.injective s
  rw [MonoidHom.range_eq_top_of_surjective _ e.surjective, inf_top_eq] at hm
  rw [hm]
  exact h

end Transport

section Inner

variable {S G' : Type} [Group S] [Group G']

theorem noCfgJ2_of_inner (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hgood : ∀ s : S, orderOf s = 3 → GoodJ2 (Subgroup.centralizer ({s} : Set S))) :
    NoCfgJ2 S := by
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
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  rw [RonanK429H.autFix_conj]
  exact hgood s hso

theorem noCfgJ2_of_subgroupModel {P : Subgroup G'} (e : S ≃* P)
    (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ x ∈ P, orderOf x = 3 → GoodJ2 (Subgroup.centralizer ({x} : Set G') ⊓ P)) :
    NoCfgJ2 S := by
  refine noCfgJ2_of_inner hZ hout fun s hs => ?_
  let f : S →* G' := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  refine GoodJ2.of_map f hf ?_
  rw [RonanK429H.map_centralizer_singleton f hf s, hr]
  exact h (f s) (e s).2 (by rw [orderOf_injective f hf s]; exact hs)

theorem noCfgJ2_of_model (e : S ≃* G') (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ y : G', orderOf y = 3 → GoodJ2 (Subgroup.centralizer ({y} : Set G'))) :
    NoCfgJ2 S :=
  noCfgJ2_of_inner hZ hout fun s hs =>
    GoodJ2.of_mulEquiv_centralizer e (h (e s) (by rw [MulEquiv.orderOf_eq]; exact hs))

end Inner

section Criteria

private theorem dvd_card_of_quotEquiv_j2 {P : Type*} [Group P] (N : Subgroup P) [N.Normal]
    (e : P ⧸ N ≃* Blueprint.NativeSporadic.J2) : 604800 ∣ Nat.card P := by
  rw [← KFacts.KS14.card_nativeJ2, ← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card N

theorem goodJ2_of_card_dvd {S : Type} [Group S] {C : Subgroup S} {M : ℕ}
    (hC : Nat.card C ∣ M) (h : ¬ 604800 ∣ M) : GoodJ2 C := by
  intro P hPC _ _ N _
  exact ⟨fun e => h ((dvd_card_of_quotEquiv_j2 N e).trans
    ((Subgroup.card_dvd_of_le hPC).trans hC))⟩

theorem rowOfK9_of_not_dvd {X : Type} [Group X] (h : ¬ 604800 ∣ Nat.card X) : RowOfK9 X := by
  intro S _ _ _ _ ⟨e⟩ σ _ _
  refine goodJ2_of_card_dvd (M := Nat.card S) (Subgroup.card_subgroup_dvd_card _) ?_
  rwa [Nat.card_congr e.toEquiv]

theorem goodJ2_of_perfect_le {S : Type} [Group S] {C E : Subgroup S}
    (hE : ∀ P : Subgroup S, P ≤ C → Group.IsPerfect P → P ≤ E)
    (h : ¬ 604800 ∣ Nat.card E) : GoodJ2 C := by
  intro P hPC _ hPp N _
  exact ⟨fun e => h ((dvd_card_of_quotEquiv_j2 N e).trans
    (Subgroup.card_dvd_of_le (hE P hPC hPp)))⟩

theorem goodJ2_of_isQuasisimple {S : Type} [Group S] [Finite S] {C : Subgroup S}
    (hC : CFSG.IsQuasisimple C) (hZ : IsPGroup 3 (Subgroup.center C))
    (h : ∀ k : ℕ, Nat.card C ≠ 604800 * 3 ^ k) : GoodJ2 C := by
  intro P hPC hPs hPp N hN
  haveI := hPp
  refine ⟨fun e => ?_⟩
  have hcard : Nat.card (P ⧸ N) = 604800 :=
    (Nat.card_congr e.toEquiv).trans KFacts.KS14.card_nativeJ2
  haveI : Finite (P ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial (P ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  haveI : Nontrivial P := (QuotientGroup.mk'_surjective N).nontrivial
  rcases Res429.eq_top_or_le_center_of_isSubnormal hC hPs with htop | hcen
  · have hPeq : P = C := le_antisymm hPC (Subgroup.subgroupOf_eq_top.mp htop)
    subst hPeq
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC hN with hNtop | hNcen
    · haveI : Subsingleton (P ⧸ N) := by
        rw [hNtop]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_nontrivial _ ‹Nontrivial (P ⧸ N)›
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨a, ha⟩ := (hZ.to_le hNcen).exists_card_eq
      refine h a ?_
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcard, ha]
  · have hab : ∀ a b : P, a * b = b * a := by
      intro a b
      have ha : (⟨a, hPC a.2⟩ : C) ∈ Subgroup.center C := hcen a.2
      have h' := Subgroup.mem_center_iff.mp ha ⟨b, hPC b.2⟩
      exact Subtype.ext (congrArg Subtype.val h').symm
    exact Group.IsPerfect.not_isSolvable P (Group.isSolvable_of_comm hab)

theorem rowOfK9_J2 : RowOfK9 (Spor .J2) := by
  intro S _ _ _ _ ⟨e⟩ σ _ h1
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J2 ≃* Spor .J2 := b
  have hS : Nat.card S = 604800 :=
    (Nat.card_congr (e.trans b'.symm).toEquiv).trans KFacts.KS14.card_nativeJ2
  refine goodJ2_of_card_dvd (M := Nat.card (autFix σ)) dvd_rfl fun hdvd => h1 ?_
  have hdvd' : Nat.card (autFix σ) ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _
  rw [hS] at hdvd'
  have hcard : Nat.card (autFix σ) = Nat.card S := by
    rw [hS]
    exact Nat.dvd_antisymm hdvd' hdvd
  have htop : autFix σ = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  ext x
  have hx : x ∈ autFix σ := htop ▸ Subgroup.mem_top x
  exact hx

theorem rowOfK9_spor {s : TauCeti.SporadicName}
    (hb : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* Spor s))
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) → NoCfgJ2 S) :
    RowOfK9 (Spor s) := by
  intro S _ _ hs hna ⟨e⟩
  obtain ⟨b⟩ := hb
  exact h S hs hna ⟨e.trans b.symm⟩

end Criteria

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
