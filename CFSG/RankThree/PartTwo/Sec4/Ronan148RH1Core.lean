module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def IsA5Type (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 5))

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem IsA5Type.card {X : Type} [Group X] (h : IsA5Type X) : Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]

theorem IsA5Type.nontrivial {X : Type} [Group X] (h : IsA5Type X) : Nontrivial X := by
  obtain ⟨e⟩ := h
  haveI : Nontrivial (alternatingGroup (Fin 5)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_alternatingGroup_five]
    norm_num
  exact e.toEquiv.nontrivial

theorem IsA5Type.isSimpleGroup {X : Type} [Group X] (h : IsA5Type X) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  haveI := alternatingGroup.isSimpleGroup_five
  exact e.isSimpleGroup

theorem IsA5Type.congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsA5Type Y) :
    IsA5Type X := by
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

theorem isA5Type_quot_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsA5Type (Y ⧸ CFSG.pCore 2 Y)) : IsA5Type (X ⧸ CFSG.pCore 2 X) :=
  h.congr (quotPCoreTwoCongr e)

section Good

variable {S : Type} [Group S]

@[expose] def Good427 (C : Subgroup S) : Prop :=
  ∀ K : Subgroup S, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal →
    ¬ IsA5Type (K ⧸ CFSG.pCore 2 K)

@[expose] def NoCfgS427 (S : Type) [Group S] : Prop :=
  ∀ σ : MulAut S, σ ^ 3 = 1 → σ ≠ 1 → Good427 (autFix σ)

end Good

section Transport

variable {S G' : Type} [Group S] [Group G']

theorem Good427.of_map {C : Subgroup S} (f : S →* G') (hf : Function.Injective f)
    (h : Good427 (C.map f)) : Good427 C := by
  intro K hKC hKq hKs hT
  have eK : K ≃* K.map f := K.equivMapOfInjective f hf
  refine h (K.map f) (Subgroup.map_mono hKC) (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq) ?_
    (isA5Type_quot_congr eK.symm hT)
  let eC : C ≃* C.map f := C.equivMapOfInjective f hf
  have heC : ∀ x : C, ((eC x : C.map f) : G') = f x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply C f hf x
  have hsurj : Function.Surjective (eC : C →* C.map f) := eC.surjective
  have hmap := hKs.map hsurj
  have heq : (K.subgroupOf C).map (eC : C →* C.map f) = (K.map f).subgroupOf (C.map f) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      rw [← heC x, hxy]
    · rintro ⟨x, hxK, rfl⟩
      refine ⟨⟨x, hKC hxK⟩, hxK, Subtype.ext ?_⟩
      rw [heC]
  rwa [heq] at hmap

theorem Good427.map_mulEquiv {C : Subgroup S} (φ : S ≃* G') (h : Good427 C) :
    Good427 (C.map φ.toMonoidHom) := by
  refine Good427.of_map φ.symm.toMonoidHom φ.symm.injective ?_
  have : (C.map φ.toMonoidHom).map φ.symm.toMonoidHom = C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id C
    ext x
    simp
  rw [this]
  exact h

theorem Good427.conj {P : Subgroup S} {y k : S} (hk : k ∈ P) (hy : y ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : Good427 (Subgroup.centralizer ({y} : Set S) ⊓ P)) :
    Good427 (Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P) := by
  have hmap : (Subgroup.centralizer ({y} : Set S) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P := by
    rw [← centralizer_pow_of_pow_three hy he]
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

theorem Good427.of_isConj {a b : S} (hab : IsConj a b)
    (h : Good427 (Subgroup.centralizer ({a} : Set S))) :
    Good427 (Subgroup.centralizer ({b} : Set S)) := by
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

theorem Good427.of_mulEquiv_centralizer (e : S ≃* G') {s : S}
    (h : Good427 (Subgroup.centralizer ({e s} : Set G'))) :
    Good427 (Subgroup.centralizer ({s} : Set S)) := by
  refine Good427.of_map e.toMonoidHom e.injective ?_
  have hm := RonanK429H.map_centralizer_singleton e.toMonoidHom e.injective s
  rw [MonoidHom.range_eq_top_of_surjective _ e.surjective, inf_top_eq] at hm
  rw [hm]
  exact h

end Transport

section Inner

variable {S G' : Type} [Group S] [Group G']

theorem noCfgS427_of_inner (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hgood : ∀ s : S, orderOf s = 3 → Good427 (Subgroup.centralizer ({s} : Set S))) :
    NoCfgS427 S := by
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
  rw [autFix_conj]
  exact hgood s hso

theorem noCfgS427_of_subgroupModel [Finite S] {P : Subgroup G'} (e : S ≃* P)
    (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ x ∈ P, orderOf x = 3 → Good427 (Subgroup.centralizer ({x} : Set G') ⊓ P)) :
    NoCfgS427 S := by
  refine noCfgS427_of_inner hZ hout fun s hs => ?_
  let f : S →* G' := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  refine Good427.of_map f hf ?_
  rw [RonanK429H.map_centralizer_singleton f hf s, hr]
  exact h (f s) (e s).2 (by rw [orderOf_injective f hf s]; exact hs)

theorem noCfgS427_of_model [Finite S] (e : S ≃* G') (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ y : G', orderOf y = 3 → Good427 (Subgroup.centralizer ({y} : Set G'))) :
    NoCfgS427 S :=
  noCfgS427_of_inner hZ hout fun s hs =>
    Good427.of_mulEquiv_centralizer e (h (e s) (by rw [MulEquiv.orderOf_eq]; exact hs))

end Inner

section Criteria

variable {S : Type} [Group S] [Finite S]

theorem good427_of_card_dvd {C : Subgroup S} {M : ℕ} (hC : Nat.card C ∣ M) (h60 : ¬ 60 ∣ M) :
    Good427 C := by
  intro K hKC _ _ hT
  apply h60
  obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow K
  have h1 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K := ha ▸ Dvd.intro _ rfl
  rw [hT.card] at h1
  exact h1.trans ((Subgroup.card_dvd_of_le hKC).trans hC)

theorem exists_card_eq_sixty_mul {K : Subgroup S} (hT : IsA5Type (K ⧸ CFSG.pCore 2 K)) :
    ∃ a : ℕ, Nat.card K = 60 * 2 ^ a := by
  obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow K
  exact ⟨a, by rw [ha, hT.card]⟩

theorem good427_of_isQuasisimple {C : Subgroup S} (hC : IsQuasisimple C)
    (hZ : IsPGroup 3 (Subgroup.center C)) (h60 : Nat.card C ≠ 60) : Good427 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  haveI := hT.nontrivial
  haveI : Nontrivial K := (QuotientGroup.mk'_surjective (CFSG.pCore 2 K)).nontrivial
  rcases Res429.eq_top_or_le_center_of_isSubnormal hC hKs with htop | hcen
  · have hKeq : K = C := le_antisymm hKC (Subgroup.subgroupOf_eq_top.mp htop)
    subst hKeq
    have hO : CFSG.pCore 2 K = ⊥ := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hle := pCore_two_le_center' hC
      have h2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, ha⟩ := h2 ⟨x, hx⟩
      obtain ⟨b, hb⟩ := hZ ⟨x, hle hx⟩
      have ha' : x ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have hb' : x ^ 3 ^ b = 1 := congrArg Subtype.val hb
      have hord : orderOf x ∣ Nat.gcd (2 ^ a) (3 ^ b) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow a b (by norm_num))] at hord
      exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord))
    have eQ : K ⧸ CFSG.pCore 2 K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    apply h60
    rw [← Nat.card_congr eQ.toEquiv, hT.card]
  ·
    have hab : ∀ a b : K, a * b = b * a := by
      intro a b
      have ha : (⟨a, hKC a.2⟩ : C) ∈ Subgroup.center C := hcen a.2
      have h := Subgroup.mem_center_iff.mp ha ⟨b, hKC b.2⟩
      exact Subtype.ext (congrArg Subtype.val h).symm
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hab)

theorem isComponent_subgroupOf_of_isA5Type {C K : Subgroup S} (hKC : K ≤ C)
    [hKp : Group.IsPerfect K] (hKs : (K.subgroupOf C).IsSubnormal)
    (hT : IsA5Type (K ⧸ CFSG.pCore 2 K)) (hO : CFSG.pCore 2 C = ⊥) :
    IsComponent (K.subgroupOf C) ∧ CFSG.pCore 2 K = ⊥ := by
  set K' : Subgroup C := K.subgroupOf C
  have eK : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  have hle := CFSG.GH74.GLS.Balance.SolvComp.map_pCore_le_pCore_of_isSubnormal 2 hKs
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K'.subtype_injective] at hle
  have hK2 : CFSG.pCore 2 K = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 eK, hle, Subgroup.map_bot]
  refine ⟨⟨?_, hKs⟩, hK2⟩
  have eQ : K ⧸ CFSG.pCore 2 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hK2).trans QuotientGroup.quotientBot
  haveI : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := inferInstance
  haveI := hT.isSimpleGroup
  haveI : IsSimpleGroup K := eQ.symm.isSimpleGroup
  haveI : IsSimpleGroup K' := eK.isSimpleGroup
  haveI : Group.IsPerfect K' := Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom)
    eK.symm.surjective
  haveI : Nontrivial K' := by
    haveI := hT.nontrivial
    haveI : Nontrivial K := eQ.symm.toEquiv.nontrivial
    exact eK.toEquiv.nontrivial
  exact isQuasisimple_of_isSimpleGroup'

theorem not_isPGroup_three_of_isA5Type {K : Subgroup S} [Group.IsPerfect K]
    (hT : IsA5Type (K ⧸ CFSG.pCore 2 K)) (h : IsPGroup 3 K) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hT.nontrivial
  haveI : Nontrivial K := (QuotientGroup.mk'_surjective (CFSG.pCore 2 K)).nontrivial
  exact not_isPGroup_of_isPerfect h

theorem good427_of_selfCentralizing' {C R : Subgroup S} (hRC : R ≤ C)
    (hRn : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR3 : IsPGroup 3 R)
    (hcent : Subgroup.centralizer (R : Set S) ⊓ C ≤ R) : Good427 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R' : Subgroup C := R.subgroupOf C
  have hR'n : R'.Normal := normal_subgroupOf_of_forall_conj' hRn
  have hO : CFSG.pCore 2 C = ⊥ := by
    set O := CFSG.pCore 2 C
    have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
    have hR'3 : IsPGroup 3 R' := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
    have hdisj : O ⊓ R' = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime ?_
      obtain ⟨a, ha⟩ := hO2.exists_card_eq
      obtain ⟨b, hb⟩ := hR'3.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow a b (by norm_num)
    haveI := hR'n
    have hcomm : ⁅O, R'⁆ = ⊥ := by
      rw [eq_bot_iff, ← hdisj]
      exact le_inf (Subgroup.commutator_le_left O R') (Subgroup.commutator_le_right O R')
    have hOR : O ≤ R' := by
      intro x hx
      have hxc : (x : S) ∈ Subgroup.centralizer (R : Set S) ⊓ C := by
        refine ⟨?_, x.2⟩
        show (x : S) ∈ Subgroup.centralizer (R : Set S)
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
        rw [Subgroup.mem_centralizer_iff] at this
        have h' := this ⟨r, hRC hr⟩ hr
        exact congrArg Subtype.val h'
      exact hcent hxc
    rw [eq_bot_iff, ← hdisj]
    exact le_inf le_rfl hOR
  obtain ⟨hcomp, -⟩ := isComponent_subgroupOf_of_isA5Type hKC hKs hT hO
  rcases CFSG.LocalCores.component_normal_subgroup hcomp hR'n with hle | hcomm
  · refine not_isPGroup_three_of_isA5Type hT (hR3.to_le fun k hk => ?_)
    have := hle (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    exact this
  · refine not_isPGroup_three_of_isA5Type hT (hR3.to_le fun k hk => hcent ⟨?_, hKC hk⟩)
    show k ∈ Subgroup.centralizer (R : Set S)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    rw [Subgroup.mem_centralizer_iff] at this
    have h' := this ⟨r, hRC hr⟩ hr
    exact congrArg Subtype.val h'

end Criteria

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
