module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

@[expose] def Good425 {S : Type} [Group S] (C : Subgroup S) : Prop :=
  ∀ K : Subgroup S, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal →
    ¬ IsType425 (K ⧸ aschbacherSolvableCore 3 K)

section Transport425

variable {S G' : Type} [Group S] [Group G']

theorem Good425.of_map [Finite S] (f : S →* G') (hf : Function.Injective f) {C : Subgroup S}
    (h : Good425 (C.map f)) : Good425 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  have eK : K ≃* K.map f := K.equivMapOfInjective f hf
  have hKq' : IsQuasisimple (K.map f) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq
  refine h (K.map f) (Subgroup.map_mono hKC) hKq' ?_ (isType425_theta_congr eK hT)
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

theorem Good425.map_mulEquiv [Finite G'] (φ : S ≃* G') {C : Subgroup S} (h : Good425 C) :
    Good425 (C.map φ.toMonoidHom) := by
  refine Good425.of_map φ.symm.toMonoidHom φ.symm.injective ?_
  rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id S by
    ext; simp, Subgroup.map_id]

theorem Good425.conj [Finite S] {P : Subgroup S} {y k : S} (hk : k ∈ P) (hy : y ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : Good425 (Subgroup.centralizer ({y} : Set S) ⊓ P)) :
    Good425 (Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P) := by
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

theorem Good425.of_isConj [Finite S] {a b : S} (hab : IsConj a b)
    (h : Good425 (Subgroup.centralizer ({a} : Set S))) :
    Good425 (Subgroup.centralizer ({b} : Set S)) := by
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

end Transport425

section Criteria425

variable {S : Type} [Group S] [Finite S]

theorem theta_eq_bot_of_center_three {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hZ : IsPGroup 3 (Subgroup.center X)) : aschbacherSolvableCore 3 X = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : Nat.card (aschbacherSolvableCore 3 X) ∣ Nat.card (Subgroup.center X) :=
    Subgroup.card_dvd_of_le (aschbacherSolvableCore_le_center hX)
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at hd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hnd : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 X) :=
    (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
  have hj0 : j = 0 := by
    by_contra h
    exact hnd (by rw [hj]; exact dvd_pow_self 3 h)
  rw [hj0, pow_zero] at hj
  exact Subgroup.card_eq_one.mp hj

theorem good425_of_isQuasisimple {C : Subgroup S} (hC : IsQuasisimple C)
    (hZ : IsPGroup 3 (Subgroup.center C)) {B : ℕ} (hB : Nat.card C < B ^ 3)
    (hCt : Nat.card C ∉ typeOrders425 (Nat.card C) B) : Good425 C := by
  intro K hKC hKq hKs hT
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hKeq : K = C := Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hKC hC hKq.1 hnt hKs
  rw [hKeq] at hT
  have hθ := theta_eq_bot_of_center_three hC hZ
  have eQ : C ⧸ aschbacherSolvableCore 3 C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot
  have hTC : IsType425 C := isType425_congr eQ hT
  exact hCt (card_mem_typeOrders425 hC Nat.card_pos hB hTC (dvd_refl _))

theorem good425_of_selfCentralizing' {C R : Subgroup S} (hRC : R ≤ C)
    (hRn : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR3 : IsPGroup 3 R)
    (hcent : Subgroup.centralizer (R : Set S) ⊓ C ≤ R) : Good425 C := by
  intro K hKC hKq hKs hT
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect K := hKq.1
  set R' : Subgroup C := R.subgroupOf C
  have hR'n : R'.Normal := RonanK429H.normal_subgroupOf_of_forall_conj' hRn
  have hR'3 : IsPGroup 3 R' := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
  have hR's : Group.IsSolvable R' := by
    haveI := hR'3.isNilpotent
    infer_instance
  have hK'c : IsComponent (K.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hKq, hKs⟩
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hR's hR'n.isSubnormal).1
    (K.subgroupOf C) hK'c
  have hKR : K ≤ R := by
    intro k hk
    refine hcent ⟨?_, hKC hk⟩
    show k ∈ Subgroup.centralizer (R : Set S)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hmem : ⁅(⟨k, hKC hk⟩ : C), (⟨r, hRC hr⟩ : C)⁆ ∈ ⁅K.subgroupOf C, R'⁆ :=
      Subgroup.commutator_mem_commutator (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
        (show (⟨r, hRC hr⟩ : C) ∈ R' from hr)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact (congrArg Subtype.val hmem).symm
  have hK3 : IsPGroup 3 K := hR3.to_le hKR
  haveI := hK3.isNilpotent
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem good425_of_derived_le {C E : Subgroup S} (hder : ⁅C, C⁆ ≤ E) {M B : ℕ} (hM0 : 0 < M)
    (hB : M < B ^ 3) (hE : Nat.card E ∣ M) (hfree : typeOrders425 M B = []) : Good425 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  have hKK : ⁅K, K⁆ = K := Subgroup.commutator_eq_self (H := K)
  have hKE : K ≤ E := by
    have h := Subgroup.commutator_mono hKC hKC
    rw [hKK] at h
    exact h.trans hder
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hKE).trans hE)
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) hM0 hB hT hdvd
  rw [hfree] at hmem
  exact List.not_mem_nil hmem

theorem noCC425_of_good425
    (h : ∀ s : S, orderOf s = 3 → Good425 (Subgroup.centralizer ({s} : Set S))) : NoCC425 S :=
  fun s K hc => h s hc.orderOf_eq K hc.le_centralizer hc.isQuasisimple hc.isSubnormal hc.isType

end Criteria425

theorem noCC425_of_subgroupModel {S G' : Type} [Group S] [Group G'] [Finite S] {P : Subgroup G'}
    (e : S ≃* P) (h : ∀ x ∈ P, orderOf x = 3 → Good425 (Subgroup.centralizer ({x} : Set G') ⊓ P)) :
    NoCC425 S := by
  intro s K hc
  let f : S →* G' := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  have hgood : Good425 ((Subgroup.centralizer ({s} : Set S)).map f) := by
    rw [RonanK429H.map_centralizer_singleton f hf s, hr]
    exact h (f s) (e s).2 (by rw [orderOf_injective f hf s]; exact hc.orderOf_eq)
  exact (Good425.of_map f hf hgood) K hc.le_centralizer hc.isQuasisimple hc.isSubnormal hc.isType


section More425

variable {S : Type} [Group S] [Finite S]

theorem good425_of_card_dvd {C : Subgroup S} {M B : ℕ} (hC : Nat.card C ∣ M) (hM0 : 0 < M)
    (hB : M < B ^ 3) (hfree : typeOrders425 M B = []) : Good425 C := by
  intro K hKC hKq _ hT
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hKC).trans hC)
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) hM0 hB hT hdvd
  rw [hfree] at hmem
  exact List.not_mem_nil hmem

theorem good425_centralizer_of_mulEquiv {T : Type} [Group T] [Finite T] (e : S ≃* T) {s : S}
    (h : Good425 (Subgroup.centralizer ({e s} : Set T))) :
    Good425 (Subgroup.centralizer ({s} : Set S)) := by
  refine Good425.of_map (e : S →* T) e.injective ?_
  rwa [map_centralizer_singleton_equiv e s]

end More425

theorem good425_all_of_subgroupModel {S G' : Type} [Group S] [Group G'] [Finite S]
    {P : Subgroup G'} (e : S ≃* P)
    (h : ∀ x ∈ P, orderOf x = 3 → Good425 (Subgroup.centralizer ({x} : Set G') ⊓ P)) :
    ∀ s : S, orderOf s = 3 → Good425 (Subgroup.centralizer ({s} : Set S)) := by
  intro s hs
  let f : S →* G' := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  have hgood : Good425 ((Subgroup.centralizer ({s} : Set S)).map f) := by
    rw [RonanK429H.map_centralizer_singleton f hf s, hr]
    exact h (f s) (e s).2 (by rw [orderOf_injective f hf s]; exact hs)
  exact Good425.of_map f hf hgood

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
