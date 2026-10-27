module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCore
public import CFSG.Models.PGLSimple
public import CFSG.GH74.GLS.Balance.SolvCompBasic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Transport

variable {S G' : Type} [Group S] [Group G']

theorem Good429.of_map {C : Subgroup S} (f : S →* G') (hf : Function.Injective f)
    (h : Good429 (C.map f)) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  have eK : K ≃* K.map f := K.equivMapOfInjective f hf
  haveI : Group.IsPerfect (K.map f) := Group.IsPerfect.map f
  refine h (K.map f) (Subgroup.map_mono hKC) inferInstance ?_ (isType429_quot_congr eK hT)
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

theorem map_centralizer_singleton (f : S →* G') (hf : Function.Injective f) (s : S) :
    (Subgroup.centralizer ({s} : Set S)).map f =
      Subgroup.centralizer ({f s} : Set G') ⊓ f.range := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rw [← map_mul, ← map_mul, hx], x, rfl⟩
  · rintro ⟨hy, x, rfl⟩
    refine ⟨x, hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hy

theorem Good429.map_mulEquiv {C : Subgroup S} (φ : S ≃* G') (h : Good429 C) :
    Good429 (C.map φ.toMonoidHom) := by
  refine Good429.of_map φ.symm.toMonoidHom φ.symm.injective ?_
  rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id S by
    ext; simp, Subgroup.map_id]

theorem centralizer_pow_of_pow_three {y : S} (hy : y ^ 3 = 1) {e : ℕ} (he : e = 1 ∨ e = 2) :
    Subgroup.centralizer ({y ^ e} : Set S) = Subgroup.centralizer ({y} : Set S) := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      have h4 : y = (y ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hy, one_mul, pow_one]
      rw [h4]
      exact (Commute.pow_right (show Commute z (y ^ 2) from hz) 2).eq
    · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      exact (Commute.pow_right (show Commute z y from hz) 2).eq

theorem Good429.conj {P : Subgroup S} {y k : S} (hk : k ∈ P) (hy : y ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : Good429 (Subgroup.centralizer ({y} : Set S) ⊓ P)) :
    Good429 (Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P) := by
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

theorem Good429.of_isConj {a b : S} (hab : IsConj a b)
    (h : Good429 (Subgroup.centralizer ({a} : Set S))) :
    Good429 (Subgroup.centralizer ({b} : Set S)) := by
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

theorem Good429.of_mulEquiv_centralizer (e : S ≃* G') {s : S}
    (h : Good429 (Subgroup.centralizer ({e s} : Set G'))) :
    Good429 (Subgroup.centralizer ({s} : Set S)) := by
  refine Good429.of_map e.toMonoidHom e.injective ?_
  have hm := map_centralizer_singleton e.toMonoidHom e.injective s
  rw [MonoidHom.range_eq_top_of_surjective _ e.surjective, inf_top_eq] at hm
  rw [hm]
  exact h

theorem card_centralizer_mulEquiv (e : S ≃* G') (s : S) :
    Nat.card (Subgroup.centralizer ({e s} : Set G')) =
      Nat.card (Subgroup.centralizer ({s} : Set S)) := by
  have h := map_centralizer_singleton e.toMonoidHom e.injective s
  rw [MonoidHom.range_eq_top_of_surjective _ e.surjective, inf_top_eq] at h
  rw [show (e.toMonoidHom s) = e s from rfl] at h
  rw [← h, Subgroup.card_map_of_injective e.injective]

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence) in
theorem not_three_dvd_outer_of_mulEquiv (e : S ≃* G')
    (h : ¬ 3 ∣ Nat.card (Outer G')) : ¬ 3 ∣ Nat.card (Outer S) := by
  rwa [Nat.card_congr (equivalence e).toEquiv]

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem not_three_dvd_outer_of_le_two [Finite G'] (h : Nat.card (Outer G') ≤ 2) :
    ¬ 3 ∣ Nat.card (Outer G') := by
  haveI : Finite (MulAut G') := Finite.of_injective (fun φ : MulAut G' => (φ : G' → G'))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hpos : 0 < Nat.card (Outer G') := Nat.card_pos
  omega

theorem forall_good429_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : ∀ x : T', orderOf x = 3 → Good429 (Subgroup.centralizer ({x} : Set T'))) :
    ∀ x : T, orderOf x = 3 → Good429 (Subgroup.centralizer ({x} : Set T)) := fun x hx =>
  Good429.of_mulEquiv_centralizer e (h (e x) (by rwa [MulEquiv.orderOf_eq]))

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem noCfgS429_of_model [Finite S] (e : S ≃* G') (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ x : G', orderOf x = 3 → Good429 (Subgroup.centralizer ({x} : Set G'))) :
    NoCfgS429 S := by
  refine noCfgS429_of_inner hZ hout fun s hs => ?_
  have hs' : orderOf (e s) = 3 := by rwa [MulEquiv.orderOf_eq]
  exact Good429.of_mulEquiv_centralizer e (h (e s) hs')

end Transport

section CriteriaFree

theorem isQuasisimple_of_isSimpleGroup' {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] [Nontrivial X] : IsQuasisimple X := by
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_isSimpleGroup_of_isPerfect
  have e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨inferInstance, e.isSimpleGroup, ?_⟩
  have hnc := Group.IsPerfect.not_isMulCommutative X
  by_contra hc
  push_neg at hc
  apply hnc
  refine ⟨⟨fun a b => ?_⟩⟩
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact hc _ _

theorem not_isPGroup_of_isPerfect {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Nontrivial X] {p : ℕ} [Fact p.Prime] (h : IsPGroup p X) : False :=
  Group.IsPerfect.not_isNilpotent X h.isNilpotent

variable {S : Type} [Group S] [Finite S]

theorem isPGroup_three_of_pow_three {K : Subgroup S} (h : ∀ k ∈ K, k ^ 3 = 1) :
    IsPGroup 3 K := by
  intro k
  exact ⟨1, by rw [pow_one]; exact Subtype.ext (h k k.2)⟩

theorem pCore_two_le_center' {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    CFSG.pCore 2 Q ≤ Subgroup.center Q := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ
      (inferInstance : (CFSG.pCore 2 Q).Normal) with h | h
  · exfalso
    have h2 : IsPGroup 2 (CFSG.pCore 2 Q) := CFSG.pCore_isPGroup
    rw [h] at h2
    have hp : IsPGroup 2 Q := h2.of_equiv Subgroup.topEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hQ.1
    haveI : Nontrivial Q := by
      haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hQ.2.1.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
    exact Group.IsPerfect.not_isNilpotent Q hp.isNilpotent
  · exact h

theorem good429_of_isQuasisimple {C : Subgroup S} (hC : IsQuasisimple C)
    (hZ : IsPGroup 3 (Subgroup.center C)) {B : ℕ} (hB : Nat.card C < B ^ 3)
    (hCt : Nat.card C ∉ typeOrders (Nat.card C) B) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  haveI := nontrivial_of_isType429 hT
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
    haveI : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := inferInstance
    have hmem := card_mem_typeOrders (M := Nat.card K) (B := B) Nat.card_pos hB hT
      (by rw [Nat.card_congr eQ.toEquiv])
    rw [Nat.card_congr eQ.toEquiv] at hmem
    exact hCt hmem
  ·
    have hab : ∀ a b : K, a * b = b * a := by
      intro a b
      have ha : (⟨a, hKC a.2⟩ : C) ∈ Subgroup.center C := hcen a.2
      have h := Subgroup.mem_center_iff.mp ha ⟨b, hKC b.2⟩
      exact Subtype.ext (congrArg Subtype.val h).symm
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hab)

theorem good429_of_simple_small_index {C E : Subgroup S} (hEC : E ≤ C) [hEs : IsSimpleGroup E]
    {m : ℕ} (hm : m < 30) (hCm : Nat.card C ≤ m * Nat.card E) (hdvd : ¬ Nat.card E ∣ m.factorial)
    {B : ℕ} (hB : Nat.card E < B ^ 3) (hfree : typeOrders (Nat.card E) B = []) :
    Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  set E' : Subgroup C := E.subgroupOf C
  have eE : E' ≃* E := Subgroup.subgroupOfEquivOfLe hEC
  haveI : IsSimpleGroup E' := eE.isSimpleGroup
  have hE'card : Nat.card E' = Nat.card E := Nat.card_congr eE.toEquiv
  have hidx : E'.index ≤ m := by
    have hmul := Subgroup.card_mul_index E'
    rw [hE'card] at hmul
    have hE0 : 0 < Nat.card E := Nat.card_pos
    by_contra hlt
    push_neg at hlt
    have : Nat.card E * (m + 1) ≤ Nat.card E * E'.index := Nat.mul_le_mul_left _ hlt
    nlinarith
  set N := E'.normalCore
  have hNE : N ≤ E' := E'.normalCore_le
  have hNnormal : (N.subgroupOf E').Normal := Subgroup.normal_subgroupOf
  have hNcases := hNnormal.eq_bot_or_eq_top
  have hNeq : N = E' := by
    rcases hNcases with h | h
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at h
      have hN1 : N = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hx (hNE hx))
      have hdiv : N.index ∣ E'.index.factorial := E'.index_normalCore_dvd_factorial_index
      rw [hN1, Subgroup.index_bot] at hdiv
      apply hdvd
      calc Nat.card E ∣ Nat.card C := Subgroup.card_dvd_of_le hEC
        _ ∣ E'.index.factorial := hdiv
        _ ∣ m.factorial := Nat.factorial_dvd_factorial hidx
    · exact le_antisymm hNE (Subgroup.subgroupOf_eq_top.mp h)
  haveI hE'n : E'.Normal := hNeq ▸ E'.normalCore_normal
  set K' : Subgroup C := K.subgroupOf C
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  haveI : Group.IsPerfect (K'.map (QuotientGroup.mk' E')) := Group.IsPerfect.map _
  have hpf : (Nat.card (K'.map (QuotientGroup.mk' E'))).primeFactors.card ≤ 2 := by
    have hd : Nat.card (K'.map (QuotientGroup.mk' E')) ∣ E'.index :=
      Subgroup.card_subgroup_dvd_card _
    have hpos : 0 < E'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h30 : E'.index < 30 := by omega
    have h1 : E'.index.primeFactors.card ≤ 2 := by
      interval_cases h : E'.index <;> exact primeFactors_card_le_two_of_twoPrimeOK (by decide)
    exact (Finset.card_le_card (Nat.primeFactors_mono hd (by omega))).trans h1
  haveI := subsingleton_of_isPerfect_of_card_primeFactors hpf
  have hbot : K'.map (QuotientGroup.mk' E') = ⊥ := Subgroup.eq_bot_of_subsingleton _
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  have hKE : K ≤ E := fun k hk =>
    hbot (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
  haveI := nontrivial_of_isType429 hT
  have hE0 : 0 < Nat.card E := Nat.card_pos
  refine not_isType429_of_dvd hE0 hB hfree ?_ hT
  obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow K
  have h1 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K := ha ▸ Dvd.intro _ rfl
  exact h1.trans (Subgroup.card_dvd_of_le hKE)

end CriteriaFree

section Simple

theorem isSimpleGroup_of_isType429 {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (h : IsType429 X) : IsSimpleGroup X := by
  haveI := nontrivial_of_isType429 h
  rcases h with ⟨p, e, hp, he, (⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩)⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p e)
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact φ.isSimpleGroup
  · have hpp : p.Prime := hp.out
    by_cases hq : p ^ e = 2
    · exfalso
      have hp2 : p = 2 := by
        rcases (Nat.prime_two.eq_one_or_self_of_dvd p
          (hq ▸ dvd_pow_self p (by omega))) with h | h
        · exact absurd h hpp.one_lt.ne'
        · exact h
      subst hp2
      have he1 : e = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using hq)
      subst he1
      exact not_subsingleton X (subsingleton_of_mulEquiv_projSU_three_two φ)
    · haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible (n := 3) (p := p) (f := e)
        ⟨Fact.out, he, le_rfl, fun h => hq (Prod.mk.inj h).2⟩
      exact φ.isSimpleGroup
  · haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact φ.isSimpleGroup
  · haveI : IsSimpleGroup Blueprint.NativeSporadic.M12 :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact φ.isSimpleGroup
  · haveI : IsSimpleGroup Blueprint.NativeSporadic.M22 :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact φ.isSimpleGroup
  · haveI : IsSimpleGroup Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact φ.isSimpleGroup

variable {S : Type} [Group S] [Finite S]

theorem isComponent_subgroupOf_of_isType429 {C K : Subgroup S} (hKC : K ≤ C)
    [hKp : Group.IsPerfect K] (hKs : (K.subgroupOf C).IsSubnormal)
    (hT : IsType429 (K ⧸ CFSG.pCore 2 K)) (hO : CFSG.pCore 2 C = ⊥) :
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
  haveI := isSimpleGroup_of_isType429 hT
  haveI : IsSimpleGroup K := eQ.symm.isSimpleGroup
  haveI : IsSimpleGroup K' := eK.isSimpleGroup
  haveI : Group.IsPerfect K' := Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom)
    eK.symm.surjective
  haveI : Nontrivial K' := by
    haveI := nontrivial_of_isType429 hT
    haveI : Nontrivial K := eQ.symm.toEquiv.nontrivial
    exact eK.toEquiv.nontrivial
  exact isQuasisimple_of_isSimpleGroup'

end Simple

section Criteria

variable {S : Type} [Group S] [Finite S]

theorem not_isPGroup_three_of_isType429 {K : Subgroup S} [Group.IsPerfect K]
    (hT : IsType429 (K ⧸ CFSG.pCore 2 K)) (h : IsPGroup 3 K) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := nontrivial_of_isType429 hT
  haveI : Nontrivial K := (QuotientGroup.mk'_surjective (CFSG.pCore 2 K)).nontrivial
  exact not_isPGroup_of_isPerfect h

end Criteria

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
