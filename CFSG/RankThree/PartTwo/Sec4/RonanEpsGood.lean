module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHLift
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHBlock
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsL2pOrder

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projSL projSU)
open scoped commutatorElement

@[expose] def EpsQuot (X : Type) [Group X] : Prop :=
  IsTypeEps (X ⧸ CFSG.pCore 2 X) ∧ IsTypeEpsCube (X ⧸ CFSG.pCore 2 X)

theorem EpsQuot.congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : EpsQuot X) :
    EpsQuot Y :=
  ⟨isTypeEps_of_mulEquiv (quotPCoreCongr e).symm h.1,
    isTypeEpsCube_of_mulEquiv (quotPCoreCongr e).symm h.2⟩

theorem EpsQuot.of_surjective {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) (h : EpsQuot B) : EpsQuot A := by
  set g : A →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hkerg : g.ker = CFSG.pCore 2 A := by
    have hk : g.ker = (CFSG.pCore 2 B).comap f := by
      ext a
      simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [hk]
    refine le_antisymm (comap_pCore_two_le f hker) ?_
    intro a ha
    exact map_pCore_two_le f hf ⟨a, ha, rfl⟩
  have e : A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B :=
    (QuotientGroup.quotientMulEquivOfEq hkerg.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  exact ⟨isTypeEps_of_mulEquiv e h.1, isTypeEpsCube_of_mulEquiv e h.2⟩

theorem isSimpleGroup_of_isTypeEps' {X : Type} [Group X] (h : IsTypeEps X) : IsSimpleGroup X := by
  obtain ⟨p, f, hp, -, hf, ⟨-, ⟨ψ⟩⟩ | ⟨-, hq2, ⟨ψ⟩⟩⟩ := h
  · haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p f) (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact ψ.isSimpleGroup
  · haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible (n := 3) (p := p) (f := f)
      ⟨Fact.out, hf, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega⟩
    exact ψ.isSimpleGroup

theorem EpsQuot.nontrivial {X : Type} [Group X] [Finite X] (h : EpsQuot X) : Nontrivial X := by
  have h1 := le_card_of_isTypeEpsCube h.2
  have hq : Nontrivial (X ⧸ CFSG.pCore 2 X) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact (QuotientGroup.mk'_surjective (CFSG.pCore 2 X)).nontrivial

section Good

variable {S G' : Type} [Group S] [Group G']

@[expose] def GoodEps (C : Subgroup S) : Prop :=
  ∀ K : Subgroup S, K ≤ C → Group.IsPerfect K → (K.subgroupOf C).IsSubnormal → EpsQuot K → False

theorem GoodEps.of_map {C : Subgroup S} (f : S →* G') (hf : Function.Injective f)
    (h : GoodEps (C.map f)) : GoodEps C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  have eK : K ≃* K.map f := K.equivMapOfInjective f hf
  haveI : Group.IsPerfect (K.map f) := Group.IsPerfect.map f
  refine h (K.map f) (Subgroup.map_mono hKC) inferInstance ?_ (hT.congr eK)
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

theorem GoodEps.map_mulEquiv {C : Subgroup S} (φ : S ≃* G') (h : GoodEps C) :
    GoodEps (C.map φ.toMonoidHom) := by
  refine GoodEps.of_map φ.symm.toMonoidHom φ.symm.injective ?_
  rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id S by
    ext; simp, Subgroup.map_id]

theorem GoodEps.of_mulEquiv_centralizer (e : S ≃* G') {s : S}
    (h : GoodEps (Subgroup.centralizer ({e s} : Set G'))) :
    GoodEps (Subgroup.centralizer ({s} : Set S)) := by
  refine GoodEps.of_map e.toMonoidHom e.injective ?_
  have hm := RonanK429H.map_centralizer_singleton e.toMonoidHom e.injective s
  rw [MonoidHom.range_eq_top_of_surjective _ e.surjective, inf_top_eq] at hm
  rw [hm]
  exact h

theorem GoodEps.conj_of_normalizes {P : Subgroup S} {x k : S}
    (hk : ∀ g : S, g ∈ P ↔ k * g * k⁻¹ ∈ P)
    (h : GoodEps (Subgroup.centralizer ({x} : Set S) ⊓ P)) :
    GoodEps (Subgroup.centralizer ({k * x * k⁻¹} : Set S) ⊓ P) := by
  have hmap : (Subgroup.centralizer ({x} : Set S) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * x * k⁻¹} : Set S) ⊓ P := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      refine ⟨?_, (hk z).mp hzP⟩
      calc k * z * k⁻¹ * (k * x * k⁻¹) = k * (z * x) * k⁻¹ := by group
        _ = k * (x * z) * k⁻¹ := by rw [hzc]
        _ = k * x * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hwc, hwP⟩
      refine ⟨k⁻¹ * w * k, ⟨?_, (hk _).mpr (by simpa [mul_assoc] using hwP)⟩, by group⟩
      calc k⁻¹ * w * k * x = k⁻¹ * (w * (k * x * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * x * k⁻¹) * w) * k := by rw [hwc]
        _ = x * (k⁻¹ * w * k) := by group
  rw [← hmap]
  exact h.map_mulEquiv (MulAut.conj k)

theorem GoodEps.map_of_central [Finite S] (φ : S →* G') (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center S) (h2 : IsPGroup 2 φ.ker) {C : Subgroup S}
    (hC : φ.ker ≤ C) (h : GoodEps C) : GoodEps (C.map φ) := by
  intro K hKC hKp hKs hT
  haveI := hKp
  set Kt : Subgroup S := K.comap φ with hKt
  have hKtC : Kt ≤ C := by
    intro x hx
    obtain ⟨y, hyC, hy⟩ := hKC hx
    have : y⁻¹ * x ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
    have := C.mul_mem hyC (hC this)
    simpa using this
  have hmapKt : Kt.map φ = K := Subgroup.map_comap_eq_self_of_surjective hφ K
  set K1 : Subgroup S := ⁅Kt, Kt⁆ with hK1
  have hK1Kt : K1 ≤ Kt := Subgroup.commutator_le_self Kt
  have hmapK1 : K1.map φ = K := by
    rw [hK1, Subgroup.map_commutator, hmapKt]
    exact Subgroup.commutator_eq_self
  have hKtsup : ∀ x ∈ Kt, ∃ y ∈ K1, ∃ z ∈ φ.ker, x = y * z := by
    intro x hx
    have hφx : φ x ∈ K1.map φ := by rw [hmapK1]; exact hx
    obtain ⟨y, hy, hyx⟩ := hφx
    refine ⟨y, hy, y⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  haveI hK1p : Group.IsPerfect K1 := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le_self K1) ?_
    rw [hK1, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨a1, ha1, z, hz, rfl⟩ := hKtsup a ha
    obtain ⟨b1, hb1, w, hw, rfl⟩ := hKtsup b hb
    rw [commutatorElement_mul_central (hZ hz) (hZ hw)]
    exact Subgroup.commutator_mem_commutator ha1 hb1
  have hKts : (Kt.subgroupOf C).IsSubnormal := by
    set ψ : C →* C.map φ := φ.subgroupMap C
    have hcomap : (K.subgroupOf (C.map φ)).comap ψ = Kt.subgroupOf C := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hKt]
      rfl
    rw [← hcomap]
    exact hKs.comap ψ
  have hK1s : (K1.subgroupOf C).IsSubnormal := by
    have hle : K1.subgroupOf C ≤ Kt.subgroupOf C := fun x hx => hK1Kt hx
    refine Subgroup.IsSubnormal.trans hle ?_ hKts
    refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : ((g : Kt.subgroupOf C) : C) ∈ Kt.subgroupOf C := g.2
    rw [Subgroup.mem_subgroupOf] at hg
    have hnKt : (((n : Kt.subgroupOf C) : C) : S) ∈ Kt := hK1Kt hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e : ((g : C) : S) * ((n : C) : S) * ((g : C) : S)⁻¹ =
        ⁅((g : C) : S), ((n : C) : S)⁆ * ((n : C) : S) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact K1.mul_mem (Subgroup.commutator_mem_commutator hg hnKt) hn
  have hT1 : EpsQuot K1 := by
    let f : K1 →* K := (φ.comp K1.subtype).codRestrict K (fun x => by
      have : φ x ∈ K1.map φ := ⟨x, x.2, rfl⟩
      rw [hmapK1] at this
      exact this)
    have hf : Function.Surjective f := by
      intro k
      have hk : (k : G') ∈ K1.map φ := by rw [hmapK1]; exact k.2
      obtain ⟨y, hy, hyk⟩ := hk
      exact ⟨⟨y, hy⟩, Subtype.ext hyk⟩
    have hker : IsPGroup 2 f.ker := by
      let ι : f.ker →* φ.ker := (K1.subtype.comp f.ker.subtype).codRestrict φ.ker (fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx ⊢
        exact congrArg Subtype.val hx)
      refine IsPGroup.of_injective h2 ι ?_
      intro x y hxy
      have h' := congrArg (fun t : φ.ker => (t : S)) hxy
      exact Subtype.ext (Subtype.ext h')
    exact EpsQuot.of_surjective f hf hker hT
  exact h K1 (hK1Kt.trans hKtC) hK1p hK1s hT1

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem noCfgSEps_of_goodEps_model [Finite S] (e : S ≃* G') (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ x : G', orderOf x = 3 → GoodEps (Subgroup.centralizer ({x} : Set G'))) :
    NoCfgSEps S := by
  intro A σ K hc
  obtain ⟨s, rfl⟩ := cubeInner_of_not_three_dvd_card_outer hout σ hc.pow_three
  have hinj := conj_injective_of_center_eq_bot hZ
  have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hc.pow_three, map_one])
  have hs1 : s ≠ 1 := fun h1 => hc.ne_one (by rw [h1, map_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hs' : orderOf (e s) = 3 := by rwa [MulEquiv.orderOf_eq]
  have hgood := GoodEps.of_mulEquiv_centralizer e (h (e s) hs')
  rw [← autFix_conj] at hgood
  exact hgood K hc.le_autFix hc.isPerfect hc.isSubnormal ⟨hc.isType, isTypeEpsCube_of_cfgSEps hc⟩

end Good

section Block

variable {G M : Type} [Group G] [Group M] [Finite G] [Finite M]

theorem false_of_quasisimple_block {C K : Subgroup G} (hKC : K ≤ C) [hKp : Group.IsPerfect K]
    (hKs : (K.subgroupOf C).IsSubnormal) (β : G →* M)
    (hβ : Function.Injective (β.comp K.subtype)) {Q : Subgroup M} (hQC : Q ≤ C.map β)
    (hKQ : K.map β ≤ Q) (hQ : IsQuasisimple Q) {z : M} (hzQ : z ∈ Q)
    (hz : ∀ q ∈ Q, q * z = z * q) (hz3 : orderOf z = 3) (hT : EpsQuot K) : False := by
  haveI : Nontrivial K := hT.nontrivial
  have hs := isSubnormal_subgroupOf_of_le hQC hKQ (isSubnormal_map_subgroupOf hKC β hKs)
  rcases Res429.eq_top_or_le_center_of_isSubnormal hQ hs with htop | hcen
  · have hzK : z ∈ K.map β := Subgroup.subgroupOf_eq_top.mp htop hzQ
    obtain ⟨k, hkK, hkz⟩ := hzK
    have hkc : ∀ k' : K, (⟨k, hkK⟩ : K) * k' = k' * ⟨k, hkK⟩ := by
      intro k'
      apply hβ
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Subgroup.coe_mul, map_mul, hkz]
      exact (hz (β k') (hKQ ⟨k', k'.2, rfl⟩)).symm
    have hko : orderOf (⟨k, hkK⟩ : K) = 3 := by
      rw [← hz3, ← hkz]
      exact (orderOf_injective _ hβ ⟨k, hkK⟩).symm
    have hcen : (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k, hkK⟩ : K ⧸ CFSG.pCore 2 K) ∈
        Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
      rw [← map_mul, ← map_mul, hkc k']
    have hne : (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k, hkK⟩ : K ⧸ CFSG.pCore 2 K) ≠ 1 := by
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨_, h1⟩
      have hn' : (⟨k, hkK⟩ : K) ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hd : orderOf (⟨k, hkK⟩ : K) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
      rw [hko] at hd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)) hd
    rw [center_eq_bot_of_isTypeEps hT.1, Subgroup.mem_bot] at hcen
    exact hne hcen
  · have hab : ∀ a b : K, a * b = b * a := by
      intro a b
      apply hβ
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Subgroup.coe_mul, map_mul]
      have ha : (⟨β a, hKQ ⟨a, a.2, rfl⟩⟩ : Q) ∈ Subgroup.center Q := hcen (by
        show β a ∈ K.map β
        exact ⟨a, a.2, rfl⟩)
      have := Subgroup.mem_center_iff.mp ha ⟨β b, hKQ ⟨b, b.2, rfl⟩⟩
      exact (congrArg Subtype.val this).symm
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hab)

theorem false_of_quasisimple_block_on {C K : Subgroup G} (hKC : K ≤ C) [hKp : Group.IsPerfect K]
    (hKs : (K.subgroupOf C).IsSubnormal) (β : C →* M)
    (hβ : Function.Injective (β.comp (Subgroup.inclusion hKC))) {Q : Subgroup M}
    (hQC : Q ≤ β.range) (hKQ : ∀ k : K, β (Subgroup.inclusion hKC k) ∈ Q) (hQ : IsQuasisimple Q)
    {z : M} (hzQ : z ∈ Q) (hz : ∀ q ∈ Q, q * z = z * q) (hz3 : orderOf z = 3)
    (hT : EpsQuot K) : False := by
  set K' : Subgroup C := K.subgroupOf C with hK'
  let e : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hs : (K'.subgroupOf (⊤ : Subgroup C)).IsSubnormal := hKs.comap (⊤ : Subgroup C).subtype
  have hcomp : ∀ a : K', (β.comp K'.subtype) a = (β.comp (Subgroup.inclusion hKC)) (e a) :=
    fun a => rfl
  have hinj : Function.Injective (β.comp K'.subtype) := fun a b hab =>
    e.injective (hβ (by rw [← hcomp, ← hcomp]; exact hab))
  have hQC' : Q ≤ (⊤ : Subgroup C).map β := by
    rw [← MonoidHom.range_eq_map]
    exact hQC
  have hKQ' : K'.map β ≤ Q := by
    rintro _ ⟨c, hc, rfl⟩
    exact hKQ ⟨c, hc⟩
  exact false_of_quasisimple_block (G := C) le_top hs β hinj hQC' hKQ' hQ hzQ hz hz3
    (hT.congr e.symm)

end Block

section Component

variable {C : Type} [Group C] [Finite C]

theorem subsingleton_of_isPerfect_of_isPGroup' {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] {p : ℕ} [Fact p.Prime] (h : IsPGroup p X) : Subsingleton X := by
  by_contra hX
  rw [not_subsingleton_iff_nontrivial] at hX
  haveI : Group.IsNilpotent X := h.isNilpotent
  exact Group.IsPerfect.not_isSolvable X inferInstance

theorem eq_or_commutator_eq_bot_of_normal_quasisimple {K Q : Subgroup C} [hKp : Group.IsPerfect K]
    (hKs : K.IsSubnormal) (hKsimple : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (hQn : Q.Normal)
    (hQq : IsQuasisimple Q) : K = Q ∨ ⁅Q, K⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp : IsComponent Q := ⟨hQq, hQn.isSubnormal⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hKs with hQK | hc
  · left
    set Q' : Subgroup K := Q.subgroupOf K with hQ'
    haveI hQ'n : Q'.Normal := hQn.subgroupOf K
    set π : K →* K ⧸ CFSG.pCore 2 K := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
    have hmn : (Q'.map π).Normal := hQ'n.map π (QuotientGroup.mk'_surjective _)
    haveI := hKsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q'.map π) with hb | ht
    · exfalso
      have hle : Q' ≤ CFSG.pCore 2 K := by
        rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hb
        exact hb
      have h2 : IsPGroup 2 Q' := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).to_le hle
      have e : Q' ≃* Q := Subgroup.subgroupOfEquivOfLe hQK
      have h2Q : IsPGroup 2 Q := h2.of_equiv e
      haveI : Group.IsPerfect Q := hQq.1
      obtain ⟨a, b, hab⟩ := hQq.2.2
      have : Subsingleton Q := subsingleton_of_isPerfect_of_isPGroup' h2Q
      have : Subsingleton (Q ⧸ Subgroup.center Q) :=
        (QuotientGroup.mk'_surjective (Subgroup.center Q)).subsingleton
      exact hab (Subsingleton.elim _ _)
    ·
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' Q').comp (CFSG.pCore 2 K).subtype) := by
        intro x
        obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective Q' x
        have hk : π k ∈ Q'.map π := by rw [ht]; exact Subgroup.mem_top _
        obtain ⟨q, hq, hqk⟩ := hk
        have hqk' : q⁻¹ * k ∈ CFSG.pCore 2 K := by
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hqk
          exact hqk
        refine ⟨⟨q⁻¹ * k, hqk'⟩, ?_⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        have e1 : (q⁻¹ * k)⁻¹ * k = k⁻¹ * q * k⁻¹⁻¹ := by group
        rw [e1]
        exact hQ'n.conj_mem q hq k⁻¹
      have h2 : IsPGroup 2 (K ⧸ Q') :=
        (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).of_surjective _ hsurj
      haveI : Group.IsPerfect (K ⧸ Q') :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Q') (QuotientGroup.mk'_surjective _)
      have hsub : Subsingleton (K ⧸ Q') := subsingleton_of_isPerfect_of_isPGroup' h2
      have htop : Q' = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
      refine le_antisymm (fun k hk => ?_) hQK
      have : (⟨k, hk⟩ : K) ∈ Q' := by rw [htop]; exact Subgroup.mem_top _
      exact this
  · exact Or.inr hc

end Component

theorem false_of_epsQuot_sl2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hF : Nat.card F = p) {X : Type} [Group X] [Finite X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hT : EpsQuot X) : False := by
  have h4 : 4 ≤ Nat.card F := by omega
  have hQ : IsQuasisimple X :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4)
  have hchar : ringChar F ≠ 2 := by
    haveI : Fact p.Prime := ⟨hp⟩
    have := Fintype.ofFinite F
    have hc : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
    rw [ringChar.eq F p]
    omega
  have hZ2 : Nat.card (Subgroup.center X) = 2 := by
    rw [← CFSG.GH74.GLS.Stage2.Local.card_center_SL2_eq_two' hchar]
    exact Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have hO2 : CFSG.pCore 2 X = Subgroup.center X := by
    refine le_antisymm (pCore_two_le_center' hQ) ?_
    apply le_sSup
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨inferInstance, IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])⟩
  have hcardX : Nat.card X = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_SL_two, hF]
  have h2 : 2 * Nat.card (X ⧸ CFSG.pCore 2 X) = p * (p ^ 2 - 1) := by
    rw [← hcardX, (CFSG.pCore 2 X).card_eq_card_quotient_mul_card_subgroup, hO2, hZ2, mul_comm]
  exact not_isTypeEpsCube_of_two_mul_card_eq_psl2_prime hp h5 h2 hT.2

end CFSG.RankThree.PartTwo.Sec4.RonanEps
