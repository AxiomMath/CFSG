module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG.Open

@[expose] def IsGoodInvolution {X : Type} [Group X] [Finite X] (z : X) : Prop :=
  orderOf z = 2 ∧ 2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({z} : Set X)) ∧
    ∃ H : Subgroup X, H ≤ Subgroup.centralizer ({z} : Set X) ∧ IsSimpleGroup H ∧
      3 ∣ Nat.card H ∧ Nat.card H ≠ 3

theorem map_centralizer_singleton {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (z : X) :
    (Subgroup.centralizer ({z} : Set X)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ z} : Set Y) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ h
    simpa using this
  · intro h
    apply φ.injective
    simpa using h

theorem IsGoodInvolution.map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (φ : X ≃* Y)
    {z : X} (h : IsGoodInvolution z) : IsGoodInvolution (φ z) := by
  obtain ⟨h2, hr, H, hHC, hHs, h3, h3'⟩ := h
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact h2, ?_, H.map φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← map_centralizer_singleton]
    exact hr.trans (CFSG.SectionRank.pRank_le_map (by norm_num) _ φ.injective _)
  · rw [← map_centralizer_singleton]
    exact Subgroup.map_mono hHC
  · exact MulEquiv.isSimpleGroup (H.equivMapOfInjective _ φ.injective).symm
  · rwa [Subgroup.card_map_of_injective φ.injective]
  · rwa [Subgroup.card_map_of_injective φ.injective]

@[expose] noncomputable def sylowMap {X Y : Type} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] (φ : X ≃* Y) (S : Sylow p X) : Sylow p Y :=
  S.mapSurjective (f := φ.toMonoidHom) φ.surjective

theorem coe_sylowMap {X Y : Type} [Group X] [Group Y] [Finite X] {p : ℕ} [Fact p.Prime]
    (φ : X ≃* Y) (S : Sylow p X) :
    (sylowMap φ S : Subgroup Y) = (S : Subgroup X).map φ.toMonoidHom :=
  Sylow.coe_mapSurjective _ _

@[expose] def centerPart {X : Type} [Group X] (R : Set X) (S : Subgroup X) : Set X :=
  {z | z ∈ R ∧ z ∈ S ∧ z ∈ Subgroup.centralizer (S : Set X)}

@[expose] def HasLongRootSet (X : Type) [Group X] [Finite X] : Prop :=
  ∃ R : Set X, (∀ α : X ≃* X, ∀ z ∈ R, α z ∈ R) ∧ (∀ z ∈ R, IsGoodInvolution z) ∧
    ∀ S : Sylow 2 X, Odd (centerPart R (S : Subgroup X)).ncard

theorem image_centerPart {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (R : Set X)
    (S : Subgroup X) :
    φ '' centerPart R S = centerPart (φ '' R) (S.map φ.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzR, hzS, hzC⟩, rfl⟩
    refine ⟨⟨z, hzR, rfl⟩, ⟨z, hzS, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hzC) s hs]
  · rintro ⟨⟨z, hzR, rfl⟩, ⟨w, hwS, hwz⟩, hzC⟩
    have hwz' : w = z := φ.injective hwz
    subst hwz'
    refine ⟨w, ⟨hzR, hwS, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply φ.injective
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hzC) (φ s) ⟨s, hs, rfl⟩

theorem HasLongRootSet.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X ≃* Y) (h : HasLongRootSet X) : HasLongRootSet Y := by
  obtain ⟨R, hinv, hgood, hodd⟩ := h
  refine ⟨φ '' R, ?_, ?_, ?_⟩
  · rintro α _ ⟨z, hz, rfl⟩
    refine ⟨((φ.trans α).trans φ.symm) z, hinv _ z hz, ?_⟩
    simp
  · rintro _ ⟨z, hz, rfl⟩
    exact (hgood z hz).map φ
  · intro S
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let S' : Sylow 2 X := sylowMap φ.symm S
    have hS' : (S' : Subgroup X) = (S : Subgroup Y).map φ.symm.toMonoidHom := coe_sylowMap _ _
    have hS : (S : Subgroup Y) = (S' : Subgroup X).map φ.toMonoidHom := by
      rw [hS', Subgroup.map_map]
      conv_lhs => rw [← Subgroup.map_id (S : Subgroup Y)]
      congr 1
      exact MonoidHom.ext fun y => (φ.apply_symm_apply y).symm
    rw [hS, ← image_centerPart, Set.ncard_image_of_injective _ φ.injective]
    exact hodd S'

theorem forall_good_of_sylow {X : Type} [Group X] [Finite X] (P : Sylow 2 X)
    (h : ∀ z ∈ (P : Subgroup X), z ∈ Subgroup.centralizer ((P : Subgroup X) : Set X) →
      orderOf z = 2 → IsGoodInvolution z) :
    ∀ S : Sylow 2 X, ∀ z ∈ (S : Subgroup X),
      z ∈ Subgroup.centralizer ((S : Subgroup X) : Set X) → orderOf z = 2 →
        IsGoodInvolution z := by
  intro S z hzS hzC hz2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S P
  have hmemP : ∀ y : X, y ∈ (P : Subgroup X) ↔ g⁻¹ * y * g ∈ (S : Subgroup X) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hw : IsGoodInvolution (g * z * g⁻¹) := by
    refine h _ ((hmemP _).mpr (by simpa [mul_assoc] using hzS)) ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hs := (hmemP y).mp hy
      have hc := (Subgroup.mem_centralizer_iff.mp hzC) _ hs
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
        _ = g * z * g⁻¹ * y := by group
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hz2
  have := hw.map (MulAut.conj g⁻¹)
  simpa [MulAut.conj_apply, mul_assoc] using this

section Omega

variable {X : Type} [Group X]

@[expose] def centerOmega (S : Subgroup X) : Subgroup X where
  carrier := {z | z ∈ S ∧ z ∈ Subgroup.centralizer (S : Set X) ∧ z ^ 2 = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨S.mul_mem ha.1 hb.1, Subgroup.mul_mem _ ha.2.1 hb.2.1, ?_⟩
    have hab : a * b = b * a := (Subgroup.mem_centralizer_iff.mp ha.2.1 b hb.1).symm
    rw [(Commute.mul_pow hab 2), ha.2.2, hb.2.2, one_mul]
  one_mem' := ⟨S.one_mem, Subgroup.one_mem _, one_pow 2⟩
  inv_mem' {a} ha := ⟨S.inv_mem ha.1, Subgroup.inv_mem _ ha.2.1, by rw [inv_pow, ha.2.2, inv_one]⟩

theorem mem_centerOmega {S : Subgroup X} {z : X} :
    z ∈ centerOmega S ↔ z ∈ S ∧ z ∈ Subgroup.centralizer (S : Set X) ∧ z ^ 2 = 1 :=
  Iff.rfl

end Omega

theorem odd_ncard_involutions_center {X : Type} [Group X] [Finite X] (h2 : 2 ∣ Nat.card X)
    (S : Sylow 2 X) :
    Odd {z : X | z ∈ (S : Subgroup X) ∧ z ∈ Subgroup.centralizer ((S : Subgroup X) : Set X) ∧
      orderOf z = 2}.ncard := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset : {z : X | z ∈ (S : Subgroup X) ∧ z ∈ Subgroup.centralizer ((S : Subgroup X) : Set X) ∧
      orderOf z = 2} = (centerOmega (S : Subgroup X) : Set X) \ {1} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, mem_centerOmega,
      Set.mem_singleton_iff, orderOf_eq_prime_iff]
    tauto
  set Ω := centerOmega (S : Subgroup X)
  have hΩp : IsPGroup 2 Ω := fun g => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, g.2.2.2, Subgroup.coe_one])⟩
  obtain ⟨k, hk⟩ := hΩp.exists_card_eq
  have hS1 : (S : Subgroup X) ≠ ⊥ := S.ne_bot_of_dvd_card h2
  have hZ : Subgroup.center (S : Subgroup X) ≠ ⊥ := by
    have : Nontrivial (S : Subgroup X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hS1
    exact (Subgroup.nontrivial_iff_ne_bot _).mp S.isPGroup'.center_nontrivial
  have hZ2 : 2 ∣ Nat.card (Subgroup.center (S : Subgroup X)) := by
    obtain ⟨n, hn⟩ := (S.isPGroup'.to_subgroup (Subgroup.center (S : Subgroup X))).exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hZ
    · rw [hn, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  have hwΩ : (((w : Subgroup.center (S : Subgroup X)) : (S : Subgroup X)) : X) ∈ Ω := by
    refine ⟨(w : (S : Subgroup X)).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have := Subgroup.mem_center_iff.mp w.2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    · have ho : orderOf (((w : Subgroup.center (S : Subgroup X)) : (S : Subgroup X)) : X) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
      have := pow_orderOf_eq_one (((w : Subgroup.center (S : Subgroup X)) : (S : Subgroup X)) : X)
      rwa [ho] at this
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have hbot := Subgroup.eq_bot_of_card_eq _ hk
    rw [hbot, Subgroup.mem_bot] at hwΩ
    have hw1 : w = 1 := Subtype.ext (Subtype.ext hwΩ)
    rw [hw1, orderOf_one] at hw
    omega
  rw [hset, Set.ncard_sdiff_singleton_of_mem Ω.one_mem, ← Nat.card_coe_set_eq]
  change Odd (Nat.card Ω - 1)
  rw [hk]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  refine ⟨2 ^ j - 1, ?_⟩
  rw [pow_succ]
  omega

theorem hasLongRootSet_of_forall {X : Type} [Group X] [Finite X] (h2 : 2 ∣ Nat.card X)
    (h : ∀ S : Sylow 2 X, ∀ z ∈ (S : Subgroup X),
      z ∈ Subgroup.centralizer ((S : Subgroup X) : Set X) → orderOf z = 2 → IsGoodInvolution z) :
    HasLongRootSet X := by
  let R : Set X := {z | orderOf z = 2 ∧ ∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧
    z ∈ Subgroup.centralizer ((S : Subgroup X) : Set X)}
  refine ⟨R, ?_, ?_, ?_⟩
  · rintro α z ⟨hz2, S, hzS, hzC⟩
    refine ⟨by rw [MulEquiv.orderOf_eq]; exact hz2, sylowMap α S, ?_, ?_⟩
    · rw [coe_sylowMap]
      exact ⟨z, hzS, rfl⟩
    · rw [coe_sylowMap, Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hzC) s hs]
  · rintro z ⟨hz2, S, hzS, hzC⟩
    exact h S z hzS hzC hz2
  · intro S
    have hset : centerPart R (S : Subgroup X) = {z : X | z ∈ (S : Subgroup X) ∧
        z ∈ Subgroup.centralizer ((S : Subgroup X) : Set X) ∧ orderOf z = 2} := by
      ext z
      constructor
      · rintro ⟨⟨hz2, -⟩, hzS, hzC⟩
        exact ⟨hzS, hzC, hz2⟩
      · rintro ⟨hzS, hzC, hz2⟩
        exact ⟨⟨hz2, S, hzS, hzC⟩, hzS, hzC⟩
    rw [hset]
    exact odd_ncard_involutions_center h2 S

theorem exists_sylow_inf {G : Type} [Group G] [Finite G] {I N : Subgroup G} (hIN : I ≤ N)
    (hN : N ≤ Subgroup.normalizer (I : Set G)) (T : Sylow 2 N) :
    ∃ S : Sylow 2 I, ((S : Subgroup I) : Set I) =
      {z : I | (z : G) ∈ (T : Subgroup N).map N.subtype} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I' : Subgroup N := I.subgroupOf N
  have hI' : I'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (I : Set G) := hN g.2
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hg _).mp hx⟩
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal T I'
  let e : I' ≃* I := Subgroup.subgroupOfEquivOfLe hIN
  refine ⟨sylowMap e P, ?_⟩
  ext z
  rw [coe_sylowMap, SetLike.mem_coe, Subgroup.mem_map_equiv, hP,
    Subgroup.mem_subgroupOf, Set.mem_ofPred_eq]
  constructor
  · intro hz
    exact ⟨_, hz, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    have : y = ((e.symm z : I') : N) := Subtype.ext (by change (y : G) = (z : G); exact hyz)
    rw [← this]
    exact hy

theorem exists_good_of_hasLongRootSet {G : Type} [Group G] [Finite G] {I N : Subgroup G}
    (hIN : I ≤ N) (hN : N ≤ Subgroup.normalizer (I : Set G)) (hI : HasLongRootSet I)
    (T : Sylow 2 N) :
    ∃ z : I, (z : G) ∈ (T : Subgroup N).map N.subtype ∧
      (T : Subgroup N).map N.subtype ≤ Subgroup.centralizer {(z : G)} ∧ IsGoodInvolution z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hinv, hgood, hodd⟩ := hI
  obtain ⟨S, hS⟩ := exists_sylow_inf hIN hN T
  set T' : Subgroup G := (T : Subgroup N).map N.subtype with hT'
  have hT'N : T' ≤ Subgroup.normalizer (I : Set G) := (Subgroup.map_subtype_le _).trans hN
  have hT'p : IsPGroup 2 T' := T.isPGroup'.map _
  have hmemS : ∀ z : I, z ∈ (S : Subgroup I) ↔ (z : G) ∈ T' := fun z => by
    rw [← SetLike.mem_coe, hS]
    rfl
  let act : MulDistribMulAction T' I := Subgroup.conjMulDistribMulActionOfLeNormalizer T' I hT'N
  have hsmul : ∀ (t : T') (z : I), ((t • z : I) : G) = (t : G) * z * (t : G)⁻¹ := fun t z =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit T' I hT'N t z
  let α : T' → I ≃* I := fun t => MulDistribMulAction.toMulEquiv I t
  have hα : ∀ t z, α t z = t • z := fun _ _ => rfl
  have key : ∀ (t : T') (s : I), (s : G) ∈ T' → ((t • s : I) : G) ∈ T' := fun t s hs => by
    rw [hsmul]
    exact T'.mul_mem (T'.mul_mem t.2 hs) (T'.inv_mem t.2)
  let Ω : SubMulAction T' I :=
    { carrier := centerPart R (S : Subgroup I)
      smul_mem' := by
        rintro t z ⟨hzR, hzS, hzC⟩
        refine ⟨by rw [← hα]; exact hinv _ z hzR, ?_, ?_⟩
        · rw [hmemS]
          exact key t z ((hmemS z).mp hzS)
        · rw [Subgroup.mem_centralizer_iff]
          intro s hs
          rw [SetLike.mem_coe] at hs
          have hs' : t⁻¹ • s ∈ (S : Subgroup I) := by
            rw [hmemS] at hs ⊢
            exact key t⁻¹ s hs
          have hcomm := (Subgroup.mem_centralizer_iff.mp hzC) _ hs'
          have h1 : t • (t⁻¹ • s * z) = t • (z * t⁻¹ • s) := by rw [hcomm]
          rwa [smul_mul', smul_mul', smul_inv_smul] at h1 }
  have hodd' := hodd S
  have hcard := hT'p.card_modEq_card_fixedPoints Ω
  have hΩcard : Nat.card Ω = (centerPart R (S : Subgroup I)).ncard :=
    (Nat.card_coe_set_eq _)
  rw [hΩcard] at hcard
  have hfix : (MulAction.fixedPoints T' Ω).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints T' Ω) = 0 := by rw [hne]; simp
    rw [h0] at hcard
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_iff.mpr hcard)
  obtain ⟨⟨z, hzΩ⟩, hzfix⟩ := hfix
  obtain ⟨hzR, hzS, -⟩ := id hzΩ
  refine ⟨z, (hmemS z).mp hzS, ?_, hgood z hzR⟩
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := congrArg (fun w : Ω => ((w : I) : G)) (hzfix ⟨t, ht⟩)
  simp only at h1
  change (((⟨t, ht⟩ : T') • z : I) : G) = z at h1
  rw [hsmul] at h1
  calc t * (z : G) = (t * z * t⁻¹) * t := by group
    _ = z * t := by rw [h1]

end CFSG.RankThree.PartTwo.KFacts.KS21
