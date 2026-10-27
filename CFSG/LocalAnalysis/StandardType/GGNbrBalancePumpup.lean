module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyElement
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification

@[expose] noncomputable def ggLayerClosure {G : Type} [Group G] (p : ℕ) (Y J : Subgroup G) :
    Subgroup G :=
  ⨆ (a : G) (_ : a ∈ CFSG.Open.lBalancePLayer p Y), J.map (MulAut.conj a⁻¹).toMonoidHom

@[expose] def GGPumpupInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime →
    (∀ P : Subgroup G, P ≠ ⊥ → IsPGroup p P →
      CFSG.Open.lBalanceIsKGroup ↥(Subgroup.normalizer (P : Set G))) →
    ∀ x y : G, x * y = y * x → orderOf x = p → orderOf y = p →
    ∀ J : Subgroup G, CFSG.Open.lBalanceIsPComponent p
        (CFSG.Open.lBalancePLayer p
          (CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({x} : Set G)) ⊓
            Subgroup.centralizer ({y} : Set G))) J →
      (CFSG.Open.lBalanceIsPComponent p
          (CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({y} : Set G)))
          (ggLayerClosure p (Subgroup.centralizer ({y} : Set G)) J) ∧
        x ∈ Subgroup.normalizer
          (ggLayerClosure p (Subgroup.centralizer ({y} : Set G)) J : Set G)) ∨
      ∃ A : Subgroup G, CFSG.Open.lBalanceIsPComponent p
          (CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({y} : Set G))) A ∧
        x ∉ Subgroup.normalizer (A : Set G) ∧
        ggLayerClosure p (Subgroup.centralizer ({y} : Set G)) J =
          ⨆ (i : ℕ) (_ : i < p), A.map (MulAut.conj (x ^ i)).toMonoidHom

section Basic

open scoped commutatorElement

variable {G : Type} [Group G]

theorem center_eq_bot_of_simple_of_nonabelian [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

theorem lBalanceIsKGroup_normalizer_of_kProper [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP1 : P ≠ ⊥) (hP : IsPGroup p P) :
    CFSG.Open.lBalanceIsKGroup ↥(Subgroup.normalizer (P : Set G)) := by
  apply lBalanceIsKGroup_of_kProper hK
  intro htop
  have : Fact p.Prime := ⟨hp⟩
  have hn : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact hP1 h
  · subst h
    have hG : IsPGroup p G := hP.of_equiv Subgroup.topEquiv
    have : Nontrivial (Subgroup.center G) := hG.center_nontrivial
    rw [center_eq_bot_of_simple_of_nonabelian hnab] at this
    exact not_nontrivial _ this

theorem lBalancePLayer_le (p : ℕ) (Y : Subgroup G) : CFSG.Open.lBalancePLayer p Y ≤ Y :=
  sSup_le fun _ hK => LBalance.subnormal_le hK.1

theorem lBalancePLayer_subgroupOf_normal (p : ℕ) (Y : Subgroup G) :
    ((CFSG.Open.lBalancePLayer p Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (lBalancePLayer_le p Y)]
  intro a g ha hg
  rw [← largeEvenPLayer_eq_lBalancePLayer] at ha ⊢
  exact conj_mem_largeEvenPLayer hg ha

theorem lBalanceIsPComponent_of_normal [Finite G] {p : ℕ} [Fact p.Prime] {Y M L : Subgroup G}
    (hYM : Y ≤ M) [(Y.subgroupOf M).Normal] (hLY : L ≤ Y)
    (hL : CFSG.Open.lBalanceIsPComponent p Y L) : CFSG.Open.lBalanceIsPComponent p M L := by
  have h1 := (LBalance.pComponent_nested_iff p Y M L hYM hLY).2 hL
  have h2 := LBalance.pComponent_normal_extension p (Y.subgroupOf M) (L.subgroupOf M) h1
  exact (LBalance.pComponent_nested_iff p M M L le_rfl (hLY.trans hYM)).1
    (by rw [Subgroup.subgroupOf_self]; exact h2)

theorem mem_normalizer_of_commutator_le_self {A : Subgroup G} {x : G}
    (h : (⁅A, Subgroup.zpowers x⁆ : Subgroup G) ≤ A) : x ∈ Subgroup.normalizer (A : Set G) := by
  have key : ∀ z ∈ Subgroup.zpowers x, ∀ a ∈ A, z * a * z⁻¹ ∈ A := fun z hz a ha => by
    have h1 : ⁅a⁻¹, z⁆ ∈ A := h (Subgroup.commutator_mem_commutator (A.inv_mem ha) hz)
    have h2 : z * a * z⁻¹ = a * ⁅a⁻¹, z⁆ := by rw [commutatorElement_def]; group
    rw [h2]
    exact A.mul_mem ha h1
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key x (Subgroup.mem_zpowers x) a, fun ha => ?_⟩
  have h3 := key x⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) _ ha
  rwa [inv_inv, show x⁻¹ * (x * a * x⁻¹) * x = a by group] at h3

variable [Finite G]

theorem largeEvenPPrimeCoreOf_le_of_isSubnormal {p : ℕ} [Fact p.Prime] {A X : Subgroup G}
    (hA : IsSubnormal A X) :
    LargeEvenPPrimeCoreOf p A ≤ CFSG.Open.lBalancePrimeCore p X := by
  induction hA with
  | refl A =>
    rw [LBalance.primeCore_eq_map]
    exact le_rfl
  | @step A M X hAM hn _ ih =>
    refine le_trans ?_ ih
    have hOM : LargeEvenPPrimeCoreOf p A ≤ M := (Subgroup.map_subtype_le _).trans hAM
    have hle : (LargeEvenPPrimeCoreOf p A).subgroupOf M ≤ LargeEvenPPrimeCore p ↥M := by
      apply le_sSup
      refine ⟨?_, ?_⟩
      · rw [Subgroup.normal_subgroupOf_iff hOM]
        intro o m ho hm
        have hmA : m ∈ Subgroup.normalizer (A : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hn hm
        exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_largeEvenPPrimeCoreOf hmA) o).mp ho
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOM).toEquiv, LargeEvenPPrimeCoreOf,
          Subgroup.card_map_of_injective A.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
    calc LargeEvenPPrimeCoreOf p A
        = ((LargeEvenPPrimeCoreOf p A).subgroupOf M).map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hOM).symm
      _ ≤ LargeEvenPPrimeCoreOf p M := Subgroup.map_mono hle

omit [Finite G] in
theorem exists_le_iff_commutator_le_lBalancePrimeCore (p : ℕ) {X : Subgroup G} {b : G}
    (hb : b ∈ X) : ∃ W : Subgroup G,
      (∀ H : Subgroup G, H ≤ X →
        (⁅H, Subgroup.zpowers b⁆ : Subgroup G) ≤ CFSG.Open.lBalancePrimeCore p X → H ≤ W) ∧
      (∀ H : Subgroup G, H ≤ W →
        (⁅H, Subgroup.zpowers b⁆ : Subgroup G) ≤ CFSG.Open.lBalancePrimeCore p X) := by
  set q := QuotientGroup.mk' (CFSG.pPrimeCore p ↥X)
  set b' : ↥X := ⟨b, hb⟩
  refine ⟨((Subgroup.centralizer ({q b'} : Set (↥X ⧸ CFSG.pPrimeCore p ↥X))).comap q).map
    X.subtype, fun H hHX hH h hh => ?_, fun H hHW => ?_⟩
  · have hc : ⁅h, b⁆ ∈ CFSG.Open.lBalancePrimeCore p X :=
      hH (Subgroup.commutator_mem_commutator hh (Subgroup.mem_zpowers b))
    rw [LBalance.primeCore_eq_map] at hc
    obtain ⟨c, hc, hceq⟩ := hc
    have hc' : c = ⁅(⟨h, hHX hh⟩ : ↥X), b'⁆ := Subtype.ext hceq
    refine ⟨⟨h, hHX hh⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← hc']
    exact (QuotientGroup.eq_one_iff _).mpr hc
  · rw [Subgroup.commutator_le]
    intro h hh z hz
    obtain ⟨w, hw, rfl⟩ := hHW hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hw
    have hcomm : q w * q (b' ^ k) = q (b' ^ k) * q w := by
      rw [map_zpow]
      exact (Commute.zpow_right hw k).eq
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement] at hcomm
    have hmem := (QuotientGroup.eq_one_iff _).mp hcomm
    rw [LBalance.primeCore_eq_map]
    exact ⟨_, hmem, rfl⟩

end Basic


section Main

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggLayerClosure_centralizer_eq (p : ℕ) (y : G) (J : Subgroup G) :
    ggLayerClosure p (Subgroup.centralizer ({y} : Set G)) J =
      ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G))),
        J.map (MulAut.conj a⁻¹).toMonoidHom := by
  rw [ggLayerClosure, largeEvenPLayer_eq_lBalancePLayer]

omit [Finite G] in
theorem le_ggLayerClosure (p : ℕ) (Y J : Subgroup G) : J ≤ ggLayerClosure p Y J := by
  refine le_trans (le_of_eq ?_) (le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl)
  rw [inv_one, map_one]
  exact (Subgroup.map_id J).symm

theorem facts_of_closure_pair {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) {d : G}
    (hD : D = Subgroup.closure {x, d}) : d ∈ B ∧ x * d = d * x ∧ d ≠ 1 ∧ d ^ p = 1 := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hdD : d ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hdB : d ∈ B := hDJ.1.1 hdD
  refine ⟨hdB, congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨d, hdB⟩), ?_,
    hS.1.1.2 d hdB⟩
  rintro rfl
  have hD' : D = Subgroup.zpowers x := by
    rw [hD, closure_pair_eq_sup, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
  have hcard := hDJ.1.2.2.1
  rw [hD', Nat.card_zpowers] at hcard
  have hle := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
  rw [hcard] at hle
  nlinarith [hp.two_le]

theorem eq_closure_pair_of_mem {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) {d : G} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) : D = Subgroup.closure {x, d} := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hox : orderOf x = p := orderOf_eq_prime (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hle : Subgroup.closure {x, d} ≤ D := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hDJ.1.2.2.2.1
    · exact hdD
  have hlt : Subgroup.zpowers x < Subgroup.closure {x, d} := by
    refine lt_of_le_of_ne ?_ fun h => hdx ?_
    · rw [closure_pair_eq_sup]
      exact le_sup_left
    · rw [h]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hox] at h1
  have h2 : Nat.card (Subgroup.closure {x, d} : Subgroup G) ∣ p ^ 2 :=
    hDJ.1.2.2.1 ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp h2
  have hk2 : k = 2 := by
    interval_cases k
    · rw [hk', pow_zero] at h1
      exact absurd h1 (by have := hp.one_lt; omega)
    · rw [hk', pow_one] at h1
      exact absurd h1 (lt_irrefl p)
    · rfl
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hk', hk2, hDJ.1.2.2.1]

theorem lBalanceIsPComponent_pLayer_of_stdSub {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {d : G} (hD : D = Subgroup.closure {x, d}) :
    CFSG.Open.lBalanceIsPComponent p
      (CFSG.Open.lBalancePLayer p
        (CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({x} : Set G)) ⊓
          Subgroup.centralizer ({d} : Set G))) J := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hJ0 := isComponentOf_inf_centralizer_of_stdSub hI.2.2.2.2.2.2.1 hDJ.1 hD
  obtain ⟨hJL, hLc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
  have hLLx : L ≤ CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({x} : Set G)) :=
    le_sSup ((largeEvenPComponent_iff_lBalance p _ L).1 hLc).2
  set Y := CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({x} : Set G)) ⊓
    Subgroup.centralizer ({d} : Set G) with hYdef
  have hJY : J ≤ Y := le_inf (hJL.trans hLLx) (hJ0.1.trans inf_le_left)
  have hYle : Y ≤ Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (lBalancePLayer_le p _))
  have hJp : CFSG.Open.lBalanceIsPComponent p Y J :=
    lBalanceIsPComponent_of_isComponentOf
      (LocalAnalysis.ComponentInitial.isComponentOf_of_le hJ0 hJY hYle)
      (not_le_lBalancePrimeCore_of_dvd hpJ)
  have : ((CFSG.Open.lBalancePLayer p Y).subgroupOf Y).Normal :=
    lBalancePLayer_subgroupOf_normal p Y
  exact LBalance.Asm.pComponent_relative_normal_restriction p _ Y J (lBalancePLayer_le p Y) hJp
    (le_sSup hJp)


theorem ggNbr_of_cycled {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) (hpJ : p ∣ Nat.card J)
    {d : G} (hD : D = Subgroup.closure {x, d}) {A : Subgroup G}
    (hA : CFSG.Open.lBalanceIsPComponent p
      (CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({d} : Set G))) A)
    (hxA : x ∉ Subgroup.normalizer (A : Set G))
    (hK : ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J =
      ⨆ (i : ℕ) (_ : i < p), A.map (MulAut.conj (x ^ i)).toMonoidHom) :
    GGNbr p B x D J d A := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  obtain ⟨hdB, hxd, hd1, -⟩ := facts_of_closure_pair hI hDJ hD
  set X := Subgroup.centralizer ({d} : Set G) with hXdef
  have hLdX := lBalancePLayer_le p X
  have : ((CFSG.Open.lBalancePLayer p X).subgroupOf X).Normal :=
    lBalancePLayer_subgroupOf_normal p X
  have hAX : CFSG.Open.lBalanceIsPComponent p X A :=
    lBalanceIsPComponent_of_normal hLdX (LBalance.subnormal_le hA.1) hA
  have hAXle : A ≤ X := LBalance.subnormal_le hAX.1
  have hA' : LargeEvenPComponent p X A :=
    (largeEvenPComponent_iff_lBalance p X A).2 ⟨hAXle, hAX⟩
  have hAsn : IsSubnormal A X := (AssemblyBPredicates.isSubnormal_iff_open A X).2 hAX.1
  have hxX : x ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hxd
  have hON : X ≤ Subgroup.normalizer (CFSG.Open.lBalancePrimeCore p X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (LBalance.primeCore_le p X)).mp
      (LBalance.primeCore_normal p X)
  have hdA : d ∈ Subgroup.centralizer (A : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hAXle ha)
  have hzdA : Subgroup.zpowers d ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hdA
  have hJX : J ≤ X :=
    (isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hD).1.trans inf_le_left
  refine ⟨⟨hS.1, hdB, hd1, hAXle, hA', fun b => ⟨?_, ?_⟩⟩, hD, ?_, ?_⟩
  · rintro ⟨hbB, hbA, hbO⟩
    have hbX : b ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨b, hbB⟩ : ↥B) ⟨d, hdB⟩))
    have hxb : Commute x b :=
      congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨b, hbB⟩)
    obtain ⟨W, hW1, hW2⟩ := exists_le_iff_commutator_le_lBalancePrimeCore p hbX
    have hAO : LargeEvenPPrimeCoreOf p A ≤ CFSG.Open.lBalancePrimeCore p X :=
      largeEvenPPrimeCoreOf_le_of_isSubnormal hAsn
    have hKW : ⨆ (i : ℕ) (_ : i < p), A.map (MulAut.conj (x ^ i)).toMonoidHom ≤ W := by
      refine iSup₂_le fun i _ => hW1 _ ?_ ?_
      · rw [← map_conj_eq_of_mem (Subgroup.pow_mem _ hxX i)]
        exact Subgroup.map_mono hAXle
      · have hxib : x ^ i * b = b * x ^ i := (hxb.pow_left i).eq
        rw [← zpowers_map_conj_of_commute hxib, ← Subgroup.map_commutator,
          ← map_conj_eq_of_mem_normalizer (hON (Subgroup.pow_mem _ hxX i))]
        exact Subgroup.map_mono (hbO.trans hAO)
    have hJb : (⁅J, Subgroup.zpowers b⁆ : Subgroup G) ≤ CFSG.Open.lBalancePrimeCore p X :=
      hW2 J ((le_ggLayerClosure p X J).trans (hK ▸ hKW))
    have hbJ : b ∈ Subgroup.centralizer (J : Set G) :=
      mem_centralizer_of_commutator_le_coprime hp hDJ.1.2.2.2.2.2.1.2.2 hpJ
        (LBalance.primeCore_coprime p X) (hJX.trans hON)
        (le_normalizer_of_stdSub hS hI.2.2.2.2.2.2.2 hDJ.1 hbB) hJb
    have hbD : b ∈ D := by
      rw [hDJ.1.2.2.2.2.2.2]
      exact ⟨hbB, hbJ⟩
    have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.zpowers_le]
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ((Commute.zpow_left hxd k).symm).eq.symm
    have hb' : b ∈ ((Subgroup.zpowers x : Set G) * (Subgroup.zpowers d : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hdN, ← closure_pair_eq_sup, ← hD]
      exact hbD
    obtain ⟨u, hu, e, he, rfl⟩ := hb'
    have heN : e ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ (hzdA he)
    have huN : u ∈ Subgroup.normalizer (A : Set G) := by
      have h := Subgroup.mul_mem _ hbA (Subgroup.inv_mem _ heN)
      simpa using h
    have hu1 : u = 1 := by
      by_contra hu1
      exact hxA ((Subgroup.zpowers_le.mpr huN)
        (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp hu hu1))
    simp only [hu1, one_mul]
    exact he
  · intro hb
    have hbA : b ∈ Subgroup.centralizer (A : Set G) := hzdA hb
    refine ⟨Subgroup.zpowers_le.mpr hdB hb, Subgroup.centralizer_le_normalizer _ hbA, ?_⟩
    have hbot : (⁅A, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.zpowers_le.mpr hbA
    rw [hbot]
    exact bot_le
  · rw [← ggLayerClosure_centralizer_eq, hK]
    refine le_trans (le_of_eq ?_) (le_iSup₂_of_le 0 hp.pos le_rfl)
    rw [pow_zero, map_one]
    exact (Subgroup.map_id A).symm
  · intro h
    exact hxA (mem_normalizer_of_commutator_le_self (h.trans (Subgroup.map_subtype_le _)))

theorem pumpup_of_stdSub (hPU : GGPumpupInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {d : G} (hD : D = Subgroup.closure {x, d}) :
    LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G))
        (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) ∧
      J ≤ ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J ∧
      x ∈ Subgroup.normalizer (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J : Set G) ∧
      (GGNbr p B x D J d (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) ∨
        (⁅ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J, Subgroup.zpowers x⁆ :
            Subgroup G) ≤
          LargeEvenPPrimeCoreOf p (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J)) := by
  have : IsSimpleGroup G := hI.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hI.2.1
  have hKP : KProper InCatalog G := hI.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hxB : x ∈ B := hS.2.1
  have hox : orderOf x = p := orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1
  obtain ⟨hdB, hxd, hd1, hdp⟩ := facts_of_closure_pair hI hDJ hD
  have hod : orderOf d = p := orderOf_eq_prime hdp hd1
  set X := Subgroup.centralizer ({d} : Set G) with hXdef
  have : ((CFSG.Open.lBalancePLayer p X).subgroupOf X).Normal :=
    lBalancePLayer_subgroupOf_normal p X
  rcases hPU G p hp (fun P hP1 hP => lBalanceIsKGroup_normalizer_of_kProper hnab hKP hp hP1 hP)
      x d hxd hox hod J (lBalanceIsPComponent_pLayer_of_stdSub hI hDJ hpJ hD) with
    ⟨hK, hxK⟩ | ⟨A, hA, hxA, hKA⟩
  · have hKX : CFSG.Open.lBalanceIsPComponent p X (ggLayerClosure p X J) :=
      lBalanceIsPComponent_of_normal (lBalancePLayer_le p X) (LBalance.subnormal_le hK.1) hK
    have hK' : LargeEvenPComponent p X (ggLayerClosure p X J) :=
      (largeEvenPComponent_iff_lBalance p X _).2 ⟨LBalance.subnormal_le hKX.1, hKX⟩
    refine ⟨hK', le_ggLayerClosure p X J, hxK, ?_⟩
    by_cases hc : (⁅ggLayerClosure p X J, Subgroup.zpowers x⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (ggLayerClosure p X J)
    · exact Or.inr hc
    · exact Or.inl (ggNbr_of_pComponent hI hDJ hpJ hD hK' (le_ggLayerClosure p X J)
        (ggLayerClosure_centralizer_eq p d J).le hc)
  · exfalso
    have hnbr := ggNbr_of_cycled hI hDJ hpJ hD hA hxA hKA
    exact hxA ((hst.2.2.1 d A (isNeighborOf_of_ggNbr hDJ hnbr)).1 hxB)

theorem exists_pComponent_of_stdSub (hPU : GGPumpupInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    ∃ A : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) A ∧ J ≤ A ∧
      x ∈ Subgroup.normalizer (A : Set G) := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  by_cases hdx : d ∈ Subgroup.zpowers x
  · obtain ⟨hJL, hLc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
    have hzd : Subgroup.zpowers d = Subgroup.zpowers x := by
      refine le_antisymm (Subgroup.zpowers_le.mpr hdx) (Subgroup.zpowers_le.mpr ?_)
      exact mem_zpowers_of_mem_zpowers_of_ne_one hp (hS.1.1.2 x hS.2.1) hdx hd1
    refine ⟨L, ?_, hJL, ?_⟩
    · rw [centralizer_singleton_eq_of_zpowers_eq hzd]
      exact hLc
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  · obtain ⟨hK, hJK, hxK, -⟩ :=
      pumpup_of_stdSub hPU hI hDJ hpJ (eq_closure_pair_of_mem hI hDJ hdD hdx)
    exact ⟨_, hK, hJK, hxK⟩

end Main

end CFSG.StandardType

end
