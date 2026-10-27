module

import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Adapters.GeneralizedFitting
public import CFSG.Walter.Bender1970.S1.QdNotInvolved
public import CFSG.Walter.Bender1970.S3.CoreExchange
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.AmbientSylowZJNormalizer

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.Glauberman

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylow_two_mem {t : G} (ht : orderOf t = 2) :
    ∃ T : Sylow 2 G, t ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp' : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨T, hT⟩ := hp'.exists_le_sylow
  exact ⟨T, hT (Subgroup.mem_zpowers t)⟩

theorem BenderCounterexample.exists_mem_benderM_ne (hG : BenderCounterexample G) {s : G}
    (hs : orderOf s = 2) {H : Subgroup G} (hsH : benderM s ≠ {H}) :
    ∃ M ∈ benderM s, M ≠ H := by
  by_contra hcon
  push Not at hcon
  apply hsH
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    omega
  obtain ⟨M, hM⟩ := hG.benderM_nonempty hs1
  ext X
  refine ⟨fun hX => hcon X hX, fun hX => ?_⟩
  rw [Set.mem_singleton_iff] at hX
  subst hX
  rw [← hcon M hM]
  exact hM

theorem rank_map_conj (g : G) (X : Subgroup G) :
    rank (X.map (MulAut.conj g).toMonoidHom) = rank X := by
  have key : ∀ (g : G) (X : Subgroup G), rank X ≤ rank (X.map (MulAut.conj g).toMonoidHom) :=
    fun g X => rank_le fun p hp =>
      (CFSG.SectionRank.pRank_le_map hp.one_lt _ (MulAut.conj g).injective X).trans
        (pRank_le_rank hp _)
  refine le_antisymm ?_ (key g X)
  have := key g⁻¹ (X.map (MulAut.conj g).toMonoidHom)
  rwa [map_conj_map_conj_inv] at this

theorem isCyclic_of_rank_le_one {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPp : IsPGroup p P) (h : rank P ≤ 1) : IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p P) := ⟨hPp⟩
  by_contra hcyc
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := P) hp2 hcyc
  have hS'P : S.map P.subtype ≤ P := Subgroup.map_subtype_le S
  have hS'el : CFSG.Open.IsElemAbelian p (S.map P.subtype) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', hae⟩ := a.2
      obtain ⟨b', hb', hbe⟩ := b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hae, ← hbe]
      exact congrArg (fun x : P => (x : G))
        (congrArg Subtype.val (hSel.toIsMulCommutative.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · rintro _ ⟨x, hx, rfl⟩
      have := congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := S) x hx)
      simpa using this
  have hS'card : Nat.card (S.map P.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hScard]
  have := le_rank hp hS'P hS'el hS'card
  omega

omit [Finite G] in
theorem natCard_subgroupOf_of_le {U X : Subgroup G} (h : U ≤ X) :
    Nat.card (U.subgroupOf X) = Nat.card U :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem exists_le_normalizer_card_eq_mul {U X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hUX : U ≤ X) (hU : IsPGroup p U) (hdvd : p * Nat.card U ∣ Nat.card X) :
    ∃ U₁ : Subgroup G, U ≤ U₁ ∧ U₁ ≤ X ∧ U₁ ≤ Subgroup.normalizer (U : Set G) ∧
      IsPGroup p U₁ ∧ Nat.card U₁ = p * Nat.card U := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hdvd' : p ^ (n + 1) ∣ Nat.card X := by rwa [pow_succ', ← hn]
  obtain ⟨K, hKcard, hUK, hKX⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (hn ▸ pow_dvd_pow p (Nat.le_succ n)) hdvd' hUX
  have hKp : IsPGroup p K := IsPGroup.of_card hKcard
  have hidx : (U.subgroupOf K).index = p := by
    have h := (U.subgroupOf K).card_mul_index
    rw [natCard_subgroupOf_of_le hUK, hn, hKcard, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos n) h
  have hmin : (Nat.card K).minFac = p := by
    rw [hKcard, Nat.Prime.pow_minFac hp (Nat.succ_ne_zero n)]
  have hnorm : (U.subgroupOf K).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (hidx.trans hmin.symm)
  refine ⟨K, hUK, hKX, ?_, hKp, by rw [hKcard, hn, pow_succ']⟩
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have := hnorm.conj_mem ⟨u, hUK hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨k, hk⟩
    exact Subgroup.mem_subgroupOf.mp this
  · intro hu
    have := hnorm.conj_mem ⟨k * u * k⁻¹, hUK hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨k, hk⟩⁻¹
    have h' := Subgroup.mem_subgroupOf.mp this
    simpa [mul_assoc] using h'

theorem exists_sylow_map_subtype_eq {U X : Subgroup G} {p : ℕ} [Fact p.Prime] (hUX : U ≤ X)
    (hU : IsPGroup p U) (hmax : ¬ p * Nat.card U ∣ Nat.card X) :
    ∃ P : Sylow p X, (P : Subgroup X).map X.subtype = U := by
  have hU' : IsPGroup p (U.subgroupOf X) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  obtain ⟨P, hP⟩ := hU'.exists_le_sylow
  refine ⟨P, ?_⟩
  suffices h : (P : Subgroup X) = U.subgroupOf X by
    rw [h, Subgroup.map_subgroupOf_eq_of_le hUX]
  refine le_antisymm ?_ hP
  by_contra hlt
  have hlt' : U.subgroupOf X < P := lt_of_le_of_ne hP fun h => hlt h.symm.le
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  obtain ⟨n, hn⟩ := hU'.exists_card_eq
  have hcardlt : Nat.card (U.subgroupOf X) < Nat.card P := Subgroup.card_lt_of_lt hlt'
  have hnm : n < m := by
    rw [hn, hm] at hcardlt
    exact (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcardlt
  apply hmax
  rw [← natCard_subgroupOf_of_le hUX, hn, ← pow_succ']
  exact (pow_dvd_pow p hnm).trans (hm ▸ P.card_subgroup_dvd_card)

theorem BenderCounterexample.normalizer_zj_eq
    (hG : BenderCounterexample G) {X : Subgroup G}
    (hX : IsCoatom X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPGroup p (generalizedFittingSubgroupOf X)) {P : Subgroup G} (hPX : P ≤ X)
    (hP : IsPGroup p P) (hP1 : P ≠ ⊥) (hmax : ¬ p * Nat.card P ∣ Nat.card X) :
    ¬ p * Nat.card P ∣ Nat.card G ∧ Subgroup.normalizer ((ZJ P : Subgroup G) : Set G) = X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨PB, hPB⟩ := exists_sylow_map_subtype_eq hPX hP hmax
  have hPBne : (PB : Subgroup X) ≠ ⊥ := by
    intro h
    apply hP1
    rw [← hPB, h, Subgroup.map_bot]
  obtain ⟨PG, hPG, hN⟩ := exists_ambient_sylow_with_zj_normalizer_eq_of_fstar_pgroup hp2
    hG.isSimpleGroup (qd_not_involved_of_hasAbelianSylowTwo hG.hasAbelianSylowTwo hp2) X hX hF
    PB hPBne
  have hPGP : (PG : Subgroup G) = P := hPG.trans hPB
  refine ⟨?_, hPGP ▸ hN⟩
  rw [← hPGP]
  intro hdvd
  rw [PG.card_eq_multiplicity, ← pow_succ'] at hdvd
  exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp hdvd

theorem mem_generalizedFittingSubgroupOf_of_le_centralizer {H : Subgroup G}
    (hH : HasAbelianSylowTwo H) {t : G} (htH : t ∈ H) (ht : orderOf t = 2)
    (hC : ∀ p : ℕ, p.Prime → p ≠ 2 → qCoreOf H p ≤ Subgroup.centralizer ({t} : Set G)) :
    t ∈ generalizedFittingSubgroupOf H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s : H := ⟨t, htH⟩ with hsdef
  obtain ⟨S, hsS⟩ := exists_sylow_mem htH ht
  have hS := hH S
  have hsF : CFSG.fittingSubgroup H ≤ Subgroup.centralizer ({s} : Set H) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hp2 : (p : ℕ) = 2
    · have hxS : x ∈ (S : Subgroup H) := by
        have hle : pCore (p : ℕ) H ≤ (S : Subgroup H) := by
          rw [hp2]
          exact IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2) (G := H)) S
        exact hle hx
      exact setLike_mul_comm hxS hsS
    · have hxq : (x : G) ∈ qCoreOf H p := ⟨x, hx, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hC p hp hp2 hxq))
  have hFit : CFSG.fittingSubgroupOf (⊤ : Subgroup H) = CFSG.fittingSubgroup H :=
    CFSG.Adapters.fittingSubgroupOf_top_eq_foundations H
  have hEF : ∀ K : Subgroup H, IsComponentOf K ⊤ →
      K ≤ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H) := by
    intro K hK
    have := (CFSG.LocalCores.component_solvable_centralizer (R := CFSG.fittingSubgroup H)
      inferInstance (CFSG.fittingSubgroup_normal).isSubnormal).1 K
      ((isComponent_iff_isComponentOf_top K).mpr hK)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
  obtain ⟨e, he, hconj⟩ := exists_mem_componentLayerOf_conj_eq' hH S hsS
  have heC : e ∈ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H) :=
    (sSup_le fun K hK => hEF K hK) he
  have hc : e⁻¹ * s ∈
      Subgroup.centralizer (generalizedFittingSubgroupOf (⊤ : Subgroup H) : Set H) := by
    suffices hle : generalizedFittingSubgroupOf (⊤ : Subgroup H) ≤
        Subgroup.centralizer ({e⁻¹ * s} : Set H) by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    apply sup_le
    · rw [show CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup H) = _ from hFit]
      intro f hf
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : f * s = s * f := Subgroup.mem_centralizer_singleton_iff.mp (hsF hf)
      have h2 : f * e = e * f := Subgroup.mem_centralizer_iff.mp heC f hf
      have h2' : f * e⁻¹ = e⁻¹ * f := Commute.inv_right h2
      calc f * (e⁻¹ * s) = f * e⁻¹ * s := by rw [mul_assoc]
        _ = e⁻¹ * f * s := by rw [h2']
        _ = e⁻¹ * (s * f) := by rw [mul_assoc, h1]
        _ = e⁻¹ * s * f := by rw [mul_assoc]
    · apply sSup_le
      intro K hK x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hconj K hK x hx
      calc x * (e⁻¹ * s) = e⁻¹ * (e * x * e⁻¹) * s := by group
        _ = e⁻¹ * (s * x * s⁻¹) * s := by rw [h]
        _ = e⁻¹ * s * x := by group
  have hcF := CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le hc
  have heF : e ∈ generalizedFittingSubgroupOf (⊤ : Subgroup H) :=
    (le_sup_right : componentLayerOf (⊤ : Subgroup H) ≤ _) he
  have hsF' : s ∈ generalizedFittingSubgroupOf (⊤ : Subgroup H) := by
    have : s = e * (e⁻¹ * s) := by group
    rw [this]
    exact mul_mem heF hcF
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq H]
  exact ⟨s, hsF', rfl⟩

theorem BenderCounterexample.exists_hyperplane_mem_benderABar
    (hG : BenderCounterexample G)
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpt : ⁅Subgroup.zpowers t, qCoreOf H p⁆ ≠ ⊥) :
    ∃ R ≤ (T : Subgroup G), rank R = rank (T : Subgroup G) - 1 ∧
      ∃ V ≤ qCoreOf H p, V ≠ ⊥ ∧ V ≤ Subgroup.centralizer (R : Set G) ∧
        t ∈ Subgroup.normalizer (V : Set G) ∧ V ∈ benderABar H ∧ ⁅V, Subgroup.zpowers t⁆ = V := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Pbar, hPbarP, hPbarC, hPbart, hPbarA⟩ := bender1970_3_5 hG ht hH hp hpt
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hTab := hG.hasAbelianSylowTwo T
  have hTC := hG.sylow_le_centralizer T htT
  have hPbarodd : Odd (Nat.card Pbar) := by
    obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le hPbarP).exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨R, hRT, hRr, hRt⟩ := bender1970_3_4 T hTab htT ht (hTC.trans hPbarC) hPbarodd hPbart
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set D := Pbar ⊓ Subgroup.centralizer (R : Set G) with hDdef
  set V := ⁅D, Subgroup.zpowers t⁆ with hVdef
  have htR : t ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hcommT r (hRT hr) t htT
  have htD : t ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_inf (hPbarC htC) (Subgroup.le_normalizer htR)
  have hVD : V ≤ D := commutator_zpowers_le_of_mem_normalizer htD
  have hV1 : V ≠ ⊥ := by
    rw [hVdef, Subgroup.commutator_comm]
    exact hRt
  have hVt : t ∈ Subgroup.normalizer (V : Set G) :=
    mem_normalizer_commutator htD (Subgroup.le_normalizer (Subgroup.mem_zpowers t))
  have hVA : V ∈ benderABar H := hPbarA V (hVD.trans inf_le_left) hV1 hVt
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card D) := by
    obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le (inf_le_left.trans hPbarP)).exists_card_eq
    rw [Nat.card_zpowers, ht, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hVtt : ⁅V, Subgroup.zpowers t⁆ = V :=
    le_antisymm (commutator_zpowers_le_of_mem_normalizer hVt)
      (commutator_le_commutator_commutator D _ (Subgroup.zpowers_le.mpr htD) hcop)
  exact ⟨R, hRT, hRr, V, hVD.trans (inf_le_left.trans hPbarP), hV1, hVD.trans inf_le_right, hVt,
    hVA, hVtt⟩

end CFSG.Walter
