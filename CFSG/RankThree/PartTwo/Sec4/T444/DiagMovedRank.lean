module

public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG
open CFSG.Assembly.RankThreeEven (projSL)

private theorem dmr_lt_three_pow (k : ℕ) : k < 3 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

private theorem dmr_one_lt_openPRank {X : Type} [Group X] [Finite X] (K : Subgroup X)
    {E : Subgroup X} (hEK : E ≤ K) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) : 1 < CFSG.Open.pRank 3 K := by
  have hmem : (2 : ℕ) ∈ {k : ℕ | ∃ E : Subgroup X, E ≤ K ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := ⟨E, hEK, hE, hc⟩
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup X, E ≤ K ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E', -, -, hk⟩
    have h1 : Nat.card E' ≤ Nat.card X := Subgroup.card_le_card_group E'
    rw [hk] at h1
    exact le_of_lt (lt_of_lt_of_le (dmr_lt_three_pow k) h1)
  have h2 := le_csSup hbdd hmem
  unfold CFSG.Open.pRank
  exact lt_of_lt_of_le (by norm_num) h2

private theorem dmr_exists_elemAbelian_pRank_two {H : Type} [Group H] [Finite H]
    (hr : CFSG.pRank 3 H = 2) :
    ∃ A : Subgroup H, IsElementaryAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  set S : Set ℕ := {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 3 A ∧ Nat.card A = 3 ^ r}
    with hSdef
  have hr' : sSup S = 2 := hr
  have hbdd : BddAbove S := by
    by_contra hnb
    rw [csSup_of_not_bddAbove hnb] at hr'
    simp at hr'
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty] at hr'
    simp at hr'
  obtain ⟨b, hb⟩ := hbdd
  have hfin : S.Finite := (Set.finite_Iic b).subset fun r hrS => hb hrS
  have hmem : sSup S ∈ S := hne.csSup_mem hfin
  rw [hr'] at hmem
  exact hmem

private theorem dmr_exists_E9_L34 :
    ∃ E₀ : Subgroup ↥(projSL 3 (GaloisField 2 2)),
      IsElementaryAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 2 :=
  dmr_exists_elemAbelian_pRank_two CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_projSL

private theorem dmr_sylow_surj {A : Type} [Group A] [Finite A] {E : Type} [Group E] [Finite E]
    [IsElementaryAbelian 3 E] (hE9 : Nat.card E = 3 ^ 2) (φ : A →* E)
    (hφ : Function.Surjective φ) :
    ∃ S : Subgroup A, IsPGroup 3 S ∧ ¬ IsCyclic S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 A))
  have htop : ∀ Q : Sylow 3 E, Q.toSubgroup = ⊤ := by
    intro Q
    have hcard : Q.toSubgroup.index * Nat.card Q.toSubgroup = Nat.card E :=
      Subgroup.index_mul_card (H := Q.toSubgroup)
    have hnd : ¬ 3 ∣ Q.toSubgroup.index := Sylow.not_dvd_index Q
    have hdvd : Q.toSubgroup.index ∣ 3 ^ 2 :=
      ⟨Nat.card Q.toSubgroup, by rw [← hE9]; exact hcard.symm⟩
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have h1 : Q.toSubgroup.index = 1 := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [hm, h0, pow_zero]
      · have h3 : 3 ∣ Q.toSubgroup.index := by
          rw [hm]
          exact dvd_pow_self 3 hpos.ne'
        exact absurd h3 hnd
    exact (Subgroup.index_eq_one (H := Q.toSubgroup)).1 h1
  have hmapeq : (P.mapSurjective hφ).toSubgroup = Subgroup.map φ P.toSubgroup := rfl
  have hsurjP : ∀ y : E, ∃ x ∈ P.toSubgroup, φ x = y := by
    intro y
    have hy : y ∈ (P.mapSurjective hφ).toSubgroup := by
      rw [htop]
      exact Subgroup.mem_top y
    rw [hmapeq] at hy
    exact Subgroup.mem_map.1 hy
  refine ⟨P.toSubgroup, P.isPGroup', fun hcyc => ?_⟩
  have hψ : Function.Surjective (φ.comp P.toSubgroup.subtype) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hsurjP y
    exact ⟨⟨x, hx⟩, hxy⟩
  exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hE9
    (isCyclic_of_surjective (φ.comp P.toSubgroup.subtype) hψ)

private def dmr_pi {G : Type} [Group G] (Z : Subgroup G) [Z.Normal] (H : Subgroup (G ⧸ Z)) :
    ↥(H.comap (QuotientGroup.mk' Z)) →* ↥H :=
  ((QuotientGroup.mk' Z).comp (H.comap (QuotientGroup.mk' Z)).subtype).codRestrict H
    (fun x => Subgroup.mem_comap.1 x.2)

private def dmr_Phi {G : Type} [Group G] (Z : Subgroup G) [Z.Normal] (H : Subgroup (G ⧸ Z))
    (N : Subgroup H) [N.Normal] {T : Type} [Group T] (e : ↥H ⧸ N ≃* T) :
    ↥(H.comap (QuotientGroup.mk' Z)) →* T :=
  (e.toMonoidHom.comp (QuotientGroup.mk' N)).comp (dmr_pi Z H)

private theorem dmr_Phi_surj {G : Type} [Group G] (Z : Subgroup G) [Z.Normal]
    (H : Subgroup (G ⧸ Z)) (N : Subgroup H) [N.Normal] {T : Type} [Group T]
    (e : ↥H ⧸ N ≃* T) : Function.Surjective (dmr_Phi Z H N e) := by
  intro l
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e.symm l)
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (h : G ⧸ Z)
  have hkH : k ∈ H.comap (QuotientGroup.mk' Z) := by
    rw [Subgroup.mem_comap]
    show QuotientGroup.mk k ∈ H
    rw [hk]
    exact h.2
  refine ⟨⟨k, hkH⟩, ?_⟩
  have hpi : dmr_pi Z H ⟨k, hkH⟩ = h := Subtype.ext hk
  show e (QuotientGroup.mk (dmr_pi Z H ⟨k, hkH⟩)) = l
  rw [hpi, hh, MulEquiv.apply_symm_apply]

theorem ys03_one_lt_pRank_of_hasSection_L34 {X : Type} [Group X] [Finite X] (K : Subgroup X)
    (hZ : IsPGroup 3 (Subgroup.center K))
    (hsec : HasSection (K ⧸ Subgroup.center K) (projSL 3 (GaloisField 2 2))) :
    1 < CFSG.Open.pRank 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, N, hN, ⟨e⟩⟩ := hsec
  obtain ⟨E₀, hE0, hE9⟩ := dmr_exists_E9_L34
  let B : Subgroup K := H.comap (QuotientGroup.mk' (Subgroup.center K))
  let Φ : ↥B →* ↥(projSL 3 (GaloisField 2 2)) := dmr_Phi (Subgroup.center K) H N e
  have hΦ : Function.Surjective Φ := dmr_Phi_surj (Subgroup.center K) H N e
  let Aa : Subgroup ↥B := E₀.comap Φ
  let φ : ↥Aa →* ↥E₀ := (Φ.comp Aa.subtype).codRestrict E₀ (fun x => x.2)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨b, hb⟩ := hΦ (y : ↥(projSL 3 (GaloisField 2 2)))
    exact ⟨⟨b, Subgroup.mem_comap.2 (by rw [hb]; exact y.2)⟩, Subtype.ext hb⟩
  obtain ⟨S, hSp, hScyc⟩ := dmr_sylow_surj hE9 φ hφ
  haveI : Fact (IsPGroup 3 S) := ⟨hSp⟩
  obtain ⟨T, -, hTcard, hTel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hScyc
  let ι : ↥S →* X := K.subtype.comp (B.subtype.comp (Aa.subtype.comp S.subtype))
  have hι : Function.Injective ι :=
    K.subtype_injective.comp (B.subtype_injective.comp
      (Aa.subtype_injective.comp S.subtype_injective))
  have hEK : T.map ι ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact (B.subtype (Aa.subtype (S.subtype x))).2
  have hcardT : Nat.card (T.map ι) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hι, hTcard]
  have hTab : CFSG.Open.IsElemAbelian 3 T := CFSG.Open.isElemAbelian_of_isElementaryAbelian
  exact dmr_one_lt_openPRank K hEK (hTab.map ι) hcardT

private theorem dmr_conj_isComponent {X : Type} [Group X] {K : Subgroup X}
    (hK : CFSG.IsComponent K) (g : X) :
    CFSG.IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

private theorem dmr_central_conj {X : Type} [Group X] {K : Subgroup X} {z : X}
    (hzc : ∀ k ∈ K, k * z = z * k) (g : X) :
    ∀ k' ∈ K.map (MulAut.conj g).toMonoidHom, k' * (g * z * g⁻¹) = g * z * g⁻¹ * k' := by
  intro k' hk'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
  have hkz := hzc k hk
  show g * k * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * k * g⁻¹)
  calc g * k * g⁻¹ * (g * z * g⁻¹) = g * (k * z) * g⁻¹ := by group
    _ = g * (z * k) * g⁻¹ := by rw [hkz]
    _ = g * z * g⁻¹ * (g * k * g⁻¹) := by group

private theorem dmr_conj_comm {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.IsComponent K) {z : X} (hzK : z ∈ K) (hzc : ∀ k ∈ K, k * z = z * k) (g h : X) :
    g * z * g⁻¹ * (h * z * h⁻¹) = h * z * h⁻¹ * (g * z * g⁻¹) := by
  have ha : g * z * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.2 ⟨z, hzK, rfl⟩
  have hb : h * z * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom :=
    Subgroup.mem_map.2 ⟨z, hzK, rfl⟩
  rcases CFSG.LocalCores.distinct_components_commute (dmr_conj_isComponent hK g)
      (dmr_conj_isComponent hK h) with hKK | hbot
  · have hb' : h * z * h⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by
      rw [hKK]
      exact hb
    exact (dmr_central_conj hzc g _ hb').symm
  · have hmem := Subgroup.commutator_mem_commutator ha hb
    rw [hbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.1 hmem

private theorem dmr_closure_facts {X : Type} [Group X] {m : ℕ} (S : Set X)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hSn : ∀ y ∈ S, ∀ g : X, g * y * g⁻¹ ∈ S)
    (hSe : ∀ y ∈ S, y ^ m = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      (∀ y ∈ Subgroup.closure S, y ^ m = 1) ∧ (Subgroup.closure S).Normal := by
  have hcen : Subgroup.closure S ≤ Subgroup.centralizer S := by
    refine (Subgroup.closure_le _).2 ?_
    intro a ha
    show a ∈ Subgroup.centralizer S
    exact Subgroup.mem_centralizer_iff.2 fun b hb => hSc b hb a ha
  have hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have hsub : Subgroup.closure S ≤ Subgroup.centralizer ({a} : Set X) := by
      refine (Subgroup.closure_le _).2 ?_
      intro s hs
      show s ∈ Subgroup.centralizer ({a} : Set X)
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      rw [hc]
      exact (Subgroup.mem_centralizer_iff.1 (hcen ha) s hs).symm
    exact Subgroup.mem_centralizer_iff.1 (hsub hb) a (Set.mem_singleton a)
  refine ⟨hcomm, ?_, ?_⟩
  · intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hSe x hx
    | one => exact one_pow m
    | mul x y hx hy ihx ihy =>
      rw [(show Commute x y from hcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  · refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hSn x hx g)
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      rw [e]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ihx

private theorem dmr_eq_one_of_central_coprime {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hcore : CFSG.pPrimeCore p X = ⊥) {K : Subgroup X} (hK : CFSG.IsComponent K)
    {z : X} (hzK : z ∈ K) (hzc : ∀ k ∈ K, k * z = z * k) (hcop : Nat.Coprime (orderOf z) p) :
    z = 1 := by
  set S : Set X := {y | ∃ g : X, y = g * z * g⁻¹} with hSdef
  have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a ⟨g, rfl⟩ b ⟨h, rfl⟩
    exact dmr_conj_comm hK hzK hzc g h
  have hSn : ∀ y ∈ S, ∀ g : X, g * y * g⁻¹ ∈ S := by
    rintro y ⟨h, rfl⟩ g
    exact ⟨g * h, by group⟩
  have hSe : ∀ y ∈ S, y ^ orderOf z = 1 := by
    rintro y ⟨g, rfl⟩
    rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  obtain ⟨-, hExp, hNormal⟩ := dmr_closure_facts (m := orderOf z) S hSc hSn hSe
  have hcopN : Nat.Coprime p (Nat.card (Subgroup.closure S)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hp := ⟨hp⟩) hdvd
    have hxX : orderOf (x : X) = p := (Subgroup.orderOf_coe x).trans hx
    have hdiv : orderOf (x : X) ∣ orderOf z := orderOf_dvd_of_pow_eq_one (hExp (x : X) x.2)
    rw [hxX] at hdiv
    have h1 : p = 1 := Nat.eq_one_of_dvd_coprimes hcop hdiv dvd_rfl
    have h2 := hp.two_le
    omega
  have hNbot : Subgroup.closure S = ⊥ :=
    CFSG.pPrimeCore_eq_bot_iff.1 hcore (Subgroup.closure S) hNormal hcopN
  have hzS : z ∈ S := ⟨1, by simp⟩
  have hzN : z ∈ Subgroup.closure S := Subgroup.subset_closure hzS
  rw [hNbot, Subgroup.mem_bot] at hzN
  exact hzN

theorem ys03_center_isPGroup_of_component {G : Type} [Group G] [Finite G]
    {K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)} (hK : CFSG.IsComponent K) :
    IsPGroup 3 (Subgroup.center K) := by
  haveI : Finite (G ⧸ CFSG.pPrimeCore 3 G) :=
    Finite.of_surjective _ QuotientGroup.mk_surjective
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcore : CFSG.pPrimeCore 3 (G ⧸ CFSG.pPrimeCore 3 G) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hprime : ∀ d : ℕ, d.Prime → d ∣ Nat.card (Subgroup.center K) → d = 3 := by
    intro d hd hdvd
    by_contra hne
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' d (hp := ⟨hd⟩) hdvd
    have hzK : ((w : K) : G ⧸ CFSG.pPrimeCore 3 G) ∈ K := (w : K).2
    have hzc : ∀ k ∈ K, k * ((w : K) : G ⧸ CFSG.pPrimeCore 3 G) =
        ((w : K) : G ⧸ CFSG.pPrimeCore 3 G) * k := by
      intro k hk
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 w.2 ⟨k, hk⟩)
    have hz : orderOf ((w : K) : G ⧸ CFSG.pPrimeCore 3 G) = d := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
    have hcop : Nat.Coprime (orderOf ((w : K) : G ⧸ CFSG.pPrimeCore 3 G)) 3 := by
      rw [hz]
      exact (Nat.coprime_primes hd Nat.prime_three).2 hne
    have hz1 := dmr_eq_one_of_central_coprime Nat.prime_three hcore hK hzK hzc hcop
    have hw1 : w = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz1
    have hd1 : d = 1 := by
      rw [← hw, hw1, orderOf_one]
    exact hd.one_lt.ne' hd1
  have hpos : Nat.card (Subgroup.center K) ≠ 0 := Nat.card_pos.ne'
  exact IsPGroup.iff_card.2 ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos
    (fun {d} hd hdvd => hprime d hd hdvd)⟩

end CFSG.RankThree.PartTwo.Sec4

end
