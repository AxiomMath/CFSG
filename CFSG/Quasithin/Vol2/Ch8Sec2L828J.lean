module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828I
public import CFSG.Quasithin.Vol2.Ch8Sec2HLU
public import CFSG.Quasithin.Vol2.Ch8Sec2D3Inputs
public import CFSG.Quasithin.Vol2.Ch8Sec2L828E
public import CFSG.Quasithin.Vol2.Ch8Sec2L828G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section L828J

variable {G : Type} [Group G] [Finite G]

theorem commutator_centralizer_le_828 {X U : Subgroup G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hNX : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hperf : ⁅X, X⁆ = X) (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X))
    (hXC : ¬ X ≤ Subgroup.centralizer (U : Set G)) :
    ⁅X, Subgroup.centralizer (U : Set G)⁆ ≤ pCoreOf 2 X := by
  have hCN : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.centralizer_le_normalizer _).trans hNX
  have hNC : Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  refine commutator_le_pCoreOf_828 (D := X ⊓ Subgroup.centralizer (U : Set G)) hq hperf hCN
    inf_le_left ?_ ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer (hXU.trans hNC)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  · intro e
    apply hXC
    rw [← e]
    exact inf_le_right
  · exact le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hCN)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (hXU.trans hNC))

omit [Finite G] in
theorem exists_y_828 {J P : Subgroup G} {Q : Type*} [Group Q] (f : ↥J →* Q)
    (hf : Function.Surjective f) (hP : IsPGroup 2 ↥P) (hker : ∀ x : ↥J, f x = 1 ↔ (x : G) ∈ P)
    {m : ℕ} (hm : Odd m) (h3 : 3 ∣ m) (e : Q ≃* DihedralGroup m) {v : ↥J}
    (hv : (v : G) ∉ P) (hv2 : v ^ 2 = 1) :
    ∃ y : ↥J, y ^ 3 = 1 ∧ ((y * v * y⁻¹ * v⁻¹ : ↥J) : G) ∉ P := by
  set i : ZMod m := ((m / 3 : ℕ) : ZMod m) with hidef
  have hi3 : DihedralGroup.r i ^ 3 = 1 := by
    rw [pow_succ, pow_two, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, DihedralGroup.one_def]
    congr 1
    have h3i : (3 : ZMod m) * i = 0 := by
      rw [hidef, show (3 : ZMod m) = ((3 : ℕ) : ZMod m) by norm_num, ← Nat.cast_mul,
        Nat.mul_div_cancel' h3, ZMod.natCast_self]
    linear_combination h3i
  have hi1 : DihedralGroup.r i ≠ 1 := by
    rw [DihedralGroup.one_def]
    intro h
    have hi0 : i = 0 := DihedralGroup.r.inj h
    rw [hidef, ZMod.natCast_eq_zero_iff] at hi0
    have hm0 : 0 < m := hm.pos
    have h1 : 0 < m / 3 := Nat.div_pos (Nat.le_of_dvd hm0 h3) (by norm_num)
    have h2 : m / 3 < m := Nat.div_lt_self hm0 (by norm_num)
    exact absurd (Nat.le_of_dvd h1 hi0) (by omega)
  set b := e.symm (DihedralGroup.r i) with hbdef
  have hb3 : b ^ 3 = 1 := by rw [hbdef, ← map_pow, hi3, map_one]
  have hb1 : b ≠ 1 := fun h => hi1 (by rw [← e.apply_symm_apply (DihedralGroup.r i), ← hbdef,
    h, map_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  obtain ⟨z, hz⟩ := hf b
  have hz3 : ((z ^ 3 : ↥J) : G) ∈ P := (hker _).mp (by rw [map_pow, hz, hb3])
  obtain ⟨c, hc⟩ := hP ⟨_, hz3⟩
  have hc' : (z ^ 3) ^ 2 ^ c = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hc
    simpa using this
  refine ⟨z ^ 2 ^ c, ?_, fun hmem => ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    exact hc'
  ·
    have h1 : f (z ^ 2 ^ c * v * (z ^ 2 ^ c)⁻¹ * v⁻¹) = 1 := (hker _).mpr hmem
    have hcomm : Commute (f v) (f (z ^ 2 ^ c)) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : ⁅f (z ^ 2 ^ c), f v⁆ = 1 := by
        rw [commutatorElement_def]
        exact h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
    refine not_commute_dihedral_828 hm e (fun h => hv ((hker v).mp h))
      (by rw [← map_pow, hv2, map_one]) ?_ ?_ hcomm
    · rw [map_pow, hz]
      intro h
      have h4 : orderOf b ∣ 2 ^ c := orderOf_dvd_of_pow_eq_one h
      rw [hbo] at h4
      have := (Nat.prime_three.dvd_of_dvd_pow h4)
      omega
    · rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hc', map_one]

theorem succ_le_pRank_of_commute_828 {p : ℕ} (hp : p.Prime) {E H : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) {r : ℕ} (hEcard : Nat.card E = p ^ r) {b : G}
    (hbc : ∀ e ∈ E, Commute e b) (hbp : b ^ p = 1) (hbE : b ∉ E) (hEH : E ≤ H) (hbH : b ∈ H) :
    r + 1 ≤ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := fun h => hbE (h ▸ one_mem E)
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcomm : ∀ (e : E) (c : Subgroup.zpowers b),
      Commute (E.subtype e) ((Subgroup.zpowers b).subtype c) := by
    rintro e ⟨c, k, rfl⟩
    exact (hbc e e.2).zpow_right k
  let f : E × Subgroup.zpowers b →* G :=
    MonoidHom.noncommCoprod E.subtype (Subgroup.zpowers b).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨e, c⟩ hx
    have hx' : (e : G) * c = 1 := hx
    have hcE : (c : G) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hx']
      exact inv_mem e.2
    have hc1 : c = 1 := by
      by_contra hc
      have htop := zpowers_eq_top_of_prime_card (G := Subgroup.zpowers b)
        (by rw [Nat.card_zpowers, hbord]) hc
      have hbmem : (⟨b, Subgroup.mem_zpowers b⟩ : Subgroup.zpowers b) ∈ Subgroup.zpowers c :=
        htop ▸ Subgroup.mem_top _
      obtain ⟨m, hm⟩ := hbmem
      apply hbE
      have : (c : G) ^ m = b := congrArg Subtype.val hm
      rw [← this]
      exact zpow_mem hcE m
    rw [hc1, OneMemClass.coe_one, mul_one] at hx'
    have he1 : e = 1 := Subtype.ext hx'
    rw [he1, hc1]
    rfl
  have hEc := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E × Subgroup.zpowers b) ?_ ?_ ?_
    f hf ?_
  · rintro ⟨e₁, c₁⟩ ⟨e₂, c₂⟩
    refine Prod.ext (mul_comm' e₁ e₂) ?_
    obtain ⟨c₁, k₁, rfl⟩ := c₁
    obtain ⟨c₂, k₂, rfl⟩ := c₂
    exact Subtype.ext (Commute.zpow_zpow_self b k₁ k₂).eq
  · rintro ⟨e, c⟩
    refine Prod.ext (Subtype.ext (hE.2 e e.2)) ?_
    obtain ⟨c, k, rfl⟩ := c
    apply Subtype.ext
    change (b ^ k) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  · rw [Nat.card_prod, hEcard, Nat.card_zpowers, hbord, pow_succ]
  · rintro _ ⟨⟨e, c⟩, rfl⟩
    exact H.mul_mem (hEH e.2) ((Subgroup.zpowers_le.mpr hbH) c.2)

theorem step828OneA_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal)
    (hcard : Mathieu.StmtH13Card) (h825 : Stmt8_2_5) (h827 : Step827) : Step828OneA := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hcase K hK hLUK
  obtain ⟨hr, m₀, h3m, ⟨eI₀⟩⟩ := hcase
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, hIU, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, -⟩ :=
    lu_facts_828 hLU82_holds hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe hLUT
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ x.2.1)⟩
  have hS : QuasithinUnique.IsSylowTwoOf T
      (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) :=
    ⟨hTU, hyp.fsu.sylow.1, fun h2 =>
      hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTU))⟩
  have hH2 : pCoreOf 2 (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff, ← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hU2
  have hKn := lemma_1_2_4_normal hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 hH2 hS
    hfam hLUK hK hLUT
  have hq := h827 G T L I hyp h731 h821 hc hrow H h k hH hh hC K hK hLUK
  have hKN : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := le_of_mem_cComp hK
  have hNK : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤
      Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKn
  have hKO := commutator_centralizer_le_828 hKN hNK (perfect_of_mem_cComp hK) hq
    (fun hKC => hLUC (hLUK.trans hKC))
  have hCK : Subgroup.centralizer (ch82U (fsuV T I) h : Set G) ≤
      Subgroup.normalizer (K : Set G) :=
    (Subgroup.centralizer_le_normalizer _).trans hNK
  obtain ⟨-, hhI, -, -, -, -, -, hker, -, hdisj, -⟩ := id hC
  have hw1 : wParam T (fsuV T I) = 1 := by
    rcases hr with hr | hr
    · exact (hC5.2.2.2.1 hr).1
    · exact (hC5.2.2.2.2.1 hr).1
  have hk1 : k = 1 := by
    have h1 := hC5.1
    rw [hw1] at h1
    exact_mod_cast h1.symm
  obtain ⟨m, hmo, hm1, ⟨eI⟩⟩ : ∃ m : ℕ, Odd m ∧ 1 < m ∧
      Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
        DihedralGroup m) := by
    rcases hdisj with ⟨-, m, hmo, hm1, hm⟩ | hP | hSz
    · exact ⟨m, hmo, hm1, hm⟩
    · rw [hk1] at hP
      obtain ⟨⟨-, -, -, h22, -⟩, -⟩ := hP
      exact absurd rfl h22
    · obtain ⟨-, a, ha, -, -, -, he, -⟩ := hSz
      omega
  have hmm : m₀ = m := by
    have h1 := Nat.card_congr eI.toEquiv
    have h2 := Nat.card_congr eI₀.toEquiv
    rw [DihedralGroup.nat_card] at h1 h2
    omega
  subst hmm
  set J := ch82I (fsuV T I) h with hJdef
  have hJ2 : IsPGroup 2 ↥(pCoreOf 2 J) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hkerJ : ∀ x : ↥J, QuotientGroup.mk' ((kerIn (fsuM T L ⊓ J) J).subgroupOf J) x = 1 ↔
      (x : G) ∈ pCoreOf 2 J := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker]
  have hVP : ¬ fsuV T I ≤ pCoreOf 2 J := by
    intro hVle
    have hhP : h ∈ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hhI
    have hJle : J ≤ pCoreOf 2 J := by
      refine sup_le hVle fun x hx => ?_
      rw [B6.mem_conjSub] at hx
      have := (Subgroup.mem_normalizer_iff.mp hhP _).mp (hVle hx)
      simpa [mul_assoc] using this
    have htriv : ∀ q : E2.StarQuot (fsuM T L ⊓ J) J, q = 1 := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (fsuM T L ⊓ J) J).subgroupOf J) q
      exact (hkerJ x).mpr (hJle x.2)
    have hc1 : Nat.card (E2.StarQuot (fsuM T L ⊓ J) J) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (htriv a).trans (htriv b).symm⟩, ⟨1⟩⟩
    have hc2 := Nat.card_congr eI.toEquiv
    rw [DihedralGroup.nat_card, hc1] at hc2
    omega
  obtain ⟨v, hvV, hvP⟩ := Set.not_subset.mp hVP
  let v' : ↥J := ⟨v, (le_sup_left : fsuV T I ≤ J) hvV⟩
  have hv2 : v' ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ hvV)
  obtain ⟨y', hy3', hyv⟩ := exists_y_828 (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) hJ2 hkerJ hmo h3m eI hvP hv2
  have hyC : (y' : G) ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := hIU y'.2
  have hy3 : (y' : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3'
    simpa using this
  have hyK : (y' : G) ∉ K := by
    intro hy
    apply hyv
    have h1 : ((y' * v' * y'⁻¹ * v'⁻¹ : ↥J) : G) ∈ pCoreOf 2 K := by
      apply hKO
      have := Subgroup.commutator_mem_commutator hy (hIU v'.2)
      simpa [commutatorElement_def] using this
    have hJN : J ≤ Subgroup.normalizer ((pCoreOf 2 K ⊓ J : Subgroup G) : Set G) :=
      (le_inf ((hIU.trans hCK).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
    have h2 : pCoreOf 2 K ⊓ J ≤ pCoreOf 2 J :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hJN
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
    exact h2 ⟨h1, (y' * v' * y'⁻¹ * v'⁻¹).2⟩
  have hyN : (y' : G) ∈ Subgroup.normalizer (K : Set G) := hCK hyC
  have hBp : IsPGroup 3 ↥(Subgroup.zpowers (y' : G)) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hy3, one_zpow]
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_normalized_828 (p := 3) hBp (Subgroup.zpowers_le.mpr hyN)
  have hO2 : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf K) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_of_injective K.subtype
      K.subtype_injective
  have hcent : ∀ q : ↥K, q ∈ (Q₀ : Subgroup ↥K) → Commute (q : G) (y' : G) := by
    intro q hq
    obtain ⟨q', hq', hq'e⟩ := hQ₀ _ (Subgroup.mem_zpowers _) q hq
    have hc1 : q⁻¹ * q' ∈ (Q₀ : Subgroup ↥K) := mul_mem (inv_mem hq) hq'
    have hc2 : ((q⁻¹ * q' : ↥K) : G) ∈ pCoreOf 2 K := by
      have e : ((q⁻¹ * q' : ↥K) : G) = ⁅(q : G)⁻¹, (y' : G)⁆ := by
        rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hq'e, inv_inv]
        group
      rw [e]
      exact hKO (Subgroup.commutator_mem_commutator (K.inv_mem q.2) hyC)
    have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) (Q₀ : Subgroup ↥K)
      ((pCoreOf 2 K).subgroupOf K) Q₀.isPGroup' hO2
    have hc : q⁻¹ * q' = 1 :=
      Subgroup.disjoint_def.mp hdis hc1 (Subgroup.mem_subgroupOf.mpr hc2)
    have hqq : q' = q := (inv_mul_eq_one.mp hc).symm
    rw [hqq] at hq'e
    show (q : G) * y' = y' * q
    calc (q : G) * y' = y' * q * (y' : G)⁻¹ * y' := by rw [← hq'e]
      _ = y' * q := by group
  have hQcyc : IsCyclic ↥(Q₀ : Subgroup ↥K) := by
    by_contra hnc
    have : Fact (IsPGroup 3 ↥(Q₀ : Subgroup ↥K)) := ⟨Q₀.isPGroup'⟩
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (by norm_num : (3 : ℕ) ≠ 2) hnc
    set E : Subgroup G := (S.map (Q₀ : Subgroup ↥K).subtype).map K.subtype with hEdef
    have hEcard : Nat.card E = 3 ^ 2 := by
      rw [hEdef, Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hScard]
    have hEK : E ≤ K := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hmemE : ∀ e ∈ E, ∃ s ∈ S, e = (((s : ↥(Q₀ : Subgroup ↥K)) : ↥K) : G) := by
      rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
    have hS3 : ∀ s ∈ S, s ^ 3 = 1 := fun s hs => by
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSel.exponent_dvd_p ⟨s, hs⟩
      exact congrArg Subtype.val h
    have hE : CFSG.Open.IsElemAbelian 3 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
      · obtain ⟨s, hs, hse⟩ := hmemE a a.2
        obtain ⟨t, ht, hte⟩ := hmemE b b.2
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hse, hte]
        have hst : (⟨s, hs⟩ : ↥S) * ⟨t, ht⟩ = ⟨t, ht⟩ * ⟨s, hs⟩ := mul_comm _ _
        have := congrArg (fun x : ↥S => (((x : ↥(Q₀ : Subgroup ↥K)) : ↥K) : G)) hst
        simpa using this
      · obtain ⟨s, hs, rfl⟩ := hmemE e he
        rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, hS3 s hs]
        rfl
    have hbc : ∀ e ∈ E, Commute e (y' : G) := by
      intro e he
      obtain ⟨s, -, rfl⟩ := hmemE e he
      exact hcent _ s.2
    have h3 := succ_le_pRank_of_commute_828 Nat.prime_three hE hEcard hbc hy3
      (fun hyE => hyK (hEK hyE)) (hEK.trans hKN) ((Subgroup.centralizer_le_normalizer _) hyC)
    have h2 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke hH2 Nat.prime_three
      (by norm_num)
    omega
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  let eW : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≃* ↥(ch82U (fsuV T I) h) :=
    (MulEquiv.subgroupCongr hfix).trans (Subgroup.subgroupOfEquivOfLe hUV)
  have heW : ∀ w, ((eW w : ↥(ch82U (fsuV T I) h)) : G) = ((w : ↥(fsuV T I)) : G) :=
    fun w => rfl
  have heWs : ∀ u : ↥(ch82U (fsuV T I) h),
      (((eW.symm u : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (u : G) := fun u => rfl
  let ψ : ↥K →* MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) :=
    (MulAut.congr eW.symm).toMonoidHom.comp
      ((conjAct (ch82U (fsuV T I) h)).comp (Subgroup.inclusion hKN))
  have hψ : ∀ (x : ↥K) (w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))),
      (((ψ x w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (x : G) * ((w : ↥(fsuV T I)) : G) * (x : G)⁻¹ := by
    intro x w
    show (((eW.symm (conjAct (ch82U (fsuV T I) h) (Subgroup.inclusion hKN x) (eW w)) :
      ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) = _
    rw [heWs, CFSG.QuasithinUnique.Setup.coe_conjAct_apply, heW]
    rfl
  have hXalt := (hlu82_82 hLU82_holds hcard hrow hL0 hV hLN hC5 hAN hAL hAp hAe).2.1 hr
  have hXY : autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
      (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≤ ψ.range := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨b, hb, hgb⟩ := Subgroup.mem_map.mp hg
    have hbLU : (b : G) ∈ ch82LU L (ch82U (fsuV T I) h) := Subgroup.mem_subgroupOf.mp hb
    refine ⟨⟨b, hLUK hbLU⟩, ?_⟩
    ext w
    rw [hψ, resHom_apply, ← hgb, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
  have hYp : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    have hKp : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hW16 : Nat.card ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 16 := by
    rw [Nat.card_congr eW.toEquiv]
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    have hrk : rk ↥(ch82U (fsuV T I) h) = 4 := by
      rcases hr with hr | hr
      · exact (hC5.2.2.2.1 hr).2.2.2
      · exact (hC5.2.2.2.2.1 hr).2.2.2
    have hn4 : n = 4 := by
      rw [← hrk]
      unfold rk
      rw [hn, padicValNat.prime_pow]
    rw [hn, hn4]
    norm_num
  have h9 : ¬ 9 ∣ Nat.card ↥ψ.range := by
    intro h9
    have hsurj : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
    let P := Q₀.mapSurjective hsurj
    have hP9 : 3 ^ 2 ∣ Nat.card ↥(P : Subgroup ↥ψ.range) :=
      P.pow_dvd_card_of_pow_dvd_card (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h9)
    have hPcyc : IsCyclic ↥(P : Subgroup ↥ψ.range) := by
      have : (P : Subgroup ↥ψ.range) = (Q₀ : Subgroup ↥K).map ψ.rangeRestrict := rfl
      rw [this]
      exact isCyclic_of_surjective (ψ.rangeRestrict.subgroupMap (Q₀ : Subgroup ↥K))
        (ψ.rangeRestrict.subgroupMap_surjective _)
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(P : Subgroup ↥ψ.range))
    obtain ⟨c, hc⟩ := hP9
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact Nat.card_pos.ne' hc
    have hgo : orderOf (g ^ c) = 9 := by
      rw [orderOf_pow_of_dvd hc0 (by rw [hg, hc]; exact Dvd.intro_left _ rfl), hg, hc]
      norm_num
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)
    have hz : orderOf (((g ^ c : ↥(P : Subgroup ↥ψ.range)) : ↥ψ.range) :
        MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) = 9 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hgo]
    have h1 := pow_three_eq_one_of_card_828 hW16 (g := (((g ^ c : ↥(P : Subgroup ↥ψ.range)) :
      ↥ψ.range) : MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))))
      (by rw [← hz]; exact pow_orderOf_eq_one _)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hz] at h2
    norm_num at h2
  have hYX := eq_of_le_alternatingNatural_828 hXalt hXY hYp h9
  have hact : ∀ x ∈ K, ∃ b ∈ ch82LU L (ch82U (fsuV T I) h),
      b⁻¹ * x ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := by
    intro x hx
    have hmem : ψ ⟨x, hx⟩ ∈ autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
        (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) := hYX ▸ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨g, hg, hgψ⟩ := mem_autSub.mp hmem
    obtain ⟨b, hb, hgb⟩ := Subgroup.mem_map.mp hg
    have hbLU : (b : G) ∈ ch82LU L (ch82U (fsuV T I) h) := Subgroup.mem_subgroupOf.mp hb
    refine ⟨b, hbLU, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := congrArg (fun φ : MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) =>
      (((φ (eW.symm ⟨u, hu⟩) : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) :
        ↥(fsuV T I)) : G)) hgψ
    rw [resHom_apply, ← hgb, CFSG.QuasithinUnique.Setup.coe_conjAct_apply, hψ, heWs] at h1
    calc u * ((b : G)⁻¹ * x) = (b : G)⁻¹ * (b * u * (b : G)⁻¹) * x := by group
      _ = (b : G)⁻¹ * (x * u * x⁻¹) * x := by rw [h1]
      _ = (b : G)⁻¹ * x * u := by group
  have hfam' : ch82LU L (ch82U (fsuV T I) h) ∈
      cComp (ch82LU L (ch82U (fsuV T I) h) ⊔ T) := hfam
  exact eq_of_forall_mul_828 hfam' hLUK hK hKn hS hq hLUC hact

end L828J

end CFSG.Quasithin.H13
