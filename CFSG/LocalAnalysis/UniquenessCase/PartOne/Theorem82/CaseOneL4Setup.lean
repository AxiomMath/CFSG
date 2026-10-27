module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLieChar
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.GroupTheory.SteinbergCBFTFactorization
import CFSG.GroupTheory.CommutingConjugatePair
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma exists_coords_data {c : Counterexample4 G} (h : Case811Sylow c) (hK6c : K6c)
    {r : ℕ} (hlie : IsLie811 c.Lbar .l4 r 1) :
    ∃ (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar)
      (a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L)
      (e : Multiplicative (Fin 4 → ZMod 3) →* G),
      IsSumZeroCoords h.Abar c₀ ∧
      a.range = h.A.subgroupOf c.L ∧
      (∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) ∧
      e = c.L.subtype.comp a ∧
      e.range = h.A ∧
      (∀ v, e v = 1 ↔ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s) ∧
      (∀ σ : Equiv.Perm (Fin 4), ∃ n ∈ c.L, ∀ v,
        n * e v * n⁻¹ = e (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, hc₀⟩ := (hK6c c.Lbar .l4 r 1 hlie h.Abar h.isElemAbelian_Abar h.card_Abar).1 rfl
  obtain ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩ := h.exists_coords_lift hc₀.1
  have ha_memX : ∀ v, a v ∈ h.A.subgroupOf c.L := by
    intro v
    have hv : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at hv
  have ha_eq_one_iff : ∀ v, a v = 1 ↔ c₀ v = 1 := by
    intro v
    constructor
    · intro hv
      rw [← ha_apply v, hv, map_one]
    · intro hv
      have h : (⟨a v, ha_memX v⟩ : h.A.subgroupOf c.L) =
          ⟨1, (h.A.subgroupOf c.L).one_mem⟩ := hXinj (by
        show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) =
          QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (1 : ↥c.L)
        rw [ha_apply v, hv, map_one])
      exact congrArg Subtype.val h
  let e : Multiplicative (Fin 4 → ZMod 3) →* G := c.L.subtype.comp a
  have he_range : e.range = h.A := by
    rw [MonoidHom.range_comp, ha_range, Subgroup.map_subgroupOf_eq_of_le h.A_le_L]
  have he_eq_one_iff : ∀ v, e v = 1 ↔ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s := by
    intro v
    have h1 : e v = 1 ↔ a v = 1 := by
      constructor
      · intro hv; exact Subtype.ext hv
      · intro hv; exact congrArg Subtype.val hv
    rw [h1, ha_eq_one_iff v, hc₀.2.1 v]
  have he_exists_perm : ∀ σ : Equiv.Perm (Fin 4), ∃ n ∈ c.L, ∀ v,
      n * e v * n⁻¹ = e (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)) := by
    intro σ
    let φ : Multiplicative (Fin 4 → ZMod 3) → Multiplicative (Fin 4 → ZMod 3) :=
      fun v => Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)
    obtain ⟨n, hn⟩ := hc₀.2.2.2 σ
    have hform : ∀ v, n * c₀ v * n⁻¹ = c₀ (φ v) := by
      intro v
      simpa [φ] using hn v
    have hn_norm : n ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) :=
      h.mem_normalizer_of_coords hc₀.1 hform
    obtain ⟨g, -, -, hgact⟩ :=
      h.exists_conj_of_coords (c₀ := c₀) a ha_range ha_apply hXinj φ hn_norm hform
    refine ⟨(g : G), g.2, ?_⟩
    intro v
    simpa [e] using hgact v
  exact ⟨c₀, a, e, hc₀, ha_range, ha_apply, rfl, he_range, he_eq_one_iff, he_exists_perm⟩

private lemma mem_L_of_mul_ker {c : Counterexample4 G} {r m : ℕ} (hr : r.Prime)
    {C : Subgroup G} (hC_le_M : C ≤ c.S.M) (hC_not_dvd : ¬ r ∣ Nat.card C)
    {x : G} (hxM : x ∈ c.S.M) (hxord : orderOf x ∣ r ^ m)
    {l : ↥c.L} (hx : x = (x * (l : G)⁻¹) * (l : G))
    (hkC : x * (l : G)⁻¹ ∈ C) : x ∈ c.L := by
  classical
  haveI : ((c.L).subgroupOf c.S.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp81.1).mpr c.le_normalizer_L
  let q : ↥c.S.M →* (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) :=
    QuotientGroup.mk' ((c.L).subgroupOf c.S.M)
  let xM : ↥c.S.M := ⟨x, hxM⟩
  let kM : ↥c.S.M := ⟨x * (l : G)⁻¹, hC_le_M hkC⟩
  let lM : ↥c.S.M := ⟨(l : G), c.hyp81.1 l.2⟩
  have hxM_eq : xM = kM * lM := by
    apply Subtype.ext
    exact hx
  have hlM : lM ∈ (c.L).subgroupOf c.S.M := l.2
  have hq_l : q lM = 1 := by
    change (QuotientGroup.mk lM : ↥c.S.M ⧸ (c.L).subgroupOf c.S.M) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hlM
  have hq_eq : q xM = q kM := by
    rw [hxM_eq, map_mul, hq_l, mul_one]
  have hqxdvd : orderOf (q xM) ∣ r ^ m := by
    have h1 : orderOf (q xM) ∣ orderOf xM := orderOf_map_dvd q xM
    have h2 : orderOf xM = orderOf x := by
      rw [← Subgroup.orderOf_coe xM]
    rw [h2] at h1
    exact h1.trans hxord
  have hqkdvd : orderOf (q xM) ∣ Nat.card C := by
    rw [hq_eq]
    have h1 : orderOf (q kM) ∣ orderOf kM := orderOf_map_dvd q kM
    have h2 : orderOf kM ∣ Nat.card C := by
      let kC : C := ⟨x * (l : G)⁻¹, hkC⟩
      have h3 : orderOf kM = orderOf kC := by
        rw [← Subgroup.orderOf_coe kM, ← Subgroup.orderOf_coe kC]
      rw [h3]
      exact orderOf_dvd_natCard kC
    exact h1.trans h2
  have hcop : Nat.Coprime (Nat.card C) (r ^ m) := by
    have h1 : Nat.Coprime (Nat.card C) r := (hr.coprime_iff_not_dvd.mpr hC_not_dvd).symm
    exact h1.pow_right m
  have hone : orderOf (q xM) = 1 := by
    have hdvd : orderOf (q xM) ∣ Nat.gcd (Nat.card C) (r ^ m) := Nat.dvd_gcd hqkdvd hqxdvd
    rw [hcop.gcd_eq_one] at hdvd
    exact Nat.dvd_one.mp hdvd
  have hq1 : q xM = 1 := orderOf_eq_one_iff.mp hone
  have hxker : xM ∈ q.ker := MonoidHom.mem_ker.mpr hq1
  rw [QuotientGroup.ker_mk'] at hxker
  exact hxker

private lemma mem_L_of_kernel {c : Counterexample4 G} (hK6L4 : K6L4) {r : ℕ}
    (hlie : IsLie811 c.Lbar .l4 r 1) (hr : r ∈ uniqueFourSigma c.S.M)
    (hC : CFSG.Open.pRank r
      ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype) = 0) :
    ∀ x ∈ c.S.M, IsPGroup r (Subgroup.zpowers x) → x ∈ c.L := by
  classical
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  have hr2 : r ≠ 2 := by omega
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let φ : ↥c.S.M →* MulAut c.Lbar :=
    CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L
  let C : Subgroup G := φ.ker.map c.S.M.subtype
  have hC_le_M : C ≤ c.S.M := Subgroup.map_subtype_le _
  have hC_not_dvd : ¬ r ∣ Nat.card C :=
    CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero hr.1.1 hC
  intro x hxM hxpg
  obtain ⟨m, hm⟩ := hxpg.exists_card_eq
  have hxord : orderOf x = r ^ m := by rw [← Nat.card_zpowers, hm]
  let xM : ↥c.S.M := ⟨x, hxM⟩
  have hφord : orderOf (φ xM) ∣ r ^ m := by
    have h1 : orderOf (φ xM) ∣ orderOf xM := orderOf_map_dvd φ xM
    have h2 : orderOf xM = orderOf x := by
      rw [← Subgroup.orderOf_coe xM]
    rw [h2, hxord] at h1
    exact h1
  obtain ⟨k, hk⟩ := (hK6L4 c.Lbar r hlie hr5).1 (φ xM)
  have hφinner : φ xM ∈ innAut c.Lbar :=
    CFSG.GroupTheory.mem_of_pow_two_pow_mem_of_orderOf_dvd_prime_pow hr.1.1 hr2 hφord hk
  obtain ⟨ybar, hybar⟩ := MonoidHom.mem_range.mp hφinner
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective N ybar
  let lM : ↥c.S.M := ⟨(l : G), c.hyp81.1 l.2⟩
  have hφl : φ lM = MulAut.conj ybar := by
    rw [← hl]
    exact CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L c.S.M c.le_normalizer_L
      (c.hyp81.1 l.2) l.2
  have hφx : φ xM = MulAut.conj ybar := hybar.symm
  have hφprod : φ (xM * lM⁻¹) = 1 := by
    rw [map_mul, map_inv, hφx, hφl, mul_inv_cancel]
  have hkC : x * (l : G)⁻¹ ∈ C :=
    Subgroup.mem_map.mpr ⟨xM * lM⁻¹, MonoidHom.mem_ker.mpr hφprod, rfl⟩
  have hx_eq : x = (x * (l : G)⁻¹) * (l : G) := by group
  exact mem_L_of_mul_ker hr.1.1 hC_le_M hC_not_dvd hxM (by rw [hxord]) hx_eq hkC


private lemma map_zpowers_subgroupOf {c : Counterexample4 G} {V : Type*} [Group V]
    (a : V →* ↥c.L) (c₀ : V →* c.Lbar)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) (v : V) :
    ((Subgroup.zpowers (a v : G)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) = Subgroup.zpowers (c₀ v) := by
  classical
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ Subgroup.zpowers ((a v : G)) := hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy'
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have hn' : (a v) ^ n = y := Subtype.ext hn
    calc c₀ v ^ n = (π (a v)) ^ n := by rw [ha_apply]
      _ = π ((a v) ^ n) := by rw [map_zpow]
      _ = π y := by rw [hn']
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨(a v) ^ n, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
    · rw [map_zpow, ha_apply, hn]

private lemma factorization_centralizer_eq {c : Counterexample4 G} {r : ℕ}
    (h : Case811Sylow c)
    (hmemL : ∀ x ∈ c.S.M, IsPGroup r (Subgroup.zpowers x) → x ∈ c.L)
    (hr : r ∈ uniqueFourSigma c.S.M) {V : Type*} [Group V]
    (a : V →* ↥c.L) (c₀ : V →* c.Lbar)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) (v : V)
    (hv3 : orderOf (a v : G) = 3) :
    (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({(a v : G)} : Set G))).factorization r =
      (Nat.card ↥(Subgroup.centralizer ({c₀ v} : Set c.Lbar))).factorization r := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  have hr2 : r ≠ 2 := by omega
  let H : Subgroup G := c.L ⊓ Subgroup.centralizer ({(a v : G)} : Set G)
  let K : Subgroup G := c.S.M ⊓ Subgroup.centralizer ({(a v : G)} : Set G)
  let CLbar : Subgroup c.Lbar := Subgroup.centralizer ({c₀ v} : Set c.Lbar)
  have hHK : H ≤ K := inf_le_inf c.hyp81.1 le_rfl
  have hfacHK : (Nat.card ↥K).factorization r = (Nat.card ↥H).factorization r :=
    CFSG.GroupTheory.factorization_eq_of_forall_isPGroup_zpowers_mem hr.1.1 hHK
      (fun x hxK hxpg => ⟨hmemL x hxK.1 hxpg, hxK.2⟩)
  have hBL : Subgroup.zpowers (a v : G) ≤ c.L := Subgroup.zpowers_le.mpr (a v).2
  have hB3 : IsPGroup 3 (Subgroup.zpowers (a v : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv3, pow_one]
  have hcent := Counterexample4.centralizer_map_lbar c (q := 3) (by norm_num) hBL hB3
  have hmapZp : ((Subgroup.zpowers (a v : G)).subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) = Subgroup.zpowers (c₀ v) :=
    map_zpowers_subgroupOf a c₀ ha_apply v
  let HL : Subgroup ↥c.L := H.subgroupOf c.L
  have hmapHL : HL.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) = CLbar := by
    have h := hcent
    rw [hmapZp] at h
    have hcentG : Subgroup.centralizer (Subgroup.zpowers (a v : G) : Set G) =
        Subgroup.centralizer ({(a v : G)} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcentG] at h
    have hcent' : Subgroup.centralizer (Subgroup.zpowers (c₀ v) : Set c.Lbar) = CLbar := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent'] at h
    exact h.symm
  have hcard := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf
    (G := ↥c.L) (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) HL
  rw [hmapHL] at hcard
  have hker2 : IsPGroup 2 ↥((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).ker ⊓ HL) := by
    rw [QuotientGroup.ker_mk']
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).to_le inf_le_left
  have hcardH : Nat.card ↥HL = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard' : Nat.card ↥H = Nat.card ↥CLbar *
      Nat.card ↥((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).ker ⊓ HL) := by
    rw [← hcardH, hcard]
  have hfacHCL : (Nat.card ↥H).factorization r = (Nat.card ↥CLbar).factorization r := by
    rw [hcard', Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := r) hker2 hr.1.1 hr2),
      add_zero]
  exact hfacHK.trans hfacHCL


private lemma pRank_centralizer_eq {c : Counterexample4 G} {r : ℕ}
    (hr : r ∈ uniqueFourSigma c.S.M) {V : Type*} [Group V]
    (a : V →* ↥c.L) (c₀ : V →* c.Lbar)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) (v : V)
    (hv3 : orderOf (a v : G) = 3) :
    CFSG.Open.pRank r (c.L ⊓ Subgroup.centralizer ({(a v : G)} : Set G)) =
      CFSG.Open.pRank r (Subgroup.centralizer ({c₀ v} : Set c.Lbar)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  have hr2 : r ≠ 2 := by omega
  have hBL : Subgroup.zpowers (a v : G) ≤ c.L := Subgroup.zpowers_le.mpr (a v).2
  have hB3 : IsPGroup 3 (Subgroup.zpowers (a v : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv3, pow_one]
  have hcent := Counterexample4.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := r) hr2
    hBL hB3
  have hleft : c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (a v : G) : Set G) =
      c.L ⊓ Subgroup.centralizer ({(a v : G)} : Set G) := by
    congr 1
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hright : Subgroup.centralizer
      (((Subgroup.zpowers (a v : G)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) : Set c.Lbar) =
      Subgroup.centralizer ({c₀ v} : Set c.Lbar) := by
    rw [map_zpowers_subgroupOf a c₀ ha_apply v]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hleft, hright] at hcent
  exact hcent

private lemma dvd_card_centralizer_of_K6L4 {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6L4 : K6L4) {r : ℕ} (hlie : IsLie811 c.Lbar .l4 r 1)
    (hr : r ∈ uniqueFourSigma c.S.M)
    (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar) (hc₀ : IsSumZeroCoords h.Abar c₀) :
    ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      r ∣ Nat.card ↥(c.L ⊓ Subgroup.centralizer (X : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  have hr2 : r ≠ 2 := by omega
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hdiv := (hK6L4 c.Lbar r hlie hr5).2 h.Abar h.isElemAbelian_Abar h.card_Abar c₀ hc₀
  intro X hXA hXcard
  have hX3 : IsPGroup 3 X := h.elemAbelian.isPGroup.to_le hXA
  have hXL : X ≤ c.L := hXA.trans h.A_le_L
  have hXbar_le : (X.subgroupOf c.L).map π ≤ h.Abar :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono c.L hXA)
  have hXbar_card : Nat.card ↥((X.subgroupOf c.L).map π) = 3 := by
    rw [Counterexample4.card_map_lbar c hXL (by rw [hXcard]; norm_num), hXcard]
  have hdvdbar : r ∣ Nat.card ↥(Subgroup.centralizer
      (((X.subgroupOf c.L).map π : Subgroup c.Lbar) : Set c.Lbar)) :=
    hdiv.1 ((X.subgroupOf c.L).map π) hXbar_le hXbar_card
  exact (c.dvd_card_centralizer_lbar_iff (q := 3) (by norm_num) (p := r) hr2 hXL hX3).mpr
    hdvdbar


private lemma map_centralizer_subgroupOf {c : Counterexample4 G} {r : ℕ}
    (hr : r ∈ uniqueFourSigma c.S.M) {V : Type*} [Group V]
    (a : V →* ↥c.L) (c₀ : V →* c.Lbar)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) (v : V)
    (hv3 : orderOf (a v : G) = 3) :
    ((c.L ⊓ Subgroup.centralizer ({(a v : G)} : Set G)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) =
      Subgroup.centralizer ({c₀ v} : Set c.Lbar) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hr2 : r ≠ 2 := by have := c.five_le_of_mem_sigma hr; omega
  have hBL : Subgroup.zpowers (a v : G) ≤ c.L := Subgroup.zpowers_le.mpr (a v).2
  have hB3 : IsPGroup 3 (Subgroup.zpowers (a v : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv3, pow_one]
  have hcent := Counterexample4.centralizer_map_lbar c (q := 3) (by norm_num) hBL hB3
  have hmapZp : ((Subgroup.zpowers (a v : G)).subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) = Subgroup.zpowers (c₀ v) :=
    map_zpowers_subgroupOf a c₀ ha_apply v
  have hleft : c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (a v : G) : Set G) =
      c.L ⊓ Subgroup.centralizer ({(a v : G)} : Set G) := by
    congr 1
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hright : Subgroup.centralizer (Subgroup.zpowers (c₀ v) : Set c.Lbar) =
      Subgroup.centralizer ({c₀ v} : Set c.Lbar) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hmapZp, hright, hleft] at hcent
  exact hcent.symm


private lemma exists_perfect_a1 {c : Counterexample4 G} (h : Case811Sylow c) (hK6L4 : K6L4)
    {r : ℕ} (hlie : IsLie811 c.Lbar .l4 r 1) (hr : r ∈ uniqueFourSigma c.S.M)
    (a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L)
    (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hc₀ : IsSumZeroCoords h.Abar c₀)
    (hv3 : orderOf (a Case811L4.vA1 : G) = 3) :
    ∃ K : Subgroup G,
      K ≤ c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA1 : G)} : Set G) ∧
      ⁅K, K⁆ = K ∧ 3600 < Nat.card K ∧
      ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) → N = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hK6 := (hK6L4 c.Lbar r hlie hr5).2 h.Abar h.isElemAbelian_Abar h.card_Abar c₀ hc₀
  obtain ⟨Kbar, hKbar_le, -, hKbar_comm, hKbar_card, hKbar_odd⟩ :=
    hK6.2.2.2.2.2.2.2.1
  let H : Subgroup G := c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA1 : G)} : Set G)
  let HL : Subgroup ↥c.L := H.subgroupOf c.L
  have hmapH : HL.map π = Subgroup.centralizer ({c₀ Case811L4.vA1} : Set c.Lbar) :=
    map_centralizer_subgroupOf hr a c₀ ha_apply Case811L4.vA1 hv3
  have hKbar_le_map : Kbar ≤ HL.map π := by
    rw [hmapH]
    exact hKbar_le
  let Good : Subgroup ↥c.L → Prop := fun K' => K' ≤ HL ∧ K'.map π = Kbar
  have hGood : ∃ K', Good K' := by
    refine ⟨(Kbar.comap π) ⊓ HL, inf_le_right, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.1
    · intro hx
      have hxmap : x ∈ HL.map π := hKbar_le_map hx
      obtain ⟨y, hyHL, hyx⟩ := hxmap
      exact ⟨y, ⟨by change π y ∈ Kbar; rwa [hyx], hyHL⟩, hyx⟩
  obtain ⟨K, hKmin⟩ :=
    exists_minimalFor_of_wellFoundedLT Good (fun K' => Nat.card ↥K') hGood
  have hKle : K ≤ HL := hKmin.prop.1
  have hKmap : K.map π = Kbar := hKmin.prop.2
  have hmin : ∀ K' : Subgroup ↥c.L, Good K' → K' ≤ K → K' = K := by
    intro K' hK' hle
    by_contra hne
    have hlt : K' < K := lt_of_le_of_ne hle hne
    have hcard : Nat.card ↥K' < Nat.card ↥K :=
      Set.Finite.card_lt_card (Set.toFinite (K : Set ↥c.L)) hlt
    exact hKmin.not_lt hK' hcard
  have hcomm_le : ⁅K, K⁆ ≤ K := by
    refine Subgroup.commutator_le.mpr ?_
    intro g hg h hh
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
  have hcommGood : Good ⁅K, K⁆ := by
    refine ⟨hcomm_le.trans hKle, ?_⟩
    rw [Subgroup.map_commutator, hKmap, hKbar_comm]
  have hKcomm : ⁅K, K⁆ = K := hmin ⁅K, K⁆ hcommGood hcomm_le
  have hKbar_le_K : Nat.card ↥Kbar ≤ Nat.card ↥K := by
    have hcard := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf
      (G := ↥c.L) π K
    rw [hKmap] at hcard
    rw [hcard]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hKbar_ge : 7200 ≤ Nat.card ↥Kbar := by
    rw [hKbar_card]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have h1 : 25 ≤ r ^ 2 := by nlinarith
    have h2 : 24 ≤ r ^ 2 - 1 := by omega
    have h3 : 576 ≤ (r ^ 2 - 1) ^ 2 := by
      calc 576 = 24 ^ 2 := by norm_num
        _ ≤ (r ^ 2 - 1) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : 14400 ≤ r ^ 2 * (r ^ 2 - 1) ^ 2 := by
      calc 14400 = 25 * 576 := by norm_num
        _ ≤ r ^ 2 * (r ^ 2 - 1) ^ 2 := Nat.mul_le_mul h1 h3
    simpa using h4
  have hKcard : 3600 < Nat.card ↥K := by omega
  let KG : Subgroup G := K.map c.L.subtype
  have hKG_le : KG ≤ c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA1 : G)} : Set G) := by
    have hmapHL : HL.map c.L.subtype =
        c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA1 : G)} : Set G) :=
      Subgroup.map_subgroupOf_eq_of_le (H := c.L ⊓
        Subgroup.centralizer ({(a Case811L4.vA1 : G)} : Set G)) (K := c.L) inf_le_left
    rw [← hmapHL]
    exact Subgroup.map_mono hKle
  have hKG_comm : ⁅KG, KG⁆ = KG := by
    have h := congrArg (Subgroup.map c.L.subtype) hKcomm
    rwa [Subgroup.map_commutator] at h
  have hKG_card : Nat.card ↥KG = Nat.card ↥K :=
    Subgroup.card_map_of_injective c.L.subtype_injective
  have hKG_big : 3600 < Nat.card ↥KG := by rw [hKG_card]; exact hKcard
  refine ⟨KG, hKG_le, hKG_comm, hKG_big, ?_⟩
  intro N hNK hNnormal hNodd
  let NL : Subgroup ↥c.L := N.subgroupOf c.L
  have hKG_le_L : KG ≤ c.L := Subgroup.map_subtype_le K
  have hN_le_L : N ≤ c.L := hNK.trans hKG_le_L
  have hNL_le_K : NL ≤ K := by
    intro x hx
    have hxG : (x : G) ∈ N := hx
    have hxKG : (x : G) ∈ KG := hNK hxG
    obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hxKG
    have hxy : x = y := Subtype.ext hyx.symm
    rwa [hxy]
  have hNL_normal : (NL.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hnN : (n : G) ∈ N := hn
    let nKG : ↥KG := ⟨(n : G), hNK hnN⟩
    let kKG : ↥KG := ⟨(k : G), Subgroup.mem_map_of_mem c.L.subtype k.2⟩
    have hnN' : nKG ∈ N.subgroupOf KG := hnN
    have hconjN : (k : G) * (n : G) * (k : G)⁻¹ ∈ N :=
      hNnormal.conj_mem nKG hnN' kKG
    exact hconjN
  let Nbar : Subgroup c.Lbar := NL.map π
  have hNbar_le : Nbar ≤ Kbar := by
    rw [← hKmap]
    exact Subgroup.map_mono hNL_le_K
  have hNbar_normal : (Nbar.subgroupOf Kbar).Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hnNbar : (n : c.Lbar) ∈ Nbar := hn
    obtain ⟨nL, hnL, hnπ⟩ := Subgroup.mem_map.mp hnNbar
    have hkKbar : (k : c.Lbar) ∈ K.map π := by rw [hKmap]; exact k.2
    obtain ⟨kK, hkK, hkπ⟩ := Subgroup.mem_map.mp hkKbar
    have hconjNL : kK * nL * kK⁻¹ ∈ NL :=
      hNL_normal.conj_mem ⟨nL, hNL_le_K hnL⟩ hnL ⟨kK, hkK⟩
    refine Subgroup.mem_map.mpr ⟨kK * nL * kK⁻¹, hconjNL, ?_⟩
    rw [map_mul, map_mul, map_inv, hkπ, hnπ]
    rfl
  have hNL_dvd : Nat.card ↥NL ∣ Nat.card ↥N := by
    rw [← Subgroup.card_map_of_injective c.L.subtype_injective (K := NL)]
    rw [Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hNbar_odd : Odd (Nat.card ↥Nbar) :=
    Odd.of_dvd_nat hNodd ((Subgroup.card_map_dvd NL π).trans hNL_dvd)
  have hNbar_bot : Nbar = ⊥ := hKbar_odd Nbar hNbar_le hNbar_normal hNbar_odd
  have hNL_le_ker : NL ≤ π.ker := (Subgroup.map_eq_bot_iff (f := π) NL).mp hNbar_bot
  have hNL_le_N : NL ≤ CFSG.Open.pCore 2 ↥c.L := by
    have h := hNL_le_ker
    rwa [QuotientGroup.ker_mk'] at h
  have hNL_bot : NL = ⊥ := by
    have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
      (H := CFSG.Open.pCore 2 ↥c.L) (K := NL)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) (Odd.of_dvd_nat hNodd hNL_dvd)
    rw [inf_eq_right.mpr hNL_le_N] at h
    exact h
  have hNcard : Nat.card ↥N = 1 := by
    have hmapN : NL.map c.L.subtype = N :=
      Subgroup.map_subgroupOf_eq_of_le hN_le_L
    have hNLeq : Nat.card ↥N = Nat.card ↥NL := by
      rw [← hmapN, Subgroup.card_map_of_injective c.L.subtype_injective]
    rw [hNLeq, hNL_bot]
    simp
  exact Subgroup.eq_bot_of_card_eq N hNcard


private lemma exists_nonsolvable_a3 {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6L4 : K6L4) {r : ℕ} (hlie : IsLie811 c.Lbar .l4 r 1)
    (hr : r ∈ uniqueFourSigma c.S.M)
    (a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L)
    (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hc₀ : IsSumZeroCoords h.Abar c₀)
    (hv3 : orderOf (a Case811L4.vA3 : G) = 3) :
    ∃ K : Subgroup G,
      K ≤ c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA3 : G)} : Set G) ∧
      ¬ IsSolvable ↥K ∧
      ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) →
        N ≤ Subgroup.centralizer (K : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hK6 := (hK6L4 c.Lbar r hlie hr5).2 h.Abar h.isElemAbelian_Abar h.card_Abar c₀ hc₀
  obtain ⟨Kbar, hKbar_le, hKbar_nonsolv, hKbar_odd⟩ := hK6.2.2.2.2.2.2.2.2
  let H : Subgroup G := c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA3 : G)} : Set G)
  let HL : Subgroup ↥c.L := H.subgroupOf c.L
  have hmapH : HL.map π = Subgroup.centralizer ({c₀ Case811L4.vA3} : Set c.Lbar) :=
    map_centralizer_subgroupOf hr a c₀ ha_apply Case811L4.vA3 hv3
  have hKbar_le_map : Kbar ≤ HL.map π := by
    rw [hmapH]
    exact hKbar_le
  let K : Subgroup ↥c.L := (Kbar.comap π) ⊓ HL
  have hKle : K ≤ HL := inf_le_right
  have hKmap : K.map π = Kbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.1
    · intro hx
      have hxmap : x ∈ HL.map π := hKbar_le_map hx
      obtain ⟨y, hyHL, hyx⟩ := hxmap
      exact ⟨y, ⟨by change π y ∈ Kbar; rwa [hyx], hyHL⟩, hyx⟩
  let KG : Subgroup G := K.map c.L.subtype
  have hKG_le : KG ≤ c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA3 : G)} : Set G) := by
    have hmapHL : HL.map c.L.subtype =
        c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA3 : G)} : Set G) :=
      Subgroup.map_subgroupOf_eq_of_le (H := c.L ⊓
        Subgroup.centralizer ({(a Case811L4.vA3 : G)} : Set G)) (K := c.L) inf_le_left
    rw [← hmapHL]
    exact Subgroup.map_mono hKle
  let f : ↥K →* ↥Kbar := (π.comp K.subtype).codRestrict Kbar (fun x => by
    have hx : π (x : ↥c.L) ∈ K.map π := ⟨x, x.2, rfl⟩
    rwa [hKmap] at hx)
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : c.Lbar) ∈ K.map π := by rw [hKmap]; exact y.2
    obtain ⟨x, hxK, hxπ⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxK⟩, Subtype.ext hxπ⟩
  have hKbar_solv_of_K : Group.IsSolvable ↥K → Group.IsSolvable ↥Kbar := fun hsolv =>
    Group.isSolvable_of_surjective (f := f) hf_surj
  have hK_solv_of_KG : Group.IsSolvable ↥KG → Group.IsSolvable ↥K := by
    intro hsolv
    let e : ↥K ≃* ↥KG := Subgroup.equivMapOfInjective K c.L.subtype c.L.subtype_injective
    haveI : Group.IsSolvable ↥KG := hsolv
    exact Group.isSolvable_of_isSolvable_injective (G := ↥K) (G' := ↥KG)
      (f := e.toMonoidHom) e.injective
  have hKG_nonsolv : ¬ IsSolvable ↥KG := fun hsolv =>
    hKbar_nonsolv (hKbar_solv_of_K (hK_solv_of_KG hsolv))
  have hKG_le_L : KG ≤ c.L := Subgroup.map_subtype_le K
  refine ⟨KG, hKG_le, hKG_nonsolv, ?_⟩
  intro N hNK hNnormal hNodd
  let NL : Subgroup ↥c.L := N.subgroupOf c.L
  have hN_le_L : N ≤ c.L := hNK.trans hKG_le_L
  have hNL_le_K : NL ≤ K := by
    intro x hx
    have hxG : (x : G) ∈ N := hx
    have hxKG : (x : G) ∈ KG := hNK hxG
    obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hxKG
    have hxy : x = y := Subtype.ext hyx.symm
    rwa [hxy]
  have hNL_normal : (NL.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hnN : (n : G) ∈ N := hn
    let nKG : ↥KG := ⟨(n : G), hNK hnN⟩
    let kKG : ↥KG := ⟨(k : G), Subgroup.mem_map_of_mem c.L.subtype k.2⟩
    have hnN' : nKG ∈ N.subgroupOf KG := hnN
    have hconjN : (k : G) * (n : G) * (k : G)⁻¹ ∈ N :=
      hNnormal.conj_mem nKG hnN' kKG
    exact hconjN
  let Nbar : Subgroup c.Lbar := NL.map π
  have hNbar_le : Nbar ≤ Kbar := by
    rw [← hKmap]
    exact Subgroup.map_mono hNL_le_K
  have hNbar_normal : (Nbar.subgroupOf Kbar).Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hnNbar : (n : c.Lbar) ∈ Nbar := hn
    obtain ⟨nL, hnL, hnπ⟩ := Subgroup.mem_map.mp hnNbar
    have hkKbar : (k : c.Lbar) ∈ K.map π := by rw [hKmap]; exact k.2
    obtain ⟨kK, hkK, hkπ⟩ := Subgroup.mem_map.mp hkKbar
    have hconjNL : kK * nL * kK⁻¹ ∈ NL :=
      hNL_normal.conj_mem ⟨nL, hNL_le_K hnL⟩ hnL ⟨kK, hkK⟩
    refine Subgroup.mem_map.mpr ⟨kK * nL * kK⁻¹, hconjNL, ?_⟩
    rw [map_mul, map_mul, map_inv, hkπ, hnπ]
    rfl
  have hNL_dvd : Nat.card ↥NL ∣ Nat.card ↥N := by
    rw [← Subgroup.card_map_of_injective c.L.subtype_injective (K := NL)]
    rw [Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hNbar_odd : Odd (Nat.card ↥Nbar) :=
    Odd.of_dvd_nat hNodd ((Subgroup.card_map_dvd NL π).trans hNL_dvd)
  have hNbar_cent : Nbar ≤ Subgroup.centralizer (Kbar : Set c.Lbar) :=
    hKbar_odd Nbar hNbar_le hNbar_normal hNbar_odd
  have hNL_odd : Odd (Nat.card ↥NL) := Odd.of_dvd_nat hNodd hNL_dvd
  have hNL_ker_bot : NL ⊓ π.ker = ⊥ := by
    have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
      (H := π.ker) (K := NL) (by
        rw [QuotientGroup.ker_mk']
        exact CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) hNL_odd
    rwa [inf_comm] at h
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let nKG : ↥KG := ⟨n, hNK hn⟩
  let kKG : ↥KG := ⟨k, hk⟩
  have hnN' : nKG ∈ N.subgroupOf KG := hn
  have hconjN : k * n * k⁻¹ ∈ N := hNnormal.conj_mem nKG hnN' kKG
  have hnN : n ∈ N := hn
  have hcommN : n * k * n⁻¹ * k⁻¹ ∈ N := by
    have h : k * n * k⁻¹ * n⁻¹ ∈ N := N.mul_mem hconjN (N.inv_mem hnN)
    have := N.inv_mem h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  let nL : ↥c.L := ⟨n, hN_le_L hn⟩
  let kL : ↥c.L := ⟨k, hKG_le_L hk⟩
  have hcommL_ker : nL * kL * nL⁻¹ * kL⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have hnbar : π nL ∈ Nbar := Subgroup.mem_map.mpr ⟨nL, hn, rfl⟩
    obtain ⟨kK, hkK, hkK_eq⟩ := Subgroup.mem_map.mp hk
    have hkL_eq : kL = kK := Subtype.ext hkK_eq.symm
    have hkbar : π kL ∈ Kbar := by
      rw [hkL_eq, ← hKmap]
      exact ⟨kK, hkK, rfl⟩
    have hcent := hNbar_cent hnbar
    have hcomm1 : π kL * π nL = π nL * π kL :=
      Subgroup.mem_centralizer_iff.mp hcent (π kL) hkbar
    simp only [map_mul, map_inv]
    rw [← hcomm1]
    group
  have hcommL_NL : nL * kL * nL⁻¹ * kL⁻¹ ∈ NL := hcommN
  have hcommL_bot : nL * kL * nL⁻¹ * kL⁻¹ = 1 := by
    have hmem : nL * kL * nL⁻¹ * kL⁻¹ ∈ NL ⊓ π.ker := ⟨hcommL_NL, hcommL_ker⟩
    rwa [hNL_ker_bot, Subgroup.mem_bot] at hmem
  have hcommG : n * k * n⁻¹ * k⁻¹ = 1 := by
    have := congrArg Subtype.val hcommL_bot
    simpa using this
  have hnk : n * k = k * n := by
    calc n * k = (n * k * n⁻¹ * k⁻¹) * (k * n) := by group
      _ = k * n := by rw [hcommG, one_mul]
  exact hnk.symm


private lemma map_centralizer_conj {c : Counterexample4 G} (h : Case811Sylow c) {x y : G}
    (hxM : x ∈ c.S.M) :
    (c.L ⊓ Subgroup.centralizer ({y} : Set G)).map (MulAut.conj x).toMonoidHom =
      c.L ⊓ Subgroup.centralizer ({MulAut.conj x y} : Set G) := by
  classical
  have hxN : x ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L hxM
  have hxL : ∀ z : G, z ∈ c.L ↔ MulAut.conj x z ∈ c.L := by
    intro z
    exact Subgroup.mem_normalizer_iff.mp hxN z
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzL : z ∈ c.L := hz.1
    have hzC : ∀ u ∈ ({y} : Set G), u * z = z * u :=
      Subgroup.mem_centralizer_iff.mp hz.2
    refine ⟨(hxL z).mp hzL, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro u hu
    have hu' : u = MulAut.conj x y := by simpa using hu
    rw [hu']
    have hcomm : z * y = y * z := (hzC y (by simp)).symm
    calc MulAut.conj x y * MulAut.conj x z =
        MulAut.conj x (y * z) := by rw [map_mul]
      _ = MulAut.conj x (z * y) := by rw [hcomm]
      _ = MulAut.conj x z * MulAut.conj x y := by rw [map_mul]
  · rintro ⟨hwL, hwC⟩
    have hwC' : ∀ u ∈ ({MulAut.conj x y} : Set G), u * w = w * u :=
      Subgroup.mem_centralizer_iff.mp hwC
    refine ⟨MulAut.conj x⁻¹ w, ⟨(hxL _).mpr ?_, Subgroup.mem_centralizer_iff.mpr ?_⟩, ?_⟩
    · have hconj : MulAut.conj x (MulAut.conj x⁻¹ w) = w := by
        show x * (x⁻¹ * w * (x⁻¹)⁻¹) * x⁻¹ = w
        group
      rwa [hconj]
    · intro u hu
      have hu' : u = y := by simpa using hu
      rw [hu']
      have hcomm : x * y * x⁻¹ * w = w * (x * y * x⁻¹) := hwC' _ (by simp)
      have h' : y * (x⁻¹ * w * x) = (x⁻¹ * w * x) * y := by
        calc y * (x⁻¹ * w * x)
            = x⁻¹ * ((x * y * x⁻¹) * w) * x := by group
          _ = x⁻¹ * (w * (x * y * x⁻¹)) * x := by rw [hcomm]
          _ = (x⁻¹ * w * x) * y := by group
      simpa [MulAut.conj_apply] using h'
    · show x * (x⁻¹ * w * (x⁻¹)⁻¹) * x⁻¹ = w
      group


private lemma factorization_three_centralizer_eq {c : Counterexample4 G} (h : Case811Sylow c)
    {r : ℕ} (hr : r ∈ uniqueFourSigma c.S.M) {V : Type*} [Group V]
    (a : V →* ↥c.L) (c₀ : V →* c.Lbar)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) (v : V)
    (hv3 : orderOf (a v : G) = 3) :
    (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({(a v : G)} : Set G))).factorization 3 =
      (Nat.card ↥(c.L ⊓ Subgroup.centralizer ({(a v : G)} : Set G))).factorization 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let K : Subgroup G := c.S.M ⊓ Subgroup.centralizer ({(a v : G)} : Set G)
  let H : Subgroup G := c.L ⊓ Subgroup.centralizer ({(a v : G)} : Set G)
  have hHK : H ≤ K := inf_le_inf c.hyp81.1 le_rfl
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 K
  have hTK : T ≤ K := hT.le
  have hT3 : IsPGroup 3 T := hT.isPGroup
  have hTleM : T ≤ c.S.M := hTK.trans inf_le_left
  obtain ⟨S, hS_eq⟩ := h.sylow.exists_sylow_eq_subgroupOf
  let W : Subgroup ↥c.S.M := T.subgroupOf c.S.M
  have hW3 : IsPGroup 3 W := hT3.comap_subtype (K := c.S.M)
  obtain ⟨cM, -, hcW⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (K := ⊤) S le_top W le_top hW3
  let cG : G := (cM : ↥c.S.M)
  have hcM : cG ∈ c.S.M := cM.2
  let Tc : Subgroup G := T.map (MulAut.conj cG).toMonoidHom
  have hTc_card : Nat.card ↥Tc = Nat.card ↥T :=
    Subgroup.card_map_of_injective (MulAut.conj cG).injective
  have hTc3 : IsPGroup 3 ↥Tc := hT3.map _
  have hSP : (S : Subgroup ↥c.S.M).map c.S.M.subtype = h.P := by
    rw [hS_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.sylow.le]
  have hTc_le_P : Tc ≤ h.P := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have htM : t ∈ c.S.M := hTleM ht
    have htW : (⟨t, htM⟩ : ↥c.S.M) ∈ W := ht
    have hmem := hcW (Subgroup.mem_map.mpr ⟨⟨t, htM⟩, htW, rfl⟩)
    have hmap := Subgroup.mem_map_of_mem c.S.M.subtype hmem
    rwa [hSP] at hmap
  have hTc_le_L : Tc ≤ c.L := hTc_le_P.trans h.P_le_L
  have hTc_cent : Tc ≤ Subgroup.centralizer
      ({(MulAut.conj cG (a v : G))} : Set G) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have htK : t ∈ K := hTK ht
    have htcent : t ∈ Subgroup.centralizer ({(a v : G)} : Set G) := htK.2
    have htcent' : ∀ u ∈ ({(a v : G)} : Set G), u * t = t * u :=
      Subgroup.mem_centralizer_iff.mp htcent
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro u hu
    have hu' : u = MulAut.conj cG (a v : G) := by simpa using hu
    rw [hu']
    have hcomm : t * (a v : G) = (a v : G) * t := (htcent' _ (by simp)).symm
    have hmap := congrArg (MulAut.conj cG) hcomm
    simpa [map_mul] using hmap.symm
  let Hc : Subgroup G := c.L ⊓ Subgroup.centralizer
    ({(MulAut.conj cG (a v : G))} : Set G)
  have hHc_map : H.map (MulAut.conj cG).toMonoidHom = Hc :=
    map_centralizer_conj h hcM
  have hHc_card : Nat.card ↥Hc = Nat.card ↥H := by
    rw [← hHc_map, Subgroup.card_map_of_injective (MulAut.conj cG).injective]
  have hTc_le_Hc : Tc ≤ Hc := le_inf hTc_le_L hTc_cent
  have hTc_dvd : Nat.card ↥Tc ∣ Nat.card ↥Hc := Subgroup.card_dvd_of_le hTc_le_Hc
  obtain ⟨k, hk⟩ := hTc3.exists_card_eq
  have hk_le : k ≤ (Nat.card ↥Hc).factorization 3 := by
    rw [hk] at hTc_dvd
    exact (Nat.prime_three.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hTc_dvd
  have hTc_le_pow : Nat.card ↥Tc ≤ 3 ^ (Nat.card ↥H).factorization 3 := by
    rw [hHc_card] at hk_le
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk_le
  have hT_card : Nat.card ↥T = 3 ^ (Nat.card ↥K).factorization 3 := hT.card_eq
  have hKfac_le : (Nat.card ↥K).factorization 3 ≤ (Nat.card ↥H).factorization 3 := by
    have hle : 3 ^ (Nat.card ↥K).factorization 3 ≤ 3 ^ (Nat.card ↥H).factorization 3 := by
      rw [← hT_card, ← hTc_card]
      exact hTc_le_pow
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hHfac_le : (Nat.card ↥H).factorization 3 ≤ (Nat.card ↥K).factorization 3 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hHK) 3
  exact le_antisymm hKfac_le hHfac_le


private lemma exists_sylow_a2 {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6d : K6dL4) (hK6L4 : K6L4) {r : ℕ} (hlie : IsLie811 c.Lbar .l4 r 1)
    (hr : r ∈ uniqueFourSigma c.S.M)
    (a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L)
    (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar)
    (ha_range : a.range = h.A.subgroupOf c.L)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hc₀ : IsSumZeroCoords h.Abar c₀)
    (hv3 : orderOf (a Case811L4.vA2 : G) = 3) :
    ∃ Q : Subgroup G, h.A ≤ Q ∧ IsMulCommutative ↥Q ∧
      CFSG.ABGLocalTools.IsSylowOf 3 Q
        (c.S.M ⊓ Subgroup.centralizer ({(a Case811L4.vA2 : G)} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hK6 := (hK6L4 c.Lbar r hlie hr5).2 h.Abar h.isElemAbelian_Abar h.card_Abar c₀ hc₀
  let CLbarA : Subgroup c.Lbar := Subgroup.centralizer (h.Abar : Set c.Lbar)
  have hcommAbar : IsMulCommutative ↥CLbarA :=
    hK6d c.Lbar r hlie hr5 h.Abar h.isElemAbelian_Abar h.card_Abar
  haveI : IsMulCommutative ↥h.Abar := h.isElemAbelian_Abar.1
  have hAbar_le_cent : h.Abar ≤ CLbarA := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hcomm : x * y = y * x := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥h.Abar)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    exact hcomm.symm
  have hAbar_sub3 : IsPGroup 3 ↥(h.Abar.subgroupOf CLbarA) :=
    h.isElemAbelian_Abar.isPGroup.comap_subtype (K := CLbarA)
  obtain ⟨QbarS, hQbarS_ge⟩ := hAbar_sub3.exists_le_sylow
  let Qbar : Subgroup c.Lbar := (QbarS : Subgroup ↥CLbarA).map CLbarA.subtype
  have hQbar_sylow : CFSG.ABGLocalTools.IsSylowOf 3 Qbar CLbarA := ⟨QbarS, rfl⟩
  have hAbar_le_Qbar : h.Abar ≤ Qbar := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAbar_le_cent]
    exact Subgroup.map_mono hQbarS_ge
  have hQbar_sylow_a2 : CFSG.ABGLocalTools.IsSylowOf 3 Qbar
      (Subgroup.centralizer ({c₀ Case811L4.vA2} : Set c.Lbar)) :=
    hK6.2.2.2.2.2.2.1 Qbar hQbar_sylow
  let H2 : Subgroup G := c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA2 : G)} : Set G)
  let K2 : Subgroup G := c.S.M ⊓ Subgroup.centralizer ({(a Case811L4.vA2 : G)} : Set G)
  let HL2 : Subgroup ↥c.L := H2.subgroupOf c.L
  let CLbar2 : Subgroup c.Lbar := Subgroup.centralizer ({c₀ Case811L4.vA2} : Set c.Lbar)
  have hmapH2 : HL2.map π = CLbar2 :=
    map_centralizer_subgroupOf hr a c₀ ha_apply Case811L4.vA2 hv3
  have hQbar_le_CLbar2 : Qbar ≤ CLbar2 := hQbar_sylow_a2.le
  have hQbar_le_map : Qbar ≤ HL2.map π := by
    rw [hmapH2]
    exact hQbar_le_CLbar2
  let Q0 : Subgroup ↥c.L := (Qbar.comap π) ⊓ HL2
  have hQ0_le_HL2 : Q0 ≤ HL2 := inf_le_right
  have hQ0map : Q0.map π = Qbar := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.1
    · intro hx
      have hxmap : x ∈ HL2.map π := hQbar_le_map hx
      obtain ⟨y, hyHL, hyx⟩ := hxmap
      exact ⟨y, ⟨by change π y ∈ Qbar; rwa [hyx], hyHL⟩, hyx⟩
  let AL : Subgroup ↥c.L := h.A.subgroupOf c.L
  have ha_memA : (a Case811L4.vA2 : G) ∈ h.A := by
    have hv : a Case811L4.vA2 ∈ a.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rwa [ha_range] at hv
  haveI : IsMulCommutative ↥h.A := h.elemAbelian.1
  have hAL_le_HL2 : AL ≤ HL2 := by
    intro x hx
    have hxA : (x : G) ∈ h.A := hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hy' : y = (a Case811L4.vA2 : G) := by simpa using hy
    rw [hy']
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥h.A)).comm ⟨(x : G), hxA⟩
        ⟨(a Case811L4.vA2 : G), ha_memA⟩)).symm
  have hAL_le_Q0 : AL ≤ Q0 := by
    refine le_inf ?_ hAL_le_HL2
    intro x hx
    change π x ∈ Qbar
    exact hAbar_le_Qbar ⟨x, hx, rfl⟩
  have hX3 : IsPGroup 3 AL := h.elemAbelian.isPGroup.comap_subtype (K := c.L)
  obtain ⟨S, hS_ge⟩ := (hX3.comap_subtype (K := Q0)).exists_le_sylow
  let QL : Subgroup ↥c.L := (S : Subgroup ↥Q0).map Q0.subtype
  have hQL_le_Q0 : QL ≤ Q0 := Subgroup.map_subtype_le _
  have hQL3 : IsPGroup 3 ↥QL := S.isPGroup'.map Q0.subtype
  have hAL_le_QL : AL ≤ QL := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAL_le_Q0]
    exact Subgroup.map_mono hS_ge
  have hQ0fac : (Nat.card ↥Q0).factorization 3 = (Nat.card ↥Qbar).factorization 3 := by
    have hcard := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf
      (G := ↥c.L) π Q0
    rw [hQ0map] at hcard
    have hker2 : IsPGroup 2 ↥(π.ker ⊓ Q0) := by
      rw [QuotientGroup.ker_mk']
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).to_le inf_le_left
    rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hker2
          Nat.prime_three (by norm_num)),
      add_zero]
  have hS_card : Nat.card ↥(S : Subgroup ↥Q0) = 3 ^ (Nat.card ↥Q0).factorization 3 :=
    Sylow.card_eq_multiplicity S
  have hQLcard : Nat.card ↥QL = 3 ^ (Nat.card ↥Q0).factorization 3 := by
    rw [← hS_card]
    exact Subgroup.card_map_of_injective Q0.subtype_injective
  have hQbar_card : Nat.card ↥Qbar = 3 ^ (Nat.card ↥CLbar2).factorization 3 :=
    hQbar_sylow_a2.card_eq
  have hQbar_fac : (Nat.card ↥Qbar).factorization 3 =
      (Nat.card ↥CLbar2).factorization 3 := by
    rw [hQbar_card, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_three, smul_eq_mul, mul_one]
  have hCL2fac : (Nat.card ↥CLbar2).factorization 3 = (Nat.card ↥H2).factorization 3 := by
    have hcard := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf
      (G := ↥c.L) π HL2
    rw [hmapH2] at hcard
    have hker2 : IsPGroup 2 ↥(π.ker ⊓ HL2) := by
      rw [QuotientGroup.ker_mk']
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).to_le inf_le_left
    have hcardH : Nat.card ↥HL2 = Nat.card ↥H2 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hcard' : Nat.card ↥H2 = Nat.card ↥CLbar2 * Nat.card ↥(π.ker ⊓ HL2) := by
      rw [← hcardH, hcard]
    rw [hcard', Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hker2
          Nat.prime_three (by norm_num)),
      add_zero]
  have hH2fac : (Nat.card ↥H2).factorization 3 = (Nat.card ↥K2).factorization 3 :=
    (factorization_three_centralizer_eq h hr a c₀ ha_apply Case811L4.vA2 hv3).symm
  have hQLcardK : Nat.card ↥QL = 3 ^ (Nat.card ↥K2).factorization 3 := by
    rw [hQLcard, hQ0fac, hQbar_fac, hCL2fac, hH2fac]
  have hQL_eq_Qbar_card : Nat.card ↥QL = Nat.card ↥Qbar := by
    rw [hQLcardK, hQbar_card, hCL2fac, hH2fac]
  have hQLmap_eq : QL.map π = Qbar := by
    have hle : QL.map π ≤ Qbar := by
      rw [← hQ0map]
      exact Subgroup.map_mono hQL_le_Q0
    have hinj : Function.Injective (π.comp QL.subtype) :=
      CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := N)
        (Q := QL) hN3 hQL3
    let eQL : ↥QL ≃* ↥(QL.map π) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]))
    have hcard : Nat.card ↥(QL.map π) = Nat.card ↥Qbar := by
      rw [← Nat.card_congr eQL.toEquiv, hQL_eq_Qbar_card]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hrange : (π.comp QL.subtype).range = Qbar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hQLmap_eq
  have hinj : Function.Injective (π.comp QL.subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := N)
      (Q := QL) hN3 hQL3
  let e : ↥QL ≃* ↥Qbar :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hQbar_comm : IsMulCommutative ↥Qbar := by
    refine ⟨⟨fun x y => ?_⟩⟩
    refine Subtype.ext ?_
    have h := (IsMulCommutative.is_comm (M := ↥CLbarA)).comm
      ⟨x, hQbar_sylow.le x.2⟩ ⟨y, hQbar_sylow.le y.2⟩
    simpa using congrArg Subtype.val h
  have hQL_comm : IsMulCommutative ↥QL :=
    Function.Surjective.isMulCommutative e.symm.surjective hQbar_comm
  let Q : Subgroup G := QL.map c.L.subtype
  have hQ_card : Nat.card ↥Q = Nat.card ↥QL :=
    Subgroup.card_map_of_injective c.L.subtype_injective
  have hQ_comm : IsMulCommutative ↥Q := by
    let eQ : ↥QL ≃* ↥Q := Subgroup.equivMapOfInjective QL c.L.subtype c.L.subtype_injective
    exact Function.Surjective.isMulCommutative eQ.surjective hQL_comm
  have hQ_le_H2 : Q ≤ H2 := by
    have hmapHL2 : HL2.map c.L.subtype = H2 :=
      Subgroup.map_subgroupOf_eq_of_le (H := H2) (K := c.L) inf_le_left
    rw [← hmapHL2]
    exact Subgroup.map_mono (hQL_le_Q0.trans hQ0_le_HL2)
  have hQ_le_M : Q ≤ c.S.M := hQ_le_H2.trans (inf_le_left.trans c.hyp81.1)
  have hQ_le_K2 : Q ≤ K2 := le_inf hQ_le_M (hQ_le_H2.trans inf_le_right)
  have hQ_cardK : Nat.card ↥Q = 3 ^ (Nat.card ↥K2).factorization 3 := by
    rw [hQ_card, hQLcardK]
  have hA_le_Q : h.A ≤ Q := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h.A_le_L]
    exact Subgroup.map_mono hAL_le_QL
  exact ⟨Q, hA_le_Q, hQ_comm,
    CFSG.ABGLocalTools.isSylowOf_of_card hQ_le_K2 hQ_cardK⟩


private lemma orderOf_a_of_nonconstant {c : Counterexample4 G} (h : Case811Sylow c)
    (a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L)
    (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar)
    (ha_range : a.range = h.A.subgroupOf c.L)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hc₀ : IsSumZeroCoords h.Abar c₀)
    {v : Multiplicative (Fin 4 → ZMod 3)}
    (hv : ¬ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s) :
    orderOf (a v : G) = 3 := by
  have ha_mem : (a v : G) ∈ h.A := by
    have hv' : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at hv'
  have hpow : (a v : G) ^ 3 = 1 := h.elemAbelian.2 _ ha_mem
  have hne : (a v : G) ≠ 1 := by
    intro h1
    have h1' : a v = 1 := Subtype.ext h1
    have hc1 : c₀ v = 1 := by rw [← ha_apply v, h1', map_one]
    exact hv ((hc₀.2.1 v).mp hc1)
  exact orderOf_eq_prime hpow hne

theorem Case811Sylow.exists_case811L4 {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) (hK6d : K6dL4) (hK6L4 : K6L4) {r : ℕ} (hlie : IsLie811 c.Lbar .l4 r 1)
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (hC : CFSG.Open.pRank r ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) = 0) :
    ∃ t : Case811L4 c, t.toCase811Sylow = h ∧ t.r = r := by
  classical
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  obtain ⟨c₀, a, e, hc₀, ha_range, ha_apply, he_eq, he_range, he_eq_one_iff, he_exists_perm⟩ :=
    exists_coords_data h hK6c hlie
  subst e
  have hmemL := mem_L_of_kernel hK6L4 hlie hr hC
  have hdvd := dvd_card_centralizer_of_K6L4 h hK6L4 hlie hr c₀ hc₀
  have hvA1 : orderOf (a Case811L4.vA1 : G) = 3 :=
    orderOf_a_of_nonconstant h a c₀ ha_range ha_apply hc₀ (by decide)
  have hvA2 : orderOf (a Case811L4.vA2 : G) = 3 :=
    orderOf_a_of_nonconstant h a c₀ ha_range ha_apply hc₀ (by decide)
  have hvA3 : orderOf (a Case811L4.vA3 : G) = 3 :=
    orderOf_a_of_nonconstant h a c₀ ha_range ha_apply hc₀ (by decide)
  have hK6 := (hK6L4 c.Lbar r hlie hr5).2 h.Abar h.isElemAbelian_Abar h.card_Abar c₀ hc₀
  have hfac1 : (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer
      ({(a Case811L4.vA1 : G)} : Set G))).factorization r = 2 := by
    rw [factorization_centralizer_eq h hmemL hr a c₀ ha_apply Case811L4.vA1 hvA1]
    exact hK6.2.1
  have hfac2 : (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer
      ({(a Case811L4.vA2 : G)} : Set G))).factorization r = 1 := by
    rw [factorization_centralizer_eq h hmemL hr a c₀ ha_apply Case811L4.vA2 hvA2]
    exact hK6.2.2.1
  have hfac3 : (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer
      ({(a Case811L4.vA3 : G)} : Set G))).factorization r = 3 := by
    rw [factorization_centralizer_eq h hmemL hr a c₀ ha_apply Case811L4.vA3 hvA3]
    exact hK6.2.2.2.1
  have hp1 : 2 ≤ CFSG.Open.pRank r
      (c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA1 : G)} : Set G) : Subgroup G) := by
    rw [pRank_centralizer_eq hr a c₀ ha_apply Case811L4.vA1 hvA1]
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank r
      (Subgroup.centralizer ({c₀ Case811L4.vA1} : Set c.Lbar))]
    change 2 ≤ CFSG.pRank r
      ↥(Subgroup.centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, -1, -1])} : Set c.Lbar))
    rw [hK6.2.2.2.2.1]
  have hp3 : 2 ≤ CFSG.Open.pRank r
      (c.L ⊓ Subgroup.centralizer ({(a Case811L4.vA3 : G)} : Set G) : Subgroup G) := by
    rw [pRank_centralizer_eq hr a c₀ ha_apply Case811L4.vA3 hvA3]
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank r
      (Subgroup.centralizer ({c₀ Case811L4.vA3} : Set c.Lbar))]
    change 2 ≤ CFSG.pRank r
      ↥(Subgroup.centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 1, 0])} : Set c.Lbar))
    rw [hK6.2.2.2.2.2.1]
  obtain ⟨K1, hK1le, hK1comm, hK1card, hK1odd⟩ :=
    exists_perfect_a1 h hK6L4 hlie hr a c₀ ha_apply hc₀ hvA1
  obtain ⟨K3, hK3le, hK3non, hK3odd⟩ :=
    exists_nonsolvable_a3 h hK6L4 hlie hr a c₀ ha_apply hc₀ hvA3
  obtain ⟨Q, hAQ, hQcomm, hQsylow⟩ :=
    exists_sylow_a2 h hK6d hK6L4 hlie hr a c₀ ha_range ha_apply hc₀ hvA2
  let t : Case811L4 c :=
    { toCase811Sylow := h, r := r, lie := hlie, mem_sigma := hr,
      e := c.L.subtype.comp a, range_e := he_range, e_eq_one_iff := he_eq_one_iff,
      exists_perm := he_exists_perm, mem_L := hmemL, dvd_card_centralizer := hdvd,
      factorization_a1 := hfac1, factorization_a2 := hfac2, factorization_a3 := hfac3,
      two_le_pRank_a1 := hp1, two_le_pRank_a3 := hp3,
      perfect_a1 := ⟨K1, hK1le, hK1comm, hK1card, hK1odd⟩,
      nonsolvable_a3 := ⟨K3, hK3le, hK3non, hK3odd⟩,
      sylow_a2 := ⟨Q, hAQ, hQcomm, hQsylow⟩ }
  exact ⟨t, rfl, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
