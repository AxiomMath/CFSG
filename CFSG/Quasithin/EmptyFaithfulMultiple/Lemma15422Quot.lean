module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Local
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Layer

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15422

section Solvable

variable {H : Type*} [Group H] [Finite H]

theorem centralizer_le_of_isSolvable [Group.IsSolvable H]
    (hO : ∀ B : Subgroup H, B.Normal → Odd (Nat.card B) → B = ⊥) :
    Subgroup.centralizer (Open.pCore 2 H : Set H) ≤ Open.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.fittingSubgroup H ≤ Open.pCore 2 H := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have : Fact q.1.1.Prime := ⟨hq⟩
    by_cases h2 : q.1.1 = 2
    · have hn : (CFSG.pCore q.1.1 H).Normal := CFSG.pCore_normal
      have hp : IsPGroup 2 (CFSG.pCore q.1.1 H) := h2 ▸ CFSG.pCore_isPGroup
      exact CFSG.LieType.BorelTits.le_pCore 2 hn hp
    · have hb : CFSG.pCore q.1.1 H = ⊥ := by
        refine hO _ CFSG.pCore_normal ?_
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := q.1.1) (G := H))
        rw [hk]
        exact (hq.odd_of_ne_two h2).pow
      rw [hb]
      exact bot_le
  exact (Subgroup.centralizer_le hF).trans
    ((CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance).trans hF)

end Solvable

section Transfer

variable {G : Type*} [Group G]

theorem charTwo_subgroupOf {X L : Subgroup G} (hXL : X ≤ L) (h : CharTwo X) :
    CharTwo (X.subgroupOf L) := by
  rw [CFSG.QuasithinUnique.charTwo_iff_internal] at h ⊢
  exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
    (Subgroup.subgroupOfEquivOfLe hXL).symm h

theorem mem_oTwoUpper_subgroupOf [Finite G] {I K L : Subgroup G} (hKI : K ≤ I) (hLK : L ≤ K)
    (hL : L = oTwoUpper L) {v : G} (hv : v ∈ L) (hvI : v ∈ I) :
    (⟨v, hvI⟩ : ↥I) ∈ oTwoUpper (K.subgroupOf I) := by
  have hmap := oTwoUpper_map I.subtype (K.subgroupOf I)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKI] at hmap
  have hvL : v ∈ oTwoUpper L := by
    rw [← hL]
    exact hv
  have hvK : v ∈ oTwoUpper K := oTwoUpper_mono hLK hvL
  rw [hmap] at hvK
  obtain ⟨w, hw, hwv⟩ := hvK
  have : w = ⟨v, hvI⟩ := Subtype.ext hwv
  rwa [← this]

end Transfer

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

structure Hyp15422 (s : Setting15419 G T) : Prop where
  hyp : MultipleCentralizerHypothesis G T
  hnot : ¬ IsLThreeTwoOrASix G
  h12 : Stmt15412 G T
  h14 : Stmt15414 G T
  h17 : Stmt15417 G T
  h19 : Stmt15419 G T
  h20 : Stmt15420 G T
  hI : ¬ CharTwo s.I

namespace Hyp15422

variable {s : Setting15419 G T}

omit [Finite G] in
theorem mem_pCore_iff {x : ↥s.I} : x ∈ Open.pCore 2 ↥s.I ↔ (x : G) ∈ pCoreOf 2 s.I := by
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem swap (h : Hyp15422 s) : Hyp15422 (swapSetting s) :=
  { h with hI := by rw [swapSetting_I]; exact h.hI }

theorem triple (h : Hyp15422 s) : F6.IsGoldschmidtTripleIn s.I s.G₁ s.G₂ :=
  isGoldschmidtTripleIn s h.hyp h.h12 h.h19 (isSylowTwoOf_T₀ s h.h19 h.h20)

theorem isSylowIn (h : Hyp15422 s) :
    IsSylowIn 2 (Open.pCore 2 ↥s.I) (CFSG.pPrimeCore 3 ↥s.I) := by
  obtain ⟨h1, h2, h3⟩ := h.triple.isSylowTwoOf_pCore_pPrimeCore
  exact ⟨h1, h2, h3⟩

theorem not_centralizer_le (h : Hyp15422 s) :
    ¬ Subgroup.centralizer (Open.pCore 2 ↥s.I : Set ↥s.I) ≤ Open.pCore 2 ↥s.I :=
  fun hc => h.hI (CFSG.QuasithinUnique.charTwo_iff_internal.mpr hc)

theorem oddCore (h : Hyp15422 s) :
    ∀ B : Subgroup ↥s.I, B.Normal → Odd (Nat.card B) → B = ⊥ := by
  intro B hBn hBo
  rw [eq_bot_iff]
  intro b hb
  have hBle : B ≤ fusionOddCore ↥s.I := le_sSup ⟨hBn, hBo⟩
  have hbO : (b : G) ∈ oddCoreIn s.I := by
    change (b : G) ∈ (fusionOddCore ↥s.I).map s.I.subtype
    exact ⟨b, hBle hb, rfl⟩
  have hb2 := sq_eq_one_of_mem_oddCoreIn s h.hyp h.hnot h.h14 h.h17 h.h19 h.h20 hbO
  have hb2' : b ^ 2 = 1 := Subtype.ext (by simpa using hb2)
  have h1 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hb2'
  have h2 : orderOf b ∣ Nat.card B := by
    have := orderOf_dvd_natCard (⟨b, hb⟩ : B)
    rwa [Subgroup.orderOf_mk] at this
  have hodd : Odd (orderOf b) := Odd.of_dvd_nat hBo h2
  have h3 : orderOf b = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h4 | h4
    · exact h4
    · rw [h4] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)

theorem inf_pPrimeCore_eq_bot (h : Hyp15422 s) :
    (quasithinOmegaOneCenter T).subgroupOf s.I ⊓ CFSG.pPrimeCore 3 ↥s.I = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Open.pCore 2 ↥s.I).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  rw [eq_bot_iff]
  intro x hx
  have hx2 : (x : G) ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hx.1).2.2
  have hxQ : x ∈ Open.pCore 2 ↥s.I := mem_of_isPGroup_zpowers h.isSylowIn hx.2
    (isPGroup_zpowers_of_sq (Subtype.ext (by simpa using hx2)))
  have hxZ : (x : G) ∈ quasithinOmegaOneCenter T ⊓ pCoreOf 2 s.I :=
    ⟨hx.1, mem_pCore_iff.mp hxQ⟩
  rw [omegaOneCenter_inf_pCoreOf_eq_bot s h.hyp h.h17 h.h19 h.h20 h.hI, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.mpr (Subtype.ext hxZ)

theorem mk_ne_one (h : Hyp15422 s) {z : ↥s.I} (hz : (z : G) ∈ quasithinOmegaOneCenter T)
    (hz1 : (z : G) ≠ 1) : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I) z ≠ 1 := by
  intro h1
  have : z ∈ (quasithinOmegaOneCenter T).subgroupOf s.I ⊓ CFSG.pPrimeCore 3 ↥s.I :=
    ⟨hz, (QuotientGroup.eq_one_iff z).mp h1⟩
  rw [h.inf_pPrimeCore_eq_bot, Subgroup.mem_bot] at this
  exact hz1 (congrArg Subtype.val this)

theorem exists_mk_eq (h : Hyp15422 s) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ ∃ (hzI : z ∈ s.I) (v : G) (hvI : v ∈ s.I),
      v ∈ s.L₁ ∧ QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I) ⟨z, hzI⟩ =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I) ⟨v, hvI⟩ := by
  obtain ⟨z, hz, hz1, v, hv, hzv⟩ := exists_mem_L₁ s h.hyp h.h12 h.h19
  have hzI : z ∈ s.I := T₀_le_I s (omegaOneCenter_le_T₀ s hz)
  have hvI : v ∈ s.I := (le_sup_left.trans le_sup_left : s.L₁ ≤ s.I) hv
  refine ⟨z, hz, hz1, hzI, v, hvI, hv, ?_⟩
  have hmem : (⟨z, hzI⟩ : ↥s.I) * (⟨v, hvI⟩ : ↥s.I)⁻¹ ∈ CFSG.pPrimeCore 3 ↥s.I :=
    h.isSylowIn.le (mem_pCore_iff.mpr hzv)
  have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)
      ((⟨z, hzI⟩ : ↥s.I) * (⟨v, hvI⟩ : ↥s.I)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem config (h : Hyp15422 s) :
    Config15422 ((s.G₁.subgroupOf s.I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)))
      ((s.G₂.subgroupOf s.I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)))
      (((quasithinOmegaOneCenter T).subgroupOf s.I).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pPrimeCore 3 ↥s.I with hNdef
  set π := QuotientGroup.mk' N with hπ
  set Z := quasithinOmegaOneCenter T with hZdef
  have htr := h.triple
  have hZT₀ : Z ≤ s.T₀ := omegaOneCenter_le_T₀ s
  have hZI : Z ≤ s.I := hZT₀.trans (T₀_le_I s)
  have hZN := h.inf_pPrimeCore_eq_bot
  have hZcard : Nat.card (Z.subgroupOf s.I) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv]
    exact (h.h14 h.hnot).2
  have hZ'card : Nat.card ((Z.subgroupOf s.I).map π) = 4 := by
    rw [F6.card_map_mk, ← Subgroup.inf_relIndex_right, inf_comm, hZN, Subgroup.relIndex_bot_left,
      hZcard]
  rcases htr.goldschmidt_mod_pPrimeCore with ⟨hinf, hamal, -⟩ | ⟨-, -, ⟨e⟩, -, -⟩
  swap
  · exfalso
    have h6 : Nat.card (↥s.I ⧸ N) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have hdvd := Subgroup.card_subgroup_dvd_card ((Z.subgroupOf s.I).map π)
    rw [hZ'card, h6] at hdvd
    exact absurd hdvd (by decide)
  refine ⟨hamal, hZ'card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx2 : (x : G) ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hx).2.2
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    rw [← map_pow, this, map_one]
  · rw [hinf]
    refine Subgroup.map_mono fun x hx => ⟨?_, ?_⟩
    · exact (le_sup_right : s.T₀ ≤ s.G₁) (hZT₀ hx)
    · exact (le_sup_right : s.T₀ ≤ s.G₂) (hZT₀ hx)
  · rw [hinf]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have htT₀ : (t : G) ∈ s.T₀ := by
      rw [← G₁_inf_G₂ s h.hyp h.h12 h.h19]
      exact ⟨ht.1, ht.2⟩
    have hc : t * x = x * t := Subtype.ext ((Subgroup.mem_centralizer_iff.mp
      (mem_quasithinOmegaOneCenter_iff.mp hx).2.1) t (T₀_le s htT₀))
    rw [← map_mul, ← map_mul, hc]
  · obtain ⟨z, hz, hz1, hzc⟩ := exists_mem_centralizer_G₁ s h.hnot h.h14
    have hzI : z ∈ s.I := hZI hz
    refine ⟨π ⟨z, hzI⟩, ⟨⟨z, hzI⟩, hz, rfl⟩, h.mk_ne_one hz hz1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    have hc : g * ⟨z, hzI⟩ = ⟨z, hzI⟩ * g :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzc) g hg)
    rw [← map_mul, ← map_mul, hc]
  · obtain ⟨z, hz, hz1, hzc⟩ := exists_mem_centralizer_G₂ s h.hnot h.h14
    have hzI : z ∈ s.I := hZI hz
    refine ⟨π ⟨z, hzI⟩, ⟨⟨z, hzI⟩, hz, rfl⟩, h.mk_ne_one hz hz1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    have hc : g * ⟨z, hzI⟩ = ⟨z, hzI⟩ * g :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzc) g hg)
    rw [← map_mul, ← map_mul, hc]
  · obtain ⟨z, hz, hz1, hzI, v, hvI, hv, hzv⟩ := h.exists_mk_eq
    refine ⟨π ⟨z, hzI⟩, ⟨⟨z, hzI⟩, hz, rfl⟩, h.mk_ne_one hz hz1, ?_⟩
    rw [hzv, oTwoUpper_map]
    exact Subgroup.mem_map_of_mem π (mem_oTwoUpper_subgroupOf le_sup_left le_sup_left
      (factor_L₁ s).eq_oTwoUpper hv hvI)
  · obtain ⟨z, hz, hz1, hzI', v, hvI', hv, hzv⟩ := h.swap.exists_mk_eq
    have hzI : z ∈ s.I := by rw [← swapSetting_I s]; exact hzI'
    have hvI : v ∈ s.I := by rw [← swapSetting_I s]; exact hvI'
    have hzv' : π ⟨z, hzI⟩ = π ⟨v, hvI⟩ := by
      have e : ∀ (I' : Subgroup G) (hI' : I' = s.I) (hz' : z ∈ I') (hv' : v ∈ I'),
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I') ⟨z, hz'⟩ =
            QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I') ⟨v, hv'⟩ →
          π ⟨z, hzI⟩ = π ⟨v, hvI⟩ := by
        rintro I' rfl hz' hv' h'
        exact h'
      exact e _ (swapSetting_I s) hzI' hvI' hzv
    refine ⟨π ⟨z, hzI⟩, ⟨⟨z, hzI⟩, hz, rfl⟩, h.mk_ne_one hz hz1, ?_⟩
    rw [hzv', oTwoUpper_map]
    exact Subgroup.mem_map_of_mem π (mem_oTwoUpper_subgroupOf le_sup_right le_sup_left
      (factor_L₂ s).eq_oTwoUpper hv hvI)
  · intro hsolv
    have hNsolv : Group.IsSolvable ↥N := htr.isSolvable_pPrimeCore
    have : Group.IsSolvable ↥s.I := Group.isSolvable_of_ker_le_range N.subtype π
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
    exact h.not_centralizer_le (centralizer_le_of_isSolvable h.oddCore)

theorem exists_u (h : Hyp15422 s) :
    ∃ u : ↥s.I, u ∈ s.T₀.subgroupOf s.I ∧ (∀ t ∈ s.T₀.subgroupOf s.I, t * u = u * t) ∧
      u ^ 2 = 1 ∧ QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I) u ≠ 1 ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I) u ∈
        oTwoUpper (⊤ : Subgroup (↥s.I ⧸ CFSG.pPrimeCore 3 ↥s.I)) ∧
      CharTwo (Subgroup.centralizer ({u} : Set ↥s.I)) := by
  obtain ⟨z, hz, hz1, hzI, v, hvI, hv, hzv⟩ := h.exists_mk_eq
  obtain ⟨hzT, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hz
  refine ⟨⟨z, hzI⟩, omegaOneCenter_le_T₀ s hz, fun t ht => ?_, Subtype.ext (by simpa using hz2),
    h.mk_ne_one hz hz1, ?_, ?_⟩
  · exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzC) t (T₀_le s ht))
  · rw [hzv]
    have hv' := mem_oTwoUpper_subgroupOf (le_sup_left : s.G₁ ≤ s.I) le_sup_left
      (factor_L₁ s).eq_oTwoUpper hv hvI
    have hv'' : (⟨v, hvI⟩ : ↥s.I) ∈ oTwoUpper (⊤ : Subgroup ↥s.I) := oTwoUpper_mono le_top hv'
    have hmap := oTwoUpper_map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)) (⊤ : Subgroup ↥s.I)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ hv''
  · have hc := charTwo_subgroupOf (inf_le_left : s.I ⊓ Subgroup.centralizer ({z} : Set G) ≤ s.I)
      (charTwo_inf_centralizer s h.hyp h.h17 h.h19 h.h20 hz hz1)
    have heq : (s.I ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf s.I =
        Subgroup.centralizer ({⟨z, hzI⟩} : Set ↥s.I) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨-, hx⟩
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx)
      · intro hx
        exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hx)⟩
    rwa [heq] at hc

theorem oTwoUpper_le_closure (h : Hyp15422 s) :
    oTwoUpper (⊤ : Subgroup ↥s.I) ≤ Subgroup.closure {y : ↥s.I | y ^ 3 = 1} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htr := h.triple.subgroupOf
  rw [← F6.twoResidual_eq_oTwoUpper, F6.twoResidual_top_eq htr, F6.twoResidual_eq_oTwoUpper,
    F6.twoResidual_eq_oTwoUpper]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_T₀ s h.hyp)
  have hcard : ∀ (s' : Setting15419 G T), s'.T₀ = s.T₀ → s'.I = s.I →
      Nat.card ↥(s'.G₁.subgroupOf s.I) = 2 ^ a * 3 := by
    intro s' hT hI
    have hG₁I : s'.G₁ ≤ s.I := hI ▸ le_sup_left
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG₁I).toEquiv]
    have h1 := Subgroup.relIndex_mul_card s'.T₀ s'.G₁
    rw [relIndex_T₀_G₁ s' h.hyp h.h12, inf_eq_left.mpr le_sup_right, hT, ha] at h1
    rw [← h1, mul_comm]
  have hle : ∀ K : Subgroup ↥s.I, (∃ k : ℕ, Nat.card K = 2 ^ k * 3) →
      oTwoUpper K ≤ Subgroup.closure {y : ↥s.I | y ^ 3 = 1} := by
    rintro K ⟨k, hk⟩
    refine Subgroup.closure_mono fun x hx => ?_
    have hx3 := pow_three_eq_one_of_odd hk (g := ⟨x, hx.1⟩)
      (by rw [Subgroup.orderOf_mk]; exact hx.2)
    exact congrArg Subtype.val hx3
  refine sup_le (hle _ ⟨a, hcard s rfl rfl⟩) (hle _ ⟨a, ?_⟩)
  have := hcard (swapSetting s) (swapSetting_T₀ s) (swapSetting_I s)
  rwa [swapSetting_G₁] at this

end Hyp15422

theorem stmt15422_of_caseEight
    (hyp : MultipleCentralizerHypothesis G T)
    (hnot : ¬ IsLThreeTwoOrASix G) (h12 : Stmt15412 G T) (h14 : Stmt15414 G T)
    (h17 : Stmt15417 G T) (h19 : Stmt15419 G T) (h20 : Stmt15420 G T)
    (hcase : ∀ s : Setting15419 G T, ¬ CharTwo s.I →
      Config15422 ((s.G₁.subgroupOf s.I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)))
        ((s.G₂.subgroupOf s.I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I)))
        (((quasithinOmegaOneCenter T).subgroupOf s.I).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥s.I))) →
      IsCaseEight15422 (↥s.I ⧸ CFSG.pPrimeCore 3 ↥s.I)) :
    Stmt15422 G T := by
  intro s hI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Hyp15422 s := ⟨hyp, hnot, h12, h14, h17, h19, h20, hI⟩
  have hc := h.config
  obtain ⟨u, huT, huc, hu2, hu1, huO, huC⟩ := h.exists_u
  have hT₀I := T₀_le_I s
  have hT₀2 : IsPGroup 2 (s.T₀.subgroupOf s.I) :=
    (isPGroup_T₀ s hyp).of_equiv (Subgroup.subgroupOfEquivOfLe hT₀I).symm
  obtain ⟨K, hKO, hKT, ⟨eK⟩, φ, hφs, hφk, hφT⟩ := exists_alternatingGroup h.isSylowIn
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥s.I)).symm h.oddCore h.not_centralizer_le
    hc.amalgam.pCore_eq_bot hT₀2 (isSylowTwoOf_T₀ s h19 h20).2.2 huT huc hu2 hu1 huO huC
    h.oTwoUpper_le_closure (hcase s hI hc)
  refine ⟨K.map s.I.subtype, ?_, ?_, ⟨(K.equivMapOfInjective s.I.subtype
    s.I.subtype_injective).symm.trans eK⟩, φ, hφs, ?_⟩
  · rw [hKO, ← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · have h1 := congrArg (Subgroup.map s.I.subtype) hKT
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT₀I,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  · ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨T₀_le s (hφT hx), ?_⟩
      rw [hφk] at hx
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) k hk)
    · rintro ⟨-, hx⟩
      rw [hφk, Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) k ⟨k, hk, rfl⟩)

end L15422

end CFSG.Quasithin.EmptyFaithfulMultiple
