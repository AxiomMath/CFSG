module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12G2
public import CFSG.RankThree.PartTwo.Sec12.Hering129LRank
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY5
import CFSG.Goldschmidt.Steps.Sec82e
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KS12G2
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three (R3 adjointEquivR3 one14 canon14 dec14
  dec14_injective)

namespace G23

@[expose] def wU : List ℕ := [0]

@[expose] def wS : List ℕ := [3]

@[expose] def wV : List ℕ := [3, 2, 3, 0, 2, 3, 0, 2, 3, 0, 2]

@[expose] def wT : List ℕ := [2, 0, 2, 0]

@[expose] def cU : List ℕ := wordCode wU

@[expose] def cS : List ℕ := wordCode wS

@[expose] def cV : List ℕ := wordCode wV

@[expose] def cT : List ℕ := wordCode wT

theorem relations :
    mulF (mulF cU cU) cU = one14 ∧ mulF (mulF cS cS) cS = one14 ∧
    mulF (mulF cV cV) cV = one14 ∧
    mulF cU cV = mulF cV cU ∧ mulF cU cS = mulF cS cU ∧ mulF cS cV = mulF cV cS ∧
    mulF cT cT = one14 ∧ mulF cT cU = mulF cU cT ∧ mulF cT cV = mulF cV cT ∧
    cU ≠ one14 ∧ cV ≠ one14 ∧ cT ≠ one14 ∧ cV ≠ cU ∧ cV ≠ mulF cU cU ∧
    cS ≠ one14 ∧ cS ≠ cV ∧ cS ≠ mulF cV cV ∧ cS ≠ cU ∧ cS ≠ mulF cU cV ∧
    cS ≠ mulF cU (mulF cV cV) ∧ cS ≠ mulF cU cU ∧ cS ≠ mulF (mulF cU cU) cV ∧
    cS ≠ mulF (mulF cU cU) (mulF cV cV) := by
  decide +kernel

section Facts


theorem wordCode_append (w w' : List ℕ) :
    wordCode (w ++ w') = mulF (wordCode w) (wordCode w') := by
  refine dec14_injective (canon14_wordCode _) (canon14_mulF _ _) ?_
  rw [← coe_wordGL, wordGL_append, Units.val_mul, coe_wordGL, coe_wordGL, dec14_mulF]

theorem cube_of {w : List ℕ} (h : mulF (mulF (wordCode w) (wordCode w)) (wordCode w) = one14) :
    wordR3 w ^ 3 = 1 := by
  rw [pow_three', ← wordR3_append, ← wordR3_append, ← wordR3_nil]
  apply wordR3_eq_of_code
  rw [wordCode_append, wordCode_append, wordCode_nil]
  exact h

theorem comm_of {w w' : List ℕ} (h : mulF (wordCode w) (wordCode w') =
    mulF (wordCode w') (wordCode w)) : wordR3 w * wordR3 w' = wordR3 w' * wordR3 w := by
  rw [← wordR3_append, ← wordR3_append]
  apply wordR3_eq_of_code
  rw [wordCode_append, wordCode_append]
  exact h

theorem sq_of {w : List ℕ} (h : mulF (wordCode w) (wordCode w) = one14) :
    wordR3 w ^ 2 = 1 := by
  rw [wordR3_sq, ← wordR3_nil]
  apply wordR3_eq_of_code
  rw [wordCode_append, wordCode_nil]
  exact h

theorem u_cube : wordR3 wU ^ 3 = 1 := cube_of relations.1

theorem s_cube : wordR3 wS ^ 3 = 1 := cube_of relations.2.1

theorem v_cube : wordR3 wV ^ 3 = 1 := cube_of relations.2.2.1

theorem u_comm_v : wordR3 wU * wordR3 wV = wordR3 wV * wordR3 wU :=
  comm_of relations.2.2.2.1

theorem u_comm_s : wordR3 wU * wordR3 wS = wordR3 wS * wordR3 wU :=
  comm_of relations.2.2.2.2.1

theorem s_comm_v : wordR3 wS * wordR3 wV = wordR3 wV * wordR3 wS :=
  comm_of relations.2.2.2.2.2.1

theorem t_sq : wordR3 wT ^ 2 = 1 := sq_of relations.2.2.2.2.2.2.1

theorem t_comm_u : wordR3 wT * wordR3 wU = wordR3 wU * wordR3 wT :=
  comm_of relations.2.2.2.2.2.2.2.1

theorem t_comm_v : wordR3 wT * wordR3 wV = wordR3 wV * wordR3 wT :=
  comm_of relations.2.2.2.2.2.2.2.2.1

theorem u_ne_one : wordR3 wU ≠ 1 :=
  wordR3_ne_one_of relations.2.2.2.2.2.2.2.2.2.1

theorem v_ne_one : wordR3 wV ≠ 1 :=
  wordR3_ne_one_of relations.2.2.2.2.2.2.2.2.2.2.1

theorem t_ne_one : wordR3 wT ≠ 1 :=
  wordR3_ne_one_of relations.2.2.2.2.2.2.2.2.2.2.2.1

theorem v_ne_u : wordR3 wV ≠ wordR3 wU :=
  wordR3_ne_of_code relations.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem v_ne_u_sq : wordR3 wV ≠ wordR3 wU ^ 2 := by
  rw [wordR3_sq]
  refine wordR3_ne_of_code ?_
  rw [wordCode_append]
  exact relations.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_ne_pow_mul_pow : ∀ i j : ℕ, i < 3 → j < 3 →
    wordR3 wS ≠ wordR3 wU ^ i * wordR3 wV ^ j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    relations
  intro i j hi hj
  interval_cases i <;> interval_cases j
  · rw [pow_zero, pow_zero, mul_one]
    exact wordR3_ne_one_of h0
  · rw [pow_zero, one_mul, pow_one]
    exact wordR3_ne_of_code h1
  · rw [pow_zero, one_mul, wordR3_sq]
    refine wordR3_ne_of_code ?_
    rw [wordCode_append]
    exact h2
  · rw [pow_zero, pow_one, mul_one]
    exact wordR3_ne_of_code h3
  · rw [pow_one, pow_one, ← wordR3_append]
    refine wordR3_ne_of_code ?_
    rw [wordCode_append]
    exact h4
  · rw [pow_one, wordR3_sq, ← wordR3_append]
    refine wordR3_ne_of_code ?_
    rw [wordCode_append, wordCode_append]
    exact h5
  · rw [pow_zero, mul_one, wordR3_sq]
    refine wordR3_ne_of_code ?_
    rw [wordCode_append]
    exact h6
  · rw [wordR3_sq, pow_one, ← wordR3_append]
    refine wordR3_ne_of_code ?_
    rw [wordCode_append, wordCode_append]
    exact h7
  · rw [wordR3_sq, wordR3_sq, ← wordR3_append]
    refine wordR3_ne_of_code ?_
    rw [wordCode_append, wordCode_append, wordCode_append]
    exact h8

end Facts

section EFT

theorem exists_EFT_of_elements {Z : Type} [Group Z] {u v s t : Z} (hu : u ^ 3 = 1)
    (hv : v ^ 3 = 1) (hs : s ^ 3 = 1) (huv : u * v = v * u) (hus : u * s = s * u)
    (hsv : s * v = v * s) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvu : v ≠ u) (hvu2 : v ≠ u ^ 2)
    (hsne : ∀ i j : ℕ, i < 3 → j < 3 → s ≠ u ^ i * v ^ j) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htu : t * u = u * t) (htv : t * v = v * t) :
    ∃ E F T : Subgroup Z, E ≤ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card E = 9 ∧
      Nat.card F = 27 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set Z) := by
  obtain ⟨B, hBa, hBb⟩ : ∃ B : CFSG.RankThree.Asc83Table.E9Basis Z, B.a = u ∧ B.b = v :=
    ⟨CFSG.RankThree.Asc83Table.E9Basis.ofNe hu hv huv hu1 hv1 hvu hvu2, rfl, rfl⟩
  have hEq : ∀ e ∈ B.sub, e ^ 3 = 1 := by
    intro e he
    obtain ⟨i, j, -, -, rfl⟩ := B.exists_pow_mul_pow he
    rw [((B.hab.pow_pow i j)).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3, pow_mul,
      pow_mul, B.ha, B.hb, one_pow, one_pow, one_mul]
  have hasc : Commute B.a s := by rw [hBa]; exact hus
  have hbsc : Commute B.b s := by rw [hBb]; exact hsv.symm
  have hatc : Commute B.a t := by rw [hBa]; exact htu.symm
  have hbtc : Commute B.b t := by rw [hBb]; exact htv.symm
  have hsE : s ∉ B.sub := by
    intro hs'
    obtain ⟨i, j, hi, hj, hij⟩ := B.exists_pow_mul_pow hs'
    exact hsne i j hi hj (by rw [hij, hBa, hBb])
  have hz : ∀ e ∈ B.sub, e * s = s * e := by
    intro e he
    obtain ⟨i, j, -, -, rfl⟩ := B.exists_pow_mul_pow he
    exact ((hasc.pow_left i).mul_left (hbsc.pow_left j)).eq
  have hcard : Nat.card B.sub = 3 ^ 2 := by rw [B.card]; norm_num
  have hF := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers Nat.prime_three hcard hEq hs hsE hz
  refine ⟨B.sub, B.sub ⊔ Subgroup.zpowers s, Subgroup.zpowers t, le_sup_left, hF.1, B.card,
    by rw [hF.2]; norm_num, ?_, ?_, ?_⟩
  · intro h
    exact ht1 (Subgroup.zpowers_eq_bot.mp h)
  · exact IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
  · intro e he
    obtain ⟨i, j, -, -, rfl⟩ := B.exists_pow_mul_pow he
    exact mem_normalizer_zpowers_of_comm ((hatc.pow_left i).mul_left (hbtc.pow_left j)).eq


theorem exists_EFT_R3 :
    ∃ E F T : Subgroup ↥R3, E ≤ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card E = 9 ∧
      Nat.card F = 27 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set ↥R3) :=
  exists_EFT_of_elements (u := wordR3 wU) (v := wordR3 wV) (s := wordR3 wS) (t := wordR3 wT)
    u_cube v_cube s_cube u_comm_v u_comm_s s_comm_v u_ne_one v_ne_one v_ne_u v_ne_u_sq
    s_ne_pow_mul_pow t_sq t_ne_one t_comm_u t_comm_v

end EFT

end G23

section Transport

variable {G : Type} [Group G] [Finite G]

theorem false_of_isoEFT {Z : Type} [Group Z] (hFE : partTwoF G = partTwoE G) {Y : Subgroup G}
    {x : G} (hx : x ∈ Subgroup.centralizer (Y : Set G)) (hx3 : orderOf x = 3) (hxY : x ∉ Y)
    (e : Y ⧸ aschbacherSolvableCore 3 Y ≃* Z)
    (h : ∃ E F T : Subgroup Z, E ≤ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card E = 9 ∧
      Nat.card F = 27 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set Z)) : False := by
  obtain ⟨E, F, T, hEF, hF, hE9, hF27, hT, hT2, hET⟩ := h
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  refine false_of_lift_of_partTwoF_eq hFE hx hx3 hxY
    (E := E.map e.symm.toMonoidHom) (F := F.map e.symm.toMonoidHom)
    (T := T.map e.symm.toMonoidHom) (Subgroup.map_mono hEF)
    (CFSG.Open.IsElemAbelian.map hF _) (by rw [Subgroup.card_map_of_injective hinj, hE9])
    (by rw [Subgroup.card_map_of_injective hinj, hF27]) ?_ (hT2.map _) ?_
  · intro h0
    exact hT ((Subgroup.map_eq_bot_iff_of_injective (H := T) hinj).mp h0)
  · rintro _ ⟨w, hw, rfl⟩
    exact (KFacts.mulEquiv_mem_normalizer_map_iff e.symm T w).mpr (hET hw)

end Transport

section YG2


theorem nonempty_equiv_R3_of_isoGTwo {Q : Type} [Group Q] {r : TauCeti.PrimePower}
    (hr3 : r.card = 3) (h : Sec4.IsoGTwo Q r) : Nonempty (Q ≃* ↥R3) := by
  obtain ⟨K, _, _, hcard, -, ⟨e⟩⟩ := Hering129KModels.exists_adjoint_model h
  haveI : Fintype K := Fintype.ofFinite K
  have hFc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard, hr3]
  let ρ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hFc
  exact ⟨(e.trans (CFSG.TauCetiBridge.adjointGroupCongr (τ := .G2) ρ)).trans adjointEquivR3⟩

section Glue

variable {G : Type} [Group G] [Finite G]

theorem not_mem_of_center_theta_eq_bot {x : G} {Y : Subgroup G} (hx3 : orderOf x = 3)
    (hYx : Y ≤ Subgroup.centralizer ({x} : Set G))
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥) : x ∉ Y := by
  intro hxY
  have hc : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x, hxY⟩ ∈
      Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      have hg : (g : G) * x = x * (g : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hYx g.2)
      change ((g * ⟨x, hxY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) =
        ((⟨x, hxY⟩ * g : Y) : Y ⧸ aschbacherSolvableCore 3 Y)
      rw [show (g * ⟨x, hxY⟩ : Y) = ⟨x, hxY⟩ * g from Subtype.ext hg]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  have hord : orderOf (⟨⟨x, hxY⟩, hc⟩ : ↥(aschbacherSolvableCore 3 Y)) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx3]
  have h3dvd : 3 ∣ Nat.card ↥(aschbacherSolvableCore 3 Y) := by
    have hdvd := orderOf_dvd_natCard (⟨⟨x, hxY⟩, hc⟩ : ↥(aschbacherSolvableCore 3 Y))
    rwa [hord] at hdvd
  exact three_not_dvd_card_aschbacherSolvableCore h3dvd

theorem card_eq_three_or_range {X : Type} [Group X] [Finite X] {r : TauCeti.PrimePower}
    (hX : SectionFourHyp X) (h : IsG2D4 X r 1) (hr3 : 3 ≤ r.card) :
    r.card = 3 ∨ (4 ≤ r.card ∧ r.p ≠ 3) := by
  by_cases h4 : 4 ≤ r.card
  · right
    refine ⟨h4, fun hp3 => ?_⟩
    rcases p_eq_two_or_exponent_eq_one_of_sectionFourHyp_g2 hX h with h2 | hexp
    · omega
    · have : r.card = r.p := by rw [TauCeti.PrimePower.card_def, hexp, pow_one]
      omega
  · left
    omega

theorem gap129YG2Range_of (h1 : Sec4.Item4_1LargePrime) : Gap129YG2Range := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb Y hY hXY r hIso
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  have hYle : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  have hS4 : SectionFourHyp (Y ⧸ aschbacherSolvableCore 3 Y) :=
    sectionFourHyp_quot_of_mem_thetaComponentsAt h1 hstd.toTheoremFourHyp hx1 hYx
  have hGD : IsG2D4 (Y ⧸ aschbacherSolvableCore 3 Y) r 1 := Or.inl ⟨rfl, hIso⟩
  have hr3 : 3 ≤ r.card := by
    obtain ⟨hv, -⟩ := hIso
    exact (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rcases card_eq_three_or_range hS4 hGD hr3 with hrc | hrange
  · exfalso
    obtain ⟨eR⟩ := nonempty_equiv_R3_of_isoGTwo hrc hIso
    have hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ :=
      Hering129KModels.center_eq_bot_of_isG2D4 hGD
    have hx3o : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hxC : x ∈ Subgroup.centralizer (Y : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hYle hy)
    have hxY : x ∉ Y := not_mem_of_center_theta_eq_bot hx3o hYle hZ
    have hEFT := G23.exists_EFT_R3
    have h1 := @false_of_isoEFT G _ _ ↥R3 _ hstd.partTwoF_eq Y x hxC hx3o hxY eR
    exact h1 hEFT
  · exact hrange

end Glue

end YG2

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
