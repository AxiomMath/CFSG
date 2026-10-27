module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Eleven_exists_member_not_le (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G}
    (hVg : ¬ V ≤ conjSubgroup D.M g) :
    ∃ X ∈ wConj D.M V₀ V hV L, ¬ X ≤ conjSubgroup D.M g := by
  by_contra hcon
  push Not at hcon
  apply hVg
  rw [← iSup_wConj_eq D h1217 h.hyp151 hV hL]
  exact iSup₂_le fun X hX => hcon X hX

theorem s15_Eleven_exists_Bv_two (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    (hs2 : s15 D.M V₀ V hV L = 2) {g : G} {A : Subgroup G} {i : ℕ}
    (hAg : A ≤ conjSubgroup V g) (hAM : A ≤ D.M) (hmA : E3.mQuot (conjSubgroup V g) A = i)
    (hAN : ¬ A ≤ normalizer (wSub V₀ V hV L : Set G)) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) :
    ∃ (B : Subgroup G) (v : G), Cfg11 V D.M i g A B v ∧ v ∈ X := by
  have hA2 : IsPGroup 2 A := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hAg
  have hWX := s15_Glue3_normalizer_eq_of_s_two D h.hyp151 hV hs2 hX
  have hN : A ⊓ normalizer (X : Set G) = A ⊓ normalizer (wSub V₀ V hV L : Set G) := by
    ext x
    constructor
    · rintro ⟨hxA, hxX⟩
      refine ⟨hxA, ?_⟩
      have hmem : x ∈ D.M ⊓ normalizer (X : Set G) := ⟨hAM hxA, hxX⟩
      rw [hWX] at hmem
      exact hmem.2
    · rintro ⟨hxA, hxW⟩
      refine ⟨hxA, ?_⟩
      have hmem : x ∈ D.M ⊓ normalizer (wSub V₀ V hV L : Set G) := ⟨hAM hxA, hxW⟩
      rw [← hWX] at hmem
      exact hmem.2
  have hlt : A ⊓ normalizer (wSub V₀ V hV L : Set G) < A :=
    lt_of_le_of_ne inf_le_left fun heq => hAN (inf_eq_left.1 heq)
  have hne : A ⊓ normalizer (wSub V₀ V hV L : Set G) ≠ A := hlt.ne
  have hm1 := s15_Glue_mQuot_inf_normalizer_le_one D h.hyp151 hV hAM hA2 hs2
  have hm0 : E3.mQuot A (A ⊓ normalizer (wSub V₀ V hV L : Set G)) ≠ 0 := fun h0 =>
    hne ((E3.mQuot_eq_zero_iff hA2 inf_le_left).1 h0)
  have hm : E3.mQuot A (A ⊓ normalizer (wSub V₀ V hV L : Set G)) = 1 := by omega
  obtain ⟨v, hv, hcomm, ⟨a, haA, hanot⟩, hvX⟩ := s15_Glue3_seven_conj D h.hyp151 hV hL hX hAM hA2
    (inf_le_left : A ⊓ normalizer (wSub V₀ V hV L : Set G) ≤ A) hN.le hne
  refine ⟨A ⊓ normalizer (wSub V₀ V hV L : Set G), v,
    ⟨hAg, hAM, hmA, inf_le_left, hm, hv, ?_, ⟨a, haA, ?_⟩⟩, ?_⟩
  · intro b hb
    have := hcomm b hb
    rw [hV1] at this
    exact Subgroup.mem_bot.1 this
  · intro h1
    apply hanot
    rw [hV1, h1]
    exact Subgroup.one_mem _
  · exact hvX (hN.symm.le.trans inf_le_right)

theorem s15_Eleven_exists_transvection_member {Δ : Set (Subgroup G)} {t : G}
    (hcard : (suppAct Δ t).ncard = 2) (f : Subgroup G → ℕ)
    (h1 : ∀ E ∈ suppAct Δ t, 1 ≤ f E) (hsum : ∑ᶠ E ∈ suppAct Δ t, f E ≤ 3) :
    ∃ E ∈ suppAct Δ t, f E = 1 := by
  obtain ⟨a, b, hab, hS⟩ := Set.ncard_eq_two.1 hcard
  rw [hS] at h1 hsum ⊢
  rw [finsum_mem_pair hab] at hsum
  by_contra hcon
  push Not at hcon
  have ha := h1 a (Set.mem_insert _ _)
  have hb := h1 b (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have ha' := hcon a (Set.mem_insert _ _)
  have hb' := hcon b (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  omega

theorem s15_Eleven_normalizes_conj (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) (g : G) {y : G}
    (hy : y ∈ conjSubgroup D.M g) {x : G} (hx : x ∈ conjSubgroup X g) (hx1 : x ≠ 1)
    (hfix : y * x * y⁻¹ = x) : y ∈ normalizer (conjSubgroup X g : Set G) := by
  have hy' : g * y * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hy
  have hx' : g * x * g⁻¹ ∈ X := mem_conjSubgroup_iff.1 hx
  have hx1' : g * x * g⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, h1]
    group
  have hfix' : (g * y * g⁻¹) * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * x * g⁻¹ := by
    have e : (g * y * g⁻¹) * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * x * y⁻¹) * g⁻¹ := by
      group
    rw [e, hfix]
  have hN := s15_Glue3_normalizes_of_fixes D h hV hL hV1 hX hy' hx' hx1' hfix'
  rw [← E3.conjSubgroup_normalizer]
  exact mem_conjSubgroup_iff.2 hN

theorem s15_Eleven_axis_hyperplane {X F : Subgroup G} (hX : IsElemAbelian 2 X)
    (hF : IsElemAbelian 2 F) (hFN : F ≤ normalizer (X : Set G))
    (hC : ∀ x ∈ F, x ≠ 1 → ∀ y ∈ X, x * y * x⁻¹ = y → ∀ f ∈ F, f * y * f⁻¹ = y)
    (hfaith : ∀ x ∈ F, (∀ y ∈ X, x * y * x⁻¹ = y) → x = 1) :
    rk ↥F + E3.mQuot X (X ⊓ centralizer (F : Set G)) ≤ rk ↥X := by
  set K : Subgroup G := X ⊓ centralizer (F : Set G) with hK
  by_cases hXle : X ≤ centralizer (F : Set G)
  · have hKeq : K = X := by
      rw [hK]
      exact inf_eq_left.2 hXle
    have hmq : E3.mQuot X K = 0 := by rw [hKeq, E3.mQuot_self]
    have hFbot : F = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hfaith x hx fun y hy => by
        have hc := Subgroup.mem_centralizer_iff.1 (hXle hy) x hx
        calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hc]
          _ = y := by group)
    rw [hFbot, rk_bot, hmq]
    exact Nat.zero_le _
  · obtain ⟨u, huX, huC⟩ := IsConcreteLE.not_le_iff_exists.1 hXle
    let c : G → G := fun f => f * u * f⁻¹ * u⁻¹
    have hc_def : ∀ f, c f = f * u * f⁻¹ * u⁻¹ := fun f => rfl
    have hcX : ∀ f ∈ F, c f ∈ X := by
      intro f hf
      rw [hc_def f]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.1 (hFN hf) u).1 huX) (X.inv_mem huX)
    have hfixc : ∀ f ∈ F, f * c f * f⁻¹ = c f := by
      intro f hf
      have hff : f * f = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hF hf
      have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
      have huu : u * u = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hX huX
      have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
      have hdX : f * u * f⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hFN hf) u).1 huX
      have hdd : (f * u * f⁻¹) * (f * u * f⁻¹) = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hX hdX
      have hdinv : (f * u * f⁻¹)⁻¹ = f * u * f⁻¹ := inv_eq_of_mul_eq_one_right hdd
      have hcomm : (f * u * f⁻¹) * u = u * (f * u * f⁻¹) := CFSG.Open.IsElemAbelian.comm hX hdX huX
      have hfinv' : f⁻¹ * f⁻¹ = 1 := by rw [hfinv, hff]
      have hfixu : f * (f * u * f⁻¹) * f⁻¹ = u := by
        have e : f * (f * u * f⁻¹) * f⁻¹ = (f * f) * u * (f⁻¹ * f⁻¹) := by group
        rw [e, hff, hfinv']
        group
      have hinvu : f * u⁻¹ * f⁻¹ = (f * u * f⁻¹)⁻¹ := by group
      rw [hc_def f]
      calc f * (f * u * f⁻¹ * u⁻¹) * f⁻¹
          = (f * (f * u * f⁻¹) * f⁻¹) * (f * u⁻¹ * f⁻¹) := by group
        _ = u * (f * u⁻¹ * f⁻¹) := by rw [hfixu]
        _ = u * (f * u * f⁻¹)⁻¹ := by rw [hinvu]
        _ = u * (f * u * f⁻¹) := by rw [hdinv]
        _ = (f * u * f⁻¹) * u := hcomm.symm
        _ = (f * u * f⁻¹) * u⁻¹ := by rw [huinv]
        _ = f * u * f⁻¹ * u⁻¹ := by group
    have hcK : ∀ f ∈ F, c f ∈ K := by
      intro f hf
      refine ⟨hcX f hf, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro f' hf'
      by_cases hf1 : f = 1
      · have hc1 : c f = 1 := by
          rw [hc_def f, hf1]
          group
        rw [hc1]
        simp
      · have h := hC f hf hf1 (c f) (hcX f hf) (hfixc f hf) f' hf'
        calc f' * c f = (f' * c f * f'⁻¹) * f' := by group
          _ = c f * f' := by rw [h]
    have hinj_c : ∀ f ∈ F, ∀ f' ∈ F, c f = c f' → f = f' := by
      intro f hf f' hf' heq
      have heq' : f * u * f⁻¹ * u⁻¹ = f' * u * f'⁻¹ * u⁻¹ := by
        rw [← hc_def f, ← hc_def f']
        exact heq
      have hmain : f * u * f⁻¹ = f' * u * f'⁻¹ := by
        calc f * u * f⁻¹ = f * u * f⁻¹ * u⁻¹ * u := by group
          _ = f' * u * f'⁻¹ * u⁻¹ * u := congrArg (fun z => z * u) heq'
          _ = f' * u * f'⁻¹ := by group
      have hx : f⁻¹ * f' ∈ F := F.mul_mem (F.inv_mem hf) hf'
      have hxu : (f⁻¹ * f') * u * (f⁻¹ * f')⁻¹ = u := by
        calc (f⁻¹ * f') * u * (f⁻¹ * f')⁻¹
            = f⁻¹ * (f' * u * f'⁻¹) * f := by group
          _ = f⁻¹ * (f * u * f⁻¹) * f := by rw [hmain]
          _ = u := by group
      by_cases hx1 : f⁻¹ * f' = 1
      · simpa using inv_eq_of_mul_eq_one_right hx1
      · exfalso
        have hcu : u ∈ centralizer (F : Set G) := by
          refine Subgroup.mem_centralizer_iff.2 ?_
          intro f'' hf''
          have h'' := hC (f⁻¹ * f') hx hx1 u huX hxu f'' hf''
          calc f'' * u = (f'' * u * f''⁻¹) * f'' := by group
            _ = u * f'' := by rw [h'']
        exact huC hcu
    have hvarphi : Function.Injective (fun f : ↥F => (⟨c f.1, hcK f.1 f.2⟩ : ↥K)) := by
      intro a b hab
      exact Subtype.ext (hinj_c a.1 a.2 b.1 b.2 (congrArg Subtype.val hab))
    have hcard_le : Nat.card ↥F ≤ Nat.card ↥K :=
      Nat.card_le_card_of_injective _ hvarphi
    have hcardF : Nat.card ↥F = 2 ^ rk ↥F := by
      have h := E3.card_eq_two_pow_mul (V := F) (U := ⊥)
        (CFSG.Open.IsElemAbelian.isPGroup hF) bot_le
      rw [Subgroup.card_bot, mul_one, s15_FiveTen_mQuot_bot_eq_rk] at h
      exact h
    have hcardX : Nat.card ↥X = 2 ^ rk ↥X := by
      have h := E3.card_eq_two_pow_mul (V := X) (U := ⊥)
        (CFSG.Open.IsElemAbelian.isPGroup hX) bot_le
      rw [Subgroup.card_bot, mul_one, s15_FiveTen_mQuot_bot_eq_rk] at h
      exact h
    have hcardK : Nat.card ↥X = 2 ^ E3.mQuot X K * Nat.card ↥K := by
      refine E3.card_eq_two_pow_mul (CFSG.Open.IsElemAbelian.isPGroup hX) ?_
      rw [hK]
      exact inf_le_left
    have hpow : 2 ^ (rk ↥F + E3.mQuot X K) ≤ 2 ^ rk ↥X := by
      calc 2 ^ (rk ↥F + E3.mQuot X K)
          = 2 ^ rk ↥F * 2 ^ E3.mQuot X K := by rw [pow_add]
        _ = Nat.card ↥F * 2 ^ E3.mQuot X K := by rw [← hcardF]
        _ ≤ Nat.card ↥K * 2 ^ E3.mQuot X K :=
            Nat.mul_le_mul_right (2 ^ E3.mQuot X K) hcard_le
        _ = 2 ^ E3.mQuot X K * Nat.card ↥K := by rw [mul_comm]
        _ = Nat.card ↥X := hcardK.symm
        _ = 2 ^ rk ↥X := hcardX
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hpow

theorem s15_Eleven_exists_normalized_transvection_of_wClos
    (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥)
    (hW : E3.wClos V 0 D.M ≤ centralizer (V : Set G))
    (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    (hs2 : s15 D.M V₀ V hV L = 2) (hγ : 4 ≤ gamma15 D.M V₀ V hV L)
    {i : ℕ} (hi : i ≤ 2)
    (h4 : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M →
      4 ≤ E3.mQuot V U)
    {g : G} {A : Subgroup G} (hAg : A ≤ conjSubgroup V g) (hAM : A ≤ D.M)
    (hmA : E3.mQuot (conjSubgroup V g) A = i)
    (hAN : ¬ A ≤ normalizer (wSub V₀ V hV L : Set G)) :
    ∃ (X : Subgroup G) (v : G) (X₀ : Subgroup G),
      X ∈ wConj D.M V₀ V hV L ∧
      ¬ X ≤ conjSubgroup D.M g ∧
      v ∈ X ∧ v ≠ 1 ∧ v * v = 1 ∧ v ∈ conjSubgroup D.M g ∧
      ¬ V ≤ conjSubgroup D.M g ∧
      X₀ ∈ wConj D.M V₀ V hV L ∧
      v ∈ normalizer (conjSubgroup X₀ g : Set G) ∧
      E3.mQuot (conjSubgroup X₀ g)
        (conjSubgroup X₀ g ⊓ centralizer ({v} : Set G)) = 1 := by

  obtain ⟨B₀, v₀, hcfg₀⟩ := s15_Eleven_exists_Bv D h hV hL hV1 hAg hAM hmA hAN
  have hVg : ¬ V ≤ conjSubgroup D.M g :=
    (s15_Eleven_not_le_of_wClos D.M V hW hcfg₀).2
  obtain ⟨X, hX, hXg⟩ := s15_Eleven_exists_member_not_le D h1217 h hV hL hVg
  obtain ⟨B, v, hcfg, hvX⟩ := s15_Eleven_exists_Bv_two D h hV hL hV1 hs2 hAg hAM hmA hAN hX
  have hv1 : v ≠ 1 := by
    obtain ⟨a, -, ha⟩ := hcfg.comm_A
    rintro rfl
    exact ha (by group)
  have hvg : v ∈ conjSubgroup D.M g := s15_Eleven_v_mem_conj D hi hcfg h4
  obtain ⟨hc2, -, hcn, hn⟩ :=
    s15_Eleven_support_of_wClos D h1217 h hV hL hW hV1 hcfg hvg
  have hY := E3.isElemAbelian_conjSubgroup hV g
  have hind := s15_Glue3_wConjG_indep D h.hyp151 hV hL hV1 g
  have hspan := s15_Glue3_wConjG_sSup D h1217 h.hyp151 hV hL g
  have hγΔ : ∀ E ∈ wConjG D.M V₀ V hV L g, rk ↥E = gamma15 D.M V₀ V hV L :=
    fun E hE => s15_Glue3_wConjG_rk D h.hyp151 hV hV1 g hE
  have ht : v * v = 1 := s15_Eleven_sq hV hcfg.v_mem
  have hperm : ∀ E ∈ wConjG D.M V₀ V hV L g, conjSubgroup E v ∈ wConjG D.M V₀ V hV L g :=
    fun E hE => s15_Glue3_wConjG_perm D hV hvg hE
  have hΔcard : (wConjG D.M V₀ V hV L g).ncard = 2 := by
    rw [s15_Glue3_wConjG_ncard D h.hyp151 hV g]
    exact hs2
  have hsub : suppAct (wConjG D.M V₀ V hV L g) v ⊆ wConjG D.M V₀ V hV L g := fun E hE => hE.1
  have hsuppcard : (suppAct (wConjG D.M V₀ V hV L g) v).ncard = 2 := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hnlt : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) <
      gamma15 D.M V₀ V hV L := by omega
  have hfin := s15_Support_eq_finsum hY hind hspan hγΔ ht hperm hnlt
  have hsum : ∑ᶠ E ∈ suppAct (wConjG D.M V₀ V hV L g) v,
      E3.mQuot E (E ⊓ centralizer ({v} : Set G)) ≤ 3 := by
    rw [← hfin]
    omega
  obtain ⟨E₀, hE₀, hE₀1⟩ := s15_Eleven_exists_transvection_member hsuppcard
    (fun E => E3.mQuot E (E ⊓ centralizer ({v} : Set G)))
    (fun E hE => s15_Support_one_le hY hspan hE) hsum
  obtain ⟨X₀, hX₀, rfl⟩ := mem_wConjG.1 (hsub hE₀)
  have hE₀1' : E3.mQuot (conjSubgroup X₀ g) (conjSubgroup X₀ g ⊓ centralizer ({v} : Set G)) = 1 :=
    hE₀1
  have hmv : suppMoved (wConjG D.M V₀ V hV L g) v = ∅ :=
    s15_Support_conj_eq_of_lt hY hind hspan hγΔ ht hperm hnlt
  have hE₀fix : conjSubgroup (conjSubgroup X₀ g) v = conjSubgroup X₀ g := by
    by_contra hne
    have hmem : conjSubgroup X₀ g ∈ suppMoved (wConjG D.M V₀ V hV L g) v := ⟨hE₀.1, hne⟩
    rw [hmv] at hmem
    exact hmem
  exact ⟨X, v, X₀, hX, hXg, hvX, hv1, ht, hvg, hVg, hX₀,
    conjSubgroup_eq_iff_mem_normalizer.mp hE₀fix, hE₀1'⟩

theorem s15_Eleven_s_two (D : Data G) (h1217 : R1217 D) (h159 : R15_9 D) (hT7 : RT7 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    (hs2 : s15 D.M V₀ V hV L = 2) (hγ : 4 ≤ gamma15 D.M V₀ V hV L) {i : ℕ} (hi : i ≤ 2)
    (h4 : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M → 4 ≤ E3.mQuot V U)
    {g : G} {A : Subgroup G} (hAg : A ≤ conjSubgroup V g) (hAM : A ≤ D.M)
    (hmA : E3.mQuot (conjSubgroup V g) A = i)
    (hAN : ¬ A ≤ normalizer (wSub V₀ V hV L : Set G)) : False := by
  obtain ⟨X, v, X₀, hX, hXg, hvX, hv1, -, -, hVg, hX₀, -, hE₀1'⟩ :=
    s15_Eleven_exists_normalized_transvection_of_wClos D h1217 h hV hL
      (h159 V₀ V L h hL) hV1 hs2 hγ hi h4 hAg hAM hmA hAN
  have hY := E3.isElemAbelian_conjSubgroup hV g
  have hγΔ : ∀ E ∈ wConjG D.M V₀ V hV L g, rk ↥E = gamma15 D.M V₀ V hV L :=
    fun E hE => s15_Glue3_wConjG_rk D h.hyp151 hV hV1 g hE
  have hXV : ∀ Z ∈ wConj D.M V₀ V hV L, Z ≤ V := by
    rintro Z ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hFV : conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) ≤ conjSubgroup V g := fun x hx =>
    E3.conjSubgroup_mono_left g (hXV X₀ hX₀) hx.1
  have hFab : IsElemAbelian 2 (conjSubgroup X₀ g ⊓ centralizer ({v} : Set G)) := hY.mono hFV
  have hcentM : centralizer ({v} : Set G) ≤ D.M := by
    have h1 := s15_Glue3_centralizer_le_conj D h hV hX 1
      (by rw [conjSubgroup_one]; exact hvX) hv1
    rwa [conjSubgroup_one] at h1
  have hFM : conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) ≤ D.M := fun x hx => hcentM hx.2
  have hfix : ∀ x ∈ conjSubgroup X₀ g ⊓ centralizer ({v} : Set G), x * v * x⁻¹ = v := by
    intro x hx
    have hcomm := Subgroup.mem_centralizer_iff.1 hx.2 v (Set.mem_singleton v)
    calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [hcomm]
      _ = v := by group
  have hFN : conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) ≤ normalizer (X : Set G) :=
    fun x hx => s15_Glue3_normalizes_of_fixes D h.hyp151 hV hL hV1 hX (hFM hx) hvX hv1 (hfix x hx)
  have hrkF : rk ↥(conjSubgroup X₀ g ⊓ centralizer ({v} : Set G)) + 1 = gamma15 D.M V₀ V hV L := by
    have hD := hγΔ (conjSubgroup X₀ g) ⟨X₀, hX₀, rfl⟩
    have h1 := E3.mQuot_add (V := conjSubgroup X₀ g) (U := ⊥)
      (U' := conjSubgroup X₀ g ⊓ centralizer ({v} : Set G)) bot_le inf_le_left
    rw [s15_FiveTen_mQuot_bot_eq_rk, s15_FiveTen_mQuot_bot_eq_rk] at h1
    omega
  have hF1 : conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, rk_bot] at hrkF
    omega
  have hfaith : ∀ x ∈ conjSubgroup X₀ g ⊓ centralizer ({v} : Set G),
      (∀ y ∈ X, x * y * x⁻¹ = y) → x = 1 := by
    intro x hx hcomm
    by_contra hx1
    have hle := s15_Glue3_centralizer_le_conj D h hV hX₀ g hx.1 hx1
    apply hXg
    intro y hy
    apply hle
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hxy := hcomm y hy
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [hxy]
  have hCc : ∀ x ∈ conjSubgroup X₀ g ⊓ centralizer ({v} : Set G), x ≠ 1 → ∀ y ∈ X,
      x * y * x⁻¹ = y → ∀ f ∈ conjSubgroup X₀ g ⊓ centralizer ({v} : Set G),
        f * y * f⁻¹ = y := by
    intro x hx hx1 y hy hxy f hf
    have hle := s15_Glue3_centralizer_le_conj D h hV hX₀ g hx.1 hx1
    have hyC : y ∈ centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [hxy]
    have hyMg : y ∈ conjSubgroup D.M g := hle hyC
    have hyx : y * x * y⁻¹ = x := by
      have e : x * y = y * x := by
        calc x * y = x * y * x⁻¹ * x := by group
          _ = y * x := by rw [hxy]
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [e]
        _ = x := by group
    have hyN := s15_Eleven_normalizes_conj D h.hyp151 hV hL hV1 hX₀ g hyMg hx.1 hx1 hyx
    have hc1 : y * f * y⁻¹ * f⁻¹ ∈ conjSubgroup X₀ g := by
      have h1 : y * f * y⁻¹ ∈ conjSubgroup X₀ g := (Subgroup.mem_normalizer_iff.1 hyN f).1 hf.1
      exact (conjSubgroup X₀ g).mul_mem h1 ((conjSubgroup X₀ g).inv_mem hf.1)
    have hc2' : y * f * y⁻¹ * f⁻¹ ∈ X := by
      have h1 : f * y⁻¹ * f⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 (hFN hf) y⁻¹).1 (X.inv_mem hy)
      have e : y * f * y⁻¹ * f⁻¹ = y * (f * y⁻¹ * f⁻¹) := by group
      rw [e]
      exact X.mul_mem hy h1
    have hbot := s15_Glue3_inf_V_eq_bot_conj D h hV hVg hX₀
    have hmem : y * f * y⁻¹ * f⁻¹ ∈ conjSubgroup X₀ g ⊓ V := ⟨hc1, hXV X hX hc2'⟩
    rw [hbot] at hmem
    have h1 : y * f * y⁻¹ * f⁻¹ = 1 := Subgroup.mem_bot.1 hmem
    have e : y * f = f * y := by
      calc y * f = (y * f * y⁻¹ * f⁻¹) * (f * y) := by group
        _ = f * y := by rw [h1, one_mul]
    calc f * y * f⁻¹ = y * f * f⁻¹ := by rw [e]
      _ = y := by group
  have hXel : IsElemAbelian 2 X := hV.mono (hXV X hX)
  have hax := s15_Eleven_axis_hyperplane hXel hFab hFN hCc hfaith
  have hrkX : rk ↥X = gamma15 D.M V₀ V hV L := s15_Glue3_rk_wConj D h.hyp151 hV hV1 hX
  have hKX : ¬ X ≤ centralizer ((conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) : Subgroup G) :
      Set G) := by
    intro hle
    apply hF1
    rw [eq_bot_iff]
    intro x hx
    refine Subgroup.mem_bot.2 (hfaith x hx fun y hy => ?_)
    have hxy := Subgroup.mem_centralizer_iff.1 (hle hy) x hx
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy]
      _ = y := by group
  have hmK : E3.mQuot X (X ⊓ centralizer ((conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) :
      Subgroup G) : Set G)) = 1 := by
    have h1 : E3.mQuot X (X ⊓ centralizer ((conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) :
        Subgroup G) : Set G)) ≠ 0 := by
      intro h0
      have hKeq := (E3.mQuot_eq_zero_iff hXel.isPGroup inf_le_left).1 h0
      apply hKX
      intro y hy
      have hyK : y ∈ X ⊓ centralizer ((conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) :
          Subgroup G) : Set G) := by
        rw [hKeq]
        exact hy
      exact hyK.2
    omega
  have hV1' : v1Sub D.M V₀ V h.hyp151.isElemAbelian L = ⊥ := hV1
  have h7 := hT7 V₀ V L h hL 1 X hX (conjSubgroup X₀ g ⊓ centralizer ({v} : Set G)) ⊥
    (X ⊓ centralizer ((conjSubgroup X₀ g ⊓ centralizer ({v} : Set G) : Subgroup G) : Set G))
    hFab (by rw [conjSubgroup_one]; exact hFM) bot_le
    (by simp only [hV1', sup_bot_eq, conjSubgroup_one]; exact hFN)
    (by
      intro x hx
      simp only [hV1', sup_bot_eq, conjSubgroup_one]
      constructor
      · intro hx1 d hd
        rw [Subgroup.mem_bot.1 hx1]
        simp
      · intro hcomm
        refine Subgroup.mem_bot.2 (hfaith x hx fun y hy => ?_)
        have h1 := Subgroup.mem_bot.1 (hcomm y hy)
        calc x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y := by group
          _ = y := by rw [h1, one_mul])
    (by simp only [hV1', conjSubgroup_one]; exact bot_le)
    (by simp only [hV1', sup_bot_eq, conjSubgroup_one]; exact inf_le_left)
    (by simp only [hV1', sup_bot_eq, conjSubgroup_one]; exact hmK)
    (by
      intro x hx k hk
      simp only [hV1', conjSubgroup_one]
      have hxk := Subgroup.mem_centralizer_iff.1 hk.2 x hx
      rw [Subgroup.mem_bot]
      calc x * k * x⁻¹ * k⁻¹ = k * x * x⁻¹ * k⁻¹ := by rw [hxk]
        _ = 1 := by group)
    (by
      rw [s15_FiveTen_mQuot_bot_eq_rk]
      omega)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
