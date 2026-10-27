module

public import CFSG.RankThree.PartTwo.Sec15.Wales154HJ
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.SCent
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4
import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofNormSolv
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.GroupTheory.PGroupFixedPointCongruence
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open Subgroup

section Model

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155 (exists_conj_case caseJ centralizer_caseJ_pow
  x5aJ x5cJ card_centralizer_x5a card_centralizer_x5c card_centralizer_le_of_orderOf_seven
  prime_dvd_card_GJ)
open CFSG.Monster.B.Co2 (Rep eqA_iff)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219 (centralizerConjEquiv)
open CFSG.AGLEmbeddingD2.Wilson.Proving (exists_third_prime_dvd_card_of_not_isSolvable)
open CFSG.RankThree.PartTwo.Sec16.Res162Seven (exists_commute_of_not_dvd)

private theorem card_modEq_card_inf_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {R : Subgroup G} {g : G} (hg : orderOf g = p)
    (hgR : g ∈ normalizer (R : Set G)) :
    Nat.card R ≡ Nat.card (R ⊓ centralizer ({g} : Set G) : Subgroup G) [MOD p] := by
  have hH : IsPGroup p (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hHR : zpowers g ≤ normalizer (R : Set G) := zpowers_le.2 hgR
  have hconj : ∀ h ∈ zpowers g, ∀ x ∈ R, h * x * h⁻¹ ∈ R :=
    fun h hh x hx => (mem_normalizer_iff.mp (hHR hh) x).mp hx
  let _ : MulAction (zpowers g) R :=
    { smul := fun h y => ⟨(h : G) * y * (h : G)⁻¹, hconj h h.2 y y.2⟩
      one_smul := fun y => Subtype.ext (by
        change (1 : G) * y * (1 : G)⁻¹ = y
        group)
      mul_smul := fun h k y => Subtype.ext (by
        change ((h : G) * k) * y * ((h : G) * k)⁻¹ =
          (h : G) * ((k : G) * y * (k : G)⁻¹) * (h : G)⁻¹
        group) }
  have e : Nat.card (MulAction.fixedPoints (zpowers g) R) =
      Nat.card (R ⊓ centralizer ({g} : Set G) : Subgroup G) := Nat.card_congr
    { toFun := fun y => ⟨(y.1 : G), y.1.2, mem_centralizer_singleton_iff.2 (by
        have h1 : g * (y.1 : G) * g⁻¹ = y.1 := congrArg Subtype.val (y.2 ⟨g, mem_zpowers g⟩)
        calc (y.1 : G) * g = (g * y.1 * g⁻¹) * g := by rw [h1]
          _ = g * y.1 := by group)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h => Subtype.ext (by
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h.2
        have hc : Commute (x : G) (g ^ n) :=
          (show Commute (x : G) g from mem_centralizer_singleton_iff.1 x.2.2).zpow_right n
        change (h : G) * x * (h : G)⁻¹ = x
        rw [← hn, ← hc.eq, mul_inv_cancel_right])⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e]
  exact hH.card_modEq_card_fixedPoints R

private theorem ne_of_eqA_eq_false {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1)
    (hu : Rep 315 u h.1) (he : CFSG.Monster.B.Co2.Native.eqA 315 t u = false) : g ≠ h :=
  fun hgh => by
    have := (eqA_iff ht hu).2 (congrArg Subtype.val hgh)
    rw [he] at this
    exact Bool.false_ne_true this

private theorem card_kleinSub_eq_four {G : Type*} [Group G] {a b : G} {ha : a * a = 1}
    {hb : b * b = 1} {hab : a * b = b * a} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (kleinSub ha hb hab) = 4 := by
  have hset : ((kleinSub ha hb hab : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext x
    exact mem_kleinSub
  have h1 : a * b ≠ 1 := fun h =>
    hne ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right ha)).symm
  have h2 : a * b ≠ a := fun h => hb1 (mul_eq_left.1 h)
  have h3 : a * b ≠ b := fun h => ha1 (mul_eq_right.1 h)
  have m1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
    rintro (h | h | h)
    exacts [ha1 h.symm, hb1 h.symm, h1 h.symm]
  have m2 : a ∉ ({b, a * b} : Set G) := by
    rintro (h | h)
    exacts [hne h, h2 h.symm]
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem m1,
    Set.ncard_insert_of_notMem m2, Set.ncard_pair h3.symm]

private theorem card_W
    (i : Fin 3) : Nat.card (WJ i) = 4 := by
  have hne : wJ i 0 ≠ wJ i 1 :=
    ne_of_eqA_eq_false (rep_w i 0) (rep_w i 1) (by simpa using (chkW_parts i).2.2.2.1)
  exact card_kleinSub_eq_four (w_ne_one i 0) (w_ne_one i 1) hne

private theorem card_V :
    Nat.card VJ = 4 := by
  obtain ⟨-, -, -, -, -, -, -, h7, h8, -⟩ := local45
  have hv2 : v2J ≠ 1 := ne_of_eqA_eq_false rep_v2 rep_one (by simpa using h7)
  have hne : v1J ≠ v2J := ne_of_eqA_eq_false rep_v1 rep_v2 (by simpa using h8)
  exact card_kleinSub_eq_four v1_ne_one hv2 hne

private theorem card_Vk
    (k : Fin 3) : Nat.card (VkJ k) = 4 := by
  rw [VkJ, Subgroup.card_map_of_injective (MulAut.conj (cJ k)).injective, card_V]

private theorem sq_of_mem_Vk
    {k : Fin 3} {x : GJ} (hx : x ∈ VkJ k) : x ^ 2 = 1 := by
  have h := mul_self_of_mem_kleinSub (mem_Vk.1 hx)
  calc x ^ 2 = cJ k * ((cJ k)⁻¹ * x * cJ k * ((cJ k)⁻¹ * x * cJ k)) * (cJ k)⁻¹ := by
        rw [sq]; group
    _ = 1 := by rw [h]; group

private theorem SJ_le_of
    {l : Fin 3} {X : Subgroup GJ}
    (h : ∀ idx < 4, ∃ j : Fin 3, ∃ i : ℕ, (gensS l.1)[idx]! = vkArr j.1 i ∧ VkJ j ≤ X) :
    SJ l ≤ X := by
  refine subOf_le_of _ (gensS_spec l) fun idx hidx => ?_
  obtain ⟨j, i, he, hj⟩ := h idx (by rwa [gensS_size] at hidx)
  have hg : gElt (gensS l.1) (gensS_spec l) idx hidx = vkE j i :=
    elA_eq_iff _ (by rw [he]; exact rep_vkE j i)
  rw [hg]
  exact hj (vkE_mem j i)

private theorem exists_SJ_le
    {X : Subgroup GJ} {j k : Fin 3} (hjk : j ≠ k) (hj : VkJ j ≤ X) (hk : VkJ k ≤ X) :
    ∃ l : Fin 3, SJ l ≤ X := by
  have s0 : VkJ 0 ≤ X → VkJ 1 ≤ X → SJ 0 ≤ X := fun h0 h1 => SJ_le_of fun idx hidx => by
    interval_cases idx
    · exact ⟨0, 1, gensS0.1, h0⟩
    · exact ⟨0, 2, gensS0.2.1, h0⟩
    · exact ⟨1, 1, gensS0.2.2.1, h1⟩
    · exact ⟨1, 2, gensS0.2.2.2, h1⟩
  have s1 : VkJ 0 ≤ X → VkJ 2 ≤ X → SJ 1 ≤ X := fun h0 h2 => SJ_le_of fun idx hidx => by
    interval_cases idx
    · exact ⟨0, 1, gensS1.1, h0⟩
    · exact ⟨0, 2, gensS1.2.1, h0⟩
    · exact ⟨2, 1, gensS1.2.2.1, h2⟩
    · exact ⟨2, 2, gensS1.2.2.2, h2⟩
  have s2 : VkJ 1 ≤ X → VkJ 2 ≤ X → SJ 2 ≤ X := fun h1 h2 => SJ_le_of fun idx hidx => by
    interval_cases idx
    · exact ⟨1, 1, gensS2.1, h1⟩
    · exact ⟨1, 2, gensS2.2.1, h1⟩
    · exact ⟨2, 1, gensS2.2.2.1, h2⟩
    · exact ⟨2, 2, gensS2.2.2.2, h2⟩
  fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hjk
    | exact ⟨0, s0 hj hk⟩
    | exact ⟨0, s0 hk hj⟩
    | exact ⟨1, s1 hj hk⟩
    | exact ⟨1, s1 hk hj⟩
    | exact ⟨2, s2 hj hk⟩
    | exact ⟨2, s2 hk hj⟩

private theorem inf_centralizer_E0_eq_bot
    {R : Subgroup GJ}
    (hR2 : IsPGroup 2 R) : R ⊓ centralizer (E0 : Set GJ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  have hxE : x ∈ E0 := by
    have := hx.2
    rwa [centralizer_E0] at this
  have h3 : x ^ 3 = 1 := cube_of_mem_P3 (E0_le_P3 hxE)
  obtain ⟨n, hn⟩ := hR2 ⟨x, hx.1⟩
  have h2 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right n (by norm_num))
    (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2))

private theorem card_modEq_one_three
    {R : Subgroup GJ}
    (hR2 : IsPGroup 2 R) (hRE : E0 ≤ normalizer (R : Set GJ)) : Nat.card R ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.GroupTheory.card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot
    (IsPGroup.of_card card_E0) hRE (inf_centralizer_E0_eq_bot hR2)

private theorem card_cases
    {R : Subgroup GJ} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hRE : E0 ≤ normalizer (R : Set GJ)) :
    Nat.card R = 4 ∨ Nat.card R = 16 ∨ Nat.card R = 64 := by
  obtain ⟨m, hm⟩ := le_S hR2 hRE
  have hdvd : Nat.card R ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← card_S m]
    exact Subgroup.card_dvd_of_le hm
  obtain ⟨n, hn, hRn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h3 := card_modEq_one_three hR2 hRE
  have h1 : Nat.card R ≠ 1 := fun h => hR1 (Subgroup.card_eq_one.mp h)
  rw [hRn] at h3 h1 ⊢
  interval_cases n
  · exact absurd rfl h1
  · exact absurd h3 (by decide)
  · exact Or.inl rfl
  · exact absurd h3 (by decide)
  · exact Or.inr (Or.inl rfl)
  · exact absurd h3 (by decide)
  · exact Or.inr (Or.inr rfl)

private theorem isSolvable_normalizer_of_card
    {R : Subgroup GJ}
    (hR2 : IsPGroup 2 R) (hRE : E0 ≤ normalizer (R : Set GJ)) (h64 : Nat.card R = 64) :
    Group.IsSolvable (normalizer (R : Set GJ)) := by
  obtain ⟨m, hm⟩ := le_S hR2 hRE
  have hRS : R = SJ m := Subgroup.eq_of_le_of_card_ge hm (by rw [card_S, h64])
  have hmax : R ∈ Set.range SJ := ⟨m, hRS.symm⟩
  rw [← maxInvariant_E0] at hmax
  exact Sec16.ks162J2NormSolv GJ ⟨CFSG.ComponentClassification.J2Cover.nativeEquivP.symm⟩ E0
    (by rw [card_E0]; norm_num) R hmax

private theorem card_centralizer_v1 :
    Nat.card (centralizer ({v1J} : Set GJ)) = 240 := by
  rw [centralizer_v1, card_subOf (by decide) enum45.2.2.2.2.1 gensCv_spec, enum45.2.2.2.2.2.1]

private theorem card_centralizer_of_mem_V
    {v : GJ} (hv : v ∈ VJ) (hv1 : v ≠ 1) :
    Nat.card (centralizer ({v} : Set GJ)) = 240 := by
  have e : ∀ g y : GJ, Nat.card (centralizer ({g * y * g⁻¹} : Set GJ)) =
      Nat.card (centralizer ({y} : Set GJ)) :=
    fun g y => Nat.card_congr (centralizerConjEquiv g y).toEquiv
  have h2 : Nat.card (centralizer ({v2J} : Set GJ)) = 240 := by
    rw [← hV_v1, e, card_centralizer_v1]
  rcases mem_kleinSub.1 hv with h | h | h | h
  · exact absurd h hv1
  · rw [h, card_centralizer_v1]
  · rw [h, h2]
  · rw [h, ← hV_v2, e, h2]

private theorem card_centralizer_of_mem_Vk
    {k : Fin 3} {v : GJ} (hv : v ∈ VkJ k) (hv1 : v ≠ 1) :
    Nat.card (centralizer ({v} : Set GJ)) = 240 := by
  have hu1 : (cJ k)⁻¹ * v * cJ k ≠ 1 := fun h => hv1 (by
    calc v = cJ k * ((cJ k)⁻¹ * v * cJ k) * (cJ k)⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have e : v = cJ k * ((cJ k)⁻¹ * v * cJ k) * (cJ k)⁻¹ := by group
  rw [e, Nat.card_congr (centralizerConjEquiv _ _).toEquiv]
  exact card_centralizer_of_mem_V (mem_Vk.1 hv) hu1

private theorem sixtyfour_dvd_card_centralizer
    {R : Subgroup GJ} (hR2 : IsPGroup 2 R)
    (hRE : E0 ≤ normalizer (R : Set GJ)) {w : GJ} (hw : w ∈ R ⊓ centralizer ({zJ} : Set GJ)) :
    64 ∣ Nat.card (centralizer ({w} : Set GJ)) := by
  obtain ⟨m, hm⟩ := le_S hR2 hRE
  have hwc : w ∈ centralizer ((SJ m : Subgroup GJ) : Set GJ) :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.inf_centralizer_z_le_centralizer
      (isPGroup_S m) (E0_le_normalizer_S m) ⟨hm hw.1, hw.2⟩
  have hle : SJ m ≤ centralizer ({w} : Set GJ) := fun s hs =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hwc s hs)
  rw [← card_S m]
  exact Subgroup.card_dvd_of_le hle

private theorem not_sixteen_dvd_of_orderOf_five
    {g : GJ} (hg : orderOf g = 5) :
    ¬ 16 ∣ Nat.card (centralizer ({g} : Set GJ)) := by
  obtain ⟨k, c, hc, e, he0, he5, rfl⟩ := exists_conj_case hg
  rw [Nat.card_congr (centralizerConjEquiv k (caseJ c ^ e)).toEquiv,
    centralizer_caseJ_pow hc he0 he5]
  interval_cases c
  · rw [show caseJ 0 = x5aJ by simp [caseJ], card_centralizer_x5a]
    norm_num
  · rw [show caseJ 1 = x5cJ by simp [caseJ], card_centralizer_x5c]
    norm_num

private theorem exists_mem_orderOf_five_or_seven
    {K : Subgroup GJ} (hK1 : K ≠ ⊥)
    (hKp : Group.IsPerfect K) : ∃ g ∈ K, orderOf g = 5 ∨ orderOf g = 7 := by
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hK1
  obtain ⟨r, hr, hrK, hr2, hr3⟩ := exists_third_prime_dvd_card_of_not_isSolvable
    (Group.IsPerfect.not_isSolvable K) Nat.prime_two Nat.prime_three
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrK
  refine ⟨g, g.2, ?_⟩
  rw [Subgroup.orderOf_coe, hg]
  rcases prime_dvd_card_GJ hr (hrK.trans (Subgroup.card_subgroup_dvd_card K)) with
    rfl | rfl | rfl | rfl
  · exact absurd rfl hr2
  · exact absurd rfl hr3
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem exists_pieces
    {R : Subgroup GJ} (hR2 : IsPGroup 2 R)
    (hRE : E0 ≤ normalizer (R : Set GJ)) (h16 : Nat.card R = 16) :
    (∃ w ∈ R ⊓ centralizer ({zJ} : Set GJ), w ≠ 1) ∧
      ∃ k : Fin 3, ∃ v ∈ VkJ k, v ∈ R ∧ v ≠ 1 := by
  have hgen := le_sup_pieces hR2 hRE
  have hsmall : ∀ X : Subgroup GJ, Nat.card X = 4 → ¬ R ≤ X := fun X hX hRX => by
    have := Subgroup.card_le_of_le hRX
    omega
  have hpair : ∀ j k : Fin 3, j ≠ k → R ⊓ centralizer ({aJ j} : Set GJ) ≠ ⊥ →
      R ⊓ centralizer ({aJ k} : Set GJ) ≠ ⊥ → False := by
    intro j k hjk hj hk
    obtain ⟨l, hl⟩ :=
      exists_SJ_le hjk (Vk_le_of_ne_bot hR2 hRE j hj) (Vk_le_of_ne_bot hR2 hRE k hk)
    have := Subgroup.card_le_of_le hl
    rw [card_S, h16] at this
    omega
  obtain ⟨k, hk⟩ : ∃ k : Fin 3,
      R ≤ R ⊓ centralizer ({zJ} : Set GJ) ⊔ R ⊓ centralizer ({aJ k} : Set GJ) := by
    by_cases h0 : R ⊓ centralizer ({aJ 0} : Set GJ) = ⊥
    · by_cases h1 : R ⊓ centralizer ({aJ 1} : Set GJ) = ⊥
      · simp only [h0, h1, sup_bot_eq] at hgen
        exact ⟨2, hgen⟩
      · have h2 : R ⊓ centralizer ({aJ 2} : Set GJ) = ⊥ := by
          by_contra h2
          exact hpair 1 2 (by decide) h1 h2
        simp only [h0, h2, sup_bot_eq] at hgen
        exact ⟨1, hgen⟩
    · have h1 : R ⊓ centralizer ({aJ 1} : Set GJ) = ⊥ := by
        by_contra h1
        exact hpair 0 1 (by decide) h0 h1
      have h2 : R ⊓ centralizer ({aJ 2} : Set GJ) = ⊥ := by
        by_contra h2
        exact hpair 0 2 (by decide) h0 h2
      simp only [h1, h2, sup_bot_eq] at hgen
      exact ⟨0, hgen⟩
  have hZ : R ⊓ centralizer ({zJ} : Set GJ) ≠ ⊥ := by
    intro hZ
    rw [hZ, bot_sup_eq] at hk
    exact hsmall _ (card_Vk k) (hk.trans (piece_a hR2 k))
  have hA : R ⊓ centralizer ({aJ k} : Set GJ) ≠ ⊥ := by
    intro hA
    rw [hA, sup_bot_eq] at hk
    rcases piece_z hR2 hRE with hz | ⟨i, hz⟩
    · exact hZ hz
    · rw [hz] at hk
      exact hsmall _ (card_W i) hk
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
  exact ⟨⟨w, hw, fun h => hw1 (Subtype.ext h)⟩,
    k, v, piece_a hR2 k hv, hv.1, fun h => hv1 (Subtype.ext h)⟩

private theorem sq_eq_one_of_card_four
    {R : Subgroup GJ}
    (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRE : E0 ≤ normalizer (R : Set GJ))
    (h4 : Nat.card R = 4) : ∀ r ∈ R, r ^ 2 = 1 := by
  have key : ∀ X : Subgroup GJ, X ≤ R → Nat.card X = 4 → (∀ x ∈ X, x ^ 2 = 1) →
      ∀ r ∈ R, r ^ 2 = 1 := by
    intro X hXR hX4 hX r hr
    have hXeq : X = R := Subgroup.eq_of_le_of_card_ge hXR (by rw [hX4, h4])
    exact hX r (by rw [hXeq]; exact hr)
  by_contra hcon
  have hz : R ⊓ centralizer ({zJ} : Set GJ) = ⊥ := by
    rcases piece_z hR2 hRE with hz | ⟨i, hz⟩
    · exact hz
    · refine (hcon (key (WJ i) (by rw [← hz]; exact inf_le_left) (card_W i) fun x hx => ?_)).elim
      rw [sq]
      exact mul_self_of_mem_kleinSub hx
  have ha : ∀ k : Fin 3, R ⊓ centralizer ({aJ k} : Set GJ) = ⊥ := fun k => by
    by_contra h
    exact hcon (key _ (Vk_le_of_ne_bot hR2 hRE k h) (card_Vk k) fun x hx => sq_of_mem_Vk hx)
  have hgen := le_sup_pieces hR2 hRE
  simp only [hz, ha, sup_bot_eq] at hgen
  exact hR1 (le_bot_iff.1 hgen)

private theorem false_of_card_sixteen
    {R K : Subgroup GJ}
    (hR2 : IsPGroup 2 R) (hRE : E0 ≤ normalizer (R : Set GJ)) (hK1 : K ≠ ⊥)
    (hKp : Group.IsPerfect K) (hKR : K ≤ normalizer (R : Set GJ)) (h16 : Nat.card R = 16) :
    False := by
  obtain ⟨g, hgK, hg⟩ := exists_mem_orderOf_five_or_seven hK1 hKp
  have hgR : g ∈ normalizer (R : Set GJ) := hKR hgK
  have hFdvd : Nat.card (R ⊓ centralizer ({g} : Set GJ) : Subgroup GJ) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← h16]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨n, hn, hFn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hFdvd
  rcases hg with hg5 | hg7
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hmod := card_modEq_card_inf_centralizer hg5 hgR
    rw [h16, hFn] at hmod
    have hn04 : n = 0 ∨ n = 4 := by
      interval_cases n
      · exact Or.inl rfl
      · exact absurd hmod (by decide)
      · exact absurd hmod (by decide)
      · exact absurd hmod (by decide)
      · exact Or.inr rfl
    rcases hn04 with rfl | rfl
    ·
      have hF1 : R ⊓ centralizer ({g} : Set GJ) = ⊥ :=
        Subgroup.card_eq_one.mp (by rw [hFn, pow_zero])
      obtain ⟨⟨w, hwZ, hw1⟩, k, v, hvV, hvR, hv1⟩ := exists_pieces hR2 hRE h16
      have hw64 := sixtyfour_dvd_card_centralizer hR2 hRE hwZ
      have hv240 := card_centralizer_of_mem_Vk hvV hv1
      set S : Set GJ := {t | t ∈ R ∧ Nat.card (centralizer ({t} : Set GJ)) = 240}
      have hC1 : centralizer ({(1 : GJ)} : Set GJ) = ⊤ := by
        ext x
        simp [mem_centralizer_singleton_iff]
      have h1S : ∀ t ∈ S, t ≠ 1 := by
        rintro t ⟨-, htC⟩ rfl
        rw [hC1, Subgroup.card_top, card_GJ] at htC
        norm_num at htC
      have hQ : ∀ y x : GJ, Nat.card (centralizer ({x} : Set GJ)) = 240 →
          Nat.card (centralizer ({y * x * y⁻¹} : Set GJ)) = 240 := fun y x hx =>
        (Nat.card_congr (centralizerConjEquiv y x).toEquiv).trans hx
      have h3 : 3 ∣ Nat.card S := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        by_contra h3
        obtain ⟨t, htR, htC, htz⟩ := exists_commute_of_not_dvd
          (orderOf_eq_prime z_cube zJ_ne_one) (hRE zJ_mem_E0)
          (fun t => Nat.card (centralizer ({t} : Set GJ)) = 240) hQ h3
        have h64 := sixtyfour_dvd_card_centralizer hR2 hRE
          ⟨htR, mem_centralizer_singleton_iff.2 htz.symm⟩
        have htC' : Nat.card (centralizer ({t} : Set GJ)) = 240 := htC
        rw [htC'] at h64
        norm_num at h64
      have h5 : 5 ∣ Nat.card S := by
        by_contra h5
        obtain ⟨t, htR, htC, htg⟩ := exists_commute_of_not_dvd hg5 hgR
          (fun t => Nat.card (centralizer ({t} : Set GJ)) = 240) hQ h5
        have htF : t ∈ R ⊓ centralizer ({g} : Set GJ) :=
          ⟨htR, mem_centralizer_singleton_iff.2 htg.symm⟩
        rw [hF1, mem_bot] at htF
        exact h1S t ⟨htR, htC⟩ htF
      have hpos : 0 < Nat.card S := by
        rw [Nat.card_coe_set_eq, Set.ncard_pos]
        exact ⟨v, hvR, hv240⟩
      have hlt : Nat.card S < 15 := by
        have hsub0 : S ⊆ (R : Set GJ) \ {1} := fun t ht => ⟨ht.1, h1S t ht⟩
        have hsub : S ⊂ (R : Set GJ) \ {1} := by
          rw [Set.ssubset_iff_of_subset hsub0]
          refine ⟨w, ⟨hwZ.1, hw1⟩, fun hw => ?_⟩
          rw [hw.2] at hw64
          norm_num at hw64
        have hR16 : (R : Set GJ).ncard = 16 := by
          rw [← Nat.card_coe_set_eq]
          exact h16
        have := Set.ncard_lt_ncard hsub
        rw [Set.ncard_sdiff_singleton_of_mem (show (1 : GJ) ∈ (R : Set GJ) from one_mem R),
          hR16] at this
        rw [Nat.card_coe_set_eq]
        omega
      omega
    ·
      have hFR : R ⊓ centralizer ({g} : Set GJ) = R :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hFn, h16]; norm_num)
      have hRC : R ≤ centralizer ({g} : Set GJ) := by
        rw [← hFR]
        exact inf_le_right
      apply not_sixteen_dvd_of_orderOf_five hg5
      rw [← h16]
      exact Subgroup.card_dvd_of_le hRC
  ·
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hmod := card_modEq_card_inf_centralizer hg7 hgR
    rw [h16, hFn] at hmod
    have h2F : 2 ∣ Nat.card (R ⊓ centralizer ({g} : Set GJ) : Subgroup GJ) := by
      rw [hFn]
      interval_cases n
      · exact absurd hmod (by decide)
      · exact dvd_refl 2
      · exact absurd hmod (by decide)
      · exact absurd hmod (by decide)
      · exact ⟨8, by norm_num⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2F
    have hto : orderOf (t : GJ) = 2 := by rw [Subgroup.orderOf_coe, ht]
    have htC : (t : GJ) ∈ centralizer ({g} : Set GJ) := t.2.2
    have h14 : 2 * 7 ∣ Nat.card (centralizer ({g} : Set GJ)) := by
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ ?_
      · rw [← hto]
        exact Subgroup.orderOf_dvd_natCard _ htC
      · rw [← hg7]
        exact Subgroup.orderOf_dvd_natCard _ (mem_centralizer_singleton_iff.2 rfl)
    have hle := card_centralizer_le_of_orderOf_seven hg7
    have hpos : 0 < Nat.card (centralizer ({g} : Set GJ)) := Nat.card_pos
    have := Nat.le_of_dvd hpos h14
    omega

private theorem four_of_GJ
    {R K : Subgroup GJ} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hRE : E0 ≤ normalizer (R : Set GJ)) (hK1 : K ≠ ⊥) (hKp : Group.IsPerfect K)
    (hKR : K ≤ normalizer (R : Set GJ)) : Nat.card R = 4 ∧ ∀ r ∈ R, r ^ 2 = 1 := by
  rcases card_cases hR2 hR1 hRE with h4 | h16 | h64
  · exact ⟨h4, sq_eq_one_of_card_four hR2 hR1 hRE h4⟩
  · exact (false_of_card_sixteen hR2 hRE hK1 hKp hKR h16).elim
  · exfalso
    have := isSolvable_normalizer_of_card hR2 hRE h64
    have hsol : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKR)
    have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hK1
    exact Group.IsPerfect.not_isSolvable K hsol

private theorem exists_mulEquiv_E0
    {Γ : Type} [Group Γ]
    (hΓ : Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup Γ}
    (hE9 : Nat.card E = 9) : ∃ ε : Γ ≃* GJ, E.map ε.toMonoidHom = E0 := by
  obtain ⟨e⟩ := hΓ
  let ε₀ : Γ ≃* GJ := e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hcard : Nat.card (E.map ε₀.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ε₀.injective, hE9]
  have hE0 : Nat.card E0 = 9 := by rw [card_E0]; norm_num
  obtain ⟨g, hg⟩ := KFacts.KS14.Native.j2_exists_conjugate_of_card_nine
    ⟨CFSG.ComponentClassification.J2Cover.nativeEquivP.symm⟩ hcard hE0
  refine ⟨ε₀.trans (MulAut.conj g⁻¹), ?_⟩
  have e1 : (ε₀.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp ε₀.toMonoidHom := rfl
  rw [e1, ← Subgroup.map_map]
  exact hg.symm

end Model

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
theorem ks154J2Four :
    KS154J2Four := by
  intro Γ _ hΓ E K R hE3 hE9 hK1 hKp hEK hR1 hR2 hER hKR
  have : Finite Γ := Nat.finite_of_card_ne_zero (by
    rw [KFacts.KS14.card_eq_of_j2 hΓ]
    norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : 3 ^ 2 ∣ Nat.card E := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
    rw [hk]
    refine pow_dvd_pow 3 ?_
    by_contra hk2
    push Not at hk2
    have : Nat.card E ≤ 3 := by
      rw [hk]
      interval_cases k <;> norm_num
    omega
  obtain ⟨E₉', hE₉'⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set E₉ := E₉'.map E.subtype with hE₉def
  have hE₉9 : Nat.card E₉ = 9 := by
    rw [hE₉def, Subgroup.card_map_of_injective E.subtype_injective, hE₉']
    norm_num
  have hE₉E : E₉ ≤ E := Subgroup.map_subtype_le _
  obtain ⟨ε, hε⟩ := exists_mulEquiv_E0 hΓ hE₉9
  have hN : (normalizer (R : Set Γ)).map ε.toMonoidHom =
      normalizer ((R.map ε.toMonoidHom : Subgroup GJ) : Set GJ) :=
    Subgroup.map_equiv_normalizer_eq R ε
  have hR'2 : IsPGroup 2 (R.map ε.toMonoidHom) := hR2.map _
  have hR'1 : R.map ε.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ ε.injective]
    exact hR1
  have hR'E : E0 ≤ normalizer ((R.map ε.toMonoidHom : Subgroup GJ) : Set GJ) := by
    rw [← hε, ← hN]
    exact Subgroup.map_mono (hE₉E.trans hER)
  have hK'1 : K.map ε.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ ε.injective]
    exact hK1
  have hK'p : Group.IsPerfect (K.map ε.toMonoidHom) := Group.IsPerfect.map ε.toMonoidHom
  have hK'R : K.map ε.toMonoidHom ≤ normalizer ((R.map ε.toMonoidHom : Subgroup GJ) : Set GJ) := by
    rw [← hN]
    exact Subgroup.map_mono hKR
  obtain ⟨h4, hsq⟩ := four_of_GJ hR'2 hR'1 hR'E hK'1 hK'p hK'R
  refine ⟨by rw [← h4, Subgroup.card_map_of_injective ε.injective], fun r hr => ?_⟩
  have h1 := hsq (ε r) ⟨r, hr, rfl⟩
  apply ε.injective
  rw [map_pow, h1, map_one]

end CFSG.RankThree.PartTwo.Sec15.Wales154
