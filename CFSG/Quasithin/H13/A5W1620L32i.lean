module

public import CFSG.Quasithin.H13.A5W1620L32e
public import CFSG.Quasithin.H13.A5W1620L32f
public import CFSG.Quasithin.H13.A5W1620L32h
public import CFSG.Quasithin.Background.C41PfCorr

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem Lv_le_of_red (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {F : Type} [Field F] [Finite F] (hF2 : Nat.card F = 2)
    (e : ↥(S.plus K) ≃* ↥(StatedSL 3 F))
    {K₀ : Subgroup G} (hK₀K : K₀ ≤ K) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G)) (hK₀W : autOn K₀ (S.WK K) = S.plus K)
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hchar : CharTwo (K₀ ⊔ S.Tv))
    (hWP : S.WK K ≤ pCoreOf 2 (K₀ ⊔ S.Tv))
    (hred : IsTwoReducedIn (K₀ ⊔ S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)))
    (hLvK₀ : S.Lv ≤ Subgroup.normalizer (K₀ : Set G))
    (h1317 : ∀ g : G, (∀ t ∈ S.Tv,
        (g * S.z * g⁻¹) * t * (g * S.z * g⁻¹)⁻¹ * t⁻¹ ∈ Subgroup.zpowers S.v12) →
      ¬ K₀ ≤ Subgroup.centralizer ({g * S.z * g⁻¹} : Set G))
    {F' : Type} [Field F'] [Fintype F'] {α : ↥K₀ →* ↥(StatedSL 3 F')}
    (hF'2 : Fintype.card F' = 2) (hα : IsModO2Surj K₀ α)
    {i : ℕ} (hi : C134CorrLocal.IsC134CaseCorr i (K₀ ⊔ S.Tv) S.Tv K₀) : S.Lv ≤ K₀ := by
  classical
  by_cases hne : ∃ l ∈ S.Lv, ∃ k ∈ K₀, ∃ w ∈ S.WK K,
      k * (l * w * l⁻¹) * k⁻¹ ≠ l * (k * w * k⁻¹) * l⁻¹
  · exact S.Lv_le_of_not_commute_red h1222 h517 hF hK hT hK₀K hTK₀ hK₀W hLvK₀ hF2 e hne
  exfalso
  push Not at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF'2' : Nat.card F' = 2 := by rw [Nat.card_eq_fintype_card, hF'2]
  have hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₀K.trans hK.1
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  set W := S.WK K with hWdef
  have hWcomm : IsMulCommutative ↥W := hR.2.2.1.1
  have hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w := fun w hw w' hw' =>
    congrArg Subtype.val (mul_comm (⟨w, hw⟩ : ↥W) ⟨w', hw'⟩)
  have hKW : K₀ ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    hK₀K.trans ((le_sup_left.trans le_sup_left).trans hR.2.1)
  have hLvW : S.Lv ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans hR.2.1
  obtain ⟨y₀, hyLv, hyodd, hyρ⟩ := S.exists_Lv_c234_odd
  set y : G := (y₀ : G) with hy
  have hy3 : y ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (S.orderOf_dvd_three_of_Lv hyLv hyodd)
  have hyW : y ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) := hLvW hyLv
  have hyK₀ : y ∈ Subgroup.normalizer (K₀ : Set G) := hLvK₀ hyLv
  have hcommW : ∀ k ∈ K₀, ∀ w ∈ W, k * (y * w * y⁻¹) * k⁻¹ = y * (k * w * k⁻¹) * y⁻¹ :=
    fun k hk w hw => hne y hyLv k hk w hw
  suffices hfix : ∀ k ∈ K₀, y * (k * S.z * k⁻¹ * S.z⁻¹) * y⁻¹ = k * S.z * k⁻¹ * S.z⁻¹ from
    S.false_of_commute_of_fix_red h1222 h517 hF hK hT hK₀K hz y₀ hyρ hyW hcommW hfix
  have hzW : S.z ∈ W := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hkz : ∀ {W' : Subgroup G}, S.z ∈ W' → ∀ k ∈ K₀, k * S.z * k⁻¹ * S.z⁻¹ ∈ ⁅W', K₀⁆ := by
    intro W' hzW' k hk
    have h1 := Subgroup.commutator_mem_commutator hk hzW'
    rw [Subgroup.commutator_comm] at h1
    exact h1
  have hne1 : ∀ {W' : Subgroup G}, S.z ∈ W' → ⁅W', K₀⁆ ≠ ⊥ := by
    intro W' hzW' h
    apply hz
    intro k hk
    have h1 := hkz hzW' k hk
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * S.z = (k * S.z * k⁻¹ * S.z⁻¹) * S.z * k := by group
      _ = S.z * k := by rw [h1, one_mul]
  have hUne : ¬ ⁅W, K₀⁆ ≤ ⊥ := fun h => hne1 hzW (le_bot_iff.mp h)
  have hUW : ⁅W, K₀⁆ ≤ W := L32.commutator_le_left_of_le_normalizer hKW
  have hyU : ∀ u ∈ ⁅W, K₀⁆, y * u * y⁻¹ ∈ ⁅W, K₀⁆ := fun u hu =>
    SteinbergCC.conj_mem_commutator (fun w hw => (Subgroup.mem_normalizer_iff.mp hyW w).mp hw)
      (fun k hk => (Subgroup.mem_normalizer_iff.mp hyK₀ k).mp hk) hu
  have hcommU : ∀ k ∈ K₀, ∀ u ∈ ⁅W, K₀⁆, k * (y * u * y⁻¹) * k⁻¹ = y * (k * u * k⁻¹) * y⁻¹ :=
    fun k hk u hu => hcommW k hk u (hUW hu)
  have hUnc : ¬ ⁅W, K₀⁆ ≤ Subgroup.centralizer (K₀ : Set G) := by
    intro h
    apply hUne
    have h1 := L32.commutator_le_commutator_commutator hKW hWc hK₀p
    have h2 : ⁅⁅W, K₀⁆, K₀⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro u hu k hk
      have hc := Subgroup.mem_centralizer_iff.mp (h hu) k hk
      rw [Subgroup.mem_bot, commutatorElement_def]
      calc u * k * u⁻¹ * k⁻¹ = (k * u) * u⁻¹ * k⁻¹ := by rw [hc]
        _ = 1 := by group
    rw [h2] at h1
    exact h1
  set H := K₀ ⊔ S.Tv with hHdef
  have hK₀H : K₀ ≤ H := le_sup_left
  have hHK₀ : H ≤ Subgroup.normalizer (K₀ : Set G) := sup_le Subgroup.le_normalizer hTK₀
  have hHP : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQP : c134Q H K₀ ≤ pCoreOf 2 H :=
    L32.commutator_le_left_of_le_normalizer (hK₀H.trans hHP)
  have hUQ : ⁅W, K₀⁆ ≤ c134Q H K₀ := Subgroup.commutator_mono hWP le_rfl
  have hyQ : ∀ q ∈ c134Q H K₀, y * q * y⁻¹ ∈ c134Q H K₀ :=
    L32.conj_mem_commutator_pCoreOf hK₀H hHK₀ hK₀p hyK₀
  have hyQ' : ∀ q ∈ c134Q H K₀, y⁻¹ * q * y⁻¹⁻¹ ∈ c134Q H K₀ :=
    L32.conj_mem_commutator_pCoreOf hK₀H hHK₀ hK₀p (Subgroup.inv_mem _ hyK₀)
  have hyZQ : ∀ u ∈ centerOf (c134Q H K₀), y * u * y⁻¹ ∈ centerOf (c134Q H K₀) := by
    intro u hu
    refine ⟨hyQ u hu.1, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hu.2 _ (hyQ' q hq)
    calc q * (y * u * y⁻¹) = y * ((y⁻¹ * q * y⁻¹⁻¹) * u) * y⁻¹ := by group
      _ = y * (u * (y⁻¹ * q * y⁻¹⁻¹)) * y⁻¹ := by rw [h1]
      _ = y * u * y⁻¹ * q := by group
  set V' := conjClosure S.V1 H with hV'def
  have hzV' : S.z ∈ V' := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hV'W : V' ≤ W := by
    rw [hWdef, S.WK_eq hT]
    exact conjClosure_mono le_rfl (sup_le (hK₀K.trans (le_sup_left.trans le_sup_left))
      (S.Tv_le_HK K))
  have hKV' : K₀ ≤ Subgroup.normalizer ((V' : Subgroup G) : Set G) := hK₀H.trans hred.2.1
  have hV'c : ∀ w ∈ V', ∀ w' ∈ V', w * w' = w' * w := fun w hw w' hw' =>
    hWc w (hV'W hw) w' (hV'W hw')
  have hPV' : pCoreOf 2 H ≤ Subgroup.centralizer (V' : Set G) :=
    hred.2.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hHP fun d hd => by
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨d, hd⟩
      refine ⟨k, ?_⟩
      have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [hk']
      exact Subgroup.one_mem _
  have hU'V' : ⁅V', K₀⁆ ≤ V' := L32.commutator_le_left_of_le_normalizer hKV'
  have hU'Z : ⁅V', K₀⁆ ≤ centerOf (c134Q H K₀) := by
    intro u hu
    refine ⟨Subgroup.commutator_mono (hV'W.trans hWP) le_rfl hu,
      Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hPV' (hQP hq)) u (hU'V' hu)).symm
  have hcommU' : ∀ k ∈ K₀, ∀ u ∈ ⁅V', K₀⁆,
      k * (y * u * y⁻¹) * k⁻¹ = y * (k * u * k⁻¹) * y⁻¹ :=
    fun k hk u hu => hcommW k hk u (hV'W (hU'V' hu))
  have hK₀U' : ∀ k ∈ K₀, ∀ u ∈ ⁅V', K₀⁆, k * u * k⁻¹ ∈ ⁅V', K₀⁆ := fun k hk =>
    L32.conj_mem_commutator_left hKV' hk
  have hU'ne : ¬ ⁅V', K₀⁆ ≤ ⊥ := fun h => hne1 hzV' (le_bot_iff.mp h)
  match i, hi with
  | 1, hi =>
    obtain ⟨-, n, F₁, _, _, hcard, -, α₁, hα₁s, hα₁k, β₁, -, hβ₁k, hβ₁e⟩ := hi
    have hF₁ : Nat.card F₁ = 2 := L32.natCard_eq_two_of_isModO2Surj hF'2'
      (by rw [Nat.card_eq_fintype_card, hcard]) ⟨hα₁s, hα₁k⟩ hα
    have hfixU := L32.conj_eq_of_natural hF₁ hα₁s hβ₁k hβ₁e hKW hWc hK₀p hUQ hUne bot_le hyU
      hcommU
    exact fun k hk => hfixU _ (hkz hzW k hk)
  | 2, hi =>
    obtain ⟨⟨n, F₂, _, _, α₂, hcard, hα₂, hKQ, -, β₂, -, hβ₂k, hβ₂e⟩, -⟩ := hi
    have hF₂ : Nat.card F₂ = 2 := L32.natCard_eq_two_of_isModO2Surj hF'2'
      (by rw [Nat.card_eq_fintype_card, hcard]) hα₂ hα
    have hβ₂k' : β₂.ker = ⊥ := by rw [hβ₂k, Subgroup.bot_subgroupOf]
    rcases L32.conj_eq_or_fixedPointFree_of_sum_two hF₂ hα₂.1 hKQ hβ₂k' hβ₂e hUQ
        (fun k hk => L32.conj_mem_commutator_left hKW hk) hy3 hyU hcommU with hfixU | ⟨-, hfp⟩
    · exact fun k hk => hfixU _ (hkz hzW k hk)
    · exfalso
      have haP : S.a ∈ pCoreOf 2 H :=
        S.a_mem_pCoreOf h1222 h517 le_sup_right (sup_le hK₀G S.Tv_le_Gv) hchar
      have hcommA : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ c134Q H K₀ := by
        intro k hk
        have h1 := Subgroup.commutator_mem_commutator haP (K₀.inv_mem hk)
        have e1 : k⁻¹ * S.a * k * S.a⁻¹ = ⁅S.a, k⁻¹⁆⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e1]
        exact Subgroup.inv_mem _ h1
      have hyNQ : y ∈ Subgroup.normalizer ((c134Q H K₀ : Subgroup G) : Set G) :=
        B6.mem_normalizer_of_forall_mem hyQ fun q hq => by
          have := hyQ' q hq
          rwa [inv_inv] at this
      refine S.false_of_comm_mem_of_fixed' h1222 h517 hK₀G hK₀ hTK₀ h1317
        (A := c134Q H K₀) (L32.sq_eq_one_of_sum_two hF₂ hβ₂k') (L32.mul_comm_of_sum_two hβ₂k')
        hKQ hcommA (Y := Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyK₀)
        (Subgroup.zpowers_le.mpr hyNQ) (fun y' hy' => S.Lv_comm_a
          ((Subgroup.zpowers_le.mpr hyLv) hy')) ?_
      intro m hm hm' k hk
      have h1 := hm' y (Subgroup.mem_zpowers y)
      have hmQ : y * m * y⁻¹ * m⁻¹ ∈ c134Q H K₀ := Subgroup.mul_mem _ (hyQ m hm)
        (Subgroup.inv_mem _ hm)
      have h2 := L32.eq_one_of_forall_conj_eq_sum_two hF₂ hα₂.1 hβ₂k' hβ₂e hmQ h1
      have h3 : y * m * y⁻¹ = m := by
        calc y * m * y⁻¹ = (y * m * y⁻¹ * m⁻¹) * m := by group
          _ = m := by rw [h2, one_mul]
      rw [hfp m hm h3]
      group
  | 3, hi =>
    obtain ⟨⟨n, F₃, _, _, α₃, hcard, hα₃, hZnat, -⟩, -⟩ := hi
    have hF₃ : Nat.card F₃ = 2 := L32.natCard_eq_two_of_isModO2Surj hF'2'
      (by rw [Nat.card_eq_fintype_card, hcard]) hα₃ hα
    obtain ⟨-, -, β₃, -, hβ₃k, hβ₃e⟩ := L32.natural_of_sum_one hZnat
    have hβ₃k' : β₃.ker = ⊥ := by rw [hβ₃k, Subgroup.bot_subgroupOf]
    have hZU : centerOf (c134Q H K₀) ≤ ⁅V', K₀⁆ :=
      L32.le_of_ne_bot hF₃ hα₃.1 hβ₃k' hβ₃e hU'Z hK₀U' fun h => hU'ne (le_bot_iff.mpr h)
    have hfixU' := L32.conj_eq_of_natural hF₃ hα₃.1 hβ₃k hβ₃e hKV' hV'c hK₀p hU'Z hU'ne bot_le
      (fun u hu => hZU (hyZQ u (hU'Z hu))) hcommU'
    exact fun k hk => hfixU' _ (hkz hzV' k hk)
  | 4, hi =>
    obtain ⟨⟨n, F₄, _, _, α₄, hcard, hα₄, -, -, -, hN4, -, -, -⟩, -⟩ := hi
    have hF₄ : Nat.card F₄ = 2 := L32.natCard_eq_two_of_isModO2Surj hF'2'
      (by rw [Nat.card_eq_fintype_card, hcard]) hα₄ hα
    obtain ⟨-, -, β₄, -, hβ₄k, hβ₄e⟩ := L32.natural_of_sum_one hN4
    have hβ₄k' : β₄.ker = ⊥ := by rw [hβ₄k, Subgroup.bot_subgroupOf]
    have hU'X : ⁅V', K₀⁆ ≤ ⁅centerOf (c134Q H K₀), K₀⁆ :=
      (L32.commutator_le_commutator_commutator hKV' hV'c hK₀p).trans
        (Subgroup.commutator_mono hU'Z le_rfl)
    have hXU : ⁅centerOf (c134Q H K₀), K₀⁆ ≤ ⁅V', K₀⁆ :=
      L32.le_of_ne_bot hF₄ hα₄.1 hβ₄k' hβ₄e hU'X hK₀U' fun h => hU'ne (le_bot_iff.mpr h)
    have hyX : ∀ u ∈ ⁅centerOf (c134Q H K₀), K₀⁆, y * u * y⁻¹ ∈ ⁅centerOf (c134Q H K₀), K₀⁆ :=
      fun u hu => SteinbergCC.conj_mem_commutator hyZQ
        (fun k hk => (Subgroup.mem_normalizer_iff.mp hyK₀ k).mp hk) hu
    have hfixU' := L32.conj_eq_of_natural hF₄ hα₄.1 hβ₄k hβ₄e hKV' hV'c hK₀p hU'X hU'ne bot_le
      (fun u hu => hXU (hyX u (hU'X hu))) hcommU'
    exact fun k hk => hfixU' _ (hkz hzV' k hk)
  | 5, hi =>
    obtain ⟨⟨α₅, hα₅, -, hsum⟩, -⟩ := hi
    obtain ⟨-, -, β₅, -, hβ₅k, hβ₅e⟩ := L32.natural_of_sum_one hsum
    have hfixU := L32.conj_eq_of_natural (F := ZMod 2) (by simp) hα₅.1 hβ₅k hβ₅e hKW hWc hK₀p
      hUQ (fun h => hUnc (h.trans inf_le_right)) inf_le_right hyU hcommU
    exact fun k hk => hfixU _ (hkz hzW k hk)
  | 0, hi => exact hi.elim
  | n + 6, hi => exact hi.elim

end Setting

end CFSG.Quasithin.H13.A5
