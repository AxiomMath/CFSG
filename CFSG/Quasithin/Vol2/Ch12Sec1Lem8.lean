module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem7
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Conj
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

open Sec121H9 Sec121Tr H9Conj in
theorem lem1218_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211) (hH91 : LemH91)
    (h1216 : Lem1216) (h1217 : Lem1217) (hH92 : LemH92Use) (hH93 : LemH93Use) (hRk : LemH9Rank4)
    (hCent : LemH9Cent) (hAxes : LemH9Axes) : Lem1218 := by
  intro G _ _ T L V V₁ V₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hW
  obtain ⟨hTL, hNV⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hV := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hcV : IsMulCommutative ↥V := hV.1
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNV.ge
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hH9 := h9Hyp_of_hyp121 hyp hTL hV
  obtain ⟨-, -, hcardV⟩ := Sec1212.card_eq_of_hyp121 hyp
  have hVT : V ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hyp.le hMV hV2).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTL))
  have h322 : HypE322 T V :=
    ⟨⟨le_top, hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hyp.sylow.2⟩, hVT,
      hTL.trans hMV⟩
  obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ n hyp hTL).2
  obtain ⟨hr, hs, -⟩ := ((lem1212_of h1001 h331 h1211) G T L V V₁ V₂ n β hyp hβ).2 hV
  have hn4 : 4 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hw1 : wParam T V = ((1 : ℕ) : ℕ∞) := by
    refine le_antisymm (iInf₂_le 1 hW) (le_iInf₂ fun j hj => ?_)
    have hj1 : 1 ≤ j := by
      by_contra hlt
      apply hj
      interval_cases j
      exact h1217 G T L V V₁ V₂ n hyp
    exact_mod_cast hj1
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV h322 (by rw [hw1]; exact ENat.natCast_ne_top 1)
  have h24 : HypE324 T V hV := Or.inl (by rw [hw1]; norm_num)
  have hVg : ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) :=
    e3_28_four_left hV h322 h24 hg
  have hrk := e3_28_three hV h322 h24 hg
  have hk : ((n - 2 : ℕ) : ℕ∞) + wParam T V + 1 ≤ rParam V := by
    rw [hw1]
    refine le_trans ?_ hr
    have e : n - 2 + 1 + 1 = n := by omega
    exact_mod_cast e.le
  have h332 := e3_32 hV hg hk
  have hm1 := hg.2
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup G, A = conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) :=
    ⟨_, rfl⟩
  rw [← hAdef] at hrk h332 hm1
  rw [hw1] at hm1
  have hAg : A ≤ conjSubgroup V g := hAdef ▸ inf_le_left
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAdef ▸ inf_le_right
  have hAM : A ≤ Subgroup.normalizer (L : Set G) := hAN.trans hNV.le
  have hAe : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg (isElemAbelian_conjSubgroup hV g)
  have hĀe := isElemAbelian2_autI hV hAe hAN
  have hĀM := autI_mono hV hAM
  have hcardVg : Nat.card (conjSubgroup V g) = 2 * Nat.card A := by
    rw [card_eq_two_pow_mul (isPGroup_conjSubgroup hV2 g) hAg]
    have hm : mQuot (conjSubgroup V g) A = 1 := by exact_mod_cast hm1.symm
    rw [hm, pow_one]
  have hcardVg' : Nat.card (conjSubgroup V g) = Nat.card V := E3.card_conjSubgroup V g
  have hUmem : ∀ w ∈ gammaCheck (n - 2) (autI hV A),
      w.val ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := fun w hw =>
    (h332 (Subgroup.mem_map_of_mem (valHom hV) hw)).2
  have h1216' : ∀ h : G, V₁ ⊓ conjSubgroup V h ≠ ⊥ → ⁅V, conjSubgroup V h⁆ = ⊥ := fun h hne => by
    rw [Sec1217.conjSubgroup_eq_conjugate] at hne ⊢
    exact (h1216 G T L V V₁ V₂ n hyp).2 h hne
  have hV₁g : V₁ ⊓ conjSubgroup V g = ⊥ := by
    by_contra hne
    exact hg.1 (h1216' g hne)
  have hV₂g : V₂ ⊓ conjSubgroup V g = ⊥ := by
    by_contra hne
    obtain ⟨m₀, hm₀, hm₀1⟩ := Sec121Swap.exists_swap_of_hyp121 hyp
    obtain ⟨-, hsw⟩ := Sec121Swap.swap_of_hyp121 hyp hm₀ hm₀1
    have hne' : V₁ ⊓ conjSubgroup V (g * m₀⁻¹) ≠ ⊥ := by
      intro h0
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have h1 : m₀ * x * m₀⁻¹ ∈ V₁ ⊓ conjSubgroup V (g * m₀⁻¹) := by
        refine Subgroup.mem_inf.mpr ⟨hsw x hx.1, ?_⟩
        rw [mem_conjSubgroup_iff]
        have h2 := mem_conjSubgroup_iff.mp hx.2
        simpa [mul_assoc] using h2
      rw [h0, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      calc x = m₀⁻¹ * (m₀ * x * m₀⁻¹) * m₀ := by group
        _ = 1 := by rw [h1]; group
    have h3 := h1216' (g * m₀⁻¹) hne'
    have h4 : conjSubgroup V m₀⁻¹ = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ (hMV hm₀))
    have h5 : conjSubgroup ⁅V, conjSubgroup V g⁆ m₀⁻¹ = ⊥ := by
      rw [conjSubgroup_commutator, h4, conjSubgroup_conjSubgroup]
      exact h3
    apply hg.1
    have h6 : conjSubgroup (conjSubgroup ⁅V, conjSubgroup V g⁆ m₀⁻¹) m₀ = conjSubgroup ⊥ m₀ := by
      rw [h5]
    rwa [conjSubgroup_inv_conj, conjSubgroup_bot] at h6
  have hUfix : ∀ {Y : Subgroup G}, Y ⊓ conjSubgroup V g = ⊥ → ∀ b ∈ A,
      b ∈ Subgroup.normalizer (Y : Set G) → ∀ u ∈ Y,
        u ∈ Subgroup.normalizer (conjSubgroup V g : Set G) → b * u * b⁻¹ = u := by
    intro Y hY b hb hbY u hu huN
    have h1 : b * u * b⁻¹ * u⁻¹ ∈ Y ⊓ conjSubgroup V g := by
      refine ⟨Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hbY u).mp hu) (Y.inv_mem hu), ?_⟩
      have h2 : u * b⁻¹ * u⁻¹ ∈ conjSubgroup V g :=
        (Subgroup.mem_normalizer_iff.mp huN b⁻¹).mp ((conjSubgroup V g).inv_mem (hAg hb))
      have e : b * u * b⁻¹ * u⁻¹ = b * (u * b⁻¹ * u⁻¹) := by group
      rw [e]
      exact (conjSubgroup V g).mul_mem (hAg hb) h2
    rw [hY, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hLnorm : ∀ {Y : Subgroup G}, Y ≤ V → autI hV L ≤ stabV (subI hV Y) →
      ∀ {b : G} (hbN : b ∈ Subgroup.normalizer (V : Set G)),
        convI hV ⟨b, hbN⟩ ∈ autI hV L → b ∈ Subgroup.normalizer (Y : Set G) := by
    intro Y hYV hinv b hbN hbL
    refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := hinv hbL (IntMod.mk hV ⟨a, hYV ha⟩)
    rw [mem_subI, mem_subI, convI_apply_val] at h1
    exact h1.mp ha
  have hstab : ∀ {Y : Subgroup G} {b : G} (hbN : b ∈ Subgroup.normalizer (V : Set G)),
      b ∈ Subgroup.normalizer (Y : Set G) → convI hV ⟨b, hbN⟩ ∈ stabV (subI hV Y) := by
    intro Y b hbN hbY u
    rw [mem_subI, mem_subI, convI_apply_val]
    exact Subgroup.mem_normalizer_iff.mp hbY u.val
  have hW₁₂ : subI hV V₁ ≠ subI hV V₂ := by
    intro h
    have h1 : subI hV V₁ = ⊥ := by rw [← hH9.inf, ← h, inf_idem]
    have h2 := hH9.card₁
    rw [h1, Subgroup.card_bot] at h2
    rcases hyp.rank with rfl | rfl <;> norm_num at h2
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G, B = A ⊓ Subgroup.normalizer (V₁ : Set G) := ⟨_, rfl⟩
  have hBA : B ≤ A := hBdef ▸ inf_le_left
  have hBV₁ : B ≤ Subgroup.normalizer (V₁ : Set G) := hBdef ▸ inf_le_right
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBA.trans hAN
  have hBL : autI hV B ≤ autI hV L := by
    intro φ hφ
    obtain ⟨⟨b, hbN⟩, hbB, rfl⟩ := (mem_autI hV).1 hφ
    by_contra hbL
    apply hW₁₂
    have hbM : convI hV ⟨b, hbN⟩ ∈ autI hV (Subgroup.normalizer (L : Set G)) :=
      (mem_autI hV).2 ⟨⟨b, hbN⟩, hAM (hBA hbB), rfl⟩
    rw [← map_W₁_of_not_mem hH9 hbM hbL, map_eq_of_mem_stabV (hstab hbN (hBV₁ hbB))]
  have hBV₂ : B ≤ Subgroup.normalizer (V₂ : Set G) := fun b hb =>
    hLnorm hV₂V hH9.inv₂ (hBN hb) (hBL ((mem_autI hV).2 ⟨⟨b, hBN hb⟩, hb, rfl⟩))
  have hBbeq : autI hV B = autI hV A ⊓ autI hV L := by
    apply le_antisymm (le_inf (autI_mono hV hBA) hBL)
    intro φ hφ
    obtain ⟨⟨a, haN⟩, haA, rfl⟩ := (mem_autI hV).1 hφ.1
    have haV₁ := hLnorm hV₁V hH9.inv₁ haN hφ.2
    exact (mem_autI hV).2 ⟨⟨a, haN⟩, by rw [hBdef]; exact ⟨haA, haV₁⟩, rfl⟩
  have hĀB : Nat.card (autI hV A) ≤ 2 * Nat.card (autI hV B) := by
    have h1 := Subgroup.relIndex_mul_card (autI hV L) (autI hV A)
    have h2 : (autI hV L).relIndex (autI hV A) ≤ 2 := by
      rw [← hH9.index]
      exact Subgroup.relIndex_le_of_le_right hĀM (by rw [hH9.index]; norm_num)
    rw [inf_comm, ← hBbeq] at h1
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  have hAB : Nat.card A ≤ 2 * Nat.card B := by
    have h1 := card_autI_mul_card_inf hV hAN
    have h2 := card_autI_mul_card_inf hV hBN
    have h3 : B ⊓ Subgroup.centralizer (V : Set G) = A ⊓ Subgroup.centralizer (V : Set G) := by
      apply le_antisymm (inf_le_inf_right _ hBA)
      intro x hx
      refine ⟨?_, hx.2⟩
      rw [hBdef]
      refine ⟨hx.1, Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_⟩
      have h4 := Subgroup.mem_centralizer_iff.mp hx.2 a (hV₁V ha)
      rw [← h4, mul_inv_cancel_right]
      exact ha
    rw [h3] at h2
    rw [← h1, ← h2]
    nlinarith
  have hĀp := isPGroup_of_isElemAbelian2 hĀe
  have hrkA : n - 1 ≤ rk ↥(autI hV A) := by
    rw [hw1] at hrk
    have h2 : ((n - 1 : ℕ) : ℕ∞) ≤ rParam V - ((1 : ℕ) : ℕ∞) := by
      rw [ENat.natCast_sub]
      exact tsub_le_tsub_right hr _
    exact_mod_cast h2.trans hrk
  rcases (by omega : rk ↥(autI hV A) = n - 1 ∨ n ≤ rk ↥(autI hV A)) with heq | hge
  ·
    have hcardĀ : Nat.card (autI hV A) = 2 ^ (n - 1) := by
      rw [card_eq_two_pow_of_isPGroup hĀp, heq]
    have hfixY : ∀ {Y : Subgroup G}, Y ≤ V → Y ⊓ conjSubgroup V g = ⊥ →
        B ≤ Subgroup.normalizer (Y : Set G) → ∀ bb ∈ autI hV B, bb ≠ 1 →
          fixV (Subgroup.zpowers bb) ⊓ subI hV Y =
            subI hV (Y ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) := by
      intro Y hYV hYg hBY bb hbb hbb1
      have hbbA : bb ∈ autI hV A := autI_mono hV hBA hbb
      obtain ⟨⟨b, hbN⟩, hbB, rfl⟩ := (mem_autI hV).1 hbb
      apply le_antisymm
      · intro w hw
        rw [Subgroup.mem_inf] at hw
        rw [mem_subI, Subgroup.mem_inf]
        refine ⟨hw.2, ?_⟩
        have hzle : Subgroup.zpowers (convI hV ⟨b, hbN⟩) ≤ autI hV A :=
          Subgroup.zpowers_le.mpr hbbA
        have hord : orderOf (convI hV ⟨b, hbN⟩) = 2 := orderOf_eq_prime (hĀe.2 _ hbbA) hbb1
        have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers (convI hV ⟨b, hbN⟩))
          (autI hV A)
        rw [inf_eq_left.mpr hzle, Nat.card_zpowers, hord, hcardĀ] at h1
        have h8 : (Subgroup.zpowers (convI hV ⟨b, hbN⟩)).relIndex (autI hV A) = 2 ^ (n - 2) := by
          have e : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
            rw [← pow_succ]
            congr 1
            omega
          rw [e] at h1
          exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
        have hq : mQuot (autI hV A) (Subgroup.zpowers (convI hV ⟨b, hbN⟩)) ≤ n - 2 := by
          rw [mQuot, h8, padicValNat.prime_pow]
        exact hUmem w (fixV_le_gammaCheck hzle hq hw.1)
      · intro w hw
        rw [mem_subI, Subgroup.mem_inf] at hw
        rw [Subgroup.mem_inf]
        refine ⟨?_, hw.1⟩
        rw [H.mem_fixV_zpowers_iff]
        apply IntMod.val_injective
        rw [convI_apply_val]
        exact hUfix hYg b (hBA hbB) (hBY hbB) w.val hw.1 hw.2
    have hBbe : IsElemAbelian2 (autI hV B) :=
      isElemAbelian2_autI hV (B2F.isElemAbelian_mono hBA hAe) hBN
    have hBbcard : 2 ^ (n - 2) ≤ Nat.card (autI hV B) := by
      have e : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hcardĀ, e] at hĀB
      omega
    obtain ⟨rfl, hB4, hfix4⟩ := hAxes _ _ _ _ _ _ _ hH9 _ hBL hBbe hBbcard
      fun b hb c hc hb1 hc1 => by
        rw [hfixY hV₁V hV₁g hBV₁ b hb hb1, hfixY hV₁V hV₁g hBV₁ c hc hc1,
          hfixY hV₂V hV₂g hBV₂ b hb hb1, hfixY hV₂V hV₂g hBV₂ c hc hc1]
        exact ⟨rfl, rfl⟩
    obtain ⟨φ, hφA, hφL⟩ : ∃ φ ∈ autI hV A, φ ∉ autI hV L := by
      by_contra hcon
      push Not at hcon
      have h1 : autI hV A ≤ autI hV B := by
        rw [hBbeq]
        exact le_inf le_rfl hcon
      have h2 := Subgroup.card_le_of_le h1
      rw [hcardĀ, hB4] at h2
      norm_num at h2
    obtain ⟨⟨a, haN⟩, haA, rfl⟩ := (mem_autI hV).1 hφA
    obtain ⟨bb, hbb, hbb1⟩ := ((autI hV B).bot_or_exists_ne_one).resolve_left fun h0 => by
      rw [h0, Subgroup.card_bot] at hB4
      norm_num at hB4
    have hU₁ : Nat.card ↥(V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) = 2 ^ 2 := by
      have h1 := hfix4 bb hbb hbb1
      rwa [hfixY hV₁V hV₁g hBV₁ bb hbb hbb1, card_subI hV (inf_le_left.trans hV₁V)] at h1
    have hU₁C : (V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) ⊓
        Subgroup.centralizer (conjSubgroup V g : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hau : a * u * a⁻¹ = u := by
        have h1 := Subgroup.mem_centralizer_iff.mp hu.2 a (hAg haA)
        rw [h1, mul_inv_cancel_right]
      have hmk : IntMod.mk hV ⟨u, hV₁V hu.1.1⟩ ∈ subI hV V₁ ⊓ subI hV V₂ := by
        refine ⟨hu.1.1, ?_⟩
        rw [← map_W₁_of_not_mem hH9 ((mem_autI hV).2 ⟨⟨a, haN⟩, hAM haA, rfl⟩) hφL]
        refine ⟨IntMod.mk hV ⟨u, hV₁V hu.1.1⟩, hu.1.1, ?_⟩
        apply IntMod.val_injective
        rw [MulEquiv.coe_toMonoidHom, convI_apply_val]
        exact hau
      rw [hH9.inf, Subgroup.mem_bot] at hmk
      rw [Subgroup.mem_bot]
      exact congrArg IntMod.val hmk
    have hXN : conjSubgroup (V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹ ≤
        Subgroup.normalizer (V : Set G) := by
      have h1 := conjSubgroup_mono_left g⁻¹
        (inf_le_right : V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) ≤
          Subgroup.normalizer (conjSubgroup V g : Set G))
      rwa [conjSubgroup_normalizer, conjSubgroup_conj_inv] at h1
    have hXe : IsElemAbelian 2
        (conjSubgroup (V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹) :=
      isElemAbelian_conjSubgroup (B2F.isElemAbelian_mono (inf_le_left.trans hV₁V) hV) g⁻¹
    have hXcent : Nat.card (IntMod V hV) ≤ 2 ^ 2 * Nat.card (fixV (autI hV
        (conjSubgroup (V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹))) := by
      rw [card_fixV_autI hV hXN]
      have h1 := Sec1217.card_conj_inf_centralizer (conjSubgroup V g)
        (V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹
      rw [conjSubgroup_conj_inv] at h1
      rw [h1]
      have h2 : B ≤ conjSubgroup V g ⊓ Subgroup.centralizer
          ((V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) : Subgroup G) : Set G) := by
        intro b hb
        refine ⟨hAg (hBA hb), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
        have h3 := hUfix hV₁g b (hBA hb) (hBV₁ hb) u hu.1 hu.2
        calc u * b = (b * u * b⁻¹) * b := by rw [h3]
          _ = b * u := by group
      have h3 := Subgroup.card_le_of_le h2
      show Nat.card V ≤ _
      omega
    have h1 := hCent _ _ _ _ _ _ _ hH9 _ (autI_mono hV (hXN.trans hNV.le))
      (isElemAbelian2_autI hV hXe hXN) hXcent
    have h2 := card_autI_mul_card_inf hV hXN
    have h3 := Sec1217.card_conj_inf_centralizer
      (V₁ ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) (conjSubgroup V g) g⁻¹
    rw [conjSubgroup_conj_inv, hU₁C, Subgroup.card_bot] at h3
    rw [h3, E3.card_conjSubgroup, hU₁] at h2
    omega
  ·
    have hcardĀ : 2 ^ n ≤ Nat.card (autI hV A) := by
      rw [card_eq_two_pow_of_isPGroup hĀp]
      exact Nat.pow_le_pow_right (by norm_num) hge
    rcases hyp.rank with rfl | rfl
    swap
    ·
      have htop := (hH92 _ _ _ _ _ _ _ hH9 (isDualH9_of_isDualPairing121 hV hV₁V hV₂V hβ) _ hĀM
        hĀe hcardĀ).2.1
      apply hVg
      intro v hv
      exact hUmem (IntMod.mk hV ⟨v, hv⟩) (by rw [htop]; exact Subgroup.mem_top _)
    have hĀ16 : Nat.card (autI hV A) = 2 ^ 4 :=
      le_antisymm (hRk _ _ _ _ _ _ hH9 _ hĀM hĀe) hcardĀ
    have hΓtop : gammaCheck 2 (autI hV A) ≠ ⊤ := by
      intro htop
      apply hVg
      intro v hv
      exact hUmem (IntMod.mk hV ⟨v, hv⟩) (by rw [show 4 - 2 = 2 from rfl, htop]; trivial)
    obtain ⟨-, hD2⟩ := e16_facts_of_lemH93Use hH93 hH9 hĀM hĀe hĀ16
    obtain ⟨hΓ6, hfix4, hfaith⟩ := hD2 hΓtop
    have hU64 : 2 ^ 6 ≤ Nat.card ↥(V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) := by
      rw [← hΓ6, ← Subgroup.card_map_of_injective (valHom_injective hV)]
      exact Subgroup.card_le_of_le h332
    have h37 := e3_7 hV (B := A) hAdef.le
      (by rw [hs]; exact_mod_cast (by rw [← hm1]; norm_num : (mQuot (conjSubgroup V g) A : ℕ∞) < 2))
    have hYN : conjSubgroup (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹ ≤
        Subgroup.normalizer (V : Set G) := by
      have h1 := conjSubgroup_mono_left g⁻¹
        (inf_le_right : V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) ≤
          Subgroup.normalizer (conjSubgroup V g : Set G))
      rwa [conjSubgroup_normalizer, conjSubgroup_conj_inv] at h1
    have hYe : IsElemAbelian 2
        (conjSubgroup (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹) :=
      isElemAbelian_conjSubgroup (B2F.isElemAbelian_mono inf_le_left hV) g⁻¹
    have hYbe := isElemAbelian2_autI hV hYe hYN
    have hYbM := autI_mono hV (hYN.trans hNV.le)
    have hYb16 := hRk _ _ _ _ _ _ hH9 _ hYbM hYbe
    have h2 := card_autI_mul_card_inf hV hYN
    have h3 := Sec1217.card_conj_inf_centralizer
      (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) (conjSubgroup V g) g⁻¹
    rw [conjSubgroup_conj_inv] at h3
    rw [h3, E3.card_conjSubgroup] at h2
    have hUC : (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) ⊓
        Subgroup.centralizer (conjSubgroup V g : Set G) ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
      intro x hx
      have h4 : x ∈ V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) := ⟨hx.1.1, hx.2⟩
      rw [← h37] at h4
      exact h4
    have hcUC := Subgroup.card_le_of_le hUC
    rw [← card_fixV_autI hV hAN] at hcUC
    have hc4 : Nat.card (fixV (autI hV A)) = 2 ^ 2 := by nlinarith
    have hU64' : Nat.card ↥(V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) = 2 ^ 6 := by
      nlinarith
    have hYb16' : Nat.card (autI hV
        (conjSubgroup (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹)) = 2 ^ 4 := by
      nlinarith
    have hfaith' := hfaith hc4
    have hmVU : mQuot V (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) = 2 := by
      have h4 := card_eq_two_pow_mul hV2
        (inf_le_left : V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) ≤ V)
      rw [hcardV, hU64'] at h4
      have h5 : 2 ^ mQuot V (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) = 2 ^ 2 := by
        omega
      exact Nat.pow_right_injective (le_refl 2) h5
    have hCU : Subgroup.centralizer
        ((V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) : Subgroup G) : Set G) ≤
          Subgroup.normalizer (V : Set G) := by
      by_contra hC
      have h4 := rParam_le_mQuot inf_le_left hC
      rw [hmVU] at h4
      have h5 := hr.trans h4
      norm_num at h5
    have hVgU : conjSubgroup V g ⊓ Subgroup.centralizer
        ((V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) : Subgroup G) : Set G) ≤
          A ⊓ Subgroup.centralizer (V : Set G) := by
      intro c hc
      have hcN := hCU hc.2
      have hcA : c ∈ A := by rw [hAdef]; exact ⟨hc.1, hcN⟩
      refine Subgroup.mem_inf.mpr ⟨hcA, (convI_eq_one_iff hV ⟨c, hcN⟩).mp ?_⟩
      refine hfaith' _ ((mem_autI hV).2 ⟨⟨c, hcN⟩, hcA, rfl⟩) fun w hw => ?_
      apply IntMod.val_injective
      rw [convI_apply_val]
      have h4 := Subgroup.mem_centralizer_iff.mp hc.2 w.val ⟨w.val_mem, hUmem w hw⟩
      show c * w.val * c⁻¹ = w.val
      rw [← h4, mul_inv_cancel_right]
    have hCA : Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) = 2 ^ 3 := by
      have h4 := card_autI_mul_card_inf hV hAN
      rw [hĀ16] at h4
      rw [hcardVg', hcardV] at hcardVg
      omega
    have hCVgU : Nat.card ↥(conjSubgroup V g ⊓ Subgroup.centralizer
        ((V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) : Subgroup G) : Set G)) = 2 ^ 3 := by
      refine le_antisymm (hCA ▸ Subgroup.card_le_of_le hVgU) ?_
      rw [← hCA]
      refine Subgroup.card_le_of_le fun x hx => ⟨hAg hx.1, ?_⟩
      exact Subgroup.centralizer_le (by exact_mod_cast inf_le_left) hx.2
    obtain ⟨hne8, -⟩ := e16_facts_of_lemH93Use hH93 hH9 hYbM hYbe hYb16'
    apply hne8
    rw [card_fixV_autI hV hYN]
    have h4 := Sec1217.card_conj_inf_centralizer (conjSubgroup V g)
      (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) g⁻¹
    rw [conjSubgroup_conj_inv] at h4
    rw [h4, hCVgU]

end CFSG.Quasithin.H13
