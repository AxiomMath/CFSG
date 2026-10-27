module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R15_11Small (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L), mSub V₀ ≤ 2 →
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ i : ℕ, i ≤ 2 → ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M →
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L = ⊥ ∧
          ((gamma15 D.M V₀ V h.hyp151.isElemAbelian L = 2 ∧
              s15 D.M V₀ V h.hyp151.isElemAbelian L = 4 ∧ i = 2) ∨
            (s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 ∧
              gamma15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3))

theorem s16c34_eleven_not_le (D : Data G) (h159 : R15_9Small D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV₀ : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) {i : ℕ} {g : G}
    {A B : Subgroup G} {v : G} (hcfg : Cfg11 V D.M i g A B v) :
    ¬ conjSubgroup V g ≤ D.M ∧ ¬ V ≤ conjSubgroup D.M g := by
  obtain ⟨a, haA, ha⟩ := hcfg.comm_A
  have hC := h159 V₀ V L h hV₀ hL
  have hav : a * v = v * a → a * v * a⁻¹ * v⁻¹ = 1 := fun hh => by
    rw [hh]
    group
  constructor
  · intro hVgM
    have hmem : conjSubgroup V g ≤ E3.wClos V 0 D.M :=
      le_iSup₂_of_le (conjSubgroup V g) ⟨hVgM, g, le_rfl, E3.mQuot_self _⟩ le_rfl
    exact ha (hav (Subgroup.mem_centralizer_iff.1 (hC (hmem (hcfg.A_le haA))) v hcfg.v_mem).symm)
  · intro hVM
    have hmem' : conjSubgroup V g⁻¹ ≤ D.M := by
      have := E3.conjSubgroup_mono_left g⁻¹ hVM
      rwa [E3.conjSubgroup_conj_inv] at this
    have hmem : conjSubgroup V g⁻¹ ≤ E3.wClos V 0 D.M :=
      le_iSup₂_of_le (conjSubgroup V g⁻¹) ⟨hmem', g⁻¹, le_rfl, E3.mQuot_self _⟩ le_rfl
    have hx : g * v * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
      rw [e]
      exact hcfg.v_mem
    have hy : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 (hcfg.A_le haA)
    have hcomm := Subgroup.mem_centralizer_iff.1 (hC (hmem hx)) _ hy
    apply ha
    apply hav
    have h1 : g * a * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * a * g⁻¹) := hcomm
    have h2 : g * (a * v) * g⁻¹ = g * (v * a) * g⁻¹ := by
      calc g * (a * v) * g⁻¹ = g * a * g⁻¹ * (g * v * g⁻¹) := by group
        _ = g * v * g⁻¹ * (g * a * g⁻¹) := h1
        _ = g * (v * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem s16c34_eleven_not_centralizer_le (D : Data G) (h159 : R15_9Small D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV₀ : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) {i : ℕ} {g : G}
    {A B : Subgroup G} {v : G} (hcfg : Cfg11 V D.M i g A B v) {a : G} (haA : a ∈ A) :
    ¬ centralizer ({a * v * a⁻¹ * v⁻¹} : Set G) ≤ conjSubgroup D.M g := by
  intro hle
  apply (s16c34_eleven_not_le D h159 h hV₀ hV hL hcfg).2
  have hz : a * v * a⁻¹ * v⁻¹ ∈ V := by
    have h1 : a * v * a⁻¹ ∈ V := by
      have := h.hyp151.hyp125.pairFacts.le_normalizer (hcfg.A_le_M haA)
      exact (Subgroup.mem_normalizer_iff.1 this v).1 hcfg.v_mem
    exact V.mul_mem h1 (V.inv_mem hcfg.v_mem)
  intro y hy
  apply hle
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact congrArg Subtype.val (hV.1.is_comm.comm ⟨_, hz⟩ ⟨y, hy⟩)

theorem s16c34_eleven_support (D : Data G) (h1217 : R1217 D) (h159 : R15_9Small D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV₀ : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥)
    (hV1 : v1Sub D.M V₀ V hV L = ⊥) {i : ℕ} {g : G} {A B : Subgroup G} {v : G}
    (hcfg : Cfg11 V D.M i g A B v) (hvg : v ∈ conjSubgroup D.M g) :
    2 ≤ (suppAct (wConjG D.M V₀ V hV L g) v).ncard ∧
      (3 ≤ s15 D.M V₀ V hV L →
        s15 D.M V₀ V hV L - 1 ≤ (suppAct (wConjG D.M V₀ V hV L g) v).ncard) ∧
      (suppAct (wConjG D.M V₀ V hV L g) v).ncard ≤
        E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) ∧
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)) ≤ i + 1 := by
  have hY := E3.isElemAbelian_conjSubgroup hV g
  have hind := s15_Glue3_wConjG_indep D h.hyp151 hV hL hV1 g
  have hspan := s15_Glue3_wConjG_sSup D h1217 h.hyp151 hV hL g
  have hγ : ∀ X ∈ wConjG D.M V₀ V hV L g, rk ↥X = gamma15 D.M V₀ V hV L :=
    fun X hX => s15_Glue3_wConjG_rk D h.hyp151 hV hV1 g hX
  have ht : v * v = 1 := s15_Eleven_sq hV hcfg.v_mem
  have hperm : ∀ X ∈ wConjG D.M V₀ V hV L g, conjSubgroup X v ∈ wConjG D.M V₀ V hV L g :=
    fun X hX => s15_Glue3_wConjG_perm D hV hvg hX
  have hcard := s15_Support_ncard_act_le hY hind hspan hγ (two_le_gamma15 D h.hyp151 hV hL) ht hperm
  obtain ⟨a, haA, ha⟩ := hcfg.comm_A
  have hmem : a * v * a⁻¹ * v⁻¹ ∈ sSup (suppAct (wConjG D.M V₀ V hV L g) v) := by
    rw [sSup_eq_iSup]
    exact s15_Support_comm_mem hY hspan ht hperm (hcfg.A_le haA)
  have hsub : suppAct (wConjG D.M V₀ V hV L g) v ⊆ wConjG D.M V₀ V hV L g := fun X hX => hX.1
  obtain ⟨h2, h3⟩ := s15_Eleven_supp_card_ge D h hV g hsub hmem ha
    (s16c34_eleven_not_centralizer_le D h159 h hV₀ hV hL hcfg haA)
  exact ⟨h2, h3, hcard, s15_Eleven_n_le hcfg⟩

theorem s16c34_eleven_s_two (D : Data G) (h1217 : R1217 D) (h159 : R15_9Small D) (hT7 : RT7Small D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV₀ : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    (hs2 : s15 D.M V₀ V hV L = 2) (hγ : 4 ≤ gamma15 D.M V₀ V hV L) {i : ℕ} (hi : i ≤ 2)
    (h4 : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M → 4 ≤ E3.mQuot V U)
    {g : G} {A : Subgroup G} (hAg : A ≤ conjSubgroup V g) (hAM : A ≤ D.M)
    (hmA : E3.mQuot (conjSubgroup V g) A = i)
    (hAN : ¬ A ≤ normalizer (wSub V₀ V hV L : Set G)) : False := by
  obtain ⟨B₀, v₀, hcfg₀⟩ := s15_Eleven_exists_Bv D h hV hL hV1 hAg hAM hmA hAN
  have hVg : ¬ V ≤ conjSubgroup D.M g := (s16c34_eleven_not_le D h159 h hV₀ hV hL hcfg₀).2
  obtain ⟨X, hX, hXg⟩ := s15_Eleven_exists_member_not_le D h1217 h hV hL hVg
  obtain ⟨B, v, hcfg, hvX⟩ := s15_Eleven_exists_Bv_two D h hV hL hV1 hs2 hAg hAM hmA hAN hX
  have hv1 : v ≠ 1 := by
    obtain ⟨a, -, ha⟩ := hcfg.comm_A
    rintro rfl
    exact ha (by group)
  have hvg : v ∈ conjSubgroup D.M g := s15_Eleven_v_mem_conj D hi hcfg h4
  obtain ⟨hc2, -, hcn, hn⟩ := s16c34_eleven_support D h1217 h159 h hV₀ hV hL hV1 hcfg hvg
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
  have h7 := hT7 V₀ V L h hV₀ hL 1 X hX (conjSubgroup X₀ g ⊓ centralizer ({v} : Set G)) ⊥
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

theorem s16c34_eleven_s_four (D : Data G) (h1217 : R1217 D) (h159 : R15_9Small D) (hT8 : RT8 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV₀ : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    (hs4 : s15 D.M V₀ V hV L = 4) (hγ : 3 ≤ gamma15 D.M V₀ V hV L) {i : ℕ} {g : G}
    {A B : Subgroup G} {v : G} (hcfg : Cfg11 V D.M i g A B v) (hvg : v ∈ conjSubgroup D.M g)
    (hcard : (suppAct (wConjG D.M V₀ V hV L g) v).ncard =
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)))
    (hle : (suppAct (wConjG D.M V₀ V hV L g) v).ncard ≤ 3) : False := by
  have hY := E3.isElemAbelian_conjSubgroup hV g
  have hind := s15_Glue3_wConjG_indep D h.hyp151 hV hL hV1 g
  have hspan := s15_Glue3_wConjG_sSup D h1217 h.hyp151 hV hL g
  have hγΔ : ∀ E ∈ wConjG D.M V₀ V hV L g, rk ↥E = gamma15 D.M V₀ V hV L :=
    fun E hE => s15_Glue3_wConjG_rk D h.hyp151 hV hV1 g hE
  have ht : v * v = 1 := s15_Eleven_sq hV hcfg.v_mem
  have hperm : ∀ E ∈ wConjG D.M V₀ V hV L g, conjSubgroup E v ∈ wConjG D.M V₀ V hV L g :=
    fun E hE => s15_Glue3_wConjG_perm D hV hvg hE
  have hfix := s15_Support_eq_of_ncard_eq hY hind hspan hγΔ hγ ht hperm hcard
  obtain ⟨a, haA, ha⟩ := hcfg.comm_A
  have hcent := hT8 V₀ V L h hL hV1 hs4 hγ g v hvg ht hle hfix a (hcfg.A_le haA) ha
  exact s16c34_eleven_not_centralizer_le D h159 h hV₀ hV hL hcfg haA hcent

theorem s16c34_fifteen_eleven (D : Data G) (h1217 : R1217 D) (h159 : R15_9Small D)
    (hT7 : RT7Small D) (hT8 : RT8 D) : R15_11Small D := by
  intro V₀ V L h hV₀ hL i hi hC
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  have hV1 := s15_Eleven_v1_eq_bot D h hV hC
  refine ⟨hV1, ?_⟩
  by_contra hcon
  obtain ⟨hn1, hn2⟩ := not_or.1 hcon
  have hev := s15_Eleven_even D h hV hL hV1 hC
  have hspos := s15_Eleven_pos_s D h.hyp151 hV
  have h4 := s15_Eleven_h4 D h hV hL hev hn2
  obtain ⟨g, A, hAg, hAM, hmA, hAN⟩ := s15_Eleven_exists_A D h hV hL hV1 hC
  obtain ⟨B, v, hcfg⟩ := s15_Eleven_exists_Bv D h hV hL hV1 hAg hAM hmA hAN
  have hvg := s15_Eleven_v_mem_conj D hi hcfg h4
  obtain ⟨hc2, hcs, hcn, hn⟩ := s16c34_eleven_support D h1217 h159 h hV₀ hV hL hV1 hcfg hvg
  rcases s15_Eleven_cases hev hspos hi hc2 hcs hcn hn with hs2 | ⟨hs4, hi2, hc3, hn3⟩
  · have hγ : 4 ≤ gamma15 D.M V₀ V hV L := by
      by_contra hlt
      exact hn2 ⟨hs2, by omega⟩
    exact s16c34_eleven_s_two D h1217 h159 hT7 h hV₀ hV hL hV1 hs2 hγ hi h4 hAg hAM hmA hAN
  · have hγ : 3 ≤ gamma15 D.M V₀ V hV L := by
      have h2 := two_le_gamma15 D h.hyp151 hV hL
      by_contra hlt
      exact hn1 ⟨by omega, hs4, hi2⟩
    exact s16c34_eleven_s_four D h1217 h159 hT8 h hV₀ hV hL hV1 hs4 hγ hcfg hvg (by omega)
      (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
