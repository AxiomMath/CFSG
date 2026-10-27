module

public import CFSG.Quasithin.Background.E6TwentyTwo

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623A3Dichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → E3.rParam V = 1 →
    U ≤ V → E3.mQuot V U = 1 → ¬ Subgroup.centralizer (U : Set G) ≤ M →
    CharTwo (Subgroup.centralizer (U : Set G)) →
    IsChi0Block (Subgroup.centralizer (U : Set G)) L → IsAltType L 3 → ¬ L ≤ M →
    ∀ t ∈ T, CFSG.conjugate L t = L ∨ ⁅L, CFSG.conjugate L t⁆ = ⊥

@[expose] def E623A5Dichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → E3.rParam V = 1 →
    U ≤ V → E3.mQuot V U = 1 → ¬ Subgroup.centralizer (U : Set G) ≤ M →
    CharTwo (Subgroup.centralizer (U : Set G)) →
    IsChi0Block (Subgroup.centralizer (U : Set G)) L → IsAltType L 5 → ¬ L ≤ M →
    ∀ t ∈ T, CFSG.conjugate L t = L ∨ ⁅L, CFSG.conjugate L t⁆ = ⊥

section Orbit

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem false_of_dichotomy (h311 : Theorem311Stmt) (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    (hm : 2 < E3.mParam (autI hV M)) (h6 : 6 ≤ E3.mQuot V ⊥) (hUV : U ≤ V)
    (hU1 : E3.mQuot V U = 1) (hLU : L ≤ Subgroup.centralizer (U : Set G)) (hLM : ¬ L ≤ M)
    (hdich : ∀ t ∈ T, CFSG.conjugate L t = L ∨ ⁅L, CFSG.conjugate L t⁆ = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} (hxL : x ∈ L) (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hxC : x ∉ Subgroup.centralizer (L : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.normal
  have hUt : ∀ t ∈ T, CFSG.conjugate U t ≤ V ∧ E3.mQuot V (CFSG.conjugate U t) = 1 :=
    fun t ht => ⟨conjugate_le_of_mem_normalizer hUV (hTN ht), (mQuot_conjugate (hTN ht)).trans hU1⟩
  have hLUt : ∀ t : G, CFSG.conjugate L t ≤
      Subgroup.centralizer ((CFSG.conjugate U t : Subgroup G) : Set G) := by
    intro t
    rw [← BenderBranch.conjugate_centralizer]
    exact BenderBranch.conjugate_mono hLU t
  have hconj : ∀ g : G, g⁻¹ * x * g ∈ CFSG.conjugate L g ∧ (g⁻¹ * x * g) ^ p = 1 ∧
      g⁻¹ * x * g ∉ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    intro g
    refine ⟨BenderBranch.mem_conjugate_iff.2 (by group; exact hxL), ?_, ?_⟩
    · rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hxp]
      group
    · rw [← BenderBranch.conjugate_centralizer, BenderBranch.mem_conjugate_iff]
      intro hx
      apply hxC
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [this] at hx
  have horbit : ∃ t₀ ∈ T, ∀ t ∈ T, CFSG.conjugate L t = L ∨
      CFSG.conjugate L t = CFSG.conjugate L t₀ := by
    by_cases hall : ∀ t ∈ T, CFSG.conjugate L t = L
    · exact ⟨1, T.one_mem, fun t ht => Or.inl (hall t ht)⟩
    push Not at hall
    obtain ⟨t₀, ht₀, hne₀⟩ := hall
    refine ⟨t₀, ht₀, fun t ht => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hne₁, hne₂⟩ := hcon
    have hc0 : ⁅L, CFSG.conjugate L t₀⁆ = ⊥ := (hdich t₀ ht₀).resolve_left hne₀
    have hc1 : ⁅L, CFSG.conjugate L t⁆ = ⊥ := (hdich t ht).resolve_left hne₁
    have hxg : t * t₀⁻¹ ∈ T := T.mul_mem ht (T.inv_mem ht₀)
    have heqg : CFSG.conjugate (CFSG.conjugate L (t * t₀⁻¹)) t₀ = CFSG.conjugate L t := by
      rw [BenderBranch.conjugate_conjugate, inv_mul_cancel_right]
    have hc2 : ⁅CFSG.conjugate L t₀, CFSG.conjugate L t⁆ = ⊥ := by
      rcases hdich _ hxg with he | he
      · exfalso
        apply hne₂
        rw [← heqg, he]
      · rw [← heqg]
        unfold CFSG.conjugate
        rw [← Subgroup.map_commutator]
        change ⁅L, CFSG.conjugate L (t * t₀⁻¹)⁆.map _ = ⊥
        rw [he, Subgroup.map_bot]
    set D := U ⊓ CFSG.conjugate U t₀ ⊓ CFSG.conjugate U t with hDdef
    have hDV : D ≤ V := inf_le_left.trans (inf_le_left.trans hUV)
    have hD1 : D ≠ ⊥ := by
      intro h0
      have h1 := mQuot_inf_le (U := U ⊓ CFSG.conjugate U t₀) (U' := CFSG.conjugate U t) hV2
      have h2 := mQuot_inf_le (U := U) (U' := CFSG.conjugate U t₀) hV2
      rw [← hDdef, h0, (hUt t ht).2] at h1
      rw [hU1, (hUt t₀ ht₀).2] at h2
      omega
    have hLD : L ≤ Subgroup.centralizer (D : Set G) :=
      hLU.trans (Subgroup.centralizer_le (inf_le_left.trans inf_le_left))
    have hL0D : CFSG.conjugate L t₀ ≤ Subgroup.centralizer (D : Set G) :=
      (hLUt t₀).trans (Subgroup.centralizer_le (inf_le_left.trans inf_le_right))
    have hLgD : CFSG.conjugate L t ≤ Subgroup.centralizer (D : Set G) :=
      (hLUt t).trans (Subgroup.centralizer_le inf_le_right)
    have h3 := three_le_pRank_of_commuting (p := p)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc0)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc2) hLD hL0D hLgD hxL
      (hconj t₀).1 (hconj t).1 hxp (hconj t₀).2.1 (hconj t).2.1 hx1 (hconj t₀).2.2
      (hconj t).2.2
    have h4 : CFSG.Open.pRank p (Subgroup.centralizer (D : Set G)) ≤ 2 :=
      (CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.centralizer_le_normalizer _)).trans
        ((A1b.pRank_le_evenRank hp hp2 ⟨D, hD1, hV2.to_le hDV, rfl⟩).trans h.qtke.2.2)
    omega
  obtain ⟨t₀, ht₀, ht₀orb⟩ := horbit
  set Y := L ⊔ CFSG.conjugate L t₀ with hYdef
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := by
    intro t ht
    have hmem : ∀ g ∈ T, CFSG.conjugate L g ≤ Y := fun g hg => by
      rcases ht₀orb g hg with he | he
      · rw [he]
        exact le_sup_left
      · rw [he]
        exact le_sup_right
    have hle : CFSG.conjugate Y t ≤ Y := by
      unfold CFSG.conjugate
      rw [Subgroup.map_sup]
      refine sup_le (hmem t ht) ?_
      have := hmem (t₀ * t) (T.mul_mem ht₀ ht)
      rwa [← BenderBranch.conjugate_conjugate] at this
    have heq : CFSG.conjugate Y t = Y :=
      Subgroup.eq_of_le_of_card_ge hle (BenderBranch.card_conjugate Y t).ge
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 heq
  set W := V ⊓ Subgroup.centralizer (Y : Set G) with hWdef
  have hWV : W ≤ V := inf_le_left
  have hUU : U ⊓ CFSG.conjugate U t₀ ≤ W := by
    intro y hy
    refine ⟨hUV hy.1, ?_⟩
    have hyL : y ∈ Subgroup.centralizer (L : Set G) := Subgroup.le_centralizer_iff.1 hLU hy.1
    have hyL0 : y ∈ Subgroup.centralizer ((CFSG.conjugate L t₀ : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.1 (hLUt t₀) hy.2
    have hYy : Y ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hyL l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hyL0 l hl)
    exact Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hYy hl)
  have hWq : E3.mQuot V W ≤ 2 := by
    have h1 := E3.mQuot_mono (V := V) hUU
    have h2 := mQuot_inf_le (U := U) (U' := CFSG.conjugate U t₀) hV2
    rw [hU1, (hUt t₀ ht₀).2] at h2
    omega
  have hW1 : W ≠ ⊥ := by
    intro h0
    rw [h0] at hWq
    omega
  have hLW : L ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.1 (inf_le_right.trans
      (Subgroup.centralizer_le (show (L : Set G) ⊆ Y from fun _ hx => Subgroup.mem_sup_left hx)))
  have hWM : ¬ Subgroup.centralizer (W : Set G) ≤ M := fun hle => hLM (hLW.trans hle)
  have hWΓ : W ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hWV hW1 hWM (by omega)
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    B2F.le_normalizer_inf h.normal (B2F.le_normalizer_centralizer hTY)
  exact hWM (e6_13 h311 h hWV hW1 hWΓ.2.2.2 hTW)

end Orbit

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_three_of_alt {L : Subgroup G} (hs : IsShort2 L)
    (ha : IsAltType L 3 ∨ IsAltType L 5) :
    ∃ x ∈ L, x ^ 3 = 1 ∧ x ≠ 1 ∧ x ∉ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases ha with h3 | h5
  · obtain ⟨-, hU4, -, -, -, -, c, hcL, hc3, -, hcu, -⟩ := hs.alt3_structure h3
    obtain ⟨u, huU, hu1⟩ : ∃ u ∈ blockU L, u ≠ 1 := by
      by_contra hall
      push Not at hall
      have : blockU L = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
      rw [this, Subgroup.card_bot] at hU4
      omega
    have huL : u ∈ L := (C1.blockU_le_blockQ hs).trans (C1.blockQ_le L) huU
    refine ⟨c, hcL, hc3 ▸ pow_orderOf_eq_one c, ?_, ?_⟩
    · intro h1
      rw [h1, orderOf_one] at hc3
      omega
    · intro hcC
      apply hcu u huU hu1
      have h1 : u * c = c * u := Subgroup.mem_centralizer_iff.1 hcC u huL
      rw [← h1]
      group
  · obtain ⟨α, hαs, hαk, -⟩ := h5
    have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card]
      decide
    have hdvd : 60 ∣ Nat.card L := by
      have h1 := Subgroup.card_range_dvd α
      rw [MonoidHom.range_eq_top.2 hαs, Subgroup.card_top, hcardA] at h1
      exact h1
    obtain ⟨⟨x, hxL⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3
      (dvd_trans (by norm_num) hdvd)
    have hx' : orderOf x = 3 := by rwa [Subgroup.orderOf_mk] at hx
    have hx3 : x ^ 3 = 1 := hx' ▸ pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx'
      omega
    refine ⟨x, hxL, hx3, hx1, fun hxC => ?_⟩
    have hαx : α ⟨x, hxL⟩ ≠ 1 := by
      intro h1
      have hker : (⟨x, hxL⟩ : L) ∈ CFSG.pCore 2 L := by
        rw [← hαk]
        exact h1
      have h2 : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2) ⟨⟨x, hxL⟩, hker⟩
      rw [Subgroup.orderOf_mk, hx] at hk
      have h3 : (3 : ℕ) ∣ 2 ^ k := hk ▸ dvd_refl 3
      have h4 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      omega
    apply hαx
    have hcen : α ⟨x, hxL⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro σ
      obtain ⟨l, rfl⟩ := hαs σ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC l l.2)
    rw [alternatingGroup.center_eq_bot (by simp)] at hcen
    exact hcen

theorem e623_of (h311 : Theorem311Stmt) (h622 : E622Stmt)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hA3 : E623A3Dichotomy) (hA5 : E623A5Dichotomy) : E623Stmt := by
  intro G _ _ T M V hV h hm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hr
  push Not at hr
  have hr1 : E3.rParam V = 1 := le_antisymm hr (one_le_rParam h)
  have h15 : HypE615 hV M := Or.inr hm
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr1).2
  obtain ⟨U, hUV, hUC, hUr⟩ := exists_eq_rParam' (V := V) (by rw [hr1]; exact ENat.one_ne_top)
  have hU1 : E3.mQuot V U = 1 := by
    rw [hr1] at hUr
    exact_mod_cast hUr
  have hUne : U ≠ ⊥ := by
    rintro rfl
    omega
  have hUM : ¬ Subgroup.centralizer (U : Set G) ≤ M := by
    intro hle
    apply hUC
    have h1 := inf_centralizer_le_normalizer h hUV hUne
    rwa [inf_eq_right.2 hle] at h1
  obtain ⟨-, -, hUΓ⟩ := e6_16_one hV h h15 hUV hU1 hUM
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hH : CharTwo H := h622 G T M V U hV h h15 hUV hU1
  have hQsyl : IsSylowTwoOf Q H := e6_5_one h hUΓ
  have hcgs : cgsIn H Q ≤ H ⊓ M := (e6_5_two h hUΓ).1
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hH
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQsyl.1.trans h1)
  have hsq : IsSQTKIn H :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 G H Q (H ⊓ M) hsq hH hQsyl hcgs inf_le_left
  obtain ⟨i, hiM⟩ : ∃ i, ¬ Lb i ≤ M := by
    by_contra hall
    push Not at hall
    apply hUM
    intro x hx
    obtain ⟨m, hm', y, hy, rfl⟩ := hprod x hx
    refine M.mul_mem hm'.2 (Subgroup.list_prod_mem (K := M) fun z hz => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
    exact hall j (hy j)
  set L := Lb i with hLdef
  have hLblock : IsBlock2 H L := (hLb i).1.1
  have hLH : L ≤ H := hLblock.2.1
  have hKN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hUΓ).2
  have hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 := by
    have hUC' : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun l hl => (Subgroup.mem_centralizer_iff.1 (hLH hl) u hu).symm
    have hUi : U.relIndex V = 2 := by
      have := E3.relIndex_eq_two_pow h.isPGroup_V U
      rw [hU1, pow_one] at this
      exact this
    rw [← hUi]
    exact Subgroup.relIndex_le_of_le_left hUC' (by rw [hUi]; norm_num)
  rcases (hLb i).1.2 with ⟨n, hn, hlin⟩ | h3 | h5
  ·
    apply hiM
    have hc := centralizes_of_lin2_block h.isElemAbelian h.le hQsyl
      (inf_le_left.trans h.inM.2) hKN hH hLblock hn hlin (hLb i).2.1 hidx
    intro l hl
    exact h.centralizer_le (Subgroup.mem_centralizer_iff.2 fun v hv => hc v hv l hl)
  · have hd := hA3 G T M V U L hV h hm hr1 hUV hU1 hUM hH (hLb i).1 h3 hiM
    obtain ⟨x, hxL, hx3, hx1, hxC⟩ := exists_three_of_alt hLblock.1 (Or.inl h3)
    exact false_of_dichotomy h311 hV h hm h6 hUV hU1 hLH hiM hd Nat.prime_three (by norm_num)
      hxL hx3 hx1 hxC
  · have hd := hA5 G T M V U L hV h hm hr1 hUV hU1 hUM hH (hLb i).1 h5 hiM
    obtain ⟨x, hxL, hx3, hx1, hxC⟩ := exists_three_of_alt hLblock.1 (Or.inr h5)
    exact false_of_dichotomy h311 hV h hm h6 hUV hU1 hLH hiM hd Nat.prime_three (by norm_num)
      hxL hx3 hx1 hxC

end Main

end E6

end CFSG.Quasithin
