module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UFF1
public import CFSG.Quasithin.Vol2.Ch11SecSFF
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem autOn_sup {K T V : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))
    (hT : T ≤ Subgroup.normalizer (V : Set G)) : autOn (K ⊔ T) V = autOn K V ⊔ autOn T V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hK hT

theorem normal_autOn_subgroupOf {K T V : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ((autOn K V).subgroupOf (autOn (K ⊔ T) V)).Normal := by
  have hKT : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  refine ⟨fun a ha b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  obtain ⟨y, hy, hya⟩ := ha
  obtain ⟨x, hx, hxb⟩ := (b : ↥(autOn (K ⊔ T) V)).2
  refine ⟨x * y * x⁻¹, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hKT hx) _).mp hy
    simpa using this
  · simp only [map_mul, map_inv, hya, hxb]
    rfl

theorem false_of_autOn_sup_simple {Kp T V : Subgroup G}
    (hKpN : Kp ≤ Subgroup.normalizer (V : Set G)) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hTK : T ≤ Subgroup.normalizer (Kp : Set G))
    (hT2 : IsPGroup 2 T) {S : Type} [Group S] [IsSimpleGroup S] (hS2 : ¬ IsPGroup 2 S)
    (e : ↥(autOn (Kp ⊔ T) V) ≃* S)
    (hcont : ∀ g : ↥Kp →* S, Function.Surjective g → False) : False := by
  have hle : autOn Kp V ≤ autOn (Kp ⊔ T) V := Subgroup.map_mono fun x hx => le_sup_left (a := Kp) hx
  have hn := normal_autOn_subgroupOf (V := V) hTK
  have hmap : (((autOn Kp V).subgroupOf (autOn (Kp ⊔ T) V)).map e.toMonoidHom).Normal :=
    hn.map e.toMonoidHom e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((autOn Kp V).subgroupOf (autOn (Kp ⊔ T) V)).map e.toMonoidHom) with h | h
  ·
    have h1 : (autOn Kp V).subgroupOf (autOn (Kp ⊔ T) V) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
    have h2 : autOn Kp V = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have : (⟨a, hle ha⟩ : ↥(autOn (Kp ⊔ T) V)) ∈ (autOn Kp V).subgroupOf (autOn (Kp ⊔ T) V) :=
        ha
      rw [h1, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have h3 : autOn (Kp ⊔ T) V = autOn T V := by rw [autOn_sup hKpN hTN, h2, bot_sup_eq]
    apply hS2
    have hT' : IsPGroup 2 ↥(autOn T V) :=
      (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map _
    rw [← h3] at hT'
    exact hT'.of_equiv e
  ·
    have h1 : autOn (Kp ⊔ T) V ≤ autOn Kp V := by
      intro b hb
      have hx : e ⟨b, hb⟩ ∈ ((autOn Kp V).subgroupOf (autOn (Kp ⊔ T) V)).map e.toMonoidHom := by
        rw [h]; trivial
      obtain ⟨y, hy, hye⟩ := hx
      have : y = ⟨b, hb⟩ := e.injective hye
      rw [this, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      exact hy
    have heq : autOn Kp V = autOn (Kp ⊔ T) V := le_antisymm hle h1
    obtain ⟨f₀, hf₀⟩ := exists_autOn_surjective hKpN
    exact hcont (e.toMonoidHom.comp ((MulEquiv.subgroupCongr heq).toMonoidHom.comp f₀))
      (e.surjective.comp ((MulEquiv.subgroupCongr heq).surjective.comp hf₀))


theorem not_isPGroup_two_of_three_dvd {S : Type} [Group S] [Finite S] (h : 3 ∣ Nat.card S) :
    ¬ IsPGroup 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hS
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
  rw [hn] at h
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)

theorem three_dvd_card_SL_zmod_two {n : ℕ} (hn : n = 4 ∨ n = 5) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), Nat.card_zmod]
  rcases hn with rfl | rfl <;> decide

section FF

variable [Finite G]

theorem u3_false_of_concl701FF
    (h325 : H13.Stmt3_2_5) (h328 : H13.Stmt3_2_8)
    (hG2 : FactG2Simple) {T Kp Ip : Subgroup G} (hfsu : H13.FSU G T Kp Ip)
    (hTK : T ≤ Subgroup.normalizer (Kp : Set G))
    (hVN : Kp ⊔ T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G))
    [IsMulCommutative ↥(H13.fsuV T Ip)] [Group.IsPerfect ↥Kp] {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup ↥Kp} [N.Normal]
    (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ N)) (ψ : ↥Kp →* Y)
    (hψ : Function.Surjective ψ) {k : ℕ} (hk : 2 ≤ k) (hU : IsPSU 3 2 k Y)
    (hFF : H13.Concl701FF T Kp Ip) : False := by
  have hKpN : Kp ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G) := le_sup_left.trans hVN
  have hTN : T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G) := le_sup_right.trans hVN
  obtain ⟨f₀, hf₀⟩ := exists_autOn_surjective hKpN
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have hpos : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n → 1 ≤ n := by
    intro K _ _ n hK
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hK
      exact absurd hK Finite.one_lt_card.ne'
    · exact h0
  have hZ2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hSL : ∀ {K : Type} [Field K] [Finite K] {m n : ℕ}, 2 ≤ m → (3 ≤ m ∨ 2 ≤ n) →
      Nat.card K = 2 ^ n →
      Nonempty (↥(autOn Kp (H13.fsuV T Ip)) ≃* Matrix.SpecialLinearGroup (Fin m) K) → False :=
    fun hm hmn hK ⟨e⟩ => u3_false_of_SL hY hN hQ ψ hψ hk hU hm (hpos hK) hmn hK
      (e.toMonoidHom.comp f₀) (e.surjective.comp hf₀)
  have hAlt : ∀ {m : ℕ}, 5 ≤ m → m ≤ 8 →
      Nonempty (↥(autOn Kp (H13.fsuV T Ip)) ≃* alternatingGroup (Fin m)) → False :=
    fun hm5 hm8 ⟨e⟩ => u3_false_of_alt hY hN hQ ψ hψ hk hU (e.toMonoidHom.comp f₀)
      (e.surjective.comp hf₀) hm5 hm8 (MulEquiv.refl _)
  have hSp : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n →
      Nonempty (↥(autOn Kp (H13.fsuV T Ip)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K)) →
        False :=
    fun hK ⟨e⟩ => u3_false_of_statedSp hY hN hQ ψ hψ hk hU hK (e.toMonoidHom.comp f₀)
      (e.surjective.comp hf₀)
  rcases SecS.concl701FF_list h325 h328 hfsu hTK hFF with hl | ⟨-, ht⟩
  · rcases hl with ⟨n, K, _, _, hK, he⟩ | ⟨n, K, _, _, hK, he⟩ | he | he | he | he
    · exact hSL (by norm_num) (Or.inl le_rfl) hK he
    · exact hSp hK he
    · exact hAlt (by norm_num) (by norm_num) he
    · exact hSL (by norm_num) (Or.inl (by norm_num)) hZ2 he
    · exact hSL (by norm_num) (Or.inl (by norm_num)) hZ2 he
    · exact hAlt (by norm_num) (by norm_num) he
  · rcases ht with ⟨n, hL⟩ | ⟨n, K, _, _, hK, he⟩ | he | ⟨n, K, _, _, hK, he⟩ |
        ⟨n, K, _, _, hK, he⟩ | he | he | he | he | ⟨-, -, he⟩ | ⟨n, hn, he⟩ | he
    ·
      rcases hL with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hc).1 rfl
        obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
        have : CharP K 2 := KGNat.charP_two_of_card (by have := hpos hK; omega) hK
        have ε : ↥(autOn Kp (H13.fsuV T Ip)) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
          (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
            K).symm).trans ((QuotientGroup.quotientMulEquivOfEq KGNat.center_SL2_eq_bot).trans
              QuotientGroup.quotientBot)
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · obtain rfl : n = 1 := by have := hpos hK; omega
          refine u3_false_of_card_le hY hN hQ ψ hψ hk hU (ε.toMonoidHom.comp f₀)
            (ε.surjective.comp hf₀) ?_ ?_ <;>
            rw [← Nat.card_congr ε.toEquiv, hcard] <;> decide
        · exact hSL le_rfl (Or.inr hn2) hK ⟨ε⟩
      all_goals exact absurd h (by norm_num)
    · exact hSL (by norm_num) (Or.inl le_rfl) hK he
    · exact hSL (by norm_num) (Or.inl le_rfl) hZ2 he
    · exact hSp hK he
    · obtain ⟨e⟩ := he
      exact u3_false_of_G2 hY hN hQ ψ hψ hk hU hG2 hK (e.toMonoidHom.comp f₀)
        (e.surjective.comp hf₀)
    · exact hAlt (by norm_num) (by norm_num) he
    · exact hAlt (by norm_num) (by norm_num) he
    · exact hAlt (by norm_num) (by norm_num) he
    ·
      obtain ⟨e⟩ := he
      have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
      exact false_of_autOn_sup_simple hKpN hTN hTK hT2
        (not_isPGroup_two_of_three_dvd (by rw [card_alt (n := 7) (by norm_num)]; decide)) e
        fun g hg => u3_false_of_alt hY hN hQ ψ hψ hk hU g hg (by norm_num) (by norm_num)
          (MulEquiv.refl _)
    ·
      obtain ⟨e⟩ := he
      exact u3_false_of_alt hY hN hQ ψ hψ hk hU
        ((e.toMonoidHom.comp (QuotientGroup.mk' _)).comp f₀)
        ((e.surjective.comp (QuotientGroup.mk'_surjective _)).comp hf₀) (m := 6) (by norm_num)
        (by norm_num) (MulEquiv.refl _)
    ·
      obtain ⟨e⟩ := he
      have hn3 : 3 ≤ n := by omega
      have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
        SecA.isSimpleGroup_SL_zmod_two hn3
      exact false_of_autOn_sup_simple hKpN hTN hTK hT2
        (not_isPGroup_two_of_three_dvd (three_dvd_card_SL_zmod_two hn)) e
        fun g hg => u3_false_of_SL hY hN hQ ψ hψ hk hU (by omega) le_rfl (Or.inl hn3) hZ2 g hg
    · exact hSL (by norm_num) (Or.inl (by norm_num)) hZ2 he

end FF

end CFSG.Quasithin.Vol2.Ch11.SecB
