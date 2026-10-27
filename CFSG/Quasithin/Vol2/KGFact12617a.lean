module

public import CFSG.Quasithin.Vol2.KGFact12617Lie
public import CFSG.Quasithin.Vol2.KGFact12618f
public import CFSG.Quasithin.Vol2.KGFact12617

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem list_cases {K B : Subgroup Γ} (hKs : IsSimpleGroup ↥K) (hlist : B56QuasisimpleList ↥K)
    (hBK : B < K) (hBB : ⁅B, B⁆ = B)
    (hBiso : Open.quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) :
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(StatedSp 2 F))) ∨
      (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Even n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥K ≃* ↥(Open.quasithinG2 F))) ∨
      IsAlt 7 ↥K ∨ Nonempty (↥K ≃* ↥(StatedSL 4 (ZMod 2))) ∨
      Nonempty (↥K ≃* ↥(StatedSL 5 (ZMod 2))) := by
  classical
  have := hKs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := id hBiso
  have hD := KG12614.dataA6_of φ hφs (by exact hφk)
  obtain ⟨a, ha⟩ := hD.card
  have hBdvd : Nat.card ↥B ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hBK.le
  have h5K : 5 ∣ Nat.card ↥K :=
    (show 5 ∣ Nat.card ↥B by rw [ha]; exact dvd_mul_of_dvd_right (by norm_num) _).trans hBdvd
  have hBne : Nat.card ↥B ≠ Nat.card ↥K := fun h =>
    hBK.ne (Subgroup.eq_of_le_of_card_ge hBK.le h.ge)
  have hBle : Nat.card ↥B ≤ Nat.card ↥K := Nat.le_of_dvd Nat.card_pos hBdvd
  have h1a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hKnc : ∃ x y : ↥K, x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have hB1 : B = ⊥ := by
      rw [← hBB, eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      have := hc ⟨x, hBK.le hx⟩ ⟨y, hBK.le hy⟩
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val this
    rw [hB1, Subgroup.card_bot] at ha
    omega
  have hZK : 1 < Nat.card (Subgroup.center ↥K) → False := by
    intro hZ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · rw [h, Subgroup.card_bot] at hZ
      omega
    · obtain ⟨x, y, hxy⟩ := hKnc
      have hx : x ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.1 hx y).symm
  have hF1 : ∀ (F : Type) [Field F] [Finite F], Nat.card F ≠ 1 := fun F _ _ h => by
    have := Finite.one_lt_card (α := F)
    omega
  rcases hlist with ⟨n, F, _, _, hF, ⟨eK⟩⟩ | ⟨n, F, _, _, hF, ⟨eK⟩⟩ | ⟨n, F, _, _, hF, ⟨eK⟩⟩ |
    ⟨n, F, _, _, hF, ⟨eK⟩⟩ | hA6 | hA7 | hHat | ⟨F, _, _, hF, ⟨eK⟩⟩ | hL4 | hL5
  ·
    have := FFC.charP_two_of_card_pow hF
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    exact (false_of_sq_of_pow_four hBK.le (pow_four_of_mulEquiv eK
      (sq_eq_one_of_pow_four_sl2 h2)) φ hφs).elim
  ·
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact (hF1 F (by rw [hF]; rfl)).elim
      have hZ : Nat.card (Subgroup.center ↥K) = 3 := by
        rw [Nat.card_congr (Subgroup.centerCongr
          (eK.trans (specialLinearGroupEquivStatedSL 3 F).symm)).toEquiv,
          CFSG.RankThree.SubgroupLists.card_center_sl3, hF]
        have h3 : 3 ∣ 2 ^ (m + m) - 1 := by
          have h4 : 2 ^ (m + m) % 3 = 1 := by
            rw [← two_mul, pow_mul, Nat.pow_mod]
            norm_num
          have : 1 ≤ 2 ^ (m + m) := Nat.one_le_two_pow
          omega
        exact Nat.gcd_eq_right h3
      exact (hZK (by omega)).elim
    · obtain ⟨h1, -, h2, h3, -⟩ := not_five_dvd_of_odd hodd
      rw [Nat.card_congr eK.toEquiv, card_statedSL_three1527d, hF] at h5K
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5K with h | h
      · exact (h1 h).elim
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
      · exact (h2 h).elim
      · exact (h3 h).elim
  ·
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact (hF1 F (by rw [hF]; rfl)).elim
      · have hK : Nat.card ↥K = 720 := by
          rw [Nat.card_congr eK.toEquiv,
            CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
          decide
        have hB360 : Nat.card ↥B = 360 := by
          rw [ha, hK] at hBdvd
          rw [ha, hK] at hBne
          rw [ha]
          rcases a with _ | _ | a
          · rfl
          · exact (hBne (by norm_num)).elim
          · have h1 := Nat.le_of_dvd (by norm_num) hBdvd
            have h2 : 4 ≤ 2 ^ (a + 2) := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
            nlinarith
        have hidx : (B.subgroupOf K).index = 2 := by
          have hc := (B.subgroupOf K).card_mul_index
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK.le).toEquiv, hB360, hK] at hc
          omega
        have hn := Subgroup.normal_of_index_eq_two hidx
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf K) with h | h
        · have hB1 : B = ⊥ := by
            have h2 := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
            rwa [inf_eq_left.2 hBK.le] at h2
          rw [hB1, Subgroup.card_bot] at hB360
          omega
        · exact (hBK.ne (le_antisymm hBK.le (Subgroup.subgroupOf_eq_top.1 h))).elim
    · exact Or.inl ⟨n, F, inferInstance, inferInstance, hn, hF, ⟨eK⟩⟩
  ·
    rcases Nat.even_or_odd n with hev | hodd
    · rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · exact (hF1 F (by rw [hF]; rfl)).elim
        · exact absurd hev (by decide)
      · exact Or.inr (Or.inl ⟨n, F, inferInstance, inferInstance, hn, hev, hF, ⟨eK⟩⟩)
    · obtain ⟨-, h6, h2, -, h6'⟩ := not_five_dvd_of_odd hodd
      rw [Nat.card_congr eK.toEquiv, card_quasithinG2_1527d hF, hF] at h5K
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5K with h | h
      · exact (h6 h).elim
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
      · exact (h6' h).elim
      · exact (h2 h).elim
  ·
    obtain ⟨e6⟩ := hA6
    have hK : Nat.card ↥K = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    omega
  ·
    exact Or.inr (Or.inr (Or.inl hA7))
  ·
    exact (hZK (by rw [hHat.2.1]; norm_num)).elim
  ·
    have hG := card_quasithinG2_1527d (n := 1) (by rw [hF]; rfl)
    rw [hF] at hG
    have hd : Nat.card ↥K ∣ 12096 := by
      rw [Nat.card_congr eK.toEquiv]
      refine (Subgroup.card_dvd_of_le (Subgroup.commutator_le.2 fun x hx y hy => ?_)).trans
        (by rw [hG]; norm_num)
      rw [commutatorElement_def]
      exact (Open.quasithinG2 F).mul_mem ((Open.quasithinG2 F).mul_mem
        ((Open.quasithinG2 F).mul_mem hx hy) ((Open.quasithinG2 F).inv_mem hx))
        ((Open.quasithinG2 F).inv_mem hy)
    have := h5K.trans hd
    norm_num at this
  · exact Or.inr (Or.inr (Or.inr (Or.inl hL4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hL5)))

theorem factKv12617_of (hLie : FactKv12617LieFam) (hL52 : FactKv12617L52)
    (hA8 : FactKv12617A8) : FactKv12617 := by
  intro Γ _ _ Y K T T₀ B R hKY hYK hKs hlist hT hYeq hO2 hBK hT₀ hT₀4 hT₀N hBB hBiso hR hRC hT₀R
    hKR
  have hC : Conf12617 Y K T T₀ B R := ⟨hKY, hYK, hKs, hT, hYeq, hO2, hBK, hT₀, hT₀4, hT₀N, hBB,
    hBiso, hR, hRC, hT₀R, hKR⟩
  rcases list_cases hKs hlist hBK hBB hBiso with h | h | hA7 | hL4 | hL5
  · exact (hLie Γ Y K T T₀ B R hC (Or.inl h)).elim
  · exact (hLie Γ Y K T T₀ B R hC (Or.inr h)).elim
  · exact (hR (eq_bot_iff.2 ((a7_branch hYK hKY hKs hA7 hT hYeq hO2 hBK hBiso).2 ▸ hRC))).elim
  · exact hA8 Γ Y K T T₀ B R hC hL4
  · exact (hL52 Γ Y K T T₀ B R hC hL5).elim

end CFSG.Quasithin.H13.KG12618
