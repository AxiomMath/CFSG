module

public import CFSG.Quasithin.Vol2.Ch12Sec9Statements
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Sporadic.J4
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

theorem isQuasisimple_of_isSimpleGroup_of_not_prime {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hp : ¬ (Nat.card Q).Prime) :
    CFSG.IsQuasisimple Q ∧ Subgroup.center Q = ⊥ := by
  have hnab : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := h }
    exact hp IsSimpleGroup.prime_card
  obtain ⟨a, b, hab⟩ := hnab
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab
  refine ⟨⟨?_, ?_, ?_⟩, hZ⟩
  · rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator Q) with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ ∈ _root_.commutator Q := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup
  · refine ⟨QuotientGroup.mk a, QuotientGroup.mk b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hZ,
      Subgroup.mem_bot] at h
    exact inv_mul_eq_one.1 h

variable {G : Type} [Group G] [Finite G]

theorem false_of_modules12_2_2_card (h1222 : Stmt12_2_2) {T K : Subgroup G}
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : QuasithinUnique.quasithinIsQTKECat G) (hsyl : quasithinIsSylowTwo T)
    (hnot : ¬ Alt12_2_2 G) (hKmax : quasithinIsMaximalLocal T K)
    (hKf : quasithinIsFaithfulLocal T K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hN : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∉
      ({168, 20160, 9999360, 60, 360, 2520, 6048} : Finset ℕ)) : False := by
  rcases h1222 G T hs hnab hqtke hsyl with hAlt | h3
  · exact hnot hAlt
  obtain ⟨-, ⟨VK, hVK⟩, hall⟩ := h3 K hKmax hKf hq
  obtain ⟨-, -, -, hc, hmod⟩ := hall VK hVK
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hN
  obtain ⟨h168, h20160, h5, h60, h360, h2520, h6048⟩ := hN
  rcases hmod with ⟨m, hm, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨m, hm5, hm8, ⟨φ, hφ, -⟩, -⟩ | ⟨-, φ, hφ, -⟩ | ⟨hU, -⟩ | ⟨-, hZ3, -, -⟩
  · have h := Nat.card_congr e.toEquiv
    rcases hm with rfl | rfl | rfl
    · rw [card_sl_three_zmod_two] at h
      exact h168 h
    · rw [card_sl_four_zmod_two] at h
      exact h20160 h
    · rw [card_sl_five_zmod_two] at h
      exact h5 h
  · have h := Nat.card_congr e.toEquiv
    rw [card_sl_three_zmod_two] at h
    exact h168 h
  · have h := Nat.card_congr e.toEquiv
    rw [card_sl_five_zmod_two] at h
    exact h5 h
  · have h := card_eq_of_surjective_alternating hq hZ hm5 φ hφ
    interval_cases m <;> rw [nat_card_alternatingGroup] at h <;> norm_num [Nat.factorial] at h
    · exact h60 h
    · exact h360 h
    · exact h2520 h
    · exact h20160 h
  · have h := card_eq_of_surjective_alternating hq hZ (by norm_num) φ hφ
    rw [nat_card_alternatingGroup] at h
    norm_num [Nat.factorial] at h
    exact h2520 h
  · exact h6048 (card_of_lieModel_psu_three_three hU)
  · rw [hZ, Subgroup.card_bot] at hZ3
    omega

theorem lemma12_9_2
    (h1222 : Stmt12_2_2) : Lemma12_9_2 := by
  intro G _ _ T L V n hcx hn4 ⟨K, hKmax, hKf, hK⟩
  have hyp := hcx.hyp.hyp
  rcases hK with he | he | he
  · obtain ⟨e⟩ := he
    have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      CFSG.LieType.Universal.SpecialLinear.isQuasisimple 4 (ZMod 2) (by norm_num)
    exact hcx.select hn4
      ⟨K, hKmax, hKf, CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSL, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    have hsK : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2 e
    have hcK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 244823040 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
    obtain ⟨hq, hZ⟩ := isQuasisimple_of_isSimpleGroup_of_not_prime
      (Q := ↥K ⧸ CFSG.pCore 2 ↥K) (by rw [hcK]; norm_num)
    exact false_of_modules12_2_2_card h1222 hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
      hyp.notAlt hKmax hKf hq hZ (by rw [hcK]; norm_num)
  · obtain ⟨e⟩ := he
    have hsK : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J4.isSimpleGroup_J4 e
    have hcK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 86775571046077562880 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J4.card_J4]
    obtain ⟨hq, hZ⟩ := isQuasisimple_of_isSimpleGroup_of_not_prime
      (Q := ↥K ⧸ CFSG.pCore 2 ↥K) (by
        rw [hcK]
        intro hp
        rcases hp.eq_one_or_self_of_dvd 2 ⟨43387785523038781440, by norm_num⟩ with h | h <;>
          norm_num at h)
    exact false_of_modules12_2_2_card h1222 hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
      hyp.notAlt hKmax hKf hq hZ (by rw [hcK]; norm_num)

end CFSG.Quasithin.H13
