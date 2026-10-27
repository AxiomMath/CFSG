module

public import CFSG.Quasithin.Vol2.KGFact1296Cl
public import CFSG.Quasithin.Vol2.KGFact1296A7
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace KG1296

theorem of_map {M M' : Type*} [Group M] [Group M'] (e : M ≃* M') {B : Subgroup M} {m : ℕ}
    (h : InnClosed (B.map e.toMonoidHom) ∧ ParConclusion (B.map e.toMonoidHom) m) :
    InnClosed B ∧ ParConclusion B m := by
  have hB : (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id B
    ext x
    simp
  rw [← hB]
  exact ⟨innClosed_map e.symm h.1, parConclusion_map e.symm h.2⟩

theorem of_top {M : Type*} [Group M] (h : pCoreOf 2 (⊤ : Subgroup M) = ⊥) (m : ℕ) :
    InnClosed (⊤ : Subgroup M) ∧ ParConclusion (⊤ : Subgroup M) m := by
  refine ⟨fun α _ h2 => ⟨1, Subgroup.mem_top _, ?_⟩, fun Q hQ _ hQbot => ?_⟩
  · rw [map_one]
    refine MulEquiv.ext fun x => ?_
    have := h2 x (Subgroup.mem_top x)
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  · rw [h] at hQ
    exact absurd (eq_bot_iff.2 hQ) hQbot

theorem of_SL {k : ℕ} (hk : k = 3 ∨ k = 4)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin (k + 1)) (ZMod 2))}
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin (k + 1)) (ZMod 2)))
    (hT : (T : Subgroup (Matrix.SpecialLinearGroup (Fin (k + 1)) (ZMod 2))) ≤
      Subgroup.normalizer (B : Set (Matrix.SpecialLinearGroup (Fin (k + 1)) (ZMod 2))))
    (hB : Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) (m : ℕ) :
    InnClosed B ∧ ParConclusion B m := by
  obtain ⟨ι, rfl⟩ := exists_mulAut_Pone hk T hT hB
  exact ⟨innClosed_map ι (innClosed_Pone (by omega)),
    parConclusion_map ι (parConclusion_Pone (by omega) m)⟩

theorem pCoreOf_top_SL4 :
    pCoreOf 2 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (pCoreOf 2 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))).Normal :=
    Subgroup.normalizer_eq_top_iff.1
      (eq_top_iff.2 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  exact CFSG.Quasithin.H13.KGH91.NatCoord.eq_bot_of_normal_isPGroup (n := 4) (by norm_num)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem eq_top_of_modO2_SL4 {B : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))}
    (hB : Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) : B = ⊤ := by
  obtain ⟨e⟩ := hB
  refine Subgroup.eq_top_of_le_card _ ?_
  have hcard : Nat.card B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hpos : 0 < Nat.card (CFSG.pCore 2 ↥B) := Nat.card_pos
  rw [hcard, Nat.card_congr e.toEquiv]
  exact Nat.le_mul_of_pos_right _ hpos

end KG1296

open KG1296 in
theorem parabolicFact1296_holds : ParabolicFact1296 := by
  intro G _ _ X K S B Q hKX hXN hS hKS hiso hBK hSB hinn hcases hQlt hQN hD hXQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_sylow_normalizing hKX hXN hS hSB
  obtain ⟨eB⟩ := nonempty_modO2_barOf (K := K) hBK
  have key : ∀ {M : Type} [Group M] (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M),
      (∃ T' : Sylow 2 M, (T' : Subgroup M) ≤
        Subgroup.normalizer (((barOf K B).map e.toMonoidHom : Subgroup M) : Set M)) ∧
      Nonempty (ModO2 B ≃* ModO2 ((barOf K B).map e.toMonoidHom)) := by
    intro M _ e
    have hsurj : Function.Surjective (e.toMonoidHom : (↥K ⧸ CFSG.pCore 2 ↥K) → M) := e.surjective
    refine ⟨⟨T.mapSurjective hsurj, ?_⟩, ?_⟩
    · rw [Sylow.coe_mapSurjective hsurj T]
      exact map_le_normalizer_map e hT
    · obtain ⟨e'⟩ := nonempty_modO2_map e (barOf K B)
      exact ⟨eB.trans e'⟩
  rcases hcases with ⟨⟨e3⟩, hcard3, ht⟩ | ⟨⟨e4⟩, hcard4⟩
  · have h : Hyp1296 X K S B Q 3 :=
      ⟨hKX, hXN, hS, hKS, hBK, hSB, hinn, hcard3, hQlt, hQN, hD, hXQ⟩
    rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    ·
      obtain ⟨-, ⟨e'⟩⟩ := key e
      have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := ⟨e'.symm.trans e3⟩
      obtain ⟨h1, h2⟩ := of_map e ⟨innClosed_A7 hB', parConclusion_A7 hB' 3⟩
      exact reduction h (center_eq_bot_of_mulEquiv e
        (alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num))) h1 h2
    ·
      obtain ⟨⟨T', hT'⟩, ⟨e'⟩⟩ := key e
      obtain ⟨h1, h2⟩ := of_map e (of_SL (k := 3) (Or.inl rfl) T' hT' ⟨e'.symm.trans e3⟩ 3)
      exact reduction h (center_eq_bot_of_mulEquiv e CFSG.Quasithin.SLnTwo.center_eq_bot) h1 h2
    ·
      obtain ⟨φ, hφ⟩ := ht ⟨e⟩
      have hφ' : (barOf K B).map φ.toMonoidHom = Ct := hφ
      obtain ⟨h1, h2⟩ := of_map φ (by rw [hφ']; exact ⟨innClosed_Ct, parConclusion_Ct⟩)
      exact reduction h (center_eq_bot_of_mulEquiv φ CFSG.Quasithin.SLnTwo.center_eq_bot) h1 h2
  · have h : Hyp1296 X K S B Q 4 :=
      ⟨hKX, hXN, hS, hKS, hBK, hSB, hinn, hcard4, hQlt, hQN, hD, hXQ⟩
    rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    ·
      obtain ⟨-, ⟨e'⟩⟩ := key e
      exact absurd ⟨e'.symm.trans e4⟩ not_modO2_SL4_of_A7
    ·
      obtain ⟨-, ⟨e'⟩⟩ := key e
      have htop := eq_top_of_modO2_SL4 ⟨e'.symm.trans e4⟩
      obtain ⟨h1, h2⟩ := of_map e (by rw [htop]; exact of_top pCoreOf_top_SL4 4)
      exact reduction h (center_eq_bot_of_mulEquiv e CFSG.Quasithin.SLnTwo.center_eq_bot) h1 h2
    ·
      obtain ⟨⟨T', hT'⟩, ⟨e'⟩⟩ := key e
      obtain ⟨h1, h2⟩ := of_map e (of_SL (k := 4) (Or.inr rfl) T' hT' ⟨e'.symm.trans e4⟩ 4)
      exact reduction h (center_eq_bot_of_mulEquiv e CFSG.Quasithin.SLnTwo.center_eq_bot) h1 h2

end CFSG.Quasithin.H13
