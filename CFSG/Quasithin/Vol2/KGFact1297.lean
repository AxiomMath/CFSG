module

public import CFSG.Quasithin.Vol2.KGFact1297A7
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7In

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace KG1297

open KG1296

variable {G : Type} [Group G]

theorem nonabelian_of_center {M : Type*} [Group M] [Nontrivial M]
    (h : Subgroup.center M = ⊥) : ∃ a b : M, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  have : x ∈ Subgroup.center M := Subgroup.mem_center_iff.2 fun g => hcon g x
  rw [h, Subgroup.mem_bot] at this
  exact hx this

theorem of_equiv [Finite G] {X K S B Y : Subgroup G} {m : ℕ} {M : Type} [Group M] [Finite M]
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M) (hs : IsSimpleGroup M) (hZ : Subgroup.center M = ⊥)
    (hInn : InnClosed ((barOf K B).map e.toMonoidHom))
    (hLat : LatHyp ((barOf K B).map e.toMonoidHom) m) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S X)
    (hKS : K ⊔ S = X) (hBK : B ≤ K) (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hinn : ∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B)
    (hSY : S ≤ Y) (hYX : Y ≤ X) (hYB : ¬ Y ≤ B ⊔ S) (hY3 : CFSG.Open.pRank 3 Y ≤ 1)
    (hidx : (B ⊓ Y).relIndex B = 2 ^ m - 1) : LatOut B Y m := by
  have hs' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := e.isSimpleGroup
  have hZ' := center_eq_bot_of_mulEquiv e hZ
  have hBB : ((barOf K B).map e.toMonoidHom).map e.symm.toMonoidHom = barOf K B := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (barOf K B)
    ext x
    simp
  have hInn' : InnClosed (barOf K B) := by
    have := innClosed_map e.symm hInn
    rwa [hBB] at this
  exact reduction hKX hXN hS hKS hBK hSB hinn hSY hYX hYB hY3 hidx hs'
    (nonabelian_of_center hZ') hZ' hInn' (LatHyp.of_map e hLat)

end KG1297

open KG1296 KG1297 in
theorem latticeFact1297_holds :
    LatticeFact1297 := by
  intro G _ _ X K S B Y hKX hXN hS hKS hiso hBK hSB hinn hcases hSY hYX hYB hY3 _
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
  have hA7s : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hA7Z : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  have hSL4 := CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (K := ZMod 2)
    (Nat.card_zmod 2) (m := 4) (by norm_num)
  have hSL5 := CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (K := ZMod 2)
    (Nat.card_zmod 2) (m := 5) (by norm_num)
  rcases hcases with ⟨⟨e3⟩, hidx, ht⟩ | ⟨⟨e4⟩, hidx⟩
  ·
    have hidx' : (B ⊓ Y).relIndex B = 2 ^ 3 - 1 := hidx
    have hout : LatOut B Y 3 := by
      rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      ·
        obtain ⟨-, ⟨e'⟩⟩ := key e
        have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
            Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := ⟨e'.symm.trans e3⟩
        exact of_equiv e hA7s hA7Z (innClosed_A7 hB') (latHyp_A7 hB') hKX hXN hS hKS hBK hSB
          hinn hSY hYX hYB hY3 hidx'
      ·
        obtain ⟨⟨T', hT'⟩, ⟨e'⟩⟩ := key e
        have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
            Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := ⟨e'.symm.trans e3⟩
        exact of_equiv e hSL4 CFSG.Quasithin.SLnTwo.center_eq_bot
          (of_SL (k := 3) (Or.inl rfl) T' hT' hB' 3).1 (latHyp_four hB') hKX hXN hS hKS hBK
          hSB hinn hSY hYX hYB hY3 hidx'
      ·
        obtain ⟨φ, hφ⟩ := ht ⟨e⟩
        have hφ' : (barOf K B).map φ.toMonoidHom = Ct := hφ
        exact of_equiv φ hSL5 CFSG.Quasithin.SLnTwo.center_eq_bot (hφ' ▸ innClosed_Ct)
          (hφ' ▸ latHyp_Ct) hKX hXN hS hKS hBK hSB hinn hSY hYX hYB hY3 hidx'
    obtain ⟨-, hY', hBY, hmax⟩ := hout
    exact ⟨⟨e3⟩, hY', hBY, hmax⟩
  ·
    exfalso
    have hidx' : (B ⊓ Y).relIndex B = 2 ^ 4 - 1 := hidx
    have hout : LatOut B Y 4 := by
      rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      ·
        obtain ⟨-, ⟨e'⟩⟩ := key e
        exact (not_modO2_SL4_of_A7 ⟨e'.symm.trans e4⟩).elim
      ·
        obtain ⟨-, ⟨e'⟩⟩ := key e
        have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
            Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := ⟨e'.symm.trans e4⟩
        have htop := eq_top_of_modO2_SL4 hB'
        exact of_equiv e hSL4 CFSG.Quasithin.SLnTwo.center_eq_bot
          (by rw [htop]; exact (of_top pCoreOf_top_SL4 4).1) (latHyp_four_top hB') hKX hXN hS
          hKS hBK hSB hinn hSY hYX hYB hY3 hidx'
      ·
        obtain ⟨⟨T', hT'⟩, ⟨e'⟩⟩ := key e
        have hB' : Nonempty (ModO2 ((barOf K B).map e.toMonoidHom) ≃*
            Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := ⟨e'.symm.trans e4⟩
        exact of_equiv e hSL5 CFSG.Quasithin.SLnTwo.center_eq_bot
          (of_SL (k := 4) (Or.inr rfl) T' hT' hB' 4).1 (latHyp_five hB') hKX hXN hS hKS hBK
          hSB hinn hSY hYX hYB hY3 hidx'
    exact absurd hout.1 (by norm_num)

end CFSG.Quasithin.H13
