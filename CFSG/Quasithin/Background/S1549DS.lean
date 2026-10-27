module

public import CFSG.Quasithin.Background.S1549DBr
public import CFSG.Quasithin.Background.S1549DSMod
public import CFSG.Quasithin.Background.S1549DL3N

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C
open scoped commutatorElement Pointwise

theorem isQuasisimple_of_simple_nonab {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hnc : ∃ a b : Y, a * b ≠ b * a) : CFSG.IsQuasisimple Y :=
  isQuasisimple_of_perfect_of_isSimpleGroup (by
    have hc : (commutator Y).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h0 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_def] at this
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
    · exact ⟨h1⟩) hs

theorem list_data
    {Y : Type} [Group Y] [Finite Y]
    (hY : IsHat Y ↥(alternatingGroup (Fin 6)) ∨ IsAlt 7 Y ∨ IsG2TwoDerived Y) :
    CFSG.IsQuasisimple Y ∧ (Nat.card Y = 1080 ∨ Nat.card Y = 2520 ∨ Nat.card Y = 6048) := by
  rcases hY with hhat | h7 | ⟨F, _, _, hF, ⟨eG⟩⟩
  · refine ⟨hhat.1, Or.inl ?_⟩
    exact card_of_isHat1527d hhat (by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial])
  · obtain ⟨e7⟩ := h7
    have hs7 : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
    have hsY : IsSimpleGroup Y := e7.isSimpleGroup
    have hc4 : 4 ≤ Nat.card (Fin 7) := by simp
    obtain ⟨a, b, hab⟩ := FFC.exists_noncomm_of_center_eq_bot (alternatingGroup.center_eq_bot hc4)
    have hnc : ∃ a b : Y, a * b ≠ b * a := by
      refine ⟨e7.symm a, e7.symm b, fun h => hab ?_⟩
      have := congrArg e7 h
      simpa using this
    refine ⟨isQuasisimple_of_simple_nonab hsY hnc, Or.inr (Or.inl ?_)⟩
    rw [Nat.card_congr e7.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
    norm_num [Nat.factorial]
  · obtain ⟨hsD, hncD, -⟩ := FFC.commutator_data_g2 (H := CFSG.Open.quasithinG2 F) hF
      (MulEquiv.refl ↥(CFSG.Open.quasithinG2 F))
    have hsY : IsSimpleGroup Y := eG.isSimpleGroup
    have hnc : ∃ a b : Y, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hncD
      refine ⟨eG.symm a, eG.symm b, fun h => hab ?_⟩
      have := congrArg eG h
      simpa using this
    refine ⟨isQuasisimple_of_simple_nonab hsY hnc, Or.inr (Or.inr ?_)⟩
    rw [Nat.card_congr eG.toEquiv]
    exact card_commutator_quasithinG2_two hF

theorem _root_.CFSG.Quasithin.S1549C.input49S_of
    (hB51 : AsB51) (hB42 : AsB42) : S1549C.Input49S := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od L e hlist
  rintro ⟨A, hA⟩
  classical
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  have hV : ∀ v : UTil T M V₁ H, v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := h.isElemAbelian_tilde.2
      (w : SecQuot (Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G))
        (quasithinOmegaOneCenter T)) w.2
    simpa using this
  have hLH : L ≤ H := (le_of_mem_cComp e.lctx.comp).trans (preStar_le _ _)
  have hTH : T ≤ H := h.T_le_H
  have hY0L : Y0 T Mc M ≤ L := e.k.trans (le_of_eq e.l.eq)
  have hHeq : H = L ⊔ T := by
    calc H = conjClosure L T ⊔ Y0 T Mc M ⊔ T := e.lctx.eq
      _ = L ⊔ Y0 T Mc M ⊔ T := by rw [e.l.eq]
      _ = L ⊔ T := by rw [sup_eq_left.mpr hY0L]
  have hTnL : ∀ y ∈ T, ∀ l' ∈ L, y * l' * y⁻¹ ∈ L := fun y hy l' hl' =>
    e.l.eq ▸ mem_conjClosure hy hl'
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [hHeq]
    refine sup_le Subgroup.le_normalizer ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro l
    exact ⟨fun hl => hTnL x hx l hl, fun hl => by simpa [mul_assoc] using hTnL x⁻¹ (T.inv_mem hx) _ hl⟩
  have hlist' : IsHat ↥(starOfSub h L) ↥(alternatingGroup (Fin 6)) ∨ IsAlt 7 ↥(starOfSub h L) ∨
      IsG2TwoDerived ↥(starOfSub h L) := by
    rw [← starOf_eq_starOfSub cx hb hLH]
    exact hlist
  obtain ⟨hLq, hLc⟩ := list_data hlist'
  have hLs : SQTKGroup ↥(starOfSub h L) := sqtkGroup_starOfSub cx hb hLH
  have hXLS : starOfSub h H ≤ starOfSub h L ⊔ starOfSub h T := by
    rw [congrArg (starOfSub h) hHeq, starOfSub_sup h hLH hTH]
  have hLn : ∀ x ∈ starOfSub h H, ∀ l ∈ starOfSub h L, x * l * x⁻¹ ∈ starOfSub h L := by
    intro x hx l hl
    obtain ⟨x', -, rfl⟩ := (mem_starOfSub h).mp hx
    obtain ⟨l', hl'L, rfl⟩ := (mem_starOfSub h).mp hl
    refine (mem_starOfSub h).mpr ⟨x' * l' * x'⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hHL x'.2) (l' : G)).mp hl'L
    simpa using this
  have hS : IsSylowTwoOf (starOfSub h T) (starOfSub h H) := by
    rw [starOfSub_H h]
    exact isSylowTwoOf_starOfSub_T h
  have hO2 : pCoreOf 2 (starOfSub h H) = ⊥ := pCoreOf_starOfSub_H h
  have hLJ := starOfSub_le_ffJ cx hb od e.lctx
  have hA' : IsStrongFFStarOffender (V := UTil T M V₁ H) (starOfSub h H) A := by
    have := hA
    unfold StrongOff at this
    rwa [starOf_eq_starOfSub cx hb le_rfl] at this
  have hN : Nat.card ↥(starOfSub h L) = 1080 ∨ Nat.card ↥(starOfSub h L) = 2520 ∨
      Nat.card ↥(starOfSub h L) = 6048 := hLc
  exact list_no_strong hB51 hB42 hV hLn hLq hLs hN rfl hS hXLS hO2 hLJ hA'

end S1549D

end CFSG.Quasithin
