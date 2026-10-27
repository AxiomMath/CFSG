module

public import CFSG.Quasithin.Background.S1549DBr
public import CFSG.Quasithin.Background.S1549DL3M

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C
open scoped commutatorElement Pointwise

theorem _root_.CFSG.Quasithin.S1549C.input49L3_of
    (h113 : StageLemma14113) (hB51 : AsB51) : S1549C.Input49L3 := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od L e hiso
  rintro ⟨A, hA, hAle⟩
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
  have hY0H : Y0 T Mc M ≤ H := le_sup_left.trans hb.adm.hY0
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
  have hQT : pCoreOf 2 H ≤ T := IsSylowTwoOf.pCoreOf_le h.sylow_H
  have hTMH : T ≤ M ⊓ H := le_inf cx.c.hyp.T_le hTH
  have hY0M : Y0 T Mc M ≤ M :=
    (Y0_le T Mc M).trans (inf_le_left.trans (Y153_le Mc M))
  have hc168 : Nat.card ↥(StarOf T M V₁ H L) = 168 := by
    obtain ⟨eL⟩ := hiso
    exact card_of_equiv_statedSL3 eL
  have hiso' : Nonempty (↥(starOfSub h L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) := by
    rw [← starOf_eq_starOfSub cx hb hLH]
    exact hiso
  obtain ⟨eL⟩ := hiso'
  have hLq : CFSG.IsQuasisimple ↥(starOfSub h L) := isQuasisimple_of_equiv_statedSL3 eL
  have hLs : SQTKGroup ↥(starOfSub h L) := sqtkGroup_starOfSub cx hb hLH
  have hLc : Nat.card ↥(starOfSub h L) = 168 := card_of_equiv_statedSL3 eL
  have hLX : starOfSub h L ≤ starOfSub h H := starOfSub_mono h hLH
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
  obtain ⟨a, haS, haZ⟩ := exists_zvec cx.c
  have hzS : ∀ s ∈ starOfSub h T, s (vecOf h a (le_conjClosure _ _ haS)) =
      vecOf h a (le_conjClosure _ _ haS) := by
    intro s hs
    obtain ⟨x, hxT, rfl⟩ := (mem_starOfSub h).mp hs
    exact starHom_T_zvec cx.c h haS hxT
  have hgen : Subgroup.closure {v | ∃ g ∈ starOfSub h H,
      g (vecOf h a (le_conjClosure _ _ haS)) = v} = ⊤ := by
    have := closure_orbit_zvec cx.c h haS haZ
    rwa [← starOfSub_H h] at this
  have hM : ∀ g ∈ starOfSub h H, g (vecOf h a (le_conjClosure _ _ haS)) =
      vecOf h a (le_conjClosure _ _ haS) → g ∈ starOfSub h (M ⊓ H) := by
    intro g hg hgz
    obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp hg
    exact (mem_starOfSub h).mpr ⟨x, ⟨mem_M_of_fix_zvec cx.c cx.r46 h haS haZ hgz, x.2⟩, rfl⟩
  have hP₀L : starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ≤ starOfSub h L :=
    starOfSub_mono h (sup_le hY0L inf_le_right)
  have hpar : IsMinParabolicOf (starOfSub h L) (starOfSub h (Y0 T Mc M ⊔ (T ⊓ L))) := by
    rcases e.l.par with h7 | hhat | hmp
    · exfalso
      obtain ⟨e7⟩ := h7
      have h1 := Nat.card_congr e7.toEquiv
      rw [hc168, card_alternatingGroup1527d 7 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · exfalso
      have h1 := card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        norm_num [Nat.factorial])
      omega
    · rwa [starOf_eq_starOfSub cx hb hLH,
        starOf_eq_starOfSub cx hb (sup_le hY0H (inf_le_left.trans hTH))] at hmp
  have hSL : starOfSub h T ⊓ starOfSub h L ≤ starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) :=
    (starOfSub_inf_le h hQT).trans (starOfSub_mono h le_sup_right)
  have hPM : starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ⊔ starOfSub h T ≤ starOfSub h (M ⊓ H) :=
    sup_le (starOfSub_mono h (sup_le (le_inf hY0M hY0H) (inf_le_left.trans hTMH)))
      (starOfSub_mono h hTMH)
  have hPS : starOfSub h (Y0 T Mc M ⊔ T) =
      starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ⊔ starOfSub h T := by
    rw [← starOfSub_sup h (sup_le hY0H (inf_le_left.trans hTH)) hTH]
    congr 1
    exact le_antisymm (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
      (sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right)
  have hAP : A ≤ pCoreOf 2 (starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ⊔ starOfSub h T) := by
    have hle : pCoreOf 2 (Y0 T Mc M ⊔ T) ≤ H := (pCoreOf_le 2 _).trans (sup_le hY0H hTH)
    rw [starOf_eq_starOfSub cx hb hle] at hAle
    rw [← hPS]
    exact hAle.trans (starOfSub_pCoreOf_le h (sup_le hY0H hTH))
  have hres := l3_endgame hB51 hV hLX hLn hLq hLs hLc hS hXLS hO2 hLJ hA' hzS hgen hM hP₀L hpar hSL
    hPM hAP
  exact not_starOfSub_L_le_M h113 cx hb od e.lctx hres

end S1549D

end CFSG.Quasithin
