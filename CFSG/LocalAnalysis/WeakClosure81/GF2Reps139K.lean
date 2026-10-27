module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139C
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Cliff
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139F
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139E
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139G
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenHyp139N3Layer
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.lemmaK (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    (hC : DNormComp G D) {K : Subgroup (MulAut W)} (hK : IsComponentOf K G)
    (hKD : ¬ K ≤ Subgroup.centralizer (D : Set (MulAut W))) :
    (∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K) ∧ KXIrr K X ⊤ := by
  classical
  obtain ⟨hcommK, hfixK⟩ := Std139.lemmaG hw2 S hn hC hK hKD
  obtain ⟨-, -, -, -, hfixX, -⟩ := Std139.exists_gen hw2 S
  have hF := Std139.lemmaF hw2 S hn hC hK hKD
  have hirrTop : KXIrr K X ⊤ := by
    simpa [hcommK] using hF.2.2.2.2
  refine ⟨?_, hirrTop⟩
  intro g hg
  by_contra hneMap
  set K' : Subgroup (MulAut W) := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hne : K' ≠ K := by simpa [hK'def] using hneMap
  have hK'comp : IsComponentOf K' G :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK hg
  have hcommKK' : ⁅K, K'⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hK hK'comp (Ne.symm hne)
  have hcommXK' : ⁅X, K'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    exact S.component_commutes_X hK'comp k' hk' x hx
  have hMR : ⁅K ⊔ X, K'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommKK')
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommXK')
  have hRK' : ⁅K', K'⁆ = K' := by
    have hq := hK'comp.2.2.1
    have hmap := Subgroup.map_subtype_commutator K'
    rw [hq, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have hfixSup : fixV (K ⊔ X) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwX : w ∈ fixV X := fun x hx => hw x (Subgroup.mem_sup_right hx)
    rwa [hfixX] at hwX
  have hirrSup : IsIrrOn (K ⊔ X) ⊤ (⊤ ⊓ fixV (K ⊔ X)) := by
    rw [hfixSup, inf_bot_eq]
    refine ⟨bot_lt_iff_ne_bot.mpr hirrTop.1, ?_, ?_, ?_⟩
    · intro h _ u _
      exact Subgroup.mem_top u
    · intro h _ u hu
      simpa [Subgroup.mem_bot] using hu
    · intro J hJ _ _
      exact hirrTop.2.2.2 J (fun k hk u hu => hJ k (Subgroup.mem_sup_left hk) u hu)
        (fun x hx u hu => hJ x (Subgroup.mem_sup_right hx) u hu) le_top
  have hWmul : ∀ w : W, w * w = 1 := fun w => by
    rw [← pow_two]
    exact hw2 w
  have hschur := s13_schur_perfect hWmul (K ⊔ X) K' hMR hRK' (⊤ : Subgroup W)
    (fun _ _ _ _ => Subgroup.mem_top _) (fun _ _ _ _ => Subgroup.mem_top _) hirrSup
  have hK'triv : commSub ⊤ K' = ⊥ := by
    simpa [hfixSup] using hschur
  have hfixK' : fixV K' = ⊤ := top_le_iff.mp (commSub_eq_bot_iff.mp hK'triv)
  have hK'bot : K' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    ext w
    have hw : w ∈ fixV K' := by
      rw [hfixK']
      exact Subgroup.mem_top w
    simpa using mem_fixV.mp hw r hr
  haveI hnt : Nontrivial (↥K' ⧸ Subgroup.center ↥K') := hK'comp.2.2.2.toNontrivial
  haveI hsub : Subsingleton (↥K' ⧸ Subgroup.center ↥K') := by
    rw [hK'bot]
    infer_instance
  exact (not_subsingleton (↥K' ⧸ Subgroup.center ↥K')) hsub

theorem Std139.exists_comp139 (h134 : W4Lem13_4) (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) (hn : 3 ≤ n) : ∃ K : Subgroup (MulAut W), Comp139 G X D K := by
  obtain ⟨K, hK, hKD⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.sixfourteen_n3_exists_component_not_centralized hw2
      S.isK S.o2 S.irr S.cost S.XG S.Xnorm S.Xcard S.sG S.s2 S.s_not_cent S.Yinv S.Yrk
      S.card S.DG S.DX S.Dcs S.elem S.Dcard S.YD (by omega)
  have hC : DNormComp G D := Std139.lemmaC h134 hw2 S hn
  have hKnormal := Std139.lemmaK hw2 S hn hC hK hKD
  have hG := Std139.lemmaG hw2 S hn hC hK hKD
  exact ⟨K, hK, hKD, hKnormal.1, hG.1, hG.2, hKnormal.2⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
