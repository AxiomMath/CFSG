module

public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Mat
public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Rep
public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Line
public import CFSG.LocalAnalysis.StandardType.FS81.N7N0Line
public import CFSG.LocalAnalysis.StandardType.FS81.N6Split
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
public import CFSG.LocalAnalysis.StandardType.FS81.N6All

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem false_of_evenN0_seven {Xg : Subgroup (GL (Fin 8) (ZMod 3))}
    (h : EvenN0MatHyp 7 Xg) : False := by
  obtain ⟨T, hTX, hT⟩ := h.exists_T
  exact false_of_conj_tau0_seven hT hTX h.sub
    (fun A hA hfix => EvenN0MatHyp.comm_of_mem_H hT
      (h.mem_H_of_mulVec_e0 hA (c := 1) (by rw [hfix, one_smul])))
    (fun A hA hcomm =>
      EvenN0MatHyp.eq_zero_or_eq_smul_of_commute_tau0 hT hcomm)
    (fun A hA A' hA' c hc => h.conj_eq_of_mulVec_e0 hT hA hA' hc)
    (EvenN0Line.evenN0MatHyp_hroot (n := 7) (by decide) h)
    (fun A hA h0 => h.wt_two_of_O6 ⟨A, hA, rfl⟩ h0)

theorem Basis3.evenN0MatHyp_xg {G : Type} [Group G] [Finite G] {n : ℕ} (B : Basis3 G (n + 1))
    {b₀ : G} (hb0 : B.b 0 = b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 n)
    (hodd : OddCoreTrivial B.span) (hfus : Fus42 B b₀) :
    EvenN0MatHyp n ((ggAutomizer ⊤ B.span).map B.glHom) where
  norm A hA hcol := by
    obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hA
    have hc : B.matOf φ *ᵥ Pi.single 0 1 = B.matOf φ 0 0 • Pi.single 0 1 := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi
        simp
      · rw [show B.matOf φ i 0 = 0 from hcol i hi, Pi.single_eq_of_ne hi, mul_zero]
    have himg := B.conj_b_of_mulVec_single hg hc
    rw [hb0] at himg
    have hgb : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
      refine mem_normalizer_zpowers_of_conj ?_
      rw [himg]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _
    rw [← hN0]
    exact (B.mem_realized_iff _ _).mpr ⟨φ, ⟨g, hgb, hgN, hg⟩, rfl⟩
  sub M hM := B.exists_xg_of_realized _ (by rw [hN0]; exact hM)
  odd N hNn hNodd := by
    set e := (ggAutomizer ⊤ B.span).equivMapOfInjective B.glHom B.glHom_injective with he
    have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    have h := hodd (N.map e.symm.toMonoidHom) (hNn.map _ e.symm.surjective)
      (by rwa [Subgroup.card_map_of_injective hinj])
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h
  moves := by
    obtain ⟨x, hx, i, hi, hxi⟩ := B.exists_xg_moves_e0 hb0 hfus
    refine ⟨x, hx, i, hi, ?_⟩
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at hxi

theorem l1N7N0_holds : L1N7N0 := fun _ _ _ _ _ _ _ B hB _ hfus hodd hN0 =>
  false_of_evenN0_seven (B.evenN0MatHyp_xg hB.2.1 hN0 (hB.1.symm ▸ hodd) hfus)

end CFSG.StandardType.FrameRoute.FS81

end
