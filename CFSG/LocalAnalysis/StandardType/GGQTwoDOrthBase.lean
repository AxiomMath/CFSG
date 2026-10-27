module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseMod
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]


theorem ggQTwoDOrthBase_sideCoord (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (hn : lab.n = 1) (hr : 4 ≤ lab.rank)
    (htag : lab.tag = .D ∨ lab.tag = .twD) :
    ∃ (hx : x ∈ Bs) (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs),
      τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3))) = ⟨x, hx⟩ ∧
      ((n = lab.rank ∧ HdRo7D.DCoordModel 3 Bs L n τ) ∨
        (n + 1 = lab.rank ∧ HdRo7C.C2CoordModel 3 Bs L n τ)) := by
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hEA, hxBs, -, h4⟩ := hconf.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hBs : GGBstar 3 B Bs := hconf.2.1
  have hM : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  have hC : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2
  obtain ⟨n, τ, hτ, hmod⟩ := HdRo7D.d_sideCoord_exact HdRo7D.d_frameOmega_holds hRig hxBs rfl
    hBs hM hΛ hhas htag hn hr hx1 hC h4
  exact ⟨hxBs, n, τ, hτ, hmod⟩

private theorem qtwoDOrthBase_dModel (hRig : GGLabelRigidInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (hn : lab.n = 1) (hr4 : 4 ≤ lab.rank) (htag : lab.tag = .D ∨ lab.tag = .twD) :
    ∃ (hx : x ∈ Bs) (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs),
      τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3))) = ⟨x, hx⟩ ∧
      n = lab.rank ∧ HdRo7D.DCoordModel 3 Bs L n τ := by
  obtain ⟨hx, n, τ, hτx, hmod⟩ := ggQTwoDOrthBase_sideCoord hRig hroute hΛ hhas hn hr4 htag
  rcases hmod with h | h
  · exact ⟨hx, n, τ, hτx, h⟩
  · exact (ggQTwoDFrame_not_c2 hroute hpres hle3 (by omega) τ h.2).elim

theorem ggQTwoDOrthBase_weylD (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 4 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hL : qtwoOrthL G L 𝒦) :
    GGWeylOfType 3 (ggCoxeterMatrixD (m - 1)) (ggAutomizer L Bs) := by
  classical
  obtain ⟨hroute, -, -, hpres, -⟩ := hcfg
  subst hM
  obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hL
  have hp3 : p = 3 := ggQTwoD_p_eq_three hRig hroute hΛ hhas hn
  subst hp3
  have hr4 : 4 ≤ lab.rank := ggQTwoD_four_le_rank hRig hroute hΛ hhas hn htag
  obtain ⟨-, n, τ, -, hnl, hDm⟩ := qtwoDOrthBase_dModel hRig hroute hpres
    (reindexD_M_le_three e') hΛ hhas hn hr4 htag
  have hrank : lab.rank + 1 = m :=
    (ggQTwoFrame_core hRig hTBF hWI hroute e' hpres hm hΛ hhas hn hr4 htag).1
  have hmn : m - 1 = n := by omega
  rw [hmn]
  exact qtwoDOrthBase_weylD_of_model (by omega) hDm

private theorem qtwoDOrthBase_toAdd_mulSingle (n : ℕ) :
    (fun i : Fin (n + 1) => Multiplicative.toAdd
      ((Pi.mulSingle (0 : Fin (n + 1)) (Multiplicative.ofAdd (1 : ZMod 3)) :
        Fin (n + 1) → Multiplicative (ZMod 3)) i)) = dBasis (n + 1) 0 := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [dBasis, Pi.basisFun_apply]
  · simp [dBasis, Pi.basisFun_apply, Pi.single_apply, Pi.mulSingle_eq_of_ne hi, hi]

theorem ggQTwoDOrthBase_coord (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 4 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hL : qtwoOrthL G L 𝒦) :
    ∃ (hx : x ∈ Bs) (β₀ : Additive ↥Bs ≃+ DVec m),
      qtwoDActsAs β₀ (ggAutomizerJoin L Bs 𝒦) (dEven m) ∧
        ∃ (i₀ : Fin m) (c : ZMod 3), c ≠ 0 ∧
          β₀ (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1 ∧
          qtwoDActsAs β₀ (ggAutomizer L Bs) (dEvenStab m (Pi.single i₀ 1)) := by
  classical
  obtain ⟨hroute, -, -, hpres, -⟩ := hcfg
  subst hM
  obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hL
  have hp3 : p = 3 := ggQTwoD_p_eq_three hRig hroute hΛ hhas hn
  subst hp3
  have hr4 : 4 ≤ lab.rank := ggQTwoD_four_le_rank hRig hroute hΛ hhas hn htag
  obtain ⟨hx, n, τ, hτx, hnl, hDm⟩ := qtwoDOrthBase_dModel hRig hroute hpres
    (reindexD_M_le_three e') hΛ hhas hn hr4 htag
  have hfix := ggQTwoD_fix hTBF hWI hroute
  obtain ⟨Θ, ϑ, hϑ, hΘ⟩ := ggQTwoDFrame_module hroute hm e' hpres (tauIota τ) hfix
  have hmn : m = n + 1 := by
    have h := LinearEquiv.finrank_eq Θ
    simpa using h
  subst hmn
  have hg : ∀ (ε : Bool) (a b : Fin (n + 1)), 0 < a.val → 0 < b.val → a ≠ b →
      ∃ (ε' : Bool) (a' b' : Fin (n + 1)), a' ≠ b' ∧
        Θ.symm * dTau (n + 1) ε a b * Θ.symm⁻¹ = dTau (n + 1) ε' a' b' := by
    intro ε a b ha hb hab
    have hmem := ggLinInv_dTau_mem_automizer_d τ hDm ε ha hb hab
    have hA : ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) ε a b) ∈ ggAutomizerJoin L Bs 𝒦 :=
      ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hmem
    obtain ⟨ε', a', b', hne, hconj⟩ := ggQTwoD_refl_conj hroute (by omega) e' hpres (tauIota τ)
      hϑ hΘ hA (ggIsReflection_ggLinInv_dTau τ ε hab)
    refine ⟨ε', a', b', hne, LinearEquiv.ext fun v => ?_⟩
    have h1 : dTau (n + 1) ε a b (Θ v) = Θ (dTau (n + 1) ε' a' b' v) := by
      rw [← hconj v, ggLin_ggLinInv]
    show Θ.symm (dTau (n + 1) ε a b (Θ v)) = _
    rw [h1, LinearEquiv.symm_apply_apply]
  let z : Fin (n + 1) := ⟨0, by omega⟩
  obtain ⟨j, ⟨s, hs, hsj⟩, -⟩ := ggQTwoDFrame_axis (m := n + 1) (by omega) z rfl Θ.symm hg
  have hacts := qtwoDOrthBase_acts_of_module (tauIota τ) Θ ϑ (qtwoE0 e' e) hΘ
  have hβx : ((tauIota τ).trans Θ.symm.toAddEquiv)
      (Additive.ofMul (τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3))))) =
        s • dBasis (n + 1) j := by
    show Θ.symm (tauIota τ (Additive.ofMul (τ _))) = _
    rw [tauIota_ofMul_tau, qtwoDOrthBase_toAdd_mulSingle]
    exact hsj
  refine ⟨hx, (tauIota τ).trans Θ.symm.toAddEquiv, hacts, j, s, hs, ?_, ?_⟩
  · rw [← hτx, hβx, dBasis, Pi.basisFun_apply]
  · have hb : (dBasis (n + 1) j : DVec (n + 1)) = Pi.single j 1 := by
      rw [dBasis, Pi.basisFun_apply]
    rw [← hb]
    exact qtwoDOrthBase_acts_stab hDm _
      (fun a ha => hacts.1 a (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha)) hs hβx

end CFSG.StandardType.QTwo

end
