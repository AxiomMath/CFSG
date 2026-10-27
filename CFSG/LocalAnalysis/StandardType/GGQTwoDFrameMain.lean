module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameB
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameRoots
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameLow

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly CFSG.Open

section Frame

variable {G : Type} [Group G] [Finite G]

theorem simpleLo_hi_pos {m : ℕ} (hm : 3 ≤ m) {t : Fin m} (ht : t.val ≠ 0) :
    0 < (OrthTorus.simpleLo t).val ∧ 0 < (OrthTorus.simpleHi t).val := by
  by_cases h : t.val + 1 < m
  · rw [OrthTorus.simpleLo_of_lt h, OrthTorus.simpleHi_of_lt h]
    omega
  · have hlast : t.val + 1 = m := by have := t.isLt; omega
    rw [OrthTorus.simpleLo_of_last hlast, OrthTorus.simpleHi_of_last hlast]
    omega

theorem ggQTwoD_refl_conj {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 4 ≤ m)
    {ι : Type} (e' : Fin m ≃ ι)
    {e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) ((ggCoxeterMatrixD m).reindex e') e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (ι' : Additive ↥Bs ≃+ V)
    {Θ : DVec m ≃ₗ[ZMod 3] V} {ϑ : (ggCoxeterMatrixD m).Group ≃* dEven m} (hϑ : IsDEquiv m ϑ)
    (hΘ : ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m),
      ggLin (p := 3) ι' ((qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) (Θ v) =
        Θ (((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) v))
    {φ : MulAut ↥Bs} (hφA : φ ∈ ggAutomizerJoin L Bs 𝒦) (hφ : GGIsReflection 3 φ) :
    ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧
      ∀ v : DVec m, ggLin (p := 3) ι' φ (Θ v) = Θ (dTau m ε' a' b' v) := by
  obtain ⟨w, i, hφeq⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres
    (reindexD_M_le_three e') hφA hφ
  let i₀ : Fin m := e'.symm i
  let w₀ : (ggCoxeterMatrixD m).Group := (ggCoxeterMatrixD m).reindexGroupEquiv e' w
  let u : (ggCoxeterMatrixD m).Group := w₀ * (ggCoxeterMatrixD m).simple i₀ * w₀⁻¹
  have hsymm : ((ggCoxeterMatrixD m).reindexGroupEquiv e').symm u =
      w * ((ggCoxeterMatrixD m).reindex e').simple i * w⁻¹ := by
    simp only [u, w₀, map_mul, map_inv, CoxeterMatrix.reindexGroupEquiv_symm_apply_simple,
      MulEquiv.symm_apply_apply, i₀, Equiv.apply_symm_apply]
  have heq : e (w * ((ggCoxeterMatrixD m).reindex e').simple i * w⁻¹) = qtwoE0 e' e u := by
    show e (w * ((ggCoxeterMatrixD m).reindex e').simple i * w⁻¹) =
      e (((ggCoxeterMatrixD m).reindexGroupEquiv e').symm u)
    rw [hsymm]
  have hφu : φ = ((qtwoE0 e' e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    rw [hφeq, heq]
  have hϑu : ((ϑ u : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      ((ϑ w₀ : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) *
        dTau m (decide (i₀.val + 1 = m)) (OrthTorus.simpleLo i₀) (OrthTorus.simpleHi i₀) *
        (((ϑ w₀ : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m))⁻¹ := by
    simp only [u, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hϑ i₀]
  have hne : OrthTorus.simpleLo i₀ ≠ OrthTorus.simpleHi i₀ :=
    OrthTorus.simpleLo_ne_simpleHi (by omega) i₀
  obtain ⟨ε', a', b', hab', hconj⟩ := dEven_conj_dTau m (ϑ w₀).2
    (decide (i₀.val + 1 = m)) hne
  refine ⟨ε', a', b', hab', fun v => ?_⟩
  rw [hφu, hΘ u v]
  have hv : ((ϑ u : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) v = dTau m ε' a' b' v := by
    rw [hϑu, hconj]
  rw [hv]

private theorem plq_e_dPermW {m : ℕ} (e : (ggCoxeterMatrixD m).Group ≃* dEven m)
    (π : Equiv.Perm (Fin m)) :
    ((e (dPermW e π) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dPerm m π := by
  rw [dPermW, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem ggQTwoD_perm_conj {Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} {L : Subgroup G} {m : ℕ}
    {ι : Type} (e' : Fin m ≃ ι)
    {e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι' : Additive ↥Bs ≃+ V)
    {Θ : DVec m ≃ₗ[ZMod 3] V} {ϑ : (ggCoxeterMatrixD m).Group ≃* dEven m} (hϑ : IsDEquiv m ϑ)
    (hΘ : ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m),
      ggLin (p := 3) ι' ((qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) (Θ v) =
        Θ (((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) v))
    (π : Equiv.Perm (Fin m)) (i : Fin m) (v : DVec m) :
    ggLin (p := 3) ι' ((qtwoE0 e' e (dPermW ϑ π * (ggCoxeterMatrixD m).simple i *
        (dPermW ϑ π)⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) (Θ v) =
      Θ (dTau m (decide (i.val + 1 = m)) (π (OrthTorus.simpleLo i))
        (π (OrthTorus.simpleHi i)) v) := by
  rw [hΘ (dPermW ϑ π * (ggCoxeterMatrixD m).simple i * (dPermW ϑ π)⁻¹) v]
  have hϑw : ((ϑ (dPermW ϑ π * (ggCoxeterMatrixD m).simple i * (dPermW ϑ π)⁻¹) : dEven m) :
      DVec m ≃ₗ[ZMod 3] DVec m) =
      dPerm m π * dTau m (decide (i.val + 1 = m)) (OrthTorus.simpleLo i) (OrthTorus.simpleHi i) *
        (dPerm m π)⁻¹ := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, plq_e_dPermW, hϑ i]
  rw [hϑw, dPerm_conj_dTau m π (decide (i.val + 1 = m)) (OrthTorus.simpleLo i)
    (OrthTorus.simpleHi i)]

omit [Finite G] in
theorem ggQTwoD_eq_of_ggLin {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι' : Additive ↥Bs ≃+ V) {m : ℕ} (Θ : DVec m ≃ₗ[ZMod 3] V) {φ ψ : MulAut ↥Bs}
    (h : ∀ v : DVec m, ggLin (p := 3) ι' φ (Θ v) = ggLin (p := 3) ι' ψ (Θ v)) : φ = ψ := by
  apply ggLin_injective (p := 3) ι'
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨v, hv⟩ := Θ.surjective u
  rw [← hv]
  exact h v

theorem ggQTwoFrame_core (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hroute : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {m : ℕ} {ι : Type}
    (e' : Fin m ≃ ι) {e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) ((ggCoxeterMatrixD m).reindex e') e)
    (hm4 : 4 ≤ m) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (hn : lab.n = 1) (hr4 : 4 ≤ lab.rank)
    (htag : lab.tag = .D ∨ lab.tag = .twD) :
    lab.rank + 1 = m ∧
      QTwoFrameAt Bs L ((ggCoxeterMatrixD m).reindex e') (ggAutomizerJoin L Bs 𝒦) e e' := by
  have hp3 : p = 3 := ggQTwoD_p_eq_three hRig hroute hΛ hhas hn
  subst hp3
  obtain ⟨n, τ, hmod⟩ := ggQTwoD_sideCoord hRig hroute hΛ hhas hn hr4 htag
  have hD : n = lab.rank ∧ HdRo7D.DCoordModel 3 Bs L n τ := by
    rcases hmod with h | h
    · exact h
    · exact (ggQTwoDFrame_not_c2 hroute hpres (reindexD_M_le_three e') (by omega) τ h.2).elim
  obtain ⟨hnl, hDm⟩ := hD
  have hfix := ggQTwoD_fix hTBF hWI hroute
  obtain ⟨Θ, ϑ, hϑ, hΘ⟩ := ggQTwoDFrame_module hroute (by omega : 4 ≤ m) e' hpres (tauIota τ) hfix
  have hmn : m = n + 1 := by
    have h := LinearEquiv.finrank_eq Θ
    simpa using h
  subst hmn
  refine ⟨by omega, ?_⟩
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
  obtain ⟨j, -, hcover⟩ := ggQTwoDFrame_axis (m := n + 1) (by omega) z rfl Θ.symm hg
  let π : Equiv.Perm (Fin (n + 1)) := Equiv.swap z j
  refine ⟨((ggCoxeterMatrixD (n + 1)).reindexGroupEquiv e').symm (dPermW ϑ π), fun i hi => ?_⟩
  have hconj_eq : (e (((ggCoxeterMatrixD (n + 1)).reindexGroupEquiv e').symm (dPermW ϑ π) *
      ((ggCoxeterMatrixD (n + 1)).reindex e').simple (e' i) *
      (((ggCoxeterMatrixD (n + 1)).reindexGroupEquiv e').symm (dPermW ϑ π))⁻¹) :
        ↥(ggAutomizerJoin L Bs 𝒦)) =
      qtwoE0 e' e (dPermW ϑ π * (ggCoxeterMatrixD (n + 1)).simple i * (dPermW ϑ π)⁻¹) := by
    simp only [qtwoE0, MulEquiv.trans_apply, map_mul, map_inv,
      CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
  rw [hconj_eq]
  obtain ⟨hlo, hhi⟩ := simpleLo_hi_pos (m := n + 1) (by omega) hi
  have hlo' : π (OrthTorus.simpleLo i) ≠ j := fun h =>
    (Nat.pos_iff_ne_zero.mp hlo) (congrArg Fin.val
      (π.injective (h.trans (Equiv.swap_apply_left z j).symm)))
  have hhi' : π (OrthTorus.simpleHi i) ≠ j := fun h =>
    (Nat.pos_iff_ne_zero.mp hhi) (congrArg Fin.val
      (π.injective (h.trans (Equiv.swap_apply_left z j).symm)))
  have hne' : π (OrthTorus.simpleLo i) ≠ π (OrthTorus.simpleHi i) :=
    π.injective.ne (OrthTorus.simpleLo_ne_simpleHi (by omega) i)
  obtain ⟨ε, a, b, ha, hb, hab, hconj⟩ := hcover (decide (i.val + 1 = n + 1))
    (π (OrthTorus.simpleLo i)) (π (OrthTorus.simpleHi i)) hlo' hhi' hne'
  have hmem := ggLinInv_dTau_mem_automizer_d τ hDm ε ha hb hab
  have heq : ((qtwoE0 e' e (dPermW ϑ π * (ggCoxeterMatrixD (n + 1)).simple i *
      (dPermW ϑ π)⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) ε a b) := by
    refine ggQTwoD_eq_of_ggLin (tauIota τ) Θ fun v => ?_
    rw [ggQTwoD_perm_conj e' (tauIota τ) hϑ hΘ π i v, ggLin_ggLinInv]
    have h2 : Θ.symm (dTau (n + 1) ε a b (Θ v)) =
        dTau (n + 1) (decide (i.val + 1 = n + 1)) (π (OrthTorus.simpleLo i))
          (π (OrthTorus.simpleHi i)) v :=
      congrArg (fun F : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1) => F v) hconj
    rw [← h2, LinearEquiv.apply_symm_apply]
  rw [heq]
  exact hmem

end Frame

section Producer


theorem ggQTwoFrameInput_of_inputs {R : ℕ → Prop}
    (hR : ∀ m, R m → 4 ≤ m) (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGQTwoFrameInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM lab hΛ hhas hn htag
  obtain ⟨hroute, -, -, hpres, -⟩ := hcfg
  subst hM
  exact ggQTwoFrame_core hRig hTBF hWI hroute e' hpres (hR m hm) hΛ hhas hn
    (ggQTwoD_four_le_rank hRig hroute hΛ hhas hn htag) htag

end Producer

end CFSG.StandardType.QTwo

end
