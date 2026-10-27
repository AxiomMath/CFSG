module

import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtCorank
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSix
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

structure PrimExtSetting (G H : Subgroup (U ≃ₗ[ZMod p] U)) (d : ℕ) : Prop where
  four_le_finrank : 4 ≤ Module.finrank (ZMod p) U
  reflGen : ReflGen p G
  absIrred : AbsIrred p G
  primitive : ¬ Quasithin.SimsG4.IsImprimitiveOnV G
  transvectionFree : QTwoLin.TransvectionFree G
  dmax : DMax p G d
  three_lt : 3 < d
  noOrth : ∀ X ≤ G, ReflGen p X → SplitSupport X (Module.finrank (ZMod p) U - 1) →
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) →
    (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ¬ IsOrthType p (movedGroup X)
  H_le : H ≤ G
  reflGen_H : ReflGen p H
  splitSupport : SplitSupport H (Module.finrank (ZMod p) U - 1)
  dmax_H : DMax p H d
  maximal : ∀ X ≤ G, ReflGen p X → SplitSupport X (Module.finrank (ZMod p) U - 1) →
    DMax p X d → Nat.card X ≤ Nat.card H
  primitive_H : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup H)

theorem isCommIrredPair_conj {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hHG : H ≤ G)
    {g h b : U ≃ₗ[ZMod p] U} (hg : g ∈ H) (hpair : IsCommIrredPair p G H h b) :
    IsCommIrredPair p G H (g * h * g⁻¹) (g * b * g⁻¹) := by
  obtain ⟨hhH, hh, hbG, hb, hcomm, hirr⟩ := hpair
  have hgG : g ∈ G := hHG hg
  have hIrr : IrredOnSection (Subgroup.closure (insert (g * b * g⁻¹)
      (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤ := by
    have hCB : Subgroup.closure (insert (g * b * g⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) =
        Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro x hx
        rw [Set.mem_insert_iff] at hx
        rcases hx with hxb | hx
        · subst x
          have hbC : b ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) :=
            Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
          have hgC : g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) :=
            Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hg))
          have hgiC : g⁻¹ ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) :=
            Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr (H.inv_mem hg)))
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC hbC) hgiC
        · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hx))
      · rw [Subgroup.closure_le]
        intro x hx
        rw [Set.mem_insert_iff] at hx
        rcases hx with hxb | hx
        · subst x
          have hgbg : g * b * g⁻¹ ∈
              Subgroup.closure (insert (g * b * g⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) :=
            Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
          have hgC : g ∈ Subgroup.closure (insert (g * b * g⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) :=
            Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hg))
          have hgiC : g⁻¹ ∈
              Subgroup.closure (insert (g * b * g⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) :=
            Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr (H.inv_mem hg)))
          have hprod := Subgroup.mul_mem _ (Subgroup.mul_mem _ hgiC hgbg) hgC
          have heq : g⁻¹ * (g * b * g⁻¹) * g = b := by group
          rwa [heq] at hprod
        · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hx))
    rw [hCB]
    exact hirr
  refine ⟨H.mul_mem (H.mul_mem hg hhH) (H.inv_mem hg),
    IsRefl.conj hh g,
    G.mul_mem (G.mul_mem hgG hbG) (G.inv_mem hgG),
    IsRefl.conj hb g, ?_, hIrr⟩
  calc (g * h * g⁻¹) * (g * b * g⁻¹) = g * (h * b) * g⁻¹ := by group
    _ = g * (b * h) * g⁻¹ := by rw [hcomm]
    _ = (g * b * g⁻¹) * (g * h * g⁻¹) := by group

private theorem closure_insert_apply_mem [Module.Finite (ZMod p) U] {W : Submodule (ZMod p) U}
    {b : U ≃ₗ[ZMod p] U} {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hb : ∀ x ∈ W, b x ∈ W) (hH : ∀ h ∈ H, ∀ x ∈ W, h x ∈ W) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))), ∀ x ∈ W, g x ∈ W := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => ∀ x ∈ W, g x ∈ W) ?_ ?_ ?_ ?_ hg
  · intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hxb | hx
    · subst x; exact hb
    · exact hH x hx
  · intro x hx; simpa using hx
  · intro x y _ _ px py z hz
    rw [LinearEquiv.mul_apply]
    exact px _ (py _ hz)
  · intro x _ px z hz
    have hxle : W.map (x : U →ₗ[ZMod p] U) ≤ W := Submodule.map_le_iff_le_comap.mpr px
    have hmap : W.map (x : U →ₗ[ZMod p] U) = W :=
      Submodule.eq_of_le_of_finrank_eq hxle (by rw [LinearEquiv.finrank_map_eq])
    have hz' : z ∈ W.map (x : U →ₗ[ZMod p] U) := by rw [hmap]; exact hz
    obtain ⟨y, hy, hyz⟩ := hz'
    have : x⁻¹ z = y := by rw [← hyz]; simp
    rw [this]; exact hy

theorem not_le_of_isCommIrredPair [Module.Finite (ZMod p) U]
    (_hn : 2 ≤ Module.finrank (ZMod p) U) {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) {h b : U ≃ₗ[ZMod p] U}
    (hpair : IsCommIrredPair p G H h b) :
    ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H ∧
      ∃ v ∈ centralizerSpace H, b v ≠ v := by
  obtain ⟨hcompl, hdim, hirrH⟩ := hs
  obtain ⟨hhH, hhr, hbG, hbr, hcomm, hirr⟩ := hpair
  have hpos : 0 < Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H) := by
    have hle := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hhH
    have h1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hhr.2
    have := Submodule.finrank_mono hle
    omega
  constructor
  · intro hle
    have hinv := closure_insert_apply_mem
      (W := HardMathSupport.Kantor79.commutatorSpace H)
      (fun x hx => by
        have hdiff : b x - x ∈ HardMathSupport.Kantor79.commutatorSpace H := hle ⟨x, rfl⟩
        have : b x = x + (b x - x) := by abel
        rw [this]; exact Submodule.add_mem _ hx hdiff)
      (fun g hg x hx => apply_mem_commutatorSpace hg hx)
    rcases hirr (HardMathSupport.Kantor79.commutatorSpace H) bot_le le_top hinv with hbot | htop
    · rw [hbot, finrank_bot] at hpos; exact absurd hpos (lt_irrefl 0)
    · have hlt : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) <
          Module.finrank (ZMod p) U := by rw [hdim]; omega
      rw [htop, finrank_top] at hlt
      exact absurd hlt (lt_irrefl _)
  · by_contra h
    push Not at h
    have hfixH : ∀ g ∈ H, ∀ x ∈ centralizerSpace H, g x ∈ centralizerSpace H := by
      intro g hg x hx
      refine (mem_centralizerSpace).mpr fun k hk => ?_
      rw [(mem_centralizerSpace.mp hx) g hg]
      exact (mem_centralizerSpace.mp hx) k hk
    have hinv := closure_insert_apply_mem (W := centralizerSpace H)
      (fun x hx => by rw [h x hx]; exact hx) hfixH
    rcases hirr (centralizerSpace H) bot_le le_top hinv with hbot | htop
    · have hsup := hcompl.sup_eq_top
      have hVtop : HardMathSupport.Kantor79.commutatorSpace H = ⊤ := by
        rw [← hsup, hbot, sup_bot_eq]
      have hlt : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) <
          Module.finrank (ZMod p) U := by rw [hdim]; omega
      rw [hVtop, finrank_top] at hlt
      exact absurd hlt (lt_irrefl _)
    · have hinf := hcompl.inf_eq_bot
      have hVbot : HardMathSupport.Kantor79.commutatorSpace H = ⊥ := by
        rw [← hinf, htop, inf_top_eq]
      rw [hVbot, finrank_bot] at hpos; exact absurd hpos (lt_irrefl 0)

private theorem irred_contra_of_invariant [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {h b : U ≃ₗ[ZMod p] U}
    (hpair : IsCommIrredPair p G H h b) {W : Submodule (ZMod p) U}
    (hb : ∀ x ∈ W, b x ∈ W) (hH : ∀ g ∈ H, ∀ x ∈ W, g x ∈ W)
    (hbot : W ≠ ⊥) (htop : W ≠ ⊤) : False := by
  have hinv := closure_insert_apply_mem (W := W) hb hH
  rcases hpair.2.2.2.2.2 W bot_le le_top hinv with h | h
  · exact hbot h
  · exact htop h

private theorem basisClosure_blockSucc_apply_last {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U)
    {T : Set (Matrix (Fin m) (Fin m) (ZMod p))} {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ basisClosure f (Matrix.blockSucc '' T)) :
    g (f (Fin.last m)) = f (Fin.last m) := by
  refine Subgroup.closure_induction
    (p := fun g _ => g (f (Fin.last m)) = f (Fin.last m)) ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain ⟨M, _, hxM⟩ := hx
    apply f.repr.injective
    ext i
    have h1 : f.repr (x (f (Fin.last m))) i =
        (LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U)) i (Fin.last m) :=
      (LinearMap.toMatrix_apply f f (x : U →ₗ[ZMod p] U) i (Fin.last m)).symm
    rw [h1, ← hxM]
    induction i using Fin.lastCases <;> simp
  · simp
  · intro x y _ _ px py
    rw [LinearEquiv.mul_apply, py, px]
  · intro x _ px
    simpa using (congrArg (fun v => x⁻¹ v) px).symm

private theorem basisClosure_blockSucc_coord_apply {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U)
    {T : Set (Matrix (Fin m) (Fin m) (ZMod p))} {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ basisClosure f (Matrix.blockSucc '' T)) :
    ∀ w : U, f.coord (Fin.last m) (g w) = f.coord (Fin.last m) w := by
  have hL : (f.coord (Fin.last m)).comp (g : U →ₗ[ZMod p] U) = f.coord (Fin.last m) := by
    refine Subgroup.closure_induction
      (p := fun g : U ≃ₗ[ZMod p] U =>
        fun _ => (f.coord (Fin.last m)).comp (g : U →ₗ[ZMod p] U) = f.coord (Fin.last m))
      ?_ ?_ ?_ ?_ hg
    · intro x hx
      obtain ⟨M, _, hxM⟩ := hx
      apply f.ext
      intro i
      rw [LinearMap.comp_apply, f.coord_apply]
      have h1 : f.repr ((x : U →ₗ[ZMod p] U) (f i)) (Fin.last m) =
          (LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U)) (Fin.last m) i :=
        (LinearMap.toMatrix_apply f f (x : U →ₗ[ZMod p] U) (Fin.last m) i).symm
      rw [h1, ← hxM, f.coord_apply]
      induction i using Fin.lastCases <;> simp
    · ext v; simp
    · intro x y _ _ px py
      ext v
      change f.coord (Fin.last m) (x (y v)) = f.coord (Fin.last m) v
      rw [show f.coord (Fin.last m) (x (y v)) = f.coord (Fin.last m) (y v) from
            congrFun (congrArg DFunLike.coe px) (y v),
          show f.coord (Fin.last m) (y v) = f.coord (Fin.last m) v from
            congrFun (congrArg DFunLike.coe py) v]
    · intro x _ px
      ext v
      have h2 := congrFun (congrArg DFunLike.coe px) (x⁻¹ v)
      simp only [LinearMap.comp_apply] at h2
      simpa using h2.symm
  intro w
  exact congrFun (congrArg DFunLike.coe hL) w

private theorem blockSucc_pair_coord_data [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U) {T : Set (Matrix (Fin m) (Fin m) (ZMod p))}
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hfH : H = basisClosure f (Matrix.blockSucc '' T))
    (hm : 1 ≤ m) :
    (∀ g ∈ H, g (f (Fin.last m)) = f (Fin.last m)) ∧
    (∀ g ∈ H, ∀ v, f.coord (Fin.last m) (g v) = f.coord (Fin.last m) v) ∧
    (∀ g ∈ H, ∀ x ∈ Submodule.span (ZMod p) {f (Fin.last m)},
      g x ∈ Submodule.span (ZMod p) {f (Fin.last m)}) ∧
    LinearMap.ker (f.coord (Fin.last m)) ≠ ⊥ ∧ LinearMap.ker (f.coord (Fin.last m)) ≠ ⊤ ∧
    Submodule.span (ZMod p) {f (Fin.last m)} ≠ ⊥ ∧
    Submodule.span (ZMod p) {f (Fin.last m)} ≠ ⊤ := by
  have : NeZero m := ⟨by omega⟩
  have hlast0 : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := fun h => hlast0 h.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; exact basisClosure_blockSucc_apply_last f (hfH ▸ hg)
  · intro g hg; exact basisClosure_blockSucc_coord_apply f (hfH ▸ hg)
  · intro g hg x hx
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, basisClosure_blockSucc_apply_last f (hfH ▸ hg)]⟩
  · intro hbot
    have hf0 : f (0 : Fin (m + 1)) ∈ LinearMap.ker (f.coord (Fin.last m)) := by
      rw [LinearMap.mem_ker, f.coord_apply]; simp [hlast0]
    rw [hbot] at hf0
    exact (f.ne_zero (0 : Fin (m + 1))) (by simpa using hf0)
  · intro htop
    have hmem : f (Fin.last m) ∈ LinearMap.ker (f.coord (Fin.last m)) := by rw [htop]; trivial
    rw [LinearMap.mem_ker, f.coord_apply] at hmem
    simp at hmem
  · intro hbot
    have : f (Fin.last m) ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hbot]; exact Submodule.mem_span_singleton_self _
    exact f.ne_zero _ (by simpa using this)
  · intro htop
    have hmem : f (0 : Fin (m + 1)) ∈ Submodule.span (ZMod p) {f (Fin.last m)} := by
      rw [htop]; trivial
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h2 := congrArg (fun v => f.repr v (0 : Fin (m + 1))) hc
    simp [f.repr_self, h0last] at h2

private theorem mem_span_last_of_forall_repr_eq_zero [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U) {w : U}
    (hw : ∀ i : Fin m, f.repr w i.castSucc = 0) :
    w ∈ Submodule.span (ZMod p) {f (Fin.last m)} := by
  rw [Submodule.mem_span_singleton]
  refine ⟨f.repr w (Fin.last m), ?_⟩
  rw [← f.sum_repr w, Fin.sum_univ_castSucc]
  simp [hw]

private theorem psi_eq_zero_on_ker_coord_last_of_forall [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U) {ψ : Module.Dual (ZMod p) U}
    (hψ : ∀ i : Fin m, ψ (f i.castSucc) = 0) :
    ∀ x ∈ LinearMap.ker (f.coord (Fin.last m)), ψ x = 0 := by
  intro x hx
  rw [← f.sum_repr x, map_sum, Fin.sum_univ_castSucc]
  have hx0 : f.repr x (Fin.last m) = 0 := by
    rw [← f.coord_apply]; exact LinearMap.mem_ker.mp hx
  simp [hψ, hx0]

private theorem pair_first_coords_zero [Module.Finite (ZMod p) U] {m : ℕ}
    (hp : p ≠ 2) (f : Module.Basis (Fin (m + 1)) (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {h₁ b : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hpair : IsCommIrredPair p G H h₁ b) {w : U} {ψ : Module.Dual (ZMod p) U}
    (hψ : ψ w = 2) (hb : b = Module.reflection hψ)
    (hsU : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hn : 2 ≤ Module.finrank (ZMod p) U) :
    f.repr w 0 = 0 ∧ ψ (f 0) = 0 := by
  have hzs : ψ (f 0) = 0 ∧ f.repr w 0 = 0 := by
    refine apply_eq_zero_of_commute_diagSignMat hp f (i := 0) hh₁ hψ ?_ ?_
    · have hcomm := hpair.2.2.2.2.1; rw [hb] at hcomm; exact hcomm.symm
    · intro hne
      have hle : HardMathSupport.Kantor79.movedSpace b ≤
          HardMathSupport.Kantor79.commutatorSpace H := by
        rw [hb, hne]; exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hpair.1
      exact (not_le_of_isCommIrredPair hn hsU hpair).1 hle
  exact ⟨hzs.2, hzs.1⟩

private theorem false_of_mem_ker_coord_last [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {h₁ b : U ≃ₗ[ZMod p] U} {ψ : Module.Dual (ZMod p) U}
    {w : U} (hψ : ψ w = 2) (hpair : IsCommIrredPair p G H h₁ b)
    (hb : b = Module.reflection hψ)
    (hHW : ∀ g ∈ H, ∀ x ∈ LinearMap.ker (f.coord (Fin.last m)),
      g x ∈ LinearMap.ker (f.coord (Fin.last m)))
    (hbot : LinearMap.ker (f.coord (Fin.last m)) ≠ ⊥)
    (htop : LinearMap.ker (f.coord (Fin.last m)) ≠ ⊤)
    (hw : w ∈ LinearMap.ker (f.coord (Fin.last m))) : False := by
  have hbW : ∀ x ∈ LinearMap.ker (f.coord (Fin.last m)),
      b x ∈ LinearMap.ker (f.coord (Fin.last m)) := by
    intro x hx
    rw [hb, Module.reflection_apply]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hw)
  exact irred_contra_of_invariant hpair hbW hHW hbot htop

private theorem false_of_psi_eq_zero_on_ker_coord_last [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {h₁ b : U ≃ₗ[ZMod p] U} {ψ : Module.Dual (ZMod p) U}
    {w : U} (hψ : ψ w = 2) (hpair : IsCommIrredPair p G H h₁ b)
    (hb : b = Module.reflection hψ)
    (hHW : ∀ g ∈ H, ∀ x ∈ LinearMap.ker (f.coord (Fin.last m)),
      g x ∈ LinearMap.ker (f.coord (Fin.last m)))
    (hbot : LinearMap.ker (f.coord (Fin.last m)) ≠ ⊥)
    (htop : LinearMap.ker (f.coord (Fin.last m)) ≠ ⊤)
    (h0 : ∀ x ∈ LinearMap.ker (f.coord (Fin.last m)), ψ x = 0) : False := by
  have hbW : ∀ x ∈ LinearMap.ker (f.coord (Fin.last m)),
      b x ∈ LinearMap.ker (f.coord (Fin.last m)) := by
    intro x hx
    rw [LinearMap.mem_ker, hb, Module.reflection_apply]
    simp [h0 x hx, LinearMap.mem_ker.mp hx]
  exact irred_contra_of_invariant hpair hbW hHW hbot htop

private theorem false_of_psi_last_eq_zero [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {h₁ b : U ≃ₗ[ZMod p] U} {ψ : Module.Dual (ZMod p) U}
    {w : U} (hψ : ψ w = 2) (hpair : IsCommIrredPair p G H h₁ b)
    (hb : b = Module.reflection hψ)
    (hHW : ∀ g ∈ H, ∀ x ∈ Submodule.span (ZMod p) {f (Fin.last m)},
      g x ∈ Submodule.span (ZMod p) {f (Fin.last m)})
    (hbot : Submodule.span (ZMod p) {f (Fin.last m)} ≠ ⊥)
    (htop : Submodule.span (ZMod p) {f (Fin.last m)} ≠ ⊤)
    (hψl : ψ (f (Fin.last m)) = 0) : False := by
  have hbW : ∀ x ∈ Submodule.span (ZMod p) {f (Fin.last m)},
      b x ∈ Submodule.span (ZMod p) {f (Fin.last m)} := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, hb, Module.reflection_apply, hψl, zero_smul, sub_zero]⟩
  exact irred_contra_of_invariant hpair hbW hHW hbot htop

private theorem false_of_mem_span_last [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {h₁ b : U ≃ₗ[ZMod p] U} {ψ : Module.Dual (ZMod p) U}
    {w : U} (hψ : ψ w = 2) (hpair : IsCommIrredPair p G H h₁ b)
    (hb : b = Module.reflection hψ)
    (hHW : ∀ g ∈ H, ∀ x ∈ Submodule.span (ZMod p) {f (Fin.last m)},
      g x ∈ Submodule.span (ZMod p) {f (Fin.last m)})
    (hbot : Submodule.span (ZMod p) {f (Fin.last m)} ≠ ⊥)
    (htop : Submodule.span (ZMod p) {f (Fin.last m)} ≠ ⊤)
    (hw : w ∈ Submodule.span (ZMod p) {f (Fin.last m)}) : False := by
  have hbW : ∀ x ∈ Submodule.span (ZMod p) {f (Fin.last m)},
      b x ∈ Submodule.span (ZMod p) {f (Fin.last m)} := by
    intro x hx
    rw [hb, Module.reflection_apply]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hw)
  exact irred_contra_of_invariant hpair hbW hHW hbot htop

theorem coords_of_isCommIrredPair (hp : p ≠ 2) [Module.Finite (ZMod p) U] {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U) {T : Set (Matrix (Fin m) (Fin m) (ZMod p))}
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H m)
    (hfH : H = basisClosure f (Matrix.blockSucc '' T)) {h₁ b : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hpair : IsCommIrredPair p G H h₁ b) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hb : b = Module.reflection hψ) :
    f.repr w 0 = 0 ∧ ψ (f 0) = 0 ∧ f.repr w (Fin.last m) ≠ 0 ∧ ψ (f (Fin.last m)) ≠ 0 ∧
      (∃ i : Fin m, f.repr w i.castSucc ≠ 0) ∧ ∃ i : Fin m, ψ (f i.castSucc) ≠ 0 := by
  have hfinU : Module.finrank (ZMod p) U = m + 1 := by
    rw [Module.finrank_eq_card_basis f]; simp
  have hsU : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [hfinU]; simpa using hs
  have hm1 : 1 ≤ m := by
    have h2 := Submodule.finrank_mono
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hpair.1)
    have h3 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h₁) = 1 :=
      hpair.2.1.2
    rw [hs.2.1, h3] at h2
    omega
  have hn : 2 ≤ Module.finrank (ZMod p) U := by rw [hfinU]; omega
  obtain ⟨_, hHcoord, hHWlast, hkbot, hktop, hsbot, hstop⟩ :=
    blockSucc_pair_coord_data f hfH hm1
  have hHWfirst : ∀ g ∈ H, ∀ x ∈ LinearMap.ker (f.coord (Fin.last m)),
      g x ∈ LinearMap.ker (f.coord (Fin.last m)) := by
    intro g hg x hx
    exact LinearMap.mem_ker.mpr (by rw [hHcoord g hg x]; exact LinearMap.mem_ker.mp hx)
  obtain ⟨hA, hB⟩ := pair_first_coords_zero hp f hh₁ hpair hψ hb hsU hn
  refine ⟨hA, hB, ?_, ?_, ?_, ?_⟩
  · intro hw
    exact false_of_mem_ker_coord_last f hψ hpair hb hHWfirst hkbot hktop
      (by rw [LinearMap.mem_ker, f.coord_apply]; exact hw)
  · intro hψl
    exact false_of_psi_last_eq_zero f hψ hpair hb hHWlast hsbot hstop hψl
  · by_contra hw
    push Not at hw
    exact false_of_mem_span_last f hψ hpair hb hHWlast hsbot hstop
      (mem_span_last_of_forall_repr_eq_zero f hw)
  · by_contra hψf
    push Not at hψf
    exact false_of_psi_eq_zero_on_ker_coord_last f hψ hpair hb hHWfirst hkbot hktop
      (psi_eq_zero_on_ker_coord_last_of_forall f hψf)

namespace PrimExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}

theorem not_isOrthType (S : PrimExtSetting G H d) : ¬ IsOrthType p (movedGroup H) := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
  exact S.noOrth H S.H_le S.reflGen_H S.splitSupport S.primitive_H
    ⟨x, hx, y, hy, hxr, hyr, by rw [hxy]; exact S.three_lt⟩

theorem card_le_of_orderOf (S : PrimExtSetting G H d) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hXG : X ≤ G) (hX : ReflGen p X) (hs : SplitSupport X (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = d) :
    Nat.card X ≤ Nat.card H :=
  S.maximal X hXG hX hs
    ⟨fun x hx y hy hxr hyr => S.dmax.1 x (hXG hx) y (hXG hy) hxr hyr, hd⟩

theorem eq_of_le [Module.Finite (ZMod p) U] (S : PrimExtSetting G H d)
    {K : Subgroup (U ≃ₗ[ZMod p] U)} (hKG : K ≤ G) (hHK : H ≤ K) (hK : ReflGen p K)
    (hs : SplitSupport K (Module.finrank (ZMod p) U - 1)) : K = H := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
  have : Fintype U := Fintype.ofEquiv (Fin (Module.finrank (ZMod p) U) → ZMod p)
    (Module.finBasis (ZMod p) U).equivFun.symm
  have : Finite (U ≃ₗ[ZMod p] U) := Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
    (fun a b h => LinearEquiv.ext (fun x => congrFun h x))
  exact (Subgroup.eq_of_le_of_card_ge hHK
    (card_le_of_orderOf S hKG hK hs ⟨x, hHK hx, y, hHK hy, hxr, hyr, hxy⟩)).symm

theorem centreOrderBound (hp : p ≠ 2) [Module.Finite (ZMod p) U] (S : PrimExtSetting G H d)
    (h19 : LemmaOneNineInput) : CentreOrderBound p G (Module.finrank (ZMod p) U - 1) :=
  h19 p U G hp S.reflGen S.transvectionFree S.absIrred S.primitive

theorem exists_model (hp : p ≠ 2) [Module.Finite (ZMod p) U] (S : PrimExtSetting G H d)
    (htab : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1)) (h19 : LemmaOneNineInput) :
    (Module.finrank (ZMod p) U = 4 ∧ d = 5 ∧ p ≠ 5 ∧
        ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U), α ^ 2 = α + 1 ∧
          H = basisClosure f (h3Mats α)) ∨
      (Module.finrank (ZMod p) U = 4 ∧ d = 4 ∧ p ≠ 7 ∧
        ∃ (β : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U), 2 * β ^ 2 + β + 1 = 0 ∧
          H = basisClosure f (j34Mats β)) ∨
      (Module.finrank (ZMod p) U = 5 ∧ d = 5 ∧ p ≠ 5 ∧
        ∃ (α : ZMod p) (f : Module.Basis (Fin 5) (ZMod p) U), α ^ 2 = α + 1 ∧
          H = basisClosure f (h4Mats α)) ∨
      (Module.finrank (ZMod p) U = 5 ∧ d = 4 ∧ p ≠ 3 ∧
        ∃ f : Module.Basis (Fin 5) (ZMod p) U, H = basisClosure f f4ExtMats) := by
  have hTFH : QTwoLin.TransvectionFree H := fun g hg => S.transvectionFree g (S.H_le hg)
  have hl : 3 ≤ Module.finrank (ZMod p) U - 1 := by have := S.four_le_finrank; omega
  have hfin : Module.finrank (ZMod p) U = (Module.finrank (ZMod p) U - 1) + 1 := by omega
  have hcent : ∀ z ∈ H, (∀ x ∈ H, z * x = x * z) → orderOf z ≤ 3 :=
    centreOrderBound hp S h19 H S.H_le S.reflGen_H S.splitSupport
  have h := htab U H d hp hl hfin S.reflGen_H hTFH S.splitSupport S.primitive_H
    (not_isOrthType S) hcent S.dmax_H S.three_lt
  rcases h with ⟨hl3, hd5, hp5, α, f, hα, hfH⟩ | ⟨hl3, hd4, hp7, β, f, hβ, hfH⟩ |
    ⟨hl4, hd5, hp5, α, f, hα, hfH⟩ | ⟨hl4, hd4, hp3, f, hfH⟩
  · left; exact ⟨by omega, hd5, hp5, α, f, hα, hfH⟩
  · right; left; exact ⟨by omega, hd4, hp7, β, f, hβ, hfH⟩
  · right; right; left; exact ⟨by omega, hd5, hp5, α, f, hα, hfH⟩
  · right; right; right; exact ⟨by omega, hd4, hp3, f, hfH⟩

theorem lemmaTwoThreeFrame (hp : p ≠ 2) [Module.Finite (ZMod p) U] (S : PrimExtSetting G H d)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {h₁ z τ : U ≃ₗ[ZMod p] U}
    (hfr : PrimFrameData p H h₁ z τ) :
    LemmaTwoThreeFrame p G H z {s | ∃ g ∈ H, s = g * h₁ * g⁻¹} := by
  have hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
    exact ⟨x, hx, y, hy, hxr, hyr, by rw [hxy]; exact S.three_lt⟩
  have hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ G → H ≤ K → ReflGen p K →
      SplitSupport K (Module.finrank (ZMod p) U - 1) → K = H :=
    fun K hKG hHK hK hsK => eq_of_le S hKG hHK hK hsK
  refine ⟨S.H_le, S.transvectionFree, S.reflGen_H, S.splitSupport, S.four_le_finrank, ?_, ?_,
    hfr.1, hfr.2.1, hfr.2.2.1, ?_, ?_, ?_⟩
  · intro b hbG hb' hbH
    exact mem_of_movedSpace_le_of_maximal hp S.four_le_finrank htab S.transvectionFree S.H_le
      S.reflGen_H S.splitSupport hd hmax hbG hb' hbH
  · intro b hbG hb' hbH hbH'
    exact irredOnSection_closure_insert_of_not_le hp S.four_le_finrank htab S.transvectionFree
      S.H_le S.reflGen_H S.splitSupport hd hbG hb' hbH hbH'
  · intro g hg s hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨g * k, H.mul_mem hg hk, by group⟩
  · exact ⟨h₁, ⟨1, H.one_mem, by group⟩, hfr.2.2.2.1, hfr.2.2.2.2.1,
      hfr.2.2.2.2.2.1, hfr.2.2.2.2.2.2.1⟩
  · intro x hx hxr hxle
    obtain ⟨g, hg, hgm⟩ := hfr.2.2.2.2.2.2.2.2.2 x hx hxr hxle
    exact ⟨g * h₁ * g⁻¹, ⟨g, hg, rfl⟩, H.mul_mem (H.mul_mem hg hfr.2.2.2.1) (H.inv_mem hg),
      IsRefl.conj hfr.2.2.2.2.1 g, hgm⟩

theorem exists_pair (hp : p ≠ 2) [Module.Finite (ZMod p) U] (S : PrimExtSetting G H d)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {h₁ z τ : U ≃ₗ[ZMod p] U}
    (hfr : PrimFrameData p H h₁ z τ) : ∃ b, IsCommIrredPair p G H h₁ b := by
  have hF := lemmaTwoThreeFrame hp S htab hfr
  have hirrG : IrredOnSection G ⊥ ⊤ := fun X _ _ hinv => S.absIrred.1 X hinv
  obtain ⟨a, haG, haRefl, haH, haH'⟩ := hF.exists_isRefl_not_le hp S.reflGen hirrG
  obtain ⟨h, hhS, b, hpair⟩ := hF.exists_pair_of_isCaseCRefl hp hfr.2.2.2.2.2.2.2.1
    hfr.2.2.2.2.2.2.2.2.1 haG haRefl haH haH'
  obtain ⟨g, hg, hgh⟩ := hhS
  refine ⟨g⁻¹ * b * g, ?_⟩
  have hres := isCommIrredPair_conj S.H_le (H.inv_mem hg) hpair
  rw [hgh] at hres
  simpa [mul_assoc] using hres

theorem exists_reflection_coords (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H d) (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {m : ℕ}
    (f : Module.Basis (Fin (m + 1)) (ZMod p) U) {T : Set (Matrix (Fin m) (Fin m) (ZMod p))}
    (hfH : H = basisClosure f (Matrix.blockSucc '' T)) {h₁ z τ : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hfr : PrimFrameData p H h₁ z τ) :
    ∃ (w : U) (ψ : Module.Dual (ZMod p) U) (hψ : ψ w = 2), Module.reflection hψ ∈ G ∧
      Module.reflection hψ ∉ H ∧ f.repr w 0 = 0 ∧ ψ (f 0) = 0 ∧ f.repr w (Fin.last m) ≠ 0 ∧
      ψ (f (Fin.last m)) ≠ 0 ∧ ∃ i : Fin m, f.repr w i.castSucc ≠ 0 := by
  obtain ⟨b, hpair⟩ := exists_pair hp S htab hfr
  obtain ⟨w, ψ, hψ, hb⟩ := (isRefl_iff hp b).mp hpair.2.2.2.1
  have hfinU : Module.finrank (ZMod p) U = m + 1 := by
    rw [Module.finrank_eq_card_basis f]; simp
  have hs' : SplitSupport H m := by
    have := S.splitSupport
    rw [hfinU] at this
    simpa using this
  have hcoords := coords_of_isCommIrredPair hp f hs' hfH hh₁ hpair hψ hb
  have hbnotH : Module.reflection hψ ∉ H := by
    intro hbH
    have hfix := (basisClosure_blockSucc_apply_last f (hfH ▸ hbH))
    rw [Module.reflection_apply] at hfix
    have hw0 : w ≠ 0 := by
      intro hw0
      rw [hw0, map_zero] at hψ
      exact (ZMod.prime_ne_zero p 2 hp) hψ.symm
    have hsmul : ψ (f (Fin.last m)) • w = 0 := by
      have h : -(ψ (f (Fin.last m)) • w) = 0 := by
        calc -(ψ (f (Fin.last m)) • w)
            = (f (Fin.last m) - ψ (f (Fin.last m)) • w) - f (Fin.last m) := by abel
          _ = f (Fin.last m) - f (Fin.last m) := by rw [hfix]
          _ = 0 := sub_self _
      simpa using h
    exact (smul_eq_zero.mp hsmul).elim hcoords.2.2.2.1 hw0
  have hbG : Module.reflection hψ ∈ G := by rw [← hb]; exact hpair.2.2.1
  exact ⟨w, ψ, hψ, hbG, hbnotH, hcoords.1, hcoords.2.1, hcoords.2.2.1, hcoords.2.2.2.1,
    hcoords.2.2.2.2.1⟩

theorem exists_isCentralizingSplit (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H d) {h₁ b : U ≃ₗ[ZMod p] U} (hpair : IsCommIrredPair p G H h₁ b)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hirr : IrredOnSection (reflSubgroupIn p H (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1))) ⊥
      (HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1))))) :
    IsCentralizingSplit p G H (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U))))
      h₁ := by
  have hn : 2 ≤ Module.finrank (ZMod p) U := by have := S.four_le_finrank; omega
  have hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    (not_le_of_isCommIrredPair hn S.splitSupport hpair).1
  have hirr' := irredOnSection_closure_insert_reflSubgroupIn hp S.transvectionFree S.H_le
    S.splitSupport hpair hdim hirr
  exact isCentralizingSplit_of_irredOnSection hp S.transvectionFree S.H_le S.splitSupport
    hpair.1 hpair.2.1 hpair.2.2.1 hpair.2.2.2.1 hpair.2.2.2.2.1 hbH hdim hirr'

end PrimExtSetting

end CFSG.StandardType.ZS

end
