module

public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCompSgn
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

section Helpers

variable {k : ℕ} {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

private def signVec (a : Fin k) : Fin k → Multiplicative (ZMod p) :=
  fun j => if j = a then 1 else Multiplicative.ofAdd 1

private theorem signVec_self (a : Fin k) : signVec (p := p) a a = 1 := by
  rw [signVec, if_pos rfl]

private theorem signVec_of_ne {a j : Fin k} (hj : j ≠ a) :
    signVec (p := p) a j = Multiplicative.ofAdd 1 := by
  rw [signVec, if_neg hj]

private theorem permAut_swap_signVec {a b : Fin k} (hab : a ≠ b) :
    SpCoord.permAut (Equiv.swap a b) (signVec (p := p) b) = signVec (p := p) a := by
  funext j
  rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hja : j = a
  · subst hja
    rw [Equiv.swap_apply_left, signVec_self, signVec_self]
  · have hjb : Equiv.swap a b j ≠ b := by
      intro h
      apply hja
      have h2 := (Equiv.swap_apply_eq_iff (x := a) (y := b) (z := j) (w := b)).1 h
      rwa [Equiv.swap_apply_right] at h2
    rw [signVec_of_ne hjb, signVec_of_ne hja]

private def pairIdx (a b : Fin k) (hab : a ≠ b) : {ij : Fin k × Fin k // ij.1 < ij.2} :=
  if h : a < b then ⟨(a, b), h⟩
  else ⟨(b, a), lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab)⟩

private theorem permAut_pairIdx {a b : Fin k} (hab : a ≠ b) :
    (SpCoord.permAut (p := p) (Equiv.swap (pairIdx a b hab).1.1 (pairIdx a b hab).1.2) :
        MulAut (Fin k → Multiplicative (ZMod p))) =
      SpCoord.permAut (p := p) (Equiv.swap a b) := by
  rw [pairIdx]
  split_ifs with h
  · rfl
  · rw [Equiv.swap_comm]

private theorem swap_eq_swap_of_lt {i j i' j' : Fin k} (hij : i < j) (hij' : i' < j')
    (h : Equiv.swap i j = Equiv.swap i' j') : i = i' ∧ j = j' := by
  have hsupp : ({i, j} : Finset (Fin k)) = {i', j'} := by
    rw [← Equiv.Perm.support_swap (ne_of_lt hij), ← Equiv.Perm.support_swap (ne_of_lt hij'), h]
  have hi : i = i' ∨ i = j' := by
    have h1 : i ∈ ({i', j'} : Finset (Fin k)) := by rw [← hsupp]; simp
    simpa using h1
  have hj : j = i' ∨ j = j' := by
    have h1 : j ∈ ({i', j'} : Finset (Fin k)) := by rw [← hsupp]; simp
    simpa using h1
  rcases hi with hi | hi
  · have hjj : j = j' := by
      rcases hj with hj | hj
      · exact absurd (hi.trans hj.symm) (ne_of_lt hij)
      · exact hj
    exact ⟨hi, hjj⟩
  · rcases hj with hj | hj
    · exfalso
      have hlt : j < i := by rw [hj, hi]; exact hij'
      exact lt_asymm hij hlt
    · exact absurd (hi.trans hj.symm) (ne_of_lt hij)

theorem finrank_polarPerp_iSup_eq_two {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ)
    (hkℓ : k + 1 = ℓ) (hS : IsPlaneSystem Q U) :
    Module.finrank F (polarPerp Q (⨆ j, U j)) = 2 := by
  have hsum : Module.finrank F ↥(⨆ j, U j) = 2 * k := by
    have h := hS.finrank_biSup (Finset.univ : Finset (Fin k))
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [show (⨆ j, U j : Submodule F V) = ⨆ j ∈ (Finset.univ : Finset (Fin k)), U j from by
      rw [← Finset.sup_eq_iSup, Finset.sup_univ_eq_iSup]]
    exact h
  have hcompl : IsCompl (⨆ j, U j) (polarPerp Q (⨆ j, U j)) := hS.isCompl_iSup
  have hV : Module.finrank F ↥(⨆ j, U j) + Module.finrank F (polarPerp Q (⨆ j, U j)) =
      Module.finrank F V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (s := (⨆ j, U j : Submodule F V)) (t := polarPerp Q (⨆ j, U j))
    rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h
    exact h.symm
  omega

theorem quad_add_eq_one {f f' : V} (hQf : Q f = 0) (hQf' : Q f' = 0)
    (hff' : QuadraticMap.polar Q f f' = 1) : Q (f + f') = 1 := by
  have h := QuadraticMap.map_add (Q : V → F) f f'
  rw [h, hQf, hQf', hff']
  simp

private theorem signChange_conj_delta (hF : IsCoherentFrame Q p U e E u c t)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e c) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (a l : Fin k) :
    signChange Q u v a * (τ (Pi.mulSingle l (Multiplicative.ofAdd 1)) : V ≃ₗ[F] V) *
        (signChange Q u v a)⁻¹ =
      (τ (SpCoord.sgnAut a (Pi.mulSingle l (Multiplicative.ofAdd 1))) : V ≃ₗ[F] V) := by
  rw [inv_eq_of_mul_eq_one_left (signChange_mul_self hF hv)]
  by_cases hla : l = a
  · rw [hla, SpCoord.sgnAut_mulSingle_self, map_inv, hτ a]
    exact signChange_conj_self hF hv
  · rw [SpCoord.sgnAut_mulSingle_of_ne hla, hτ l]
    exact signChange_conj_of_ne hF hv hla

private theorem frameSwap_conj_delta (hF : IsCoherentFrame Q p U e E u c t)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e c) {i j : Fin k} (hij : i < j)
    (l : Fin k) :
    frameSwap Q e u c t i j * (τ (Pi.mulSingle l (Multiplicative.ofAdd 1)) : V ≃ₗ[F] V) *
        (frameSwap Q e u c t i j)⁻¹ =
      (τ (SpCoord.permAut (Equiv.swap i j) (Pi.mulSingle l (Multiplicative.ofAdd 1))) :
        V ≃ₗ[F] V) := by
  have hij' : i ≠ j := ne_of_lt hij
  rw [inv_eq_of_mul_eq_one_left (frameSwap_mul_self hF hij')]
  by_cases hli : l = i
  · rw [hli, SpCoord.permAut_mulSingle, Equiv.swap_apply_left, hτ j, hτ i]
    exact frameSwap_conj_left hF hij'
  · by_cases hlj : l = j
    · rw [hlj, SpCoord.permAut_mulSingle, Equiv.swap_apply_right, hτ i, hτ j]
      exact frameSwap_conj_right hF hij'
    · rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hli hlj, hτ l]
      exact frameSwap_conj_of_ne hF hij' hli hlj

end Helpers

theorem ggTorusModelAt_of_coherentFrame_hyp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ) {k : ℕ} (hkℓ : k + 1 = ℓ)
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}
    {u : Fin k → V} {c t : F} (hF : IsCoherentFrame Q p U e E u c t) {f f' : V}
    (hf : f ∈ polarPerp Q (⨆ j, U j)) (hf' : f' ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hQf' : Q f' = 0) (hff' : QuadraticMap.polar Q f f' = 1) : GGTorusModelAt p E := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨by have h := hp.two_le; omega⟩
  haveI : Fact (2 < p) := ⟨by have h := hp.two_le; omega⟩
  haveI : IsMulCommutative ↥E := hF.isElemAbelian.1
  have hQv : Q (f + f') = 1 := quad_add_eq_one hQf hQf' hff'
  have hQv0 : Q (f + f') ≠ 0 := by rw [hQv]; exact one_ne_zero
  have hvW : f + f' ∈ polarPerp Q (⨆ j, U j) := by
    rw [mem_polarPerp_iff] at hf hf' ⊢
    intro y hy
    rw [polar_add_right, hf y hy, hf' y hy, add_zero]
  have hW2 : Module.finrank F (polarPerp Q (⨆ j, U j)) = 2 :=
    finrank_polarPerp_iSup_eq_two hdim hkℓ hF.toIsPlaneFrame.toIsPlaneSystem
  obtain ⟨τ, hτinj, hτrange, hτgen, hact⟩ := exists_frameTorus hF.toIsPlaneFrame hp
  let x : Fin k → ↥(orthDerived Q) := fun a => τ (signVec (p := p) a)
  have hxE : ∀ a, x a ∈ E := by
    intro a
    rw [← hτrange]
    exact MonoidHom.mem_range.mpr ⟨signVec (p := p) a, rfl⟩
  have hxpow : ∀ a, x a ^ p = 1 := fun a => hF.isElemAbelian.2 (x a) (hxE a)
  have hxpred : ∀ a, (∀ v ∈ U a, (x a : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x a : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v := by
    intro a
    constructor
    · intro v hv
      have h := hact (signVec (p := p) a) a v hv
      rw [signVec_self] at h
      simpa using h
    · intro j hja v hv
      have h := hact (signVec (p := p) a) j v hv
      rw [signVec_of_ne hja, toAdd_ofAdd, ZMod.val_one p, pow_one] at h
      simpa using h
  have hxtriple : ∀ a, x a ∈ E ∧ (∀ v ∈ U a, (x a : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x a : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v :=
    fun a => ⟨hxE a, hxpred a⟩
  let ι := Fin k ⊕ {ij : Fin k × Fin k // ij.1 < ij.2}
  have hι : Nonempty ι := ⟨Sum.inl ⟨0, by omega⟩⟩
  let w : ι → ↥(orthDerived Q) := fun i =>
    match i with
    | Sum.inl a => ⟨signChange Q u (f + f') a, signChange_mem_orthDerived hQ hF hQv0⟩
    | Sum.inr q => ⟨frameSwap Q e u c t q.1.1 q.1.2, frameSwap_mem_orthDerived hQ hdim (by omega)⟩
  let s : ι → MulAut (Fin k → Multiplicative (ZMod p)) := fun i =>
    match i with
    | Sum.inl a => SpCoord.sgnAut a
    | Sum.inr q => SpCoord.permAut (Equiv.swap q.1.1 q.1.2)
  let S : ι → Subgroup ↥(orthDerived Q) := fun i =>
    match i with
    | Sum.inl a => (supportedFixedDerived Q (x a : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)
    | Sum.inr q => pairBlock Q e t q.1.1 q.1.2 false
  have hws : ∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f) := by
    rintro (a | ⟨⟨i, j⟩, hij⟩) f
    · refine conj_eq_of_mulSingle τ (w (Sum.inl a)) (s (Sum.inl a)) ?_ f
      intro cc
      refine Subtype.ext ?_
      exact signChange_conj_delta hF hτgen hvW hQv0 a cc
    · exact conj_eq_of_mulSingle τ (w (Sum.inr ⟨(i, j), hij⟩)) (s (Sum.inr ⟨(i, j), hij⟩))
        (fun cc => Subtype.ext (frameSwap_conj_delta hF hτgen hij cc)) f
  have hs : ∀ i, s i * s i = 1 := by
    rintro (a | ⟨⟨i, j⟩, hij⟩)
    · rw [← _root_.sq]
      exact SpCoord.sgnAut_sq a
    · rw [← _root_.sq]
      exact SpCoord.permAut_swap_sq i j
  have hfix : ∀ i, Nat.card {f // s i f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p)) := by
    rintro (a | ⟨⟨i, j⟩, hij⟩)
    · exact SpCoord.card_fix_sgnAut hp hp2 a
    · exact SpCoord.card_fix_permAut_swap hp hp2 (ne_of_lt hij)
  have hsinj : Function.Injective s := by
    have hgone : (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ≠ 1 := by
      intro h
      have h1 := congrArg Multiplicative.toAdd h
      rw [toAdd_ofAdd, toAdd_one] at h1
      exact one_ne_zero h1
    have hginv : (Multiplicative.ofAdd (1 : ZMod p))⁻¹ ≠ Multiplicative.ofAdd (1 : ZMod p) := by
      intro h
      have h1 := congrArg Multiplicative.toAdd h
      rw [toAdd_inv, toAdd_ofAdd] at h1
      exact ZMod.neg_one_ne_one h1
    have hsgn : ∀ i l : Fin k, SpCoord.sgnAut i (Pi.mulSingle l (Multiplicative.ofAdd 1)) l =
        if l = i then (Multiplicative.ofAdd (1 : ZMod p))⁻¹ else Multiplicative.ofAdd 1 := by
      intro i l
      rw [SpCoord.sgnAut_apply]
      by_cases hli : l = i
      · subst hli
        rw [Function.update_self, Pi.mulSingle_eq_same, if_pos rfl]
      · rw [Function.update_of_ne hli, Pi.mulSingle_eq_same, if_neg hli]
    have hsp : ∀ (i : Fin k) (σ : Equiv.Perm (Fin k)), SpCoord.sgnAut i ≠
        (SpCoord.permAut σ : MulAut (Fin k → Multiplicative (ZMod p))) := by
      intro i σ h
      have h1 := congrFun (congrArg (fun φ : MulAut (Fin k → Multiplicative (ZMod p)) =>
        φ (Pi.mulSingle i (Multiplicative.ofAdd 1))) h) i
      rw [hsgn i i, if_pos rfl, SpCoord.permAut_mulSingle, Pi.mulSingle_apply] at h1
      split_ifs at h1
      · exact hginv h1
      · exact hgone (inv_eq_one.mp h1)
    rintro (a | ⟨⟨i, j⟩, hij⟩) (a' | ⟨⟨i', j'⟩, hij'⟩) h
    · change SpCoord.sgnAut a = SpCoord.sgnAut a' at h
      have h1 := congrFun (congrArg (fun φ : MulAut (Fin k → Multiplicative (ZMod p)) =>
        φ (Pi.mulSingle a (Multiplicative.ofAdd 1))) h) a
      rw [hsgn a a, hsgn a' a, if_pos rfl] at h1
      by_cases haa : a = a'
      · exact congrArg Sum.inl haa
      · rw [if_neg haa] at h1
        exact absurd h1 hginv
    · exact absurd h (hsp a (Equiv.swap i' j'))
    · exact absurd h.symm (hsp a' (Equiv.swap i j))
    · change SpCoord.permAut (Equiv.swap i j) = SpCoord.permAut (Equiv.swap i' j') at h
      have hσσ : Equiv.swap i j = Equiv.swap i' j' := by
        refine Equiv.ext fun l => ?_
        have h1 := congrArg (fun φ : MulAut (Fin k → Multiplicative (ZMod p)) =>
          φ (Pi.mulSingle l (Multiplicative.ofAdd 1))) h
        rw [SpCoord.permAut_mulSingle, SpCoord.permAut_mulSingle] at h1
        exact (SpCoord.mulSingle_ofAdd_eq_iff one_ne_zero h1).1
      obtain ⟨hii, hjj⟩ := swap_eq_swap_of_lt hij hij' hσσ
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hii hjj))
  have hwS : ∀ i, w i ∈ S i := by
    rintro (a | ⟨⟨i, j⟩, hij⟩)
    · refine Subgroup.mem_subgroupOf.mpr ?_
      exact reflect_mul_reflect_mem_signBlock hF.toIsPlaneFrame a hQ hp hp2 (hxtriple a)
        (Submodule.mem_sup_left (hF.mem a)) (Submodule.mem_sup_right hvW)
        (by rw [hF.quad_eq a]; exact hF.c_ne_zero) hQv0
    · have hij' : i ≠ j := ne_of_lt hij
      have hconj_i : w (Sum.inr ⟨(i, j), hij⟩) * e i * w (Sum.inr ⟨(i, j), hij⟩) = e j :=
        Subtype.ext (frameSwap_conj_left hF hij')
      have hconj_j : w (Sum.inr ⟨(i, j), hij⟩) * e j * w (Sum.inr ⟨(i, j), hij⟩) = e i :=
        Subtype.ext (frameSwap_conj_right hF hij')
      have hgg : w (Sum.inr ⟨(i, j), hij⟩) * w (Sum.inr ⟨(i, j), hij⟩) = 1 :=
        Subtype.ext (frameSwap_mul_self hF hij')
      have hcomm : e i * e j = e j * e i :=
        setLike_mul_comm (hF.toIsPlaneFrame.mem i) (hF.toIsPlaneFrame.mem j)
      have hkey : w (Sum.inr ⟨(i, j), hij⟩) * (e i * e j) * w (Sum.inr ⟨(i, j), hij⟩) =
          e i * e j := by
        have hstep : (w (Sum.inr ⟨(i, j), hij⟩) * e i * w (Sum.inr ⟨(i, j), hij⟩)) *
            (w (Sum.inr ⟨(i, j), hij⟩) * e j * w (Sum.inr ⟨(i, j), hij⟩)) = e j * e i := by
          rw [hconj_i, hconj_j]
        have hexp : (w (Sum.inr ⟨(i, j), hij⟩) * e i * w (Sum.inr ⟨(i, j), hij⟩)) *
            (w (Sum.inr ⟨(i, j), hij⟩) * e j * w (Sum.inr ⟨(i, j), hij⟩)) =
            w (Sum.inr ⟨(i, j), hij⟩) * (e i * e j) * w (Sum.inr ⟨(i, j), hij⟩) := by
          rw [show w (Sum.inr ⟨(i, j), hij⟩) * e i * w (Sum.inr ⟨(i, j), hij⟩) *
              (w (Sum.inr ⟨(i, j), hij⟩) * e j * w (Sum.inr ⟨(i, j), hij⟩)) =
              w (Sum.inr ⟨(i, j), hij⟩) * e i * (w (Sum.inr ⟨(i, j), hij⟩) *
                w (Sum.inr ⟨(i, j), hij⟩)) * e j * w (Sum.inr ⟨(i, j), hij⟩) from by group,
            hgg, mul_one]
          group
        rw [← hexp, hstep, hcomm]
      have hgy : w (Sum.inr ⟨(i, j), hij⟩) * (e i * e j) =
          (e i * e j) * w (Sum.inr ⟨(i, j), hij⟩) := by
        calc w (Sum.inr ⟨(i, j), hij⟩) * (e i * e j)
            = w (Sum.inr ⟨(i, j), hij⟩) * (e i * e j) * 1 := by rw [mul_one]
          _ = w (Sum.inr ⟨(i, j), hij⟩) * (e i * e j) *
              (w (Sum.inr ⟨(i, j), hij⟩) * w (Sum.inr ⟨(i, j), hij⟩)) := by rw [hgg]
          _ = (w (Sum.inr ⟨(i, j), hij⟩) * (e i * e j) * w (Sum.inr ⟨(i, j), hij⟩)) *
              w (Sum.inr ⟨(i, j), hij⟩) := by group
          _ = (e i * e j) * w (Sum.inr ⟨(i, j), hij⟩) := by rw [hkey]
      have hgP : ∀ y ∈ polarPerp Q (U i ⊔ U j),
          (w (Sum.inr ⟨(i, j), hij⟩) : V ≃ₗ[F] V) y = y :=
        fun y hy => frameSwap_apply_of_mem_polarPerp hF hy
      exact mem_pairBlock_of_mul_self hQ hp hp2 hpq hF hij' false hgy hgP hgg
  have hcomp : ∀ i, CFSG.Assembly.IsComponentOf (S i)
      (Subgroup.centralizer (τ '' {f | s i f = f})) := by
    rintro (a | ⟨⟨i, j⟩, hij⟩)
    · refine isComponentOf_signBlock hF.toIsPlaneFrame a hQ hp hp2 hW2 hf hQf hff' (hxtriple a)
        ?_ ?_
      · exact mem_image_fix_sgnAut hF.toIsPlaneFrame hp τ hτrange hact (hxE a) (hxpred a).1
      · exact image_fix_sgnAut_subset hp hp2 τ e hτgen
    · have hij' : i ≠ j := ne_of_lt hij
      refine isComponentOf_pairBlock hQ hp hp2 hpq hF hij' hF4 false ?_ ?_
      · refine mem_image_fix_swap τ e hτgen hij'
      · exact image_fix_swap_subset τ e hτgen hij'
  have hdvd : ∀ i, p ∣ Nat.card (S i) := by
    rintro (a | ⟨⟨i, j⟩, hij⟩)
    · exact dvd_card_signBlock hF.toIsPlaneFrame a hQ hp hp2 hW2 hf hQf hff' (hxtriple a)
    · exact dvd_card_pairBlock hQ hp hp2 hpq hF (ne_of_lt hij) hF4 false
  have hgen : ∀ j₀ : ι, (⨆ (i : ι) (_ : i ≠ j₀), S i) = ⊤ := by
    intro j₀
    have hxodd : ∀ a, OddOrderIsometry Q p (x a : V ≃ₗ[F] V) := fun a =>
      oddOrderIsometry_of_orthDerived_pow_eq_one hQ hp hp2 (hxpow a)
    have hxle : ∀ a, supportedFixedDerived Q (x a : V ≃ₗ[F] V) ≤ orthDerived Q := fun a =>
      (hxodd a).supportedFixedDerived_le_orthDerived
    have hGEN : orthDerived Q ≤ ⨆ a, supportedFixedDerived Q (x a : V ≃ₗ[F] V) :=
      orthDerived_le_iSup_supportedFixedDerived hQ hdim (by omega) hp hp2 hF.toIsPlaneFrame
        hf hf' hQf hQf' hff' hW2 hxpred hxE
    have hstep : (⨆ a, supportedFixedDerived Q (x a : V ≃ₗ[F] V)) ≤
        (⨆ (i : ι) (_ : i ≠ j₀), S i).map (orthDerived Q).subtype := by
      refine iSup_le fun a => ?_
      by_cases hja : Sum.inl a = j₀
      ·
        obtain ⟨b, hba⟩ : ∃ b : Fin k, b ≠ a := by
          refine Fintype.exists_ne_of_one_lt_card ?_ a
          simpa using (show 1 < k by omega)
        have hab : a ≠ b := hba.symm
        let q : {ij : Fin k × Fin k // ij.1 < ij.2} := pairIdx a b hab
        have hbne : Sum.inl b ≠ j₀ := by
          intro h
          exact hba (Sum.inl_injective (h.trans hja.symm))
        have hne : Sum.inr q ≠ j₀ := by
          rw [← hja]
          intro h
          cases h
        have hb_le : supportedFixedDerived Q (x b : V ≃ₗ[F] V) ≤
            (⨆ (i : ι) (_ : i ≠ j₀), S i).map (orthDerived Q).subtype := by
          intro y hy
          refine Subgroup.mem_map.mpr ⟨⟨y, hxle b hy⟩, ?_, rfl⟩
          exact Subgroup.mem_iSup_of_mem (Sum.inl b) (Subgroup.mem_iSup_of_mem hbne
            (Subgroup.mem_subgroupOf.mpr hy))
        have hgimg : (w (Sum.inr q) : V ≃ₗ[F] V) ∈
            (⨆ (i : ι) (_ : i ≠ j₀), S i).map (orthDerived Q).subtype := by
          refine Subgroup.mem_map.mpr ⟨w (Sum.inr q), ?_, rfl⟩
          exact Subgroup.mem_iSup_of_mem (Sum.inr q) (Subgroup.mem_iSup_of_mem hne
            (hwS (Sum.inr q)))
        have hconj : (w (Sum.inr q) : V ≃ₗ[F] V) * (x b : V ≃ₗ[F] V) *
            (w (Sum.inr q) : V ≃ₗ[F] V)⁻¹ = (x a : V ≃ₗ[F] V) := by
          have h1 := hws (Sum.inr q) (signVec (p := p) b)
          have h2 : s (Sum.inr q) (signVec (p := p) b) = signVec (p := p) a := by
            show SpCoord.permAut (Equiv.swap (pairIdx a b hab).1.1 (pairIdx a b hab).1.2)
              (signVec (p := p) b) = signVec (p := p) a
            rw [permAut_pairIdx hab, permAut_swap_signVec hab]
          have h3 : w (Sum.inr q) * τ (signVec (p := p) b) * (w (Sum.inr q))⁻¹ =
              τ (signVec (p := p) a) := by
            rw [← h2]
            exact h1
          exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) h3
        have himg_le : (supportedFixedDerived Q (x b : V ≃ₗ[F] V)).map
            (MulAut.conj (w (Sum.inr q) : V ≃ₗ[F] V)).toMonoidHom ≤
            (⨆ (i : ι) (_ : i ≠ j₀), S i).map (orthDerived Q).subtype := by
          intro z hz
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
          have hmem : (w (Sum.inr q) : V ≃ₗ[F] V) * y * (w (Sum.inr q) : V ≃ₗ[F] V)⁻¹ ∈
              (⨆ (i : ι) (_ : i ≠ j₀), S i).map (orthDerived Q).subtype :=
            mul_mem (mul_mem hgimg (hb_le hy)) (inv_mem hgimg)
          simpa [MulAut.conj_apply] using hmem
        have heq : supportedFixedDerived Q (x a : V ≃ₗ[F] V) =
            (supportedFixedDerived Q (x b : V ≃ₗ[F] V)).map
              (MulAut.conj (w (Sum.inr q) : V ≃ₗ[F] V)).toMonoidHom := by
          rw [← hconj]
          exact supportedFixedDerived_conj (hxodd b)
            (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q (w (Sum.inr q)).2)
        rw [heq]
        exact himg_le
      · intro y hy
        refine Subgroup.mem_map.mpr ⟨⟨y, hxle a hy⟩, ?_, rfl⟩
        exact Subgroup.mem_iSup_of_mem (Sum.inl a) (Subgroup.mem_iSup_of_mem hja
          (Subgroup.mem_subgroupOf.mpr hy))
    have hmain : orthDerived Q ≤ (⨆ (i : ι) (_ : i ≠ j₀), S i).map
        (orthDerived Q).subtype := hGEN.trans hstep
    refine eq_top_iff.2 fun z _ => ?_
    have hz : (z : V ≃ₗ[F] V) ∈ (⨆ (i : ι) (_ : i ≠ j₀), S i).map
        (orthDerived Q).subtype := hmain z.2
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    rw [← (Subtype.ext hyz : y = z)]
    exact hy
  exact ⟨k, τ, ι, w, s, S, hι, hτinj, hτrange, hws, hs, hfix, hsinj, hwS, hcomp, hdvd, hgen⟩

end CFSG.StandardType.OmNsRootGen

end
