module

public import CFSG.RankThree.PartOne.KC.OrthogonalAutSixSemilinear
public import CFSG.RankThree.PartOne.K159.RowFourType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth

public section

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

variable {K : Type*} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂]

theorem SemiSim.mapSub_suppPerp {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (T : SemiSim Q₁ Q₂) (P : Submodule K V₁) :
    T.mapSub (suppPerp Q₁ P) = suppPerp Q₂ (T.mapSub P) := by
  ext y
  rw [SemiSim.mem_mapSub, mem_suppPerp, mem_suppPerp]
  constructor
  · intro hy x hx
    have hx' : T.e.symm x ∈ P := T.mem_mapSub.mp hx
    calc
      polar Q₂ x y = polar Q₂ (T.e (T.e.symm x)) (T.e (T.e.symm y)) := by
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      _ = T.μ * T.σ (polar Q₁ (T.e.symm x) (T.e.symm y)) := T.polar_e _ _
      _ = 0 := by rw [hy (T.e.symm x) hx', map_zero, mul_zero]
  · intro hy p hp
    have hp' : T.e p ∈ T.mapSub P := T.e_mem_mapSub.mpr hp
    have h := hy (T.e p) hp'
    rw [← Equiv.apply_symm_apply T.e y, T.polar_e_eq_zero_iff] at h
    exact h



theorem SemiSim.mapSub_sup {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (T : SemiSim Q₁ Q₂) (P Q : Submodule K V₁) :
    T.mapSub (P ⊔ Q) = T.mapSub P ⊔ T.mapSub Q := by
  ext y
  constructor
  · intro hy
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp (T.mem_mapSub.mp hy)
    refine Submodule.mem_sup.mpr ⟨T.e p, T.e_mem_mapSub.mpr hp, T.e q,
      T.e_mem_mapSub.mpr hq, ?_⟩
    rw [← T.map_add', hpq, Equiv.apply_symm_apply]
  · intro hy
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
    refine T.mem_mapSub.mpr ?_
    rw [← hab, show T.e.symm (a + b) = T.e.symm a + T.e.symm b from T.symm.map_add' a b]
    exact Submodule.add_mem_sup (T.mem_mapSub.mp ha) (T.mem_mapSub.mp hb)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.GroupTheory.WeirSylow CFSG.RankThree.PartOne.K159
open CFSG.RankThree.PartOne.KCOrthogonalAut
open CFSG.LocalAnalysis.GLTheoremA.K155XOr

theorem exists_semisim_preserving_planes_of_normalizes_anchored_supportedDerived
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (W : Submodule K V) {m : Nat} (U : Fin m → Submodule K V)
    (hm : 2 ≤ m) (hK : 2 < Nat.card K)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2)
    (hU : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUdim : ∀ i, finrank K (U i) = 2)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (hspan : W ⊔ ⨆ i, U i = ⊤)
    (htype : ∀ i, IsPlusType (Q.comp (U i).subtype) ↔ ¬ IsPlusType (Q.comp W.subtype))
    (alpha : MulAut (orthDerived Q))
    (hnorm : ∀ i, ((supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q)).map
      alpha.toMonoidHom = (supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q)) :
    ∃ S : SemiSim Q Q,
      (∀ g : orthDerived Q, ∀ v : V,
        ((alpha g : orthDerived Q) : V ≃ₗ[K] V) v =
          S.e ((g : V ≃ₗ[K] V) (S.e.symm v))) ∧
      S.mapSub W = W ∧ ∀ i, S.mapSub (U i) = U i := by
  classical
  have hWpoly : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hUpoly : ∀ i, PolarNondegOn Q (U i) := fun i => polarNondegOn_of_nondegenerate (hU i)
  have hbinary : ∀ S T : Submodule K V, PolarNondegOn Q S → PolarNondegOn Q T →
      (∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0) → PolarNondegOn Q (S ⊔ T) := by
    intro S T hS hT horth
    have hSreg : (polarBilin (Q.comp S.subtype)).Nondegenerate := K159.nondegenerate_of_regOn hS
    have hTreg : (polarBilin (Q.comp T.subtype)).Nondegenerate := K159.nondegenerate_of_regOn hT
    have hdisj : Disjoint S T := by
      rw [Submodule.disjoint_def]
      intro x hx hx'
      exact hS x hx fun y hy => by rw [polar_comm]; exact horth y hy x hx'
    have hreg : (polarBilin (Q.comp (S ⊔ T).subtype)).Nondegenerate :=
      nondegenerate_polarBilin_of_isometryEquiv
        (K159.isometryEquivSup Q S T hdisj horth).symm
        (nondegenerate_polarBilin_prod hSreg hTreg)
    exact polarNondegOn_of_nondegenerate hreg
  have hUindep : iSupIndep U := by
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hxi hxj
    have hle : (⨆ (j) (_ : j ≠ i), U j) ≤ suppPerp Q (U i) := by
      refine iSup_le fun j => iSup_le fun hji => ?_
      intro y hy
      rw [mem_suppPerp]
      intro u hu
      exact hUU i j hji.symm u hu y hy
    exact hUpoly i x hxi fun y hy => by
      rw [polar_comm]
      exact mem_suppPerp.mp (hle hxj) y hy
  let S : Submodule K V := ⨆ i, U i
  have hUregAll : ∀ s : Finset (Fin m), PolarNondegOn Q (s.sup U) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro x hx _
        rw [Finset.sup_empty] at hx
        rw [Submodule.mem_bot] at hx
        rw [hx]
    | insert i s hi ih =>
        rw [Finset.sup_insert]
        refine hbinary (U i) (s.sup U) (hUpoly i) ih ?_
        intro x hx y hy
        have hle : s.sup U ≤ suppPerp Q (U i) := by
          refine Finset.sup_le fun j hj => ?_
          intro y hy
          rw [mem_suppPerp]
          intro u hu
          exact hUU i j (fun h => hi (h.symm ▸ hj)) u hu y hy
        exact mem_suppPerp.mp (hle hy) x hx
  have hSeq : Finset.univ.sup U = S := by
    rw [Finset.sup_eq_iSup]
    simp [S]
  have hSreg : PolarNondegOn Q S := by
    rw [← hSeq]
    exact hUregAll Finset.univ
  have hSdim : finrank K S = 2 * m := by
    have h := TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep (K := K) (M := V) (V := U) hUindep
    have h' : finrank K S = ∑ i, finrank K (U i) := h
    simp only [hUdim] at h'
    have h'' : finrank K S = m * 2 := by
      simpa [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h'
    rw [h'']
    omega
  have hSle : S ≤ suppPerp Q W := by
    change (⨆ i, U i) ≤ suppPerp Q W
    refine iSup_le fun i => ?_
    intro u hu
    rw [mem_suppPerp]
    intro w hw
    exact hWU i w hw u hu
  have hWSorth : ∀ w ∈ W, ∀ s ∈ S, polar Q w s = 0 := fun w hw s hs =>
    mem_suppPerp.mp (hSle hs) w hw
  have hWdisjS : Disjoint W S := by
    rw [Submodule.disjoint_def]
    intro x hxW hxS
    exact hWpoly x hxW fun y hy => by rw [polar_comm]; exact hWSorth y hy x hxS
  have hspanS : W ⊔ S = ⊤ := hspan
  have hVdim : finrank K V = 2 * (m + 1) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := K) W S
    rw [hspanS, hWdisjS.eq_bot, finrank_bot, hWdim, hSdim, finrank_top] at hdim
    omega
  have hregtop : PolarNondegOn Q (W ⊔ S) := hbinary W S hWpoly hSreg hWSorth
  have hQpoly : PolarNondegOn Q ⊤ := by
    rw [← hspanS]
    exact hregtop
  have hQtot : (polarBilin Q).Nondegenerate := by
    constructor
    · intro x hx
      exact hQpoly x (Submodule.mem_top) fun y _ => hx y
    · intro y hy
      exact hQpoly y (Submodule.mem_top) fun x _ => by rw [polar_comm]; exact hy x
  have hAUdisj : ∀ i, Disjoint W (U i) := fun i => by
    rw [Submodule.disjoint_def]
    intro x hxW hxU
    exact hWpoly x hxW fun y hy => by rw [polar_comm]; exact hWU i y hy x hxU
  have hAregAll : ∀ i, (polarBilin (Q.comp (W ⊔ U i).subtype)).Nondegenerate := fun i =>
    nondegenerate_polarBilin_of_isometryEquiv
      (K159.isometryEquivSup Q W (U i) (hAUdisj i) (hWU i)).symm
      (nondegenerate_polarBilin_prod hW (hU i))
  have hAdimAll : ∀ i, finrank K ↥(W ⊔ U i) = 4 := fun i => by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := K) W (U i)
    rw [(hAUdisj i).eq_bot, finrank_bot, hWdim, hUdim i] at hdim
    omega
  have hprodWU : ∀ i, IsPlusType ((Q.comp W.subtype).prod (Q.comp (U i).subtype)) ↔
      (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp (U i).subtype)) := fun i =>
    K159.isPlusType_prod_iff hW (hU i) (d₁ := 1) (d₂ := 1) le_rfl le_rfl
      (by rw [hWdim]) (by rw [hUdim i])
  have hone_type : ∀ i, ¬ (IsPlusType (Q.comp W.subtype) ↔
      IsPlusType (Q.comp (U i).subtype)) := by
    intro i hiff
    by_cases hWp : IsPlusType (Q.comp W.subtype)
    · exact ((htype i).mp (hiff.mp hWp)) hWp
    · exact hWp (hiff.mpr ((htype i).mpr hWp))
  have hAminusAll : ∀ i, ¬ IsPlusType (Q.comp (W ⊔ U i).subtype) := by
    intro i hp
    have hp' : IsPlusType ((Q.comp W.subtype).prod (Q.comp (U i).subtype)) :=
      (isPlusType_congr (K159.isometryEquivSup Q W (U i) (hAUdisj i) (hWU i))).mp hp
    exact hone_type i ((hprodWU i).mp hp')
  have hdim : finrank K V = 6 ∨ 8 ≤ finrank K V := by
    rw [hVdim]
    omega
  have hnotPlus : finrank K V = 8 → ¬ IsPlusType Q := by
    intro hdimV8 hplus
    have hm3 : m = 3 := by
      rw [hVdim] at hdimV8
      omega
    subst hm3
    have hU12disj : Disjoint (U 1) (U 2) := by
      rw [Submodule.disjoint_def]
      intro x hx1 hx2
      exact hUpoly 1 x hx1 fun y hy => by
        rw [polar_comm]
        exact hUU 1 2 (by decide) y hy x hx2
    have hBreg : (polarBilin (Q.comp (U 1 ⊔ U 2).subtype)).Nondegenerate :=
      nondegenerate_polarBilin_of_isometryEquiv
        (K159.isometryEquivSup Q (U 1) (U 2) hU12disj (hUU 1 2 (by decide))).symm
        (nondegenerate_polarBilin_prod (hU 1) (hU 2))
    have hBdim : finrank K ↥(U 1 ⊔ U 2) = 4 := by
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := K) (U 1) (U 2)
      rw [hU12disj.eq_bot, finrank_bot, hUdim 1, hUdim 2] at hdim
      omega
    have hBplus : IsPlusType (Q.comp (U 1 ⊔ U 2).subtype) := by
      have hprod := K159.isPlusType_prod_iff (hU 1) (hU 2) (d₁ := 1) (d₂ := 1) le_rfl le_rfl
        (by rw [hUdim 1]) (by rw [hUdim 2])
      have hiff : IsPlusType (Q.comp (U 1).subtype) ↔ IsPlusType (Q.comp (U 2).subtype) :=
        (htype 1).trans (htype 2).symm
      exact (isPlusType_congr
        (K159.isometryEquivSup Q (U 1) (U 2) hU12disj (hUU 1 2 (by decide)))).mpr
        (hprod.mpr hiff)
    have horthAB : ∀ a ∈ W ⊔ U 0, ∀ b ∈ U 1 ⊔ U 2, polar Q a b = 0 := by
      intro a ha b hb
      obtain ⟨w, hw, u0, hu0, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Submodule.mem_sup.mp hb
      rw [polar_add_left, polar_add_right, polar_add_right,
        hWU 1 w hw u1 hu1, hWU 2 w hw u2 hu2,
        hUU 0 1 (by decide) u0 hu0 u1 hu1, hUU 0 2 (by decide) u0 hu0 u2 hu2]
      ring
    have hdisjAB : Disjoint (W ⊔ U 0) (U 1 ⊔ U 2) := by
      rw [Submodule.disjoint_def]
      intro x hx hx'
      exact polarNondegOn_of_nondegenerate (hAregAll 0) x hx fun y hy => by
        rw [polar_comm]
        exact horthAB y hy x hx'
    have hnotprodAB : ¬ IsPlusType
        ((Q.comp (W ⊔ U 0).subtype).prod (Q.comp (U 1 ⊔ U 2).subtype)) := by
      intro hp
      have hprod := K159.isPlusType_prod_iff (hAregAll 0) hBreg (d₁ := 2) (d₂ := 2)
        (by norm_num) (by norm_num) (by rw [hAdimAll 0]) (by rw [hBdim])
      exact hAminusAll 0 ((hprod.mp hp).mpr hBplus)
    have hnotAB : ¬ IsPlusType (Q.comp ((W ⊔ U 0) ⊔ (U 1 ⊔ U 2)).subtype) := by
      intro hp
      exact hnotprodAB ((isPlusType_congr
        (K159.isometryEquivSup Q (W ⊔ U 0) (U 1 ⊔ U 2) hdisjAB horthAB)).mp hp)
    have hABtop : W ⊔ U 0 ⊔ (U 1 ⊔ U 2) = ⊤ := by
      rw [← hspan, iSup_fin_three]
      ac_rfl
    have hnotV : ¬ IsPlusType Q := by
      intro hp
      let eTop : (Q.comp (⊤ : Submodule K V).subtype).IsometryEquiv Q :=
        { toLinearEquiv := Submodule.topEquiv
          map_app' := fun _ => rfl }
      have hpAB : IsPlusType (Q.comp ((W ⊔ U 0) ⊔ (U 1 ⊔ U 2)).subtype) :=
        (isPlusType_congr ((K159.isometryOfEq Q hABtop).trans eTop)).mpr hp
      exact hnotAB hpAB
    exact hnotV hplus
  have hD4 : finrank K V = 8 → ¬ ∃ T : Submodule K V,
      finrank K T = 4 ∧ ∀ u ∈ T, Q u = 0 := by
    intro hdimV8
    have hnot := hnotPlus hdimV8
    rintro ⟨T, hTdim, hTsing⟩
    exact hnot ⟨T, by omega, hTsing⟩
  have hQne : ∃ v, Q v ≠ 0 := by
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hVdim]; omega)
    obtain ⟨x, hx0⟩ := exists_ne (0 : V)
    by_contra h
    push Not at h
    have hB : ∀ y, polarBilin Q x y = 0 := by
      intro y
      rw [polarBilin_apply_apply]
      simp [QuadraticMap.polar, h]
    exact hx0 (hQtot.1 x hB)
  let e : ProjOrthDerived Q ≃* orthDerived Q := orthProjEquiv hQne
  let αP : MulAut (ProjOrthDerived Q) := MulAut.congr e.symm alpha
  have hαP : ∀ p : ProjOrthDerived Q, e (αP p) = alpha (e p) := by
    intro p
    simp [αP, MulAut.congr_apply]
  have hsemilinear : InducedBySemilinear Q αP := by
    rcases hdim with hdim6 | hdim8
    · exact orthogonal_aut_semilinear_even_six Q hQtot hdim6 αP
    · exact orthogonal_aut_semilinear Q hQtot hdim8 hD4 αP
  obtain ⟨σ, F, hF, μ, hμ, hFQ, hind⟩ := hsemilinear
  have hα : ∀ g : orthDerived Q,
      ((alpha g : orthDerived Q) : V ≃ₗ[K] V) =
        semilinConj F σ hF (g : V ≃ₗ[K] V) := by
    intro g
    have hmem : semilinConj F σ hF (g : V ≃ₗ[K] V) ∈ orthDerived Q :=
      semilinConj_mem_orthDerived F σ hF μ hFQ g.2
    have hquot : αP (QuotientGroup.mk g) =
        QuotientGroup.mk
          (⟨semilinConj F σ hF (g : V ≃ₗ[K] V), hmem⟩ : orthDerived Q) :=
      hind g ⟨semilinConj F σ hF (g : V ≃ₗ[K] V), hmem⟩
        fun v => semilinConj_apply F σ hF (g : V ≃ₗ[K] V) v
    have h1 := congrArg e hquot
    rw [hαP] at h1
    have hg_e : e (QuotientGroup.mk g) = g := rfl
    have hg'_e : e (QuotientGroup.mk
        (⟨semilinConj F σ hF (g : V ≃ₗ[K] V), hmem⟩ : orthDerived Q)) =
        ⟨semilinConj F σ hF (g : V ≃ₗ[K] V), hmem⟩ := rfl
    rw [hg_e, hg'_e] at h1
    exact congrArg Subtype.val h1
  let Ssim : SemiSim Q Q :=
    { e := F.toEquiv
      σ := σ
      μ := μ
      μ_ne_zero := hμ
      map_add' := F.map_add
      map_smul' := hF
      map_quad' := hFQ }
  have hHle : ∀ i, supportedDerived Q (W ⊔ U i) ≤ orthDerived Q :=
    fun i => supportedDerived_le_orthDerived_of_regular (hAregAll i)
  have hraw : ∀ i, (supportedDerived Q (W ⊔ U i)).map (semilinConj F σ hF) =
      supportedDerived Q (W ⊔ U i) := by
    intro i
    have hmapped := congrArg
      (fun J : Subgroup ↥(orthDerived Q) => J.map (orthDerived Q).subtype) (hnorm i)
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (hHle i)] at hmapped
    have hcomp : (orthDerived Q).subtype.comp alpha.toMonoidHom =
        (semilinConj F σ hF).comp (orthDerived Q).subtype := by
      ext x v
      exact congrArg (fun f : V ≃ₗ[K] V => f v) (hα x)
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (hHle i)] at hmapped
    exact hmapped
  have hImage : ∀ p, F '' ((W ⊔ U p : Submodule K V) : Set V) =
      ((W ⊔ U p : Submodule K V) : Set V) := by
    intro i
    exact semilin_image_eq_of_normalizes_supportedDerived hK hQtot (hAregAll i)
      (by rw [hAdimAll i]; norm_num) F σ hF μ hFQ (hraw i)
  have hmapA : ∀ i, Ssim.mapSub (W ⊔ U i) = W ⊔ U i := by
    intro i
    apply SetLike.coe_injective
    rw [SemiSim.coe_mapSub]
    change F '' ((W ⊔ U i : Submodule K V) : Set V) =
      ((W ⊔ U i : Submodule K V) : Set V)
    exact hImage i
  have hmap_inf : ∀ P R : Submodule K V, Ssim.mapSub (P ⊓ R) =
      Ssim.mapSub P ⊓ Ssim.mapSub R := by
    intro P R
    ext y
    rfl
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, i1] at hv
  have hWle : W ≤ suppPerp Q (U i0) := by
    intro w hw
    rw [mem_suppPerp]
    intro u hu
    rw [polar_comm]
    exact hWU i0 w hw u hu
  have hU1le : U i1 ≤ suppPerp Q (U i0) := by
    intro u hu
    rw [mem_suppPerp]
    intro v hv
    exact hUU i0 i1 hi01 v hv u hu
  have hA1le : W ⊔ U i1 ≤ suppPerp Q (U i0) := sup_le hWle hU1le
  have hdisjU0A1 : Disjoint (U i0) (W ⊔ U i1) :=
    (isCompl_suppPerp (hUpoly i0)).disjoint.mono_right hA1le
  have hWrecover : (W ⊔ U i0) ⊓ (W ⊔ U i1) = W := by
    rw [sup_inf_assoc_of_le (U i0) (show W ≤ W ⊔ U i1 from le_sup_left)]
    rw [hdisjU0A1.eq_bot, sup_bot_eq]
  have hmapW : Ssim.mapSub W = W := by
    rw [← hWrecover]
    rw [hmap_inf (W ⊔ U i0) (W ⊔ U i1), hmapA i0, hmapA i1]
  have hmapWperp : Ssim.mapSub (suppPerp Q W) = suppPerp Q W := by
    rw [SemiSim.mapSub_suppPerp, hmapW]
  have hmapUi : ∀ i, Ssim.mapSub (U i) = U i := by
    intro i
    have hUi_inter : (W ⊔ U i) ⊓ suppPerp Q W = U i := by
      rw [sup_comm W (U i)]
      rw [sup_inf_assoc_of_le W (show U i ≤ suppPerp Q W from by
        intro u hu
        rw [mem_suppPerp]
        intro w hw
        exact hWU i w hw u hu)]
      rw [(isCompl_suppPerp hWpoly).inf_eq_bot, sup_bot_eq]
    rw [← hUi_inter]
    rw [hmap_inf (W ⊔ U i) (suppPerp Q W), hmapA i, hmapWperp]
  refine ⟨Ssim, ?_, hmapW, hmapUi⟩
  intro g v
  change ((alpha g : orthDerived Q) : V ≃ₗ[K] V) v =
    F ((g : V ≃ₗ[K] V) (F.symm v))
  rw [hα g, semilinConj_apply]


section ProdIncl

variable {K : Type*} [Field K] {V E : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup E] [Module K E] {Q : QuadraticForm K V} {R : QuadraticForm K E}

theorem prodCongr_one_mem_orthDerived {g : orthDerived Q} :
    (g : V ≃ₗ[K] V).prodCongr (LinearEquiv.refl K E) ∈ orthDerived (Q.prod R) := by
  let inclGL : (V ≃ₗ[K] V) →* ((V × E) ≃ₗ[K] (V × E)) :=
    { toFun := fun x => x.prodCongr (LinearEquiv.refl K E)
      map_one' := by ext z <;> simp
      map_mul' := by intro x y; ext z <;> simp [LinearEquiv.prodCongr_apply] }
  have hO : (TauCeti.QuadraticMap.orthogonalGroup Q).map inclGL ≤
      TauCeti.QuadraticMap.orthogonalGroup (Q.prod R) := by
    rintro _ ⟨x, hx, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ?_
    intro z
    obtain ⟨v, w⟩ := z
    simp [inclGL, LinearEquiv.prodCongr_apply, QuadraticMap.prod_apply,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hx v]
  have hΩ : (orthDerived Q).map inclGL ≤ orthDerived (Q.prod R) := by
    rw [orthDerived, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hO hO
  exact hΩ ⟨g, g.2, rfl⟩

@[expose] noncomputable def orthDerivedProdIncl :
    orthDerived Q →* orthDerived (Q.prod R) where
  toFun g := ⟨(g : V ≃ₗ[K] V).prodCongr (LinearEquiv.refl K E),
    prodCongr_one_mem_orthDerived (Q := Q) (R := R)⟩
  map_one' := Subtype.ext (by ext z <;> simp)
  map_mul' g h := Subtype.ext (by ext z <;> simp [LinearEquiv.prodCongr_apply])

@[simp]
theorem coe_orthDerivedProdIncl (g : orthDerived Q) :
    ((orthDerivedProdIncl (Q := Q) (R := R) g : orthDerived (Q.prod R)) :
      (V × E) ≃ₗ[K] (V × E)) =
      (g : V ≃ₗ[K] V).prodCongr (LinearEquiv.refl K E) :=
  rfl

end ProdIncl


section Extension

variable {K : Type*} [Field K] [Finite K]
  {V E : Type*} [AddCommGroup V] [Module K V] [AddCommGroup E] [Module K E]
  [FiniteDimensional K V] [FiniteDimensional K E]
  {Q : QuadraticForm K V} {R : QuadraticForm K E}

theorem exists_semisim_extension_prod_isometric
    (S : SemiSim Q Q) (alpha : MulAut (orthDerived Q))
    (hα : ∀ g : orthDerived Q, ∀ v : V,
      ((alpha g : orthDerived Q) : V ≃ₗ[K] V) v =
        S.e ((g : V ≃ₗ[K] V) (S.e.symm v)))
    (U : Submodule K V) (hU : S.mapSub U = U)
    (j : R.IsometryEquiv (Q.comp U.subtype)) :
    ∃ (T : SemiSim (Q.prod R) (Q.prod R))
      (beta : MulAut (orthDerived (Q.prod R))),
      T.σ = S.σ ∧ T.μ = S.μ ∧
      (∀ h z, ((beta h : orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) z =
        T.e ((h : (V × E) ≃ₗ[K] (V × E)) (T.e.symm z))) ∧
      (∀ g : orthDerived Q,
        beta (orthDerivedProdIncl (Q := Q) (R := R) g) =
          orthDerivedProdIncl (Q := Q) (R := R) (alpha g)) ∧
      (∀ P : Submodule K V, S.mapSub P = P → T.mapSub (P.prod ⊥) = P.prod ⊥) ∧
      T.mapSub ((⊥ : Submodule K V).prod (⊤ : Submodule K E)) =
        (⊥ : Submodule K V).prod (⊤ : Submodule K E) ∧
      (∀ R0 : Submodule K (V × E), T.mapSub R0 = R0 →
        ((supportedDerived (Q.prod R) R0).subgroupOf (orthDerived (Q.prod R))).map
          beta.toMonoidHom =
        (supportedDerived (Q.prod R) R0).subgroupOf (orthDerived (Q.prod R))) := by
  obtain ⟨T, hTσ, hTμ, hT1, hT2, hT0⟩ :=
    SemiSim.exists_extension_prod_isometric S U hU j
  let F : (V × E) ≃+ (V × E) :=
    { toFun := T.e
      invFun := T.e.symm
      left_inv := fun z => T.e.left_inv z
      right_inv := fun z => T.e.right_inv z
      map_add' := T.map_add' }
  have hF : ∀ (c : K) (z : V × E), F (c • z) = T.σ c • F z := fun c z => T.map_smul' c z
  have hFQ : ∀ z : V × E, (Q.prod R) (F z) = T.μ * T.σ ((Q.prod R) z) :=
    fun z => T.map_quad' z
  let betaHom : orthDerived (Q.prod R) →* orthDerived (Q.prod R) :=
    semilinOrth F T.σ hF T.μ hFQ
  let beta : MulAut (orthDerived (Q.prod R)) :=
    MulEquiv.ofBijective betaHom
      ⟨semilinOrth_injective F T.σ hF T.μ hFQ,
        semilinOrth_surjective F T.σ hF T.μ hFQ⟩
  have hbeta_apply : ∀ (h : orthDerived (Q.prod R)) (z : V × E),
      ((beta h : orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) z =
        T.e ((h : (V × E) ≃ₗ[K] (V × E)) (T.e.symm z)) := by
    intro h z
    have h1 : ((beta h : orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) =
        semilinConj F T.σ hF (h : (V × E) ≃ₗ[K] (V × E)) := by
      change ((betaHom h : orthDerived (Q.prod R)) :
        (V × E) ≃ₗ[K] (V × E)) = _
      exact semilinOrth_apply F T.σ hF T.μ hFQ h
    rw [h1, semilinConj_apply]
    rfl
  let Cfun : E → E := fun w => (T.e (0, w)).2
  have hTcoord : ∀ v w, T.e (v, w) = (S.e v, Cfun w) := by
    intro v w
    have h2 : (T.e (v, w)).2 = (T.e (0, w)).2 := by
      apply EquivLike.injective j
      apply Subtype.ext
      rw [hT2 v w, hT2 0 w]
    exact Prod.ext (hT1 v w) h2
  have hC0 : Cfun 0 = 0 := by
    have h := congrArg Prod.snd (hT0 0)
    simpa [Cfun] using h
  have hCinj : Function.Injective Cfun := by
    intro w1 w2 hw
    have hz : T.e (0, w1) = T.e (0, w2) := by
      rw [hTcoord 0 w1, hTcoord 0 w2, hw]
    exact congrArg Prod.snd (T.e.injective hz)
  have hCsurj : Function.Surjective Cfun := by
    intro y
    let z : V × E := T.e.symm (0, y)
    have hz : T.e z = (0, y) := T.e.apply_symm_apply (0, y)
    have hz1 : z.1 = 0 := by
      have h := congrArg Prod.fst hz
      rw [hTcoord z.1 z.2] at h
      exact S.e.injective (by simpa [SemiSim.e_zero S] using h)
    refine ⟨z.2, ?_⟩
    have hz' : T.e (0, z.2) = (0, y) := by
      rw [← show z = (0, z.2) from Prod.ext hz1 rfl]
      exact hz
    exact congrArg Prod.snd hz'
  let C : E ≃ E := Equiv.ofBijective Cfun ⟨hCinj, hCsurj⟩
  have hC_apply : ∀ w, C w = Cfun w := fun w => rfl
  have hTsymm : ∀ x y, T.e.symm (x, y) = (S.e.symm x, C.symm y) := by
    intro x y
    apply T.e.injective
    rw [T.e.apply_symm_apply, hTcoord]
    refine Prod.ext (Equiv.apply_symm_apply S.e x).symm ?_
    simp only [Prod.snd]
    rw [← hC_apply]
    exact (Equiv.apply_symm_apply C y).symm
  have hbeta_incl : ∀ g : orthDerived Q,
      beta (orthDerivedProdIncl (Q := Q) (R := R) g) =
        orthDerivedProdIncl (Q := Q) (R := R) (alpha g) := by
    intro g
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    obtain ⟨x, y⟩ := z
    rw [hbeta_apply]
    change T.e (((orthDerivedProdIncl (Q := Q) (R := R) g :
        orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) (T.e.symm (x, y))) =
      (((orthDerivedProdIncl (Q := Q) (R := R) (alpha g) :
        orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) (x, y))
    rw [coe_orthDerivedProdIncl, coe_orthDerivedProdIncl, hTsymm,
      LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_apply, hTcoord]
    simp only [Prod.fst, Prod.snd, LinearEquiv.refl_apply]
    rw [hα g x]
    refine Prod.ext rfl ?_
    simp only [Prod.snd]
    rw [← hC_apply]
    exact Equiv.apply_symm_apply C y
  have hprodBot : ∀ P : Submodule K V, S.mapSub P = P →
      T.mapSub (P.prod ⊥) = P.prod ⊥ := by
    intro P hP
    apply SetLike.coe_injective
    rw [SemiSim.coe_mapSub]
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      change p ∈ P.prod (⊥ : Submodule K E) at hp
      rw [Submodule.mem_prod] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Submodule.mem_bot] at hp2
      change T.e p ∈ P.prod (⊥ : Submodule K E)
      rw [Submodule.mem_prod, Submodule.mem_bot, hTcoord, hp2, hC0]
      simp only [Prod.fst, Prod.snd]
      refine ⟨?_, trivial⟩
      have hmem : S.e p.1 ∈ S.mapSub P := S.e_mem_mapSub.mpr hp1
      rwa [hP] at hmem
    · intro hz
      change z ∈ P.prod (⊥ : Submodule K E) at hz
      rw [Submodule.mem_prod] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Submodule.mem_bot] at hz2
      refine ⟨(S.e.symm z.1, 0), ?_, ?_⟩
      · change (S.e.symm z.1, 0) ∈ P.prod (⊥ : Submodule K E)
        rw [Submodule.mem_prod, Submodule.mem_bot]
        refine ⟨?_, rfl⟩
        have hmem : z.1 ∈ S.mapSub P := by rw [hP]; exact hz1
        exact S.mem_mapSub.mp hmem
      · rw [hTcoord, hC0]
        exact Prod.ext (Equiv.apply_symm_apply S.e z.1) hz2.symm
  have hprodTop : T.mapSub ((⊥ : Submodule K V).prod (⊤ : Submodule K E)) =
      (⊥ : Submodule K V).prod (⊤ : Submodule K E) := by
    apply SetLike.coe_injective
    rw [SemiSim.coe_mapSub]
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      change p ∈ (⊥ : Submodule K V).prod (⊤ : Submodule K E) at hp
      rw [Submodule.mem_prod] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Submodule.mem_bot] at hp1
      change T.e p ∈ (⊥ : Submodule K V).prod (⊤ : Submodule K E)
      rw [Submodule.mem_prod, hTcoord, hp1, SemiSim.e_zero]
      exact ⟨rfl, Submodule.mem_top⟩
    · intro hz
      change z ∈ (⊥ : Submodule K V).prod (⊤ : Submodule K E) at hz
      rw [Submodule.mem_prod] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Submodule.mem_bot] at hz1
      refine ⟨(0, C.symm z.2), ?_, ?_⟩
      · change (0, C.symm z.2) ∈ (⊥ : Submodule K V).prod (⊤ : Submodule K E)
        rw [Submodule.mem_prod]
        exact ⟨rfl, Submodule.mem_top⟩
      · rw [hTcoord, SemiSim.e_zero, ← hC_apply]
        exact Prod.ext hz1.symm (Equiv.apply_symm_apply C z.2)
  have hnormalizes : ∀ R0 : Submodule K (V × E), T.mapSub R0 = R0 →
      ((supportedDerived (Q.prod R) R0).subgroupOf (orthDerived (Q.prod R))).map
        beta.toMonoidHom =
      (supportedDerived (Q.prod R) R0).subgroupOf (orthDerived (Q.prod R)) := by
    intro R0 hR0
    let H : Subgroup ((V × E) ≃ₗ[K] (V × E)) := supportedDerived (Q.prod R) R0
    have hFimg : F '' (R0 : Set (V × E)) = (R0 : Set (V × E)) := by
      have hset : (T.e '' (R0 : Set (V × E))) = (R0 : Set (V × E)) := by
        rw [← SemiSim.coe_mapSub T R0]
        exact congrArg (fun S : Submodule K (V × E) => (S : Set (V × E))) hR0
      exact hset
    have hraw : H.map (semilinConj F T.σ hF) = H :=
      map_supportedDerived_semilinConj_of_image_eq F T.σ hF T.μ T.μ_ne_zero hFQ hFimg
    have hbeta_gl : ∀ h : orthDerived (Q.prod R),
        ((beta h : orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) =
          semilinConj F T.σ hF (h : (V × E) ≃ₗ[K] (V × E)) := by
      intro h
      change ((betaHom h : orthDerived (Q.prod R)) :
        (V × E) ≃ₗ[K] (V × E)) = _
      exact semilinOrth_apply F T.σ hF T.μ hFQ h
    have hle : (H.subgroupOf (orthDerived (Q.prod R))).map beta.toMonoidHom ≤
        H.subgroupOf (orthDerived (Q.prod R)) := by
      rintro _ ⟨x, hx, rfl⟩
      change ((beta x : orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) ∈ H
      rw [hbeta_gl x]
      have hmem : semilinConj F T.σ hF (x : (V × E) ≃ₗ[K] (V × E)) ∈
          H.map (semilinConj F T.σ hF) := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hraw] at hmem
    haveI : Finite (V × E) := Module.finite_of_finite K
    haveI : Finite ((V × E) ≃ₗ[K] (V × E)) :=
      Finite.of_injective (fun e : (V × E) ≃ₗ[K] (V × E) => (e : (V × E) → (V × E)))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    have hcard : Nat.card (H.subgroupOf (orthDerived (Q.prod R))) ≤
        Nat.card ((H.subgroupOf (orthDerived (Q.prod R))).map beta.toMonoidHom) := by
      have hmapcard : Nat.card ((H.subgroupOf (orthDerived (Q.prod R))).map beta.toMonoidHom) =
          Nat.card (H.subgroupOf (orthDerived (Q.prod R))) :=
        Subgroup.card_map_of_injective (f := beta.toMonoidHom)
          (fun a b h => beta.injective (by simpa using h))
      exact hmapcard.ge
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  exact ⟨T, beta, hTσ, hTμ, hbeta_apply, hbeta_incl, hprodBot, hprodTop, hnormalizes⟩

end Extension


theorem exists_anchored_calibration_prod_extension
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V E : Type} [AddCommGroup V] [Module K V] [AddCommGroup E] [Module K E]
    [FiniteDimensional K V] [FiniteDimensional K E]
    (Q : QuadraticForm K V) (W : Submodule K V) {m : Nat} (U : Fin m → Submodule K V)
    (hm : 2 ≤ m) (hK : 2 < Nat.card K)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2)
    (hU : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUdim : ∀ i, finrank K (U i) = 2)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (hspan : W ⊔ ⨆ i, U i = ⊤)
    (htype : ∀ i, IsPlusType (Q.comp (U i).subtype) ↔ ¬ IsPlusType (Q.comp W.subtype))
    (alpha : MulAut (orthDerived Q))
    (hnorm : ∀ i, ((supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q)).map
      alpha.toMonoidHom = (supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q))
    (R : QuadraticForm K E) (o : Fin m) (j : R.IsometryEquiv (Q.comp (U o).subtype)) :
    ∃ (S : SemiSim Q Q) (T : SemiSim (Q.prod R) (Q.prod R))
      (beta : MulAut (orthDerived (Q.prod R))),
      (∀ g : orthDerived Q, ∀ v : V,
        ((alpha g : orthDerived Q) : V ≃ₗ[K] V) v =
          S.e ((g : V ≃ₗ[K] V) (S.e.symm v))) ∧
      S.mapSub W = W ∧
      (∀ i, S.mapSub (U i) = U i) ∧
      T.σ = S.σ ∧ T.μ = S.μ ∧
      (∀ h z, ((beta h : orthDerived (Q.prod R)) : (V × E) ≃ₗ[K] (V × E)) z =
        T.e ((h : (V × E) ≃ₗ[K] (V × E)) (T.e.symm z))) ∧
      (∀ g : orthDerived Q,
        beta (orthDerivedProdIncl (Q := Q) (R := R) g) =
          orthDerivedProdIncl (Q := Q) (R := R) (alpha g)) ∧
      T.mapSub (W.prod ⊥) = W.prod ⊥ ∧
      (∀ i, T.mapSub ((U i).prod ⊥) = (U i).prod ⊥) ∧
      T.mapSub ((⊥ : Submodule K V).prod (⊤ : Submodule K E)) =
        (⊥ : Submodule K V).prod (⊤ : Submodule K E) ∧
      (∀ P : Submodule K V, S.mapSub P = P → T.mapSub (P.prod ⊥) = P.prod ⊥) ∧
      (∀ P : Submodule K V, S.mapSub P = P →
        T.mapSub ((P.prod ⊥) ⊔ ((⊥ : Submodule K V).prod (⊤ : Submodule K E))) =
          (P.prod ⊥) ⊔ ((⊥ : Submodule K V).prod (⊤ : Submodule K E))) ∧
      (∀ R0 : Submodule K (V × E), T.mapSub R0 = R0 →
        ((supportedDerived (Q.prod R) R0).subgroupOf (orthDerived (Q.prod R))).map
          beta.toMonoidHom =
        (supportedDerived (Q.prod R) R0).subgroupOf (orthDerived (Q.prod R))) := by
  obtain ⟨S, hα, hSW, hSU⟩ :=
    exists_semisim_preserving_planes_of_normalizes_anchored_supportedDerived
      Q W U hm hK hW hWdim hU hUdim hWU hUU hspan htype alpha hnorm
  obtain ⟨T, beta, hTσ, hTμ, hbeta_apply, hbeta_incl, hprodBot, hprodTop, hnormalizes⟩ :=
    exists_semisim_extension_prod_isometric S alpha hα (U o) (hSU o) j
  refine ⟨S, T, beta, hα, hSW, hSU, hTσ, hTμ, hbeta_apply, hbeta_incl, ?_, ?_, hprodTop,
    hprodBot, ?_, hnormalizes⟩
  · exact hprodBot W hSW
  · intro i
    exact hprodBot (U i) (hSU i)
  · intro P hP
    rw [SemiSim.mapSub_sup, hprodBot P hP, hprodTop]

end CFSG.RankThree.PartOne.KCOrthogonal
