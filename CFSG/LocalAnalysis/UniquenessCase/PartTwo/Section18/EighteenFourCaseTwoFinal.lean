module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseTwoG26
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge
public import CFSG.GroupTheory.PerfectCentralSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement
open CFSG.GroupTheory (exists_mQuot_two_of_mem_aSet_two mQuot_le_one_of_coset_cover
  mQuot_top_eq_rkIdx)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L K : Subgroup G}

theorem exists_gammaSet_four_of_aSet_two {D : Data G} {V A : Subgroup G}
    (hV : IsElemAbelian 2 V)
    (hA2 : barSub ⊥ V hV A ∈ calABar 2 D.M ⊥ V hV)
    (ha2 : aBar D.M ⊥ V hV = 2) (hAst : A ≤ stabTil ⊥ V) :
    ∃ B : Subgroup G, B ≤ A ∧ E3.mQuot A B = 2 ∧
      CFSG.Quasithin.fixV (barSub ⊥ V hV B) ≠ CFSG.Quasithin.fixV (barSub ⊥ V hV A) := by
  obtain ⟨C, hCA2, hmq2, hfix⟩ := exists_mQuot_two_of_mem_aSet_two (W := Vtil ⊥ V hV) hA2 ha2
  have hbar : barSub ⊥ V hV (preBarSub A ⊥ V hV C) = C := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hCA2
  refine ⟨preBarSub A ⊥ V hV C, inf_le_left, ?_, ?_⟩
  · rw [show E3.mQuot A (preBarSub A ⊥ V hV C) = E3.mQuot (barSub ⊥ V hV A) C from
      (mQuot_barSub_preBarSub_gen hV hAst (hbar ▸ hCA2)).symm]
    exact hmq2
  · rw [hbar]
    exact hfix

theorem inf_centralizer_le_conjSubgroup {D : Data G} {V B : Subgroup G} {g : G}
    (hV : IsElemAbelian 2 V) (h62 : Hyp62 D.M ⊥ V)
    (hB : B ≤ conjSubgroup V g) (hBM : B ≤ D.M)
    (hmVgB : E3.mQuot (conjSubgroup V g) B = 4) (hr : (4 : ℕ∞) < rMV D.M V) :
    V ⊓ Subgroup.centralizer (B : Set G) ≤ conjSubgroup D.M g := by
  have hD : B ≤ conjSubgroup V g ⊓ D.M := le_inf hB hBM
  have hr' : ((E3.mQuot (conjSubgroup V g) B + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
    rw [show mSub (⊥ : Subgroup G) = 0 from CFSG.Quasithin.rk_bot, add_zero, hmVgB]
    exact hr
  have h := six_two_one h62 hD hr'
  have hBst : B ≤ stabTil ⊥ V := hBM.trans (le_stabTil h62.normalizer_eq.ge
    (by rw [Subgroup.normalizer_eq_top]; exact le_top))
  rwa [preCTilde_bot_eq hV hBst] at h

theorem fixV_actTil_zpowers_eq_imgTil {D : Data G} {V B : Subgroup G} {g : G} {u' : G}
    (hV : IsElemAbelian 2 V) (hmBar : mBar D.M ⊥ V hV = 4)
    (hu'M : u' ∈ D.M) (hu'st : u' ∈ stabTil ⊥ V) (hu'2 : u' * u' = 1)
    (hu'notC : u' ∉ Subgroup.centralizer (V : Set G))
    (hB'V : conjSubgroup B g⁻¹ ≤ V) (hmB' : E3.mQuot V (conjSubgroup B g⁻¹) = 4)
    (hu'B' : u' ∈ Subgroup.centralizer (conjSubgroup B g⁻¹ : Set G)) :
    fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨u', hu'st⟩)) =
      imgTil ⊥ V hV (conjSubgroup B g⁻¹) := by
  classical
  set phi : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨u', hu'st⟩ with hphidef
  have hphiM : phi ∈ Mbar D.M ⊥ V hV := actTil_mem_barSub ⊥ V hV hu'M hu'st
  have hphi2 : phi ^ 2 = 1 := by
    rw [hphidef]
    have h1 : (⟨u', hu'st⟩ : ↥(stabTil ⊥ V)) ^ 2 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hu'2
    calc actTil ⊥ V hV ⟨u', hu'st⟩ ^ 2 = actTil ⊥ V hV (⟨u', hu'st⟩ ^ 2) := by rw [map_pow]
      _ = 1 := by rw [h1, map_one]
  have hphine : phi ≠ 1 := by
    intro h1
    apply hu'notC
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h2 := (actTil_eq_one_iff ⊥ V hV ⟨u', hu'st⟩).1 h1 v hv
    rw [Subgroup.mem_bot] at h2
    calc v * u' = (u' * v * u'⁻¹) * u' := by
          rw [show u' * v * u'⁻¹ = (u' * v * u'⁻¹ * v⁻¹) * v from by group, h2, one_mul]
      _ = u' * v := by group
  have hphifix : ∀ q ∈ imgTil ⊥ V hV (conjSubgroup B g⁻¹), phi q = q := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := (mem_imgTil ⊥ V hV (conjSubgroup B g⁻¹) q).1 hq
    rw [← hxq, hphidef, actTil_mk, mkTil_eq_iff, actStab_apply_val]
    have hcomm : x.val * u' = u' * x.val :=
      (Subgroup.mem_centralizer_iff.1 hu'B') _ hx
    rw [show u' * x.val * u'⁻¹ * x.val⁻¹ = 1 by rw [← hcomm]; group]
    simp
  have hfix1 : imgTil ⊥ V hV (conjSubgroup B g⁻¹) ≤ fixV (Subgroup.zpowers phi) := by
    intro q hq
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
    exact hphifix q hq
  have hphip2 : IsPGroup 2 (Subgroup.zpowers phi) := by
    have hdvd : orderOf phi ∣ 2 := orderOf_dvd_of_pow_eq_one hphi2
    have hord : orderOf phi = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hphine
      · exact h
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hzp1 : Subgroup.zpowers phi ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hphine
  have hge : mBar D.M ⊥ V hV ≤ rkIdx (fixV (Subgroup.zpowers phi)) := by
    have h := CFSG.Quasithin.E3.mParam_le_rkIdx_fixV (X := Mbar D.M ⊥ V hV)
      (A := Subgroup.zpowers phi) (Subgroup.zpowers_le.mpr hphiM) hphip2 hzp1
    rwa [show CFSG.Quasithin.E3.mParam (Mbar D.M ⊥ V hV) = mBar D.M ⊥ V hV from rfl] at h
  have hle4 : rkIdx (fixV (Subgroup.zpowers phi)) ≤ 4 := by
    have h := CFSG.Quasithin.rkIdx_anti hfix1
    rwa [← mQuot_eq_rkIdx_imgTil hV hB'V, hmB'] at h
  have hrk : rkIdx (fixV (Subgroup.zpowers phi)) = 4 := le_antisymm hle4 (hmBar ▸ hge)
  set U : Subgroup G := preTil ⊥ V hV (fixV (Subgroup.zpowers phi)) with hUdef
  have hUV : U ≤ V := preTil_le ⊥ V hV _
  have hB'U : conjSubgroup B g⁻¹ ≤ U := by
    intro b hb
    rw [hUdef, mem_preTil_iff_of_mem ⊥ V hV _ (hB'V hb)]
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
    exact hphifix _ ((mem_imgTil ⊥ V hV _ _).2 ⟨IntMod.mk hV ⟨b, hB'V hb⟩, hb, rfl⟩)
  have hmqU : E3.mQuot V U = 4 := by
    rw [hUdef, mQuot_eq_rkIdx_imgTil hV hUV, imgTil_preTil]
    exact hrk
  have hsplit := E3.mQuot_add hB'U hUV
  have hzero : E3.mQuot U (conjSubgroup B g⁻¹) = 0 := by
    rw [hmB', hmqU] at hsplit
    omega
  have heq : conjSubgroup B g⁻¹ = U :=
    (E3.mQuot_eq_zero_iff (hV.isPGroup.to_le hUV) hB'U).1 hzero
  calc fixV (Subgroup.zpowers phi) = imgTil ⊥ V hV U := (imgTil_preTil ⊥ V hV _).symm
    _ = imgTil ⊥ V hV (conjSubgroup B g⁻¹) := by rw [heq]

theorem gap_18_4_ii_W {D : Data G} {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {X : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV))}
    (hK1 : K_OmegaPlusFour_twoNat_inv)
    (hp125 : Hyp125 D ⊥ V) (hX : IsOmegaPlus ↥X 4 2)
    (hsum : SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2)
    (hm4 : mBar D.M ⊥ V hV = 4) (hr4 : (4 : ℕ∞) < rMV D.M V)
    (hMN : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (X : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))))
    (B : Subgroup G) (g : G) (hB : B ≤ conjSubgroup V g) (hBM : B ≤ D.M)
    (hmVgB : E3.mQuot (conjSubgroup V g) B = 4)
    (hWle : V ⊓ Subgroup.centralizer (B : Set G) ≤ conjSubgroup D.M g) :
    E3.mQuot (V ⊓ Subgroup.centralizer (B : Set G))
      ((V ⊓ Subgroup.centralizer (B : Set G)) ⊓
        Subgroup.centralizer (conjSubgroup V g : Set G)) ≤ 1 := by
  classical
  have hpF : PairFacts D.M ⊥ V := hp125.pairFacts
  have hMnorm : D.M ≤ Subgroup.normalizer (V : Set G) := hpF.le_normalizer
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  set W : Subgroup G := V ⊓ Subgroup.centralizer (B : Set G) with hWdef
  set K : Subgroup G := W ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) with hKdef
  have hWV : W ≤ V := by rw [hWdef]; exact inf_le_left
  have hWCb : W ≤ Subgroup.centralizer (B : Set G) := by rw [hWdef]; exact inf_le_right
  have hWC : W ≤ conjSubgroup D.M g := by rw [hWdef]; exact hWle
  have hKle : K ≤ W := by rw [hKdef]; exact inf_le_left
  have hKC : K ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
    rw [hKdef]; exact inf_le_right
  have hW2 : IsPGroup 2 W := hV.isPGroup.to_le hWV
  have hWnormg : W ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    refine hWC.trans ?_
    rw [← E3.conjSubgroup_normalizer V g]
    exact E3.conjSubgroup_mono_left g hMnorm
  have hstabM : ∀ {x : G}, x ∈ D.M → x ∈ stabTil ⊥ V := fun hx =>
    le_stabTil hMnorm (by rw [Subgroup.normalizer_eq_top]; exact le_top) hx
  have hu'M : ∀ w : ↥W, g * (w : G) * g⁻¹ ∈ D.M := fun w =>
    (mem_conjSubgroup_iff).1 (hWC w.2)
  let κ : ↥W →* ↥(stabTil ⊥ V) :=
    { toFun := fun w => ⟨g * (w : G) * g⁻¹, hstabM (hu'M w)⟩
      map_one' := by
        apply Subtype.ext
        show g * ((1 : ↥W) : G) * g⁻¹ = 1
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show g * ((a * b : ↥W) : G) * g⁻¹ =
          (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
        rw [Subgroup.coe_mul]
        group }
  let ψ : ↥W →* MulAut (Vtil ⊥ V hV) := (actTil ⊥ V hV).comp κ
  have hψmem : ∀ w : ↥W, ψ w ∈ Mbar D.M ⊥ V hV := fun w =>
    actTil_mem_barSub ⊥ V hV (hu'M w) (hstabM (hu'M w))
  have hmemK_of_psi : ∀ (w : ↥W), ψ w = 1 → (w : G) ∈ K := by
    intro w h1
    rw [hKdef]
    refine Subgroup.mem_inf.2 ⟨w.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hv : g * x * g⁻¹ ∈ V := (mem_conjSubgroup_iff).1 hx
    have h2 : actTil ⊥ V hV ⟨g * (w : G) * g⁻¹, hstabM (hu'M w)⟩ = 1 := h1
    have h3 := (actTil_eq_one_iff ⊥ V hV ⟨g * (w : G) * g⁻¹, hstabM (hu'M w)⟩).1 h2
      (g * x * g⁻¹) hv
    rw [Subgroup.mem_bot] at h3
    have h5 : (g * (w : G) * g⁻¹) * (g * x * g⁻¹) * (g * (w : G) * g⁻¹)⁻¹ =
        g * x * g⁻¹ := by
      have h4 := congrArg (fun z => z * (g * x * g⁻¹)) h3
      simpa [mul_assoc] using h4
    have h6 : (w : G) * x * (w : G)⁻¹ = x := by
      have h4 := congrArg (fun z => g⁻¹ * z * g) h5
      simpa [mul_assoc] using h4
    calc x * (w : G) = ((w : G) * x * (w : G)⁻¹) * (w : G) := by rw [h6]
      _ = (w : G) * x := by group
  have hpsi_of_memK : ∀ (w : ↥W), (w : G) ∈ K → ψ w = 1 := by
    intro w hw
    have hwC : (w : G) ∈ Subgroup.centralizer (conjSubgroup V g : Set G) := hKC hw
    show actTil ⊥ V hV ⟨g * (w : G) * g⁻¹, hstabM (hu'M w)⟩ = 1
    rw [actTil_eq_one_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hx : g⁻¹ * v * g ∈ conjSubgroup V g := by
      refine (mem_conjSubgroup_iff).2 ?_
      rw [show g * (g⁻¹ * v * g) * g⁻¹ = v by group]
      exact hv
    have hcomm := (Subgroup.mem_centralizer_iff.1 hwC) _ hx
    have h4 : (w : G) * (g⁻¹ * v * g) * (w : G)⁻¹ = g⁻¹ * v * g := by
      rw [← hcomm]; group
    have h5 : (g * (w : G) * g⁻¹) * v * (g * (w : G) * g⁻¹)⁻¹ = v := by
      calc (g * (w : G) * g⁻¹) * v * (g * (w : G) * g⁻¹)⁻¹
          = g * ((w : G) * (g⁻¹ * v * g) * (w : G)⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * v * g) * g⁻¹ := by rw [h4]
        _ = v := by group
    rw [h5, mul_inv_cancel]
  have hB'V : conjSubgroup B g⁻¹ ≤ V := by
    have h1 : conjSubgroup B g⁻¹ ≤ conjSubgroup (conjSubgroup V g) g⁻¹ :=
      E3.conjSubgroup_mono_left g⁻¹ hB
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h1
  have hmapB : B.map (MulAut.conj g).toMonoidHom = conjSubgroup B g⁻¹ := by
    rw [conjSubgroup, inv_inv]
  have hmapV : (conjSubgroup V g).map (MulAut.conj g).toMonoidHom = V := by
    have h1 : conjSubgroup (conjSubgroup V g) g⁻¹ = V := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    simpa only [conjSubgroup, inv_inv] using h1
  have hmB' : E3.mQuot V (conjSubgroup B g⁻¹) = 4 := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (H := B) (K := conjSubgroup V g) (MulEquiv.injective (MulAut.conj g))
    unfold E3.mQuot
    rw [← hmapB, ← hmapV, h]
    exact hmVgB
  have hu'B' : ∀ w : ↥W, g * (w : G) * g⁻¹ ∈
      Subgroup.centralizer (conjSubgroup B g⁻¹ : Set G) := by
    intro w
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hb : g⁻¹ * x * g ∈ B := by
      simpa only [inv_inv] using (mem_conjSubgroup_iff).1 hx
    have hcomm := (Subgroup.mem_centralizer_iff.1 (hWCb w.2)) _ hb
    calc x * (g * (w : G) * g⁻¹)
        = g * ((g⁻¹ * x * g) * (w : G)) * g⁻¹ := by group
      _ = g * ((w : G) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * (w : G) * g⁻¹) * x := by group
  have hfixeq : ∀ (w : ↥W), ψ w ≠ 1 →
      CFSG.Quasithin.fixV (Subgroup.zpowers (ψ w)) =
        imgTil ⊥ V hV (conjSubgroup B g⁻¹) := by
    intro w hwne
    refine fixV_actTil_zpowers_eq_imgTil hV hm4 (hu'M w) (hstabM (hu'M w)) ?_ ?_ hB'V
      hmB' (hu'B' w)
    · show (g * (w : G) * g⁻¹) * (g * (w : G) * g⁻¹) = 1
      have hw2 : (w : G) * (w : G) = 1 := by
        simpa [pow_two] using hV.2 (w : G) (hWV w.2)
      calc (g * (w : G) * g⁻¹) * (g * (w : G) * g⁻¹)
          = g * ((w : G) * (w : G)) * g⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    · intro huC
      apply hwne
      show actTil ⊥ V hV ⟨g * (w : G) * g⁻¹, hstabM (hu'M w)⟩ = 1
      rw [actTil_eq_one_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      have hcomm := (Subgroup.mem_centralizer_iff.1 huC) v hv
      have h4 : (g * (w : G) * g⁻¹) * v * (g * (w : G) * g⁻¹)⁻¹ = v := by
        rw [← hcomm]; group
      rw [h4, mul_inv_cancel]
  have hfixpoint : ∀ (w u : ↥W), ψ w ≠ 1 →
      ∀ q ∈ CFSG.Quasithin.fixV (Subgroup.zpowers (ψ w)), ψ u q = q := by
    intro w u hw q hq
    rw [hfixeq w hw] at hq
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV (conjSubgroup B g⁻¹) q).1 hq
    show actTil ⊥ V hV ⟨g * (u : G) * g⁻¹, hstabM (hu'M u)⟩ (mkTil ⊥ V hV x) =
      mkTil ⊥ V hV x
    rw [actTil_mk]
    have hx' : (g * (u : G) * g⁻¹) * x.val * (g * (u : G) * g⁻¹)⁻¹ = x.val := by
      have hb : g⁻¹ * x.val * g ∈ B := by
        simpa only [inv_inv] using (mem_conjSubgroup_iff).1 hx
      have hcomm := (Subgroup.mem_centralizer_iff.1 (hWCb u.2)) _ hb
      have hub : (u : G) * (g⁻¹ * x.val * g) = (g⁻¹ * x.val * g) * (u : G) :=
        hcomm.symm
      calc (g * (u : G) * g⁻¹) * x.val * (g * (u : G) * g⁻¹)⁻¹
          = g * ((u : G) * (g⁻¹ * x.val * g) * (u : G)⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * x.val * g) * g⁻¹ := by
              rw [show (u : G) * (g⁻¹ * x.val * g) * (u : G)⁻¹ = g⁻¹ * x.val * g by
                rw [hub]; group]
        _ = x.val := by group
    have hstabx : actStab ⊥ V hV ⟨g * (u : G) * g⁻¹, hstabM (hu'M u)⟩ x = x := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      exact hx'
    rw [hstabx]
  have hKc : ∀ (w : ↥W), ψ w ≠ 1 → ∀ y ∈ Mbar D.M ⊥ V hV,
      (∀ q ∈ CFSG.Quasithin.fixV (Subgroup.zpowers (ψ w)), y q = q) →
        y = 1 ∨ y = ψ w := by
    intro w hwne y hy hyfix
    have hsq : (ψ w) ^ 2 = 1 := by
      have hw2 : (w : ↥W) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [Subgroup.coe_pow, pow_two] using hV.2 (w : G) (hWV w.2)
      rw [← map_pow, hw2, map_one]
    have htop4 : E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers (ψ w))) = 4 := by
      rw [hfixeq w hwne, mQuot_top_eq_rkIdx, ← mQuot_eq_rkIdx_imgTil hV hB'V, hmB']
    have hk := hK1 (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV) X
      (Mbar D.M ⊥ V hV ⊔ X) le_sup_right
      (sup_le hMN Subgroup.le_normalizer) hX hsum (ψ w)
      (Subgroup.mem_sup_left (hψmem w)) hwne hsq htop4
    exact hk.2.2 y (Subgroup.mem_sup_left hy) hyfix
  have hclaim : ∀ (w u : ↥W), ψ w ≠ 1 → ψ u ≠ 1 → ψ w = ψ u := by
    intro w u hw hu
    rcases hKc w hw (ψ u) (hψmem u) (hfixpoint w u hw) with h1 | h1
    · exact absurd h1 hu
    · exact h1.symm
  by_cases hex : ∃ w : ↥W, ψ w ≠ 1
  · obtain ⟨u, hu⟩ := hex
    have hcover : ∀ w : ↥W, (w : G) ∈ K ∨ (u : G)⁻¹ * (w : G) ∈ K := by
      intro w
      by_cases hwK : (w : G) ∈ K
      · exact Or.inl hwK
      · refine Or.inr ?_
        have hw : ψ w ≠ 1 := fun h1 => hwK (hmemK_of_psi w h1)
        have huw : ψ ((u : ↥W)⁻¹ * w) = 1 := by
          rw [map_mul, map_inv]
          have hwu : ψ w = ψ u := by
            rcases hKc u hu (ψ w) (hψmem w) (hfixpoint u w hu) with h1 | h1
            · exact absurd h1 hw
            · exact h1
          rw [hwu]
          group
        exact hmemK_of_psi _ huw
    exact mQuot_le_one_of_coset_cover hW2 hKle (u := (u : G))
      (fun w hw => hcover ⟨w, hw⟩)
  · have htriv : ∀ w : ↥W, ψ w = 1 := by
      intro w
      by_contra hw
      exact hex ⟨w, hw⟩
    have hKW : K = W := by
      refine le_antisymm hKle ?_
      intro x hx
      rw [hKdef]
      exact hmemK_of_psi ⟨x, hx⟩ (htriv ⟨x, hx⟩)
    rw [hKW, E3.mQuot_self]
    exact Nat.zero_le 1


theorem A5Config18.false_of_case_two
    (c : A5Config18 D V₀ V L K) (h2 : CaseTwo18 D V L K c.elemAbelian)
    (hK1 : K_OmegaPlusFour_twoNat_inv) (hK2 : K_OmegaPlusFour_twoNat_scalar)
    (h111 : W3Thm111 G) (h61 : UC6.R6_1 D) (hSg : UC6S846.SigmaStd D)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) :
    False := by
  classical
  have hV0 : V₀ = ⊥ := c.v0
  subst hV0
  have hV : IsElemAbelian 2 V := c.elemAbelian
  have hp125 : Hyp125 D ⊥ V := c.pair.data.hyp.hyp125
  have hpF : PairFacts D.M ⊥ V := hp125.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hpF.le_normalizer hpF.le_normalizer₀
  have hG26 : Gap_18_4_ii_G26 D V c.elemAbelian
      (barSub ⊥ V c.elemAbelian L ⊔ barSub ⊥ V c.elemAbelian K) :=
    c.gap_18_4_ii_G26 hK1
  have hX : IsOmegaPlus ↥(barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) 4 2 := h2.2.1
  have hsum : SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2)
      (barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) ⊤ ⊥ 2 := h2.2.2
  have hLst : L ≤ stabTil ⊥ V :=
    le_stabTil (c.pair.mem_calC_L.1.le.trans hpF.le_normalizer)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hKst : K ≤ stabTil ⊥ V :=
    le_stabTil (c.pair.mem_calC.1.le.trans hpF.le_normalizer)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLMK : L ⊔ K ≤ D.M := sup_le c.pair.mem_calC_L.1.le c.pair.mem_calC.1.le
  have hNLM : D.M ≤ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLMK).mp c.pair.sup_normal
  have hbsup : barSub ⊥ V hV (L ⊔ K) = barSub ⊥ V hV L ⊔ barSub ⊥ V hV K := by
    rw [barSub, barSub, barSub, Subgroup.subgroupOf_sup hLst hKst, Subgroup.map_sup]
  have hMN : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer ((barSub ⊥ V hV L ⊔ barSub ⊥ V hV K :
        Subgroup (MulAut (Vtil ⊥ V hV))) : Set (MulAut (Vtil ⊥ V hV))) := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer
      (barSub_mono ⊥ V hV hLMK)).mp (barSub_subgroupOf_mbar_normal hV hLMK hNLM)
    rwa [hbsup] at h
  have hm4 : mBar D.M ⊥ V hV = 4 := c.numerics.1
  have ha2 : aBar D.M ⊥ V hV = 2 := c.numerics.2.1
  have hm4' : mBar D.M ⊥ V hp125.isElemAbelian = 4 := hm4
  have ha2' : aBar D.M ⊥ V hp125.isElemAbelian = 2 := ha2
  have hr4 : (4 : ℕ∞) < rMV D.M V := c.four_lt_rMV_of_case_two h2 hG26 h111 h61 hSg hK
  have hW0 : E3.wClos V 0 D.T ≤ Subgroup.centralizer (V : Set G) := by
    have hm2 : MBarGT D.M ⊥ V 2 := (hp125.mBarGT_iff_lt_mBar 2).2 (by omega)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (commutator_wClos_eq_bot_of_lt D h111 hp125 hm2 (by omega))
  obtain ⟨A, hAγ, hAbar⟩ := S17.exists_gammaTwo_barSub_ne_bot hp125 c.numerics.2.2.2
  have hAgam : A ∈ F12.Gam 2 D.T V := by
    rw [S17.gam_eq_gammaSet 2 D.T V hV]
    exact hAγ
  have hA2 : barSub ⊥ V hV A ∈ calABar 2 D.M ⊥ V hV :=
    gap_18_4_ii_aSet D V hV (barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) hW0
      hp125 hX hsum hm4 hr4 A hAgam hAbar
  obtain ⟨hAT, U, g₀, hUV, hcard, hAeq⟩ := hAgam
  have hAg : A ≤ conjSubgroup V g₀⁻¹ := by
    rw [hAeq]
    have h1 : conjSubgroup V g₀⁻¹ = V.map (MulAut.conj g₀).toMonoidHom := by
      rw [conjSubgroup, inv_inv]
    rw [h1]
    exact Subgroup.map_mono hUV
  have hmVgA : E3.mQuot (conjSubgroup V g₀⁻¹) A = 2 :=
    mQuot_eq_of_mem_gammaSet hAγ hAg
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAst : A ≤ stabTil ⊥ V := hAM.trans hMst
  obtain ⟨B, hBA, hmAB, hfixBA⟩ := exists_gammaSet_four_of_aSet_two hV hA2 ha2 hAst
  have hBM : B ≤ D.M := hBA.trans hAM
  have hBst : B ≤ stabTil ⊥ V := hBM.trans hMst
  have hB : B ≤ conjSubgroup V g₀⁻¹ := hBA.trans hAg
  have hmVgB : E3.mQuot (conjSubgroup V g₀⁻¹) B = 4 := by
    rw [E3.mQuot_add hBA hAg, hmAB, hmVgA]
  have hWle : V ⊓ Subgroup.centralizer (B : Set G) ≤ conjSubgroup D.M g₀⁻¹ :=
    inf_centralizer_le_conjSubgroup hV hp125.hyp62 hB hBM hmVgB hr4
  have hbound : E3.mQuot (V ⊓ Subgroup.centralizer (B : Set G))
      ((V ⊓ Subgroup.centralizer (B : Set G)) ⊓
        Subgroup.centralizer (A : Set G)) ≤ 1 := by
    have h1 := gap_18_4_ii_W hK1 hp125 hX hsum hm4 hr4 hMN B g₀⁻¹ hB hBM
      hmVgB hWle
    have h2 : (V ⊓ Subgroup.centralizer (B : Set G)) ⊓
        Subgroup.centralizer (A : Set G) ≥
        (V ⊓ Subgroup.centralizer (B : Set G)) ⊓
          Subgroup.centralizer (conjSubgroup V g₀⁻¹ : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le hAg)
    exact (E3.mQuot_mono h2).trans h1
  have ht : ∃ t ∈ Subgroup.normalizer ((barSub ⊥ V hV L ⊔ barSub ⊥ V hV K :
      Subgroup (MulAut (Vtil ⊥ V hV))) : Set (MulAut (Vtil ⊥ V hV))), orderOf t = 2 ∧
      E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4 := by
    obtain ⟨t, htM, hto, hmq⟩ := c.exists_involution_mQuot_four_of_case_two h2
    exact ⟨t, hMN htM, hto, hmq⟩
  obtain ⟨ω, -, -, -, heven⟩ := even_mQuot_fixV_of_mem_aSet_two hK2
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) hX hsum ht hMN hA2 (barSub ⊥ V hV B)
      (barSub_mono ⊥ V hV hBA)
  have hbridge : E3.mQuot (CFSG.Quasithin.fixV (barSub ⊥ V hV B))
      (CFSG.Quasithin.fixV (barSub ⊥ V hV B) ⊓ CFSG.Quasithin.fixV (barSub ⊥ V hV A))
      = E3.mQuot (V ⊓ Subgroup.centralizer (B : Set G))
          ((V ⊓ Subgroup.centralizer (B : Set G)) ⊓
            Subgroup.centralizer (A : Set G)) := by
    have h1 : imgTil ⊥ V hV (preCTilde ⊥ V B hV) = CFSG.Quasithin.fixV (barSub ⊥ V hV B) :=
      imgTil_preTil ⊥ V hV _
    have h2 : imgTil ⊥ V hV (preCTilde ⊥ V A hV) = CFSG.Quasithin.fixV (barSub ⊥ V hV A) :=
      imgTil_preTil ⊥ V hV _
    have h3 : E3.mQuot (imgTil ⊥ V hV (preCTilde ⊥ V B hV))
        (imgTil ⊥ V hV (preCTilde ⊥ V B hV) ⊓ imgTil ⊥ V hV (preCTilde ⊥ V A hV))
        = E3.mQuot (preCTilde ⊥ V B hV) (preCTilde ⊥ V B hV ⊓ preCTilde ⊥ V A hV) := by
      rw [← s16c167_imgTil_inf_bot hV]
      exact s16c167_mQuot_imgTil hV (preCTilde_le ⊥ V B hV) inf_le_left
    have h4 : (V ⊓ Subgroup.centralizer (B : Set G)) ⊓
        (V ⊓ Subgroup.centralizer (A : Set G)) =
        (V ⊓ Subgroup.centralizer (B : Set G)) ⊓ Subgroup.centralizer (A : Set G) := by
      refine le_antisymm (inf_le_inf_left _ inf_le_right) ?_
      exact le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    rw [← h1, ← h2, h3, preCTilde_bot_eq hV hBst, preCTilde_bot_eq hV hAst, h4]
  rw [hbridge] at heven
  have hne : E3.mQuot (CFSG.Quasithin.fixV (barSub ⊥ V hV B))
      (CFSG.Quasithin.fixV (barSub ⊥ V hV B) ⊓ CFSG.Quasithin.fixV (barSub ⊥ V hV A)) ≠ 0 := by
    intro h0
    have hle : CFSG.Quasithin.fixV (barSub ⊥ V hV A) ≤ CFSG.Quasithin.fixV (barSub ⊥ V hV B) :=
      CFSG.Quasithin.fixV_anti (barSub_mono ⊥ V hV hBA)
    rw [inf_eq_right.2 hle] at h0
    have hP : IsPGroup 2 ↥(CFSG.Quasithin.fixV (barSub ⊥ V hV B)) :=
      CFSG.GroupTheory.PerfectCover.isPGroup_two_of_sq_eq_one
        (fun y _ => s15_Infra_vtil_sq_eq_one ⊥ V hV y)
    have heq : CFSG.Quasithin.fixV (barSub ⊥ V hV A) =
        CFSG.Quasithin.fixV (barSub ⊥ V hV B) :=
      (E3.mQuot_eq_zero_iff hP hle).1 h0
    exact hfixBA heq.symm
  rw [hbridge] at hne
  rcases heven with ⟨k, hk⟩
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      exact hne (by rw [hk, h0, add_zero])
    · exact h0
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
