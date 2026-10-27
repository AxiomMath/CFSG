module

public import CFSG.LocalAnalysis.StandardType.GGKGCentOmMinus
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusTorus
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LocalAnalysis.StandardType.GGF4ReflLin
public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LieType.Universal.Spin.OddCT.Weyl
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourSpinLifts
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic

public section

namespace CFSG.StandardType.F4KGPosition

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Open
open scoped Matrix

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {n : ℕ}

private theorem b_ne_zero_of_irr (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  refine hirr s ?_
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  calc s ^ 2 + b * s + c = s ^ 2 + s * s := by rw [hb, hs]; ring
    _ = (2 : F) * s ^ 2 := by ring
    _ = 0 := by rw [h2, zero_mul]

omit [Finite F] [CharP F 2] in
private theorem single_plane_eq (j : Fin 2) :
    (Pi.single (.inr (.inr j)) 1 : Vm n F) = planeVec n (Pi.single j 1) := by
  funext y
  rcases y with l | l | j'
  · simp [planeVec]
  · simp [planeVec]
  · by_cases h : j' = j
    · subst h
      simp [planeVec]
    · simp [planeVec, h]

omit [Finite F] in
private theorem eq_of_polar_eq_zero (hb : b ≠ 0) (k : Fin (n - 1)) (u : Vm n F)
    (hl : ∀ l, l ≠ k → polar (quadMinus n F b c) u (eVec n l) = 0 ∧
      polar (quadMinus n F b c) u (fVec n l) = 0)
    (hP : ∀ j : Fin 2, polar (quadMinus n F b c) u (planeVec n (Pi.single j 1)) = 0) :
    u = u (.inl k) • eVec n k + u (.inr (.inl k)) • fVec n k := by
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  have h0 := hP 0
  have h1 := hP 1
  rw [← single_plane_eq, polar_quadMinus_single_inr_inr_zero, h2, zero_mul, zero_add] at h0
  rw [← single_plane_eq, polar_quadMinus_single_inr_inr_one, h2, zero_mul, zero_mul,
    add_zero] at h1
  have e0 : u (.inr (.inr 0)) = 0 := (mul_eq_zero.mp h1).resolve_left hb
  have e1 : u (.inr (.inr 1)) = 0 := (mul_eq_zero.mp h0).resolve_left hb
  funext i
  rcases i with l | l | j
  · by_cases hlk : l = k
    · subst hlk
      simp [eVec, fVec]
    · have h := (hl l hlk).2
      rw [fVec, polar_quadMinus_single_inr_inl] at h
      simp [eVec, fVec, hlk, h]
  · by_cases hlk : l = k
    · subst hlk
      simp [eVec, fVec]
    · have h := (hl l hlk).1
      rw [eVec, polar_quadMinus_single_inl] at h
      simp [eVec, fVec, hlk, h]
  · have hj : u (.inr (.inr j)) = 0 := by
      rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h | h <;> rw [h]
      · exact e0
      · exact e1
    simp [eVec, fVec, hj]

omit [Finite F] [CharP F 2] in
private theorem quadMinus_combo (k : Fin (n - 1)) (a c' : F) :
    quadMinus n F b c (a • eVec n k + c' • fVec n k) = a * c' := by
  rw [quadMinus_apply, Finset.sum_eq_single k]
  · simp [eVec, fVec]
  · intro l _ hlk
    simp [eVec, fVec, hlk]
  · simp

omit [Finite F] [CharP F 2] in
private theorem polar_combo (k : Fin (n - 1)) (a c' a' c'' : F) :
    polar (quadMinus n F b c) (a • eVec n k + c' • fVec n k) (a' • eVec n k + c'' • fVec n k) =
      a * c'' + a' * c' := by
  rw [polar_quadMinus, Finset.sum_eq_single k]
  · simp [eVec, fVec]
  · intro l _ hlk
    simp [eVec, fVec, hlk]
  · simp

theorem mem_ggTorus_of_commute_twShortRoot (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hF : ∃ c' : F, c' ≠ 0 ∧ c' ≠ 1) (hn : 4 ≤ n) {p : ℕ} (hp : Odd p)
    {t : spinGroup (quadMinus n F b c)} (htp : t ^ p = 1) (k : Fin (n - 1))
    (hcomm : ∀ l, l ≠ k → ∀ (s : Bool) (P : Fin 2 → F),
      t * twShortRoot n hirr l s (.ofAdd P) = twShortRoot n hirr l s (.ofAdd P) * t) :
    t ∈ ggTorus (minusDatum n hirr) := by
  classical
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  have hb : b ≠ 0 := b_ne_zero_of_irr hirr
  have hfix : ∀ l, l ≠ k → spinAction (quadMinus n F b c) t (eVec n l) = eVec n l ∧
      spinAction (quadMinus n F b c) t (fVec n l) = fVec n l ∧
      ∀ P, spinAction (quadMinus n F b c) t (planeVec n P) = planeVec n P := by
    intro l hl
    have hc : ∀ (s : Bool) (P : Fin 2 → F) (v : Vm n F),
        eichler (quadMinus n F b c) (minusVec n l s) (planeVec n P)
            ((spinMatrix (quadMinus n F b c) t : Matrix _ _ F) *ᵥ
              (fun i => (RingEquiv.refl F) (v i))) =
          (spinMatrix (quadMinus n F b c) t : Matrix _ _ F) *ᵥ
            (fun i => (RingEquiv.refl F)
              (eichler (quadMinus n F b c) (minusVec n l s) (planeVec n P) v i)) := by
      intro s P v
      simp only [RingEquiv.refl_apply, spinMatrix_mulVec]
      rw [← spinAction_twShortRoot_eq_eichler n hirr l s P, ← LinearEquiv.mul_apply, ← map_mul,
        ← hcomm l hl s P, map_mul, LinearEquiv.mul_apply]
    obtain ⟨-, ν, -, he, hf, hpl⟩ :=
      KGCentOmMinus.semi_eq_smul_of_commute_eichler_short hirr hF
        (spinMatrix (quadMinus n F b c) t) (RingEquiv.refl F) l hc
    simp only [spinMatrix_mulVec] at he hf hpl
    have hν : ν = 1 := by
      have h := map_spinAction (quadMinus n F b c) t (planeVec n (Pi.single 0 1))
      have hq : quadMinus n F b c (planeVec n (Pi.single 0 1)) = 1 := by
        rw [quadMinus_planeVec]
        simp
      rw [hpl, QuadraticMap.map_smul, hq, smul_eq_mul, mul_one] at h
      have hsq : (ν + 1) ^ 2 = 0 := by
        calc (ν + 1) ^ 2 = ν * ν + 2 * ν + 1 := by ring
          _ = 2 * (ν + 1) := by rw [h]; ring
          _ = 0 := by rw [h2, zero_mul]
      have h1 : ν + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
      calc ν = ν + 1 + 1 := by rw [add_assoc, one_add_one_eq_two, h2, add_zero]
        _ = 1 := by rw [h1, zero_add]
    subst hν
    exact ⟨by simpa using he, by simpa using hf, fun P => by simpa using hpl P⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l : Fin (n - 1), l ≠ k := by
    by_cases hk : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
    · exact ⟨⟨0, by omega⟩, fun h => hk (by rw [← h])⟩
  have hplane := (hfix l₀ hl₀).2.2
  have hshape : ∀ v : Vm n F, (∀ l, l ≠ k → polar (quadMinus n F b c) v (eVec n l) = 0 ∧
      polar (quadMinus n F b c) v (fVec n l) = 0) →
      (∀ P, polar (quadMinus n F b c) v (planeVec n P) = 0) →
      ∃ a c' : F, spinAction (quadMinus n F b c) t v = a • eVec n k + c' • fVec n k := by
    intro v hv hvP
    refine ⟨_, _, eq_of_polar_eq_zero (c := c) hb k _ (fun l hl => ?_) (fun j => ?_)⟩
    · obtain ⟨he, hf, -⟩ := hfix l hl
      constructor
      · rw [← he, polar_spinAction]
        exact (hv l hl).1
      · rw [← hf, polar_spinAction]
        exact (hv l hl).2
    · rw [← hplane, polar_spinAction]
      exact hvP _
  obtain ⟨a, c', hx⟩ := hshape (eVec n k)
    (fun l hl => ⟨polar_eVec_eVec n b c k l, by rw [polar_eVec_fVec]; simp [Ne.symm hl]⟩)
    (fun P => polar_eVec_planeVec n b c k P)
  obtain ⟨a', c'', hy⟩ := hshape (fVec n k)
    (fun l hl => ⟨by rw [polar_fVec_eVec]; simp [Ne.symm hl], polar_fVec_fVec n b c k l⟩)
    (fun P => polar_fVec_planeVec n b c k P)
  have hQx : a * c' = 0 := by
    have h := map_spinAction (quadMinus n F b c) t (eVec n k)
    rwa [hx, quadMinus_combo, quadMinus_eVec] at h
  have hQy : a' * c'' = 0 := by
    have h := map_spinAction (quadMinus n F b c) t (fVec n k)
    rwa [hy, quadMinus_combo, quadMinus_fVec] at h
  have hPxy : a * c'' + a' * c' = 1 := by
    have h := polar_spinAction (quadMinus n F b c) t (eVec n k) (fVec n k)
    rwa [hx, hy, polar_combo, polar_eVec_fVec, if_pos rfl] at h
  have hext : ∀ g g' : spinGroup (quadMinus n F b c),
      (∀ l, spinAction (quadMinus n F b c) g (eVec n l) =
        spinAction (quadMinus n F b c) g' (eVec n l)) →
      (∀ l, spinAction (quadMinus n F b c) g (fVec n l) =
        spinAction (quadMinus n F b c) g' (fVec n l)) →
      (∀ j : Fin 2, spinAction (quadMinus n F b c) g (planeVec n (Pi.single j 1)) =
        spinAction (quadMinus n F b c) g' (planeVec n (Pi.single j 1))) → g = g' := by
    intro g g' hge hgf hgP
    apply CFSG.LargeExtraspecial.A2Mod.FrB.spinAction_injective n hirr h2
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.pi_ext
    intro i r
    have hr : (Pi.single i r : Vm n F) = r • Pi.single i 1 := by
      funext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [hij]
    rw [hr, LinearEquiv.coe_coe, LinearEquiv.coe_coe, map_smul, map_smul]
    congr 1
    rcases i with l | l | j
    · exact hge l
    · exact hgf l
    · rw [single_plane_eq]
      exact hgP j
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul, zero_add] at hPxy
    have ha'0 : a' ≠ 0 := left_ne_zero_of_mul_eq_one hPxy
    have hc''0 : c'' = 0 := (mul_eq_zero.mp hQy).resolve_left ha'0
    rw [ha0, zero_smul, zero_add] at hx
    rw [hc''0, zero_smul, add_zero] at hy
    have ht2 : t * t = 1 := by
      refine hext (t * t) 1 (fun l => ?_) (fun l => ?_) (fun j => ?_)
      · rw [map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id]
        by_cases hlk : l = k
        · subst hlk
          rw [hx, map_smul, hy, smul_smul, mul_comm, hPxy, one_smul]
        · rw [(hfix l hlk).1, (hfix l hlk).1]
      · rw [map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id]
        by_cases hlk : l = k
        · subst hlk
          rw [hy, map_smul, hx, smul_smul, hPxy, one_smul]
        · rw [(hfix l hlk).2.1, (hfix l hlk).2.1]
      · rw [map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id, hplane, hplane]
    have ht1 : t = 1 := by
      obtain ⟨m, hm⟩ := hp
      calc t = (t * t) ^ m * t := by rw [ht2, one_pow, one_mul]
        _ = t ^ p := by rw [hm, pow_succ, pow_mul, pow_two]
        _ = 1 := htp
    have h := congrFun hx (.inl k)
    rw [ht1, map_one, LinearEquiv.coe_one, id] at h
    simp [eVec, fVec] at h
  have hc'0 : c' = 0 := (mul_eq_zero.mp hQx).resolve_left ha
  rw [hc'0, mul_zero, add_zero] at hPxy
  have hc'' : c'' = a⁻¹ := eq_inv_of_mul_eq_one_right hPxy
  have ha'0 : a' = 0 := (mul_eq_zero.mp hQy).resolve_right (by rw [hc'']; exact inv_ne_zero ha)
  rw [hc'0, zero_smul, add_zero] at hx
  rw [ha'0, zero_smul, zero_add, hc''] at hy
  obtain ⟨g, hgT, hge, hgf, hgP⟩ :=
    PsiDiag.SpinM.exists_diagAct hirr (Pi.mulSingle k (Units.mk0 a ha))
  have hgt : g = t := by
    refine hext g t (fun l => ?_) (fun l => ?_) (fun j => ?_)
    · rw [← minusVec_true, hge l]
      by_cases hlk : l = k
      · subst hlk
        rw [Pi.mulSingle_eq_same, Units.val_mk0, minusVec_true, hx]
      · rw [Pi.mulSingle_eq_of_ne hlk, Units.val_one, one_smul, minusVec_true, (hfix l hlk).1]
    · rw [← minusVec_false, hgf l]
      by_cases hlk : l = k
      · subst hlk
        rw [Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val, Units.val_mk0, minusVec_false, hy]
      · rw [Pi.mulSingle_eq_of_ne hlk, inv_one, Units.val_one, one_smul, minusVec_false,
          (hfix l hlk).2.1]
    · rw [hgP, hplane]
  rw [← hgt]
  have hct := minusDatum_isCTGroupDatum n hirr hn
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  exact CFSG.LieType.Steinberg.iSup_le_normalizer_rootGroup hct hγ hgT

end Model

section Reflections

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem eq_top_of_three_reflections (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (r : Fin 3 → MulAut ↥Bs) (hr : ∀ k, GGIsReflection p (r k))
    (hc : ∀ k l, r k * r l = r l * r k) (hne : ∀ k l, k ≠ l → r k ≠ r l) (S : Subgroup ↥Bs)
    (hS : ∀ (k : Fin 3) (y : ↥Bs), (∀ l, l ≠ k → r l y = y) → y ∈ S) : S = ⊤ := by
  have hcm : ∀ x y : ↥Bs, x * y = y * x := fun x y => Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs x.2 y.2)
  have hpow : ∀ y : ↥Bs, y ^ p = 1 := fun y => Subtype.ext (by simpa using hBs.2 y y.2)
  obtain ⟨j, hj⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hinv : ∀ k (y : ↥Bs), r k (r k y) = y := by
    intro k y
    have h := congrArg (fun φ : MulAut ↥Bs => φ y) (hr k).1
    simpa [pow_two] using h
  have hrc : ∀ k l (y : ↥Bs), r k (r l y) = r l (r k y) := by
    intro k l y
    have h := congrArg (fun φ : MulAut ↥Bs => φ y) (hc k l)
    simpa using h
  let P : Fin 3 → ↥Bs → ↥Bs := fun k y => (y * r k y) ^ (j + 1)
  let N : Fin 3 → ↥Bs → ↥Bs := fun k y => (y * (r k y)⁻¹) ^ (j + 1)
  have hPN : ∀ k y, P k y * N k y = y := by
    intro k y
    have h1 : P k y * N k y = (y * r k y * (y * (r k y)⁻¹)) ^ (j + 1) :=
      (Commute.mul_pow (hcm _ _) (j + 1)).symm
    have h2 : y * r k y * (y * (r k y)⁻¹) = y * y := by
      calc y * r k y * (y * (r k y)⁻¹) = y * (r k y * y) * (r k y)⁻¹ := by group
        _ = y * (y * r k y) * (r k y)⁻¹ := by rw [hcm (r k y) y]
        _ = y * y := by group
    rw [h1, h2, ← pow_two, ← pow_mul, show 2 * (j + 1) = p + 1 by omega, pow_succ, hpow,
      one_mul]
  have hPfix : ∀ k y, r k (P k y) = P k y := by
    intro k y
    simp only [P, map_pow, map_mul, hinv, hcm (r k y) y]
  have hNinv : ∀ k y, r k (N k y) = (N k y)⁻¹ := by
    intro k y
    simp only [N, map_pow, map_mul, map_inv, hinv]
    rw [← inv_pow, mul_inv_rev, inv_inv]
  have hPcomm : ∀ k l (y : ↥Bs), r l y = y → r l (P k y) = P k y := by
    intro k l y hy
    simp only [P, map_pow, map_mul, hrc l k, hy]
  have hNfix : ∀ k l (y : ↥Bs), l ≠ k → r l (N k y) = N k y := fun k l y hlk =>
    GGIsReflection.apply_eq_of_commute hp2 hBs (hr l) (hr k) (hc l k) (hne l k hlk) (hNinv k y)
  refine eq_top_iff.mpr fun b _ => ?_
  have hb : b = P 2 (P 1 (P 0 b)) * N 2 (P 1 (P 0 b)) * N 1 (P 0 b) * N 0 b := by
    rw [hPN, hPN, hPN]
  rw [hb]
  refine S.mul_mem (S.mul_mem (S.mul_mem ?_ ?_) ?_) ?_
  · refine hS 0 _ fun l _ => ?_
    have h0 : r 0 (P 0 b) = P 0 b := hPfix 0 b
    fin_cases l
    · exact hPcomm 2 0 _ (hPcomm 1 0 _ h0)
    · exact hPcomm 2 1 _ (hPfix 1 _)
    · exact hPfix 2 _
  · exact hS 2 _ fun l hl => hNfix 2 l _ hl
  · exact hS 1 _ fun l hl => hNfix 1 l _ hl
  · exact hS 0 _ fun l hl => hNfix 0 l _ hl

end Reflections

section Weyl

open CFSG.LieType.RootSystem

theorem toStdB_weylAction_simple_B3 (k : Fin 3) (v : Fin 3 → ℤ) :
    toStdB 3 (weylAction (isFiniteType_cartanB 3)
      ((coxeterMatrix (isFiniteType_cartanB 3)).simple k) v) = stdReflB 3 k (toStdB 3 v) := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, weylAction_simple, toStdB_reflection]

@[expose] noncomputable def shortWordB3 : Fin 3 → (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
  ![(coxeterMatrix (isFiniteType_cartanB 3)).simple 1 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 0 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 1,
    (coxeterMatrix (isFiniteType_cartanB 3)).simple 1, 1]

@[expose] noncomputable def shortReflB3 (k : Fin 3) : (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
  shortWordB3 k * (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 * (shortWordB3 k)⁻¹

theorem toStdB_shortWordB3 (k : Fin 3) :
    toStdB 3 (weylAction (isFiniteType_cartanB 3) (shortWordB3 k) (Pi.single 2 1)) =
      Pi.single k 1 := by
  fin_cases k <;>
    simp only [shortWordB3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_mul,
      Module.End.mul_apply, map_one, Module.End.one_apply, toStdB_weylAction_simple_B3] <;>
    decide

private theorem simple_inv_B3 (i : Fin 3) :
    ((coxeterMatrix (isFiniteType_cartanB 3)).simple i)⁻¹ =
      (coxeterMatrix (isFiniteType_cartanB 3)).simple i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.inv_simple _ i

private theorem simple_mul_self_B3 (i : Fin 3) :
    (coxeterMatrix (isFiniteType_cartanB 3)).simple i *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple i = 1 := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.simple_mul_simple_self _ i

private theorem simple_mul_pow_B3 (i j : Fin 3) :
    ((coxeterMatrix (isFiniteType_cartanB 3)).simple i *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple j) ^
        (coxeterMatrix (isFiniteType_cartanB 3)) i j = 1 := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.simple_mul_simple_pow _ i j

private theorem shortReflB3_eq :
    shortReflB3 2 = (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 ∧
    shortReflB3 1 = (coxeterMatrix (isFiniteType_cartanB 3)).simple 1 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 1 ∧
    shortReflB3 0 = (coxeterMatrix (isFiniteType_cartanB 3)).simple 1 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 0 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 1 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 1 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 0 *
      (coxeterMatrix (isFiniteType_cartanB 3)).simple 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [shortReflB3, shortWordB3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul, inv_one, mul_one,
      mul_inv_rev, simple_inv_B3]
  group

theorem shortReflB3_commute (k l : Fin 3) :
    shortReflB3 k * shortReflB3 l = shortReflB3 l * shortReflB3 k := by
  have e02 : (coxeterMatrix (isFiniteType_cartanB 3)) 0 2 = 2 :=
    CFSG.LieType.Universal.Spin.OddCT.coxeterMatrix_of_far (by decide) (by decide) (by decide)
  have e12 : (coxeterMatrix (isFiniteType_cartanB 3)) 1 2 = 4 :=
    CFSG.LieType.Universal.Spin.OddCT.coxeterMatrix_of_succ_last (by decide) (by decide)
  have e10 : (coxeterMatrix (isFiniteType_cartanB 3)) 1 0 = 3 := by
    rw [(coxeterMatrix (isFiniteType_cartanB 3)).symmetric]
    exact CFSG.LieType.Universal.Spin.OddCT.coxeterMatrix_of_succ (by decide) (by decide)
  have p02 := simple_mul_pow_B3 0 2
  have p12 := simple_mul_pow_B3 1 2
  have p10 := simple_mul_pow_B3 1 0
  rw [e02] at p02
  rw [e12] at p12
  rw [e10] at p10
  have hsi := simple_inv_B3
  have hss := simple_mul_self_B3
  obtain ⟨h2, h1, h0⟩ := shortReflB3_eq
  set s := (coxeterMatrix (isFiniteType_cartanB 3)).simple with hs
  have r02 : s 0 * s 2 = s 2 * s 0 := by
    rw [pow_two] at p02
    rw [eq_inv_of_mul_eq_one_left p02, mul_inv_rev, hsi, hsi]
  have r12 : s 1 * s 2 * s 1 * s 2 = s 2 * s 1 * s 2 * s 1 := by
    have h' : (s 1 * s 2 * s 1 * s 2) * (s 1 * s 2 * s 1 * s 2) = 1 := by
      rw [← p12]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [eq_inv_of_mul_eq_one_left h']
    simp only [mul_inv_rev, hsi, mul_assoc]
  have r10 : s 1 * s 0 * (s 1 * s 0) * (s 1 * s 0) = 1 := by
    rw [← p10]
    simp only [pow_succ, pow_zero, one_mul]
  have huinv : (s 1 * s 0)⁻¹ = s 0 * s 1 := by rw [mul_inv_rev, hsi, hsi]
  have hu2 : MulAut.conj (s 1 * s 0) (s 2) = s 1 * s 2 * s 1 := by
    rw [MulAut.conj_apply, huinv]
    calc s 1 * s 0 * s 2 * (s 0 * s 1) = s 1 * (s 0 * s 2) * s 0 * s 1 := by group
      _ = s 1 * s 2 * (s 0 * s 0) * s 1 := by rw [r02]; group
      _ = s 1 * s 2 * s 1 := by rw [hss]; group
  have hu1 : MulAut.conj (s 1 * s 0) (s 1 * s 2 * s 1) = shortReflB3 0 := by
    rw [MulAut.conj_apply, huinv, h0]
    group
  have hu0 : MulAut.conj (s 1 * s 0) (shortReflB3 0) = s 2 := by
    rw [← hu1, ← hu2, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    calc s 1 * s 0 * (s 1 * s 0 * (s 1 * s 0 * s 2 * (s 1 * s 0)⁻¹) * (s 1 * s 0)⁻¹) *
          (s 1 * s 0)⁻¹ = (s 1 * s 0 * (s 1 * s 0) * (s 1 * s 0)) * s 2 *
            (s 1 * s 0 * (s 1 * s 0) * (s 1 * s 0))⁻¹ := by group
      _ = s 2 := by rw [r10, one_mul, inv_one, mul_one]
  have c21 : Commute (s 2) (s 1 * s 2 * s 1) := by
    show s 2 * (s 1 * s 2 * s 1) = s 1 * s 2 * s 1 * s 2
    rw [r12]
    group
  have c10 : Commute (s 1 * s 2 * s 1) (shortReflB3 0) := by
    have h := c21.map (MulAut.conj (s 1 * s 0))
    rwa [hu2, hu1] at h
  have c02 : Commute (shortReflB3 0) (s 2) := by
    have h := c10.map (MulAut.conj (s 1 * s 0))
    rwa [hu1, hu0] at h
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | rfl
    | (rw [h2, h1]; exact c21.eq)
    | (rw [h2, h1]; exact c21.eq.symm)
    | (rw [h1]; exact c10.eq)
    | (rw [h1]; exact c10.eq.symm)
    | (rw [h2]; exact c02.eq)
    | (rw [h2]; exact c02.eq.symm)

private theorem weylAction_shortReflB3 :
    weylAction (isFiniteType_cartanB 3) (shortReflB3 2) (Pi.single 2 1) = -Pi.single 2 1 ∧
    weylAction (isFiniteType_cartanB 3) (shortReflB3 1) (Pi.single 2 1) = Pi.single 2 1 ∧
    weylAction (isFiniteType_cartanB 3) (shortReflB3 0) (Pi.single 2 1) = Pi.single 2 1 ∧
    weylAction (isFiniteType_cartanB 3) (shortReflB3 1) ![0, 1, 1] = -![0, 1, 1] ∧
    weylAction (isFiniteType_cartanB 3) (shortReflB3 0) ![0, 1, 1] = ![0, 1, 1] := by
  obtain ⟨h2, h1, h0⟩ := shortReflB3_eq
  rw [h2, h1, h0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply toStdB_injective 3 <;>
    simp only [map_mul, Module.End.mul_apply, toStdB_weylAction_simple_B3, toStdB_neg] <;>
    decide

theorem shortReflB3_ne {k l : Fin 3} (hkl : k ≠ l) : shortReflB3 k ≠ shortReflB3 l := by
  obtain ⟨a2, a1, a0, b1, b0⟩ := weylAction_shortReflB3
  have hne2 : (-Pi.single 2 1 : Fin 3 → ℤ) ≠ Pi.single 2 1 := by decide
  have hne1 : (-![0, 1, 1] : Fin 3 → ℤ) ≠ ![0, 1, 1] := by decide
  intro h
  fin_cases k <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h hkl
  all_goals first
    | exact hkl rfl
    | (have := congrArg (fun w => weylAction (isFiniteType_cartanB 3) w (Pi.single 2 1)) h
       simp only [a2, a1, a0] at this
       first | exact hne2 this | exact hne2 this.symm)
    | (have := congrArg (fun w => weylAction (isFiniteType_cartanB 3) w ![0, 1, 1]) h
       simp only [b1, b0] at this
       first | exact hne1 this | exact hne1 this.symm)

end Weyl

section Torality

open CFSG.LieType.RootSystem CFSG.Assembly


theorem exists_ggTorus_conj_of_tableBPos_POmegaMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (_hpq : p ∣ 2 ^ f - 1) (ψ : (ggU .POmegaMinus 4 f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K) (hrange : ψ.range = X)
    (hpos : GGTableBPos p Bs X .POmegaMinus 4 f ψ) :
    ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .POmegaMinus 4 f).D,
      ∀ z, b * ψ z * b⁻¹ = ψ (t * z * t⁻¹) := by
  classical
  obtain ⟨hp, hp2, _, _⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  let : IsMulCommutative ↥Bs := hBs.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, by omega, le_rfl⟩
  obtain ⟨-, hdiag, hcard⟩ := ggF4QGeFour_localMap_of_mp ggInnerDiagMpInput_holds hcfg hX ψ
    hadm (two_le_lieUniversal_rank .POmegaMinus 4 2 f Nat.prime_two hadm (by decide)) hker
    hrange
  let F := GaloisField 2 f
  have hirr := minusCoeffs_irr 2 f
  let ψn : ↥(spinGroup (quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) →* G := ψ
  have hdiag' : ∀ b ∈ Bs, GGPsiInnerDiag (minusDatum 4 hirr) ψn b := hdiag
  have hcard' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψn.range : Set G)) ≤
      Nat.card Bs := by
    rw [show ψn.range = X from hrange]
    exact hcard
  obtain ⟨ℓ, hℓ, -, hpowℓ, -⟩ :=
    exists_spinMinus_lift_kernel_rank 4 hirr (by decide) ψn hker Bs hdiag' hBs.2 hcard'
  have hψinj : Function.Injective ψn := by
    have hc := CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (by decide : 4 ≤ 4) hirr
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hc.le
  have hF : ∃ c' : F, c' ≠ 0 ∧ c' ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hinj : Function.Injective (fun z : F => decide (z = 0)) := by
      intro z z' hzz
      by_cases hz : z = 0
      · have hz' : z' = 0 := by simpa [hz] using hzz.symm
        rw [hz, hz']
      · have hz' : z' ≠ 0 := fun h => hz (by simpa [h] using hzz)
        rw [hcon z hz, hcon z' hz']
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      GaloisField.card 2 f (by omega)] at h1
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  let e : (coxeterMatrix (isFiniteType_cartanB 3)).Group →* MulAut ↥Bs :=
    (ggAutomizer X Bs).subtype.comp ε.toMonoidHom
  have he_inj : Function.Injective e := (ggAutomizer X Bs).subtype_injective.comp ε.injective
  let r : Fin 3 → MulAut ↥Bs := fun k => e (shortReflB3 k)
  have hr : ∀ k, GGIsReflection p (r k) := by
    intro k
    have h : r k = e (shortWordB3 k) * e ((coxeterMatrix (isFiniteType_cartanB 3)).simple 2) *
        (e (shortWordB3 k))⁻¹ := by
      simp only [r, shortReflB3, map_mul, map_inv]
    rw [h]
    exact (hεrefl (2 : Fin 3)).conj _
  have hrc : ∀ k l, r k * r l = r l * r k := fun k l => by
    simp only [r, ← map_mul, shortReflB3_commute k l]
  have hrne : ∀ k l, k ≠ l → r k ≠ r l := fun k l hkl h => shortReflB3_ne hkl (he_inj h)
  have hroot : ∀ (k : Fin 3) (s' : Bool) (P : Fin 2 → F),
      ψn (twShortRoot 4 hirr k s' (.ofAdd P)) ∈ ggRankOneIn X Bs (r k) := by
    intro k s' P
    have h : ggRankOneIn X Bs (r k) = (ggRootLevi (ggU .POmegaMinus 4 f).D
        (weylAction (ggU .POmegaMinus 4 f).D.isFiniteType (shortWordB3 k)
          (Pi.single (2 : Fin 3) 1))).map ψ :=
      hεlevi (shortWordB3 k) (2 : Fin 3)
    rw [h]
    refine ⟨twShortRoot 4 hirr k s' (.ofAdd P), ?_, rfl⟩
    have hγ := toStdB_shortWordB3 k
    cases s'
    · apply Subgroup.mem_sup_right
      show _ ∈ minusRootGroup 4 hirr
        (-(weylAction (isFiniteType_cartanB 3) (shortWordB3 k) (Pi.single 2 1)))
      rw [minusRootGroup_eq_short 4 hirr k false (by
        rw [toStdB_neg, boolSign_false, Pi.single_neg]
        exact congrArg Neg.neg hγ)]
      exact ⟨_, rfl⟩
    · apply Subgroup.mem_sup_left
      show _ ∈ minusRootGroup 4 hirr
        (weylAction (isFiniteType_cartanB 3) (shortWordB3 k) (Pi.single 2 1))
      rw [minusRootGroup_eq_short 4 hirr k true (by rw [boolSign_true]; exact hγ)]
      exact ⟨_, rfl⟩
  have hcentr : ∀ (k : Fin 3) (bb : ↥Bs), r k bb = bb → ∀ (s' : Bool) (P : Fin 2 → F),
      ℓ bb * twShortRoot 4 hirr k s' (.ofAdd P) = twShortRoot 4 hirr k s' (.ofAdd P) * ℓ bb := by
    intro k bb hbb s' P
    have hzC := (ggOTwoPrime_le _ (hroot k s' P)).2
    have hbH : (bb : G) ∈ ggHyperplane Bs (r k) :=
      ⟨bb, show (r k : ↥Bs →* ↥Bs) bb = MonoidHom.id _ bb from hbb, rfl⟩
    have hbz : (bb : G) * ψn (twShortRoot 4 hirr k s' (.ofAdd P)) =
        ψn (twShortRoot 4 hirr k s' (.ofAdd P)) * bb :=
      Subgroup.mem_centralizer_iff.mp hzC _ hbH
    have h := hℓ bb (twShortRoot 4 hirr k s' (.ofAdd P))
    rw [mul_assoc, ← hbz, inv_mul_cancel_left] at h
    have h' := hψinj h
    calc ℓ bb * twShortRoot 4 hirr k s' (.ofAdd P)
        = ℓ bb * twShortRoot 4 hirr k s' (.ofAdd P) * (ℓ bb)⁻¹ * ℓ bb := by group
      _ = twShortRoot 4 hirr k s' (.ofAdd P) * ℓ bb := by rw [← h']
  have htop := eq_top_of_three_reflections hp2 hBs r hr hrc hrne
    ((ggTorus (minusDatum 4 hirr)).comap ℓ) fun k bb hbb =>
      mem_ggTorus_of_commute_twShortRoot hirr hF le_rfl hpodd (hpowℓ bb) k
        fun l hl s' P => hcentr l bb (hbb l hl) s' P
  intro b hb
  have hbT : ℓ ⟨b, hb⟩ ∈ ggTorus (minusDatum 4 hirr) := by
    have h : (⟨b, hb⟩ : ↥Bs) ∈ (ggTorus (minusDatum 4 hirr)).comap ℓ := htop ▸ Subgroup.mem_top _
    exact h
  refine ⟨(ℓ ⟨b, hb⟩)⁻¹, inv_mem hbT, fun z => ?_⟩
  let z' : ↥(spinGroup (quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := z
  have h := hℓ ⟨b, hb⟩ ((ℓ ⟨b, hb⟩)⁻¹ * z' * ℓ ⟨b, hb⟩)
  rw [show ℓ ⟨b, hb⟩ * ((ℓ ⟨b, hb⟩)⁻¹ * z' * ℓ ⟨b, hb⟩) * (ℓ ⟨b, hb⟩)⁻¹ = z' by group] at h
  show b * ψn z' * b⁻¹ = ψn ((ℓ ⟨b, hb⟩)⁻¹ * z' * (ℓ ⟨b, hb⟩)⁻¹⁻¹)
  rw [inv_inv, ← h]
  group

end Torality

end CFSG.StandardType.F4KGPosition
