module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplitAux1
import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Rank
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelSelfDualMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCoord
import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
import CFSG.LocalAnalysis.StandardType.GGTBJOmModelMap
import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthFixed
import CFSG.HardMathSupport.Dickson.Sec6.I1431
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHBlocks
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHModel
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Polynomial
open Module Multiplicative QuadraticMap
open CFSG.RankThree.PartOne.KCOrthogonal

namespace CommonJOmMinusNonsplit

open CFSG.StandardType.OrthTorusGen
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary

private theorem aeval_apply_of_intertwines {K V W : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (f : V ≃ₗ[K] V) (φ : W →ₗ[K] V)
    (g : W ≃ₗ[K] W) (h : ∀ w, f.toLinearMap (φ w) = φ (g.toLinearMap w))
    (p : K[X]) (w : W) :
    (aeval f.toLinearMap p) (φ w) = φ ((aeval g.toLinearMap p) w) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, map_add]
  | monomial n a =>
      have hpow : ∀ w : W, ((f.toLinearMap) ^ n) (φ w) =
          φ (((g.toLinearMap) ^ n) w) := by
        intro w
        induction n generalizing w with
        | zero => simp
        | succ n ih =>
            rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih w,
              h ((g.toLinearMap ^ n) w)]
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, hpow]
      show (algebraMap K (Module.End K V) a) (φ (((g.toLinearMap) ^ n) w)) =
        φ ((algebraMap K (Module.End K W) a) (((g.toLinearMap) ^ n) w))
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

private theorem frame_fixedSpace_lt_four {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ}
    [NeZero p] {A : Subgroup (V ≃ₗ[K] V)} (hQ : (polarBilin Q).Nondegenerate)
    (F : SevOm.Frame Q p A r) (hU : ∀ j, finrank K (F.U j) = 2)
    (hV : finrank K V ≤ 2 * r + 2)
    (f : Fin r → Multiplicative (ZMod p)) (hf : ∀ j, toAdd (f j) ≠ 0) :
    ¬ 4 ≤ finrank K (fixedSpace (F.ι (OrthTorus.piMul r p f))) := by
  intro h4
  obtain ⟨k, hk⟩ := exists_coord_eq_zero hQ F hU hV (OrthTorus.piMul r p f) h4
  exact hf k (by simpa [OrthTorus.piMul_apply] using hk)

private theorem frame_dense_piece_orbit {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ}
    [NeZero p] {A : Subgroup (V ≃ₗ[K] V)} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (F : SevOm.Frame Q p A r)
    (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V ≤ 2 * r + 2)
    (f : Fin r → Multiplicative (ZMod p)) (hf : ∀ j, toAdd (f j) ≠ 0)
    (hfixvec : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v)
    {h : K[X]} (hh : h ∈ primaryFactors (F.ι (OrthTorus.piMul r p f)).toLinearMap)
    (hX : h ≠ X - 1) (hself : reciprocalPolynomial h = h) :
    ∃ j, F.U j ≤ orbitSpace (F.ι (OrthTorus.piMul r p f)).toLinearMap h := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set x : V ≃ₗ[K] V := F.ι (OrthTorus.piMul r p f) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (OrthTorus.piMul r p f)
  have hxmem : x ∈ A := F.mem (OrthTorus.piMul r p f)
  have hfixne : fixedSpace x ≠ ⊥ := by
    obtain ⟨v, hv0, hvfix⟩ := hfixvec
    intro hbot
    exact hv0 (by simpa [hbot] using mem_fixedSpace.mpr (hvfix x hxmem))
  have hXm : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    refine mem_primaryFactors_of_primaryComponent_ne_bot irreducible_X_sub_one monic_X_sub_one ?_
    rw [← fixedSpace_eq_primaryComponent]
    exact hfixne
  by_contra hall
  push Not at hall
  have hdich : ∀ j, F.U j ≤ othersSpace x.toLinearMap h := fun j =>
    (CoordOm.frame_piece_dichotomy hQ hT hp hp2 F hAΩ hmax (OrthTorus.piMul r p f) hh j).resolve_left
      (hall j)
  have hother : (⨆ j : {j : Fin r //
      (OrthTorus.piMul r p f).toAdd j ≠ (1 : ZMod p) - 1}, F.U j.1) ≤
      othersSpace x.toLinearMap h := by
    refine iSup_le fun j => hdich j.1
  have hfix_eq : fixedSpace x = suppPerp Q (⨆ j : {j : Fin r //
      (OrthTorus.piMul r p f).toAdd j ≠ (1 : ZMod p) - 1}, F.U j.1) := by
    ext v
    rw [mem_fixedSpace, F.fix, mem_suppPerp]
    constructor
    · intro hv y hy
      refine Submodule.iSup_induction _ (motive := fun y => polar Q y v = 0) hy ?_ ?_ ?_
      · intro j y hy
        exact hv j.1 (by simpa [sub_self] using j.2) y hy
      · simp
      · intro a b ha hb
        rw [QuadraticMap.polar_add_left, ha, hb, add_zero]
    · intro hv j hj u hu
      exact hv u (Submodule.mem_iSup_of_mem ⟨j, by simpa [sub_self] using hj⟩ hu)
  have horb_le : orbitSpace x.toLinearMap h ≤ fixedSpace x := by
    rw [hfix_eq]
    intro v hv
    rw [mem_suppPerp]
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => polar Q y v = 0) hy ?_ ?_ ?_
    · intro j y hy
      rw [QuadraticMap.polar_comm]
      exact hx.polar_orbit_others hh hv (hother (Submodule.mem_iSup_of_mem j hy))
    · simp
    · intro a b ha hb
      rw [QuadraticMap.polar_add_left, ha, hb, add_zero]
  have hdisj : Disjoint (primaryComponent x.toLinearMap h) (fixedSpace x) := by
    rw [fixedSpace_eq_primaryComponent]
    exact disjoint_primaryComponent_of_ne hx hh hXm hX
  have hbot : primaryComponent x.toLinearMap h = ⊥ := by
    have h : primaryComponent x.toLinearMap h ⊓ fixedSpace x = ⊥ := disjoint_iff.mp hdisj
    rw [orbitSpace, hself, sup_idem] at horb_le
    rwa [inf_eq_left.mpr horb_le] at h
  exact (primaryComponent_ne_bot hx.squarefree_minpoly hh) hbot

private theorem block_minpoly_natDegree {K D : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ f) (hpq : p ∣ Nat.card K + 1)
    (hdim : finrank K D = 2) (c : D ≃ₗ[K] D) (hcp : c ^ p = 1)
    (hfix : ∀ u, c u = u → u = 0) {a : ZMod p} (ha : a ≠ 0) :
    (minpoly K ((c ^ a.val : D ≃ₗ[K] D) : D →ₗ[K] D)).natDegree = 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ca : D ≃ₗ[K] D := c ^ a.val
  let caL : D →ₗ[K] D := ca
  let h : K[X] := minpoly K caL
  have hmon : h.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral caL)
  haveI : Nontrivial D := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hcne : c ≠ 1 := by
    intro hc1
    obtain ⟨u, hu⟩ := exists_ne (0 : D)
    exact hu (hfix u (by rw [hc1]; rfl))
  have hcord : orderOf c = p := orderOf_eq_prime hcp hcne
  have haval : ¬ p ∣ a.val := by
    intro hdvd
    apply ha
    rw [← ZMod.natCast_zmod_val a]
    exact (ZMod.natCast_eq_zero_iff a.val p).mpr hdvd
  have hcop : p.Coprime a.val := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr haval
  have hcord_ca : orderOf ca = p := by
    rw [show ca = c ^ a.val from rfl]
    rw [Nat.Coprime.orderOf_pow (by rwa [hcord])]
    exact hcord
  have hle : h.natDegree ≤ 2 := by
    have hdvd : h ∣ caL.charpoly := LinearMap.minpoly_dvd_charpoly caL
    have hchar : caL.charpoly.natDegree = 2 := by
      rw [LinearMap.charpoly_natDegree, hdim]
    rw [← hchar]
    exact Polynomial.natDegree_le_of_dvd hdvd (LinearMap.charpoly_monic caL).ne_zero
  have hpos : 0 < h.natDegree := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral caL)
  by_contra hne
  have hge : 1 ≤ h.natDegree := hpos
  have hne2 : h.natDegree ≠ 2 := hne
  have hdeg : h.natDegree = 1 := by omega
  obtain ⟨α, hα, β, hpoly⟩ := Polynomial.natDegree_eq_one.mp hdeg
  let lam : K := -β * α⁻¹
  have hroot : h.IsRoot lam := by
    rw [Polynomial.IsRoot.def, ← hpoly]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    dsimp [lam]
    field_simp
    ring
  have heig : Module.End.HasEigenvalue caL lam := Module.End.hasEigenvalue_of_isRoot hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hv0 : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  have hvsmul : caL v = lam • v := hv.apply_eq_smul
  have hlam_p : lam ^ p = 1 := by
    have hpow := hv.pow_apply p
    have hcoe_pow : ∀ n, (caL ^ n) v = (ca ^ n) v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, pow_succ', LinearEquiv.mul_apply, ih]
          rfl
    have hcap : (caL ^ p) v = v := by
      rw [hcoe_pow p, show ca = c ^ a.val from rfl, ← pow_mul, Nat.mul_comm a.val p,
        pow_mul, hcp, one_pow]
      rfl
    rw [hcap] at hpow
    have hsub : (lam ^ p - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hpow, sub_self]
    have hlam : lam ^ p - 1 = 0 := by
      rcases smul_eq_zero.mp hsub with h0 | h0
      · exact h0
      · exact absurd h0 hv0
    exact sub_eq_zero.mp hlam
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Fact.out : p.Prime).pos.ne'] at hlam_p
    exact zero_ne_one hlam_p
  have hcopK : p.Coprime (Nat.card K - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    have h2 : p ∣ 2 := by
      have hsub := Nat.dvd_sub hpq hdvd
      have hdiff : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have hKpos : 1 < Nat.card K := Finite.one_lt_card
        omega
      rwa [hdiff] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)
  have hlam_card : lam ^ (Nat.card K - 1) = 1 := by
    simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card_sub_one_eq_one lam hlam0
  have hlam_one : lam = 1 :=
    (pow_eq_one_iff_of_coprime hcopK).mp ⟨hlam_p, hlam_card⟩
  have hfix_ca : c v = v := by
    have hcop_a : a.val.Coprime (orderOf c) := by rw [hcord]; exact hcop.symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop_a
    have hcoe_pow : ∀ n, (caL ^ n) v = (ca ^ n) v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, pow_succ', LinearEquiv.mul_apply, ih]
          rfl
    have hca_fix : ca v = v := by
      change caL v = v
      rw [hvsmul, hlam_one, one_smul]
    have hcam_all : ∀ n, (ca ^ n) v = v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hca_fix]
    have hcam_ca : (ca ^ m) v = v := hcam_all m
    have hcam : (caL ^ m) v = v := by rw [hcoe_pow m, hcam_ca]
    rw [← hm]
    change (ca ^ m) v = v
    exact hcam_ca
  exact hv0 (hfix v hfix_ca)

private theorem frame_dense_primary {K V D : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    {Q : QuadraticForm K V} {p r n : ℕ} [NeZero p] [NeZero r]
    {A : Subgroup (V ≃ₗ[K] V)} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hK : Nat.card K = 2 ^ n)
    (F : SevOm.Frame Q p A r) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V ≤ 2 * r + 2)
    (hdimD : finrank K D = 2) (c : D ≃ₗ[K] D) (hcp : c ^ p = 1)
    (hfix : ∀ u, c u = u → u = 0) (hcT : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹)
    (θ : Fin r → D →ₗ[K] V) (hθinj : ∀ j, Function.Injective (θ j))
    (hθrange : ∀ j, (θ j).range = F.U j)
    (hθact : ∀ (s : Multiplicative (Fin r → ZMod p)) (j : Fin r) (d : D),
      F.ι s (θ j d) = θ j ((c ^ (toAdd s j).val) d))
    (f : Fin r → Multiplicative (ZMod p)) (hf : ∀ j, toAdd (f j) ≠ 0)
    (hdense : ∀ j, f j = f 0 ∨ f j = (f 0)⁻¹)
    (hfixvec : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) :
    ∃ h0 : K[X], h0.natDegree = 2 ∧
      (∀ j, F.U j ≤ primaryComponent (F.ι (OrthTorus.piMul r p f)).toLinearMap h0) ∧
      (∀ h : K[X], h ∈ primaryFactors (F.ι (OrthTorus.piMul r p f)).toLinearMap →
        h ≠ X - 1 → h = h0) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set x : V ≃ₗ[K] V := F.ι (OrthTorus.piMul r p f) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (OrthTorus.piMul r p f)
  have htoadd : ∀ j, toAdd ((OrthTorus.piMul r p f) j) = toAdd (f j) := fun j => rfl
  have hxact : ∀ (j : Fin r) (d : D),
      x.toLinearMap (θ j d) =
        θ j (((c ^ (toAdd (f j)).val : D ≃ₗ[K] D) : D →ₗ[K] D) d) := by
    intro j d
    rw [hxdef]
    exact hθact (OrthTorus.piMul r p f) j d
  let a : ZMod p := toAdd (f 0)
  have ha : a ≠ 0 := hf 0
  haveI : NeZero a := ⟨ha⟩
  let ca : D ≃ₗ[K] D := c ^ a.val
  let caL : D →ₗ[K] D := ca
  let h0 : K[X] := minpoly K caL
  have h0deg : h0.natDegree = 2 := block_minpoly_natDegree hp2 hK hpq hdimD c hcp hfix (a := a) ha
  have h0mon : h0.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral caL)
  have haeval : aeval caL h0 = 0 := minpoly.aeval K caL
  have hmin_neg : minpoly K ((c ^ (-a).val : D ≃ₗ[K] D) : D →ₗ[K] D) = h0 := by
    obtain ⟨T, hT'⟩ := hcT
    have hTca : T * ca * T⁻¹ = ca⁻¹ := by
      rw [show ca = c ^ a.val from rfl]
      change MulAut.conj T (c ^ a.val) = (c ^ a.val)⁻¹
      rw [map_pow, show MulAut.conj T c = c⁻¹ from hT', inv_pow]
    have hconj : (LinearEquiv.conjAlgEquiv K T.symm.symm) caL =
        ((ca⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) := by
      rw [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.symm_symm]
      apply LinearMap.ext
      intro d
      change (T.symm.trans (ca.trans T)) d = (ca⁻¹ : D ≃ₗ[K] D) d
      simp only [LinearEquiv.trans_apply]
      have h := congrArg (fun e : D ≃ₗ[K] D => (e : D →ₗ[K] D)) hTca
      exact (LinearMap.ext_iff.mp h) d
    have hmin : minpoly K ((ca⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) = h0 := by
      have h := minpoly.algEquiv_eq (LinearEquiv.conjAlgEquiv K T.symm.symm) caL
      rw [hconj] at h
      exact h
    have hcneg : ((c ^ (-a).val : D ≃ₗ[K] D) : D →ₗ[K] D) =
        ((ca⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) := by
      rw [ZMod.val_neg_of_ne_zero a]
      have hle : a.val ≤ p := le_of_lt (ZMod.val_lt a)
      rw [pow_sub _ hle, hcp, one_mul]
    rw [hcneg]
    exact hmin
  have hmin_e : ∀ e : ZMod p, e = a ∨ e = -a →
      minpoly K ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) = h0 := by
    intro e he
    rcases he with rfl | rfl
    · rfl
    · exact hmin_neg
  have hall : ∀ j, F.U j ≤ primaryComponent x.toLinearMap h0 := by
    intro j
    have hfj : toAdd (f j) = a ∨ toAdd (f j) = -a := by
      rcases hdense j with h | h
      · left; rw [h]
      · right
        rw [h]
        exact toAdd_inv _
    have hann : aeval ((c ^ (toAdd (f j)).val : D ≃ₗ[K] D) : D →ₗ[K] D) h0 = 0 := by
      rw [← hmin_e (toAdd (f j)) hfj]
      exact minpoly.aeval K ((c ^ (toAdd (f j)).val : D ≃ₗ[K] D) : D →ₗ[K] D)
    rw [← hθrange j]
    rintro v ⟨d, rfl⟩
    rw [mem_primaryComponent]
    have hpt := aeval_apply_of_intertwines x (θ j)
      (c ^ (toAdd (f j)).val : D ≃ₗ[K] D) (fun d => hxact j d) h0 d
    rw [hann] at hpt
    simpa using hpt
  refine ⟨h0, h0deg, hall, ?_⟩
  intro h hh hX
  have hself : reciprocalPolynomial h = h := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hX
  obtain ⟨j0, hj0⟩ := frame_dense_piece_orbit hQ hT hp hp2 F hAΩ hmax hU hV f hf hfixvec hh hX hself
  have hj0' : F.U j0 ≤ primaryComponent x.toLinearMap h := by
    simpa [orbitSpace, hself, sup_idem] using hj0
  have hann : aeval ((c ^ (toAdd (f j0)).val : D ≃ₗ[K] D) : D →ₗ[K] D) h = 0 := by
    ext d
    have hpt : aeval x.toLinearMap h (θ j0 d) = 0 :=
      mem_primaryComponent.mp (hj0' (hθrange j0 ▸ ⟨d, rfl⟩))
    have hpt' := aeval_apply_of_intertwines x (θ j0)
      (c ^ (toAdd (f j0)).val : D ≃ₗ[K] D) (fun d => hxact j0 d) h d
    rw [hpt'] at hpt
    exact hθinj j0 (by simpa using hpt)
  have hfj : toAdd (f j0) = a ∨ toAdd (f j0) = -a := by
    rcases hdense j0 with h | h
    · left; rw [h]
    · right
      rw [h]
      exact toAdd_inv _
  have hdvd : h0 ∣ h := by
    rw [← hmin_e (toAdd (f j0)) hfj]
    exact minpoly.dvd K ((c ^ (toAdd (f j0)).val : D ≃ₗ[K] D) : D →ₗ[K] D) hann
  have hhdeg : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hX
  have hhmon : h.Monic := monic_of_mem_primaryFactors hh
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le h0mon hhmon hdvd (by rw [hhdeg, h0deg])

private theorem frame_dense_label {K V D : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    {Q : QuadraticForm K V} {p r n : ℕ} [NeZero p] [NeZero r]
    {A : Subgroup (V ≃ₗ[K] V)} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hK : Nat.card K = 2 ^ n)
    (hr3 : 3 ≤ r) (hnq : (r, 2 ^ n) ≠ (3, 2))
    (F : SevOm.Frame Q p A r) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V = 2 * (r + 1))
    (hdimD : finrank K D = 2) (c : D ≃ₗ[K] D) (hcp : c ^ p = 1)
    (hfix : ∀ u, c u = u → u = 0) (hcT : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹)
    (θ : Fin r → D →ₗ[K] V) (hθinj : ∀ j, Function.Injective (θ j))
    (hθrange : ∀ j, (θ j).range = F.U j)
    (hθact : ∀ (s : Multiplicative (Fin r → ZMod p)) (j : Fin r) (d : D),
      F.ι s (θ j d) = θ j ((c ^ (toAdd s j).val) d))
    (f : Fin r → Multiplicative (ZMod p)) (hf : ∀ j, toAdd (f j) ≠ 0)
    (hdense : ∀ j, f j = f 0 ∨ f j = (f 0)⁻¹)
    (hfixvec : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v)
    {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L
      (isometryCentralizer Q (F.ι (OrthTorus.piMul r p f)))) :
    GGHasLabel ⟨.twA, r - 1, n⟩ (↥L ⧸ Subgroup.center ↥L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set x : V ≃ₗ[K] V := F.ι (OrthTorus.piMul r p f) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (OrthTorus.piMul r p f)
  have hfixne : fixedSpace x ≠ ⊥ := by
    obtain ⟨v, hv0, hvfix⟩ := hfixvec
    intro hbot
    exact hv0 (by simpa [hbot] using mem_fixedSpace.mpr (hvfix x (F.mem (OrthTorus.piMul r p f))))
  have hXm : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    refine mem_primaryFactors_of_primaryComponent_ne_bot irreducible_X_sub_one monic_X_sub_one ?_
    rw [← fixedSpace_eq_primaryComponent]
    exact hfixne
  obtain ⟨h, hh, hLF⟩ := SevOm.exists_le_supportedBlock hx hL
  by_cases hX : h = X - 1
  · exfalso
    rw [hX] at hLF
    have h4 := (SevOmSmall.fixed_case_small_odd hx hL hLF).1
    exact frame_fixedSpace_lt_four hQ F hU (le_of_eq hV) f hf h4
  have hLeq : L = specialBlock Q x h := SevOm.free_case hx hp hp2 hh hX hL hLF
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hX).symm
  obtain ⟨h0, h0deg, hall, huniq⟩ :=
    frame_dense_primary hQ hT hp hp2 hpq hK F hAΩ hmax hU (le_of_eq hV) hdimD c hcp hfix hcT
      θ hθinj hθrange hθact f hf hdense hfixvec
  have hEq : h = h0 := huniq h hh hX
  have hfixed_lt : ¬ 4 ≤ finrank K (fixedSpace x) :=
    frame_fixedSpace_lt_four hQ F hU (le_of_eq hV) f hf
  have hfixed_even : Even (finrank K (fixedSpace x)) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.even_finrank_fixedSpace hx (CharP.cast_eq_zero K 2)
  have hfixed_ge : 1 ≤ finrank K (fixedSpace x) := Submodule.one_le_finrank_iff.mpr hfixne
  have hfixed2 : finrank K (fixedSpace x) = 2 := by
    obtain ⟨k, hk⟩ := hfixed_even
    omega
  have hdim_ge : 2 * r ≤ finrank K (primaryComponent x.toLinearMap h) := by
    have hle : (⨆ j : {j : Fin r // True}, F.U j.1) ≤ primaryComponent x.toLinearMap h := by
      refine iSup_le fun j => ?_
      simpa [hEq] using hall j.1
    have hdim := finrank_iSup_frame_pieces F hU (fun _ : Fin r => True)
    have hcard : Fintype.card {j : Fin r // True} = r := by simp
    rw [hcard] at hdim
    rw [← hdim]
    exact Submodule.finrank_mono hle
  have hdisj : Disjoint (primaryComponent x.toLinearMap h) (fixedSpace x) := by
    rw [fixedSpace_eq_primaryComponent]
    exact disjoint_primaryComponent_of_ne hx hh hXm hX
  have hdim_le : finrank K (primaryComponent x.toLinearMap h) ≤ 2 * r := by
    have hle := Submodule.finrank_add_finrank_le_of_disjoint hdisj
    rw [hfixed2, hV] at hle
    omega
  have hdim : finrank K (primaryComponent x.toLinearMap h) = 2 * r :=
    le_antisymm hdim_le hdim_ge
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hdeg : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hX
  have hmult : primaryMultiplicity x.toLinearMap h = r := by
    have hfr := CFSG.RankThree.PartOne.KCPrimary.finrank_primaryComponent x.toLinearMap h
    rw [hdim, hdeg] at hfr
    have : Module.finrank (AdjoinRoot h)
        (primaryComponent x.toLinearMap h) = r := by omega
    simpa [CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity] using this
  obtain ⟨ℓ, f', d, hU', B, hBsymm, hBl, -, ⟨eSU⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2.exists_selfDual_special_equiv
      (Q := Q) (x := x) hx hp hp2 hh hX hself
  have hchar : ℓ = 2 := by
    have h2 : CharP (AdjoinRoot h) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
    exact CharP.eq (AdjoinRoot h) hU'.charP h2
  have hdimE : finrank K (AdjoinRoot h) = 2 := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hEcard : Nat.card (AdjoinRoot h) = (2 ^ n) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdimE, hK]
  have hUcard := hU'.card
  rw [hEcard] at hUcard
  have hUexp : f' * d = n := by
    have hEqCard : ℓ ^ (2 * (f' * d)) = (2 ^ n) ^ 2 := hUcard.symm
    have hpow : 2 ^ (2 * (f' * d)) = 2 ^ (2 * n) := by
      simpa [hchar, pow_mul, mul_comm, mul_left_comm, mul_assoc] using hEqCard
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    omega
  have hdim_primary : Module.finrank (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) = r := by
    have hfr := CFSG.RankThree.PartOne.KCPrimary.finrank_primaryComponent x.toLinearMap h
    rw [hdim, hdeg] at hfr
    omega
  obtain ⟨b, hb⟩ := hU'.exists_orthonormal_basis (B := B) hBsymm hBl
  obtain ⟨eSU2⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.nonempty_sesqSpecialUnitaryGroup_mulEquiv_unitarySU
      (hE := hU') b hb
  rw [hdim_primary] at eSU2
  let eParam : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ (f' * d) (AdjoinRoot h) r) ≃*
      CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h) :=
    MulEquiv.subgroupCongr (by
      show CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ (f' * d) (AdjoinRoot h) r =
        CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h)
      rw [show CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ (f' * d) (AdjoinRoot h) r =
          CFSG.Open.StatedSU r (ℓ ^ (f' * d)) (AdjoinRoot h) from rfl, hchar, hUexp])
  have eStated : ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) ≃*
      CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h) :=
    eSU2.trans eParam
  let e : ↥(specialBlock Q x h) ≃* CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h) :=
    eSU.trans eStated
  have hZ : Subgroup.center (CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h)) =
      (CFSG.Open.StatedScalars (Fin r) (AdjoinRoot h)).subgroupOf
        (CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h)) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hEcard hr3 hnq).2
  let eQ : (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) ≃*
      (↥(CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h)) ⧸
        Subgroup.center ↥(CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h))) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let eProj : (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU r (2 ^ n) (AdjoinRoot h)) :=
    eQ.trans (QuotientGroup.quotientMulEquivOfEq hZ)
  rw [hLeq]
  refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (b := r - 1) (m := n)
    hEcard ?_
  have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel (by omega : 1 ≤ r)
  rw [hr1]
  exact eProj

theorem ggCommonJRowOmMinusNonsplit_dense {K : Type} [Field K] [Finite K] {p m f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    (hm : 3 ≤ m) (hmo : Odd m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {τ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c}
    (hτ : Function.Injective τ) (hsign : GGOmMinusNonsplitSignedNormalizer τ)
    (hsgn : ∀ i : Fin m, ∃ w : OrthRest.RMinus K m b c, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f))
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    {g : Fin m → Multiplicative (ZMod p)} (hD : GGCoordDense g)
    (hΛ : LargeEvenInLambda2 ⟨.twA, m - 1, f⟩) (J : Subgroup (OrthRest.RMinus K m b c))
    (hJ : IsComponentOf J (Subgroup.centralizer ({τ g} : Set (OrthRest.RMinus K m b c))))
    (hcard : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set (OrthRest.RMinus K m b c))) = p) :
    GGHasLabel ⟨.twA, m - 1, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  classical
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero m := ⟨by omega⟩
  have hpqK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  let Q : QuadraticForm K (LargeEvenMinusIdx m → K) := TableBOrth.qMinusForm K m b c
  let e := OrthTorus.rMinusEquiv K m b c
  let E₀ : Subgroup (OrthRest.RMinus K m b c) := τ.range
  have hE0ab : IsElemAbelian p E₀ := by
    have hexp : ∀ a : Fin m → Multiplicative (ZMod p), a ^ p = 1 := by
      intro a
      funext i
      apply Multiplicative.toAdd.injective
      simp only [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one,
        nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hE := CFSG.StandardType.isElemAbelian_range (p := p)
      (fun a b : Fin m → Multiplicative (ZMod p) => mul_comm a b) hexp τ
    change IsElemAbelian p τ.range
    exact hE
  have hcardE0 : Nat.card E₀ = p ^ m := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_fun,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have h3 : p ^ 3 ≤ Nat.card E₀ := by
    rw [hcardE0]
    exact Nat.pow_le_pow_right hp.one_le hm
  obtain ⟨b₀, hb₀, hb₀1⟩ := CFSG.StandardType.exists_ne_one_of_pow_le_card hp h3
  have hsc0 := CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_sc hK hp hp2 hpq hm hmo
    hirr hE0ab hcardE0
  let E₁ : Subgroup ↥(orthDerived Q) := E₀.map e.toMonoidHom
  have hE1ab : IsElemAbelian p E₁ := by
    change IsElemAbelian p (E₀.map e.toMonoidHom)
    exact hE0ab.map e.toMonoidHom
  have hE1sc := CFSG.StandardType.selfCent_map_mulEquiv e hsc0
  have hne1 : ∃ b ∈ E₁, b ≠ 1 := by
    refine ⟨e b₀, Subgroup.mem_map_of_mem e.toMonoidHom hb₀,
      fun h => hb₀1 (e.injective (by simpa using h))⟩
  obtain ⟨hAΩ, hApow, hAcomm, hmax, hneA⟩ :=
    CFSG.StandardType.map_subtype_hyps E₁ hE1ab hne1 hE1sc
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm m hirr
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx m → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, Q v = 0 := (OrthTorus.charSum_qMinusForm m hirr).2 hm
  have hpq' : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1 := Or.inr (by rw [hK]; exact hpq)
  obtain ⟨r, τ₀, F, D, i₁, i₂, i₃, c', θ, hτF, hinj, hrange, hdim, hcp, hfix, htwist, hroots,
    hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsignMove, hnoFix, hexFix⟩ :=
    OrthTorus.exists_torus_blocks (p := p) hp2 hpq' hQ hT hAΩ hApow hAcomm hmax hneA
  letI := i₁
  letI := i₂
  letI := i₃
  let Δ : OrthTorus.TBJOmData Q p (E₁.map (orthDerived Q).subtype) r :=
    { τ := τ₀, F := F, D := D, c := c', θ := θ, τ_eq := hτF, τ_inj := hinj, τ_range := hrange,
      finrank_D := hdim, c_pow := hcp, c_fix := hfix, c_twist := htwist, c_roots := hroots,
      θ_inj := hθinj, θ_range := hθrange, θ_act := hθact, normalizer := hnorm,
      swapMove := hswap, dinvMove := hdinv, signMove := hsignMove, noFixed := hnoFix,
      exFixed := hexFix }
  have hτΩ : ∀ f, Δ.τ f ∈ orthDerived Q := fun f => by
    have h : Δ.τ f ∈ Δ.τ.range := ⟨f, rfl⟩
    rw [hrange] at h
    exact hAΩ h
  let τ' : (Fin r → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c :=
    e.symm.toMonoidHom.comp (Δ.τ.codRestrict (orthDerived Q) hτΩ)
  have heτ' : ∀ f, e (τ' f) = Δ.τΩ hAΩ f := fun f => by
    show e (e.symm ((Δ.τ.codRestrict (orthDerived Q) hτΩ) f)) = Δ.τΩ hAΩ f
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hτ'inj : Function.Injective τ' := by
    intro f g hfg
    apply hinj
    have h : e (τ' f) = e (τ' g) := congrArg e hfg
    have h' : Δ.τΩ hAΩ f = Δ.τΩ hAΩ g := by simpa only [heτ'] using h
    change (Δ.τ f : (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K)) = Δ.τ g
    exact Subtype.ext_iff.mp h'
  have hτ'range : τ'.range = E₀ := by
    ext x
    exact (CFSG.StandardType.mem_range_iff_mem_comap_model e E₀ Δ.τ hτΩ hrange x).symm
  have hdom : Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := by
    rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have hpr : p ^ r = p ^ m := by
    rw [← hdom, Nat.card_congr (MonoidHom.ofInjective hτ'inj).toEquiv, hτ'range, hcardE0]
  have hr : r = m := Nat.pow_right_injective hp.two_le hpr
  subst r
  have hsign' : CommonJOmMinusNonsplit.GGOmMinusNonsplitSignedNormalizer τ' := by
    intro w hw
    let g : (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K) :=
      ((e w : ↥(orthDerived Q)) : (LargeEvenMinusIdx m → K) ≃ₗ[K]
        (LargeEvenMinusIdx m → K))
    have hAnorm : ∀ a ∈ E₁.map (orthDerived Q).subtype, g * a * g⁻¹ ∈
        E₁.map (orthDerived Q).subtype := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨e (w * x * w⁻¹), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem e.toMonoidHom (hτ'range ▸ hw x (hτ'range.symm ▸ hx))
      · have heq : e (w * x * w⁻¹) = e w * e x * e w⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        simpa only [g, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, Subgroup.coe_mul,
          Subgroup.coe_inv, map_inv] using congrArg Subtype.val heq
    obtain ⟨π, ε, hε, hrel⟩ := Δ.normalizer g hAnorm
    let eτ' : (Fin m → Multiplicative (ZMod p)) ≃* ↥τ'.range :=
      MonoidHom.ofInjective hτ'inj
    let u : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p)) :=
      fun f => eτ'.symm ⟨w * τ' f * w⁻¹, hw (τ' f) ⟨f, rfl⟩⟩
    have hu : ∀ f, τ' (u f) = w * τ' f * w⁻¹ := by
      intro f
      have h := eτ'.apply_symm_apply ⟨w * τ' f * w⁻¹, hw (τ' f) ⟨f, rfl⟩⟩
      exact congrArg Subtype.val h
    refine ⟨u, ⟨π, ε, hε, fun f i => ?_⟩, fun f => (hu f).symm⟩
    have hcoe : ∀ f, g * Δ.τ f * g⁻¹ = Δ.τ (u f) := by
      intro f
      have h := congrArg (fun x => e x) (hu f)
      rw [map_mul, map_mul, map_inv] at h
      rw [heτ' f, heτ' (u f)] at h
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
      exact h'.symm
    exact hrel f (u f) (hcoe f) i
  have hrange' : τ.range = τ'.range := by rw [hτ'range]
  obtain ⟨φ, hφ, hφnorm⟩ :=
    CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_compareTorus hτ hτ'inj hrange' hsgn hperm
      hsign'
  let g₀ : Fin m → Multiplicative (ZMod p) := φ g
  have hτg : e (τ g) = Δ.τΩ hAΩ g₀ := by
    rw [hφ g, heτ' g₀]
  let J' : Subgroup ↥(orthDerived Q) := J.map e.toMonoidHom
  have hJ'asm : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({Δ.τΩ hAΩ g₀} : Set ↥(orthDerived Q))) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ
      e.toMonoidHom e.injective
    rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e (τ g)] at h
    rwa [hτg] at h
  have hW : ∃ v : LargeEvenMinusIdx m → K, v ≠ 0 ∧ ∀ a ∈ E₁.map (orthDerived Q).subtype,
      a v = v :=
    Δ.exFixed (by
      rw [(OrthTorus.charSum_qMinusForm m hirr).1]
      exact CFSG.StandardType.modEq_neg_one_charSum (Or.inr ⟨hmo, by rw [hK]; exact hpq⟩))
  have hgdense : GGCoordDense g₀ := by
    have hφd :=
      (CommonJ.ggCoord_iff_of_normalizes (p := p) (k := m) hp hp2 hm hφnorm g).1
    exact hφd.mpr hD
  have hg₀ne : ∀ j, g₀ j ≠ 1 := fun j => (hgdense j).1
  have hden : ∀ j, g₀ j = g₀ 0 ∨ g₀ j = (g₀ 0)⁻¹ := fun j => (hgdense 0).2 j
  have hfne : ∀ j, Multiplicative.toAdd (g₀ j) ≠ 0 := by
    intro j h
    exact hg₀ne j (Multiplicative.toAdd.injective (by simpa using h))
  let L : Subgroup ((LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K)) :=
    J'.map (orthDerived Q).subtype
  have hLmap : (Subgroup.centralizer ({Δ.τΩ hAΩ g₀} : Set ↥(orthDerived Q))).map
      (orthDerived Q).subtype =
      orthDerived Q ⊓ Subgroup.centralizer
        {((Δ.τΩ hAΩ g₀ : ↥(orthDerived Q)) :
          (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K))} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe] at hz
      refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      exact congrArg Subtype.val hz
    · rintro hx
      obtain ⟨hxΩ, hxc⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hxΩ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe]
      rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
      exact Subtype.ext hxc
  have hcomp : CFSG.Assembly.IsComponentOf L
      (orthDerived Q ⊓ Subgroup.centralizer
        {((Δ.τΩ hAΩ g₀ : ↥(orthDerived Q)) :
          (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K))}) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ'asm
      (orthDerived Q).subtype Subtype.val_injective
    rwa [hLmap] at h
  have hτg' : ((Δ.τΩ hAΩ g₀ : ↥(orthDerived Q)) :
      (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K)) =
      Δ.F.ι (OrthTorus.piMul m p g₀) := by
    have hcoe : ((Δ.τΩ hAΩ g₀ : ↥(orthDerived Q)) :
        (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K)) = Δ.τ g₀ := rfl
    rw [hcoe, Δ.τ_eq g₀]
  have hL : CFSG.Assembly.IsComponentOf L
      (isometryCentralizer Q (Δ.F.ι (OrthTorus.piMul m p g₀))) := by
    have h := CFSG.StandardType.SevOm.isComponentOf_isometryCentralizer hcomp
    rwa [hτg'] at h
  have hU : ∀ j, Module.finrank K (Δ.F.U j) = 2 := by
    intro j
    rw [← Δ.θ_range j, LinearMap.finrank_range_of_inj (Δ.θ_inj j), Δ.finrank_D]
  have hVdim : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    ring
  have hΛ' : 2 ≤ m - 1 ∧ (m - 1 = 2 → 2 ≤ f) := hΛ.2
  have hnq : (m, 2 ^ f) ≠ (3, 2) := by
    intro h
    have hm3 : m = 3 := congrArg Prod.fst h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    have hf2 : 2 ≤ f := hΛ'.2 (by omega)
    have hpow : 2 ^ f = 2 ^ 1 := by rw [h2]; norm_num
    have hf1 : f = 1 := Nat.pow_right_injective (le_refl 2) hpow
    omega
  have hlabel : GGHasLabel ⟨.twA, m - 1, f⟩ (↥L ⧸ Subgroup.center ↥L) :=
    frame_dense_label (Q := Q) (p := p) (r := m) (n := f) (D := Δ.D)
      hQ hT hp hp2 hpqK hK hm hnq Δ.F hAΩ hmax hU hVdim Δ.finrank_D Δ.c Δ.c_pow Δ.c_fix
      Δ.c_twist Δ.θ Δ.θ_inj Δ.θ_range Δ.θ_act g₀ hfne hden hW hL
  have eJJ' : ↥J ≃* ↥J' := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  have eJ'L : ↥J' ≃* ↥L :=
    Subgroup.equivMapOfInjective J' (orthDerived Q).subtype Subtype.val_injective
  exact CFSG.StandardType.ggHasLabel_quotCenter_of_mulEquiv (eJJ'.trans eJ'L).symm hlabel

end CommonJOmMinusNonsplit

end CFSG.StandardType

end
