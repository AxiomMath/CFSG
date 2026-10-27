module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofNormal
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofFour
public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofGenL3
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofInv
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14.Proof142Res
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

theorem step142LowerGenL3PGL_of_model (hM : KS142L3PGLGenModel) : Step142LowerGenL3PGL := by
  intro G _ _ A c L h hL3 hL34 hPGLA hstar hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hD.commute ha hb
  obtain ⟨x, hxA, hx⟩ := hx
  obtain ⟨d, hdAL, hd1, -⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGLA)
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD
    (Sec13.facts_of_isZ3PGLThreePi hD hPGLA).2.1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := Sec13.card_zpowers_sup_zpowers_eq_nine hA h27 hcA hdA hd1 hcd
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN hcA
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hAN hxA
  have hσc : ∀ k : ℤ, ∀ hk : c ^ k ∈ Subgroup.normalizer (L : Set G),
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨c ^ k, hk⟩) = 1 := by
    intro k hk
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      have hlc : (l : G) * c ^ k = c ^ k * l :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)) k)
      rw [← hlc, mul_inv_cancel_right]
  have hcLθ := hD.mem_thetaComponentsAt
  have hxcd : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro hxcd
    obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hcomm c hcA d hdA) hxcd
    have hx' := inducesTypeOn_mul_of_eq_one hx (Subgroup.zpow_mem _ hcN (-i))
      (hσc (-i) (Subgroup.zpow_mem _ hcN (-i)))
    apply Sec16.Proof1613Fix.not_mem_of_inducesTypeOn_three hcLθ hx'
    rw [hij, mul_assoc, (hcomm _ (Subgroup.zpow_mem _ hdA j) _
      (Subgroup.zpow_mem _ hcA (-i))), ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero,
      one_mul]
    exact Subgroup.zpow_mem _ hdL j
  have hx0 := hx
  obtain ⟨hxN', π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx0
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hLp : Group.IsPerfect (↥L ⧸ θ) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hcLθ).1
  have hperf : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  set σx := thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN'⟩) with hσx
  have hact' : ∀ z : ↥L ⧸ θ,
      ((e (σx z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ :=
    hact
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set db : ↥L ⧸ θ := QuotientGroup.mk' _ d' with hdb
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (Sec16.Proof1613Inv.isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _)
      (Subgroup.one_mem _) (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e db).2
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) K := by
    intro hsZ
    apply hdb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hdb3,
      map_one, Subgroup.coe_one]
  have hxd : x * d = d * x := hcomm x hxA d hdA
  have hfix : σx db = db := by
    rw [hσx, hdb, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hxd, mul_inv_cancel_right]
  have h1 := hact' db
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  have hgen := hM π p f K hπ hK hq hperf y s hyH hsH hy3 hs hsZ hs3 hysZ
  set σd := thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) with hσd
  have hσdc : σd = MulAut.conj db := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [hσd, thetaQuotMulAut_mk, MulAut.conj_apply, hdb, QuotientGroup.mk'_apply,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
  have hed : ∀ z, e (σd z) = Res8Hess.conjM' hπ hsH (e z) := by
    intro z
    apply Subtype.ext
    rw [Res8Hess.coe_conjM', hσdc, MulAut.conj_apply, map_mul, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hse]
  have hex : ∀ z, e (σx z) = Res8Hess.conjM' hπ hyH (e z) := by
    intro z
    apply Subtype.ext
    rw [Res8Hess.coe_conjM']
    exact hact' z
  have hmem : ∀ X ∈ invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH),
      X.map e.symm.toMonoidHom ∈ {X : Subgroup (↥L ⧸ θ) | ¬ 3 ∣ Nat.card X ∧
        ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} := by
    intro X hX
    obtain ⟨hX3, hXy, hXs⟩ := hX
    set X' := X.map e.symm.toMonoidHom with hX'
    refine ⟨by rwa [hX', Subgroup.card_map_of_injective e.symm.injective], ?_⟩
    let Stab : Subgroup (MulAut (↥L ⧸ θ)) :=
      { carrier := {τ | X'.map τ.toMonoidHom ≤ X'}
        mul_mem' := fun {a b} ha hb => by
          rintro _ ⟨v, hv, rfl⟩
          exact ha ⟨b v, hb ⟨v, hv, rfl⟩, rfl⟩
        one_mem' := by
          change X'.map (1 : MulAut (↥L ⧸ θ)).toMonoidHom ≤ X'
          intro z hz
          obtain ⟨w, hw, rfl⟩ := hz
          exact hw
        inv_mem' := fun {a} ha => by
          change X'.map a⁻¹.toMonoidHom ≤ X'
          refine L3PGL.map_le_of_map_symm_le ?_
          rw [MulAut.inv_def, MulEquiv.symm_symm]
          exact ha }
    have hStab : ∀ τ : MulAut (↥L ⧸ θ), τ ∈ Stab ↔ X'.map τ.toMonoidHom ≤ X' :=
      fun τ => Iff.rfl
    have hdS : σd ∈ Stab := by
      rw [hStab]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨Res8Hess.conjM' hπ hsH z, hXs ⟨z, hz, rfl⟩, ?_⟩
      apply e.injective
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      rw [hed, MulEquiv.apply_symm_apply]
    have hxS : σx ∈ Stab := by
      rw [hStab]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨Res8Hess.conjM' hπ hyH z, hXy ⟨z, hz, rfl⟩, ?_⟩
      apply e.injective
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      rw [hex, MulEquiv.apply_symm_apply]
    intro σ hσ
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    obtain ⟨i, j, m, -, rfl⟩ := exists_pow_mul_eq hA h27 hcA hdA hxA h9 hxcd haA
    have hdec : (⟨c ^ i * d ^ j * x ^ m, haN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨c, hcN⟩ ^ i * ⟨d, hdN⟩ ^ j * ⟨x, hxN'⟩ ^ m := Subtype.ext (by simp)
    rw [← hStab, hdec]
    simp only [map_mul, map_zpow, map_pow]
    have hc1 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨c, hcN⟩) = 1 := by
      have := hσc 1 (by simpa using hcN)
      simpa using this
    rw [hc1, one_zpow, one_mul]
    exact Stab.mul_mem (Stab.zpow_mem hdS j) (Stab.pow_mem hxS m)
  rw [eq_top_iff]
  intro z _
  have hz : e z ∈ sSup (invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH)) :=
    hgen ▸ Subgroup.mem_top _
  have hle : (sSup (invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH))).map
      e.symm.toMonoidHom ≤ sSup {X : Subgroup (↥L ⧸ θ) | ¬ 3 ∣ Nat.card X ∧
        ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun X hX => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hmem X hX)
  have hmem' : z ∈ (sSup (invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH))).map
      e.symm.toMonoidHom := ⟨e z, hz, by simp⟩
  exact hle hmem'

theorem ks142L3PGLGenStd_of (hU : KS142L3PGLGenStdU) (h4 : KS142L3PGLGenStdFour) :
    KS142L3PGLGenStd := by
  intro π p f K _ hπ hK hq hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
  cases π
  · exact hU p f K hπ hK hq hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
  · by_cases hq4 : p ^ f = 4
    · have hp2 : p = 2 := by
        have hdvd : p ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hq4]
          exact dvd_pow_self p (by have := hK.one_le; omega)
        exact (Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp
          (hK.prime.dvd_of_dvd_pow hdvd)
      subst hp2
      have hf2 : f = 2 := Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by rw [hq4])
      subst hf2
      exact h4 K hπ hK hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
    · have := hK.finite
      exact L3PGL.ks142L3PGLGenStd_linear hπ hK hq hq4 hτ hτ1 hcβ hd hcβm hβ

theorem step142LowerGenL3PGL_of (hU : KS142L3PGLGenStdU) (h4 : KS142L3PGLGenStdFour) :
    Step142LowerGenL3PGL :=
  step142LowerGenL3PGL_of_model (ks142L3PGLGenModel_of_std (ks142L3PGLGenStd_of hU h4))

theorem step142LowerGenL3PGL_of_U (hU : KS142L3PGLGenStdU) : Step142LowerGenL3PGL :=
  step142LowerGenL3PGL_of hU L3PGL.ks142L3PGLGenStdFour

end CFSG.RankThree.PartTwo.Sec14
