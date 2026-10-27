module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2FullSplitTorusFieldFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The concrete full split torus of `PGL₂(K)` and its dihedral normalizer

The full standard split torus `U := (pGammaL2FullSplitTorus K).range` is
cyclic of order `|K| − 1`; its canonical involution is the projective image
of `diag(-1, 1)`, i.e. `s := pGammaL2FullSplitTorus K (-1)`.  The reflector
`w` (the projective image of `!![0, 1; 1, 0]`) satisfies `w * w = 1`,
`w ∉ U`, and inverts `U` by conjugation, so the centralizer of `s` is the
dihedral group `U ⊔ ⟨w⟩`, which has twice the order of `U`.  Moreover `U`
is not contained in the derived subgroup `PGL₂(K)'`.  This is the concrete
version of `pgl2_split_torus_centralizer_data` with the abstract
existential torus replaced by the fixed range of
`pGammaL2FullSplitTorus`.
-/

open scoped Pointwise MatrixGroups

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix

universe u

private lemma two_ne_zero_of_odd_card (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  intro h2
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd_char : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).mp h2
  have hchar2 : ringChar K = 2 := by
    rcases hdvd_char with ⟨c, hc⟩
    cases c with
    | zero => norm_num at hc
    | succ c =>
        cases c with
        | zero => omega
        | succ c =>
            exfalso
            have hrc_pos : 0 < ringChar K := by
              by_contra h
              have hz : ringChar K = 0 := by omega
              rw [hz] at hc
              norm_num at hc
            have hrc_le : ringChar K ≤ 1 := by nlinarith
            have hrc1 : ringChar K = 1 := by omega
            have hsub : Subsingleton K := (ringChar.ringChar_eq_one (R := K)).mp hrc1
            exact not_subsingleton K hsub
  have hdvd_card : 2 ∣ Fintype.card K :=
    (prime_dvd_char_iff_dvd_card (R := K) (p := 2)).mp (by simpa [hchar2])
  have hprime_dvd : (2 : ℕ) ∣ Nat.card K := by
    simpa [Nat.card_eq_fintype_card] using hdvd_card
  exact hodd.not_two_dvd_nat hprime_dvd

private lemma card_sup_eq_mul_of_disjoint_of_le_normalizer_card_four
    {G : Type u} [Group G]
    (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

set_option maxHeartbeats 8000000 in
/-- The standard full split torus involution has dihedral normalizer: its
centralizer is `U ⊔ ⟨w⟩`, where `U` is the range of the concrete full split
torus `pGammaL2FullSplitTorus K` and `s` is its canonical involution
`pGammaL2FullSplitTorus K (-1)`. -/
public theorem pgl2_fullSplitTorus_centralizer_data
    (K : Type u) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    ∃ w : PGL2 K,
      IsCyclic (pGammaL2FullSplitTorus K).range ∧
      Nat.card (pGammaL2FullSplitTorus K).range = Nat.card K - 1 ∧
      pGammaL2FullSplitTorus K (-1 : Kˣ) ∈ (pGammaL2FullSplitTorus K).range ∧
      IsInvolution (pGammaL2FullSplitTorus K (-1 : Kˣ)) ∧
      w ∉ (pGammaL2FullSplitTorus K).range ∧
      w * w = 1 ∧
      (∀ x : PGL2 K, x ∈ (pGammaL2FullSplitTorus K).range → w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({pGammaL2FullSplitTorus K (-1 : Kˣ)} : Set (PGL2 K)) =
        (pGammaL2FullSplitTorus K).range ⊔ Subgroup.zpowers w ∧
      Nat.card ((pGammaL2FullSplitTorus K).range ⊔ Subgroup.zpowers w :
        Subgroup (PGL2 K)) =
        2 * Nat.card (pGammaL2FullSplitTorus K).range ∧
      ¬ (pGammaL2FullSplitTorus K).range ≤ commutator (PGL2 K) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  rcases hK with ⟨p, n, hp, hpodd, hn, hKcard⟩
  have hodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hpodd.pow
  let diagGL (k : Kˣ) : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![(k : K), 1]) (by
        simp [Matrix.det_diagonal, Fin.prod_univ_two, k.ne_zero])
  let diagHom : Kˣ →* GL (Fin 2) K :=
    { toFun := diagGL
      map_one' := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [diagGL]
      map_mul' := by
        intro k l
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] }
  let torus : Kˣ →* PGL2 K := pGammaL2FullSplitTorus K
  have htorus_injective : Function.Injective torus := by
    intro k l hkl
    change Matrix.ProjGenLinGroup.mk (diagHom k) =
      Matrix.ProjGenLinGroup.mk (diagHom l) at hkl
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hkl with ⟨a, ha⟩
    have h11 := congrArg (fun A : GL (Fin 2) K ↦
      ((A : Matrix (Fin 2) (Fin 2) K) 1 1)) ha
    have h00 := congrArg (fun A : GL (Fin 2) K ↦
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) ha
    have ha1 : (a : K) = 1 := by
      simpa [diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using h11
    apply Units.ext
    simpa [diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two, ha1] using h00
  let U : Subgroup (PGL2 K) := torus.range
  have hUcyclic : IsCyclic U := by
    let e : Kˣ ≃* U := MulEquiv.ofBijective torus.rangeRestrict
      ⟨by
        intro a b hab
        apply htorus_injective
        exact congrArg Subtype.val hab,
        MonoidHom.rangeRestrict_surjective torus⟩
    exact e.isCyclic.mp (inferInstance : IsCyclic Kˣ)
  have hUcard : Nat.card U = Nat.card K - 1 := by
    let e : Kˣ ≃* U := MulEquiv.ofBijective torus.rangeRestrict
      ⟨by
        intro a b hab
        apply htorus_injective
        exact congrArg Subtype.val hab,
        MonoidHom.rangeRestrict_surjective torus⟩
    calc
      Nat.card U = Nat.card Kˣ := (Nat.card_congr e.toEquiv).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  let wGL : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by
      simp [Matrix.det_fin_two])
  let w : PGL2 K := Matrix.ProjGenLinGroup.mk wGL
  have hw_not_mem : w ∉ U := by
    intro hw
    rcases hw with ⟨k, hk⟩
    have hk' := hk.symm
    change Matrix.ProjGenLinGroup.mk wGL =
      Matrix.ProjGenLinGroup.mk (diagHom k) at hk'
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hk' with ⟨a, ha⟩
    have h01 := congrArg (fun A : GL (Fin 2) K ↦
      ((A : Matrix (Fin 2) (Fin 2) K) 0 1)) ha
    simp [wGL, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hwGL_sq : wGL * wGL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [wGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hw_sq : w * w = 1 := by
    change Matrix.ProjGenLinGroup.mk wGL *
      Matrix.ProjGenLinGroup.mk wGL = 1
    rw [← map_mul, hwGL_sq, map_one]
  have hw_inv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hw_sq).symm
  have hweyl_torus (k : Kˣ) :
      w * torus k * w⁻¹ = (torus k)⁻¹ := by
    rw [hw_inv]
    have hGL : wGL * diagHom k * wGL =
        Matrix.GeneralLinearGroup.scalar (Fin 2) k * diagHom k⁻¹ := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [wGL, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two]
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk (diagHom k) *
          Matrix.ProjGenLinGroup.mk wGL =
        (Matrix.ProjGenLinGroup.mk (diagHom k))⁻¹
    rw [← map_mul, ← map_mul, hGL, map_mul,
      Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    rw [map_inv diagHom k]
    exact map_inv Matrix.ProjGenLinGroup.mk (diagHom k)
  have hneg_ne_one : (-1 : Kˣ) ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := by
      have hval := congrArg (fun x : Kˣ => (x : K)) h
      have hk : (-1 : K) = 1 := by simpa using hval
      calc
        (2 : K) = (1 : K) + 1 := by norm_num
        _ = (-1 : K) + 1 := by rw [hk]
        _ = 0 := by simp
    exact two_ne_zero_of_odd_card K hodd h2
  let s : PGL2 K := torus (-1 : Kˣ)
  have hsU : s ∈ U := ⟨(-1 : Kˣ), rfl⟩
  have hssq : s * s = 1 := by
    change torus (-1 : Kˣ) * torus (-1 : Kˣ) = 1
    rw [← map_mul]
    have hk : (-1 : Kˣ) * (-1 : Kˣ) = 1 := by ext; simp
    rw [hk, map_one]
  have hsne : s ≠ 1 := by
    intro h
    apply hneg_ne_one
    apply htorus_injective
    simpa using h
  have hC_le : Subgroup.centralizer ({s} : Set (PGL2 K)) ≤
      U ⊔ Subgroup.zpowers w := by
    intro x hx
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    have hcomm : Matrix.ProjGenLinGroup.mk A * s =
        s * Matrix.ProjGenLinGroup.mk A :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hmul : Matrix.ProjGenLinGroup.mk (A * diagHom (-1 : Kˣ)) =
        Matrix.ProjGenLinGroup.mk (diagHom (-1 : Kˣ) * A) := by
      simpa [s, torus, pGammaL2FullSplitTorus, pGammaL2FullSplitTorusGL,
        diagHom, diagGL, map_mul] using hcomm
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hmul with ⟨u, hu⟩
    let a : K := (A : Matrix (Fin 2) (Fin 2) K) 0 0
    let b : K := (A : Matrix (Fin 2) (Fin 2) K) 0 1
    let c : K := (A : Matrix (Fin 2) (Fin 2) K) 1 0
    let d : K := (A : Matrix (Fin 2) (Fin 2) K) 1 1
    have h00 : a * (u : K) = a := by
      have heq := congrArg (fun M : GL (Fin 2) K ↦
        ((M : Matrix (Fin 2) (Fin 2) K) 0 0)) hu
      simpa [a, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using heq
    have h11 : d * (u : K) = d := by
      have heq := congrArg (fun M : GL (Fin 2) K ↦
        ((M : Matrix (Fin 2) (Fin 2) K) 1 1)) hu
      simpa [d, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using heq
    have h01 : b * (u : K) = -b := by
      have heq := congrArg (fun M : GL (Fin 2) K ↦
        ((M : Matrix (Fin 2) (Fin 2) K) 0 1)) hu
      simpa [b, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using heq
    have h10 : -c * (u : K) = c := by
      have heq := congrArg (fun M : GL (Fin 2) K ↦
        ((M : Matrix (Fin 2) (Fin 2) K) 1 0)) hu
      simpa [c, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using heq
    by_cases hu1 : (u : K) = 1
    · have hb0 : b = 0 := by
        have hb : b = -b := by simpa [hu1] using h01
        have h2b : b + b = 0 := by simpa [← hb] using (neg_add_cancel b)
        exact (mul_eq_zero.mp (by simpa [two_mul] using h2b)).resolve_left
          (two_ne_zero_of_odd_card K hodd)
      have hc0 : c = 0 := by
        have hc : c = -c := by simpa [hu1] using h10.symm
        have h2c : c + c = 0 := by simpa [← hc] using (neg_add_cancel c)
        exact (mul_eq_zero.mp (by simpa [two_mul] using h2c)).resolve_left
          (two_ne_zero_of_odd_card K hodd)
      have ha_ne : a ≠ 0 := by
        intro ha0
        have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
        have hval : (A : Matrix (Fin 2) (Fin 2) K).det = a * d - b * c := by
          simp [a, b, c, d, Matrix.det_fin_two]
        rw [hval, hb0, hc0, ha0] at hdet
        simpa using hdet
      have hd_ne : d ≠ 0 := by
        intro hd0
        have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
        have hval : (A : Matrix (Fin 2) (Fin 2) K).det = a * d - b * c := by
          simp [a, b, c, d, Matrix.det_fin_two]
        rw [hval, hb0, hc0, hd0] at hdet
        simpa using hdet
      have hA_diag : (A : Matrix (Fin 2) (Fin 2) K) =
          Matrix.diagonal ![a, d] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb0, hc0]
      let k : Kˣ := Units.mk0 (a / d) (by
        exact div_ne_zero ha_ne hd_ne)
      have hmk : Matrix.ProjGenLinGroup.mk A =
          Matrix.ProjGenLinGroup.mk (diagHom k) := by
        apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
        refine ⟨Units.mk0 (d⁻¹) (inv_ne_zero hd_ne), ?_⟩
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [diagHom, diagGL, k, hA_diag, Matrix.GeneralLinearGroup.scalar,
            Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv, hd_ne, inv_ne_zero]
      exact (le_sup_left : U ≤ U ⊔ Subgroup.zpowers w)
        ⟨k, hmk.symm⟩
    · have ha0 : a = 0 := by
        have h : a * ((u : K) - 1) = 0 := by
          calc
            a * ((u : K) - 1) = a * (u : K) - a := by ring
            _ = 0 := by rw [h00]; ring
        exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hu1)
      have hd0 : d = 0 := by
        have h : d * ((u : K) - 1) = 0 := by
          calc
            d * ((u : K) - 1) = d * (u : K) - d := by ring
            _ = 0 := by rw [h11]; ring
        exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hu1)
      have hb_ne : b ≠ 0 := by
        intro hb0
        have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
        have hval : (A : Matrix (Fin 2) (Fin 2) K).det = a * d - b * c := by
          simp [a, b, c, d, Matrix.det_fin_two]
        rw [hval, ha0, hd0, hb0] at hdet
        simpa using hdet
      have hc_ne : c ≠ 0 := by
        intro hc0
        have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
        have hval : (A : Matrix (Fin 2) (Fin 2) K).det = a * d - b * c := by
          simp [a, b, c, d, Matrix.det_fin_two]
        rw [hval, ha0, hd0, hc0] at hdet
        simpa using hdet
      have hA_anti : A =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 b hb_ne) *
            (wGL * diagGL (Units.mk0 (c / b) (div_ne_zero hc_ne hb_ne))) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [a, b, c, d, wGL, diagGL, diagHom, ha0, hd0,
            Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
            Matrix.vecMul, Fin.sum_univ_two, div_eq_mul_inv, hb_ne]
        all_goals field_simp [b, hb_ne]
      let k : Kˣ := Units.mk0 (c / b) (div_ne_zero hc_ne hb_ne)
      have hmk' : Matrix.ProjGenLinGroup.mk A =
          w * torus k := by
        calc
          Matrix.ProjGenLinGroup.mk A =
              Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 b hb_ne) *
                  (wGL * diagGL k)) := by
                rw [hA_anti]
          _ = Matrix.ProjGenLinGroup.mk (wGL * diagGL k) := by
            rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
          _ = Matrix.ProjGenLinGroup.mk wGL * Matrix.ProjGenLinGroup.mk (diagGL k) := by
            rw [map_mul]
          _ = w * torus k := rfl
      have hmem' : Matrix.ProjGenLinGroup.mk A ∈
          Subgroup.zpowers w ⊔ U := by
        rw [hmk']
        exact Subgroup.mul_mem_sup
          (Subgroup.mem_zpowers w) (show torus k ∈ U from ⟨k, rfl⟩)
      have hsup : Subgroup.zpowers w ⊔ U = U ⊔ Subgroup.zpowers w :=
        sup_comm (Subgroup.zpowers w) U
      rwa [hsup] at hmem'
  have hC_ge : U ⊔ Subgroup.zpowers w ≤
      Subgroup.centralizer ({s} : Set (PGL2 K)) := by
    apply sup_le
    · intro x hx
      rcases hx with ⟨k, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change torus k * torus (-1 : Kˣ) = torus (-1 : Kˣ) * torus k
      rw [← map_mul, ← map_mul]
      congr 1
      ext
      simp
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        w * s = (w * s * w⁻¹) * w := by group
        _ = s⁻¹ * w := by rw [hweyl_torus (-1 : Kˣ)]
        _ = s * w := by
          rw [show s⁻¹ = s by
            exact inv_eq_of_mul_eq_one_right hssq]
  have hw_ne_one : w ≠ 1 := by
    intro h
    apply hw_not_mem
    simpa [h]
  have hw_order : orderOf w = 2 := by
    exact orderOf_eq_prime (x := w) (p := 2)
      (by simpa [pow_two] using hw_sq) hw_ne_one
  have hzpow2 : Nat.card (Subgroup.zpowers w) = 2 := by
    simp [Nat.card_zpowers, hw_order]
  have hTeq : ∀ z : Subgroup.zpowers w,
      z = 1 ∨ z = ⟨w, Subgroup.mem_zpowers w⟩ := by
    intro z
    by_cases hz : z = 1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' (1 : Subgroup.zpowers w)).mp hzpow2 with
        ⟨z0, _hz0ne, hz0uniq⟩
      have hwne : (⟨w, Subgroup.mem_zpowers w⟩ : Subgroup.zpowers w) ≠ 1 := by
        intro h
        exact hw_ne_one (congrArg Subtype.val h)
      exact Or.inr ((hz0uniq z hz).trans (hz0uniq ⟨w, Subgroup.mem_zpowers w⟩ hwne).symm)
  have hUinf : Disjoint U (Subgroup.zpowers w) := by
    rw [Subgroup.disjoint_def]
    intro x hxU hxw
    rcases hTeq ⟨x, hxw⟩ with hx1 | hxw'
    · exact congrArg Subtype.val hx1
    · exfalso
      apply hw_not_mem
      have hxw_eq : x = w := congrArg Subtype.val hxw'
      rwa [hxw_eq] at hxU
  have hw_conj_mem (x : PGL2 K) (hx : x ∈ U) : w * x * w⁻¹ ∈ U := by
    rcases hx with ⟨k, rfl⟩
    change w * torus k * w⁻¹ ∈ U
    rw [hweyl_torus k]
    rw [← map_inv]
    exact ⟨k⁻¹, rfl⟩
  have hw_normalizes : Subgroup.zpowers w ≤
      Subgroup.normalizer (U : Set (PGL2 K)) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · exact hw_conj_mem x
    · intro hxw'
      have hxU'' : w * (w * x * w⁻¹) * w⁻¹ ∈ U :=
        hw_conj_mem (w * x * w⁻¹) hxw'
      have hx' : w * (w * x * w⁻¹) * w⁻¹ = x := by
        rw [hw_inv]
        calc
          w * (w * x * w) * w = (w * w) * x * (w * w) := by group
          _ = x := by rw [hw_sq]; simp
      rwa [hx'] at hxU''
  have hsup_card : Nat.card (U ⊔ Subgroup.zpowers w : Subgroup (PGL2 K)) =
      2 * Nat.card U := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer_card_four
      U (Subgroup.zpowers w) hw_normalizes hUinf]
    rw [hzpow2]
    rw [mul_comm]
  have hUnot_comm : ¬ U ≤ commutator (PGL2 K) := by
    intro hUle
    have hchar : ringChar K ≠ 2 := by
      intro hchar
      have heven : Fintype.card K % 2 = 0 :=
        FiniteField.even_card_of_char_two hchar
      have hodd' : Odd (Fintype.card K) := by
        simpa [Nat.card_eq_fintype_card] using hodd
      exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero heven)
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      exact ha IsSquare.zero
    let k : Kˣ := Units.mk0 a ha0
    have hmemU : torus k ∈ U := ⟨k, rfl⟩
    have hmemPSL : torus k ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := K)).range :=
      (hUle.trans (pgl2_commutator_le_psl2_range K)) hmemU
    have hsq : IsSquare ((diagHom k).det : K) :=
      (pgl2_mk_mem_psl2_range_iff_det_isSquare (diagHom k)).mp hmemPSL
    apply ha
    simpa [diagHom, diagGL, Matrix.det_diagonal, Fin.prod_univ_two, k] using hsq
  refine ⟨w, hUcyclic, hUcard, hsU, ⟨hsne, by simpa [pow_two] using hssq⟩,
    hw_not_mem, hw_sq,
    (by intro x hx; rcases hx with ⟨k, rfl⟩; exact hweyl_torus k),
    hC_le.antisymm hC_ge, hsup_card, hUnot_comm⟩

end CFSG.GorensteinWalter
