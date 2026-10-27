module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.E6ThreeModel
  CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

private theorem zlc_zeta_zpow_eq_one (ζ : Kˣ) (hζ : ζ ^ 3 = 1) {e : ℤ}
    (he : (3 : ℤ) ∣ e) : ζ ^ e = 1 := by
  obtain ⟨m, rfl⟩ := he
  have h3 : ζ ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hζ
  rw [zpow_mul, h3, one_zpow]

theorem zl_isogeny_minTorus_kappa (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    e6Isogeny K (minTorus e6Data_valid K (zetaVec ζ hζ kappa)) = 1 := by
  let κ : Fin Tag.E6.rank → ZMod 3 := kappa
  change e6Isogeny K (minTorus e6Data_valid K (zetaVec (τ := Tag.E6) ζ hζ κ)) = 1
  apply Subtype.ext
  rw [e6Isogeny_minTorus]
  have hparams : e6RootParams (zetaVec (τ := Tag.E6) ζ hζ κ) = 1 := by
    have hval : ∀ i : Fin Tag.E6.rank,
        (zetaVec (τ := Tag.E6) ζ hζ κ) i = ζ ^ (κ i).val := fun i => rfl
    funext j
    unfold e6RootParams
    have hprod : ∀ l : Fin Tag.E6.rank,
        (zetaVec (τ := Tag.E6) ζ hζ κ l) ^ Tag.cartan Tag.E6 l j =
          ζ ^ (((κ l).val : ℤ) * Tag.cartan Tag.E6 l j) := by
      intro l
      rw [hval l, ← zpow_natCast (n := (κ l).val) (a := ζ), ← zpow_mul]
    rw [Finset.prod_congr rfl (fun l _ => hprod l)]
    rw [Finset.prod_zpow_eq_zpow_sum]
    have hdiv : (3 : ℤ) ∣ ∑ l : Fin Tag.E6.rank,
        ((κ l).val : ℤ) * Tag.cartan Tag.E6 l j := by
      change (3 : ℤ) ∣ ∑ l : Fin Tag.E6.rank,
        ((kappa l).val : ℤ) * Tag.cartan Tag.E6 l j
      fin_cases j <;> decide +kernel
    exact zlc_zeta_zpow_eq_one ζ hζ hdiv
  rw [hparams, rootDiagUnit_one, OneMemClass.coe_one]

theorem zl_minTorus_kappa_ne_one (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    minTorus e6Data_valid K (zetaVec ζ hζ kappa) ≠ 1 := by
  intro h
  let κ : Fin Tag.E6.rank → ZMod 3 := kappa
  change minTorus e6Data_valid K (zetaVec (τ := Tag.E6) ζ hζ κ) = 1 at h
  have h1 : minTorus e6Data_valid K (zetaVec (τ := Tag.E6) ζ hζ κ) =
      minTorus e6Data_valid K 1 := by rw [h, map_one]
  have h' := minTorus_injective e6Data_valid K h1
  have hval : ∀ i : Fin Tag.E6.rank,
      (zetaVec (τ := Tag.E6) ζ hζ κ) i = ζ ^ (κ i).val := fun i => rfl
  have h0 := congrFun h' (⟨0, by decide⟩ : Fin Tag.E6.rank)
  rw [hval (⟨0, by decide⟩ : Fin Tag.E6.rank), Pi.one_apply] at h0
  have hk0 : (κ (⟨0, by decide⟩ : Fin Tag.E6.rank)).val = 1 := by decide +kernel
  rw [hk0] at h0
  have hζ1 : ζ = 1 := by simpa using h0
  rw [hζ1, orderOf_one] at hζo
  exact absurd hζo (by decide)

theorem zl_minTorus_kappa_mem (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (S : Subgroup (e6Data_valid.minGroup K)) (hS : ∀ i, e6Data_valid.hm K i ζ ∈ S) :
    minTorus e6Data_valid K (zetaVec ζ hζ kappa) ∈ S := by
  let κ : Fin Tag.E6.rank → ZMod 3 := kappa
  change minTorus e6Data_valid K (zetaVec (τ := Tag.E6) ζ hζ κ) ∈ S
  have hzeta : zetaVec (τ := Tag.E6) ζ hζ κ =
      ∏ i : Fin Tag.E6.rank, (Pi.mulSingle i ζ : Fin Tag.E6.rank → Kˣ) ^ (κ i).val := by
    have hval : ∀ i : Fin Tag.E6.rank,
        (zetaVec (τ := Tag.E6) ζ hζ κ) i = ζ ^ (κ i).val := fun i => rfl
    funext j
    rw [hval j]
    have hprod : (∏ i : Fin Tag.E6.rank,
          ((Pi.mulSingle i ζ : Fin Tag.E6.rank → Kˣ) ^ (κ i).val) j) =
        ((Pi.mulSingle j ζ : Fin Tag.E6.rank → Kˣ) ^ (κ j).val) j := by
      refine Finset.prod_eq_single j (fun i _ hij => ?_)
        (fun hj => absurd (Finset.mem_univ j) hj)
      rw [Pi.pow_apply, Pi.mulSingle_apply, if_neg hij.symm, one_pow]
    rw [Finset.prod_apply, hprod, Pi.pow_apply, Pi.mulSingle_apply, if_pos rfl]
  rw [hzeta]
  have key : ∀ t : Finset (Fin Tag.E6.rank),
      minTorus e6Data_valid K (Finset.prod t
        (fun i => (Pi.mulSingle i ζ : Fin Tag.E6.rank → Kˣ) ^ (κ i).val)) ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact S.one_mem
    | insert a t ha ih =>
        rw [Finset.prod_insert ha, map_mul]
        refine mul_mem ?_ ih
        rw [map_pow, minTorus_mulSingle]
        exact S.pow_mem (hS a) _
  exact key Finset.univ

theorem zl_ker_isogeny_eq_zpowers (hK3 : 3 ∣ Nat.card K - 1) (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) :
    (e6Isogeny K).ker = Subgroup.zpowers (minTorus e6Data_valid K (zetaVec ζ hζ kappa)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite (e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  let κ : Fin Tag.E6.rank → ZMod 3 := kappa
  change (e6Isogeny K).ker =
    Subgroup.zpowers (minTorus e6Data_valid K (zetaVec (τ := Tag.E6) ζ hζ κ))
  set z := minTorus e6Data_valid K (zetaVec (τ := Tag.E6) ζ hζ κ) with hzdef
  have hker : (e6Isogeny K).ker = Subgroup.center (e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)
  have hcard : Nat.card ((e6Isogeny K).ker) = 3 := by
    rw [hker, (card_center_e6 K).1]
    exact Nat.gcd_eq_left hK3
  have hz : z ∈ (e6Isogeny K).ker := by
    rw [MonoidHom.mem_ker]
    exact zl_isogeny_minTorus_kappa ζ hζ
  have hz1 : z ≠ 1 := zl_minTorus_kappa_ne_one ζ hζ hζo
  have horder : orderOf z = 3 := by
    have hdvd : orderOf z ∣ 3 := by
      have h1 := Subgroup.orderOf_dvd_natCard (e6Isogeny K).ker hz
      rw [hcard] at h1
      exact h1
    exact orderOf_eq_prime ((orderOf_dvd_iff_pow_eq_one).mp hdvd) hz1
  have hcardzp : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, horder]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hz) (by
    rw [hcard, hcardzp])).symm

end CFSG.StandardType.E6Dep.ZL

end
