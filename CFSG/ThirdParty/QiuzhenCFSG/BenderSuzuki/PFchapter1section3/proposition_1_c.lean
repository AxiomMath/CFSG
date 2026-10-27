module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Projectivization.Action
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_e
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_d
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_10_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.lemma_3_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import Mathlib.FieldTheory.Fixed

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII MatrixGroups
open scoped LinearAlgebra.Projectivization
open scoped Pointwise

universe u v

set_option maxHeartbeats 12000000

set_option maxHeartbeats 10000000 in
private theorem suzuki_exists_simultaneous_standardizer
    (k : ℕ) (hk : 0 < k)
    (P Pstd : Sylow 2 (SuzukiMatrixGroup k))
    (hPstd_root_iff :
      ∀ x : SuzukiMatrixGroup k,
        x ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) ↔
          (x : GL (Fin 4) (BinaryGaloisField (2 * k + 1))) ∈
            Subgroup.closure
              {A | ∃ a b : BinaryGaloisField (2 * k + 1),
                A = SuzukiRootGL k a b})
    (tm : SuzukiMatrixGroup k) (htm : IsInvolution tm)
    (htm_not_mem : tm ∉ (P : Subgroup (SuzukiMatrixGroup k))) :
    ∃ c : SuzukiMatrixGroup k,
      c • P = Pstd ∧
        ((c * tm * c⁻¹ : SuzukiMatrixGroup k) :
          GL (Fin 4) (BinaryGaloisField (2 * k + 1))) = SuzukiWeylGL k := by
  classical
  let K := BinaryGaloisField (2 * k + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (k + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (k + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (k + 1) x
  have hK_card : Nat.card K = 2 ^ (2 * k + 1) := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * k + 1) (by omega)
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 := by
    intro x
    letI : Fintype K := Fintype.ofFinite K
    calc
      pi (pi x) = (pi x) ^ (2 ^ (k + 1)) := hpi (pi x)
      _ = (x ^ (2 ^ (k + 1))) ^ (2 ^ (k + 1)) := by rw [hpi]
      _ = x ^ (2 ^ (k + 1 + (k + 1))) := by
        rw [← pow_mul, ← pow_add]
      _ = x ^ (2 ^ ((2 * k + 1) + 1)) := by
        congr 2
        omega
      _ = (x ^ (2 ^ (2 * k + 1))) ^ 2 := by
        rw [pow_succ, pow_mul]
      _ = x ^ 2 := by
        have hx_card : x ^ Nat.card K = x := by
          rw [← Fintype.card_eq_nat_card]
          exact FiniteField.pow_card x
        rw [← hK_card, hx_card]
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Froot : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL k a b}
  let Htorus : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL k u}
  let act : SuzukiMatrixGroup k → ℙ K (Fin 4 → K) → ℙ K (Fin 4 → K) :=
    fun g z =>
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z
  have hact_mul (x y : SuzukiMatrixGroup k) (z : ℙ K (Fin 4 → K)) :
      act (x * y) z = act x (act y z) := by
    change
      (Matrix.GeneralLinearGroup.toLin
        ((x : GL (Fin 4) K) * (y : GL (Fin 4) K))).toLinearEquiv • z =
          (Matrix.GeneralLinearGroup.toLin
            (x : GL (Fin 4) K)).toLinearEquiv •
              (Matrix.GeneralLinearGroup.toLin
                (y : GL (Fin 4) K)).toLinearEquiv • z
    rw [map_mul]
    change
      ((Matrix.GeneralLinearGroup.toLin
          (x : GL (Fin 4) K)).toLinearEquiv *
        (Matrix.GeneralLinearGroup.toLin
          (y : GL (Fin 4) K)).toLinearEquiv) • z = _
    exact mul_smul _ _ z
  have hact_one (z : ℙ K (Fin 4 → K)) : act 1 z = z := by
    change (Matrix.GeneralLinearGroup.toLin
      (1 : GL (Fin 4) K)).toLinearEquiv • z = z
    rw [map_one]
    exact one_smul _ z
  have hact_inv (x : SuzukiMatrixGroup k) (z : ℙ K (Fin 4 → K)) :
      act x⁻¹ (act x z) = z := by
    calc
      act x⁻¹ (act x z) = act (x⁻¹ * x) z := (hact_mul x⁻¹ x z).symm
      _ = act 1 z := by simp
      _ = z := hact_one z
  have hnatural := External.huppert_blackburn_XI_3_3 k hk pi hpi
  rcases hnatural with
    ⟨hpreserves, _hfull, _hfaithful, htwo_transitive, _hthree_fixed,
      _hO_card, _hG_card, hstabilizer⟩
  have hFroot_normalized :
      Froot ⊔ Htorus ≤ Subgroup.normalizer Froot := by
    exact sup_le Subgroup.le_normalizer
      (External.suzukiTorusClosure_le_normalizer_rootClosure
        k pi hpi_sq hpi)
  have hnormalizes_Pstd :
      ∀ x : SuzukiMatrixGroup k,
        (x : GL (Fin 4) K) ∈ Froot ⊔ Htorus →
          x ∈ Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k)) := by
    intro x hx
    change ∀ y : SuzukiMatrixGroup k,
      y ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) ↔
        x * y * x⁻¹ ∈ (Pstd : Subgroup (SuzukiMatrixGroup k))
    intro y
    have hxnorm := hFroot_normalized hx
    have hconj_iff :=
      Subgroup.mem_normalizer_iff.mp hxnorm (y : GL (Fin 4) K)
    constructor
    · intro hy
      apply (hPstd_root_iff _).2
      have hyroot := (hPstd_root_iff y).1 hy
      rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
      exact hconj_iff.mp hyroot
    · intro hy
      apply (hPstd_root_iff y).2
      have hyroot := (hPstd_root_iff (x * y * x⁻¹)).1 hy
      apply hconj_iff.mpr
      rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv] at hyroot
      exact hyroot
  let c0 : SuzukiMatrixGroup k :=
    Classical.choose
      (MulAction.exists_smul_eq (SuzukiMatrixGroup k) P Pstd)
  have hc0 : c0 • P = Pstd :=
    Classical.choose_spec
      (MulAction.exists_smul_eq (SuzukiMatrixGroup k) P Pstd)
  let u : SuzukiMatrixGroup k := c0 * tm * c0⁻¹
  have hu_involution : IsInvolution u := by
    constructor
    · intro hu_one
      apply htm.ne_one
      calc
        tm = c0⁻¹ * u * c0 := by simp [u]; group
        _ = c0⁻¹ * 1 * c0 := by rw [hu_one]
        _ = 1 := by simp
    · dsimp [u]
      rw [pow_two]
      calc
        (c0 * tm * c0⁻¹) * (c0 * tm * c0⁻¹) =
            c0 * (tm * tm) * c0⁻¹ := by group
        _ = 1 := by
          rw [show tm * tm = 1 by simpa [pow_two] using htm.sq_eq_one]
          simp
  have hu_not_mem : u ∉ (Pstd : Subgroup (SuzukiMatrixGroup k)) := by
    intro hu_mem
    have hu_mem_smul :
        u ∈ ((c0 • P : Sylow 2 (SuzukiMatrixGroup k)) :
          Subgroup (SuzukiMatrixGroup k)) := by
      rw [hc0]
      exact hu_mem
    rw [Sylow.coe_subgroup_smul] at hu_mem_smul
    rcases Set.mem_smul_set.mp hu_mem_smul with ⟨x, hx, hux⟩
    apply htm_not_mem
    have htm_eq : tm = x := by
      have hux' : c0 * x * c0⁻¹ = u := by
        simpa [MulAut.conj_apply] using hux
      calc
        tm = c0⁻¹ * u * c0 := by simp [u]; group
        _ = c0⁻¹ * (c0 * x * c0⁻¹) * c0 := by rw [hux']
        _ = x := by group
    change tm ∈ (P : Set (SuzukiMatrixGroup k))
    rw [htm_eq]
    exact hx
  have hu_moves_infinity : act u pinf ≠ pinf := by
    intro hu_fix
    have hu_norm :
        u ∈ Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k)) := by
      apply hnormalizes_Pstd u
      apply (hstabilizer u).mp
      change act u pinf = pinf
      exact hu_fix
    have hU_pgroup : IsPGroup 2 (Subgroup.zpowers u) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers,
        orderOf_eq_prime hu_involution.sq_eq_one hu_involution.ne_one, pow_one]
    have hu_inf :
        u ∈ Subgroup.zpowers u ⊓
          Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k)) :=
      ⟨Subgroup.mem_zpowers u, hu_norm⟩
    have hinf := hU_pgroup.inf_normalizer_sylow Pstd
    rw [hinf] at hu_inf
    exact hu_not_mem hu_inf.2
  have hpinf_mem : pinf ∈ O := Or.inl rfl
  have hpzero_mem : p 0 0 ∈ O := Or.inr ⟨(0, 0), rfl⟩
  have huinf_mem : act u pinf ∈ O := by
    exact hpreserves u pinf hpinf_mem
  have hpinf_ne_zero : pinf ≠ p 0 0 := by
    intro h
    dsimp [pinf, p] at h
    rw [Projectivization.mk_eq_mk_iff] at h
    rcases h with ⟨c, hc⟩
    have hc0 := congrFun hc (0 : Fin 4)
    simp at hc0
  rcases htwo_transitive pinf (act u pinf) pinf (p 0 0)
      hpinf_mem huinf_mem hpinf_mem hpzero_mem hu_moves_infinity.symm
      hpinf_ne_zero with ⟨b, hb_inf, hb_uinf⟩
  have hb_normalizer :
      b ∈ Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k)) := by
    apply hnormalizes_Pstd b
    apply (hstabilizer b).mp
    change act b pinf = pinf
    exact hb_inf
  have hb_inv_inf : act b⁻¹ pinf = pinf := by
    calc
      act b⁻¹ pinf = act b⁻¹ (act b pinf) :=
        congrArg (act b⁻¹) hb_inf.symm
      _ = pinf := hact_inv b pinf
  let u1 : SuzukiMatrixGroup k := b * u * b⁻¹
  have hu1_involution : IsInvolution u1 := by
    constructor
    · intro hu1_one
      apply hu_involution.ne_one
      calc
        u = b⁻¹ * u1 * b := by simp [u1]; group
        _ = b⁻¹ * 1 * b := by rw [hu1_one]
        _ = 1 := by simp
    · dsimp [u1]
      rw [pow_two]
      calc
        (b * u * b⁻¹) * (b * u * b⁻¹) = b * (u * u) * b⁻¹ := by group
        _ = 1 := by
          rw [show u * u = 1 by simpa [pow_two] using hu_involution.sq_eq_one]
          simp
  have hu1_inf : act u1 pinf = p 0 0 := by
    calc
      act u1 pinf = act b (act u (act b⁻¹ pinf)) := by
        simp only [u1, hact_mul]
      _ = act b (act u pinf) := by rw [hb_inv_inf]
      _ = p 0 0 := hb_uinf
  have hu1_zero : act u1 (p 0 0) = pinf := by
    have hu1_twice := congrArg (act u1) hu1_inf
    calc
      act u1 (p 0 0) = act u1 (act u1 pinf) := hu1_twice.symm ▸ rfl
      _ = act (u1 * u1) pinf := (hact_mul u1 u1 pinf).symm
      _ = pinf := by
        rw [show u1 * u1 = 1 by
          simpa [pow_two] using hu1_involution.sq_eq_one]
        exact hact_one pinf
  let T : SuzukiMatrixGroup k :=
    ⟨SuzukiWeylGL k, by
      exact Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩
  have hT_sq : T * T = 1 := by
    apply Subtype.ext
    exact External.suzukiWeylGL_mul_self k
  have hT_inf : act T pinf = p 0 0 := by
    change (Matrix.GeneralLinearGroup.toLin
      (SuzukiWeylGL k)).toLinearEquiv • pinf = p 0 0
    dsimp only [pinf, p]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [SuzukiWeylGL, SuzukiWeylMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have hT_zero : act T (p 0 0) = pinf := by
    calc
      act T (p 0 0) = act T (act T pinf) := by rw [hT_inf]
      _ = act (T * T) pinf := (hact_mul T T pinf).symm
      _ = pinf := by rw [hT_sq]; exact hact_one pinf
  let d : SuzukiMatrixGroup k := u1 * T
  have hd_inf : act d pinf = pinf := by
    change act (u1 * T) pinf = pinf
    rw [hact_mul, hT_inf, hu1_zero]
  have hd_zero : act d (p 0 0) = p 0 0 := by
    change act (u1 * T) (p 0 0) = p 0 0
    rw [hact_mul, hT_zero, hu1_inf]
  have hd_B : (d : GL (Fin 4) K) ∈ Froot ⊔ Htorus := by
    apply (hstabilizer d).mp
    change act d pinf = pinf
    exact hd_inf
  have hroot_zero : ∀ a b : K,
      (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL k a b)).toLinearEquiv • p 0 0 =
          p a (b + pi a * a) := by
    intro a b
    dsimp only [p]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    have hpow (z : K) : z ^ (2 ^ (k + 1)) = pi z := (hpi z).symm
    have hpow_one (z : K) : z ^ (1 + 2 ^ (k + 1)) = z * pi z := by
      rw [pow_add, hpow, pow_one]
    have hpow_two (z : K) : z ^ (2 + 2 ^ (k + 1)) = z ^ 2 * pi z := by
      rw [pow_add, hpow]
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
    funext i
    fin_cases i <;>
      simp [SuzukiRootGL, SuzukiRootMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        hpow, hpow_one, hpow_two, map_add, map_mul, hpi_sq,
        CharTwo.add_self_eq_zero]
    · linear_combination (a ^ 2 * pi a) * htwo
    · ring
  have htorus_zero : ∀ z : Kˣ,
      (Matrix.GeneralLinearGroup.toLin
        (SuzukiTorusGL k z)).toLinearEquiv • p 0 0 = p 0 0 := by
    intro z
    dsimp only [p]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨((z : K) ^ (1 + 2 ^ k))⁻¹, ?_⟩
    funext i
    fin_cases i <;>
      simp [SuzukiTorusGL, SuzukiTorusMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have hp_injective : Function.Injective (fun z : K × K => p z.1 z.2) := by
    intro z w hzw
    dsimp only [p] at hzw
    rw [Projectivization.mk_eq_mk_iff] at hzw
    rcases hzw with ⟨c, hc⟩
    have hc_one : (c : K) = 1 := by
      have hc3 := congrFun hc (3 : Fin 4)
      simpa [Units.smul_def] using hc3
    apply Prod.ext
    · have hc2 := congrFun hc (2 : Fin 4)
      simpa [Units.smul_def, hc_one] using hc2.symm
    · have hc1 := congrFun hc (1 : Fin 4)
      simpa [Units.smul_def, hc_one] using hc1.symm
  have hd_torus : (d : GL (Fin 4) K) ∈ Htorus := by
    have hd_prod :
        (d : GL (Fin 4) K) ∈
          (Froot : Set (GL (Fin 4) K)) *
            (Htorus : Set (GL (Fin 4) K)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Froot Htorus
        (External.suzukiTorusClosure_le_normalizer_rootClosure
          k pi hpi_sq hpi)]
      exact hd_B
    rcases hd_prod with ⟨f, hf, h, hh, hfh⟩
    rcases (External.suzukiRootGL_mem_closure_iff
      k pi hpi_sq hpi f).mp hf with ⟨a, b0, rfl⟩
    rcases (External.suzukiTorusGL_mem_closure_iff k h).mp hh with ⟨z, rfl⟩
    have hraw_zero :
        (Matrix.GeneralLinearGroup.toLin
          (SuzukiRootGL k a b0 * SuzukiTorusGL k z)).toLinearEquiv •
            p 0 0 = p 0 0 := by
      calc
        (Matrix.GeneralLinearGroup.toLin
            (SuzukiRootGL k a b0 * SuzukiTorusGL k z)).toLinearEquiv •
              p 0 0 =
            (Matrix.GeneralLinearGroup.toLin
              (d : GL (Fin 4) K)).toLinearEquiv • p 0 0 :=
          congrArg
            (fun A : GL (Fin 4) K =>
              (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • p 0 0) hfh
        _ = p 0 0 := by simpa [act, K] using hd_zero
    have hpoint : p a (b0 + pi a * a) = p 0 0 := by
      calc
        p a (b0 + pi a * a) =
            (Matrix.GeneralLinearGroup.toLin
              (SuzukiRootGL k a b0)).toLinearEquiv • p 0 0 :=
          (hroot_zero a b0).symm
        _ = (Matrix.GeneralLinearGroup.toLin
              (SuzukiRootGL k a b0)).toLinearEquiv •
                ((Matrix.GeneralLinearGroup.toLin
                  (SuzukiTorusGL k z)).toLinearEquiv • p 0 0) := by
          rw [htorus_zero z]
        _ = (Matrix.GeneralLinearGroup.toLin
              (SuzukiRootGL k a b0 * SuzukiTorusGL k z)).toLinearEquiv •
                p 0 0 := by
          rw [map_mul]
          change
            (Matrix.GeneralLinearGroup.toLin
                (SuzukiRootGL k a b0)).toLinearEquiv •
                (Matrix.GeneralLinearGroup.toLin
                  (SuzukiTorusGL k z)).toLinearEquiv • p 0 0 =
              ((Matrix.GeneralLinearGroup.toLin
                  (SuzukiRootGL k a b0)).toLinearEquiv *
                (Matrix.GeneralLinearGroup.toLin
                  (SuzukiTorusGL k z)).toLinearEquiv) • p 0 0
          exact (mul_smul _ _ (p 0 0)).symm
        _ = p 0 0 := hraw_zero
    have hab : (a, b0 + pi a * a) = (0, 0) := by
      apply hp_injective
      exact hpoint
    have ha : a = 0 := congrArg Prod.fst hab
    have hb0 : b0 = 0 := by
      have := congrArg Prod.snd hab
      simpa [ha] using this
    have hd_eq : (d : GL (Fin 4) K) = SuzukiTorusGL k z := by
      calc
        (d : GL (Fin 4) K) =
            SuzukiRootGL k a b0 * SuzukiTorusGL k z := hfh.symm
        _ = SuzukiRootGL k 0 0 * SuzukiTorusGL k z := by rw [ha, hb0]
        _ = 1 * SuzukiTorusGL k z := by
          rw [External.suzukiRootGL_zero_zero]
        _ = SuzukiTorusGL k z := one_mul _
    rw [hd_eq]
    exact Subgroup.subset_closure ⟨z, rfl⟩
  have hHtorus_odd : Odd (Nat.card Htorus) := by
    rcases External.huppert_blackburn_XI_3_1 k hk pi hpi_sq with
      ⟨_hpi_unique, _hpi_formula, _hFroot_pgroup, _hFroot_exp,
        _hFroot_order_four, _hFroot_class, _hFroot_card, _hFroot_typeA,
        _hFroot_mul, _hcommutator_center, _hcommutator_mem,
        htorus_equiv, _htorus_conj, _hdisjoint, _hfixed_free⟩
    rcases htorus_equiv with ⟨eH, _heH⟩
    have hcard : Nat.card Htorus = 2 ^ (2 * k + 1) - 1 := by
      calc
        Nat.card Htorus = Nat.card Kˣ := Nat.card_congr eH.symm.toEquiv
        _ = Nat.card K - 1 := by
          simpa only [K] using
            (Nat.card_units
              (α := BinaryGaloisField (2 * k + 1)))
        _ = 2 ^ (2 * k + 1) - 1 := by rw [hK_card]
    rw [hcard]
    exact Nat.Even.sub_odd
      (pow_pos (by norm_num : (0 : ℕ) < 2) (2 * k + 1))
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hd_order_odd : Odd (orderOf d) := by
    let dH : Htorus := ⟨(d : GL (Fin 4) K), hd_torus⟩
    apply Odd.of_dvd_nat hHtorus_odd
    have hdiv := orderOf_dvd_natCard dH
    simpa [dH, Subgroup.orderOf_coe] using hdiv
  rcases hd_order_odd with ⟨m, hm⟩
  let a : SuzukiMatrixGroup k := d ^ (m + 1)
  have hd_order_pow : d ^ (2 * m + 1) = 1 := by
    simpa [hm] using pow_orderOf_eq_one d
  have ha_sq : a * a = d := by
    dsimp [a]
    rw [← pow_add]
    have hexp : (m + 1) + (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hexp, pow_succ, hd_order_pow, one_mul]
  have hT_involution : IsInvolution T := by
    constructor
    · intro hT_one
      have hval := congrArg Subtype.val hT_one
      have h03 := congrArg
        (fun A : GL (Fin 4) (BinaryGaloisField (2 * k + 1)) =>
          A.val (0 : Fin 4) (3 : Fin 4)) hval
      simp [T, SuzukiWeylGL, SuzukiWeylMatrix] at h03
    · simpa [pow_two] using hT_sq
  have hT_semiconj_d : SemiconjBy T d d⁻¹ := by
    change T * (u1 * T) = (u1 * T)⁻¹ * T
    rw [mul_inv_rev, hT_involution.inv_eq_self,
      hu1_involution.inv_eq_self]
    group
  have hT_a : T * a = a⁻¹ * T := by
    have hpow := hT_semiconj_d.pow_right (m + 1)
    simpa [a, inv_pow] using hpow.eq
  have ha_conj_u1 : a⁻¹ * u1 * a = T := by
    rw [show u1 = d * T by
      calc
        u1 = u1 * (T * T) := by rw [hT_sq]; simp
        _ = (u1 * T) * T := by group
        _ = d * T := rfl]
    calc
      a⁻¹ * (d * T) * a = a⁻¹ * d * (T * a) := by group
      _ = a⁻¹ * d * (a⁻¹ * T) := by rw [hT_a]
      _ = T := by
        have ha_sq' : a ^ 2 = d := by simpa [pow_two] using ha_sq
        rw [← ha_sq']
        group
  have hd_normalizer :
      d ∈ Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k)) := by
    apply hnormalizes_Pstd d
    exact (show Htorus ≤ Froot ⊔ Htorus from le_sup_right) hd_torus
  have ha_normalizer :
      a ∈ Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k)) := by
    exact (Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k))).pow_mem
      hd_normalizer (m + 1)
  let c : SuzukiMatrixGroup k := a⁻¹ * b * c0
  refine ⟨c, ?_, ?_⟩
  · calc
      c • P = a⁻¹ • (b • (c0 • P)) := by simp [c, mul_smul]
      _ = a⁻¹ • (b • Pstd) := by rw [hc0]
      _ = a⁻¹ • Pstd := by
        rw [Sylow.smul_eq_iff_mem_normalizer.mpr hb_normalizer]
      _ = Pstd := by
        rw [Sylow.smul_eq_iff_mem_normalizer.mpr
          ((Subgroup.normalizer (Pstd : Set (SuzukiMatrixGroup k))).inv_mem
            ha_normalizer)]
  · have hcT : c * tm * c⁻¹ = T := by
      calc
        c * tm * c⁻¹ = a⁻¹ * u1 * a := by
          simp [c, u1, u, mul_inv_rev]
          group
        _ = T := ha_conj_u1
    exact congrArg Subtype.val hcT

set_option maxHeartbeats 10000000 in
private theorem psu_exists_simultaneous_standardizer
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E) (q : ℕ)
    (hq_power : ∃ n : ℕ, q = 2 ^ n) (hq_gt : 2 < q)
    (hEcard : Nat.card E = q ^ 2)
    (hfixedCard : Nat.card {z : E // J.conj z = z} = q)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (tm : ProjectiveSpecialUnitaryMatrixGroup J) (htm : IsInvolution tm)
    (htm_not_mem : tm ∉
      (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) :
    ∃ Pstd : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ j T : ProjectiveSpecialUnitaryMatrixGroup J,
        j ∈ (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
          IsInvolution j ∧ T * j * T = j * T * j ∧
            T = External.hermitianWeylPSU J hJstandard ∧
              (∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
                x ∈ (Pstd :
                    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
                  ∃ z : External.hermitianUnipotentCoord J,
                    x = External.hermitianUnipotentPSU J hJstandard z) ∧
                ∃ c : ProjectiveSpecialUnitaryMatrixGroup J,
                  c • P = Pstd ∧ c * tm * c⁻¹ = T := by
  classical
  let Pproj := ℙ E (Fin 3 → E)
  let A : Set Pproj :=
    {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
      x = Projectivization.mk E v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : Pproj // x ∈ A}
  have hq_even : Even q := by
    rcases hq_power with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hn_not_pos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn_not_pos
      subst n
      norm_num at hn
      omega
    rw [hn]
    exact Nat.even_pow.mpr ⟨even_two, ne_of_gt hnpos⟩
  have hE_even : Even (Nat.card E) := by
    rw [hEcard]
    exact hq_even.pow_of_ne_zero (by norm_num)
  letI : Fintype E := Fintype.ofFinite E
  have hcharE : ringChar E = 2 :=
    FiniteField.even_card_iff_char_two.mpr (by
      simpa [← Nat.card_eq_fintype_card] using Nat.even_iff.mp hE_even)
  have htwoE : (2 : E) = 0 := by
    simpa [hcharE] using (CharP.cast_eq_zero E (ringChar E))
  have hone_add_one : (1 : E) + 1 = 0 := by
    simpa only [one_add_one_eq_two] using htwoE
  have hone_eq_neg_one : (1 : E) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact hone_add_one
  rcases External.huppert_II_10_12 J q hEcard hfixedCard hJstandard with
    ⟨_hOmega_card, rho, pinf, _hrho_injective, hnatural,
      _hU_card, hroot_exists, _htwo_transitive, hG_card,
      _hthree_fixed⟩
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective rho _hrho_injective
  have hrho_mul_apply
      (g h : ProjectiveSpecialUnitaryMatrixGroup J) (x : Omega) :
      rho g (rho h x) = rho (g * h) x := by
    rw [map_mul]
    rfl
  rcases hroot_exists with
    ⟨R, H, hR_le_U, hH_le_U, hU_normalizes_R,
      _hR_disjoint_H, hR_join_H, _hH_cyclic, hR_card,
      _hcommutator_center, _hcommutator_card, hH_card,
      hR_regular, hcoord_exists, hH_coord, _hH_coord_surjective⟩
  rcases hcoord_exists with ⟨coordR, hcoord_matrix⟩
  let z0 : External.hermitianUnipotentCoord J :=
    ⟨(0, 1), by
      change 1 + J.conj 1 + 0 * J.conj 0 = 0
      simp only [map_one, map_zero, zero_mul, add_zero]
      exact hone_add_one⟩
  let j : ProjectiveSpecialUnitaryMatrixGroup J :=
    External.hermitianUnipotentPSU J hJstandard z0
  let T : ProjectiveSpecialUnitaryMatrixGroup J :=
    External.hermitianWeylPSU J hJstandard
  have hjGL_sq :
      External.hermitianUnipotentGL J z0 *
          External.hermitianUnipotentGL J z0 = 1 := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [z0, External.hermitianUnipotentGL,
        External.hermitianUnipotentMatrix, Matrix.mul_apply,
        Fin.sum_univ_three]
    exact hone_add_one
  have hTGL_sq :
      (External.hermitianWeylGL (K := E)) *
          External.hermitianWeylGL = 1 := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [External.hermitianWeylGL, External.hermitianWeylMatrix,
        Matrix.mul_apply, Fin.sum_univ_three]
  have hj_sq : j * j = 1 := by
    apply Subtype.ext
    change
      Matrix.ProjGenLinGroup.mk (External.hermitianUnipotentGL J z0) *
          Matrix.ProjGenLinGroup.mk (External.hermitianUnipotentGL J z0) = 1
    rw [← map_mul, hjGL_sq, map_one]
  have hT_sq : T * T = 1 := by
    apply Subtype.ext
    change
      Matrix.ProjGenLinGroup.mk (External.hermitianWeylGL (K := E)) *
          Matrix.ProjGenLinGroup.mk External.hermitianWeylGL = 1
    rw [← map_mul, hTGL_sq, map_one]
  have hbraidGL :
      External.hermitianWeylGL (K := E) *
            External.hermitianUnipotentGL J z0 *
          External.hermitianWeylGL =
        External.hermitianUnipotentGL J z0 *
            External.hermitianWeylGL *
          External.hermitianUnipotentGL J z0 := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [z0, External.hermitianUnipotentGL,
        External.hermitianUnipotentMatrix, External.hermitianWeylGL,
        External.hermitianWeylMatrix, Matrix.mul_apply,
        Fin.sum_univ_three]
    all_goals first
      | exact hone_add_one
      | exact hone_add_one.symm
      | exact hone_eq_neg_one
  have hbraid : T * j * T = j * T * j := by
    apply Subtype.ext
    change
      Matrix.ProjGenLinGroup.mk (External.hermitianWeylGL (K := E)) *
            Matrix.ProjGenLinGroup.mk (External.hermitianUnipotentGL J z0) *
          Matrix.ProjGenLinGroup.mk External.hermitianWeylGL =
        Matrix.ProjGenLinGroup.mk (External.hermitianUnipotentGL J z0) *
            Matrix.ProjGenLinGroup.mk External.hermitianWeylGL *
          Matrix.ProjGenLinGroup.mk (External.hermitianUnipotentGL J z0)
    simpa only [map_mul] using congrArg Matrix.ProjGenLinGroup.mk hbraidGL
  let pinf0 : Omega :=
    ⟨Projectivization.mk E ![1, 0, 0] (by simp), by
      refine ⟨![1, 0, 0], by simp, rfl, ?_⟩
      rw [hJstandard]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]⟩
  let pzero : Omega :=
    ⟨Projectivization.mk E ![0, 0, 1] (by simp), by
      refine ⟨![0, 0, 1], by simp, rfl, ?_⟩
      rw [hJstandard]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]⟩
  have hpinf_ne_zero : pinf0 ≠ pzero := by
    intro h
    have hval := congrArg Subtype.val h
    dsimp [pinf0, pzero] at hval
    rw [Projectivization.mk_eq_mk_iff] at hval
    rcases hval with ⟨c, hc⟩
    have hc0 := congrFun hc (0 : Fin 3)
    simp at hc0
  have hunipotentSU_coe (z : External.hermitianUnipotentCoord J) :
      ((External.hermitianUnipotentSU J hJstandard z : J.specialSubgroup) :
        GL (Fin 3) E) = External.hermitianUnipotentGL J z := rfl
  have hweylSU_coe :
      ((External.hermitianWeylSU J hJstandard : J.specialSubgroup) :
        GL (Fin 3) E) = External.hermitianWeylGL := rfl
  have htorusSU_coe (k : Eˣ) :
      ((External.hermitianTorusSU J hJstandard k : J.specialSubgroup) :
        GL (Fin 3) E) = External.hermitianTorusGL J k := rfl
  have hcoord_eq_root (z : External.hermitianUnipotentCoord J) :
      ((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) =
        External.hermitianUnipotentPSU J hJstandard z := by
    rcases hcoord_matrix z with ⟨M, hM, hMproj⟩
    have hMroot : M = External.hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i l
      change (M : Matrix (Fin 3) (Fin 3) E) i l =
        (External.hermitianUnipotentGL J z :
          Matrix (Fin 3) (Fin 3) E) i l
      rw [hM, External.hermitianUnipotentGL_val,
        External.hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    calc
      (((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) :
          Matrix.ProjGenLinGroup (Fin 3) E) =
          Matrix.ProjGenLinGroup.mk M := hMproj
      _ = Matrix.ProjGenLinGroup.mk
          (External.hermitianUnipotentGL J z) := by rw [hMroot]
      _ = ((External.hermitianUnipotentPSU J hJstandard z :
          ProjectiveSpecialUnitaryMatrixGroup J) :
            Matrix.ProjGenLinGroup (Fin 3) E) := by
        exact (External.hermitianUnipotentPSU_val J hJstandard z).symm
  have hroot_fix_inf (z : External.hermitianUnipotentCoord J) :
      rho (External.hermitianUnipotentPSU J hJstandard z) pinf0 = pinf0 := by
    apply Subtype.ext
    rw [hnatural (External.hermitianUnipotentPSU J hJstandard z) pinf0
      (External.hermitianUnipotentSU J hJstandard z) (by rfl)]
    dsimp only [pinf0]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [hunipotentSU_coe, External.hermitianUnipotentGL,
        External.hermitianUnipotentMatrix, Matrix.mulVec]
  have hR_fix_inf (r : R) : rho (r : ProjectiveSpecialUnitaryMatrixGroup J)
      pinf0 = pinf0 := by
    obtain ⟨z, rfl⟩ := coordR.surjective r
    rw [hcoord_eq_root]
    exact hroot_fix_inf z
  have hpinf_eq : pinf = pinf0 := by
    by_contra hne
    have hne' : pinf0 ≠ pinf := Ne.symm hne
    letI : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hR_card]
      nlinarith [hq_gt])
    obtain ⟨r, hr⟩ := exists_ne (1 : R)
    rcases hR_regular pinf0 pinf0 hne' hne' with ⟨r0, hr0, huniq⟩
    have hr_eq : r = r0 := huniq r (hR_fix_inf r)
    have h1_eq : (1 : R) = r0 := huniq 1 (by
      change rho (1 : ProjectiveSpecialUnitaryMatrixGroup J) pinf0 = pinf0
      rw [map_one]
      rfl)
    exact hr (hr_eq.trans h1_eq.symm)
  subst pinf
  have hT_inf : rho T pinf0 = pzero := by
    apply Subtype.ext
    rw [hnatural T pinf0 (External.hermitianWeylSU J hJstandard) (by rfl)]
    dsimp only [T, pinf0, pzero]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [hweylSU_coe, External.hermitianWeylGL,
        External.hermitianWeylMatrix, Matrix.mulVec]
  have hT_zero : rho T pzero = pinf0 := by
    calc
      rho T pzero = rho T (rho T pinf0) := by rw [hT_inf]
      _ = rho (T * T) pinf0 := hrho_mul_apply T T pinf0
      _ = pinf0 := by rw [hT_sq, map_one]; rfl
  have hH_fix_zero : ∀ h : H,
      rho (h : ProjectiveSpecialUnitaryMatrixGroup J) pzero = pzero := by
    intro h
    rcases hH_coord h with ⟨k, M, hM, hproj⟩
    have hMtorus : M = External.hermitianTorusGL J k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i l
      change (M : Matrix (Fin 3) (Fin 3) E) i l =
        (External.hermitianTorusGL J k : Matrix (Fin 3) (Fin 3) E) i l
      rw [hM, External.hermitianTorusGL_val]
      rfl
    have hh : (h : ProjectiveSpecialUnitaryMatrixGroup J) =
        External.hermitianTorusPSU J hJstandard k := by
      apply Subtype.ext
      exact hproj.trans (by
        rw [hMtorus, External.hermitianTorusPSU_val])
    rw [hh]
    apply Subtype.ext
    rw [hnatural (External.hermitianTorusPSU J hJstandard k) pzero
      (External.hermitianTorusSU J hJstandard k) (by rfl)]
    dsimp only [pzero]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(k : E), ?_⟩
    funext i
    fin_cases i <;>
      simp [htorusSU_coe, External.hermitianTorusGL,
        External.hermitianTorusMatrix, Matrix.mulVec]
  have hj_moves_zero : rho j pzero ≠ pzero := by
    intro hfix
    have hval := congrArg Subtype.val hfix
    rw [hnatural j pzero (External.hermitianUnipotentSU J hJstandard z0)
      (by rfl)] at hval
    dsimp only [j, pzero] at hval
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hval
    rcases hval with ⟨c, hc⟩
    have hc0 := congrFun hc (0 : Fin 3)
    simp [z0, hunipotentSU_coe, External.hermitianUnipotentGL,
      External.hermitianUnipotentMatrix, Matrix.mulVec] at hc0
  have hj_involution : IsInvolution j := by
    constructor
    · intro hj_one
      apply hj_moves_zero
      rw [hj_one, map_one]
      rfl
    · simpa [pow_two] using hj_sq
  have hT_involution : IsInvolution T := by
    constructor
    · intro hT_one
      apply hpinf_ne_zero
      calc
        pinf0 = rho 1 pinf0 := by rw [map_one]; rfl
        _ = rho T pinf0 := congrArg (fun x => rho x pinf0) hT_one.symm
        _ = pzero := hT_inf
    · simpa [pow_two] using hT_sq
  have hR_pgroup : IsPGroup 2 R := by
    rcases hq_power with ⟨n, hn⟩
    apply IsPGroup.of_card (n := n * 3)
    rw [hR_card, hn, pow_mul]
  obtain ⟨Pstd, hR_le_Pstd⟩ := hR_pgroup.exists_le_sylow
  have hq_sq_even : Even (q ^ 2) := hq_even.pow_of_ne_zero (by norm_num)
  have hq_cube_even : Even (q ^ 3) := hq_even.pow_of_ne_zero (by norm_num)
  have hq_sq_pos : 0 < q ^ 2 := pow_pos (by omega) 2
  have hq_sq_sub_one_odd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hq_sq_pos hq_sq_even odd_one
  have houter_odd : Odd ((q ^ 3 + 1) * (q ^ 2 - 1)) :=
    hq_cube_even.add_one.mul hq_sq_sub_one_odd
  have hq_factor : (q + 1) * (q - 1) = q ^ 2 - 1 := by
    have hq_le_sq : q ≤ q * q := by nlinarith
    rw [add_mul, one_mul, Nat.mul_sub_left_distrib]
    simp only [mul_one, pow_two]
    omega
  have hden_dvd_qsq_sub : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 :=
    dvd_trans (Nat.gcd_dvd_right 3 (q + 1)) ⟨q - 1, hq_factor.symm⟩
  have hden_dvd_numerator : Nat.gcd 3 (q + 1) ∣
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right hden_dvd_qsq_sub ((q ^ 3 + 1) * q ^ 3)
  have hgroup_dvd_numerator :
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣
        (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    rw [hG_card]
    exact Nat.div_dvd_of_dvd hden_dvd_numerator
  obtain ⟨mP, hPstd_power⟩ := IsPGroup.iff_card.mp Pstd.isPGroup'
  have hPstd_dvd_group : Nat.card Pstd ∣
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).card_subgroup_dvd_card
  have hPstd_dvd_numerator : Nat.card Pstd ∣
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_trans hPstd_dvd_group hgroup_dvd_numerator
  have hPstd_dvd_product : Nat.card Pstd ∣
      q ^ 3 * ((q ^ 3 + 1) * (q ^ 2 - 1)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hPstd_dvd_numerator
  have hPstd_coprime_outer : Nat.Coprime (Nat.card Pstd)
      ((q ^ 3 + 1) * (q ^ 2 - 1)) := by
    rw [hPstd_power]
    exact Nat.Coprime.pow_left mP houter_odd.coprime_two_left
  have hPstd_dvd_qcube : Nat.card Pstd ∣ q ^ 3 :=
    hPstd_coprime_outer.dvd_of_dvd_mul_right hPstd_dvd_product
  have hqcube_dvd_Pstd : q ^ 3 ∣ Nat.card Pstd := by
    rw [← hR_card]
    exact Subgroup.card_dvd_of_le hR_le_Pstd
  have hPstd_card : Nat.card Pstd = q ^ 3 :=
    Nat.dvd_antisymm hPstd_dvd_qcube hqcube_dvd_Pstd
  have hR_eq_Pstd :
      R = (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.eq_of_le_of_card_ge hR_le_Pstd (by rw [hPstd_card, hR_card])
  have hPstd_root_iff :
      ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        x ∈ (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
          ∃ z : External.hermitianUnipotentCoord J,
            x = External.hermitianUnipotentPSU J hJstandard z := by
    intro x
    constructor
    · intro hx
      rw [← hR_eq_Pstd] at hx
      let r : R := ⟨x, hx⟩
      obtain ⟨z, hz⟩ := coordR.surjective r
      refine ⟨z, ?_⟩
      have hz' := congrArg
        (fun y : R => (y : ProjectiveSpecialUnitaryMatrixGroup J)) hz
      exact hz'.symm.trans (hcoord_eq_root z)
    · rintro ⟨z, rfl⟩
      rw [← hR_eq_Pstd]
      have hz : ((coordR z : R) :
          ProjectiveSpecialUnitaryMatrixGroup J) ∈ R := (coordR z).property
      rwa [hcoord_eq_root z] at hz
  have hj_mem_Pstd : j ∈
      (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← hR_eq_Pstd]
    have hz : ((coordR z0 : R) :
        ProjectiveSpecialUnitaryMatrixGroup J) ∈ R := (coordR z0).property
    rw [hcoord_eq_root z0] at hz
    exact hz
  let c0 : ProjectiveSpecialUnitaryMatrixGroup J :=
    Classical.choose
      (MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P Pstd)
  have hc0 : c0 • P = Pstd :=
    Classical.choose_spec
      (MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P Pstd)
  let u : ProjectiveSpecialUnitaryMatrixGroup J := c0 * tm * c0⁻¹
  have hu_involution : IsInvolution u := by
    constructor
    · intro hu_one
      apply htm.ne_one
      calc
        tm = c0⁻¹ * u * c0 := by simp [u]; group
        _ = c0⁻¹ * 1 * c0 := by rw [hu_one]
        _ = 1 := by simp
    · dsimp [u]
      rw [pow_two]
      calc
        (c0 * tm * c0⁻¹) * (c0 * tm * c0⁻¹) =
            c0 * (tm * tm) * c0⁻¹ := by group
        _ = 1 := by
          rw [show tm * tm = 1 by simpa [pow_two] using htm.sq_eq_one]
          simp
  have hu_not_mem : u ∉
      (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro hu_mem
    have hu_mem_smul : u ∈
        ((c0 • P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [hc0]
      exact hu_mem
    rw [Sylow.coe_subgroup_smul] at hu_mem_smul
    rcases Set.mem_smul_set.mp hu_mem_smul with ⟨x, hx, hux⟩
    apply htm_not_mem
    have hux' : c0 * x * c0⁻¹ = u := by
      simpa [MulAut.conj_apply] using hux
    have htm_eq_x : tm = x := by
      calc
        tm = c0⁻¹ * u * c0 := by simp [u]; group
        _ = c0⁻¹ * (c0 * x * c0⁻¹) * c0 := by rw [hux']
        _ = x := by group
    change tm ∈ (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))
    rw [htm_eq_x]
    exact hx
  have hu_moves_inf : rho u pinf0 ≠ pinf0 := by
    intro hu_fix
    have huU : u ∈
        (MulAction.stabilizer (Equiv.Perm Omega) pinf0).comap rho := hu_fix
    have hu_norm_R := hU_normalizes_R huU
    rw [hR_eq_Pstd] at hu_norm_R
    have hU_pgroup : IsPGroup 2 (Subgroup.zpowers u) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers,
        orderOf_eq_prime hu_involution.sq_eq_one hu_involution.ne_one, pow_one]
    have hu_inf : u ∈ Subgroup.zpowers u ⊓
        Subgroup.normalizer
          (Pstd : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      ⟨Subgroup.mem_zpowers u, hu_norm_R⟩
    have hinf := hU_pgroup.inf_normalizer_sylow Pstd
    have hu_inf' : u ∈ Subgroup.zpowers u ⊓
        (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [← hinf]
      exact hu_inf
    exact hu_not_mem hu_inf'.2
  have huinf_ne : rho u pinf0 ≠ pinf0 := hu_moves_inf
  rcases hR_regular (rho u pinf0) pzero huinf_ne hpinf_ne_zero.symm with
    ⟨bR, hb_uinf, _hb_unique⟩
  let b : ProjectiveSpecialUnitaryMatrixGroup J := bR
  have hb_inf : rho b pinf0 = pinf0 := hR_le_U bR.property
  have hb_normalizer : b ∈ Subgroup.normalizer
      (Pstd : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    apply Subgroup.le_normalizer
    rw [← hR_eq_Pstd]
    exact bR.property
  have hb_inv_inf : rho b⁻¹ pinf0 = pinf0 := by
    calc
      rho b⁻¹ pinf0 = rho b⁻¹ (rho b pinf0) :=
        congrArg (rho b⁻¹) hb_inf.symm
      _ = pinf0 := by
        rw [map_inv]
        exact (rho b).symm_apply_apply pinf0
  let u1 : ProjectiveSpecialUnitaryMatrixGroup J := b * u * b⁻¹
  have hu1_involution : IsInvolution u1 := by
    constructor
    · intro hu1_one
      apply hu_involution.ne_one
      calc
        u = b⁻¹ * u1 * b := by simp [u1]; group
        _ = b⁻¹ * 1 * b := by rw [hu1_one]
        _ = 1 := by simp
    · dsimp [u1]
      rw [pow_two]
      calc
        (b * u * b⁻¹) * (b * u * b⁻¹) = b * (u * u) * b⁻¹ := by group
        _ = 1 := by
          rw [show u * u = 1 by simpa [pow_two] using hu_involution.sq_eq_one]
          simp
  have hu1_inf : rho u1 pinf0 = pzero := by
    change rho (b * u * b⁻¹) pinf0 = pzero
    rw [map_mul, map_mul]
    change rho b (rho u (rho b⁻¹ pinf0)) = pzero
    rw [hb_inv_inf]
    exact hb_uinf
  have hu1_zero : rho u1 pzero = pinf0 := by
    calc
      rho u1 pzero = rho u1 (rho u1 pinf0) := by rw [hu1_inf]
      _ = rho (u1 * u1) pinf0 := hrho_mul_apply u1 u1 pinf0
      _ = pinf0 := by
        rw [show u1 * u1 = 1 by
          simpa [pow_two] using hu1_involution.sq_eq_one, map_one]
        rfl
  let d : ProjectiveSpecialUnitaryMatrixGroup J := u1 * T
  have hd_inf : rho d pinf0 = pinf0 := by
    change rho (u1 * T) pinf0 = pinf0
    rw [map_mul]
    change rho u1 (rho T pinf0) = pinf0
    rw [hT_inf, hu1_zero]
  have hd_zero : rho d pzero = pzero := by
    change rho (u1 * T) pzero = pzero
    rw [map_mul]
    change rho u1 (rho T pzero) = pzero
    rw [hT_zero, hu1_inf]
  have hdU : d ∈
      (MulAction.stabilizer (Equiv.Perm Omega) pinf0).comap rho := hd_inf
  have hH_norm_R : H ≤ Subgroup.normalizer
      (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    hH_le_U.trans hU_normalizes_R
  have hd_prod : d ∈
      (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) *
        (H : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left R H hH_norm_R]
    rw [hR_join_H]
    exact hdU
  rcases hd_prod with ⟨r0, hr0, h0, hh0, hprod⟩
  change r0 * h0 = d at hprod
  let rR : R := ⟨r0, hr0⟩
  have hr0_fix : rho (rR : ProjectiveSpecialUnitaryMatrixGroup J) pzero =
      pzero := by
    have hfix := hd_zero
    rw [← hprod, map_mul] at hfix
    change rho r0 (rho h0 pzero) = pzero at hfix
    rw [hH_fix_zero ⟨h0, hh0⟩] at hfix
    exact hfix
  rcases hR_regular pzero pzero hpinf_ne_zero.symm hpinf_ne_zero.symm with
    ⟨runiq, hruniq, huniq⟩
  have hrR_eq : rR = runiq := huniq rR hr0_fix
  have h1_eq : (1 : R) = runiq := huniq 1 (by
    change rho (1 : ProjectiveSpecialUnitaryMatrixGroup J) pzero = pzero
    rw [map_one]
    rfl)
  have hr0_one : r0 = 1 := congrArg Subtype.val (hrR_eq.trans h1_eq.symm)
  have hdH : d ∈ H := by
    rw [← hprod, hr0_one, one_mul]
    exact hh0
  have hden_dvd_qsq_sub' : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq q 1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
  have hH_odd : Odd (Nat.card H) := by
    rw [hH_card]
    exact hq_sq_sub_one_odd.of_dvd_nat
      (Nat.div_dvd_of_dvd hden_dvd_qsq_sub')
  have hd_order_odd : Odd (orderOf d) := by
    let dH : H := ⟨d, hdH⟩
    apply Odd.of_dvd_nat hH_odd
    have hdiv := orderOf_dvd_natCard dH
    simpa [dH, Subgroup.orderOf_coe] using hdiv
  rcases hd_order_odd with ⟨m, hm⟩
  let a : ProjectiveSpecialUnitaryMatrixGroup J := d ^ (m + 1)
  have hd_order_pow : d ^ (2 * m + 1) = 1 := by
    simpa [hm] using pow_orderOf_eq_one d
  have ha_sq : a * a = d := by
    dsimp [a]
    rw [← pow_add]
    have hexp : (m + 1) + (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hexp, pow_succ, hd_order_pow, one_mul]
  have hT_semiconj_d : SemiconjBy T d d⁻¹ := by
    change T * (u1 * T) = (u1 * T)⁻¹ * T
    rw [mul_inv_rev, hT_involution.inv_eq_self,
      hu1_involution.inv_eq_self]
    group
  have hT_a : T * a = a⁻¹ * T := by
    have hpow := hT_semiconj_d.pow_right (m + 1)
    simpa [a, inv_pow] using hpow.eq
  have ha_conj_u1 : a⁻¹ * u1 * a = T := by
    rw [show u1 = d * T by
      calc
        u1 = u1 * (T * T) := by rw [hT_sq]; simp
        _ = (u1 * T) * T := by group
        _ = d * T := rfl]
    calc
      a⁻¹ * (d * T) * a = a⁻¹ * d * (T * a) := by group
      _ = a⁻¹ * d * (a⁻¹ * T) := by rw [hT_a]
      _ = T := by
        have ha_sq' : a ^ 2 = d := by simpa [pow_two] using ha_sq
        rw [← ha_sq']
        group
  have hd_normalizer : d ∈ Subgroup.normalizer
      (Pstd : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    have hd_norm_R := hU_normalizes_R (hH_le_U hdH)
    rw [hR_eq_Pstd] at hd_norm_R
    exact hd_norm_R
  have ha_normalizer : a ∈ Subgroup.normalizer
      (Pstd : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (Subgroup.normalizer
      (Pstd : Set (ProjectiveSpecialUnitaryMatrixGroup J))).pow_mem
        hd_normalizer (m + 1)
  let c : ProjectiveSpecialUnitaryMatrixGroup J := a⁻¹ * b * c0
  refine ⟨Pstd, j, T, hj_mem_Pstd, hj_involution, hbraid, rfl,
    hPstd_root_iff, c, ?_, ?_⟩
  · calc
      c • P = a⁻¹ • (b • (c0 • P)) := by simp [c, mul_smul]
      _ = a⁻¹ • (b • Pstd) := by rw [hc0]
      _ = a⁻¹ • Pstd := by
        rw [Sylow.smul_eq_iff_mem_normalizer.mpr hb_normalizer]
      _ = Pstd := by
        rw [Sylow.smul_eq_iff_mem_normalizer.mpr
          ((Subgroup.normalizer
            (Pstd : Set (ProjectiveSpecialUnitaryMatrixGroup J))).inv_mem
              ha_normalizer)]
  · calc
      c * tm * c⁻¹ = a⁻¹ * u1 * a := by
        simp [c, u1, u, mul_inv_rev]
        group
      _ = T := ha_conj_u1

private theorem hermitianTorusPSU_mem_normalizer_of_root_iff
    {K : Type*} [Field K]
    (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hPstd_root_iff :
      ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        x ∈ Pstd ↔ ∃ z : External.hermitianUnipotentCoord J,
          x = External.hermitianUnipotentPSU J hJstandard z)
    (k : Kˣ) :
    External.hermitianTorusPSU J hJstandard k ∈
      Subgroup.normalizer (Pstd : Set _) := by
  let psuGroup : Group (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Subgroup.toGroup
      (J.specialSubgroup.map Matrix.ProjGenLinGroup.mk)
  letI : Group (ProjectiveSpecialUnitaryMatrixGroup J) := psuGroup
  letI : DivisionMonoid (ProjectiveSpecialUnitaryMatrixGroup J) :=
    psuGroup.toDivisionMonoid
  let torus := External.hermitianTorusPSU J hJstandard
  let root := External.hermitianUnipotentPSU J hJstandard
  have hforward : ∀ (a : Kˣ) (x : ProjectiveSpecialUnitaryMatrixGroup J),
      x ∈ Pstd → torus a * x * (torus a)⁻¹ ∈ Pstd := by
    intro a x hx
    rcases (hPstd_root_iff x).mp hx with ⟨z, rfl⟩
    apply (hPstd_root_iff _).mpr
    refine ⟨External.hermitianTorusAction J a z, ?_⟩
    have hmul :=
      External.hermitianTorusPSU_mul_unipotent J hJstandard a z
    dsimp [torus, root] at hmul ⊢
    rw [hmul]
    simp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward k x
  · intro hx
    have hback := hforward k⁻¹
      (External.hermitianTorusPSU J hJstandard k * x *
        (External.hermitianTorusPSU J hJstandard k)⁻¹) hx
    simpa [torus, map_inv, mul_assoc] using hback

private theorem mem_aligned_sylow_iff
    {M A : Type*} [Group M] [Group A] [Finite M] [Finite A]
    (eM : M ≃* A) (PM : Sylow 2 M) (Pstd : Sylow 2 A) (c : A)
    (hcP : c • PM.mapSurjective (f := eM.toMonoidHom) eM.surjective = Pstd)
    (m : M) :
    m ∈ (PM : Subgroup M) ↔
      (eM.trans (MulAut.conj c : A ≃* A)) m ∈
        (Pstd : Subgroup A) := by
  let Pmodel : Sylow 2 A :=
    PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
  let eA : M ≃* A := eM.trans (MulAut.conj c : A ≃* A)
  constructor
  · intro hm
    have hem : eM m ∈ (Pmodel : Subgroup A) := by
      change eM m ∈ (PM : Subgroup M).map eM.toMonoidHom
      exact ⟨m, hm, rfl⟩
    have heA : eA m ∈ ((c • Pmodel : Sylow 2 A) : Subgroup A) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨eM m, hem, rfl⟩
    rw [hcP] at heA
    exact heA
  · intro hm
    have heA : eA m ∈ ((c • Pmodel : Sylow 2 A) : Subgroup A) := by
      rw [hcP]
      exact hm
    rw [Sylow.coe_subgroup_smul] at heA
    rcases Set.mem_smul_set.mp heA with ⟨y, hy, hyeq⟩
    have hyem : y = eM m := by
      apply (MulAut.conj c).injective
      simpa [eA] using hyeq
    rw [hyem] at hy
    change eM m ∈ (PM : Subgroup M).map eM.toMonoidHom at hy
    rcases hy with ⟨z, hz, hzeq⟩
    exact eM.injective hzeq |>.symm ▸ hz

private theorem subtype_mem_normalizer_of_mem_subtype_sylow_normalizer
    {B : Type*} [Group B] [Finite B]
    (M Qbar : Subgroup B) (Pbar : Sylow 2 B)
    (hQbar : Qbar = (Pbar : Subgroup B))
    (hPbar_le_M : (Pbar : Subgroup B) ≤ M)
    (z : M)
    (hz : z ∈ Subgroup.normalizer
      ((Pbar.subtype hPbar_le_M : Sylow 2 M) : Set M)) :
    (z : B) ∈ Subgroup.normalizer (Qbar : Set B) := by
  let PM : Sylow 2 M := Pbar.subtype hPbar_le_M
  change z ∈ Subgroup.normalizer ((PM : Subgroup M) : Set M) at hz
  rw [Subgroup.mem_normalizer_iff] at hz
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxPbar : x ∈ (Pbar : Subgroup B) := by
      rw [← hQbar]
      exact hx
    let xM : M := ⟨x, hPbar_le_M hxPbar⟩
    have hxPM : xM ∈ (PM : Subgroup M) := hxPbar
    have hconjPM := (hz xM).mp hxPM
    rw [hQbar]
    exact hconjPM
  · intro hx
    have hxPbar : z * x * z⁻¹ ∈ (Pbar : Subgroup B) := by
      rw [← hQbar]
      exact hx
    have hxM : x ∈ M := by
      have hconjM : z * x * z⁻¹ ∈ M := hPbar_le_M hxPbar
      have hbackM := M.mul_mem
        (M.mul_mem (M.inv_mem z.property) hconjM) z.property
      simpa [mul_assoc] using hbackM
    let xM : M := ⟨x, hxM⟩
    have hxPM : z * xM * z⁻¹ ∈ (PM : Subgroup M) := hxPbar
    have hback := (hz xM).mpr hxPM
    rw [hQbar]
    exact hback

private theorem commute_of_central_commutator_mem_odd_subgroup
    {G : Type*} [Group G] [Finite G]
    (D F : Subgroup G) (t z : G)
    (hDodd : Odd (Nat.card D))
    (ht2 : t ^ 2 = 1) (htF : t ∈ F)
    (hkD : t * z * t⁻¹ * z⁻¹ ∈ D)
    (hkcenter : t * z * t⁻¹ * z⁻¹ ∈
      (Subgroup.center F).map F.subtype) :
    z * t = t * z := by
  let k : G := t * z * t⁻¹ * z⁻¹
  have htt : t * t = 1 := by simpa [pow_two] using ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rcases hkcenter with ⟨kF, hkFcenter, hkval⟩
  have hkval' : (kF : G) = k := by simpa [k] using hkval
  have htk : t * k = k * t := by
    let tF : F := ⟨t, htF⟩
    have hcommF := (Subgroup.mem_center_iff.mp hkFcenter) tF
    have hcommG := congrArg Subtype.val hcommF
    have hcommG' : t * (kF : G) = (kF : G) * t := by
      simpa [tF] using hcommG
    calc
      t * k = t * (kF : G) := by rw [hkval']
      _ = (kF : G) * t := hcommG'
      _ = k * t := by rw [hkval']
  have htz : t * z * t = k * z := by
    dsimp [k]
    rw [htinv]
    group
  have hksq_mul : k ^ 2 * z = z := by
    calc
      k ^ 2 * z = k * (k * z) := by simp [pow_two, mul_assoc]
      _ = k * (t * z * t) := by rw [← htz]
      _ = (k * t) * z * t := by group
      _ = (t * k) * z * t := by rw [htk]
      _ = t * (k * z) * t := by group
      _ = t * (t * z * t) * t := by rw [← htz]
      _ = (t * t) * z * (t * t) := by group
      _ = z := by rw [htt]; simp
  have hk2 : k ^ 2 = 1 := by
    have h := congrArg (fun x : G => x * z⁻¹) hksq_mul
    simpa [mul_assoc] using h
  let kD : D := ⟨k, by simpa [k] using hkD⟩
  have hkD2 : kD ^ 2 = 1 := by
    apply Subtype.ext
    simpa [kD] using hk2
  have horder_two : orderOf kD ∣ 2 := orderOf_dvd_of_pow_eq_one hkD2
  have horder_card : orderOf kD ∣ Nat.card D := orderOf_dvd_natCard kD
  have horder_one : orderOf kD = 1 :=
    Nat.eq_one_of_dvd_coprimes hDodd.coprime_two_right
      horder_card horder_two
  have hk_one : k = 1 := by
    have hkD_one : kD = 1 := orderOf_eq_one_iff.mp horder_one
    simpa [kD] using congrArg Subtype.val hkD_one
  have htz' : t * z * t = z := by
    rw [htz, hk_one, one_mul]
  calc
    z * t = (t * z * t) * t := by rw [htz']
    _ = t * z := by rw [mul_assoc, htt, mul_one]

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Proposition 1(c)
-/

set_option backward.isDefEq.respectTransparency false in
public theorem proposition_1_c
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              ∃ (M : Subgroup L) (_ : M.Normal) (q : ℕ),
  Odd (Nat.card (L ⧸ M)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
    ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : M ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : ΩL ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : M, ∀ ω : ΩL,
      eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : M ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : ΩL ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : M ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : ΩL ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω))))
    (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ V)
    (h2rank : TwoRankAtLeastTwo (Subgroup.centralizer (X : Set G))) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let ΩX : Type v := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
    letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
    let F : Subgroup G :=
      let C : Subgroup G := Subgroup.centralizer (X : Set G)
      (twoPrimeResidual C).map C.subtype
    let NL : Subgroup G := (pointStabilizerCore L ΩX).map L.subtype
    let CX : Subgroup G := Subgroup.centralizer (X : Set G) ⊓ Q
    (Subgroup.centralizer (X : Set G) ⊓ Q1 = ⊥) ∧
      (NL ⊓ F = (Subgroup.center F).map F.subtype) ∧
        ∃ (ℓ : ℕ),
          (∃ n : ℕ, ℓ = 2 ^ n) ∧ 2 < ℓ ∧
            ℓ = Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ Q0) ∧
              ((∃ k : ℕ, k ≠ 0 ∧ ℓ = 2 ^ k ∧
          Nonempty ((F ⧸ Subgroup.center F) ≃* PSL2BinaryMatrixGroup k) ∧
          -- HB XI.Example 10.7(a) supplies the structure equation used here.
          orderOf (s * t) = 3 ∧ IsElementaryAbelian 2 CX ∧ Nat.card CX = ℓ) ∨
        -- HB XI.3.1 gives the Suzuki Sylow-2 structure; XI.3.3 gives its order.
        (∃ k : ℕ, k ≠ 0 ∧ ℓ = 2 ^ (2 * k + 1) ∧
          Nonempty ((F ⧸ Subgroup.center F) ≃* SuzukiMatrixGroup k) ∧
          -- HB XI.Example 10.7(b) supplies the structure equation used here.
          orderOf (s * t) = 5 ∧ IsSuzukiTwoTypeA CX ∧ Nat.card CX = ℓ ^ 2) ∨
        (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
          J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
          Nat.card E = ℓ ^ 2 ∧
          Nat.card {z : E // J.conj z = z} = ℓ ∧
          Nonempty ((F ⧸ Subgroup.center F) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∧
          -- Huppert II.10.12 gives the PSU point-stabilizer structure and order.
          orderOf (s * t) = 3 ∧ IsSuzukiTwoGroup CX ∧ Nat.card CX = ℓ ^ 3 ∧
            psuCorollaryTwoLiftedSeed F CX (L ⊓ Q0) V t)) := by
  classical
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let ΩX : Type v := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
  let HX : Subgroup L := H.comap L.subtype
  let DX : Subgroup L := D.comap L.subtype
  let QX : Subgroup L := Q.comap L.subtype
  let tX : L :=
    ⟨t, t_mem_centralizer_of_le_peterfalviV D V X t hX_le_V hsec.section2.V_eq⟩
  let N : Subgroup L := pointStabilizerCore L ΩX
  let F : Subgroup G := (twoPrimeResidual L).map L.subtype
  let NL : Subgroup G := N.map L.subtype
  let CX : Subgroup G := L ⊓ Q
  rcases proposition_1_a H D Q K V W Q0 S Q1 X t s hsec hX_ne hX_le_V with
    ⟨hA1X, hcore_mem, hNL_le⟩
  rcases proposition_4_b HX DX QX tX hA1X with ⟨pX, hpX, _hpX_unique⟩
  let sX : L := pX.1
  let rX : L := pX.2
  have hsX_eq_s : (sX : G) = s := by
    rcases proposition_4_b H D Q t hsec.section2.hA.A1 with
      ⟨p, _hp, hp_unique⟩
    have hsX_involution_G : IsInvolution (sX : G) := by
      constructor
      · intro hs_one
        exact hpX.2.1.ne_one (Subtype.ext (by simpa [sX] using hs_one))
      · simpa [sX] using congrArg Subtype.val hpX.2.1.sq_eq_one
    have hstructureX_G :
        t * (sX : G) * t = (rX : G)⁻¹ * t * (rX : G) := by
      simpa [tX, sX, rX] using congrArg Subtype.val hpX.2.2.2
    have hpairX : ((sX : G), (rX : G)) = p :=
      hp_unique _ ⟨hpX.1, hsX_involution_G, hpX.2.2.1, hstructureX_G⟩
    rcases hsec.s_conjugate with ⟨r, hrQ, hstructure⟩
    have hpair : (s, r) = p :=
      hp_unique _ ⟨hsec.s_mem_H, hsec.s_involution, hrQ, hstructure⟩
    exact congrArg Prod.fst (hpairX.trans hpair.symm)
  have hsX_mem : sX ∈ HX := hpX.1
  have hsX_involution : IsInvolution sX := hpX.2.1
  have hrX_mem : rX ∈ QX := hpX.2.2.1
  have hstructureX : tX * sX * tX = rX⁻¹ * tX * rX := hpX.2.2.2
  letI : N.Normal := proposition_4_c_pointStabilizerCore_normal
  have h4c :=
    proposition_4_c HX DX QX tX sX hA1X hsX_mem hsX_involution
      ⟨rX, hrX_mem, hstructureX⟩
  let quotientAction : MulAction (L ⧸ N) ΩX := h4c.2.2.1.choose
  letI : MulAction (L ⧸ N) ΩX := quotientAction
  have hquotient_data := h4c.2.2.1.choose_spec
  have hquotient_smul := hquotient_data.1
  have hA1bar := hquotient_data.2
  have hQbar_iso := h4c.2.2.2.1
  have horder_quotient := h4c.2.2.2.2
  let π : L →* L ⧸ N := QuotientGroup.mk' N
  have hπ_apply (x : L) : π x = (x : L ⧸ N) := by
    change QuotientGroup.mk' N x = QuotientGroup.mk x
    rfl
  have hπ_sq_eq_one (x : L) (hx : x ^ 2 = 1) :
      (x : L ⧸ N) ^ 2 = 1 := by
    rw [← hπ_apply x, ← map_pow, hx, map_one]
  let Hbar : Subgroup (L ⧸ N) := HX.map π
  let Dbar : Subgroup (L ⧸ N) := DX.map π
  let Qbar : Subgroup (L ⧸ N) := QX.map π
  let tbar : L ⧸ N := QuotientGroup.mk tX
  have hA2bar : FaithfulSMul (L ⧸ N) ΩX := by
    constructor
    intro a b hab
    revert hab
    refine QuotientGroup.induction_on a ?_
    intro g hab
    revert hab
    refine QuotientGroup.induction_on b ?_
    intro h hgh
    apply (QuotientGroup.eq_iff_div_mem (N := N)).2
    change g / h ∈ pointStabilizerCore L ΩX
    rw [pointStabilizerCore, Subgroup.mem_iInf]
    intro ω
    rw [MulAction.mem_stabilizer_iff]
    have hsame : ∀ z : ΩX, g • z = h • z := by
      intro z
      simpa only [hquotient_smul] using hgh z
    calc
      (g / h) • ω = g • (h⁻¹ • ω) := by
        simp [div_eq_mul_inv, smul_smul]
      _ = h • (h⁻¹ • ω) := hsame _
      _ = ω := by simp [smul_smul]
  have hA3bar : TwoRankAtLeastTwo (L ⧸ N) := by
    rcases h2rank with ⟨E, hE_card, hE_sq⟩
    have hNmap_le_D : N.map L.subtype ≤ D := by
      intro x hx
      rcases hx with ⟨n, hn, rfl⟩
      have hn_local := (hcore_mem n).1 hn
      have hnV : (n : G) ∈ V := (hNL_le hn_local).2
      rw [hsec.section2.V_eq] at hnV
      exact hnV.1
    have hN_card_map : Nat.card (N.map L.subtype) = Nat.card N :=
      Subgroup.card_map_of_injective (K := N) (f := L.subtype)
        L.subtype_injective
    have hN_dvd_D : Nat.card N ∣ Nat.card D := by
      rw [← hN_card_map]
      exact Subgroup.card_dvd_of_le hNmap_le_D
    have hN_odd : Odd (Nat.card N) :=
      hsec.section2.hA.A1.D_odd.of_dvd_nat hN_dvd_D
    have hN_coprime : Nat.Coprime 2 (Nat.card N) :=
      Nat.prime_two.coprime_iff_not_dvd.mpr hN_odd.not_two_dvd_nat
    have hE_injective : Function.Injective (π.subgroupMap E) := by
      intro x y hxy
      have hxyq : π (x : L) = π (y : L) := congrArg Subtype.val hxy
      have hdivN : (x : L) / (y : L) ∈ N :=
        (QuotientGroup.eq_iff_div_mem (N := N)).1 hxyq
      have hdivE : (x : L) / (y : L) ∈ E :=
        E.div_mem x.property y.property
      let d : N := ⟨(x : L) / (y : L), hdivN⟩
      have hd_sq : d ^ 2 = 1 := by
        apply Subtype.ext
        simpa [d] using congrArg Subtype.val (hE_sq ⟨(x : L) / (y : L), hdivE⟩)
      have horder_two : orderOf d ∣ 2 :=
        (orderOf_dvd_iff_pow_eq_one).2 hd_sq
      have horder_N : orderOf d ∣ Nat.card N := by
        simpa using (Subgroup.orderOf_dvd_natCard N d.property)
      have horder_one : orderOf d ∣ 1 := by
        simpa [hN_coprime.gcd_eq_one] using Nat.dvd_gcd horder_two horder_N
      have hd_one : d = 1 :=
        orderOf_eq_one_iff.mp (Nat.dvd_one.mp horder_one)
      have hdiv_one : (x : L) / (y : L) = 1 :=
        congrArg Subtype.val hd_one
      exact Subtype.ext (div_eq_one.mp hdiv_one)
    let Ebar : Subgroup (L ⧸ N) := E.map π
    let eE : E ≃* Ebar :=
      MulEquiv.ofBijective (π.subgroupMap E)
        ⟨hE_injective, MonoidHom.subgroupMap_surjective π E⟩
    refine ⟨Ebar, ?_, ?_⟩
    · calc
        Nat.card Ebar = Nat.card E := Nat.card_congr eE.symm.toEquiv
        _ = 4 := hE_card
    · intro x
      rcases eE.surjective x with ⟨y, rfl⟩
      simpa using congrArg eE (hE_sq y)
  have hAbar : HypothesisA (L ⧸ N) ΩX Hbar Dbar Qbar tbar :=
    ⟨hA1bar, hA2bar, hA3bar⟩
  have hlt : Nat.card (L ⧸ N) < Nat.card G := by
    have hL_ne_top : L ≠ ⊤ := by
      intro hL_top
      apply hX_ne
      apply le_antisymm
      · intro x hx
        rw [Subgroup.mem_bot]
        letI : FaithfulSMul G Ω := hsec.section2.hA.A2
        apply (FaithfulSMul.eq_of_smul_eq_smul (α := Ω))
        intro ω
        rcases hsec.section2.hA.A1.point_stabilizer with ⟨α, hH⟩
        have hxD : x ∈ D := by
          have hxV := hX_le_V hx
          rw [hsec.section2.V_eq] at hxV
          exact hxV.1
        have hxH : x ∈ H := hsec.section2.hA.A1.D_le_H hxD
        have hxfix : x • α = α := by
          rw [← MulAction.mem_stabilizer_iff, ← hH]
          exact hxH
        letI : MulAction.IsMultiplyPretransitive G Ω 2 :=
          hsec.section2.hA.A1.two_transitive
        have htrans : MulAction.IsPretransitive G Ω :=
          MulAction.isPretransitive_of_is_two_pretransitive
        rcases htrans.exists_smul_eq α ω with ⟨g, rfl⟩
        have hgL : g ∈ L := by
          rw [hL_top]
          trivial
        have hgcomm : x * g = g * x :=
          (Subgroup.mem_centralizer_iff.mp hgL) x hx
        calc
          x • (g • α) = (x * g) • α := by simp [smul_smul]
          _ = (g * x) • α := by rw [hgcomm]
          _ = g • (x • α) := by simp [smul_smul]
          _ = g • α := by rw [hxfix]
          _ = (1 : G) • (g • α) := by simp
      · exact bot_le
    have hL_lt : L < (⊤ : Subgroup G) :=
      lt_of_le_of_ne le_top hL_ne_top
    have hcardL : Nat.card L < Nat.card G := by
      simpa using natCard_lt_of_subgroup_lt hL_lt
    have hquot_le : Nat.card (L ⧸ N) ≤ Nat.card L :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)
    exact hquot_le.trans_lt hcardL
  rcases hind (L ⧸ N) ΩX Hbar Dbar Qbar tbar hlt hAbar with
    ⟨M, hM_normal, q, hodd, hq_power, hq_gt, hmodel⟩
  letI : M.Normal := hM_normal
  have hQbar_two : ∃ n : ℕ, Nat.card Qbar = 2 ^ n := by
    have hQbar_card : Nat.card Qbar = Nat.card ΩX - 1 := by
      rcases hA1bar.point_stabilizer with ⟨α, hHbar⟩
      let β : ΩX := tbar⁻¹ • α
      have hA1stab :
          HypothesisA1 (L ⧸ N) ΩX (MulAction.stabilizer (L ⧸ N) α)
            Dbar Qbar tbar := by
        simpa only [hHbar] using hA1bar
      have hβ_ne : β ≠ α := by
        intro hβ
        apply hA1stab.t_not_mem_H
        change tbar • α = α
        have ht_inv : tbar⁻¹ = tbar := hA1stab.involution_t.inv_eq_self
        simpa [β, ht_inv] using hβ
      have hDbar :
          Dbar = MulAction.stabilizer (L ⧸ N) α ⊓
            MulAction.stabilizer (L ⧸ N) β := by
        simpa [β, rightConjugate_stabilizer] using hA1stab.D_eq
      have hcard :=
        (hypothesisA1_Q_regular_on_complement hA1stab hβ_ne hDbar).ncard_eq
      have hcardQ :
          Nat.card Qbar = ({ω : ΩX | ω ≠ α} : Set ΩX).ncard := by
        simpa using hcard
      have hsum := Set.ncard_add_ncard_compl ({α} : Set ΩX)
      rw [Set.ncard_singleton] at hsum
      have hcompl :
          ({α} : Set ΩX)ᶜ = ({ω : ΩX | ω ≠ α} : Set ΩX) := by
        ext ω
        change (ω ≠ α) ↔ (ω ≠ α)
        rfl
      rw [hcompl, ← hcardQ] at hsum
      omega
    have hΩ_power : ∃ n : ℕ, Nat.card ΩX - 1 = 2 ^ n := by
      rcases hmodel with
          ⟨k, hk, _hqk, _eM, _rho, eΩ, _hnatural, _hequiv⟩ |
          ⟨k, hk, _hqk, _eM, _rho, eΩ, _hnatural, _hequiv⟩ |
          ⟨E, hEfield, hEfinite, J, hJstandard, hEcard, hfixedCard,
            _eM, _rho, eΩ, _hnatural, _hequiv⟩
      · have hfield : Nat.card (BinaryGaloisField k) = 2 ^ k := by
          simpa [BinaryGaloisField] using (GaloisField.card 2 k hk)
        have hpoints :
            Nat.card (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)) =
              2 ^ k + 1 := by
          calc
            _ = Nat.card (BinaryGaloisField k) + 1 :=
              Projectivization.card_of_finrank_two
                (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k) (by simp)
            _ = 2 ^ k + 1 := by rw [hfield]
        refine ⟨k, ?_⟩
        rw [Nat.card_congr eΩ, hpoints]
        omega
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        let pi : BinaryGaloisField (2 * k + 1) ≃+*
            BinaryGaloisField (2 * k + 1) :=
          iterateFrobeniusEquiv (BinaryGaloisField (2 * k + 1)) 2 (k + 1)
        have hpi : ∀ x : BinaryGaloisField (2 * k + 1),
            pi x = x ^ (2 ^ (k + 1)) := by
          intro x
          exact iterateFrobeniusEquiv_def
            (BinaryGaloisField (2 * k + 1)) 2 (k + 1) x
        rcases External.huppert_blackburn_XI_3_3 k hkpos pi hpi with
          ⟨_, _, _, _, _, hpoints, _, _⟩
        have hpoints' :
            let K := BinaryGaloisField (2 * k + 1)
            let pinf : ℙ K (Fin 4 → K) :=
              Projectivization.mk K ![1, 0, 0, 0] (by simp)
            let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
              Projectivization.mk K
                ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
                  y, x, 1] (by simp)
            let O : Set (ℙ K (Fin 4 → K)) :=
              {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
            Nat.card {z // z ∈ O} = (2 ^ (2 * k + 1)) ^ 2 + 1 := by
          simpa only [hpi] using hpoints
        refine ⟨(2 * k + 1) * 2, ?_⟩
        rw [Nat.card_congr eΩ, hpoints']
        simp [pow_mul]
      · letI : Field E := hEfield
        letI : Finite E := hEfinite
        have hpoints :=
          (External.huppert_II_10_12 J q hEcard hfixedCard hJstandard).1
        rcases hq_power with ⟨n, hn⟩
        refine ⟨n * 3, ?_⟩
        rw [Nat.card_congr eΩ, hpoints, hn]
        simp [pow_mul]
    rcases hΩ_power with ⟨n, hn⟩
    exact ⟨n, by rw [hQbar_card, hn]⟩
  have hQbar_sylow :
      ∃ P : Sylow 2 (L ⧸ N), Qbar = (P : Subgroup (L ⧸ N)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases PFchapter1section1.proposition_1_c Hbar Dbar Qbar tbar hA1bar with
      ⟨P, hP_le_Qbar⟩
    rcases hQbar_two with ⟨n, hQbar_card⟩
    have hQbar_pgroup : IsPGroup 2 Qbar :=
      IsPGroup.of_card hQbar_card
    exact ⟨P, P.is_maximal' hQbar_pgroup hP_le_Qbar⟩
  have hresidual_le_M : twoPrimeResidual (L ⧸ N) ≤ M := by
    rw [twoPrimeResidual]
    refine iSup_le ?_
    intro P
    let πM : (L ⧸ N) →* (L ⧸ N) ⧸ M := QuotientGroup.mk' M
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmapP :
        IsPGroup 2 ((P : Subgroup (L ⧸ N)).map πM) :=
      P.isPGroup'.map πM
    rcases IsPGroup.iff_card.mp hmapP with ⟨n, hn⟩
    have hcard_dvd :
        Nat.card ((P : Subgroup (L ⧸ N)).map πM) ∣
          Nat.card ((L ⧸ N) ⧸ M) :=
      Subgroup.card_subgroup_dvd_card ((P : Subgroup (L ⧸ N)).map πM)
    cases n with
    | zero =>
        have hmap_bot : (P : Subgroup (L ⧸ N)).map πM = ⊥ := by
          exact Subgroup.eq_bot_of_card_eq
            (H := (P : Subgroup (L ⧸ N)).map πM) (by simpa using hn)
        have hle_ker : (P : Subgroup (L ⧸ N)) ≤ πM.ker :=
          (Subgroup.map_eq_bot_iff
            (H := (P : Subgroup (L ⧸ N))) (f := πM)).mp hmap_bot
        simpa [πM, QuotientGroup.ker_mk'] using hle_ker
    | succ n =>
        have htwo_dvd_map :
            2 ∣ Nat.card ((P : Subgroup (L ⧸ N)).map πM) := by
          rw [hn]
          exact dvd_pow_self 2 (Nat.succ_ne_zero n)
        exact False.elim
          (hodd.not_two_dvd_nat (htwo_dvd_map.trans hcard_dvd))
  have hQbar_le_M : Qbar ≤ M := by
    rcases hQbar_sylow with ⟨P, hQbar_eq⟩
    rw [hQbar_eq]
    exact (le_iSup (fun S : Sylow 2 (L ⧸ N) =>
      (S : Subgroup (L ⧸ N))) P).trans hresidual_le_M
  have hM_simple : IsSimpleGroup M := by
    rcases hmodel with
        ⟨k, hk, hqk, eM, _rho, _eΩ, _hnatural, _hequiv⟩ |
        ⟨k, hk, _hqk, eM, _rho, _eΩ, _hnatural, _hequiv⟩ |
        ⟨E, hEfield, hEfinite, J, _hJstandard, hEcard, hfixedCard,
          eM, _rho, _eΩ, _hnatural, _hequiv⟩
    · have hfield_card : Nat.card (BinaryGaloisField k) = 2 ^ k := by
        simpa [BinaryGaloisField] using GaloisField.card 2 k hk
      have hsimple_model : IsSimpleGroup (PSL2BinaryMatrixGroup k) := by
        apply External.huppert_II_6_13 2 (by omega)
        · right
          rw [hfield_card, ← hqk]
          omega
        · right
          rw [hfield_card]
          intro h
          have heven : Even (2 ^ k) :=
            Nat.even_pow.mpr ⟨by norm_num, hk⟩
          rw [h] at heven
          exact (by decide : ¬ Even 3) heven
      exact eM.isSimpleGroup_congr.mpr hsimple_model
    · exact eM.isSimpleGroup_congr.mpr
        (External.huppert_blackburn_XI_3_6 k (Nat.pos_of_ne_zero hk)).1
    · letI : Field E := hEfield
      letI : Finite E := hEfinite
      exact eM.isSimpleGroup_congr.mpr
        (External.huppert_II_10_13 J q hq_gt hEcard hfixedCard)
  have hM_le_residual : M ≤ twoPrimeResidual (L ⧸ N) := by
    have hQbar_pgroup : IsPGroup 2 Qbar := by
      rcases hQbar_two with ⟨n, hn⟩
      exact IsPGroup.of_card hn
    have hQbar_ne : Qbar ≠ ⊥ := by
      have hQbar_even : Even (Nat.card Qbar) := hA1bar.Q_even
      intro hbot
      have hcard_one : Nat.card Qbar = 1 := by
        rw [hbot]
        simp
      rw [hcard_one] at hQbar_even
      exact (by decide : ¬ Even 1) hQbar_even
    let QM : Subgroup M := Qbar.subgroupOf M
    letI : IsSimpleGroup M := hM_simple
    have hQM_ne : QM ≠ ⊥ := by
      intro hbot
      apply hQbar_ne
      apply le_antisymm
      · intro x hx
        have hxQM : (⟨x, hQbar_le_M hx⟩ : M) ∈ QM := hx
        rw [hbot] at hxQM
        simpa using hxQM
      · exact bot_le
    have hnormal_top : Subgroup.normalClosure (QM : Set M) = ⊤ := by
      rcases (Subgroup.normalClosure_normal :
          (Subgroup.normalClosure (QM : Set M)).Normal).eq_bot_or_eq_top with
        hbot | htop
      · exfalso
        apply hQM_ne
        apply le_antisymm
        · intro x hx
          have hxclosure := Subgroup.le_normalClosure hx
          rw [hbot] at hxclosure
          simpa using hxclosure
        · exact bot_le
      · exact htop
    have hclosure_le :
        Subgroup.normalClosure (QM : Set M) ≤
          (twoPrimeResidual (L ⧸ N)).comap M.subtype := by
      intro x hx
      change (x : L ⧸ N) ∈ twoPrimeResidual (L ⧸ N)
      change x ∈ Subgroup.closure (Group.conjugatesOfSet (QM : Set M)) at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
          rcases Group.mem_conjugatesOfSet_iff.mp hx with
            ⟨a, ha, hconj⟩
          obtain ⟨m, rfl⟩ := isConj_iff.mp hconj
          let Qc : Subgroup (L ⧸ N) :=
            Qbar.map (MulAut.conj (m : L ⧸ N)).toMonoidHom
          have hQc_p : IsPGroup 2 Qc :=
            hQbar_pgroup.map (MulAut.conj (m : L ⧸ N)).toMonoidHom
          obtain ⟨P, hQc_le_P⟩ := hQc_p.exists_le_sylow
          rw [twoPrimeResidual]
          apply (le_iSup (fun S : Sylow 2 (L ⧸ N) =>
            (S : Subgroup (L ⧸ N))) P)
          apply hQc_le_P
          change (m : L ⧸ N) * (a : L ⧸ N) * (m : L ⧸ N)⁻¹ ∈ Qc
          refine ⟨(a : L ⧸ N), ?_, rfl⟩
          exact ha
      | one => exact (twoPrimeResidual (L ⧸ N)).one_mem
      | mul x y hx hy ihx ihy =>
          exact (twoPrimeResidual (L ⧸ N)).mul_mem ihx ihy
      | inv x hx ihx =>
          exact (twoPrimeResidual (L ⧸ N)).inv_mem ihx
    intro x hx
    let xM : M := ⟨x, hx⟩
    have hxclosure : xM ∈ Subgroup.normalClosure (QM : Set M) := by
      rw [hnormal_top]
      exact Subgroup.mem_top xM
    exact hclosure_le hxclosure
  have hresidual_eq : twoPrimeResidual (L ⧸ N) = M :=
    le_antisymm hresidual_le_M hM_le_residual
  have hQX_pgroup : IsPGroup 2 QX := by
    have hQbar_pgroup : IsPGroup 2 Qbar := by
      rcases hQbar_two with ⟨n, hn⟩
      exact IsPGroup.of_card hn
    rcases hQbar_iso with ⟨eQ⟩
    exact hQbar_pgroup.of_equiv eQ.symm
  have hQX_sylow :
      ∃ P : Sylow 2 L, QX = (P : Subgroup L) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases PFchapter1section1.proposition_1_c HX DX QX tX hA1X with
      ⟨P, hP_le_QX⟩
    exact ⟨P, P.is_maximal' hQX_pgroup hP_le_QX⟩
  have hCQ1_pgroup : IsPGroup 2 ↥(L ⊓ Q1) := by
    let CQ1L : Subgroup L := (L ⊓ Q1).subgroupOf L
    have hCQ1L_le_QX : CQ1L ≤ QX := by
      intro x hx
      change (x : G) ∈ Q
      exact hsec.section2.Q1_le_Q hx.2
    have hCQ1L_pgroup : IsPGroup 2 CQ1L :=
      hQX_pgroup.to_le hCQ1L_le_QX
    have hmap_eq : CQ1L.map L.subtype = L ⊓ Q1 := by
      exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
    have hmapped := hCQ1L_pgroup.map L.subtype
    rw [hmap_eq] at hmapped
    exact hmapped
  have hCQ1_odd : Odd (Nat.card ↥(L ⊓ Q1)) := by
    exact hsec.section2.Q1_odd_order.of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_right)
  have hCQ1 : L ⊓ Q1 = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases IsPGroup.iff_card.mp hCQ1_pgroup with ⟨n, hn⟩
    cases n with
    | zero =>
        exact Subgroup.eq_bot_of_card_eq (H := L ⊓ Q1) (by simpa using hn)
    | succ n =>
        exfalso
        apply hCQ1_odd.not_two_dvd_nat
        rw [hn]
        exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have hNL_centralizes_F : NL ≤ Subgroup.centralizer (F : Set G) := by
    have hN_le_centralizer_QX :
        N ≤ Subgroup.centralizer (QX : Set L) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      have hnG :
          (n : G) ∈ Subgroup.centralizer (L ⊓ Q : Set G) :=
        ((hcore_mem n).mp hn).2
      exact hnG (q : G) ⟨q.property, hq⟩
    have hresidual_le_centralizer_N :
        twoPrimeResidual L ≤ Subgroup.centralizer (N : Set L) := by
      let C : Subgroup L := Subgroup.centralizer (N : Set L)
      have hQX_le_C : QX ≤ C :=
        Subgroup.le_centralizer_iff.mp hN_le_centralizer_QX
      letI : C.Normal := by
        dsimp [C]
        infer_instance
      rw [twoPrimeResidual]
      refine iSup_le ?_
      intro P
      rcases hQX_sylow with ⟨P0, hQX_eq⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P0 P
      intro x hxP
      have hx_smul : x ∈ ((g • P0 : Sylow 2 L) : Subgroup L) := by
        simpa [hg] using hxP
      rw [Sylow.coe_subgroup_smul] at hx_smul
      have hyP0 : (MulAut.conj g)⁻¹ x ∈ (P0 : Subgroup L) :=
        (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
          (a := MulAut.conj g) (S := (P0 : Subgroup L)) (x := x)).mp hx_smul
      have hyQX : (MulAut.conj g)⁻¹ x ∈ QX := by
        rw [hQX_eq]
        exact hyP0
      have hyC : (MulAut.conj g)⁻¹ x ∈ C := hQX_le_C hyQX
      have hconjC := (inferInstance : C.Normal).conj_mem
        ((MulAut.conj g)⁻¹ x) hyC g
      simpa [C, mul_assoc] using hconjC
    have hN_le_centralizer_residual :
        N ≤ Subgroup.centralizer (twoPrimeResidual L : Set L) := by
      exact Subgroup.le_centralizer_iff.mpr hresidual_le_centralizer_N
    intro z hz
    rcases hz with ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    rcases hf with ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hN_le_centralizer_residual hn y hy)
  have hcenterF_le_NL : (Subgroup.center F).map F.subtype ≤ NL := by
    let FR : Subgroup L := twoPrimeResidual L
    let ZR : Subgroup L := (Subgroup.center FR).map FR.subtype
    have hQX_le_residual : QX ≤ FR := by
      rcases hQX_sylow with ⟨P, hQX_eq⟩
      rw [hQX_eq]
      change (P : Subgroup L) ≤ twoPrimeResidual L
      rw [twoPrimeResidual]
      exact le_iSup (fun S : Sylow 2 L => (S : Subgroup L)) P
    have hQX_ne : QX ≠ ⊥ := by
      intro hQX_bot
      have hQX_even : Even (Nat.card QX) := hA1X.Q_even
      rw [hQX_bot] at hQX_even
      norm_num at hQX_even
    letI : FR.Normal := by
      constructor
      intro x hx g
      have hmap_le :
          FR.map (MulAut.conj g).toMonoidHom ≤ FR := by
        dsimp [FR]
        rw [twoPrimeResidual, Subgroup.map_iSup]
        refine iSup_le ?_
        intro P
        let Pg : Sylow 2 L :=
          Sylow.mapSurjective (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).surjective P
        change (Pg : Subgroup L) ≤
          ⨆ S : Sylow 2 L, (S : Subgroup L)
        exact le_iSup (fun S : Sylow 2 L => (S : Subgroup L)) Pg
      exact hmap_le ⟨x, hx, rfl⟩
    letI : ZR.Normal := by
      dsimp [ZR]
      infer_instance
    have hZR_le_centralizer :
        ZR ≤ Subgroup.centralizer (FR : Set L) := by
      intro x hx
      rcases hx with ⟨xR, hxR_center, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yR : FR := ⟨y, hy⟩
      exact congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hxR_center) yR)
    intro z hz
    rcases hz with ⟨zF, hzF_center, rfl⟩
    have hzF_mem : (zF : G) ∈ (twoPrimeResidual L).map L.subtype := by
      exact zF.property
    rcases hzF_mem with ⟨zL, hzL_residual, hzL_value⟩
    let zR : FR := ⟨zL, hzL_residual⟩
    have hzR_center : zR ∈ Subgroup.center FR := by
      rw [Subgroup.mem_center_iff]
      intro yR
      have hyF_mem : ((yR : L) : G) ∈ F := by
        exact ⟨(yR : L), yR.property, rfl⟩
      let yF : F := ⟨((yR : L) : G), hyF_mem⟩
      have hcommF :=
        (Subgroup.mem_center_iff.mp hzF_center) yF
      apply Subtype.ext
      apply L.subtype_injective
      have hzL_value' : (zL : G) = (zF : G) := hzL_value
      calc
        ((yR : L) : G) * (zL : G) =
            ((yR : L) : G) * (zF : G) := by rw [hzL_value']
        _ = (zF : G) * ((yR : L) : G) :=
          congrArg Subtype.val hcommF
        _ = (zL : G) * ((yR : L) : G) := by rw [hzL_value']
    have hzL_ZR : zL ∈ ZR := by
      exact ⟨zR, hzR_center, rfl⟩
    have hzL_centralizes_QX :
        zL ∈ Subgroup.centralizer (QX : Set L) :=
      (Subgroup.centralizer_le hQX_le_residual)
        (hZR_le_centralizer hzL_ZR)
    have hzL_HX : zL ∈ HX := by
      exact
        (PFchapter1section1.proposition_1_b HX DX QX tX hA1X
          QX hQX_ne le_rfl)
            (centralizer_le_normalizer QX hzL_centralizes_QX)
    have hzL_conj_ZR : tX * zL * tX⁻¹ ∈ ZR := by
      exact (inferInstance : ZR.Normal).conj_mem zL hzL_ZR tX
    have hzL_conj_centralizes_QX :
        tX * zL * tX⁻¹ ∈ Subgroup.centralizer (QX : Set L) :=
      (Subgroup.centralizer_le hQX_le_residual)
        (hZR_le_centralizer hzL_conj_ZR)
    have hzL_conj_HX : tX * zL * tX⁻¹ ∈ HX := by
      exact
        (PFchapter1section1.proposition_1_b HX DX QX tX hA1X
          QX hQX_ne le_rfl)
            (centralizer_le_normalizer QX hzL_conj_centralizes_QX)
    have hzL_right : zL ∈ rightConjugate HX tX := by
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨tX * zL * tX⁻¹, hzL_conj_HX, ?_⟩
      simp [mul_assoc]
    have hzL_DX : zL ∈ DX := by
      have hDX_eq : DX = HX ⊓ rightConjugate HX tX := hA1X.D_eq
      rw [hDX_eq]
      exact ⟨hzL_HX, hzL_right⟩
    have hzL_N : zL ∈ N := by
      have hN_eq : N = DX ⊓ Subgroup.centralizer (QX : Set L) := h4c.1
      rw [hN_eq]
      exact ⟨hzL_DX, hzL_centralizes_QX⟩
    exact ⟨zL, hzL_N, hzL_value⟩
  have hNLF : NL ⊓ F = (Subgroup.center F).map F.subtype := by
    apply le_antisymm
    · intro z hz
      let zF : F := ⟨z, hz.2⟩
      have hzF_center : zF ∈ Subgroup.center F := by
        rw [Subgroup.mem_center_iff]
        intro f
        apply Subtype.ext
        have hzC := hNL_centralizes_F hz.1
        rw [Subgroup.mem_centralizer_iff] at hzC
        exact hzC (f : G) f.property
      exact ⟨zF, hzF_center, rfl⟩
    · intro z hz
      exact ⟨hcenterF_le_NL hz,
        (Subgroup.map_subtype_le (Subgroup.center F)) hz⟩
  have hmap_residual : (twoPrimeResidual L).map π = M := by
    rw [← hresidual_eq, twoPrimeResidual, Subgroup.map_iSup,
      twoPrimeResidual]
    apply le_antisymm
    · refine iSup_le ?_
      intro P
      let Pbar : Sylow 2 (L ⧸ N) :=
        Sylow.mapSurjective (f := π)
          (QuotientGroup.mk'_surjective N) P
      change (Pbar : Subgroup (L ⧸ N)) ≤
        ⨆ S : Sylow 2 (L ⧸ N), (S : Subgroup (L ⧸ N))
      exact le_iSup
        (fun S : Sylow 2 (L ⧸ N) => (S : Subgroup (L ⧸ N))) Pbar
    · refine iSup_le ?_
      intro Pbar
      obtain ⟨P, hP⟩ :=
        (Sylow.mapSurjective_surjective (f := π)
          (QuotientGroup.mk'_surjective N) 2) Pbar
      rw [← hP]
      exact le_iSup
        (fun S : Sylow 2 L => (S : Subgroup L).map π) P
  have hFquotM : Nonempty ((F ⧸ Subgroup.center F) ≃* M) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let FR : Subgroup L := twoPrimeResidual L
    let eF : FR ≃* F :=
      Subgroup.equivMapOfInjective FR L.subtype L.subtype_injective
    let φ0 : F →* L ⧸ N :=
      (π.comp FR.subtype).comp eF.symm.toMonoidHom
    have hφ0_le_M : φ0.range ≤ M := by
      rintro y ⟨x, rfl⟩
      change π (FR.subtype (eF.symm x)) ∈ M
      rw [← hmap_residual]
      exact ⟨eF.symm x, (eF.symm x).property, rfl⟩
    let φ : F →* M :=
      φ0.codRestrict M fun x => hφ0_le_M ⟨x, rfl⟩
    have hφ_surjective : Function.Surjective φ := by
      intro m
      have hm_map : (m : L ⧸ N) ∈ FR.map π := by
        rw [hmap_residual]
        exact m.property
      rcases hm_map with ⟨r, hr, hr_value⟩
      let rFR : FR := ⟨r, hr⟩
      let x : F := eF rFR
      refine ⟨x, ?_⟩
      apply Subtype.ext
      simpa [φ, φ0, x, rFR] using hr_value
    have hφ_ker : φ.ker = Subgroup.center F := by
      ext x
      rw [MonoidHom.mem_ker]
      let r : FR := eF.symm x
      have hr_value : ((r : L) : G) = (x : G) := by
        calc
          ((r : L) : G) = ((eF r : F) : G) :=
            (Subgroup.coe_equivMapOfInjective_apply FR L.subtype
              L.subtype_injective r).symm
          _ = (x : G) := congrArg Subtype.val (eF.apply_symm_apply x)
      constructor
      · intro hx
        have hπ_one : π (FR.subtype r) = 1 := by
          have hx_value := congrArg Subtype.val hx
          simpa [φ, φ0, r] using hx_value
        have hrN : (r : L) ∈ N :=
          (QuotientGroup.eq_one_iff (N := N) (x := (r : L))).mp hπ_one
        have hxNL : (x : G) ∈ NL := by
          exact ⟨(r : L), hrN, hr_value⟩
        have hx_center_map :
            (x : G) ∈ (Subgroup.center F).map F.subtype := by
          rw [← hNLF]
          exact ⟨hxNL, x.property⟩
        rcases hx_center_map with ⟨z, hz_center, hz_value⟩
        have hzx : z = x := by
          apply Subtype.ext
          exact hz_value
        simpa [← hzx] using hz_center
      · intro hx_center
        have hxNL : (x : G) ∈ NL :=
          hcenterF_le_NL ⟨x, hx_center, rfl⟩
        rcases hxNL with ⟨n, hn, hn_value⟩
        have hr_eq_n : (r : L) = n := by
          apply L.subtype_injective
          exact hr_value.trans hn_value.symm
        have hrN : (r : L) ∈ N := by
          rw [hr_eq_n]
          exact hn
        apply Subtype.ext
        change π (FR.subtype (eF.symm x)) = 1
        exact (QuotientGroup.eq_one_iff (N := N)
          (x := (FR.subtype (eF.symm x)))).mpr (by simpa [r] using hrN)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hφ_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ_surjective)⟩
  have hSuzuki_standard_sylow_typeA :
      ∀ (k : ℕ), k ≠ 0 → q = 2 ^ (2 * k + 1) →
        ∃ Pstd : Sylow 2 (SuzukiMatrixGroup k),
          IsSuzukiTwoTypeA (Pstd : Subgroup (SuzukiMatrixGroup k)) ∧
            Nat.card Pstd = q ^ 2 ∧
              (∀ a b : BinaryGaloisField (2 * k + 1),
                SuzukiRootGL k a b ∈
                  (Pstd : Subgroup (SuzukiMatrixGroup k)).map
                    (SuzukiMatrixGroup k).subtype) ∧
              ∀ x : SuzukiMatrixGroup k,
                x ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) ↔
                  (x : GL (Fin 4) (BinaryGaloisField (2 * k + 1))) ∈
                    Subgroup.closure
                      {A | ∃ a b : BinaryGaloisField (2 * k + 1),
                        A = SuzukiRootGL k a b} := by
    intro k hk hqk
    have hstandard_sylow_typeA :
        ∃ Pstd : Sylow 2 (SuzukiMatrixGroup k),
          IsSuzukiTwoTypeA (Pstd : Subgroup (SuzukiMatrixGroup k)) ∧
            Nat.card Pstd = q ^ 2 ∧
              (∀ a b : BinaryGaloisField (2 * k + 1),
                SuzukiRootGL k a b ∈
                  (Pstd : Subgroup (SuzukiMatrixGroup k)).map
                    (SuzukiMatrixGroup k).subtype) ∧
              ∀ x : SuzukiMatrixGroup k,
                x ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) ↔
                  (x : GL (Fin 4) (BinaryGaloisField (2 * k + 1))) ∈
                    Subgroup.closure
                      {A | ∃ a b : BinaryGaloisField (2 * k + 1),
                        A = SuzukiRootGL k a b} := by
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      let K := BinaryGaloisField (2 * k + 1)
      let pi : K ≃+* K :=
        iterateFrobeniusEquiv K 2 (k + 1)
      have hpi : ∀ x : K, pi x = x ^ (2 ^ (k + 1)) := by
        intro x
        exact iterateFrobeniusEquiv_def K 2 (k + 1) x
      have hK_card : Nat.card K = 2 ^ (2 * k + 1) := by
        simpa [K, BinaryGaloisField] using
          GaloisField.card 2 (2 * k + 1) (by omega)
      have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 := by
        intro x
        letI : Fintype K := Fintype.ofFinite K
        calc
          pi (pi x) = (pi x) ^ (2 ^ (k + 1)) := hpi (pi x)
          _ = (x ^ (2 ^ (k + 1))) ^ (2 ^ (k + 1)) := by rw [hpi]
          _ = x ^ (2 ^ (k + 1 + (k + 1))) := by
            rw [← pow_mul, ← pow_add]
          _ = x ^ (2 ^ ((2 * k + 1) + 1)) := by
            congr 2
            omega
          _ = (x ^ (2 ^ (2 * k + 1))) ^ 2 := by
            rw [pow_succ, pow_mul]
          _ = x ^ 2 := by
            have hx_card : x ^ Nat.card K = x := by
              rw [← Fintype.card_eq_nat_card]
              exact FiniteField.pow_card x
            rw [← hK_card, hx_card]
      let Froot : Subgroup (GL (Fin 4) K) :=
        Subgroup.closure
          {A | ∃ a b : K, A = SuzukiRootGL k a b}
      have hFroot_data :
          IsPGroup 2 Froot ∧
            Nat.card Froot = (2 ^ (2 * k + 1)) ^ 2 ∧
              IsSuzukiTwoTypeA Froot := by
        rcases External.huppert_blackburn_XI_3_1 k hkpos pi hpi_sq with
          ⟨_hpi_unique, _hpi_formula, hFroot_pgroup, _hFroot_exp,
            _hFroot_order_four, _hFroot_class, hFroot_card,
            hFroot_typeA, _hFroot_mul, _hFroot_commutator,
            _hFroot_commutator_mem, _hTorus_equiv, _hTorus_conj,
            _hFroot_disjoint, _hTorus_fixed_free⟩
        simpa [K, Froot] using
          And.intro hFroot_pgroup
            (And.intro hFroot_card hFroot_typeA)
      have hFroot_le : Froot ≤ SuzukiMatrixGroup k := by
        have hroot_le :
            Subgroup.closure
                {A : GL (Fin 4) (BinaryGaloisField (2 * k + 1)) |
                  ∃ a b : BinaryGaloisField (2 * k + 1),
                    A = SuzukiRootGL k a b} ≤
              Subgroup.closure (SuzukiMatrixGeneratorSet k) := by
          apply Subgroup.closure_mono
          intro A hA
          rw [SuzukiMatrixGeneratorSet]
          exact Or.inl hA
        simpa only [Froot, K, SuzukiMatrixSubgroup] using hroot_le
      let FS : Subgroup (SuzukiMatrixGroup k) :=
        Froot.comap (SuzukiMatrixGroup k).subtype
      have hFS_map :
          FS.map (SuzukiMatrixGroup k).subtype = Froot := by
        apply le_antisymm
        · rintro x ⟨y, hy, rfl⟩
          exact hy
        · intro x hx
          exact ⟨⟨x, hFroot_le hx⟩, hx, rfl⟩
      let eFS : FS ≃* Froot :=
        (Subgroup.equivMapOfInjective FS
          (SuzukiMatrixGroup k).subtype
          (SuzukiMatrixGroup k).subtype_injective).trans
            (MulEquiv.subgroupCongr hFS_map)
      have hFS_pgroup : IsPGroup 2 FS :=
        hFroot_data.1.of_equiv eFS.symm
      have hFS_card : Nat.card FS = q ^ 2 := by
        calc
          Nat.card FS = Nat.card Froot := Nat.card_congr eFS.toEquiv
          _ = (2 ^ (2 * k + 1)) ^ 2 := hFroot_data.2.1
          _ = q ^ 2 := by rw [hqk]
      have hFS_typeA : IsSuzukiTwoTypeA FS := by
        rcases hFroot_data.2.2 with
          ⟨n, hn, theta, pairLift, cocycle, htheta_order,
            htheta_nontrivial, hcocycle_add_left, hcocycle_add_right,
            hcocycle_diag, hpair_mem, hpair_one, hpair_surjective,
            hpair_injective, hpair_mul⟩
        let pairLiftS :
            BinaryGaloisField n → BinaryGaloisField n →
              SuzukiMatrixGroup k :=
          fun a z => ⟨pairLift a z, hFroot_le (hpair_mem a z)⟩
        refine ⟨n, hn, theta, pairLiftS, cocycle, htheta_order,
          htheta_nontrivial, hcocycle_add_left, hcocycle_add_right,
          hcocycle_diag, ?_, ?_, ?_, ?_, ?_⟩
        · intro a z
          exact hpair_mem a z
        · apply Subtype.ext
          exact hpair_one
        · intro x hx
          rcases hpair_surjective (x : GL (Fin 4) K) hx with
            ⟨a, z, hxaz⟩
          exact ⟨a, z, Subtype.ext hxaz⟩
        · intro a z b w hab
          exact hpair_injective a z b w (congrArg Subtype.val hab)
        · intro a z b w
          apply Subtype.ext
          exact hpair_mul a z b w
      have hG_card :
          Nat.card (SuzukiMatrixGroup k) =
            ((2 ^ (2 * k + 1)) ^ 2 + 1) *
              (2 ^ (2 * k + 1)) ^ 2 *
                (2 ^ (2 * k + 1) - 1) := by
        rcases External.huppert_blackburn_XI_3_3 k hkpos pi hpi with
          ⟨_haction, _hfull, _hfaithful, _htwo_transitive,
            _hthree_fixed, _hpoints, hcard, _hstabilizer⟩
        simpa [K] using hcard
      have hG_card_q :
          Nat.card (SuzukiMatrixGroup k) =
            (q ^ 2 + 1) * q ^ 2 * (q - 1) := by
        rw [hG_card, hqk]
      obtain ⟨Pstd, hFS_le_Pstd⟩ := hFS_pgroup.exists_le_sylow
      have hq_even : Even q := by
        rw [hqk]
        exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      have hq_sq_even : Even (q ^ 2) :=
        hq_even.pow_of_ne_zero (by norm_num)
      have hq_sub_one_odd : Odd (q - 1) :=
        Nat.Even.sub_odd (by omega) hq_even odd_one
      have houter_odd : Odd ((q ^ 2 + 1) * (q - 1)) :=
        hq_sq_even.add_one.mul hq_sub_one_odd
      obtain ⟨m, hPstd_power⟩ :=
        IsPGroup.iff_card.mp Pstd.isPGroup'
      have hPstd_dvd_group :
          Nat.card Pstd ∣ Nat.card (SuzukiMatrixGroup k) :=
        (Pstd : Subgroup (SuzukiMatrixGroup k)).card_subgroup_dvd_card
      have hPstd_dvd_product :
          Nat.card Pstd ∣ q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by
        rw [hG_card_q] at hPstd_dvd_group
        simpa [mul_assoc, mul_comm, mul_left_comm] using hPstd_dvd_group
      have hPstd_coprime_outer :
          Nat.Coprime (Nat.card Pstd) ((q ^ 2 + 1) * (q - 1)) := by
        rw [hPstd_power]
        exact Nat.Coprime.pow_left m houter_odd.coprime_two_left
      have hPstd_dvd_qsq : Nat.card Pstd ∣ q ^ 2 :=
        hPstd_coprime_outer.dvd_of_dvd_mul_right hPstd_dvd_product
      have hqsq_dvd_Pstd : q ^ 2 ∣ Nat.card Pstd := by
        rw [← hFS_card]
        exact Subgroup.card_dvd_of_le hFS_le_Pstd
      have hPstd_card : Nat.card Pstd = q ^ 2 :=
        Nat.dvd_antisymm hPstd_dvd_qsq hqsq_dvd_Pstd
      have hFS_eq_Pstd : FS = (Pstd : Subgroup (SuzukiMatrixGroup k)) :=
        Subgroup.eq_of_le_of_card_ge hFS_le_Pstd (by
          rw [hPstd_card, hFS_card])
      have hPstd_typeA :
          IsSuzukiTwoTypeA
            (Pstd : Subgroup (SuzukiMatrixGroup k)) := by
        rw [← hFS_eq_Pstd]
        exact hFS_typeA
      have hPstd_root_mem :
          ∀ a b : BinaryGaloisField (2 * k + 1),
            SuzukiRootGL k a b ∈
              (Pstd : Subgroup (SuzukiMatrixGroup k)).map
                (SuzukiMatrixGroup k).subtype := by
        intro a b
        rw [← hFS_eq_Pstd, hFS_map]
        exact Subgroup.subset_closure ⟨a, b, rfl⟩
      have hPstd_root_iff :
          ∀ x : SuzukiMatrixGroup k,
            x ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) ↔
              (x : GL (Fin 4) (BinaryGaloisField (2 * k + 1))) ∈
                Subgroup.closure
                  {A | ∃ a b : BinaryGaloisField (2 * k + 1),
                    A = SuzukiRootGL k a b} := by
        intro x
        rw [← hFS_eq_Pstd]
        rfl
      exact ⟨Pstd, hPstd_typeA, hPstd_card, hPstd_root_mem,
        hPstd_root_iff⟩
    exact hstandard_sylow_typeA
  have hq_eq_Q0 : q = Nat.card ↥(L ⊓ Q0) := by
    let Q0X : Subgroup L := Q0.comap L.subtype
    have hQ0X_le_QX : Q0X ≤ QX := by
      intro x hx
      exact hsec.section2.Q0_le_Q hx
    let Q0QX : Subgroup QX := Q0X.subgroupOf QX
    rcases hQbar_iso with ⟨eQ⟩
    let IQ : Subgroup Qbar := Q0QX.map eQ.toMonoidHom
    have hLQ0_equiv_IQ : Nonempty (↥(L ⊓ Q0) ≃* IQ) := by
      have hmap_Q0X : Q0X.map L.subtype = L ⊓ Q0 := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y.property, hy⟩
        · intro hx
          exact ⟨(⟨x, hx.1⟩ : L), hx.2, rfl⟩
      let eQ0XLQ0 : Q0X ≃* ↥(L ⊓ Q0) :=
        (Subgroup.equivMapOfInjective Q0X L.subtype L.subtype_injective).trans
          (MulEquiv.subgroupCongr hmap_Q0X)
      let eQ0XQ0QX : Q0QX ≃* Q0X :=
        Subgroup.subgroupOfEquivOfLe hQ0X_le_QX
      let eQ0QXIQ : Q0QX ≃* IQ :=
        Subgroup.equivMapOfInjective Q0QX eQ.toMonoidHom eQ.injective
      exact ⟨eQ0XLQ0.symm.trans (eQ0XQ0QX.symm.trans eQ0QXIQ)⟩
    have hIQ_sq_iff : ∀ x : Qbar, x ∈ IQ ↔ x ^ 2 = 1 := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hyQ0 : (((y : QX) : L) : G) ∈ Q0 := hy
        have hy_sq : y ^ 2 = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          rcases (hsec.section2.Q0_def (((y : QX) : L) : G)).mp hyQ0 with
            hy_one | hy_inv
          · simp [hy_one]
          · exact hy_inv.2.sq_eq_one
        calc
          eQ.toMonoidHom y ^ 2 = eQ (y ^ 2) := (map_pow eQ y 2).symm
          _ = eQ 1 := congrArg eQ hy_sq
          _ = 1 := map_one eQ
      · intro hx_sq
        let y : QX := eQ.symm x
        have hy_sq : y ^ 2 = 1 := by
          calc
            y ^ 2 = eQ.symm (x ^ 2) := (map_pow eQ.symm x 2).symm
            _ = eQ.symm 1 := congrArg eQ.symm hx_sq
            _ = 1 := map_one eQ.symm
        have hyQ0 : ((y : L) : G) ∈ Q0 := by
          apply (hsec.section2.Q0_def ((y : L) : G)).mpr
          by_cases hy_one : y = 1
          · left
            exact congrArg Subtype.val (congrArg Subtype.val hy_one)
          · right
            refine ⟨hsec.section2.hA.A1.Q_le_H y.property, ?_⟩
            constructor
            · intro hyG_one
              apply hy_one
              apply Subtype.ext
              apply Subtype.ext
              exact hyG_one
            · exact congrArg Subtype.val (congrArg Subtype.val hy_sq)
        refine ⟨y, ?_, eQ.apply_symm_apply x⟩
        exact hyQ0
    have hIQ_card : Nat.card IQ = q := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases hQbar_sylow with ⟨Pbar, hPbar⟩
      have hPbar_le_M : (Pbar : Subgroup (L ⧸ N)) ≤ M := by
        rw [← hPbar]
        exact hQbar_le_M
      let PM : Sylow 2 M := Pbar.subtype hPbar_le_M
      let eQbarPM : Qbar ≃* PM :=
        (MulEquiv.subgroupCongr hPbar).trans
          (Subgroup.subgroupOfEquivOfLe hPbar_le_M).symm
      rcases hmodel with
          ⟨k, hk, hqk, eM, rho, eΩ, hnatural, hequiv⟩ |
          ⟨k, hk, hqk, eM, rho, eΩ, hnatural, hequiv⟩ |
          ⟨E, hEfield, hEfinite, J, hJstandard, hEcard, hfixedCard,
            eM, rho, eΩ, hnatural, hequiv⟩
      · let Pmodel : Sylow 2 (PSL2BinaryMatrixGroup k) :=
          PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
        let eQbarModel : Qbar ≃* Pmodel :=
          eQbarPM.trans
            (Subgroup.equivMapOfInjective (PM : Subgroup M)
              eM.toMonoidHom eM.injective)
        have hPSL_count : Nat.card IQ = q := by
          have hfield_card : Nat.card (BinaryGaloisField k) = 2 ^ k := by
            simpa [BinaryGaloisField] using GaloisField.card 2 k hk
          rcases External.huppert_II_8_2_a_sylow_equiv_additive
              hfield_card Pmodel with ⟨eAdd⟩
          have hPmodel_sq : ∀ y : Pmodel, y ^ 2 = 1 := by
            intro y
            rcases eAdd.surjective y with ⟨a, rfl⟩
            calc
              eAdd a ^ 2 = eAdd (a ^ 2) := (map_pow eAdd a 2).symm
              _ = eAdd 1 := by
                congr 1
                rw [pow_two]
                change a.toAdd + a.toAdd = 0
                have htwo : (2 : BinaryGaloisField k) = 0 :=
                  CharP.cast_eq_zero (BinaryGaloisField k) 2
                rw [← two_mul, htwo, zero_mul]
              _ = 1 := map_one eAdd
          have hQbar_sq : ∀ x : Qbar, x ^ 2 = 1 := by
            intro x
            apply eQbarModel.injective
            simpa only [map_pow, map_one] using hPmodel_sq (eQbarModel x)
          have hIQ_top : IQ = ⊤ := by
            apply top_unique
            intro x _hx
            exact (hIQ_sq_iff x).mpr (hQbar_sq x)
          calc
            Nat.card IQ = Nat.card Qbar := by rw [hIQ_top, Subgroup.card_top]
            _ = Nat.card Pmodel := Nat.card_congr eQbarModel.toEquiv
            _ = Nat.card (Multiplicative (BinaryGaloisField k)) :=
              Nat.card_congr eAdd.symm.toEquiv
            _ = 2 ^ k := hfield_card
            _ = q := hqk.symm
        exact hPSL_count
      · let Pmodel : Sylow 2 (SuzukiMatrixGroup k) :=
          PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
        let eQbarModel : Qbar ≃* Pmodel :=
          eQbarPM.trans
            (Subgroup.equivMapOfInjective (PM : Subgroup M)
              eM.toMonoidHom eM.injective)
        have hSuzuki_count : Nat.card IQ = q := by
          have hstandard_sylow_typeA :=
            hSuzuki_standard_sylow_typeA k hk hqk
          have htypeA_twoTorsion_count :
              ∀ {A : Type} [Group A] [Finite A] (P : Subgroup A),
                IsSuzukiTwoTypeA P → Nat.card P = q ^ 2 →
                  Nat.card {x : P // x ^ 2 = 1} = q := by
            intro A _groupA _finiteA P hP_typeA hP_card
            rcases hP_typeA with
              ⟨n, hn, theta, pairLift, cocycle, _htheta_order,
                _htheta_nontrivial, _hcocycle_add_left, _hcocycle_add_right,
                hcocycle_diag, hpair_mem, hpair_one, hpair_surjective,
                hpair_injective, hpair_mul⟩
            have hadd_self (z : BinaryGaloisField n) : z + z = 0 := by
              rw [← two_smul (BinaryGaloisField n) z]
              simp only [CharTwo.two_eq_zero, zero_smul]
            let pairToP :
                BinaryGaloisField n × BinaryGaloisField n → P :=
              fun z => ⟨pairLift z.1 z.2, hpair_mem z.1 z.2⟩
            have hpairToP_injective : Function.Injective pairToP := by
              intro z w hzw
              have hpair_eq : pairLift z.1 z.2 = pairLift w.1 w.2 :=
                congrArg Subtype.val hzw
              exact Prod.ext (hpair_injective _ _ _ _ hpair_eq).1
                (hpair_injective _ _ _ _ hpair_eq).2
            have hpairToP_surjective : Function.Surjective pairToP := by
              intro x
              rcases hpair_surjective (x : A) x.property with ⟨a, z, hx⟩
              refine ⟨(a, z), ?_⟩
              apply Subtype.ext
              exact hx.symm
            let ePair : BinaryGaloisField n × BinaryGaloisField n ≃ P :=
              Equiv.ofBijective pairToP
                ⟨hpairToP_injective, hpairToP_surjective⟩
            have hcoord_card :
                Nat.card P = Nat.card (BinaryGaloisField n) ^ 2 := by
              calc
                Nat.card P =
                    Nat.card (BinaryGaloisField n × BinaryGaloisField n) :=
                  Nat.card_congr ePair.symm
                _ = Nat.card (BinaryGaloisField n) ^ 2 := by
                  rw [Nat.card_prod, pow_two]
            have hfield_card : Nat.card (BinaryGaloisField n) = q := by
              apply Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)
              calc
                Nat.card (BinaryGaloisField n) ^ 2 = Nat.card P :=
                  hcoord_card.symm
                _ = q ^ 2 := hP_card
            let torsionMap :
                BinaryGaloisField n → {x : P // x ^ 2 = 1} :=
              fun z => ⟨⟨pairLift 0 z, hpair_mem 0 z⟩, by
                apply Subtype.ext
                simp only [Subgroup.coe_one, pow_two]
                calc
                  pairLift 0 z * pairLift 0 z =
                      pairLift (0 + 0) (z + z + cocycle 0 0) :=
                    hpair_mul 0 z 0 z
                  _ = pairLift 0 0 := by
                    rw [hadd_self 0, hadd_self z, hcocycle_diag]
                    simp
                  _ = 1 := hpair_one⟩
            have htorsionMap_injective : Function.Injective torsionMap := by
              intro z w hzw
              have hpair_eq : pairLift 0 z = pairLift 0 w :=
                congrArg (fun x : {x : P // x ^ 2 = 1} =>
                  ((x.1 : P) : A)) hzw
              exact (hpair_injective 0 z 0 w hpair_eq).2
            have htorsionMap_surjective : Function.Surjective torsionMap := by
              intro x
              rcases hpair_surjective ((x.1 : P) : A) x.1.property with
                ⟨a, z, hx⟩
              have hx_sq_A :
                  ((x.1 : P) : A) * ((x.1 : P) : A) = 1 := by
                simpa [pow_two] using congrArg Subtype.val x.property
              have hpair_sq : pairLift a z * pairLift a z = 1 := by
                rw [← hx]
                exact hx_sq_A
              have hpair_coords :
                  pairLift (a + a) (z + z + cocycle a a) = pairLift 0 0 := by
                calc
                  pairLift (a + a) (z + z + cocycle a a) =
                      pairLift a z * pairLift a z :=
                    (hpair_mul a z a z).symm
                  _ = 1 := hpair_sq
                  _ = pairLift 0 0 := hpair_one.symm
              have hsecond :=
                (hpair_injective (a + a) (z + z + cocycle a a) 0 0
                  hpair_coords).2
              have hcocycle_zero : cocycle a a = 0 := by
                rw [hadd_self z] at hsecond
                simpa using hsecond
              rw [hcocycle_diag] at hcocycle_zero
              have ha : a = 0 := by
                rcases mul_eq_zero.mp hcocycle_zero with ha | htheta
                · exact ha
                · apply theta.injective
                  simpa using htheta
              refine ⟨z, ?_⟩
              apply Subtype.ext
              apply Subtype.ext
              simpa [torsionMap, pairToP, ha] using hx.symm
            let eTorsion :
                BinaryGaloisField n ≃ {x : P // x ^ 2 = 1} :=
              Equiv.ofBijective torsionMap
                ⟨htorsionMap_injective, htorsionMap_surjective⟩
            calc
              Nat.card {x : P // x ^ 2 = 1} =
                  Nat.card (BinaryGaloisField n) := Nat.card_congr eTorsion.symm
              _ = q := hfield_card
          rcases hstandard_sylow_typeA with
            ⟨Pstd, hPstd_typeA, hPstd_card, _hPstd_root_mem,
              _hPstd_root_iff⟩
          let eQbarStd : Qbar ≃* Pstd :=
            eQbarModel.trans (Sylow.equiv Pmodel Pstd)
          let eIQPstd : IQ ≃ {x : Pstd // x ^ 2 = 1} :=
            { toFun := fun x => ⟨eQbarStd (x : Qbar), by
                have hx_sq := (hIQ_sq_iff (x : Qbar)).mp x.property
                simpa only [map_pow, map_one] using
                  congrArg eQbarStd hx_sq⟩
              invFun := fun x => ⟨eQbarStd.symm (x : Pstd), by
                apply (hIQ_sq_iff _).mpr
                simpa only [map_pow, map_one] using
                  congrArg eQbarStd.symm x.property⟩
              left_inv := fun x => by
                apply Subtype.ext
                exact eQbarStd.symm_apply_apply (x : Qbar)
              right_inv := fun x => by
                apply Subtype.ext
                exact eQbarStd.apply_symm_apply (x : Pstd) }
          calc
            Nat.card IQ = Nat.card {x : Pstd // x ^ 2 = 1} :=
              Nat.card_congr eIQPstd
            _ = q := htypeA_twoTorsion_count
              (A := SuzukiMatrixGroup k) Pstd hPstd_typeA hPstd_card
        exact hSuzuki_count
      · letI : Field E := hEfield
        letI : Finite E := hEfinite
        let Pmodel : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
          PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
        let eQbarModel : Qbar ≃* Pmodel :=
          eQbarPM.trans
            (Subgroup.equivMapOfInjective (PM : Subgroup M)
              eM.toMonoidHom eM.injective)
        have hPSU_count : Nat.card IQ = q := by
          let Coord :=
            {z : E × E //
              z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}
          rcases External.huppert_II_10_12 J q hEcard hfixedCard
              hJstandard with
            ⟨_hOmega_card, rhoU, pinf, _hrhoU_injective, _hnaturalU,
              hU_card, hroot_exists, _htwo_transitive, hG_card,
              _hthree_fixed⟩
          rcases hroot_exists with
            ⟨R, HR, _hR_le_U, _hHR_le_U, _hU_normalizes_R,
              _hR_disjoint_HR, _hR_join_HR, _hHR_cyclic, hR_card,
              _hcommutator_center, _hcommutator_card, _hHR_card,
              _hR_regular, hcoord_exists, _hHR_coord, _hHR_coord_surjective⟩
          rcases hcoord_exists with ⟨coordR, hcoord_matrix⟩
          letI : Fintype E := Fintype.ofFinite E
          letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
            Finite.of_surjective eM eM.surjective
          letI : Fintype (ProjectiveSpecialUnitaryMatrixGroup J) :=
            Fintype.ofFinite (ProjectiveSpecialUnitaryMatrixGroup J)
          have hq_even : Even q := by
            rcases hq_power with ⟨n, hn⟩
            have hnpos : 0 < n := by
              by_contra hn_not_pos
              have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn_not_pos
              subst n
              norm_num at hn
              omega
            rw [hn]
            exact Nat.even_pow.mpr ⟨even_two, ne_of_gt hnpos⟩
          have hE_even : Even (Fintype.card E) := by
            rw [Fintype.card_eq_nat_card, hEcard]
            exact hq_even.pow_of_ne_zero (by norm_num)
          have hcharE : ringChar E = 2 :=
            FiniteField.even_card_iff_char_two.mpr
              (Nat.even_iff.mp hE_even)
          have htwoE : (2 : E) = 0 := by
            simpa [hcharE] using
              (CharP.cast_eq_zero E (ringChar E))
          have hR_pgroup : IsPGroup 2 R := by
            rcases hq_power with ⟨n, hn⟩
            apply IsPGroup.of_card (n := n * 3)
            rw [hR_card, hn, pow_mul]
          have hadd_selfE (a : E) : a + a = 0 := by
            rw [← two_mul, htwoE, zero_mul]
          have hneg_selfE (a : E) : -a = a := by
            rw [neg_eq_iff_add_eq_zero, hadd_selfE]
          have hcoord_square_iff :
              ∀ z : Coord, (coordR z) ^ 2 = 1 ↔ z.1.1 = 0 := by
            intro z
            rcases hcoord_matrix z with ⟨M, hMval, hcoordM⟩
            constructor
            · intro hz_sq
              have hz_sq_G :
                  ((coordR z : R) :
                    ProjectiveSpecialUnitaryMatrixGroup J) ^ 2 = 1 := by
                simpa using congrArg
                  (fun x : R =>
                    (x : ProjectiveSpecialUnitaryMatrixGroup J)) hz_sq
              have hz_sq_PGL :
                  ((((coordR z : R) :
                    ProjectiveSpecialUnitaryMatrixGroup J) :
                      Matrix.ProjGenLinGroup (Fin 3) E) ^ 2) = 1 := by
                simpa using congrArg
                  (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
                    (x : Matrix.ProjGenLinGroup (Fin 3) E)) hz_sq_G
              rw [hcoordM] at hz_sq_PGL
              have hM_mem_ker :
                  M ^ 2 ∈
                    (Matrix.ProjGenLinGroup.mk :
                      GL (Fin 3) E →*
                        Matrix.ProjGenLinGroup (Fin 3) E).ker := by
                rw [MonoidHom.mem_ker]
                simpa only [map_pow] using hz_sq_PGL
              rw [Matrix.ProjGenLinGroup.ker_mk] at hM_mem_ker
              rcases
                  (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
                    hM_mem_ker) with
                ⟨c, hc⟩
              have hc02 :=
                congrFun (congrFun hc (0 : Fin 3)) (2 : Fin 3)
              have hc02' :
                  (0 : E) =
                    z.1.2 + z.1.1 * (-J.conj z.1.1) + z.1.2 := by
                simpa [pow_two, hMval, Matrix.mul_apply,
                  Fin.sum_univ_three] using hc02
              rw [hneg_selfE] at hc02'
              have hprod :
                  z.1.1 * J.conj z.1.1 = 0 := by
                calc
                  z.1.1 * J.conj z.1.1 =
                      (z.1.2 + z.1.2) +
                        z.1.1 * J.conj z.1.1 := by
                    rw [hadd_selfE, zero_add]
                  _ = z.1.2 +
                      z.1.1 * J.conj z.1.1 + z.1.2 := by
                    ac_rfl
                  _ = 0 := hc02'.symm
              rcases mul_eq_zero.mp hprod with ha | hconj
              · exact ha
              · apply J.conj.injective
                simpa only [map_zero] using hconj
            · intro ha
              have hM_sq : M ^ 2 = 1 := by
                apply Units.ext
                ext i j
                fin_cases i <;> fin_cases j <;>
                  simp [pow_two, hMval, Matrix.mul_apply,
                    Fin.sum_univ_three, ha, hadd_selfE, hneg_selfE]
              have hmk_sq :
                  (Matrix.ProjGenLinGroup.mk M) ^ 2 = 1 := by
                rw [← map_pow, hM_sq, map_one]
              apply Subtype.ext
              apply Subtype.ext
              change
                ((((coordR z : R) :
                  ProjectiveSpecialUnitaryMatrixGroup J) :
                    Matrix.ProjGenLinGroup (Fin 3) E) ^ 2) = 1
              rw [hcoordM]
              exact hmk_sq
          have hR_square_count :
              Nat.card {x : R // x ^ 2 = 1} = q := by
            let fixedToTorsion :
                {b : E // J.conj b = b} →
                  {x : R // x ^ 2 = 1} :=
              fun b => ⟨coordR ⟨(0, b), by
                change (b : E) + J.conj b + 0 * J.conj 0 = 0
                rw [b.property]
                simp only [map_zero, zero_mul, add_zero]
                rw [← two_mul, htwoE, zero_mul]⟩,
                (hcoord_square_iff _).mpr rfl⟩
            have hfixedToTorsion_injective :
                Function.Injective fixedToTorsion := by
              intro b c hbc
              apply Subtype.ext
              have hcoord_eq :
                  coordR ⟨(0, b), by
                    change (b : E) + J.conj b + 0 * J.conj 0 = 0
                    rw [b.property]
                    simp only [map_zero, zero_mul, add_zero]
                    rw [← two_mul, htwoE, zero_mul]⟩ =
                    coordR ⟨(0, c), by
                      change (c : E) + J.conj c + 0 * J.conj 0 = 0
                      rw [c.property]
                      simp only [map_zero, zero_mul, add_zero]
                      rw [← two_mul, htwoE, zero_mul]⟩ := by
                simpa only [fixedToTorsion] using
                  congrArg (fun x : {x : R // x ^ 2 = 1} => x.1) hbc
              have hz := coordR.injective hcoord_eq
              exact congrArg (fun z : Coord => z.1.2) hz
            have hfixedToTorsion_surjective :
                Function.Surjective fixedToTorsion := by
              intro x
              rcases coordR.surjective x.1 with ⟨z, hz⟩
              have hz_sq : (coordR z) ^ 2 = 1 := by
                rw [hz]
                exact x.property
              have hza : z.1.1 = 0 :=
                (hcoord_square_iff z).mp hz_sq
              have hz_relation :
                  z.1.2 + J.conj z.1.2 = 0 := by
                have hz_property := z.property
                rw [hza] at hz_property
                simpa only [map_zero, zero_mul, add_zero] using hz_property
              have hz_fixed : J.conj z.1.2 = z.1.2 := by
                have hz_neg :
                    z.1.2 = -J.conj z.1.2 :=
                  eq_neg_of_add_eq_zero_left hz_relation
                rw [hneg_selfE] at hz_neg
                exact hz_neg.symm
              refine ⟨⟨z.1.2, hz_fixed⟩, ?_⟩
              apply Subtype.ext
              dsimp only [fixedToTorsion]
              rw [← hz]
              apply congrArg coordR
              apply Subtype.ext
              exact Prod.ext hza.symm rfl
            let eFixed :
                {b : E // J.conj b = b} ≃
                  {x : R // x ^ 2 = 1} :=
              Equiv.ofBijective fixedToTorsion
                ⟨hfixedToTorsion_injective,
                  hfixedToTorsion_surjective⟩
            calc
              Nat.card {x : R // x ^ 2 = 1} =
                  Nat.card {b : E // J.conj b = b} :=
                Nat.card_congr eFixed.symm
              _ = q := hfixedCard
          have hR_is_sylow :
              ∃ Pstd : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
                R = (Pstd : Subgroup
                  (ProjectiveSpecialUnitaryMatrixGroup J)) := by
            obtain ⟨Pstd, hR_le_Pstd⟩ :=
              hR_pgroup.exists_le_sylow
            have hq_sq_even : Even (q ^ 2) :=
              hq_even.pow_of_ne_zero (by norm_num)
            have hq_cube_even : Even (q ^ 3) :=
              hq_even.pow_of_ne_zero (by norm_num)
            have hq_sq_pos : 0 < q ^ 2 :=
              pow_pos (by omega) 2
            have hq_sq_sub_one_odd : Odd (q ^ 2 - 1) :=
              Nat.Even.sub_odd hq_sq_pos hq_sq_even odd_one
            have houter_odd :
                Odd ((q ^ 3 + 1) * (q ^ 2 - 1)) :=
              hq_cube_even.add_one.mul hq_sq_sub_one_odd
            have hq_factor :
                (q + 1) * (q - 1) = q ^ 2 - 1 := by
              have hq_le_sq : q ≤ q * q := by
                nlinarith
              rw [add_mul, one_mul, Nat.mul_sub_left_distrib]
              simp only [mul_one, pow_two]
              omega
            have hden_dvd_qsq_sub :
                Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
              exact dvd_trans (Nat.gcd_dvd_right 3 (q + 1))
                ⟨q - 1, hq_factor.symm⟩
            have hden_dvd_numerator :
                Nat.gcd 3 (q + 1) ∣
                  (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
              dvd_mul_of_dvd_right hden_dvd_qsq_sub
                ((q ^ 3 + 1) * q ^ 3)
            have hgroup_dvd_numerator :
                Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣
                  (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
              rw [hG_card]
              exact Nat.div_dvd_of_dvd hden_dvd_numerator
            obtain ⟨m, hPstd_power⟩ :=
              IsPGroup.iff_card.mp Pstd.isPGroup'
            have hPstd_dvd_group :
                Nat.card Pstd ∣
                  Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) :=
              (Pstd : Subgroup
                (ProjectiveSpecialUnitaryMatrixGroup J)).card_subgroup_dvd_card
            have hPstd_dvd_numerator :
                Nat.card Pstd ∣
                  (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
              dvd_trans hPstd_dvd_group hgroup_dvd_numerator
            have hPstd_dvd_product :
                Nat.card Pstd ∣
                  q ^ 3 * ((q ^ 3 + 1) * (q ^ 2 - 1)) := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using
                hPstd_dvd_numerator
            have hPstd_coprime_outer :
                Nat.Coprime (Nat.card Pstd)
                  ((q ^ 3 + 1) * (q ^ 2 - 1)) := by
              rw [hPstd_power]
              exact Nat.Coprime.pow_left m
                houter_odd.coprime_two_left
            have hPstd_dvd_qcube :
                Nat.card Pstd ∣ q ^ 3 :=
              hPstd_coprime_outer.dvd_of_dvd_mul_right
                hPstd_dvd_product
            have hqcube_dvd_Pstd :
                q ^ 3 ∣ Nat.card Pstd := by
              rw [← hR_card]
              exact Subgroup.card_dvd_of_le hR_le_Pstd
            have hPstd_card : Nat.card Pstd = q ^ 3 :=
              Nat.dvd_antisymm hPstd_dvd_qcube
                hqcube_dvd_Pstd
            refine ⟨Pstd,
              Subgroup.eq_of_le_of_card_ge hR_le_Pstd ?_⟩
            rw [hPstd_card, hR_card]
          rcases hR_is_sylow with ⟨Pstd, rfl⟩
          have hPstd_square_count :
              Nat.card {x : Pstd // x ^ 2 = 1} = q :=
            hR_square_count
          let eQbarStd : Qbar ≃* Pstd :=
            eQbarModel.trans (Sylow.equiv Pmodel Pstd)
          let eIQPstd : IQ ≃ {x : Pstd // x ^ 2 = 1} :=
            { toFun := fun x => ⟨eQbarStd (x : Qbar), by
                have hx_sq := (hIQ_sq_iff (x : Qbar)).mp x.property
                simpa only [map_pow, map_one] using
                  congrArg eQbarStd hx_sq⟩
              invFun := fun x => ⟨eQbarStd.symm (x : Pstd), by
                apply (hIQ_sq_iff _).mpr
                simpa only [map_pow, map_one] using
                  congrArg eQbarStd.symm x.property⟩
              left_inv := fun x => by
                apply Subtype.ext
                exact eQbarStd.symm_apply_apply (x : Qbar)
              right_inv := fun x => by
                apply Subtype.ext
                exact eQbarStd.apply_symm_apply (x : Pstd) }
          calc
            Nat.card IQ = Nat.card {x : Pstd // x ^ 2 = 1} :=
              Nat.card_congr eIQPstd
            _ = q := hPstd_square_count
        exact hPSU_count
    rcases hLQ0_equiv_IQ with ⟨eIQ⟩
    calc
      q = Nat.card IQ := hIQ_card.symm
      _ = Nat.card ↥(L ⊓ Q0) := Nat.card_congr eIQ.symm.toEquiv
  refine ⟨hCQ1, hNLF, q, hq_power, hq_gt, hq_eq_Q0, ?_⟩
  have hQX_map_CX : QX.map L.subtype = CX := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨(⟨x, hx.1⟩ : L), hx.2, rfl⟩
  let eQXCX : QX ≃* CX :=
    (Subgroup.equivMapOfInjective QX L.subtype
      L.subtype_injective).trans (MulEquiv.subgroupCongr hQX_map_CX)
  rcases hQbar_iso with ⟨eQXQbar⟩
  let eCXQbar : CX ≃* Qbar := eQXCX.symm.trans eQXQbar
  rcases hQbar_sylow with ⟨Pbar, hPbar⟩
  have hPbar_le_M : (Pbar : Subgroup (L ⧸ N)) ≤ M := by
    rw [← hPbar]
    exact hQbar_le_M
  let PM : Sylow 2 M := Pbar.subtype hPbar_le_M
  let eQbarPM : Qbar ≃* PM :=
    (MulEquiv.subgroupCongr hPbar).trans
      (Subgroup.subgroupOfEquivOfLe hPbar_le_M).symm
  let eCXPM : CX ≃* PM := eCXQbar.trans eQbarPM
  rcases hmodel with
      ⟨k, hk, hqk, eM, rho, eΩ, hnatural, hequiv⟩ |
      ⟨k, hk, hqk, eM, rho, eΩ, hnatural, hequiv⟩ |
      ⟨E, hEfield, hEfinite, J, hJstandard, hEcard, hfixedCard,
        eM, rho, eΩ, hnatural, hequiv⟩
  · left
    have hFmodel : Nonempty ((F ⧸ Subgroup.center F) ≃*
        PSL2BinaryMatrixGroup k) := by
      rcases hFquotM with ⟨eFM⟩
      exact ⟨eFM.trans eM⟩
    let Pmodel : Sylow 2 (PSL2BinaryMatrixGroup k) :=
      PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
    let eCXModel : CX ≃* Pmodel :=
      eCXPM.trans
        (Subgroup.equivMapOfInjective (PM : Subgroup M)
          eM.toMonoidHom eM.injective)
    have hfield_card : Nat.card (BinaryGaloisField k) = 2 ^ k := by
      simpa [BinaryGaloisField] using GaloisField.card 2 k hk
    rcases External.huppert_II_8_2_a_sylow_equiv_additive
        hfield_card Pmodel with ⟨eAdd⟩
    let eCXAdd : CX ≃* Multiplicative (BinaryGaloisField k) :=
      eCXModel.trans eAdd.symm
    have hst : orderOf (s * t) = 3 := by
      let sbar : L ⧸ N := QuotientGroup.mk sX
      let rbar : L ⧸ N := QuotientGroup.mk rX
      have hsX_mem_QX : sX ∈ QX := by
        change (sX : G) ∈ Q
        rw [hsX_eq_s]
        exact hsec.section2.Q0_le_Q
          ((hsec.section2.Q0_def s).mpr
            (Or.inr ⟨hsec.s_mem_H, hsec.s_involution⟩))
      have hsbar_mem_M : sbar ∈ M := by
        apply hQbar_le_M
        change QuotientGroup.mk sX ∈ QX.map π
        exact ⟨sX, hsX_mem_QX, rfl⟩
      have hrbar_mem_M : rbar ∈ M := by
        apply hQbar_le_M
        change QuotientGroup.mk rX ∈ QX.map π
        exact ⟨rX, hrX_mem, rfl⟩
      have htbar_mem_M : tbar ∈ M := by
        have htbar_pgroup : IsPGroup 2 (Subgroup.zpowers tbar) := by
          refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers tbar)
            (n := 1) ?_
          rw [Nat.card_zpowers,
            (orderOf_eq_prime_iff.mpr
              ⟨hA1bar.involution_t.sq_eq_one,
                hA1bar.involution_t.ne_one⟩), pow_one]
        obtain ⟨P, htbar_le_P⟩ := htbar_pgroup.exists_le_sylow
        apply hresidual_le_M
        rw [twoPrimeResidual]
        exact (le_iSup (fun S : Sylow 2 (L ⧸ N) =>
          (S : Subgroup (L ⧸ N))) P)
            (htbar_le_P (Subgroup.mem_zpowers tbar))
      let sM : M := ⟨sbar, hsbar_mem_M⟩
      let rM : M := ⟨rbar, hrbar_mem_M⟩
      let tM : M := ⟨tbar, htbar_mem_M⟩
      let sm : PSL2BinaryMatrixGroup k := eM sM
      let rm : PSL2BinaryMatrixGroup k := eM rM
      let tm : PSL2BinaryMatrixGroup k := eM tM
      have hsm_mem_P : sm ∈ (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) := by
        have hsM_mem_PM : sM ∈ (PM : Subgroup M) := by
          change sbar ∈ (Pbar : Subgroup (L ⧸ N))
          rw [← hPbar]
          change QuotientGroup.mk sX ∈ QX.map π
          exact ⟨sX, hsX_mem_QX, rfl⟩
        change eM sM ∈ (PM : Subgroup M).map eM.toMonoidHom
        exact ⟨sM, hsM_mem_PM, rfl⟩
      have hrm_mem_P : rm ∈ (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) := by
        have hrM_mem_PM : rM ∈ (PM : Subgroup M) := by
          change rbar ∈ (Pbar : Subgroup (L ⧸ N))
          rw [← hPbar]
          change QuotientGroup.mk rX ∈ QX.map π
          exact ⟨rX, hrX_mem, rfl⟩
        change eM rM ∈ (PM : Subgroup M).map eM.toMonoidHom
        exact ⟨rM, hrM_mem_PM, rfl⟩
      have htm_not_mem_P : tm ∉ (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) := by
        intro htm_mem
        change eM tM ∈ (PM : Subgroup M).map eM.toMonoidHom at htm_mem
        rcases htm_mem with ⟨m, hm, hm_eq⟩
        have hm_tM : m = tM := eM.injective hm_eq
        have htM_mem_PM : tM ∈ (PM : Subgroup M) := hm_tM ▸ hm
        have htbar_mem_Pbar : tbar ∈ (Pbar : Subgroup (L ⧸ N)) := htM_mem_PM
        have htbar_mem_Qbar : tbar ∈ Qbar := by
          rw [hPbar]
          exact htbar_mem_Pbar
        exact hA1bar.t_not_mem_H (hA1bar.Q_le_H htbar_mem_Qbar)
      have hPmodel_sq : ∀ y : Pmodel, y ^ 2 = 1 := by
        intro y
        rcases eAdd.surjective y with ⟨a, rfl⟩
        calc
          eAdd a ^ 2 = eAdd (a ^ 2) := (map_pow eAdd a 2).symm
          _ = eAdd 1 := by
            congr 1
            rw [pow_two]
            change a.toAdd + a.toAdd = 0
            have htwo : (2 : BinaryGaloisField k) = 0 :=
              CharP.cast_eq_zero (BinaryGaloisField k) 2
            rw [← two_mul, htwo, zero_mul]
          _ = 1 := map_one eAdd
      have hsm_involution : IsInvolution sm := by
        constructor
        · intro hsm_one
          have hsM_one : sM = 1 := by
            apply eM.injective
            simpa [sm] using hsm_one
          have hsbar_one : sbar = 1 := congrArg Subtype.val hsM_one
          have hsX_mem_N : sX ∈ N := by
            apply (QuotientGroup.eq_one_iff (N := N) sX).mp
            simpa [sbar] using hsbar_one
          have hsX_mem_DX : sX ∈ DX := by
            change (sX : G) ∈ D
            have hsX_core :
                sX ∈ pointStabilizerCore L ΩX := by
              simpa [N] using hsX_mem_N
            exact ((hcore_mem sX).mp hsX_core).1.2
          have hsX_one : sX = 1 := by
            have hsX_bot : sX ∈ (⊥ : Subgroup L) := by
              apply hA1X.Q_disjoint_D.le_bot
              exact ⟨hsX_mem_QX, hsX_mem_DX⟩
            simpa using hsX_bot
          exact hsX_involution.ne_one hsX_one
        · have hsm_sq := hPmodel_sq ⟨sm, hsm_mem_P⟩
          simpa [pow_two] using congrArg Subtype.val hsm_sq
      have hrm_sq : rm * rm = 1 := by
        have hrm_pow := hPmodel_sq ⟨rm, hrm_mem_P⟩
        simpa [pow_two] using congrArg Subtype.val hrm_pow
      have htm_involution : IsInvolution tm := by
        constructor
        · intro htm_one
          have htM_one : tM = 1 := by
            apply eM.injective
            simpa [tm] using htm_one
          exact hA1bar.involution_t.ne_one (congrArg Subtype.val htM_one)
        · have htM_sq : tM ^ 2 = 1 := by
            apply Subtype.ext
            change tbar ^ 2 = 1
            exact hπ_sq_eq_one tX hA1X.involution_t.sq_eq_one
          calc
            tm ^ 2 = eM (tM ^ 2) := (map_pow eM tM 2).symm
            _ = eM 1 := congrArg eM htM_sq
            _ = 1 := map_one eM
      have hmodel_structure :
          tm * sm * tm = rm⁻¹ * tm * rm := by
        set_option backward.isDefEq.respectTransparency false in
        exact (by
          have hbar_structure :
              tbar * sbar * tbar = rbar⁻¹ * tbar * rbar := by
            simpa [π, tbar, sbar, rbar] using congrArg π hstructureX
          have hM_structure :
              tM * sM * tM = rM⁻¹ * tM * rM := by
            apply Subtype.ext
            simpa [tM, sM, rM] using hbar_structure
          simpa [tm, sm, rm] using congrArg eM hM_structure)
      have hSylow_eq_of_common :
          ∀ (P₁ P₂ : Sylow 2 (PSL2BinaryMatrixGroup k))
            (x : PSL2BinaryMatrixGroup k),
            x ≠ 1 →
              x ∈ (P₁ : Subgroup (PSL2BinaryMatrixGroup k)) →
                x ∈ (P₂ : Subgroup (PSL2BinaryMatrixGroup k)) → P₁ = P₂ := by
        rcases External.huppert_II_8_5_a_psl2_partition
            hfield_card Pmodel with
          ⟨U, S, _hU_cyclic, _hU_card, _hS_cyclic, _hS_card, hpartition⟩
        intro P₁ P₂ x hx_ne hxP₁ hxP₂
        obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq
          (α := Sylow 2 (PSL2BinaryMatrixGroup k))
          (PSL2BinaryMatrixGroup k) Pmodel P₁
        obtain ⟨g₂, hg₂⟩ := MulAction.exists_smul_eq
          (α := Sylow 2 (PSL2BinaryMatrixGroup k))
          (PSL2BinaryMatrixGroup k) Pmodel P₂
        have hP₁_family :
            ∃ g, (P₁ : Subgroup (PSL2BinaryMatrixGroup k)) =
              (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)).map
                (MulAut.conj g).toMonoidHom := by
          refine ⟨g₁, ?_⟩
          calc
            (P₁ : Subgroup (PSL2BinaryMatrixGroup k)) =
                (g₁ • Pmodel : Sylow 2 (PSL2BinaryMatrixGroup k)) :=
              (congrArg
                (fun R : Sylow 2 (PSL2BinaryMatrixGroup k) =>
                  (R : Subgroup (PSL2BinaryMatrixGroup k))) hg₁).symm
            _ = MulAut.conj g₁ •
                (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) :=
              Sylow.coe_subgroup_smul
            _ = (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)).map
                (MulAut.conj g₁).toMonoidHom :=
              Subgroup.pointwise_smul_def _
        have hP₂_family :
            ∃ g, (P₂ : Subgroup (PSL2BinaryMatrixGroup k)) =
              (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)).map
                (MulAut.conj g).toMonoidHom := by
          refine ⟨g₂, ?_⟩
          calc
            (P₂ : Subgroup (PSL2BinaryMatrixGroup k)) =
                (g₂ • Pmodel : Sylow 2 (PSL2BinaryMatrixGroup k)) :=
              (congrArg
                (fun R : Sylow 2 (PSL2BinaryMatrixGroup k) =>
                  (R : Subgroup (PSL2BinaryMatrixGroup k))) hg₂).symm
            _ = MulAut.conj g₂ •
                (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) :=
              Sylow.coe_subgroup_smul
            _ = (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)).map
                (MulAut.conj g₂).toMonoidHom :=
              Subgroup.pointwise_smul_def _
        rcases hpartition x hx_ne with ⟨T, _hT, hT_unique⟩
        have hP₁_eq : (P₁ : Subgroup (PSL2BinaryMatrixGroup k)) = T :=
          hT_unique _ ⟨hxP₁, Or.inl hP₁_family⟩
        have hP₂_eq : (P₂ : Subgroup (PSL2BinaryMatrixGroup k)) = T :=
          hT_unique _ ⟨hxP₂, Or.inl hP₂_family⟩
        apply Sylow.ext
        exact hP₁_eq.trans hP₂_eq.symm
      have hrm_eq_sm : rm = sm := by
        have htm_pgroup : IsPGroup 2 (Subgroup.zpowers tm) := by
          refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers tm)
            (n := 1) ?_
          rw [Nat.card_zpowers,
            (orderOf_eq_prime_iff.mpr
              ⟨htm_involution.sq_eq_one, htm_involution.ne_one⟩), pow_one]
        obtain ⟨Tmodel, htm_le_T⟩ := htm_pgroup.exists_le_sylow
        have htm_mem_T : tm ∈ (Tmodel : Subgroup (PSL2BinaryMatrixGroup k)) := by
          exact htm_le_T (Subgroup.mem_zpowers tm)
        have hcommon_sylow : tm • Pmodel = rm • Tmodel := by
          have htm_mul : tm * tm = 1 := by
            simpa [pow_two] using htm_involution.sq_eq_one
          have htm_inv : tm⁻¹ = tm := htm_involution.inv_eq_self
          have hrm_inv : rm⁻¹ = rm := inv_eq_of_mul_eq_one_right hrm_sq
          let x : PSL2BinaryMatrixGroup k := tm * sm * tm
          apply hSylow_eq_of_common (tm • Pmodel) (rm • Tmodel) x
          · intro hx_one
            apply hsm_involution.ne_one
            have hx_conj := congrArg (fun z => tm * z * tm) hx_one
            calc
              sm = (tm * tm) * sm * (tm * tm) := by rw [htm_mul]; simp
              _ = tm * (tm * sm * tm) * tm := by group
              _ = tm * 1 * tm := by simpa [x] using hx_conj
              _ = 1 := by simpa using htm_mul
          · rw [Sylow.coe_subgroup_smul]
            exact Set.mem_smul_set.mpr ⟨sm, hsm_mem_P, by
              simp [x, MulAut.conj_apply, htm_inv]⟩
          · rw [Sylow.coe_subgroup_smul]
            exact Set.mem_smul_set.mpr ⟨tm, htm_mem_T, by
              simpa [x, MulAut.conj_apply, hrm_inv] using hmodel_structure.symm⟩
        have hT_comm :
            ∀ x y : Tmodel, x * y = y * x := by
          rcases External.huppert_II_8_2_a_sylow_equiv_additive
              hfield_card Tmodel with ⟨eT⟩
          intro x y
          apply eT.symm.injective
          simpa only [map_mul] using mul_comm (eT.symm x) (eT.symm y)
        let a : PSL2BinaryMatrixGroup k := sm * rm
        have ha_mem_P : a ∈ (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) := by
          exact (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)).mul_mem
            hsm_mem_P hrm_mem_P
        have ha_sq : a * a = 1 := by
          have hsm_rm_comm : sm * rm = rm * sm := by
            let smP : Pmodel := ⟨sm, hsm_mem_P⟩
            let rmP : Pmodel := ⟨rm, hrm_mem_P⟩
            have hcommP : smP * rmP = rmP * smP := by
              apply eAdd.symm.injective
              simpa only [map_mul] using mul_comm (eAdd.symm smP) (eAdd.symm rmP)
            exact congrArg Subtype.val hcommP
          have hsm_mul : sm * sm = 1 := by
            simpa [pow_two] using hsm_involution.sq_eq_one
          change (sm * rm) * (sm * rm) = 1
          calc
            (sm * rm) * (sm * rm) = sm * (rm * sm) * rm := by group
            _ = sm * (sm * rm) * rm := by rw [← hsm_rm_comm]
            _ = (sm * sm) * (rm * rm) := by group
            _ = 1 := by rw [hsm_mul, hrm_sq]; simp
        have ha_comm_tm : a * tm = tm * a := by
          have htm_mul : tm * tm = 1 := by
            simpa [pow_two] using htm_involution.sq_eq_one
          have htm_inv : tm⁻¹ = tm := htm_involution.inv_eq_self
          have hrm_inv : rm⁻¹ = rm := inv_eq_of_mul_eq_one_right hrm_sq
          have hconj_eq : rm * tm * rm = tm * sm * tm := by
            simpa [hrm_inv] using hmodel_structure.symm
          have hT_eq : (rm * tm) • Pmodel = Tmodel := by
            calc
              (rm * tm) • Pmodel = rm • (tm • Pmodel) := mul_smul _ _ _
              _ = rm • (rm • Tmodel) := congrArg
                (fun R : Sylow 2 (PSL2BinaryMatrixGroup k) => rm • R)
                hcommon_sylow
              _ = (rm * rm) • Tmodel := (mul_smul _ _ _).symm
              _ = Tmodel := by rw [hrm_sq]; simp
          let y : PSL2BinaryMatrixGroup k := (rm * tm) * rm * (rm * tm)⁻¹
          have hy_mem_T : y ∈ (Tmodel : Subgroup (PSL2BinaryMatrixGroup k)) := by
            rw [← hT_eq, Sylow.coe_subgroup_smul]
            exact Set.mem_smul_set.mpr ⟨rm, hrm_mem_P, rfl⟩
          have hy_eq : y = tm * a := by
            dsimp [y, a]
            rw [mul_inv_rev, htm_inv, hrm_inv]
            calc
              (rm * tm) * rm * (tm * rm) = (rm * tm * rm) * tm * rm := by group
              _ = (tm * sm * tm) * tm * rm := by rw [hconj_eq]
              _ = tm * sm * (tm * tm) * rm := by group
              _ = tm * (sm * rm) := by rw [htm_mul]; group
          have hy_comm : y * tm = tm * y := by
            exact congrArg Subtype.val
              (hT_comm ⟨y, hy_mem_T⟩ ⟨tm, htm_mem_T⟩)
          have hy_comm_left := congrArg (fun z => tm * z) hy_comm
          simpa [hy_eq, htm_mul, mul_assoc] using hy_comm_left
        have ha_mem_T : a ∈ (Tmodel : Subgroup (PSL2BinaryMatrixGroup k)) := by
          have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha_sq
          have htm_mem_aT :
              tm ∈ ((a • Tmodel : Sylow 2 (PSL2BinaryMatrixGroup k)) :
                Subgroup (PSL2BinaryMatrixGroup k)) := by
            rw [Sylow.coe_subgroup_smul]
            exact Set.mem_smul_set.mpr ⟨tm, htm_mem_T, by
              simp [MulAut.conj_apply, ha_inv, ha_comm_tm, ha_sq, mul_assoc]⟩
          have ha_smul_T : a • Tmodel = Tmodel :=
            hSylow_eq_of_common (a • Tmodel) Tmodel tm
              htm_involution.ne_one htm_mem_aT htm_mem_T
          have ha_normalizer :
              a ∈ Subgroup.normalizer (Tmodel : Subgroup (PSL2BinaryMatrixGroup k)) :=
            Sylow.smul_eq_iff_mem_normalizer.mp ha_smul_T
          have ha_inf_normalizer :
              a ∈ (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) ⊓
                Subgroup.normalizer (Tmodel : Subgroup (PSL2BinaryMatrixGroup k)) :=
            ⟨ha_mem_P, ha_normalizer⟩
          have hinf := Pmodel.isPGroup'.inf_normalizer_sylow Tmodel
          have ha_inf_T :
              a ∈ (Pmodel : Subgroup (PSL2BinaryMatrixGroup k)) ⊓
                (Tmodel : Subgroup (PSL2BinaryMatrixGroup k)) :=
            hinf ▸ ha_inf_normalizer
          exact ha_inf_T.2
        have ha_one : a = 1 := by
          by_contra ha_ne
          have hPT := hSylow_eq_of_common Pmodel Tmodel a ha_ne ha_mem_P ha_mem_T
          apply htm_not_mem_P
          rw [hPT]
          exact htm_mem_T
        have hsm_sq : sm * sm = 1 := by
          simpa [pow_two] using hsm_involution.sq_eq_one
        calc
          rm = (sm * sm) * rm := by rw [hsm_sq]; simp
          _ = sm * (sm * rm) := by group
          _ = sm := by change sm * a = sm; rw [ha_one]; simp
      have hmodel_braid :
          tm * sm * tm = sm * tm * sm := by
        calc
          tm * sm * tm = rm⁻¹ * tm * rm := hmodel_structure
          _ = sm⁻¹ * tm * sm := by rw [hrm_eq_sm]
          _ = sm * tm * sm := by rw [hsm_involution.inv_eq_self]
      have hbar_braid :
          tbar * sbar * tbar = sbar * tbar * sbar := by
        set_option backward.isDefEq.respectTransparency false in
        exact (by
          have hM_braid : tM * sM * tM = sM * tM * sM := by
            have hEm :
                eM (tM * sM * tM) = eM (sM * tM * sM) := by
              calc
                eM (tM * sM * tM) = eM (tM * sM) * eM tM :=
                  map_mul eM (tM * sM) tM
                _ = (eM tM * eM sM) * eM tM :=
                  congrArg (fun z => z * eM tM) (map_mul eM tM sM)
                _ = tm * sm * tm := rfl
                _ = sm * tm * sm := hmodel_braid
                _ = (eM sM * eM tM) * eM sM := rfl
                _ = eM (sM * tM) * eM sM :=
                  congrArg (fun z => z * eM sM) (map_mul eM sM tM).symm
                _ = eM (sM * tM * sM) :=
                  (map_mul eM (sM * tM) sM).symm
            exact eM.injective hEm
          exact congrArg Subtype.val hM_braid)
      have hsbar_sq : sbar * sbar = 1 := by
        rw [← pow_two]
        exact hπ_sq_eq_one sX hsX_involution.sq_eq_one
      have htbar_sq : tbar * tbar = 1 := by
        rw [← pow_two]
        exact hπ_sq_eq_one tX hA1X.involution_t.sq_eq_one
      have hbar_pow : (sbar * tbar) ^ 3 = 1 := by
        rw [pow_three]
        calc
          sbar * tbar * (sbar * tbar * (sbar * tbar)) =
              sbar * (tbar * sbar * tbar) * sbar * tbar := by group
          _ = sbar * (sbar * tbar * sbar) * sbar * tbar := by
            rw [hbar_braid]
          _ = (sbar * sbar) * tbar * (sbar * sbar) * tbar := by group
          _ = 1 := by rw [hsbar_sq]; simpa using htbar_sq
      have hsbar_mem_Hbar : sbar ∈ Hbar := by
        change QuotientGroup.mk sX ∈ HX.map π
        exact ⟨sX, hsX_mem, rfl⟩
      have hbar_ne : sbar * tbar ≠ 1 := by
        intro hprod
        have hst_eq : sbar = tbar := by
          have hright := congrArg (fun z => z * tbar) hprod
          simpa [mul_assoc, htbar_sq] using hright
        have htbar_mem_Hbar : tbar ∈ Hbar := hst_eq ▸ hsbar_mem_Hbar
        exact hA1bar.t_not_mem_H (by simpa only [tbar] using htbar_mem_Hbar)
      have hbar_order : orderOf (sbar * tbar) = 3 :=
        orderOf_eq_prime_iff.mpr ⟨hbar_pow, hbar_ne⟩
      have hquotient_order :
          orderOf (QuotientGroup.mk (sX * tX) : L ⧸ N) = 3 := by
        simpa [sbar, tbar] using hbar_order
      have hcoe_prod : ((sX * tX : L) : G) = s * t := by
        simp [hsX_eq_s, tX]
      calc
        orderOf (s * t) = orderOf ((sX * tX : L) : G) :=
          congrArg orderOf hcoe_prod.symm
        _ = orderOf (sX * tX) := Subgroup.orderOf_coe (sX * tX)
        _ = orderOf (QuotientGroup.mk (sX * tX) : L ⧸ N) :=
          horder_quotient.symm
        _ = 3 := hquotient_order
    have hCX_elementary : IsElementaryAbelian 2 CX := by
      refine
        { toIsMulCommutative := ?_
          exponent_dvd_p := ?_ }
      · refine { is_comm := ⟨?_⟩ }
        intro x y
        apply eCXAdd.injective
        simpa only [map_mul] using mul_comm (eCXAdd x) (eCXAdd y)
      · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
        intro x
        apply eCXAdd.injective
        simp only [map_pow, map_one]
        rw [pow_two]
        change (eCXAdd x).toAdd + (eCXAdd x).toAdd = 0
        have htwo : (2 : BinaryGaloisField k) = 0 :=
          CharP.cast_eq_zero (BinaryGaloisField k) 2
        rw [← two_mul, htwo, zero_mul]
    have hCX_card : Nat.card CX = q := by
      calc
        Nat.card CX = Nat.card Pmodel := Nat.card_congr eCXModel.toEquiv
        _ = Nat.card (Multiplicative (BinaryGaloisField k)) :=
          Nat.card_congr eAdd.symm.toEquiv
        _ = 2 ^ k := hfield_card
        _ = q := hqk.symm
    exact ⟨k, hk, hqk, hFmodel, hst, hCX_elementary, hCX_card⟩
  · right
    left
    have hFmodel : Nonempty ((F ⧸ Subgroup.center F) ≃*
        SuzukiMatrixGroup k) := by
      rcases hFquotM with ⟨eFM⟩
      exact ⟨eFM.trans eM⟩
    let Pmodel : Sylow 2 (SuzukiMatrixGroup k) :=
      PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
    let eCXModel : CX ≃* Pmodel :=
      eCXPM.trans
        (Subgroup.equivMapOfInjective (PM : Subgroup M)
          eM.toMonoidHom eM.injective)
    rcases hSuzuki_standard_sylow_typeA k hk hqk with
      ⟨Pstd, hPstd_typeA, hPstd_card, hPstd_root_mem,
        hPstd_root_iff⟩
    let eCXStd : CX ≃* Pstd :=
      eCXModel.trans (Sylow.equiv Pmodel Pstd)
    have hst : orderOf (s * t) = 5 := by
      let sbar : L ⧸ N := QuotientGroup.mk sX
      let rbar : L ⧸ N := QuotientGroup.mk rX
      have hsX_mem_QX : sX ∈ QX := by
        change (sX : G) ∈ Q
        rw [hsX_eq_s]
        exact hsec.section2.Q0_le_Q
          ((hsec.section2.Q0_def s).mpr
            (Or.inr ⟨hsec.s_mem_H, hsec.s_involution⟩))
      have hsbar_mem_M : sbar ∈ M := by
        apply hQbar_le_M
        change QuotientGroup.mk sX ∈ QX.map π
        exact ⟨sX, hsX_mem_QX, rfl⟩
      have hrbar_mem_M : rbar ∈ M := by
        apply hQbar_le_M
        change QuotientGroup.mk rX ∈ QX.map π
        exact ⟨rX, hrX_mem, rfl⟩
      have htbar_mem_M : tbar ∈ M := by
        have htbar_pgroup : IsPGroup 2 (Subgroup.zpowers tbar) := by
          refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers tbar)
            (n := 1) ?_
          rw [Nat.card_zpowers,
            (orderOf_eq_prime_iff.mpr
              ⟨hA1bar.involution_t.sq_eq_one,
                hA1bar.involution_t.ne_one⟩), pow_one]
        obtain ⟨P, htbar_le_P⟩ := htbar_pgroup.exists_le_sylow
        apply hresidual_le_M
        rw [twoPrimeResidual]
        exact (le_iSup (fun S : Sylow 2 (L ⧸ N) =>
          (S : Subgroup (L ⧸ N))) P)
            (htbar_le_P (Subgroup.mem_zpowers tbar))
      let sM : M := ⟨sbar, hsbar_mem_M⟩
      let rM : M := ⟨rbar, hrbar_mem_M⟩
      let tM : M := ⟨tbar, htbar_mem_M⟩
      let sm : SuzukiMatrixGroup k := eM sM
      let rm : SuzukiMatrixGroup k := eM rM
      let tm : SuzukiMatrixGroup k := eM tM
      let j : SuzukiMatrixGroup k :=
        ⟨SuzukiRootGL k 0 1, by
          have hj_gen :
              SuzukiRootGL k 0 1 ∈ SuzukiMatrixGeneratorSet k := by
            rw [SuzukiMatrixGeneratorSet]
            exact Or.inl ⟨0, 1, rfl⟩
          change SuzukiRootGL k 0 1 ∈
            (Subgroup.closure (SuzukiMatrixGeneratorSet k) :
              Set (GL (Fin 4) (BinaryGaloisField (2 * k + 1))))
          exact Subgroup.subset_closure hj_gen⟩
      let g : SuzukiMatrixGroup k :=
        ⟨SuzukiRootGL k 1 0, by
          have hg_gen :
              SuzukiRootGL k 1 0 ∈ SuzukiMatrixGeneratorSet k := by
            rw [SuzukiMatrixGeneratorSet]
            exact Or.inl ⟨1, 0, rfl⟩
          change SuzukiRootGL k 1 0 ∈
            (Subgroup.closure (SuzukiMatrixGeneratorSet k) :
              Set (GL (Fin 4) (BinaryGaloisField (2 * k + 1))))
          exact Subgroup.subset_closure hg_gen⟩
      let T : SuzukiMatrixGroup k :=
        ⟨SuzukiWeylGL k, by
          have hT_gen :
              SuzukiWeylGL k ∈ SuzukiMatrixGeneratorSet k := by
            rw [SuzukiMatrixGeneratorSet]
            exact Or.inr (Or.inr rfl)
          change SuzukiWeylGL k ∈
            (Subgroup.closure (SuzukiMatrixGeneratorSet k) :
              Set (GL (Fin 4) (BinaryGaloisField (2 * k + 1))))
          exact Subgroup.subset_closure hT_gen⟩
      have hsm_mem_P : sm ∈ (Pmodel : Subgroup (SuzukiMatrixGroup k)) := by
        have hsM_mem_PM : sM ∈ (PM : Subgroup M) := by
          change sbar ∈ (Pbar : Subgroup (L ⧸ N))
          rw [← hPbar]
          change QuotientGroup.mk sX ∈ QX.map π
          exact ⟨sX, hsX_mem_QX, rfl⟩
        change eM sM ∈ (PM : Subgroup M).map eM.toMonoidHom
        exact ⟨sM, hsM_mem_PM, rfl⟩
      have hrm_mem_P : rm ∈ (Pmodel : Subgroup (SuzukiMatrixGroup k)) := by
        have hrM_mem_PM : rM ∈ (PM : Subgroup M) := by
          change rbar ∈ (Pbar : Subgroup (L ⧸ N))
          rw [← hPbar]
          change QuotientGroup.mk rX ∈ QX.map π
          exact ⟨rX, hrX_mem, rfl⟩
        change eM rM ∈ (PM : Subgroup M).map eM.toMonoidHom
        exact ⟨rM, hrM_mem_PM, rfl⟩
      have htm_not_mem_P : tm ∉ (Pmodel : Subgroup (SuzukiMatrixGroup k)) := by
        intro htm_mem
        change eM tM ∈ (PM : Subgroup M).map eM.toMonoidHom at htm_mem
        rcases htm_mem with ⟨m, hm, hm_eq⟩
        have hm_tM : m = tM := eM.injective hm_eq
        have htM_mem_PM : tM ∈ (PM : Subgroup M) := hm_tM ▸ hm
        have htbar_mem_Pbar : tbar ∈ (Pbar : Subgroup (L ⧸ N)) := htM_mem_PM
        have htbar_mem_Qbar : tbar ∈ Qbar := by
          rw [hPbar]
          exact htbar_mem_Pbar
        exact hA1bar.t_not_mem_H (hA1bar.Q_le_H htbar_mem_Qbar)
      have hsm_sq : sm * sm = 1 := by
        have hsM_sq : sM ^ 2 = 1 := by
          apply Subtype.ext
          change sbar ^ 2 = 1
          exact hπ_sq_eq_one sX hsX_involution.sq_eq_one
        calc
          sm * sm = sm ^ 2 := by simp [pow_two]
          _ = eM (sM ^ 2) := (map_pow eM sM 2).symm
          _ = eM 1 := congrArg eM hsM_sq
          _ = 1 := map_one eM
      have htm_sq : tm * tm = 1 := by
        have htM_sq : tM ^ 2 = 1 := by
          apply Subtype.ext
          change tbar ^ 2 = 1
          exact hπ_sq_eq_one tX hA1X.involution_t.sq_eq_one
        calc
          tm * tm = tm ^ 2 := by simp [pow_two]
          _ = eM (tM ^ 2) := (map_pow eM tM 2).symm
          _ = eM 1 := congrArg eM htM_sq
          _ = 1 := map_one eM
      have hmodel_structure :
          tm * sm * tm = rm⁻¹ * tm * rm := by
        have hbar_structure :
            tbar * sbar * tbar = rbar⁻¹ * tbar * rbar := by
          simpa [π, tbar, sbar, rbar] using congrArg π hstructureX
        have hM_structure :
            tM * sM * tM = rM⁻¹ * tM * rM := by
          apply Subtype.ext
          simpa [tM, sM, rM] using hbar_structure
        simpa [tm, sm, rm] using congrArg eM hM_structure
      have hmodel_order : orderOf (sm * tm) = 5 := by
        have hstandard_suzuki_pair_order_source :
            orderOf (j * T) = 5 := by
          haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
          have hchar : (1 + 1 : BinaryGaloisField (2 * k + 1)) = 0 :=
            CharTwo.add_self_eq_zero 1
          apply orderOf_eq_prime_iff.mpr
          constructor
          · apply Subtype.ext
            change
              (SuzukiRootGL k 0 1 * SuzukiWeylGL k) ^ 5 =
                (1 : GL (Fin 4) (BinaryGaloisField (2 * k + 1)))
            ext i l
            fin_cases i <;> fin_cases l <;>
              simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
                SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four,
                pow_succ, hchar]
          · intro hpair_one
            have hGL : SuzukiRootGL k 0 1 * SuzukiWeylGL k =
                (1 : GL (Fin 4) (BinaryGaloisField (2 * k + 1))) := by
              simpa [j, T] using congrArg Subtype.val hpair_one
            have h03 :
                (SuzukiRootGL k 0 1 * SuzukiWeylGL k :
                    GL (Fin 4) (BinaryGaloisField (2 * k + 1))).val 0 3 =
                  ((1 : GL (Fin 4) (BinaryGaloisField (2 * k + 1))).val 0 3) := by
              exact congrFun (congrFun (congrArg
                (fun A : GL (Fin 4) (BinaryGaloisField (2 * k + 1)) => A.val)
                hGL) (0 : Fin 4)) (3 : Fin 4)
            have h10 : (1 : BinaryGaloisField (2 * k + 1)) = 0 := by
              simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
                SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] at h03
            exact one_ne_zero h10
        have hstandard_suzuki_pair_pow : (j * T) ^ 5 = 1 := by
          have hpow := pow_orderOf_eq_one (j * T)
          simpa [hstandard_suzuki_pair_order_source] using hpow
        have hdistinguished_suzuki_pow_transport_source :
            (sm * tm) ^ 5 = (j * T) ^ 5 := by
          have hrm_sq_eq_sm_source : rm * rm = sm := by
            have htm_involution : IsInvolution tm := by
              constructor
              · intro htm_one
                apply htm_not_mem_P
                rw [htm_one]
                exact (Pmodel : Subgroup (SuzukiMatrixGroup k)).one_mem
              · simpa [pow_two] using htm_sq
            obtain ⟨c, hcP, hctm_val⟩ :=
              suzuki_exists_simultaneous_standardizer k
                (Nat.pos_of_ne_zero hk) Pmodel Pstd hPstd_root_iff
                tm htm_involution htm_not_mem_P
            have hctm : c * tm * c⁻¹ = T := by
              apply Subtype.ext
              exact hctm_val
            have htm_eq : tm = c⁻¹ * T * c := by
              calc
                tm = c⁻¹ * (c * tm * c⁻¹) * c := by group
                _ = c⁻¹ * T * c := by rw [hctm]
            have hstandard_structure : T * j * T = g⁻¹ * T * g := by
              apply Subtype.ext
              exact (External.huppert_blackburn_XI_example_10_7_b
                k (Nat.pos_of_ne_zero hk)).1
            have hg_sq_j : g * g = j := by
              apply Subtype.ext
              simpa [pow_two] using
                (External.huppert_blackburn_XI_example_10_7_b
                  k (Nat.pos_of_ne_zero hk)).2
            have hj_mem_Pstd :
                j ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) := by
              apply (hPstd_root_iff j).2
              change SuzukiRootGL k 0 1 ∈
                Subgroup.closure
                  {A | ∃ a b : BinaryGaloisField (2 * k + 1),
                    A = SuzukiRootGL k a b}
              exact Subgroup.subset_closure ⟨0, 1, rfl⟩
            have hg_mem_Pstd :
                g ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) := by
              apply (hPstd_root_iff g).2
              change SuzukiRootGL k 1 0 ∈
                Subgroup.closure
                  {A | ∃ a b : BinaryGaloisField (2 * k + 1),
                    A = SuzukiRootGL k a b}
              exact Subgroup.subset_closure ⟨1, 0, rfl⟩
            have hback_mem :
                ∀ x : SuzukiMatrixGroup k,
                  x ∈ (Pstd : Subgroup (SuzukiMatrixGroup k)) →
                    c⁻¹ * x * c ∈
                      (Pmodel : Subgroup (SuzukiMatrixGroup k)) := by
              intro x hx
              have hx_smul :
                  x ∈ ((c • Pmodel : Sylow 2 (SuzukiMatrixGroup k)) :
                    Subgroup (SuzukiMatrixGroup k)) := by
                rw [hcP]
                exact hx
              rw [Sylow.coe_subgroup_smul] at hx_smul
              rcases Set.mem_smul_set.mp hx_smul with ⟨y, hy, hxy⟩
              have hxy' : c * y * c⁻¹ = x := by
                simpa [MulAut.conj_apply] using hxy
              have hback : c⁻¹ * x * c = y := by
                rw [← hxy']
                group
              rw [hback]
              change y ∈ (Pmodel : Set (SuzukiMatrixGroup k))
              exact hy
            have hj_back : c⁻¹ * j * c ∈
                (Pmodel : Subgroup (SuzukiMatrixGroup k)) :=
              hback_mem j hj_mem_Pstd
            have hg_back : c⁻¹ * g * c ∈
                (Pmodel : Subgroup (SuzukiMatrixGroup k)) :=
              hback_mem g hg_mem_Pstd
            let cM : M := eM.symm c
            let jM : M := eM.symm j
            let gM : M := eM.symm g
            let sjM : M := cM⁻¹ * jM * cM
            let rjM : M := cM⁻¹ * gM * cM
            let sjbar : L ⧸ N := (sjM : L ⧸ N)
            let rjbar : L ⧸ N := (rjM : L ⧸ N)
            have hsjM_mem_PM : sjM ∈ (PM : Subgroup M) := by
              change c⁻¹ * j * c ∈
                (PM : Subgroup M).map eM.toMonoidHom at hj_back
              rcases hj_back with ⟨z, hz, hz_eq⟩
              have hz_eq_sjM : z = sjM := by
                apply eM.injective
                calc
                  eM z = c⁻¹ * j * c := hz_eq
                  _ = eM sjM := by simp [sjM, cM, jM]
              change sjM ∈ (PM : Set M)
              rw [← hz_eq_sjM]
              change z ∈ (PM : Set M) at hz
              exact hz
            have hrjM_mem_PM : rjM ∈ (PM : Subgroup M) := by
              change c⁻¹ * g * c ∈
                (PM : Subgroup M).map eM.toMonoidHom at hg_back
              rcases hg_back with ⟨z, hz, hz_eq⟩
              have hz_eq_rjM : z = rjM := by
                apply eM.injective
                calc
                  eM z = c⁻¹ * g * c := hz_eq
                  _ = eM rjM := by simp [rjM, cM, gM]
              change rjM ∈ (PM : Set M)
              rw [← hz_eq_rjM]
              change z ∈ (PM : Set M) at hz
              exact hz
            have hsjbar_mem_Qbar : sjbar ∈ Qbar := by
              rw [hPbar]
              change (sjM : L ⧸ N) ∈
                (Pbar : Subgroup (L ⧸ N))
              exact hsjM_mem_PM
            have hrjbar_mem_Qbar : rjbar ∈ Qbar := by
              rw [hPbar]
              change (rjM : L ⧸ N) ∈
                (Pbar : Subgroup (L ⧸ N))
              exact hrjM_mem_PM
            have hj_sq : j * j = 1 := by
              apply Subtype.ext
              ext i l
              fin_cases i <;> fin_cases l <;>
                simp [j, SuzukiRootGL, SuzukiRootMatrix,
                  Matrix.mul_apply, Fin.sum_univ_four,
                  CharTwo.add_self_eq_zero]
            have hj_ne : j ≠ 1 := by
              intro hj_one
              have hval := congrArg Subtype.val hj_one
              have h02 := congrArg
                (fun A : GL (Fin 4) (BinaryGaloisField (2 * k + 1)) =>
                  A.val (0 : Fin 4) (2 : Fin 4)) hval
              simp [j, SuzukiRootGL, SuzukiRootMatrix] at h02
            have hjM_involution : IsInvolution jM := by
              constructor
              · intro hjM_one
                apply hj_ne
                have := congrArg eM hjM_one
                simpa [jM] using this
              · apply eM.injective
                simpa [jM, pow_two] using hj_sq
            have hsjM_involution : IsInvolution sjM := by
              simpa [sjM, rightConjugateElem] using
                isInvolution_rightConjugateElem hjM_involution
            have hsjbar_involution : IsInvolution sjbar := by
              constructor
              · intro hsjbar_one
                apply hsjM_involution.ne_one
                apply Subtype.ext
                simpa [sjbar] using hsjbar_one
              · have hsquare := congrArg
                  (fun z : M => (z : L ⧸ N)) hsjM_involution.sq_eq_one
                simpa [sjbar] using hsquare
            have hstandard_structure_M :
                tM * sjM * tM = rjM⁻¹ * tM * rjM := by
              apply eM.injective
              dsimp [sjM, rjM, cM, jM, gM]
              simp only [map_mul, map_inv, eM.apply_symm_apply]
              change
                tm * (c⁻¹ * j * c) * tm =
                  (c⁻¹ * g * c)⁻¹ * tm * (c⁻¹ * g * c)
              rw [htm_eq]
              calc
                c⁻¹ * T * c * (c⁻¹ * j * c) * (c⁻¹ * T * c) =
                    c⁻¹ * (T * j * T) * c := by group
                _ = c⁻¹ * (g⁻¹ * T * g) * c := by
                  rw [hstandard_structure]
                _ = (c⁻¹ * g * c)⁻¹ *
                    (c⁻¹ * T * c) * (c⁻¹ * g * c) := by group
            have hstandard_structure_bar :
                tbar * sjbar * tbar =
                  rjbar⁻¹ * tbar * rjbar := by
              exact congrArg (fun z : M => (z : L ⧸ N))
                hstandard_structure_M
            have hsbar_mem_Qbar : sbar ∈ Qbar := by
              change QuotientGroup.mk sX ∈ QX.map π
              exact ⟨sX, hsX_mem_QX, rfl⟩
            have hrbar_mem_Qbar : rbar ∈ Qbar := by
              change QuotientGroup.mk rX ∈ QX.map π
              exact ⟨rX, hrX_mem, rfl⟩
            have hsm_ne : sm ≠ 1 := by
              intro hsm_one
              apply htm_not_mem_P
              have hconj_one : rm⁻¹ * tm * rm = 1 := by
                simpa [hsm_one, htm_sq] using hmodel_structure.symm
              have htm_one : tm = 1 := by
                calc
                  tm = rm * (rm⁻¹ * tm * rm) * rm⁻¹ := by group
                  _ = 1 := by rw [hconj_one]; simp
              rw [htm_one]
              exact (Pmodel : Subgroup (SuzukiMatrixGroup k)).one_mem
            have hsM_involution : IsInvolution sM := by
              constructor
              · intro hsM_one
                apply hsm_ne
                have := congrArg eM hsM_one
                simpa [sm] using this
              · apply eM.injective
                simpa [sm, pow_two] using hsm_sq
            have hsbar_involution : IsInvolution sbar := by
              constructor
              · intro hsbar_one
                apply hsM_involution.ne_one
                apply Subtype.ext
                exact hsbar_one
              · have hsquare := congrArg
                  (fun z : M => (z : L ⧸ N)) hsM_involution.sq_eq_one
                simpa [sbar] using hsquare
            have hcurrent_structure_bar :
                tbar * sbar * tbar = rbar⁻¹ * tbar * rbar := by
              simpa [π, tbar, sbar, rbar] using congrArg π hstructureX
            rcases proposition_4_b Hbar Dbar Qbar tbar hA1bar with
              ⟨pbar, _hpbar, hpbar_unique⟩
            have hcurrent_eq : (sbar, rbar) = pbar :=
              hpbar_unique (sbar, rbar)
                ⟨hA1bar.Q_le_H hsbar_mem_Qbar, hsbar_involution,
                  hrbar_mem_Qbar, hcurrent_structure_bar⟩
            have hstandard_eq : (sjbar, rjbar) = pbar :=
              hpbar_unique (sjbar, rjbar)
                ⟨hA1bar.Q_le_H hsjbar_mem_Qbar, hsjbar_involution,
                  hrjbar_mem_Qbar, hstandard_structure_bar⟩
            have hpairs : (sbar, rbar) = (sjbar, rjbar) :=
              hcurrent_eq.trans hstandard_eq.symm
            have hsM_eq : sM = sjM := by
              apply Subtype.ext
              exact congrArg Prod.fst hpairs
            have hrM_eq : rM = rjM := by
              apply Subtype.ext
              exact congrArg Prod.snd hpairs
            have hsm_back : sm = c⁻¹ * j * c := by
              change eM sM = c⁻¹ * j * c
              rw [hsM_eq]
              simp [sjM, cM, jM]
            have hrm_back : rm = c⁻¹ * g * c := by
              change eM rM = c⁻¹ * g * c
              rw [hrM_eq]
              simp [rjM, cM, gM]
            calc
              rm * rm =
                  (c⁻¹ * g * c) * (c⁻¹ * g * c) := by rw [hrm_back]
              _ = c⁻¹ * (g * g) * c := by group
              _ = c⁻¹ * j * c := by rw [hg_sq_j]
              _ = sm := hsm_back.symm
          have hrel : tm * (rm * rm) * tm = rm⁻¹ * tm * rm := by
            simpa [hrm_sq_eq_sm_source] using hmodel_structure
          have hroot_four : (rm * rm) * (rm * rm) = 1 := by
            simpa [hrm_sq_eq_sm_source] using hsm_sq
          have hpow_source : (sm * tm) ^ 5 = 1 := by
            let a : SuzukiMatrixGroup k := (rm * rm) * tm
            have ha_def : a = (rm * rm) * tm := rfl
            have ha2 : a ^ 2 = rm * tm * rm := by
              calc
                a ^ 2 = (rm * rm) * (tm * (rm * rm) * tm) := by
                  simp [ha_def, pow_two]
                  group
                _ = (rm * rm) * (rm⁻¹ * tm * rm) := by
                  rw [hrel]
                _ = rm * tm * rm := by
                  group
            have ha4 : a ^ 4 = tm * (rm * rm) := by
              calc
                a ^ 4 = (a ^ 2) ^ 2 := by
                  simp [pow_succ]
                  group
                _ = (rm * tm * rm) ^ 2 := by rw [ha2]
                _ = rm * (tm * (rm * rm) * tm) * rm := by
                  simp [pow_two]
                  group
                _ = rm * (rm⁻¹ * tm * rm) * rm := by
                  rw [hrel]
                _ = tm * (rm * rm) := by
                  group
            calc
              (sm * tm) ^ 5 = a ^ 5 := by
                simp [ha_def, ← hrm_sq_eq_sm_source]
              _ = a ^ 4 * a := by
                simp [pow_succ]
              _ = (tm * (rm * rm)) * ((rm * rm) * tm) := by
                rw [ha4, ha_def]
              _ = tm * ((rm * rm) * (rm * rm)) * tm := by
                group
              _ = tm * 1 * tm := by rw [hroot_four]
              _ = 1 := by simpa using htm_sq
          exact hpow_source.trans hstandard_suzuki_pair_pow.symm
        have hdistinguished_suzuki_pow_source :
            (sm * tm) ^ 5 = 1 := by
          calc
            (sm * tm) ^ 5 = (j * T) ^ 5 :=
              hdistinguished_suzuki_pow_transport_source
            _ = 1 := hstandard_suzuki_pair_pow
        have hdistinguished_suzuki_ne_one : sm * tm ≠ 1 := by
          intro hprod
          have htm_eq_sm_inv : tm = sm⁻¹ := by
            calc
              tm = 1 * tm := by simp
              _ = (sm⁻¹ * sm) * tm := by simp
              _ = sm⁻¹ * (sm * tm) := by group
              _ = sm⁻¹ := by rw [hprod]; simp
          have htm_mem_P : tm ∈ (Pmodel : Subgroup (SuzukiMatrixGroup k)) := by
            simpa [htm_eq_sm_inv] using
              (Pmodel : Subgroup (SuzukiMatrixGroup k)).inv_mem hsm_mem_P
          exact htm_not_mem_P htm_mem_P
        haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
        exact orderOf_eq_prime_iff.mpr
          ⟨hdistinguished_suzuki_pow_source, hdistinguished_suzuki_ne_one⟩
      have hbar_order : orderOf (sbar * tbar) = 5 := by
        have hcoe_prod : ((sM * tM : M) : L ⧸ N) = sbar * tbar := rfl
        have hmodel_prod : eM (sM * tM) = sm * tm := by
          simp only [map_mul, sm, tm]
        calc
          orderOf (sbar * tbar) =
              orderOf ((sM * tM : M) : L ⧸ N) :=
            congrArg orderOf hcoe_prod.symm
          _ = orderOf (sM * tM) := Subgroup.orderOf_coe (sM * tM)
          _ = orderOf (eM (sM * tM)) := (eM.orderOf_eq (sM * tM)).symm
          _ = orderOf (sm * tm) := congrArg orderOf hmodel_prod
          _ = 5 := hmodel_order
      have hquotient_order :
          orderOf (QuotientGroup.mk (sX * tX) : L ⧸ N) = 5 := by
        simpa [sbar, tbar] using hbar_order
      have hcoe_prod : ((sX * tX : L) : G) = s * t := by
        simp [hsX_eq_s, tX]
      calc
        orderOf (s * t) = orderOf ((sX * tX : L) : G) :=
          congrArg orderOf hcoe_prod.symm
        _ = orderOf (sX * tX) := Subgroup.orderOf_coe (sX * tX)
        _ = orderOf (QuotientGroup.mk (sX * tX) : L ⧸ N) :=
          horder_quotient.symm
        _ = 5 := hquotient_order
    have hCX_typeA : IsSuzukiTwoTypeA CX := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        rcases hPstd_typeA with
          ⟨n, hn, theta, pairLift, cocycle, htheta_order,
            htheta_nontrivial, hcocycle_add_left, hcocycle_add_right,
            hcocycle_diag, hpair_mem, hpair_one, hpair_surjective,
            hpair_injective, hpair_mul⟩
        let pairLiftCX :
            BinaryGaloisField n → BinaryGaloisField n → G :=
          fun a z =>
            ((eCXStd.symm ⟨pairLift a z, hpair_mem a z⟩ : CX) : G)
        refine ⟨n, hn, theta, pairLiftCX, cocycle, htheta_order,
          htheta_nontrivial, hcocycle_add_left, hcocycle_add_right,
          hcocycle_diag, ?_, ?_, ?_, ?_, ?_⟩
        · intro a z
          exact (eCXStd.symm ⟨pairLift a z, hpair_mem a z⟩).property
        · change
            ((eCXStd.symm ⟨pairLift 0 0, hpair_mem 0 0⟩ : CX) : G) =
              ((1 : CX) : G)
          have hp :
              (⟨pairLift 0 0, hpair_mem 0 0⟩ : Pstd) = 1 :=
            Subtype.ext hpair_one
          have hcx := congrArg eCXStd.symm hp
          rw [map_one] at hcx
          exact congrArg Subtype.val hcx
        · intro x hx
          let xCX : CX := ⟨x, hx⟩
          let y : Pstd := eCXStd xCX
          rcases hpair_surjective (y : SuzukiMatrixGroup k) y.property with
            ⟨a, z, hy⟩
          refine ⟨a, z, ?_⟩
          change
            x = ((eCXStd.symm ⟨pairLift a z, hpair_mem a z⟩ : CX) : G)
          have hp : y = ⟨pairLift a z, hpair_mem a z⟩ :=
            Subtype.ext hy
          have hcx :
              xCX = eCXStd.symm ⟨pairLift a z, hpair_mem a z⟩ := by
            calc
              xCX = eCXStd.symm (eCXStd xCX) :=
                (eCXStd.symm_apply_apply xCX).symm
              _ = eCXStd.symm ⟨pairLift a z, hpair_mem a z⟩ :=
                congrArg eCXStd.symm hp
          exact congrArg Subtype.val hcx
        · intro a z b w hab
          apply hpair_injective a z b w
          have hcx :
              eCXStd.symm ⟨pairLift a z, hpair_mem a z⟩ =
                eCXStd.symm ⟨pairLift b w, hpair_mem b w⟩ := by
            apply CX.subtype_injective
            exact hab
          exact congrArg Subtype.val (eCXStd.symm.injective hcx)
        · intro a z b w
          change
            ((eCXStd.symm ⟨pairLift a z, hpair_mem a z⟩ : CX) : G) *
                ((eCXStd.symm ⟨pairLift b w, hpair_mem b w⟩ : CX) : G) =
              ((eCXStd.symm
                ⟨pairLift (a + b) (z + w + cocycle a b),
                  hpair_mem (a + b) (z + w + cocycle a b)⟩ : CX) : G)
          let pa : Pstd := ⟨pairLift a z, hpair_mem a z⟩
          let pb : Pstd := ⟨pairLift b w, hpair_mem b w⟩
          let pc : Pstd :=
            ⟨pairLift (a + b) (z + w + cocycle a b),
              hpair_mem (a + b) (z + w + cocycle a b)⟩
          have hp : pa * pb = pc := by
            apply Subtype.ext
            exact hpair_mul a z b w
          have hcx :
              eCXStd.symm pa * eCXStd.symm pb = eCXStd.symm pc := by
            calc
              _ = eCXStd.symm (pa * pb) := (eCXStd.symm.map_mul pa pb).symm
              _ = eCXStd.symm pc := congrArg eCXStd.symm hp
          exact congrArg Subtype.val hcx
      )
    have hCX_card : Nat.card CX = q ^ 2 := by
      calc
        Nat.card CX = Nat.card Pstd := Nat.card_congr eCXStd.toEquiv
        _ = q ^ 2 := hPstd_card
    exact ⟨k, hk, hqk, hFmodel, hst, hCX_typeA, hCX_card⟩
  · right
    right
    letI : Field E := hEfield
    letI : Finite E := hEfinite
    let psuGroup : Group (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Subgroup.toGroup
        (J.specialSubgroup.map Matrix.ProjGenLinGroup.mk)
    letI : Group (ProjectiveSpecialUnitaryMatrixGroup J) := psuGroup
    letI : DivisionMonoid (ProjectiveSpecialUnitaryMatrixGroup J) :=
      psuGroup.toDivisionMonoid
    have hFmodel : Nonempty ((F ⧸ Subgroup.center F) ≃*
        ProjectiveSpecialUnitaryMatrixGroup J) := by
      rcases hFquotM with ⟨eFM⟩
      exact ⟨eFM.trans eM⟩
    have hst : orderOf (s * t) = 3 := by
      let Pmodel : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
        PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
      let sbar : L ⧸ N := QuotientGroup.mk sX
      let rbar : L ⧸ N := QuotientGroup.mk rX
      have hsX_mem_QX : sX ∈ QX := by
        change (sX : G) ∈ Q
        rw [hsX_eq_s]
        exact hsec.section2.Q0_le_Q
          ((hsec.section2.Q0_def s).mpr
            (Or.inr ⟨hsec.s_mem_H, hsec.s_involution⟩))
      have hsbar_mem_M : sbar ∈ M := by
        apply hQbar_le_M
        change QuotientGroup.mk sX ∈ QX.map π
        exact ⟨sX, hsX_mem_QX, rfl⟩
      have hrbar_mem_M : rbar ∈ M := by
        apply hQbar_le_M
        change QuotientGroup.mk rX ∈ QX.map π
        exact ⟨rX, hrX_mem, rfl⟩
      have htbar_mem_M : tbar ∈ M := by
        have htbar_pgroup : IsPGroup 2 (Subgroup.zpowers tbar) := by
          refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers tbar)
            (n := 1) ?_
          rw [Nat.card_zpowers,
            (orderOf_eq_prime_iff.mpr
              ⟨hA1bar.involution_t.sq_eq_one,
                hA1bar.involution_t.ne_one⟩), pow_one]
        obtain ⟨P, htbar_le_P⟩ := htbar_pgroup.exists_le_sylow
        apply hresidual_le_M
        rw [twoPrimeResidual]
        exact (le_iSup (fun S : Sylow 2 (L ⧸ N) =>
          (S : Subgroup (L ⧸ N))) P)
            (htbar_le_P (Subgroup.mem_zpowers tbar))
      let sM : M := ⟨sbar, hsbar_mem_M⟩
      let rM : M := ⟨rbar, hrbar_mem_M⟩
      let tM : M := ⟨tbar, htbar_mem_M⟩
      let sm : ProjectiveSpecialUnitaryMatrixGroup J := eM sM
      let rm : ProjectiveSpecialUnitaryMatrixGroup J := eM rM
      let tm : ProjectiveSpecialUnitaryMatrixGroup J := eM tM
      have hsm_mem_P : sm ∈
          (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
        have hsM_mem_PM : sM ∈ (PM : Subgroup M) := by
          change sbar ∈ (Pbar : Subgroup (L ⧸ N))
          rw [← hPbar]
          change QuotientGroup.mk sX ∈ QX.map π
          exact ⟨sX, hsX_mem_QX, rfl⟩
        change eM sM ∈ (PM : Subgroup M).map eM.toMonoidHom
        exact ⟨sM, hsM_mem_PM, rfl⟩
      have hrm_mem_P : rm ∈
          (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
        have hrM_mem_PM : rM ∈ (PM : Subgroup M) := by
          change rbar ∈ (Pbar : Subgroup (L ⧸ N))
          rw [← hPbar]
          change QuotientGroup.mk rX ∈ QX.map π
          exact ⟨rX, hrX_mem, rfl⟩
        change eM rM ∈ (PM : Subgroup M).map eM.toMonoidHom
        exact ⟨rM, hrM_mem_PM, rfl⟩
      have htm_not_mem_P : tm ∉
          (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
        intro htm_mem
        change eM tM ∈ (PM : Subgroup M).map eM.toMonoidHom at htm_mem
        rcases htm_mem with ⟨m, hm, hm_eq⟩
        have hm_tM : m = tM := eM.injective hm_eq
        have htM_mem_PM : tM ∈ (PM : Subgroup M) := hm_tM ▸ hm
        have htbar_mem_Pbar : tbar ∈ (Pbar : Subgroup (L ⧸ N)) := htM_mem_PM
        have htbar_mem_Qbar : tbar ∈ Qbar := by
          rw [hPbar]
          exact htbar_mem_Pbar
        exact hA1bar.t_not_mem_H (hA1bar.Q_le_H htbar_mem_Qbar)
      have hsm_sq : sm * sm = 1 := by
        have hsM_sq : sM ^ 2 = 1 := by
          apply Subtype.ext
          change sbar ^ 2 = 1
          exact hπ_sq_eq_one sX hsX_involution.sq_eq_one
        calc
          sm * sm = sm ^ 2 := by simp [pow_two]
          _ = eM (sM ^ 2) := (map_pow eM sM 2).symm
          _ = eM 1 := congrArg eM hsM_sq
          _ = 1 := map_one eM
      have htm_sq : tm * tm = 1 := by
        have htM_sq : tM ^ 2 = 1 := by
          apply Subtype.ext
          change tbar ^ 2 = 1
          exact hπ_sq_eq_one tX hA1X.involution_t.sq_eq_one
        calc
          tm * tm = tm ^ 2 := by simp [pow_two]
          _ = eM (tM ^ 2) := (map_pow eM tM 2).symm
          _ = eM 1 := congrArg eM htM_sq
          _ = 1 := map_one eM
      have htm_involution : IsInvolution tm := by
        constructor
        · intro htm_one
          apply htm_not_mem_P
          rw [htm_one]
          exact (Pmodel :
            Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).one_mem
        · simpa [pow_two] using htm_sq
      have hmodel_structure :
          tm * sm * tm = rm⁻¹ * tm * rm := by
        have hbar_structure :
            tbar * sbar * tbar = rbar⁻¹ * tbar * rbar := by
          simpa [π, tbar, sbar, rbar] using congrArg π hstructureX
        have hM_structure :
            tM * sM * tM = rM⁻¹ * tM * rM := by
          apply Subtype.ext
          simpa [tM, sM, rM] using hbar_structure
        simpa [tm, sm, rm] using congrArg eM hM_structure
      obtain ⟨Pstd, j, T, hj_mem_Pstd, hj_involution, hstandard_braid,
          _hT_standard, _hPstd_root_iff, c, hcP, hctm⟩ :=
        psu_exists_simultaneous_standardizer J q hq_power hq_gt hEcard
          hfixedCard hJstandard Pmodel tm htm_involution htm_not_mem_P
      have htm_eq : tm = c⁻¹ * T * c := by
        calc
          tm = c⁻¹ * (c * tm * c⁻¹) * c := by group
          _ = c⁻¹ * T * c := by rw [hctm]
      have hback_mem :
          ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
            x ∈ (Pstd :
              Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) →
              c⁻¹ * x * c ∈
                (Pmodel :
                  Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
        intro x hx
        have hx_smul :
            x ∈ ((c • Pmodel :
              Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
                Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
          rw [hcP]
          exact hx
        rw [Sylow.coe_subgroup_smul] at hx_smul
        rcases Set.mem_smul_set.mp hx_smul with ⟨y, hy, hxy⟩
        have hxy' : c * y * c⁻¹ = x := by
          simpa [MulAut.conj_apply] using hxy
        have hback : c⁻¹ * x * c = y := by
          rw [← hxy']
          group
        rw [hback]
        change y ∈ (Pmodel : Set (ProjectiveSpecialUnitaryMatrixGroup J))
        exact hy
      have hj_back : c⁻¹ * j * c ∈
          (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
        hback_mem j hj_mem_Pstd
      let cM : M := eM.symm c
      let jM : M := eM.symm j
      let sjM : M := cM⁻¹ * jM * cM
      let rjM : M := sjM
      let sjbar : L ⧸ N := (sjM : L ⧸ N)
      let rjbar : L ⧸ N := (rjM : L ⧸ N)
      have hsjM_mem_PM : sjM ∈ (PM : Subgroup M) := by
        change c⁻¹ * j * c ∈ (PM : Subgroup M).map eM.toMonoidHom at hj_back
        rcases hj_back with ⟨z, hz, hz_eq⟩
        have hz_eq_sjM : z = sjM := by
          apply eM.injective
          calc
            eM z = c⁻¹ * j * c := hz_eq
            _ = eM sjM := by simp [sjM, cM, jM]
        change sjM ∈ (PM : Set M)
        rw [← hz_eq_sjM]
        change z ∈ (PM : Set M) at hz
        exact hz
      have hsjbar_mem_Qbar : sjbar ∈ Qbar := by
        rw [hPbar]
        change (sjM : L ⧸ N) ∈ (Pbar : Subgroup (L ⧸ N))
        exact hsjM_mem_PM
      have hrjbar_mem_Qbar : rjbar ∈ Qbar := by
        simpa [rjbar, rjM, sjbar] using hsjbar_mem_Qbar
      have hjM_involution : IsInvolution jM := by
        constructor
        · intro hjM_one
          apply hj_involution.ne_one
          have := congrArg eM hjM_one
          simpa [jM] using this
        · apply eM.injective
          simpa [jM] using hj_involution.sq_eq_one
      have hsjM_involution : IsInvolution sjM := by
        simpa [sjM, rightConjugateElem] using
          isInvolution_rightConjugateElem hjM_involution
      have hsjbar_involution : IsInvolution sjbar := by
        constructor
        · intro hsjbar_one
          apply hsjM_involution.ne_one
          apply Subtype.ext
          simpa [sjbar] using hsjbar_one
        · have hsquare := congrArg
            (fun z : M => (z : L ⧸ N)) hsjM_involution.sq_eq_one
          simpa [sjbar] using hsquare
      have hstandard_structure_M :
          tM * sjM * tM = rjM⁻¹ * tM * rjM := by
        set_option backward.isDefEq.respectTransparency false in
        exact (by
          apply eM.injective
          dsimp [sjM, rjM, cM, jM]
          simp only [map_mul, map_inv, eM.apply_symm_apply]
          change
            tm * (c⁻¹ * j * c) * tm =
              (c⁻¹ * j * c)⁻¹ * tm * (c⁻¹ * j * c)
          rw [htm_eq]
          calc
            c⁻¹ * T * c * (c⁻¹ * j * c) * (c⁻¹ * T * c) =
                c⁻¹ * (T * j * T) * c := by group
            _ = c⁻¹ * (j * T * j) * c := by rw [hstandard_braid]
            _ = (c⁻¹ * j * c)⁻¹ *
                (c⁻¹ * T * c) * (c⁻¹ * j * c) := by
              simp only [mul_inv_rev, inv_inv,
                hj_involution.inv_eq_self]
              group)
      have hstandard_structure_bar :
          tbar * sjbar * tbar = rjbar⁻¹ * tbar * rjbar :=
        congrArg (fun z : M => (z : L ⧸ N)) hstandard_structure_M
      have hsbar_mem_Qbar : sbar ∈ Qbar := by
        change QuotientGroup.mk sX ∈ QX.map π
        exact ⟨sX, hsX_mem_QX, rfl⟩
      have hrbar_mem_Qbar : rbar ∈ Qbar := by
        change QuotientGroup.mk rX ∈ QX.map π
        exact ⟨rX, hrX_mem, rfl⟩
      have hsm_ne : sm ≠ 1 := by
        intro hsm_one
        apply htm_not_mem_P
        have hconj_one : rm⁻¹ * tm * rm = 1 := by
          simpa [hsm_one, htm_sq] using hmodel_structure.symm
        have htm_one : tm = 1 := by
          calc
            tm = rm * (rm⁻¹ * tm * rm) * rm⁻¹ := by group
            _ = 1 := by rw [hconj_one]; simp
        rw [htm_one]
        exact (Pmodel :
          Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).one_mem
      have hsM_involution : IsInvolution sM := by
        constructor
        · intro hsM_one
          apply hsm_ne
          have := congrArg eM hsM_one
          simpa [sm] using this
        · apply eM.injective
          simpa [sm, pow_two] using hsm_sq
      have hsbar_involution : IsInvolution sbar := by
        constructor
        · intro hsbar_one
          apply hsM_involution.ne_one
          apply Subtype.ext
          exact hsbar_one
        · have hsquare := congrArg
            (fun z : M => (z : L ⧸ N)) hsM_involution.sq_eq_one
          simpa [sbar] using hsquare
      have hcurrent_structure_bar :
          tbar * sbar * tbar = rbar⁻¹ * tbar * rbar := by
        simpa [π, tbar, sbar, rbar] using congrArg π hstructureX
      rcases proposition_4_b Hbar Dbar Qbar tbar hA1bar with
        ⟨pbar, _hpbar, hpbar_unique⟩
      have hcurrent_eq : (sbar, rbar) = pbar :=
        hpbar_unique (sbar, rbar)
          ⟨hA1bar.Q_le_H hsbar_mem_Qbar, hsbar_involution,
            hrbar_mem_Qbar, hcurrent_structure_bar⟩
      have hstandard_eq : (sjbar, rjbar) = pbar :=
        hpbar_unique (sjbar, rjbar)
          ⟨hA1bar.Q_le_H hsjbar_mem_Qbar, hsjbar_involution,
            hrjbar_mem_Qbar, hstandard_structure_bar⟩
      have hpairs : (sbar, rbar) = (sjbar, rjbar) :=
        hcurrent_eq.trans hstandard_eq.symm
      have hsM_eq : sM = sjM := by
        apply Subtype.ext
        exact congrArg Prod.fst hpairs
      have hrM_eq : rM = rjM := by
        apply Subtype.ext
        exact congrArg Prod.snd hpairs
      have hsm_back : sm = c⁻¹ * j * c := by
        set_option backward.isDefEq.respectTransparency false in
        exact (by
          change eM sM = c⁻¹ * j * c
          rw [hsM_eq]
          simp [sjM, cM, jM])
      have hrm_back : rm = c⁻¹ * j * c := by
        set_option backward.isDefEq.respectTransparency false in
        exact (by
          change eM rM = c⁻¹ * j * c
          rw [hrM_eq]
          simp [rjM, sjM, cM, jM])
      have hrm_eq_sm : rm = sm := hrm_back.trans hsm_back.symm
      have hmodel_braid : tm * sm * tm = sm * tm * sm := by
        calc
          tm * sm * tm = rm⁻¹ * tm * rm := hmodel_structure
          _ = sm⁻¹ * tm * sm := by rw [hrm_eq_sm]
          _ = sm * tm * sm := by
            rw [show sm⁻¹ = sm from inv_eq_of_mul_eq_one_right hsm_sq]
      have hbar_braid : tbar * sbar * tbar = sbar * tbar * sbar := by
        have hM_braid : tM * sM * tM = sM * tM * sM := by
          apply eM.injective
          simpa [tm, sm] using hmodel_braid
        exact congrArg Subtype.val hM_braid
      have hsbar_sq : sbar * sbar = 1 := by
        rw [← pow_two]
        exact hπ_sq_eq_one sX hsX_involution.sq_eq_one
      have htbar_sq : tbar * tbar = 1 := by
        rw [← pow_two]
        exact hπ_sq_eq_one tX hA1X.involution_t.sq_eq_one
      have hbar_pow : (sbar * tbar) ^ 3 = 1 := by
        rw [pow_three]
        calc
          sbar * tbar * (sbar * tbar * (sbar * tbar)) =
              sbar * (tbar * sbar * tbar) * sbar * tbar := by group
          _ = sbar * (sbar * tbar * sbar) * sbar * tbar := by
            rw [hbar_braid]
          _ = (sbar * sbar) * tbar * (sbar * sbar) * tbar := by group
          _ = 1 := by rw [hsbar_sq]; simpa using htbar_sq
      have hbar_ne : sbar * tbar ≠ 1 := by
        intro hprod
        have hst_eq : sbar = tbar := by
          have hright := congrArg (fun z => z * tbar) hprod
          simpa [mul_assoc, htbar_sq] using hright
        have htbar_mem_Hbar : tbar ∈ Hbar := hst_eq ▸
          hA1bar.Q_le_H hsbar_mem_Qbar
        exact hA1bar.t_not_mem_H htbar_mem_Hbar
      haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
      have hbar_order : orderOf (sbar * tbar) = 3 :=
        orderOf_eq_prime_iff.mpr ⟨hbar_pow, hbar_ne⟩
      have hquotient_order :
          orderOf (QuotientGroup.mk (sX * tX) : L ⧸ N) = 3 := by
        simpa [sbar, tbar] using hbar_order
      have hcoe_prod : ((sX * tX : L) : G) = s * t := by
        simp [hsX_eq_s, tX]
      calc
        orderOf (s * t) = orderOf ((sX * tX : L) : G) :=
          congrArg orderOf hcoe_prod.symm
        _ = orderOf (sX * tX) := Subgroup.orderOf_coe (sX * tX)
        _ = orderOf (QuotientGroup.mk (sX * tX) : L ⧸ N) :=
          horder_quotient.symm
        _ = 3 := hquotient_order
    have hseed : psuCorollaryTwoLiftedSeed F CX (L ⊓ Q0) V t := by
      letI : Fintype E := Fintype.ofFinite E
      have hq_even : Even q := by
        rcases hq_power with ⟨n, hn⟩
        have hnpos : 0 < n := by
          by_contra hn_not_pos
          have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn_not_pos
          subst n
          norm_num at hn
          omega
        rw [hn]
        exact Nat.even_pow.mpr ⟨even_two, ne_of_gt hnpos⟩
      have hE_even : Even (Fintype.card E) := by
        rw [Fintype.card_eq_nat_card, hEcard]
        exact hq_even.pow_of_ne_zero (by norm_num)
      have hcharE : ringChar E = 2 :=
        FiniteField.even_card_iff_char_two.mpr
          (Nat.even_iff.mp hE_even)
      letI : CharP E 2 := by
        rw [← hcharE]
        infer_instance
      letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective eM eM.surjective
      let FR : Subgroup L := twoPrimeResidual L
      have hQX_le_FR : QX ≤ FR := by
        rcases hQX_sylow with ⟨P, hQX_eq⟩
        rw [hQX_eq]
        change (P : Subgroup L) ≤ twoPrimeResidual L
        rw [twoPrimeResidual]
        exact le_iSup (fun S : Sylow 2 L => (S : Subgroup L)) P
      have htX_mem_FR : tX ∈ FR := by
        have htX_pgroup : IsPGroup 2 (Subgroup.zpowers tX) := by
          refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers tX)
            (n := 1) ?_
          rw [Nat.card_zpowers,
            (orderOf_eq_prime_iff.mpr
              ⟨hA1X.involution_t.sq_eq_one,
                hA1X.involution_t.ne_one⟩), pow_one]
        obtain ⟨P, htX_le_P⟩ := htX_pgroup.exists_le_sylow
        change tX ∈ twoPrimeResidual L
        rw [twoPrimeResidual]
        exact (le_iSup (fun S : Sylow 2 L => (S : Subgroup L)) P)
          (htX_le_P (Subgroup.mem_zpowers tX))
      let Pmodel : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
        PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
      have htbar_mem_M : tbar ∈ M := by
        have htbar_pgroup : IsPGroup 2 (Subgroup.zpowers tbar) := by
          refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers tbar)
            (n := 1) ?_
          rw [Nat.card_zpowers,
            (orderOf_eq_prime_iff.mpr
              ⟨hA1bar.involution_t.sq_eq_one,
                hA1bar.involution_t.ne_one⟩), pow_one]
        obtain ⟨P, htbar_le_P⟩ := htbar_pgroup.exists_le_sylow
        apply hresidual_le_M
        rw [twoPrimeResidual]
        exact (le_iSup (fun S : Sylow 2 (L ⧸ N) =>
          (S : Subgroup (L ⧸ N))) P)
            (htbar_le_P (Subgroup.mem_zpowers tbar))
      let tM : M := ⟨tbar, htbar_mem_M⟩
      let tm : ProjectiveSpecialUnitaryMatrixGroup J := eM tM
      have htm_not_mem_P : tm ∉
          (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
        intro htm_mem
        change eM tM ∈ (PM : Subgroup M).map eM.toMonoidHom at htm_mem
        rcases htm_mem with ⟨m, hm, hm_eq⟩
        have hm_tM : m = tM := eM.injective hm_eq
        have htM_mem_PM : tM ∈ (PM : Subgroup M) := hm_tM ▸ hm
        have htbar_mem_Pbar : tbar ∈
            (Pbar : Subgroup (L ⧸ N)) := htM_mem_PM
        have htbar_mem_Qbar : tbar ∈ Qbar := by
          rw [hPbar]
          exact htbar_mem_Pbar
        exact hA1bar.t_not_mem_H (hA1bar.Q_le_H htbar_mem_Qbar)
      have htM_sq : tM ^ 2 = 1 := by
        apply Subtype.ext
        change tbar ^ 2 = 1
        exact hπ_sq_eq_one tX hA1X.involution_t.sq_eq_one
      have htm_involution : IsInvolution tm := by
        constructor
        · intro htm_one
          apply htm_not_mem_P
          rw [htm_one]
          exact (Pmodel :
            Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).one_mem
        · simpa [tm] using congrArg eM htM_sq
      obtain ⟨Pstd, _j, T, _hj_mem_Pstd, _hj_involution,
          _hstandard_braid, hT_standard, hPstd_root_iff, c, hcP, hctm⟩ :=
        psu_exists_simultaneous_standardizer J q hq_power hq_gt hEcard
          hfixedCard hJstandard Pmodel tm htm_involution htm_not_mem_P
      let eA : M ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
        eM.trans
          (MulAut.conj c :
            ProjectiveSpecialUnitaryMatrixGroup J ≃*
              ProjectiveSpecialUnitaryMatrixGroup J)
      have heA_tM : eA tM = T := by
        simpa [eA, tm] using hctm
      obtain ⟨omega0, gamma0, zeta0, homega0_sq, hzeta0_ne,
          hzeta0_T, hseed0, hzeta0_comm_involutions,
          ⟨omegaCoord, homega0_root⟩,
          ⟨gammaCoord, hgamma0_root⟩, ⟨k, hzeta0_torus⟩⟩ :=
        External.exists_hermitianPSU_corollary_two_seed
          J q hEcard hfixedCard hJstandard hq_gt
      have homega0_mem_Pstd : omega0 ∈
          (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
        (hPstd_root_iff omega0).mpr ⟨omegaCoord, homega0_root⟩
      have hgamma0_mem_Pstd : gamma0 ∈
          (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
        (hPstd_root_iff gamma0).mpr ⟨gammaCoord, hgamma0_root⟩
      let omegaM : M := eA.symm omega0
      let gammaM : M := eA.symm gamma0
      let zetaM : M := eA.symm zeta0
      have heA_omegaM : eA omegaM = omega0 := eA.apply_symm_apply omega0
      have heA_gammaM : eA gammaM = gamma0 := eA.apply_symm_apply gamma0
      have heA_zetaM : eA zetaM = zeta0 := eA.apply_symm_apply zeta0
      have homegaM_mem_PM : omegaM ∈ (PM : Subgroup M) := by
        apply (mem_aligned_sylow_iff eM PM Pstd c hcP omegaM).mpr
        change eA omegaM ∈
          (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        rw [heA_omegaM]
        exact homega0_mem_Pstd
      have hgammaM_mem_PM : gammaM ∈ (PM : Subgroup M) := by
        apply (mem_aligned_sylow_iff eM PM Pstd c hcP gammaM).mpr
        change eA gammaM ∈
          (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        rw [heA_gammaM]
        exact hgamma0_mem_Pstd
      have hzeta0_normalizer : zeta0 ∈
          Subgroup.normalizer
            ((Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
              Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
        rw [hzeta0_torus]
        exact hermitianTorusPSU_mem_normalizer_of_root_iff
          J hJstandard (Pstd : Subgroup _) hPstd_root_iff k
      have hzetaM_normalizer : zetaM ∈
          Subgroup.normalizer ((PM : Subgroup M) : Set M) := by
        rw [Subgroup.mem_normalizer_iff]
        intro m
        rw [mem_aligned_sylow_iff eM PM Pstd c hcP m,
          mem_aligned_sylow_iff eM PM Pstd c hcP
            (zetaM * m * zetaM⁻¹)]
        have hzeta0_iff :=
          (Subgroup.mem_normalizer_iff.mp hzeta0_normalizer) (eA m)
        have heA_conj : eA (zetaM * m * zetaM⁻¹) =
            zeta0 * eA m * zeta0⁻¹ := by
          rw [map_mul, map_mul, map_inv, heA_zetaM]
        rw [heA_conj]
        exact hzeta0_iff
      have hzeta_bar_normalizer : (zetaM : L ⧸ N) ∈
          Subgroup.normalizer (Qbar : Set (L ⧸ N)) :=
        subtype_mem_normalizer_of_mem_subtype_sylow_normalizer
          M Qbar Pbar hPbar hPbar_le_M zetaM hzetaM_normalizer
      have hQbar_ne : Qbar ≠ ⊥ := by
        have hQbar_even : Even (Nat.card Qbar) := hA1bar.Q_even
        intro hbot
        have hcard_one : Nat.card Qbar = 1 := by
          rw [hbot]
          simp
        rw [hcard_one] at hQbar_even
        exact (by decide : ¬ Even 1) hQbar_even
      have hzeta_bar_Hbar : (zetaM : L ⧸ N) ∈ Hbar :=
        (PFchapter1section1.proposition_1_b
          Hbar Dbar Qbar tbar hA1bar Qbar hQbar_ne le_rfl)
            hzeta_bar_normalizer
      have homega_bar_Qbar : (omegaM : L ⧸ N) ∈ Qbar := by
        rw [hPbar]
        exact homegaM_mem_PM
      have hgamma_bar_Qbar : (gammaM : L ⧸ N) ∈ Qbar := by
        rw [hPbar]
        exact hgammaM_mem_PM
      change (omegaM : L ⧸ N) ∈ QX.map π at homega_bar_Qbar
      change (gammaM : L ⧸ N) ∈ QX.map π at hgamma_bar_Qbar
      rcases homega_bar_Qbar with
        ⟨omegaL, homegaL_mem_QX, homega_lift⟩
      rcases hgamma_bar_Qbar with
        ⟨gammaL, hgammaL_mem_QX, hgamma_lift⟩
      have hzeta_bar_map : (zetaM : L ⧸ N) ∈
          (twoPrimeResidual L).map π := by
        rw [hmap_residual]
        exact zetaM.property
      rcases hzeta_bar_map with ⟨zetaL, hzetaL_mem_FR, hzeta_lift⟩
      have hN_le_HX : N ≤ HX := by
        intro n hn
        have hnDX : n ∈ DX := by
          have hn' : n ∈ DX ⊓ Subgroup.centralizer (QX : Set L) := by
            rw [← h4c.1]
            exact hn
          exact hn'.1
        have hn' : n ∈ HX ⊓ rightConjugate HX tX :=
          hA1X.D_eq.symm ▸ hnDX
        exact hn'.1
      have hzeta_lift_Hbar : π zetaL ∈ Hbar := by
        rw [hzeta_lift]
        exact hzeta_bar_Hbar
      change π zetaL ∈ HX.map π at hzeta_lift_Hbar
      rcases hzeta_lift_Hbar with ⟨hL, hhL_mem_HX, hhL_lift⟩
      have hzeta_div_h_mem_N : zetaL / hL ∈ N :=
        (QuotientGroup.eq_iff_div_mem (N := N)).mp hhL_lift.symm
      have hzetaL_mem_HX : zetaL ∈ HX := by
        have hzeta_eq : zetaL = (zetaL / hL) * hL := by
          simp [div_eq_mul_inv, mul_assoc]
        rw [hzeta_eq]
        exact HX.mul_mem (hN_le_HX hzeta_div_h_mem_N) hhL_mem_HX
      have hzetaM_comm_tM : zetaM * tM = tM * zetaM := by
        apply eA.injective
        simp only [map_mul]
        rw [heA_zetaM, heA_tM]
        rw [hT_standard]
        exact hzeta0_T
      have hzeta_lift_comm_t : π zetaL * π tX = π tX * π zetaL := by
        calc
          π zetaL * π tX =
              (zetaM : L ⧸ N) * (tM : L ⧸ N) := by
                rw [hzeta_lift]
                rfl
          _ = (tM : L ⧸ N) * (zetaM : L ⧸ N) :=
            congrArg Subtype.val hzetaM_comm_tM
          _ = π tX * π zetaL := by
            rw [hzeta_lift]
            rfl
      let zetaConj : L := tX * zetaL * tX⁻¹
      have hzetaConj_lift : π zetaConj = π zetaL := by
        dsimp [zetaConj]
        simp only [map_mul, map_inv]
        rw [← hzeta_lift_comm_t]
        simp
      have hzetaConj_div_mem_N : zetaConj / zetaL ∈ N :=
        (QuotientGroup.eq_iff_div_mem (N := N)).mp hzetaConj_lift
      have hzetaConj_mem_HX : zetaConj ∈ HX := by
        have hzetaConj_eq :
            zetaConj = (zetaConj / zetaL) * zetaL := by
          simp [div_eq_mul_inv, mul_assoc]
        rw [hzetaConj_eq]
        exact HX.mul_mem (hN_le_HX hzetaConj_div_mem_N) hzetaL_mem_HX
      have hzetaL_mem_DX : zetaL ∈ DX := by
        have hzeta_right : zetaL ∈ rightConjugate HX tX := by
          rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
          refine ⟨zetaConj, hzetaConj_mem_HX, ?_⟩
          simp [zetaConj, mul_assoc]
        change zetaL ∈ D.comap L.subtype
        rw [hA1X.D_eq]
        exact ⟨hzetaL_mem_HX, hzeta_right⟩
      have hzeta_mem_D : ((zetaL : L) : G) ∈ D := hzetaL_mem_DX
      let kappaL : L := tX * zetaL * tX⁻¹ * zetaL⁻¹
      have hkappa_mem_N : kappaL ∈ N := by
        simpa [kappaL, zetaConj, div_eq_mul_inv] using hzetaConj_div_mem_N
      have hkappa_mem_FR : kappaL ∈ FR := by
        dsimp [kappaL]
        exact FR.mul_mem
          (FR.mul_mem (FR.mul_mem htX_mem_FR hzetaL_mem_FR)
            (FR.inv_mem htX_mem_FR))
          (FR.inv_mem hzetaL_mem_FR)
      have hkappa_mem_NL : ((kappaL : L) : G) ∈ NL :=
        ⟨kappaL, hkappa_mem_N, rfl⟩
      have hkappa_mem_F : ((kappaL : L) : G) ∈ F :=
        ⟨kappaL, hkappa_mem_FR, rfl⟩
      have hkappa_center : ((kappaL : L) : G) ∈
          (Subgroup.center F).map F.subtype := by
        rw [← hNLF]
        exact ⟨hkappa_mem_NL, hkappa_mem_F⟩
      have hkappa_mem_V : ((kappaL : L) : G) ∈ V :=
        (hNL_le ((hcore_mem kappaL).mp hkappa_mem_N)).2
      have hkappa_mem_D : ((kappaL : L) : G) ∈ D := by
        have hkappa_peterfalvi : ((kappaL : L) : G) ∈ peterfalviV D t := by
          rw [← hsec.section2.V_eq]
          exact hkappa_mem_V
        exact hkappa_peterfalvi.1
      have ht_mem_F : t ∈ F := ⟨tX, htX_mem_FR, rfl⟩
      have hzeta_comm_t : ((zetaL : L) : G) * t =
          t * ((zetaL : L) : G) := by
        apply commute_of_central_commutator_mem_odd_subgroup
          D F t ((zetaL : L) : G) hsec.section2.hA.A1.D_odd
            hsec.section2.hA.A1.involution_t.sq_eq_one ht_mem_F
        · simpa [kappaL, tX] using hkappa_mem_D
        · simpa [kappaL, tX] using hkappa_center
      have hzeta_mem_V : ((zetaL : L) : G) ∈ V := by
        rw [hsec.section2.V_eq]
        exact ⟨hzeta_mem_D,
          (Subgroup.mem_centralizer_singleton_iff.mpr hzeta_comm_t)⟩
      have hzeta_ne : ((zetaL : L) : G) ≠ 1 := by
        intro hzeta_one
        apply hzeta0_ne
        have hzetaL_one : zetaL = 1 := by
          apply L.subtype_injective
          simpa using hzeta_one
        have hzetaM_one : zetaM = 1 := by
          apply Subtype.ext
          calc
            (zetaM : L ⧸ N) = π zetaL := hzeta_lift.symm
            _ = π 1 := congrArg π hzetaL_one
            _ = 1 := map_one π
        have hzeta0_one := congrArg eA hzetaM_one
        simpa [zetaM] using hzeta0_one
      have hzeta_centralizes_CQ0 : ((zetaL : L) : G) ∈
          Subgroup.centralizer ((L ⊓ Q0 : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        let qL : L := ⟨q, hq.1⟩
        have hqL_mem_QX : qL ∈ QX := hsec.section2.Q0_le_Q hq.2
        have hq_sq : q ^ 2 = 1 := by
          rcases (hsec.section2.Q0_def q).mp hq.2 with hq_one | hq_inv
          · simp [hq_one]
          · exact hq_inv.2.sq_eq_one
        have hqL_sq : qL ^ 2 = 1 := by
          apply L.subtype_injective
          simpa [qL] using hq_sq
        let qbar : L ⧸ N := π qL
        have hqbar_mem_Qbar : qbar ∈ Qbar := by
          exact ⟨qL, hqL_mem_QX, rfl⟩
        have hqbar_mem_Pbar : qbar ∈ (Pbar : Subgroup (L ⧸ N)) := by
          rw [← hPbar]
          exact hqbar_mem_Qbar
        let qM : M := ⟨qbar, hPbar_le_M hqbar_mem_Pbar⟩
        have hqM_mem_PM : qM ∈ (PM : Subgroup M) := hqbar_mem_Pbar
        have heA_qM_mem_Pstd : eA qM ∈
            (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
          (mem_aligned_sylow_iff eM PM Pstd c hcP qM).mp hqM_mem_PM
        rcases (hPstd_root_iff (eA qM)).mp heA_qM_mem_Pstd with
          ⟨qCoord, hqCoord⟩
        have hqM_sq : qM ^ 2 = 1 := by
          apply Subtype.ext
          simpa [qM, qbar] using congrArg π hqL_sq
        have heA_qM_sq : (eA qM) ^ 2 = 1 := by
          simpa only [map_pow, map_one] using congrArg eA hqM_sq
        have hcomm_model : zeta0 * eA qM = eA qM * zeta0 :=
          hzeta0_comm_involutions (eA qM) ⟨qCoord, hqCoord⟩ heA_qM_sq
        have hcomm_M : zetaM * qM = qM * zetaM := by
          apply eA.injective
          simpa only [map_mul, heA_zetaM] using hcomm_model
        have hcomm_quot : π zetaL * π qL = π qL * π zetaL := by
          calc
            π zetaL * π qL =
                (zetaM : L ⧸ N) * (qM : L ⧸ N) := by
              rw [hzeta_lift]
            _ = (qM : L ⧸ N) * (zetaM : L ⧸ N) :=
              congrArg Subtype.val hcomm_M
            _ = π qL * π zetaL := by
              rw [hzeta_lift]
        let kappaL : L := qL * zetaL * qL⁻¹ * zetaL⁻¹
        have hkappa_lift : π kappaL = 1 := by
          dsimp [kappaL]
          simp only [map_mul, map_inv]
          rw [← hcomm_quot]
          group
        have hkappa_mem_N : kappaL ∈ N :=
          (QuotientGroup.eq_one_iff (N := N) kappaL).mp hkappa_lift
        have hqL_mem_FR : qL ∈ FR := hQX_le_FR hqL_mem_QX
        have hkappa_mem_FR : kappaL ∈ FR := by
          dsimp [kappaL]
          exact FR.mul_mem
            (FR.mul_mem (FR.mul_mem hqL_mem_FR hzetaL_mem_FR)
              (FR.inv_mem hqL_mem_FR))
            (FR.inv_mem hzetaL_mem_FR)
        have hkappa_mem_NL : ((kappaL : L) : G) ∈ NL :=
          ⟨kappaL, hkappa_mem_N, rfl⟩
        have hkappa_mem_F : ((kappaL : L) : G) ∈ F :=
          ⟨kappaL, hkappa_mem_FR, rfl⟩
        have hkappa_center : ((kappaL : L) : G) ∈
            (Subgroup.center F).map F.subtype := by
          rw [← hNLF]
          exact ⟨hkappa_mem_NL, hkappa_mem_F⟩
        have hkappa_mem_V : ((kappaL : L) : G) ∈ V :=
          (hNL_le ((hcore_mem kappaL).mp hkappa_mem_N)).2
        have hkappa_mem_D : ((kappaL : L) : G) ∈ D := by
          have hkappa_peterfalvi : ((kappaL : L) : G) ∈
              peterfalviV D t := by
            rw [← hsec.section2.V_eq]
            exact hkappa_mem_V
          exact hkappa_peterfalvi.1
        have hq_mem_F : q ∈ F := ⟨qL, hqL_mem_FR, rfl⟩
        have hzeta_comm_q : ((zetaL : L) : G) * q =
            q * ((zetaL : L) : G) := by
          apply commute_of_central_commutator_mem_odd_subgroup
            D F q ((zetaL : L) : G) hsec.section2.hA.A1.D_odd
              hq_sq hq_mem_F
          · simpa [kappaL, qL] using hkappa_mem_D
          · simpa [kappaL, qL] using hkappa_center
        exact hzeta_comm_q.symm
      have homega_sq : (((omegaL : L) : G) ^ 2) ≠ 1 := by
        intro homega_sq_G
        apply homega0_sq
        have homegaL_sq : omegaL ^ 2 = 1 := by
          apply L.subtype_injective
          simpa using homega_sq_G
        have homegaM_sq : omegaM ^ 2 = 1 := by
          apply Subtype.ext
          calc
            ((omegaM ^ 2 : M) : L ⧸ N) =
                (omegaM : L ⧸ N) ^ 2 := rfl
            _ = (π omegaL) ^ 2 := by rw [homega_lift]
            _ = π (omegaL ^ 2) := (map_pow π omegaL 2).symm
            _ = π 1 := congrArg π homegaL_sq
            _ = 1 := map_one π
        have homega0_sq' := congrArg eA homegaM_sq
        simpa [omegaM] using homega0_sq'
      have hseedM :
          tM * omegaM * tM =
            gammaM * zetaM ^ 3 * tM *
              (zetaM⁻¹ * omegaM⁻¹ * zetaM) := by
        apply eA.injective
        simp only [map_mul, map_pow, map_inv]
        rw [heA_tM, heA_omegaM, heA_gammaM, heA_zetaM, hT_standard]
        exact hseed0
      let lhsL : L := tX * omegaL * tX
      let rhsL : L :=
        gammaL * zetaL ^ 3 * tX *
          (zetaL⁻¹ * omegaL⁻¹ * zetaL)
      have hseed_quot : π lhsL = π rhsL := by
        dsimp [lhsL, rhsL]
        simp only [map_mul, map_pow, map_inv]
        rw [homega_lift, hgamma_lift, hzeta_lift]
        simpa [tM, tbar, hπ_apply] using congrArg Subtype.val hseedM
      let deltaL : L := rhsL⁻¹ * lhsL
      have hdelta_lift : π deltaL = 1 := by
        dsimp [deltaL]
        rw [map_mul, map_inv, hseed_quot]
        simp
      have hdelta_mem_N : deltaL ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) deltaL).mp hdelta_lift
      have homegaL_mem_FR : omegaL ∈ FR :=
        hQX_le_FR homegaL_mem_QX
      have hgammaL_mem_FR : gammaL ∈ FR :=
        hQX_le_FR hgammaL_mem_QX
      have hlhs_mem_FR : lhsL ∈ FR := by
        dsimp [lhsL]
        exact FR.mul_mem (FR.mul_mem htX_mem_FR homegaL_mem_FR)
          htX_mem_FR
      have hrhs_mem_FR : rhsL ∈ FR := by
        have hconj_mem_FR : zetaL⁻¹ * omegaL⁻¹ * zetaL ∈ FR :=
          FR.mul_mem
            (FR.mul_mem (FR.inv_mem hzetaL_mem_FR)
              (FR.inv_mem homegaL_mem_FR)) hzetaL_mem_FR
        dsimp [rhsL]
        exact FR.mul_mem
          (FR.mul_mem
            (FR.mul_mem hgammaL_mem_FR (FR.pow_mem hzetaL_mem_FR 3))
            htX_mem_FR) hconj_mem_FR
      have hdelta_mem_FR : deltaL ∈ FR := by
        dsimp [deltaL]
        exact FR.mul_mem (FR.inv_mem hrhs_mem_FR) hlhs_mem_FR
      have hdelta_mem_NL : ((deltaL : L) : G) ∈ NL :=
        ⟨deltaL, hdelta_mem_N, rfl⟩
      have hdelta_mem_F : ((deltaL : L) : G) ∈ F :=
        ⟨deltaL, hdelta_mem_FR, rfl⟩
      have hzeta_mem_F : ((zetaL : L) : G) ∈ F :=
        ⟨zetaL, hzetaL_mem_FR, rfl⟩
      have hzeta_not_center : ((zetaL : L) : G) ∉
          (Subgroup.center F).map F.subtype := by
        intro hzeta_center
        rw [← hNLF] at hzeta_center
        rcases hzeta_center.1 with ⟨n, hnN, hn_value⟩
        have hn_eq : n = zetaL := L.subtype_injective hn_value
        have hzetaL_mem_N : zetaL ∈ N := hn_eq ▸ hnN
        have hzeta_lift_one : π zetaL = 1 :=
          (QuotientGroup.eq_one_iff (N := N) zetaL).2 hzetaL_mem_N
        have hzetaM_one : zetaM = 1 := by
          apply Subtype.ext
          calc
            (zetaM : L ⧸ N) = π zetaL := hzeta_lift.symm
            _ = 1 := hzeta_lift_one
            _ = (1 : M) := rfl
        apply hzeta0_ne
        have hzeta0_one := congrArg eA hzetaM_one
        simpa [zetaM] using hzeta0_one
      have hdelta_center : ((deltaL : L) : G) ∈
          (Subgroup.center F).map F.subtype := by
        rw [← hNLF]
        exact ⟨hdelta_mem_NL, hdelta_mem_F⟩
      have hdelta_mem_V : ((deltaL : L) : G) ∈ V :=
        (hNL_le ((hcore_mem deltaL).mp hdelta_mem_N)).2
      have hdelta_centralizes_CX : ((deltaL : L) : G) ∈
          Subgroup.centralizer (CX : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rcases hdelta_center with ⟨deltaF, hdeltaF_center, hdeltaF_value⟩
        let xL : L := ⟨x, hx.1⟩
        have hxF : x ∈ F := ⟨xL, hQX_le_FR hx.2, rfl⟩
        let xF : F := ⟨x, hxF⟩
        have hcommF := (Subgroup.mem_center_iff.mp hdeltaF_center) xF
        have hcommG := congrArg Subtype.val hcommF
        change x * (deltaF : G) = (deltaF : G) * x at hcommG
        have hdeltaF_value' : (deltaF : G) = ((deltaL : L) : G) :=
          hdeltaF_value
        rw [hdeltaF_value'] at hcommG
        exact hcommG
      have homega_mem_CX : ((omegaL : L) : G) ∈ CX := by
        exact ⟨omegaL.property, homegaL_mem_QX⟩
      have hgamma_mem_CX : ((gammaL : L) : G) ∈ CX := by
        exact ⟨gammaL.property, hgammaL_mem_QX⟩
      have hseed_ambient :
          t * ((omegaL : L) : G) * t =
            ((gammaL : L) : G) * (((zetaL : L) : G) ^ 3) * t *
              (((zetaL : L) : G)⁻¹ * ((omegaL : L) : G)⁻¹ *
                ((zetaL : L) : G)) * ((deltaL : L) : G) := by
        have hfactor : lhsL = rhsL * deltaL := by
          dsimp [deltaL]
          group
        simpa [lhsL, rhsL, tX] using congrArg L.subtype hfactor
      exact ⟨((omegaL : L) : G), ((gammaL : L) : G),
        ((zetaL : L) : G), ((deltaL : L) : G), homega_mem_CX,
        hgamma_mem_CX, hzeta_mem_F, hzeta_mem_V, hzeta_ne,
        hzeta_centralizes_CQ0, hzeta_not_center, hdelta_center, hdelta_mem_V,
        hdelta_centralizes_CX, homega_sq, hseed_ambient⟩
    have hCX_card : Nat.card CX = q ^ 3 := by
      have hQbar_card : Nat.card Qbar = Nat.card ΩX - 1 := by
        rcases hA1bar.point_stabilizer with ⟨α, hHbar⟩
        let β : ΩX := tbar⁻¹ • α
        have hA1stab :
            HypothesisA1 (L ⧸ N) ΩX
              (MulAction.stabilizer (L ⧸ N) α) Dbar Qbar tbar := by
          simpa only [hHbar] using hA1bar
        have hβ_ne : β ≠ α := by
          intro hβ
          apply hA1stab.t_not_mem_H
          change tbar • α = α
          have ht_inv : tbar⁻¹ = tbar :=
            hA1stab.involution_t.inv_eq_self
          simpa [β, ht_inv] using hβ
        have hDbar :
            Dbar = MulAction.stabilizer (L ⧸ N) α ⊓
              MulAction.stabilizer (L ⧸ N) β := by
          simpa [β, rightConjugate_stabilizer] using hA1stab.D_eq
        have hcard :=
          (hypothesisA1_Q_regular_on_complement hA1stab hβ_ne hDbar).ncard_eq
        have hcardQ :
            Nat.card Qbar = ({ω : ΩX | ω ≠ α} : Set ΩX).ncard := by
          simpa using hcard
        have hsum := Set.ncard_add_ncard_compl ({α} : Set ΩX)
        rw [Set.ncard_singleton] at hsum
        have hcompl :
            ({α} : Set ΩX)ᶜ = ({ω : ΩX | ω ≠ α} : Set ΩX) := by
          ext ω
          change (ω ≠ α) ↔ (ω ≠ α)
          rfl
        rw [hcompl, ← hcardQ] at hsum
        omega
      have hOmega_card : Nat.card ΩX = q ^ 3 + 1 := by
        have hmodel_card :=
          (External.huppert_II_10_12 J q hEcard hfixedCard hJstandard).1
        calc
          Nat.card ΩX = Nat.card _ := Nat.card_congr eΩ
          _ = q ^ 3 + 1 := hmodel_card
      calc
        Nat.card CX = Nat.card Qbar := Nat.card_congr eCXQbar.toEquiv
        _ = Nat.card ΩX - 1 := hQbar_card
        _ = q ^ 3 := by rw [hOmega_card]; omega
    have hCX_suzuki : IsSuzukiTwoGroup CX := by
      let Pmodel : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
        PM.mapSurjective (f := eM.toMonoidHom) eM.surjective
      let eCXModel : CX ≃* Pmodel :=
        eCXPM.trans
          (Subgroup.equivMapOfInjective (PM : Subgroup M)
            eM.toMonoidHom eM.injective)
      have hCX_power : ∃ n : ℕ, Nat.card (⊤ : Subgroup CX) = 2 ^ n := by
        have hCX_pgroup : IsPGroup 2 CX :=
          Pmodel.isPGroup'.of_equiv eCXModel.symm
        rcases hCX_pgroup.exists_card_eq with ⟨n, hn⟩
        exact ⟨n, by simpa using hn⟩
      have hCX_noncomm_source : ¬ IsMulCommutative CX := by
        rcases External.huppert_II_10_12 J q hEcard hfixedCard hJstandard with
          ⟨_hOmega_card, _rhoU, _pinf, _hrhoU_injective, _hnaturalU,
            _hU_card, hroot_exists, _htwo_transitive, _hG_card,
            _hthree_fixed⟩
        rcases hroot_exists with
          ⟨R, _HR, _hR_le_U, _hHR_le_U, _hU_normalizes_R,
            _hR_disjoint_HR, _hR_join_HR, _hHR_cyclic, hR_card,
            _hcommutator_center, hcommutator_card, _hHR_card,
            _hR_regular, _hcoord_exists, _hHR_coord,
            _hHR_coord_surjective⟩
        have hR_pgroup : IsPGroup 2 R := by
          rcases hq_power with ⟨n, hn⟩
          apply IsPGroup.of_card (n := n * 3)
          rw [hR_card, hn, pow_mul]
        have hR_noncomm : ¬ IsMulCommutative R := by
          intro hR_comm
          letI : IsMulCommutative R := hR_comm
          have hcommutator_bot : commutator R = ⊥ := by
            exact (commutator_eq_bot_iff_center_eq_top (G := R)).2
              Subgroup.center_eq_top
          have hcommutator_card_one : Nat.card (commutator R) = 1 := by
            rw [hcommutator_bot]
            simp
          have hq_one : q = 1 :=
            hcommutator_card.symm.trans hcommutator_card_one
          omega
        letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
          Finite.of_surjective eM eM.surjective
        obtain ⟨Pstd, hR_le_Pstd⟩ := hR_pgroup.exists_le_sylow
        have hPmodel_card : Nat.card Pmodel = q ^ 3 := by
          calc
            Nat.card Pmodel = Nat.card CX :=
              Nat.card_congr eCXModel.symm.toEquiv
            _ = q ^ 3 := hCX_card
        have hPstd_card : Nat.card Pstd = q ^ 3 := by
          calc
            Nat.card Pstd = Nat.card Pmodel :=
              Nat.card_congr (Sylow.equiv Pstd Pmodel).toEquiv
            _ = q ^ 3 := hPmodel_card
        have hR_eq_Pstd :
            R = (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
          Subgroup.eq_of_le_of_card_ge hR_le_Pstd (by
            rw [hPstd_card, hR_card])
        let eRCX : R ≃* CX :=
          (MulEquiv.subgroupCongr hR_eq_Pstd).trans
            ((Sylow.equiv Pstd Pmodel).trans eCXModel.symm)
        intro hCX_comm
        apply hR_noncomm
        refine { is_comm := ⟨?_⟩ }
        intro x y
        apply eRCX.injective
        simpa only [map_mul] using
          hCX_comm.is_comm.comm (eRCX x) (eRCX y)
      have hCX_two_involutions_source :
          ∃ x y : CX, IsInvolution x ∧ IsInvolution y ∧ x ≠ y := by
        have hcard_LQ0 : 2 < Nat.card ↥(L ⊓ Q0) := by
          rw [← hq_eq_Q0]
          exact hq_gt
        letI : Fintype ↥(L ⊓ Q0) := Fintype.ofFinite ↥(L ⊓ Q0)
        have hcardF : 2 < Fintype.card ↥(L ⊓ Q0) := by
          simpa [Fintype.card_eq_nat_card] using hcard_LQ0
        rcases Fintype.two_lt_card_iff.mp hcardF with
          ⟨a, b, c, hab, hac, hbc⟩
        have hexists_two_nonone :
            ∃ x y : ↥(L ⊓ Q0), (x : G) ≠ 1 ∧ (y : G) ≠ 1 ∧ x ≠ y := by
          by_cases ha : (a : G) = 1
          · refine ⟨b, c, ?_, ?_, hbc⟩
            · intro hb
              exact hab (Subtype.ext (ha.trans hb.symm))
            · intro hc
              exact hac (Subtype.ext (ha.trans hc.symm))
          · by_cases hb : (b : G) = 1
            · refine ⟨a, c, ha, ?_, hac⟩
              intro hc
              exact hbc (Subtype.ext (hb.trans hc.symm))
            · exact ⟨a, b, ha, hb, hab⟩
        rcases hexists_two_nonone with ⟨x0, y0, hx0_ne, hy0_ne, hxy0_ne⟩
        let toCX : ↥(L ⊓ Q0) → CX := fun z =>
          ⟨(z : G), ⟨z.property.1, hsec.section2.Q0_le_Q z.property.2⟩⟩
        have hinv_of_mem (z : ↥(L ⊓ Q0)) (hz_ne : (z : G) ≠ 1) :
            IsInvolution (toCX z) := by
          have hzQ0 : (z : G) ∈ Q0 := z.property.2
          rcases (hsec.section2.Q0_def (z : G)).mp hzQ0 with hz_one | hzHI
          · exact False.elim (hz_ne hz_one)
          · constructor
            · intro hcx_one
              exact hz_ne (congrArg Subtype.val hcx_one)
            · apply Subtype.ext
              exact hzHI.2.sq_eq_one
        refine ⟨toCX x0, toCX y0, hinv_of_mem x0 hx0_ne,
          hinv_of_mem y0 hy0_ne, ?_⟩
        intro hxy
        have hG : (x0 : G) = (y0 : G) := congrArg (fun z : CX => (z : G)) hxy
        exact hxy0_ne (Subtype.ext hG)
      have hCX_regular_action_source :
          ∃ (K : Type u) (_ : Group K) (_ : MulDistribMulAction K CX),
            IsCyclic K ∧ FaithfulSMul K CX ∧
              ActionRegularOn K CX (involutions CX) := by
        let Coord :=
          {z : E × E //
            z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}
        rcases External.huppert_II_10_12 J q hEcard hfixedCard hJstandard with
          ⟨_hOmega_card, _rhoU, _pinf, _hrhoU_injective, _hnaturalU,
            _hU_card, hroot_exists, _htwo_transitive, _hG_card,
            _hthree_fixed⟩
        rcases hroot_exists with
          ⟨R, _HR, _hR_le_U, _hHR_le_U, _hU_normalizes_R,
            _hR_disjoint_HR, _hR_join_HR, _hHR_cyclic, hR_card,
            _hcommutator_center, _hcommutator_card, _hHR_card,
            _hR_regular, hcoord_exists, _hHR_coord,
            _hHR_coord_surjective⟩
        let rGroup : Group R := Subgroup.toGroup R
        letI : Group R := rGroup
        letI : DivisionMonoid R := rGroup.toDivisionMonoid
        letI : LeftCancelMonoid R :=
          rGroup.toCancelMonoid.toLeftCancelMonoid
        rcases hcoord_exists with ⟨coordR, hcoord_matrix⟩
        have hR_pgroup : IsPGroup 2 R := by
          rcases hq_power with ⟨n, hn⟩
          apply IsPGroup.of_card (n := n * 3)
          rw [hR_card, hn, pow_mul]
        letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
          Finite.of_surjective eM eM.surjective
        obtain ⟨Pstd, hR_le_Pstd⟩ := hR_pgroup.exists_le_sylow
        have hPmodel_card : Nat.card Pmodel = q ^ 3 := by
          calc
            Nat.card Pmodel = Nat.card CX :=
              Nat.card_congr eCXModel.symm.toEquiv
            _ = q ^ 3 := hCX_card
        have hPstd_card : Nat.card Pstd = q ^ 3 := by
          calc
            Nat.card Pstd = Nat.card Pmodel :=
              Nat.card_congr (Sylow.equiv Pstd Pmodel).toEquiv
            _ = q ^ 3 := hPmodel_card
        have hR_eq_Pstd :
            R = (Pstd : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
          Subgroup.eq_of_le_of_card_ge hR_le_Pstd (by
            rw [hPstd_card, hR_card])
        let eRCX : R ≃* CX :=
          (MulEquiv.subgroupCongr hR_eq_Pstd).trans
            ((Sylow.equiv Pstd Pmodel).trans eCXModel.symm)

        letI : Fintype E := Fintype.ofFinite E
        have hq_even : Even q := by
          rcases hq_power with ⟨n, hn⟩
          have hnpos : 0 < n := by
            by_contra hn_not_pos
            have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn_not_pos
            subst n
            norm_num at hn
            omega
          rw [hn]
          exact Nat.even_pow.mpr ⟨even_two, ne_of_gt hnpos⟩
        have hE_even : Even (Fintype.card E) := by
          rw [Fintype.card_eq_nat_card, hEcard]
          exact hq_even.pow_of_ne_zero (by norm_num)
        have hcharE : ringChar E = 2 :=
          FiniteField.even_card_iff_char_two.mpr
            (Nat.even_iff.mp hE_even)
        letI : CharP E 2 := by
          rw [← hcharE]
          infer_instance

        let F0 : Subfield E := FixedBy.subfield E J.conj
        let K0 : Type u :=
          ULift.{u, 0} (Multiplicative (ZMod (Nat.card F0ˣ)))
        let eK : K0 ≃* F0ˣ :=
          MulEquiv.ulift.trans (zmodCyclicMulEquiv inferInstance)
        have hK0_cyclic : IsCyclic K0 :=
          eK.isCyclic.mpr inferInstance
        let coordZero : Coord := ⟨(0, 0), by simp⟩
        have hcoordMul_mem (z w : Coord) :
            let a := z.1.1 + w.1.1
            let b := z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1
            b + J.conj b + a * J.conj a = 0 := by
          dsimp
          rw [CharTwo.sub_eq_add]
          simp only [map_add, map_mul]
          rw [J.conj_involutive]
          have htwo : (2 : E) = 0 := CharTwo.two_eq_zero
          linear_combination z.property + w.property +
            (z.1.1 * J.conj w.1.1 + J.conj z.1.1 * w.1.1) * htwo
        let coordMul : Coord → Coord → Coord := fun z w =>
          ⟨(z.1.1 + w.1.1,
              z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1),
            hcoordMul_mem z w⟩
        have hcoord_zero : coordR coordZero = 1 := by
          rcases hcoord_matrix coordZero with ⟨M, hMval, hcoordM⟩
          have hM : M = 1 := by
            apply Units.ext
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [hMval, coordZero]
          apply Subtype.ext
          apply Subtype.ext
          change
            ((((coordR coordZero : R) :
                ProjectiveSpecialUnitaryMatrixGroup J) :
              Matrix.ProjGenLinGroup (Fin 3) E)) = 1
          rw [hcoordM, hM, map_one]
        have hcoord_mul (z w : Coord) :
            coordR (coordMul z w) = coordR z * coordR w := by
          rcases hcoord_matrix z with ⟨Mz, hMzval, hMz⟩
          rcases hcoord_matrix w with ⟨Mw, hMwval, hMw⟩
          rcases hcoord_matrix (coordMul z w) with
            ⟨Mzw, hMzwval, hMzw⟩
          have hMmul : Mz * Mw = Mzw := by
            apply Units.ext
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [hMzval, hMwval, hMzwval, coordMul,
                Matrix.mul_apply, Fin.sum_univ_three, map_add] <;>
              ring
          apply Subtype.ext
          apply Subtype.ext
          change
            ((((coordR (coordMul z w) : R) :
                ProjectiveSpecialUnitaryMatrixGroup J) :
              Matrix.ProjGenLinGroup (Fin 3) E)) =
            ((((coordR z : R) :
                ProjectiveSpecialUnitaryMatrixGroup J) :
              Matrix.ProjGenLinGroup (Fin 3) E)) *
            ((((coordR w : R) :
                ProjectiveSpecialUnitaryMatrixGroup J) :
              Matrix.ProjGenLinGroup (Fin 3) E))
          rw [hMzw, hMz, hMw, ← map_mul, hMmul]
        have hcoord_square_iff (z : Coord) :
            (coordR z) ^ 2 = 1 ↔ z.1.1 = 0 := by
          constructor
          · intro hsq
            have hcm : coordMul z z = coordZero := by
              apply coordR.injective
              rw [hcoord_mul, hcoord_zero]
              exact
                (@pow_two R rGroup.toMonoid (coordR z)).symm.trans hsq
            have hsecond :=
              congrArg (fun x : Coord => x.1.2) hcm
            have hprod : z.1.1 * J.conj z.1.1 = 0 := by
              dsimp only [coordMul, coordZero] at hsecond
              simpa [CharTwo.add_self_eq_zero] using hsecond
            rcases mul_eq_zero.mp hprod with ha | hconj
            · exact ha
            · apply J.conj.injective
              simpa only [map_zero] using hconj
          · intro ha
            have hcm : coordMul z z = coordZero := by
              apply Subtype.ext
              apply Prod.ext <;>
                simp [coordMul, coordZero, ha,
                  CharTwo.add_self_eq_zero]
            rw [pow_two, ← hcoord_mul, hcm, hcoord_zero]

        have hscaleCoord_mem (c : K0) (z : Coord) :
            let d : E := ((eK c : F0ˣ) : F0)
            let a := d * z.1.1
            let b := d ^ 2 * z.1.2
            b + J.conj b + a * J.conj a = 0 := by
          dsimp
          have hd :
              J.conj ((((eK c : F0ˣ) : F0) : E)) =
                (((eK c : F0ˣ) : F0) : E) :=
            ((eK c : F0ˣ) : F0).property
          simp only [map_mul, map_pow, hd]
          linear_combination
            ((((eK c : F0ˣ) : F0) : E) ^ 2) * z.property
        let scaleCoord : K0 → Coord → Coord := fun c z =>
          let d : E := ((eK c : F0ˣ) : F0)
          ⟨(d * z.1.1, d ^ 2 * z.1.2), hscaleCoord_mem c z⟩
        have hscaleCoord_one (z : Coord) : scaleCoord 1 z = z := by
          apply Subtype.ext
          simp [scaleCoord]
        have hscaleCoord_mul (c d : K0) (z : Coord) :
            scaleCoord (c * d) z = scaleCoord c (scaleCoord d z) := by
          apply Subtype.ext
          apply Prod.ext <;>
            simp [scaleCoord, map_mul, mul_pow, mul_assoc]
        have hscaleCoord_coordMul (c : K0) (z w : Coord) :
            scaleCoord c (coordMul z w) =
              coordMul (scaleCoord c z) (scaleCoord c w) := by
          apply Subtype.ext
          apply Prod.ext
          · dsimp only [scaleCoord, coordMul]
            ring
          · dsimp only [scaleCoord, coordMul]
            have hd :
                J.conj ((((eK c : F0ˣ) : F0) : E)) =
                  (((eK c : F0ˣ) : F0) : E) :=
              ((eK c : F0ˣ) : F0).property
            rw [map_mul, hd]
            ring

        let scaleR : K0 → R → R := fun c x =>
          coordR (scaleCoord c (coordR.symm x))
        have hscaleR_one_smul (x : R) : scaleR 1 x = x := by
          simp [scaleR, hscaleCoord_one]
        have hscaleR_mul_smul (c d : K0) (x : R) :
            scaleR (c * d) x = scaleR c (scaleR d x) := by
          simp [scaleR, hscaleCoord_mul]
        have hscaleR_mul (c : K0) (x y : R) :
            scaleR c (x * y) = scaleR c x * scaleR c y := by
          have hxy :
              coordR.symm (x * y) =
                coordMul (coordR.symm x) (coordR.symm y) := by
            apply coordR.injective
            simp only [Equiv.apply_symm_apply, hcoord_mul]
          simp [scaleR, hxy, hscaleCoord_coordMul, hcoord_mul]
        have hscaleR_one (c : K0) : scaleR c 1 = 1 := by
          have h := hscaleR_mul c 1 1
          have h' := congrArg
            (fun z : R => (scaleR c 1)⁻¹ * z) h
          have hone : (1 : R) = scaleR c 1 := by
            simpa [mul_assoc] using h'
          exact hone.symm
        let actionR : MulDistribMulAction K0 R :=
          { smul := scaleR
            one_smul := hscaleR_one_smul
            mul_smul := hscaleR_mul_smul
            smul_mul := hscaleR_mul
            smul_one := hscaleR_one }
        letI : MulDistribMulAction K0 R := actionR
        have hsmul_def (c : K0) (x : R) : c • x = scaleR c x := rfl
        have hR_action_preserves :
            ∀ x : R, x ∈ involutions R →
              ∀ c : K0, c • x ∈ involutions R := by
          intro x hx c
          change IsInvolution x at hx
          change IsInvolution (c • x)
          constructor
          · intro hcx
            apply hx.ne_one
            have hback :=
              congrArg (fun y : R => c⁻¹ • y) hcx
            change c⁻¹ • (c • x) = c⁻¹ • (1 : R) at hback
            rw [← mul_smul] at hback
            have hci : c⁻¹ * c = (1 : K0) := inv_mul_cancel c
            rw [hci, one_smul, smul_one] at hback
            exact hback
          · calc
              (c • x) ^ 2 = c • (x ^ 2) := by
                simp [pow_two, smul_mul']
              _ = 1 := by rw [hx.sq_eq_one, smul_one]
        have hR_action_existsUnique :
            ∀ x : R, x ∈ involutions R →
              ∀ y : R, y ∈ involutions R →
                ∃! c : K0, y = c • x := by
          intro x hx y hy
          change IsInvolution x at hx
          change IsInvolution y at hy
          let z : Coord := coordR.symm x
          let w : Coord := coordR.symm y
          have hinvolution_coord (r : R) (hr : IsInvolution r) :
              let v : Coord := coordR.symm r
              v.1.1 = 0 ∧ J.conj v.1.2 = v.1.2 ∧ v.1.2 ≠ 0 := by
            let v : Coord := coordR.symm r
            change v.1.1 = 0 ∧ J.conj v.1.2 = v.1.2 ∧ v.1.2 ≠ 0
            have hv_apply : coordR v = r := by
              simp [v]
            have hv_first : v.1.1 = 0 := by
              apply (hcoord_square_iff v).mp
              rw [hv_apply]
              exact hr.sq_eq_one
            have hv_fixed : J.conj v.1.2 = v.1.2 := by
              have hsum : v.1.2 + J.conj v.1.2 = 0 := by
                simpa [hv_first] using v.property
              have hneg : v.1.2 = -J.conj v.1.2 :=
                eq_neg_of_add_eq_zero_left hsum
              simpa only [CharTwo.neg_eq] using hneg.symm
            have hv_second : v.1.2 ≠ 0 := by
              intro hv2
              apply hr.ne_one
              have hv_zero : v = coordZero := by
                apply Subtype.ext
                apply Prod.ext
                · exact hv_first
                · exact hv2
              calc
                r = coordR v := hv_apply.symm
                _ = coordR coordZero := congrArg coordR hv_zero
                _ = 1 := hcoord_zero
            exact ⟨hv_first, hv_fixed, hv_second⟩
          rcases hinvolution_coord x hx with ⟨hz_first, hz_fixed, hz_second⟩
          rcases hinvolution_coord y hy with ⟨hw_first, hw_fixed, hw_second⟩
          let z0 : F0 := ⟨z.1.2, hz_fixed⟩
          let w0 : F0 := ⟨w.1.2, hw_fixed⟩
          have hz0_ne : z0 ≠ 0 := by
            intro hz0
            exact hz_second (congrArg Subtype.val hz0)
          have hw0_ne : w0 ≠ 0 := by
            intro hw0
            exact hw_second (congrArg Subtype.val hw0)
          let zu : F0ˣ := Units.mk0 z0 hz0_ne
          let wu : F0ˣ := Units.mk0 w0 hw0_ne
          have hsq_units_injective :
              Function.Injective (fun d : F0ˣ => d ^ 2) := by
            intro a b hab
            apply Units.ext
            apply CharTwo.sq_injective
            simpa using congrArg (fun d : F0ˣ => (d : F0)) hab
          have hsq_units_surjective :
              Function.Surjective (fun d : F0ˣ => d ^ 2) :=
            Finite.surjective_of_injective hsq_units_injective
          have hscaled_coord_iff (c : K0) :
              y = c • x ↔ (eK c) ^ 2 * zu = wu := by
            constructor
            · intro h
              rw [hsmul_def c x] at h
              have hsecond :=
                congrArg (fun r : R => (coordR.symm r).1.2) h
              apply Units.ext
              apply Subtype.ext
              simpa [actionR, scaleR, scaleCoord, z, w, zu, wu, z0, w0] using
                hsecond.symm
            · intro h
              have hval := congrArg
                (fun d : F0ˣ => (((d : F0) : E))) h
              apply coordR.symm.injective
              rw [hsmul_def c x]
              simp only [scaleR, Equiv.symm_apply_apply]
              apply Subtype.ext
              apply Prod.ext
              · simp [scaleCoord, hz_first, hw_first]
              · simpa [actionR, scaleR, scaleCoord, z, w, zu, wu, z0, w0] using
                  hval.symm
          obtain ⟨d, hd⟩ := hsq_units_surjective (wu * zu⁻¹)
          change d ^ 2 = wu * zu⁻¹ at hd
          have hd_action : y = (eK.symm d) • x := by
            apply (hscaled_coord_iff (eK.symm d)).2
            rw [eK.apply_symm_apply, hd]
            simp
          refine ⟨eK.symm d, hd_action, ?_⟩
          intro c hc
          apply eK.injective
          apply hsq_units_injective
          apply mul_right_cancel (b := zu)
          calc
            (eK c) ^ 2 * zu = wu := (hscaled_coord_iff c).mp hc
            _ = (eK (eK.symm d)) ^ 2 * zu :=
              (hscaled_coord_iff (eK.symm d)).mp hd_action |>.symm
        have hR_action_regular :
            ActionRegularOn K0 R (involutions R) :=
          ⟨hR_action_preserves, hR_action_existsUnique⟩

        let scaleCX : K0 → CX → CX := fun c x =>
          eRCX (c • eRCX.symm x)
        have hscaleCX_one_smul (x : CX) : scaleCX 1 x = x := by
          simp [scaleCX]
        have hscaleCX_mul_smul (c d : K0) (x : CX) :
            scaleCX (c * d) x = scaleCX c (scaleCX d x) := by
          simp [scaleCX, mul_smul]
        have hscaleCX_mul (c : K0) (x y : CX) :
            scaleCX c (x * y) = scaleCX c x * scaleCX c y := by
          apply eRCX.symm.injective
          simp [scaleCX, smul_mul']
        have hscaleCX_one (c : K0) : scaleCX c 1 = 1 := by
          apply eRCX.symm.injective
          simp [scaleCX]
        let actionCX : MulDistribMulAction K0 CX :=
          { smul := scaleCX
            one_smul := hscaleCX_one_smul
            mul_smul := hscaleCX_mul_smul
            smul_mul := hscaleCX_mul
            smul_one := hscaleCX_one }
        letI : MulDistribMulAction K0 CX := actionCX
        have hCX_action_regular :
            ActionRegularOn K0 CX (involutions CX) := by
          have hinvolution_symm :
              ∀ x : CX, IsInvolution x → IsInvolution (eRCX.symm x) := by
            intro x hx
            constructor
            · intro hone
              apply hx.ne_one
              calc
                x = eRCX (eRCX.symm x) := (eRCX.apply_symm_apply x).symm
                _ = eRCX 1 := congrArg eRCX hone
                _ = 1 := map_one eRCX
            · apply eRCX.injective
              simpa only [map_pow, map_one, eRCX.apply_symm_apply] using hx.sq_eq_one
          have hinvolution_apply :
              ∀ x : R, IsInvolution x → IsInvolution (eRCX x) := by
            intro x hx
            constructor
            · intro hone
              apply hx.ne_one
              have := congrArg eRCX.symm hone
              simpa only [eRCX.symm_apply_apply, map_one] using this
            · simpa only [map_pow, map_one] using congrArg eRCX hx.sq_eq_one
          constructor
          · intro x hx c
            change IsInvolution x at hx
            change IsInvolution (scaleCX c x)
            exact hinvolution_apply _
              (hR_action_regular.1 _ (hinvolution_symm x hx) c)
          · intro x hx y hy
            change IsInvolution x at hx
            change IsInvolution y at hy
            obtain ⟨c, hc, hc_unique⟩ :=
              hR_action_regular.2 (eRCX.symm x) (hinvolution_symm x hx)
                (eRCX.symm y) (hinvolution_symm y hy)
            refine ⟨c, ?_, ?_⟩
            · change y = scaleCX c x
              calc
                y = eRCX (eRCX.symm y) := (eRCX.apply_symm_apply y).symm
                _ = eRCX (c • eRCX.symm x) := congrArg eRCX hc
                _ = scaleCX c x := rfl
            · intro d hd
              apply hc_unique d
              change y = scaleCX d x at hd
              have hback := congrArg eRCX.symm hd
              simpa only [scaleCX, eRCX.symm_apply_apply] using hback
        have hCX_action_faithful : FaithfulSMul K0 CX := by
          rw [faithfulSMul_iff]
          intro c hc
          rcases hCX_two_involutions_source with
            ⟨x, _y, hx, _hy, _hxy⟩
          exact (hCX_action_regular.2 x hx x hx).unique
            (hc x).symm (by simp)
        exact ⟨K0, inferInstance, actionCX, hK0_cyclic,
          hCX_action_faithful, hCX_action_regular⟩
      exact ⟨hCX_power, hCX_noncomm_source, hCX_two_involutions_source,
        hCX_regular_action_source⟩
    exact ⟨E, inferInstance, inferInstance, J, hJstandard, hEcard, hfixedCard,
      hFmodel, hst, hCX_suzuki, hCX_card, hseed⟩

end PFchapter1section3
end CFSG.BenderSuzuki
