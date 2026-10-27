module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert-Blackburn XI.1.3(a)

The statement follows Volume III, physical page 170.  The natural projective
action and the inclusion of `PSL(2,K)` in `PGL(2,K)` are quantified directly;
no local action or recognition package is introduced.
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization
open scoped commutatorElement

universe u

public theorem huppertXI13_card_pgl2
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card (Matrix.GeneralLinearGroup.scalar (Fin 2)).range = Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalar_inj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := K))
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

private theorem huppertXI13_alternating_fin_three_regular :
    ∀ a b : Fin 3, ∃! g : alternatingGroup (Fin 3),
      (g : Equiv.Perm (Fin 3)) a = b := by
  classical
  letI : MulAction.IsPretransitive (alternatingGroup (Fin 3)) (Fin 3) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 3) (by simp)
  intro a b
  let orbit : alternatingGroup (Fin 3) → Fin 3 := fun g => g • a
  have horbit_surj : Function.Surjective orbit := by
    intro c
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
      (M := alternatingGroup (Fin 3)) a c
    exact ⟨g, hg⟩
  have hcard : Nat.card (alternatingGroup (Fin 3)) = Nat.card (Fin 3) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have horbit_inj : Function.Injective orbit :=
    ((Nat.bijective_iff_surjective_and_card orbit).2
      ⟨horbit_surj, hcard⟩).1
  obtain ⟨g, hg⟩ := horbit_surj b
  refine ⟨g, hg, ?_⟩
  intro h hh
  apply horbit_inj
  exact hh.trans hg.symm

private def huppertXI13_kleinFourPerm : Subgroup (Equiv.Perm (Fin 4)) :=
  (alternatingGroup.kleinFour (Fin 4)).map
    (alternatingGroup (Fin 4)).subtype

private theorem huppertXI13_kleinFourPerm_normal :
    huppertXI13_kleinFourPerm.Normal := by
  letI : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (by simp)
  change ((alternatingGroup.kleinFour (Fin 4)).map
    (alternatingGroup (Fin 4)).subtype).Normal
  infer_instance

private theorem huppertXI13_kleinFourPerm_regular :
    ∀ a b : Fin 4, ∃! g : huppertXI13_kleinFourPerm,
      (g : Equiv.Perm (Fin 4)) a = b := by
  classical
  have hfix : ∀ (g : huppertXI13_kleinFourPerm) (a : Fin 4),
      (g : Equiv.Perm (Fin 4)) a = a → g = 1 := by
    intro g a hga
    rcases g.property with ⟨k, hk, hkg⟩
    have hk' : k = 1 ∨
        (k : Equiv.Perm (Fin 4)).cycleType = {2, 2} := by
      have hset := alternatingGroup.coe_kleinFour_of_card_eq_four
        (α := Fin 4) (by simp)
      rw [Set.ext_iff] at hset
      have := (hset k).mp hk
      simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
        Subgroup.coe_one, Subgroup.mk_eq_one] using this
    rcases hk' with rfl | hkcycle
    · apply Subtype.ext
      simpa using hkg.symm
    · have hsupport_card :
          (k : Equiv.Perm (Fin 4)).support.card = 4 := by
        rw [← Equiv.Perm.sum_cycleType, hkcycle]
        norm_num
      have hsupport : (k : Equiv.Perm (Fin 4)).support = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simp [hsupport_card]
      have ha_support : a ∈ (k : Equiv.Perm (Fin 4)).support := by
        rw [hsupport]
        exact Finset.mem_univ a
      rw [Equiv.Perm.mem_support] at ha_support
      have hkg_a := congrArg (fun p : Equiv.Perm (Fin 4) => p a) hkg
      exact (ha_support (hkg_a.trans hga)).elim
  intro a b
  let orbit : huppertXI13_kleinFourPerm → Fin 4 := fun g => g.1 a
  have horbit_inj : Function.Injective orbit := by
    intro g h hgh
    change (g : Equiv.Perm (Fin 4)) a =
      (h : Equiv.Perm (Fin 4)) a at hgh
    have hfix_quot : ((h⁻¹ * g : huppertXI13_kleinFourPerm) :
        Equiv.Perm (Fin 4)) a = a := by
      change (h : Equiv.Perm (Fin 4))⁻¹ ((g : Equiv.Perm (Fin 4)) a) = a
      rw [hgh]
      exact (h : Equiv.Perm (Fin 4)).symm_apply_apply a
    have hone := hfix (h⁻¹ * g) a hfix_quot
    exact (inv_mul_eq_one.mp hone).symm
  let incl : alternatingGroup.kleinFour (Fin 4) →*
      Equiv.Perm (Fin 4) :=
    (alternatingGroup (Fin 4)).subtype.comp
      (alternatingGroup.kleinFour (Fin 4)).subtype
  have hrange : incl.range = huppertXI13_kleinFourPerm := by
    ext g
    simp [incl, huppertXI13_kleinFourPerm]
  let eV : alternatingGroup.kleinFour (Fin 4) ≃*
      huppertXI13_kleinFourPerm :=
    (MulEquiv.ofBijective incl.rangeRestrict
      ⟨fun x y hxy => by
          apply Subtype.ext
          apply Subtype.ext
          simpa [incl] using congrArg Subtype.val hxy,
        MonoidHom.rangeRestrict_surjective incl⟩).trans
      (MulEquiv.subgroupCongr hrange)
  have hcard : Nat.card huppertXI13_kleinFourPerm = Nat.card (Fin 4) := by
    rw [← Nat.card_congr eV.toEquiv,
      alternatingGroup.kleinFour_card_of_card_eq_four (by simp), Nat.card_fin]
  have horbit_surj : Function.Surjective orbit :=
    ((Nat.bijective_iff_injective_and_card orbit).2
      ⟨horbit_inj, hcard⟩).2
  obtain ⟨g, hg⟩ := horbit_surj b
  refine ⟨g, hg, ?_⟩
  intro h hh
  apply horbit_inj
  simpa [orbit] using hh.trans hg.symm

private theorem huppertXI13_pullback_regular
    {G X Y : Type*} [Group G] [Nontrivial Y]
    (rho : G →* Equiv.Perm X) (e : X ≃ Y)
    (act : G →* Equiv.Perm Y)
    (hact_apply : ∀ (g : G) (x : X), act g (e x) = e (rho g x))
    (hact_bij : Function.Bijective act)
    (S : Subgroup (Equiv.Perm Y)) (hSnormal : S.Normal)
    (hSregular : ∀ a b : Y, ∃! s : S, (s : Equiv.Perm Y) a = b) :
    ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
      ∀ a b : X, ∃! r : R, rho (r : G) a = b := by
  classical
  let R : Subgroup G := S.comap act
  have hRnormal : R.Normal := hSnormal.comap act
  have hRne : R ≠ ⊥ := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne Y
    obtain ⟨s, hs, _⟩ := hSregular a b
    obtain ⟨g, hg⟩ := hact_bij.2 (s : Equiv.Perm Y)
    have hgR : g ∈ R := by
      change act g ∈ S
      rw [hg]
      exact s.property
    intro hRbot
    have hg_one : g = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hRbot]
      exact hgR
    have hs_one : (s : Equiv.Perm Y) = 1 := by
      rw [← hg, hg_one, map_one]
    apply hab
    simpa [hs_one] using hs
  refine ⟨R, hRnormal, hRne, ?_⟩
  intro a b
  obtain ⟨s, hs, hs_unique⟩ := hSregular (e a) (e b)
  obtain ⟨g, hg⟩ := hact_bij.2 (s : Equiv.Perm Y)
  have hgR : g ∈ R := by
    change act g ∈ S
    rw [hg]
    exact s.property
  refine ⟨⟨g, hgR⟩, ?_, ?_⟩
  · apply e.injective
    rw [← hact_apply, hg]
    exact hs
  · intro r hr
    let sr : S := ⟨act (r : G), r.property⟩
    have hsr : (sr : Equiv.Perm Y) (e a) = e b := by
      change act (r : G) (e a) = e b
      rw [hact_apply]
      exact congrArg e hr
    have hsreq : sr = s := hs_unique sr hsr
    apply Subtype.ext
    apply hact_bij.1
    calc
      act (r : G) = (s : Equiv.Perm Y) := congrArg Subtype.val hsreq
      _ = act g := hg.symm

/-- Huppert-Blackburn XI.1.3(a), the projective-line example. -/
public theorem huppert_blackburn_XI_example_1_3_a
    (K : Type u) [Field K] [Finite K] :
    let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
    let PSL2 := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K
    let Omega := ℙ K (Fin 2 → K)
    Nat.card Omega = Nat.card K + 1 ∧
    ∃ (rho : PGL2 →* Equiv.Perm Omega)
        (iota : PSL2 →* PGL2),
      Function.Injective rho ∧ Function.Injective iota ∧
      (∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
        iota (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A) =
            Matrix.ProjGenLinGroup.mk (A : GL (Fin 2) K)) ∧
      (∀ (g : PGL2) (z : Omega) (A : GL (Fin 2) K),
        Matrix.ProjGenLinGroup.mk A = g →
          rho g z =
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) ∧
      iota.range.Normal ∧ (iota.range.index = 1 ∨ iota.range.index = 2) ∧
      (∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : PGL2,
          rho g a = a' ∧ rho g b = b' ∧ rho g c = c') ∧
      (3 < Nat.card K →
        IsSimpleGroup PSL2 ∧
        (∃ x y : PSL2, x * y ≠ y * x) ∧
        ¬ ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b) ∧
      (Nat.card K = 2 →
        Nonempty (PGL2 ≃* Equiv.Perm (Fin 3)) ∧
        ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b) ∧
      (Nat.card K = 3 →
        Nonempty (PGL2 ≃* Equiv.Perm (Fin 4)) ∧
        ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b) := by
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let PSL2 := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K
  let Omega := ℙ K (Fin 2 → K)
  change Nat.card Omega = Nat.card K + 1 ∧
    ∃ (rho : PGL2 →* Equiv.Perm Omega) (iota : PSL2 →* PGL2),
      Function.Injective rho ∧ Function.Injective iota ∧
      (∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
        iota (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A) =
            Matrix.ProjGenLinGroup.mk (A : GL (Fin 2) K)) ∧
      (∀ (g : PGL2) (z : Omega) (A : GL (Fin 2) K),
        Matrix.ProjGenLinGroup.mk A = g →
          rho g z =
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) ∧
      iota.range.Normal ∧ (iota.range.index = 1 ∨ iota.range.index = 2) ∧
      (∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : PGL2,
          rho g a = a' ∧ rho g b = b' ∧ rho g c = c') ∧
      (3 < Nat.card K →
        IsSimpleGroup PSL2 ∧
        (∃ x y : PSL2, x * y ≠ y * x) ∧
        ¬ ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b) ∧
      (Nat.card K = 2 →
        Nonempty (PGL2 ≃* Equiv.Perm (Fin 3)) ∧
        ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b) ∧
      (Nat.card K = 3 →
        Nonempty (PGL2 ≃* Equiv.Perm (Fin 4)) ∧
        ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b)
  have hprojective_line_card : Nat.card Omega = Nat.card K + 1 := by
    apply Projectivization.card_of_finrank_two
    simp
  have hnatural_maps :
      ∃ (rho : PGL2 →* Equiv.Perm Omega) (iota : PSL2 →* PGL2),
        Function.Injective rho ∧ Function.Injective iota ∧
        (∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
          iota (QuotientGroup.mk'
            (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A) =
              Matrix.ProjGenLinGroup.mk (A : GL (Fin 2) K)) ∧
        (∀ (g : PGL2) (z : Omega) (A : GL (Fin 2) K),
          Matrix.ProjGenLinGroup.mk A = g →
            rho g z =
              (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) := by
    classical
    let GL2 := GL (Fin 2) K
    let SL2m := Matrix.SpecialLinearGroup (Fin 2) K
    letI : MulAction GL2 Omega :=
      MulAction.compHom Omega
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
    have hscalar (u : Kˣ) (z : Omega) :
        Matrix.GeneralLinearGroup.scalar (Fin 2) u • z = z := by
      induction z using Projectivization.ind with
      | h v hv =>
          change Matrix.GeneralLinearGroup.toLin
            (Matrix.GeneralLinearGroup.scalar (Fin 2) u) •
              Projectivization.mk K v hv = Projectivization.mk K v hv
          rw [Projectivization.smul_mk]
          apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
          refine ⟨(u : K), ?_⟩
          change (u : K) • v = Matrix.mulVecLin
            (Matrix.GeneralLinearGroup.scalar (Fin 2) u) v
          ext i
          simp [Matrix.GeneralLinearGroup.scalar, Matrix.mulVecLin,
            Matrix.mulVec_diagonal]
    let glPerm : GL2 →* Equiv.Perm Omega := MulAction.toPermHom GL2 Omega
    have hscalar_perm :
        glPerm.comp (Matrix.GeneralLinearGroup.scalar (Fin 2)) = 1 := by
      ext u z
      exact hscalar u z
    let rho : PGL2 →* Equiv.Perm Omega :=
      Matrix.ProjGenLinGroup.lift glPerm hscalar_perm
    have hrho : Function.Injective rho := by
      rw [← MonoidHom.ker_eq_bot_iff]
      ext g
      constructor
      · intro hg
        rcases Matrix.ProjGenLinGroup.mk_surjective g with ⟨A, rfl⟩
        rw [MonoidHom.mem_ker] at hg
        have hperm : glPerm A = 1 := by
          change Matrix.ProjGenLinGroup.lift glPerm hscalar_perm
            (Matrix.ProjGenLinGroup.mk A) = 1 at hg
          simpa only [Matrix.ProjGenLinGroup.lift_mk] using hg
        have hfix : ∀ z : Omega, A • z = z := by
          intro z
          have hz := congrArg (fun f : Equiv.Perm Omega => f z) hperm
          simpa [glPerm] using hz
        have hcolinear :
            ∀ v : Fin 2 → K,
              ¬ LinearIndependent K
                ![v, (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v] := by
          intro v
          by_cases hv : v = 0
          · subst v
            intro hli
            exact (hli.ne_zero 0) rfl
          · rw [LinearIndependent.pair_iff' hv]
            simp only [not_forall, not_not]
            have hp := hfix (Projectivization.mk K v hv)
            change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
              Projectivization.mk K v hv = Projectivization.mk K v hv at hp
            rw [Projectivization.smul_mk,
              Projectivization.mk_eq_mk_iff'] at hp
            exact hp
        obtain ⟨c, hc⟩ :=
          LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
            (f := (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.toLinearMap)
            hcolinear
        rw [Subgroup.mem_bot]
        rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
        apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
        refine ⟨c, ?_⟩
        change Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) K) =
          c • LinearMap.id at hc
        rw [← Matrix.toLin'_apply'] at hc
        have hm := congrArg LinearMap.toMatrix' hc
        have hm' : (A : Matrix (Fin 2) (Fin 2) K) =
            c • (1 : Matrix (Fin 2) (Fin 2) K) := by
          simpa [Matrix.GeneralLinearGroup.coe_toLin,
            LinearMap.toMatrix_id] using hm
        calc
          Matrix.scalar (Fin 2) c =
              c • (1 : Matrix (Fin 2) (Fin 2) K) := by
            simpa using (Matrix.smul_one_eq_diagonal
              (m := Fin 2) c).symm
          _ = (A : Matrix (Fin 2) (Fin 2) K) := hm'.symm
      · intro hg
        rw [Subgroup.mem_bot] at hg
        simp [hg]
    have hcenter_map :
        Subgroup.center SL2m ≤
          (Subgroup.center GL2).comap Matrix.SpecialLinearGroup.toGL := by
      intro A hA
      change Matrix.SpecialLinearGroup.toGL A ∈ Subgroup.center GL2
      apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
      rcases Matrix.SpecialLinearGroup.mem_center_iff.mp hA with
        ⟨c, _hc, hAc⟩
      exact ⟨c, by simpa using hAc⟩
    let slToPGL : SL2m →* PGL2 :=
      Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL
    have hcenter_ker : Subgroup.center SL2m ≤ slToPGL.ker := by
      intro A hA
      rw [MonoidHom.mem_ker]
      change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) = 1
      rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
      exact hcenter_map hA
    let iota : PSL2 →* PGL2 :=
      QuotientGroup.lift (Subgroup.center SL2m) slToPGL hcenter_ker
    obtain ⟨rhoPSL, hrhoPSL, hrhoPSL_apply, _⟩ :=
      huppert_II_6_11_projective_action (K := K) 2 (by omega)
    have hcompat (x : PSL2) : rho (iota x) = rhoPSL x := by
      induction x using QuotientGroup.induction_on with
      | _ A =>
          change rho (iota (QuotientGroup.mk' (Subgroup.center SL2m) A)) =
            rhoPSL (QuotientGroup.mk' (Subgroup.center SL2m) A)
          apply Equiv.ext
          intro z
          rw [show iota (QuotientGroup.mk' (Subgroup.center SL2m) A) =
            slToPGL A from QuotientGroup.lift_mk' _ hcenter_ker A,
            hrhoPSL_apply]
          change rho (Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL A)) z = _
          rw [show rho (Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL A)) =
              glPerm (Matrix.SpecialLinearGroup.toGL A) by
                exact Matrix.ProjGenLinGroup.lift_mk hscalar_perm _]
          rfl
    have hiota : Function.Injective iota := by
      intro x y hxy
      apply hrhoPSL
      rw [← hcompat x, ← hcompat y, hxy]
    refine ⟨rho, iota, hrho, hiota, ?_, ?_⟩
    · intro A
      change iota (QuotientGroup.mk' (Subgroup.center SL2m) A) =
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A)
      exact QuotientGroup.lift_mk' _ hcenter_ker A
    · intro g z A hA
      subst g
      rw [show rho (Matrix.ProjGenLinGroup.mk A) = glPerm A by
        exact Matrix.ProjGenLinGroup.lift_mk hscalar_perm A]
      rfl
  rcases hnatural_maps with ⟨rho, iota, hrho, hiota, hiota_apply, hrho_apply⟩
  have hPSL_normal : iota.range.Normal := by
    constructor
    intro x hx g
    rcases hx with ⟨y, rfl⟩
    rcases QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) y with ⟨B, rfl⟩
    rcases Matrix.ProjGenLinGroup.mk_surjective g with ⟨A, rfl⟩
    let Cgl : GL (Fin 2) K :=
      A * Matrix.SpecialLinearGroup.toGL B * A⁻¹
    have hCdet : Matrix.det (Cgl : Matrix (Fin 2) (Fin 2) K) = 1 := by
      simp [Cgl, Matrix.GeneralLinearGroup.det_ne_zero A]
    let C : Matrix.SpecialLinearGroup (Fin 2) K := ⟨(Cgl : Matrix _ _ K), hCdet⟩
    refine ⟨QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) C, ?_⟩
    rw [hiota_apply]
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL C) =
      Matrix.ProjGenLinGroup.mk A *
        iota (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) B) *
        (Matrix.ProjGenLinGroup.mk A)⁻¹
    rw [hiota_apply, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg Matrix.ProjGenLinGroup.mk
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  have hPSL_index : iota.range.index = 1 ∨ iota.range.index = 2 := by
    classical
    let GL2 := GL (Fin 2) K
    letI : Fintype K := Fintype.ofFinite K
    let SL2m := Matrix.SpecialLinearGroup (Fin 2) K
    let centerGL := Subgroup.center GL2
    let centerSL := Subgroup.center SL2m
    have hscalar_inj : Function.Injective
        (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
      intro x y hxy
      apply Units.ext
      have h := congrArg (fun A : GL2 =>
        ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
      simpa [Matrix.GeneralLinearGroup.scalar] using h
    have hcenterGLcard : Nat.card centerGL = Nat.card K - 1 := by
      dsimp [centerGL, GL2]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      calc
        Nat.card (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
            Nat.card Kˣ :=
          (Nat.card_congr (Equiv.ofInjective
            (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalar_inj)).symm
        _ = Nat.card K - 1 := by
          simpa [Nat.card_eq_fintype_card] using
            (Fintype.card_units (α := K))
    have hGLcard : Nat.card GL2 =
        (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
      simpa [GL2, Fin.prod_univ_two] using
        (Matrix.card_GL_field (𝔽 := K) 2)
    let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
    have hmk_range : mkPGL.range = ⊤ :=
      MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
    have hPGLindex : centerGL.index = Nat.card PGL2 := by
      calc
        centerGL.index = mkPGL.ker.index := by
          rw [Matrix.ProjGenLinGroup.ker_mk]
        _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
        _ = Nat.card PGL2 := by rw [hmk_range]; simp
    have hqsub_pos : 0 < Nat.card K - 1 :=
      Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K))
    have hPGLcard : Nat.card PGL2 =
        Nat.card K * (Nat.card K ^ 2 - 1) := by
      have hmul := centerGL.index_mul_card
      rw [hPGLindex, hcenterGLcard, hGLcard] at hmul
      have hdiff : Nat.card K ^ 2 - Nat.card K =
          Nat.card K * (Nat.card K - 1) := by
        rw [pow_two]
        calc
          Nat.card K * Nat.card K - Nat.card K =
              Nat.card K * Nat.card K - Nat.card K * 1 := by simp
          _ = Nat.card K * (Nat.card K - 1) :=
            (Nat.mul_sub_left_distrib _ _ _).symm
      rw [hdiff] at hmul
      apply Nat.eq_of_mul_eq_mul_left hqsub_pos
      calc
        (Nat.card K - 1) * Nat.card PGL2 =
            Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
        _ = (Nat.card K ^ 2 - 1) *
            (Nat.card K * (Nat.card K - 1)) := hmul
        _ = (Nat.card K - 1) *
            (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring
    have hPGL_eq_SL : Nat.card PGL2 = Nat.card SL2m := by
      rw [hPGLcard, huppert614_card_specialLinearGroup]
    have hiota_card : Nat.card iota.range = Nat.card PSL2 :=
      (Nat.card_congr (Equiv.ofInjective iota hiota)).symm
    have hidxmul := iota.range.index_mul_card
    rw [hiota_card, hPGL_eq_SL] at hidxmul
    have hpslmul := huppert614_card_psl_mul_center (K := K)
    have hidxeq : iota.range.index = Nat.card centerSL := by
      apply Nat.eq_of_mul_eq_mul_left (Finite.card_pos (α := PSL2))
      calc
        Nat.card PSL2 * iota.range.index =
            iota.range.index * Nat.card PSL2 := by ac_rfl
        _ = Nat.card SL2m := hidxmul
        _ = Nat.card K * (Nat.card K ^ 2 - 1) :=
          huppert614_card_specialLinearGroup
        _ = Nat.card PSL2 * Nat.card centerSL := hpslmul.symm
    by_cases hneg : (-1 : K) = 1
    · left
      rw [hidxeq, huppert614_card_center_of_neg_one_eq_one hneg]
    · right
      rw [hidxeq, huppert614_card_center_of_neg_one_ne_one hneg]
  have hsharply_three_transitive :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : PGL2,
          rho g a = a' ∧ rho g b = b' ∧ rho g c = c' := by
    classical
    intro a b c a' b' c' hab hac hbc ha'b' ha'c' hb'c'
    have hfix_three (g : PGL2)
        (hga : rho g a = a) (hgb : rho g b = b) (hgc : rho g c = c) :
        g = 1 := by
      rcases Matrix.ProjGenLinGroup.mk_surjective g with ⟨M, rfl⟩
      let eM := (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv
      have haP : eM • a = a := by
        rw [← hrho_apply (Matrix.ProjGenLinGroup.mk M) a M rfl]
        exact hga
      have hbP : eM • b = b := by
        rw [← hrho_apply (Matrix.ProjGenLinGroup.mk M) b M rfl]
        exact hgb
      have hcP : eM • c = c := by
        rw [← hrho_apply (Matrix.ProjGenLinGroup.mk M) c M rfl]
        exact hgc
      have haS : ∃ s : Kˣ, s • a.rep = eM a.rep := by
        rw [← Projectivization.mk_rep a] at haP
        rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at haP
        exact haP
      have hbS : ∃ s : Kˣ, s • b.rep = eM b.rep := by
        rw [← Projectivization.mk_rep b] at hbP
        rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hbP
        exact hbP
      have hcS : ∃ s : Kˣ, s • c.rep = eM c.rep := by
        rw [← Projectivization.mk_rep c] at hcP
        rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hcP
        exact hcP
      rcases haS with ⟨sa, hsa⟩
      rcases hbS with ⟨sb, hsb⟩
      rcases hcS with ⟨sc, hsc⟩
      have hli : LinearIndependent K ![a.rep, b.rep] := by
        have hi : Projectivization.Independent ![a, b] :=
          (Projectivization.independent_pair_iff_ne a b).2 hab
        rw [Projectivization.independent_iff] at hi
        have hrep : Projectivization.rep ∘ ![a, b] = ![a.rep, b.rep] := by
          ext i
          fin_cases i <;> rfl
        rw [← hrep]
        exact hi
      let ba : Module.Basis (Fin 2) K (Fin 2 → K) :=
        basisOfPiSpaceOfLinearIndependent hli
      have hba : (ba : Fin 2 → (Fin 2 → K)) = ![a.rep, b.rep] := by
        exact coe_basisOfPiSpaceOfLinearIndependent hli
      let p : K := ba.repr c.rep 0
      let q : K := ba.repr c.rep 1
      have hcdecomp : p • a.rep + q • b.rep = c.rep := by
        rw [← ba.sum_repr c.rep, Fin.sum_univ_two]
        simp [p, q, hba]
      have hp : p ≠ 0 := by
        intro hp0
        have hcspan : q • b.rep = c.rep := by simpa [hp0] using hcdecomp
        have hcb : c = b := by
          rw [← Projectivization.mk_rep c, ← Projectivization.mk_rep b]
          exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).2 ⟨q, hcspan⟩
        exact hbc hcb.symm
      have hq : q ≠ 0 := by
        intro hq0
        have hcspan : p • a.rep = c.rep := by simpa [hq0] using hcdecomp
        have hca : c = a := by
          rw [← Projectivization.mk_rep c, ← Projectivization.mk_rep a]
          exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).2 ⟨p, hcspan⟩
        exact hac hca.symm
      change (sa : K) • a.rep = eM a.rep at hsa
      change (sb : K) • b.rep = eM b.rep at hsb
      change (sc : K) • c.rep = eM c.rep at hsc
      have hrel :
          p • ((sa : K) • a.rep) + q • ((sb : K) • b.rep) =
            (sc : K) • (p • a.rep + q • b.rep) := by
        calc
          p • ((sa : K) • a.rep) + q • ((sb : K) • b.rep) =
              p • eM a.rep + q • eM b.rep := by rw [hsa, hsb]
          _ = eM (p • a.rep + q • b.rep) := by simp
          _ = eM c.rep := by rw [hcdecomp]
          _ = (sc : K) • c.rep := hsc.symm
          _ = (sc : K) • (p • a.rep + q • b.rep) := by rw [hcdecomp]
      have hsa_sc : (sa : K) = (sc : K) := by
        have h0 := congrArg (fun v => ba.repr v 0) hrel
        have hba0 : ba 0 = a.rep := by simp [hba]
        have hba1 : ba 1 = b.rep := by simp [hba]
        simp [map_add, map_smul, ← hba0, ← hba1, p, q] at h0
        exact mul_left_cancel₀ hp (h0.trans (mul_comm _ _))
      have hsb_sc : (sb : K) = (sc : K) := by
        have h1 := congrArg (fun v => ba.repr v 1) hrel
        have hba0 : ba 0 = a.rep := by simp [hba]
        have hba1 : ba 1 = b.rep := by simp [hba]
        simp [map_add, map_smul, ← hba0, ← hba1, p, q] at h1
        exact mul_left_cancel₀ hq (h1.trans (mul_comm _ _))
      have hsa_sb : sa = sb := by
        apply Units.ext
        exact hsa_sc.trans hsb_sc.symm
      have heM : eM.toLinearMap = (sa : K) • LinearMap.id := by
        apply ba.ext
        intro i
        fin_cases i
        · simpa [hba] using hsa.symm
        · simpa [hba, hsa_sb] using hsb.symm
      rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
      apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
      refine ⟨(sa : K), ?_⟩
      change Matrix.scalar (Fin 2) (sa : K) =
        (M : Matrix (Fin 2) (Fin 2) K)
      change Matrix.mulVecLin (M : Matrix (Fin 2) (Fin 2) K) =
        (sa : K) • LinearMap.id at heM
      rw [← Matrix.toLin'_apply'] at heM
      have hm := congrArg LinearMap.toMatrix' heM
      simpa [LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal] using hm.symm
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype Omega := Fintype.ofFinite Omega
    let source : Fin 3 ↪ Omega :=
      ⟨![a, b, c], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all⟩
    let target : Fin 3 ↪ Omega :=
      ⟨![a', b', c'], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all⟩
    let orbit : PGL2 → (Fin 3 ↪ Omega) := fun g =>
      source.trans (rho g).toEmbedding
    have horbit_inj : Function.Injective orbit := by
      intro g h hgh
      have hga : rho g a = rho h a := by
        have h_eq := congrArg (fun e : Fin 3 ↪ Omega => e 0) hgh
        change rho g a = rho h a at h_eq
        exact h_eq
      have hgb : rho g b = rho h b := by
        have h_eq := congrArg (fun e : Fin 3 ↪ Omega => e 1) hgh
        change rho g b = rho h b at h_eq
        exact h_eq
      have hgc : rho g c = rho h c := by
        have h_eq := congrArg (fun e : Fin 3 ↪ Omega => e 2) hgh
        change rho g c = rho h c at h_eq
        exact h_eq
      have hfix_a : rho (h⁻¹ * g) a = a := by
        rw [map_mul, map_inv]
        change (rho h)⁻¹ (rho g a) = a
        rw [hga]
        exact (rho h).symm_apply_apply a
      have hfix_b : rho (h⁻¹ * g) b = b := by
        rw [map_mul, map_inv]
        change (rho h)⁻¹ (rho g b) = b
        rw [hgb]
        exact (rho h).symm_apply_apply b
      have hfix_c : rho (h⁻¹ * g) c = c := by
        rw [map_mul, map_inv]
        change (rho h)⁻¹ (rho g c) = c
        rw [hgc]
        exact (rho h).symm_apply_apply c
      exact (inv_mul_eq_one.mp
        (hfix_three (h⁻¹ * g) hfix_a hfix_b hfix_c)).symm
    have hq_two : 2 ≤ Nat.card K :=
      (Finite.one_lt_card (α := K))
    have hcard : Nat.card PGL2 = Nat.card (Fin 3 ↪ Omega) := by
      rw [huppertXI13_card_pgl2]
      have hEmbCard : Nat.card (Fin 3 ↪ Omega) =
          Fintype.card (Fin 3 ↪ Omega) := Nat.card_eq_fintype_card
      rw [hEmbCard, Fintype.card_embedding_eq, Fintype.card_fin]
      have hOmegaCard : Fintype.card Omega = Nat.card Omega :=
        Nat.card_eq_fintype_card.symm
      rw [hOmegaCard, hprojective_line_card]
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one]
      have hsub_one : Nat.card K + 1 - 1 = Nat.card K := by omega
      have hsub_two : Nat.card K + 1 - 2 = Nat.card K - 1 := by omega
      rw [hsub_one, hsub_two]
      have hfactor : Nat.card K ^ 2 - 1 =
          (Nat.card K - 1) * (Nat.card K + 1) := by
        let r := Nat.card K - 1
        have hqeq : Nat.card K = r + 1 := by
          dsimp [r]
          omega
        rw [hqeq]
        simp only [Nat.add_sub_cancel]
        apply (tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' 2 r)).2
        ring
      rw [hfactor]
      simp only [Nat.sub_zero]
      ac_rfl
    have horbit_surj : Function.Surjective orbit :=
      ((Nat.bijective_iff_injective_and_card orbit).2
        ⟨horbit_inj, hcard⟩).2
    obtain ⟨g, hg⟩ := horbit_surj target
    refine ⟨g, ?_, ?_⟩
    · have h0 := congrArg (fun e : Fin 3 ↪ Omega => e 0) hg
      have h1 := congrArg (fun e : Fin 3 ↪ Omega => e 1) hg
      have h2 := congrArg (fun e : Fin 3 ↪ Omega => e 2) hg
      change rho g a = a' at h0
      change rho g b = b' at h1
      change rho g c = c' at h2
      exact And.intro h0 (And.intro h1 h2)
    · intro h hh
      apply horbit_inj
      rw [hg]
      ext i
      fin_cases i
      · change rho h a = a'
        exact hh.1
      · change rho h b = b'
        exact hh.2.1
      · change rho h c = c'
        exact hh.2.2
  have hlarge_field :
      3 < Nat.card K →
        IsSimpleGroup PSL2 ∧
        (∃ x y : PSL2, x * y ≠ y * x) ∧
        ¬ ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b := by
    intro hK
    classical
    have hsimple : IsSimpleGroup PSL2 :=
      huppert_II_6_13 2 (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    letI : IsSimpleGroup PSL2 := hsimple
    obtain ⟨rhoPSL, hrhoPSL, hrhoPSL_apply, htwo⟩ :=
      huppert_II_6_11_projective_action (K := K) 2 (by omega)
    have hcompat (x : PSL2) : rho (iota x) = rhoPSL x := by
      rcases QuotientGroup.mk'_surjective
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) x with ⟨A, rfl⟩
      apply Equiv.ext
      intro z
      rw [hiota_apply]
      change rho (Matrix.ProjGenLinGroup.mk
        (Matrix.SpecialLinearGroup.toGL A)) z = rhoPSL
          (QuotientGroup.mk'
            (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A) z
      rw [hrho_apply _ _ _ rfl, hrhoPSL_apply]
    have hOmega_card_gt_one : 1 < Nat.card Omega := by
      rw [hprojective_line_card]
      omega
    letI : Nontrivial Omega :=
      Finite.one_lt_card_iff_nontrivial.mp hOmega_card_gt_one
    have htrans (a b : Omega) : ∃ x : PSL2, rhoPSL x a = b := by
      obtain ⟨c, hca⟩ := exists_ne a
      obtain ⟨d, hdb⟩ := exists_ne b
      rcases htwo a c b d hca.symm hdb.symm with ⟨x, hx, _⟩
      exact ⟨x, hx⟩
    letI : Fintype Omega := Fintype.ofFinite Omega
    obtain ⟨triple : Fin 3 ↪ Omega⟩ :=
      Function.Embedding.nonempty_of_card_le (α := Fin 3) (β := Omega) (by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
        hprojective_line_card]
      omega)
    let a : Omega := triple 0
    let b : Omega := triple 1
    let c : Omega := triple 2
    have hab : a ≠ b := by
      intro h
      have hij : (0 : Fin 3) = 1 := triple.injective h
      omega
    have hac : a ≠ c := by
      intro h
      have hij : (0 : Fin 3) = 2 := triple.injective h
      omega
    have hbc : b ≠ c := by
      intro h
      have hij : (1 : Fin 3) = 2 := triple.injective h
      omega
    obtain ⟨x, hxa, hxb⟩ := htwo a b a c hab hac
    have hx_ne_one : x ≠ 1 := by
      intro hx
      subst x
      simp at hxb
      exact hbc hxb
    have hfix_iota : rho (iota x) a = a := by
      rw [hcompat]
      exact hxa
    have hno_regular :
        ¬ ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ u v : Omega, ∃! r : R, rho (r : PGL2) u = v := by
      rintro ⟨R, hRnormal, _hRne, hRregular⟩
      let S : Subgroup PSL2 := R.comap iota
      have hSnormal : S.Normal := hRnormal.comap iota
      rcases hSnormal.eq_bot_or_eq_top with hSbot | hStop
      · have hcomm (r : R) : Commute (iota x) (r : PGL2) := by
          letI : iota.range.Normal := hPSL_normal
          letI : R.Normal := hRnormal
          have hcomm_mem : ⁅iota x, (r : PGL2)⁆ ∈ ⁅iota.range, R⁆ :=
            Subgroup.commutator_mem_commutator
              (show iota x ∈ iota.range from ⟨x, rfl⟩) r.property
          have hboth : ⁅iota x, (r : PGL2)⁆ ∈ iota.range ⊓ R :=
            (Subgroup.commutator_le_inf (H₁ := iota.range) (H₂ := R)) hcomm_mem
          rcases hboth.1 with ⟨y, hy⟩
          have hyS : y ∈ S := by
            change iota y ∈ R
            rw [hy]
            exact hboth.2
          have hy_one : y = 1 := by
            rw [hSbot] at hyS
            exact Subgroup.mem_bot.mp hyS
          apply commutatorElement_eq_one_iff_commute.mp
          calc
            ⁅iota x, (r : PGL2)⁆ = iota y := hy.symm
            _ = iota 1 := by rw [hy_one]
            _ = 1 := map_one iota
        have hfix_all (z : Omega) : rho (iota x) z = z := by
          obtain ⟨r, hr, _⟩ := hRregular a z
          have hxr := hcomm r
          calc
            rho (iota x) z = rho (iota x) (rho (r : PGL2) a) := by rw [hr]
            _ = rho (iota x * (r : PGL2)) a := by rw [map_mul]; rfl
            _ = rho ((r : PGL2) * iota x) a := by rw [hxr.eq]
            _ = rho (r : PGL2) (rho (iota x) a) := by rw [map_mul]; rfl
            _ = rho (r : PGL2) a := by rw [hfix_iota]
            _ = z := hr
        have hrho_one : rho (iota x) = 1 := by
          ext z
          simpa using hfix_all z
        have hiota_one : iota x = 1 := by
          apply hrho
          simpa using hrho_one
        exact hx_ne_one (hiota (by simpa using hiota_one))
      · have hixR : iota x ∈ R := by
          change x ∈ S
          rw [hStop]
          exact Subgroup.mem_top x
        have hreg := hRregular a a
        have hxsub : (⟨iota x, hixR⟩ : R) = 1 := by
          exact hreg.unique hfix_iota (by simp)
        have hiota_one : iota x = 1 := congrArg Subtype.val hxsub
        exact hx_ne_one (hiota (by simpa using hiota_one))
    have hnoncomm : ∃ x y : PSL2, x * y ≠ y * x := by
      by_contra hcomm
      push Not at hcomm
      apply hno_regular
      refine ⟨iota.range, hPSL_normal, ?_, ?_⟩
      · intro hbot
        have hix_bot : iota x ∈ (⊥ : Subgroup PGL2) := by
          rw [← hbot]
          exact ⟨x, rfl⟩
        have hiota_one : iota x = 1 := Subgroup.mem_bot.mp hix_bot
        exact hx_ne_one (hiota (by simpa using hiota_one))
      · intro u v
        obtain ⟨g, hg⟩ := htrans u v
        refine ⟨⟨iota g, ⟨g, rfl⟩⟩, ?_, ?_⟩
        · change rho (iota g) u = v
          rw [hcompat]
          exact hg
        · intro r hr
          rcases r.property with ⟨y, hy⟩
          have hry : rho (iota y) u = v := by
            rw [hy]
            exact hr
          apply Subtype.ext
          change (r : PGL2) = iota g
          rw [← hy]
          apply congrArg iota
          have hy_action : rhoPSL y u = v := by
            rw [← hcompat]
            exact hry
          have hfree (z : PSL2) (hz : rhoPSL z u = u) : z = 1 := by
            apply hrhoPSL
            apply Equiv.ext
            intro w
            obtain ⟨t, ht⟩ := htrans u w
            calc
              rhoPSL z w = rhoPSL z (rhoPSL t u) := by rw [ht]
              _ = rhoPSL (z * t) u := by rw [map_mul]; rfl
              _ = rhoPSL (t * z) u := by rw [hcomm z t]
              _ = rhoPSL t (rhoPSL z u) := by rw [map_mul]; rfl
              _ = rhoPSL t u := by rw [hz]
              _ = w := ht
              _ = rhoPSL 1 w := by simp
          have hquot_fix : rhoPSL (g⁻¹ * y) u = u := by
            rw [map_mul, map_inv]
            change (rhoPSL g)⁻¹ (rhoPSL y u) = u
            rw [hy_action, ← hg]
            exact (rhoPSL g).symm_apply_apply u
          exact (inv_mul_eq_one.mp (hfree (g⁻¹ * y) hquot_fix)).symm
    exact ⟨hsimple, hnoncomm, hno_regular⟩
  have hcard_two :
      Nat.card K = 2 →
        Nonempty (PGL2 ≃* Equiv.Perm (Fin 3)) ∧
        ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b := by
    intro hK
    classical
    letI : Fintype Omega := Fintype.ofFinite Omega
    have hOmega_card : Nat.card Omega = 3 := by
      rw [hprojective_line_card, hK]
    let eOmega : Omega ≃ Fin 3 := Finite.equivFinOfCardEq hOmega_card
    let act : PGL2 →* Equiv.Perm (Fin 3) :=
      (Equiv.permCongrHom eOmega).toMonoidHom.comp rho
    have hact_inj : Function.Injective act := by
      intro g h hgh
      apply hrho
      apply (Equiv.permCongrHom eOmega).injective
      simpa [act] using hgh
    have hact_card : Nat.card PGL2 = Nat.card (Equiv.Perm (Fin 3)) := by
      rw [huppertXI13_card_pgl2, hK, Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    have hact_bij : Function.Bijective act :=
      (Nat.bijective_iff_injective_and_card act).2 ⟨hact_inj, hact_card⟩
    let eGroup : PGL2 ≃* Equiv.Perm (Fin 3) :=
      MulEquiv.ofBijective act hact_bij
    refine ⟨⟨eGroup⟩, ?_⟩
    apply huppertXI13_pullback_regular rho eOmega act
      (fun g x => by simp [act, Equiv.permCongr_apply]) hact_bij
      (alternatingGroup (Fin 3))
    · infer_instance
    · exact huppertXI13_alternating_fin_three_regular
  have hcard_three :
      Nat.card K = 3 →
        Nonempty (PGL2 ≃* Equiv.Perm (Fin 4)) ∧
        ∃ R : Subgroup PGL2, R.Normal ∧ R ≠ ⊥ ∧
          ∀ a b : Omega, ∃! r : R, rho (r : PGL2) a = b := by
    intro hK
    classical
    letI : Fintype Omega := Fintype.ofFinite Omega
    have hOmega_card : Nat.card Omega = 4 := by
      rw [hprojective_line_card, hK]
    let eOmega : Omega ≃ Fin 4 := Finite.equivFinOfCardEq hOmega_card
    let act : PGL2 →* Equiv.Perm (Fin 4) :=
      (Equiv.permCongrHom eOmega).toMonoidHom.comp rho
    have hact_inj : Function.Injective act := by
      intro g h hgh
      apply hrho
      apply (Equiv.permCongrHom eOmega).injective
      simpa [act] using hgh
    have hact_card : Nat.card PGL2 = Nat.card (Equiv.Perm (Fin 4)) := by
      rw [huppertXI13_card_pgl2, hK, Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    have hact_bij : Function.Bijective act :=
      (Nat.bijective_iff_injective_and_card act).2 ⟨hact_inj, hact_card⟩
    let eGroup : PGL2 ≃* Equiv.Perm (Fin 4) :=
      MulEquiv.ofBijective act hact_bij
    refine ⟨⟨eGroup⟩, ?_⟩
    exact huppertXI13_pullback_regular rho eOmega act
      (fun g x => by simp [act, Equiv.permCongr_apply]) hact_bij
      huppertXI13_kleinFourPerm huppertXI13_kleinFourPerm_normal
      huppertXI13_kleinFourPerm_regular
  exact ⟨hprojective_line_card, rho, iota, hrho, hiota, hiota_apply,
    hrho_apply, hPSL_normal, hPSL_index, hsharply_three_transitive,
    hlarge_field, hcard_two, hcard_three⟩

end External
end CFSG.BenderSuzuki
