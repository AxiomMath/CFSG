module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZGLWedd
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZQuot
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open Matrix

private lemma l937z_sl_eq_det_ker {K : Type} [Field K] (n : ℕ) :
    StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  refine le_antisymm ?_ ?_
  · rw [CFSG.Open.StatedSL]
    exact (Subgroup.closure_le _).mpr (fun A hA => by
      show (GeneralLinearGroup.det A : Kˣ) = 1
      exact Units.ext (by simpa using hA))
  · intro A hA
    rw [CFSG.Open.StatedSL]
    apply Subgroup.subset_closure
    have hA' : (GeneralLinearGroup.det A : Kˣ) = 1 := hA
    simpa using congrArg (fun u : Kˣ => (u : K)) hA'

private lemma l937z_sl_centralizer_comap {K : Type} [Field K] (n : ℕ)
    (x : ↥(StatedSL n K)) :
    Subgroup.centralizer ({x} : Set ↥(StatedSL n K)) =
      (Subgroup.centralizer ({↑x} : Set (GL (Fin n) K))).comap (StatedSL n K).subtype := by
  ext y
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    simpa using congrArg Subtype.val (h x (Set.mem_singleton x))
  · intro h z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Subtype.ext (h (x : GL (Fin n) K) (Set.mem_singleton _))

private lemma l937z_sl_normal {K : Type} [Field K] (n : ℕ) (x : GL (Fin n) K) :
    Subgroup.centralizer ({x} : Set (GL (Fin n) K)) ≤
      Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set (GL (Fin n) K)) ⊓ StatedSL n K :
          Set (GL (Fin n) K)) := by
  haveI : (StatedSL n K).Normal := by
    rw [l937z_sl_eq_det_ker n]
    infer_instance
  exact Subgroup.le_normalizer_inf Subgroup.le_normalizer (by
    rw [Subgroup.normalizer_eq_top (StatedSL n K)]
    exact le_top)

private lemma l937z_sl_pCore_le {K : Type} [Field K] (n : ℕ) (x : GL (Fin n) K) :
    pCoreOf 2 (Subgroup.centralizer ({x} : Set (GL (Fin n) K)) ⊓ StatedSL n K) ≤
      pCoreOf 2 (Subgroup.centralizer ({x} : Set (GL (Fin n) K))) :=
  CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 inf_le_left (l937z_sl_normal n x)

private lemma l937z_sl_pCore_bot {K : Type} [Field K] (n : ℕ) (x : ↥(StatedSL n K))
    (hO2M : pCoreOf 2 (Subgroup.centralizer ({↑x} : Set (GL (Fin n) K)) ⊓
      StatedSL n K) = ⊥) :
    pCoreOf 2 (Subgroup.centralizer ({x} : Set ↥(StatedSL n K))) = ⊥ := by
  have hHs : Subgroup.centralizer ({x} : Set ↥(StatedSL n K)) =
      (Subgroup.centralizer ({↑x} : Set (GL (Fin n) K))).subgroupOf (StatedSL n K) := by
    rw [l937z_sl_centralizer_comap n x,
      Subgroup.comap_subtype
        (Subgroup.centralizer ({↑x} : Set (GL (Fin n) K))) (StatedSL n K)]
  have hmap : Subgroup.map (StatedSL n K).subtype
      (pCoreOf 2 (Subgroup.centralizer ({x} : Set ↥(StatedSL n K)))) = ⊥ := by
    rw [hHs]
    rw [← CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 (StatedSL n K).subtype
      (StatedSL n K).subtype_injective
      ((Subgroup.centralizer ({↑x} : Set (GL (Fin n) K))).subgroupOf (StatedSL n K))]
    rw [Subgroup.subgroupOf_map_subtype, hO2M]
  exact Subgroup.map_injective (StatedSL n K).subtype_injective
    (hmap.trans (Subgroup.map_bot _).symm)

theorem pCoreSevenTrivial_StatedSL {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    PCoreSevenTrivial ↥(StatedSL n K) := by
  intro x hx
  have hO2C : pCoreOf 2 (Subgroup.centralizer ({↑x} : Set (GL (Fin n) K))) = ⊥ :=
    pCoreOf_centralizer_GL_eq_bot (K := K) (n := n) (x : GL (Fin n) K)
      (by rw [Subgroup.orderOf_coe x, hx]; norm_num)
  exact l937z_sl_pCore_bot n x
    (eq_bot_iff.mpr ((l937z_sl_pCore_le n (x : GL (Fin n) K)).trans (le_of_eq hO2C)))

theorem lieZRow_PSL {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (h7 : ¬ 7 ∣ Nat.card K - 1) : LieZRow (StatedProj (StatedSL n K)) := by
  apply lieZRow_statedProj (StatedSL n K) ?_
    (lieZRow_of_pCoreSevenTrivial (pCoreSevenTrivial_StatedSL n))
  letI : Fintype K := Fintype.ofFinite K
  have hoddK : Odd (Nat.card K - 1) := by
    obtain ⟨f, _hp2, hf⟩ := FiniteField.card K 2
    have hcard : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    have hfne : (f : ℕ) ≠ 0 := f.pos.ne'
    have heven : Even (2 ^ (f : ℕ)) := Nat.even_pow.mpr ⟨even_two, hfne⟩
    have hodd : Odd (2 ^ (f : ℕ) - 1) :=
      Nat.Even.sub_odd (le_of_lt (Nat.one_lt_pow hfne (by norm_num))) heven odd_one
    rwa [hcard]
  have h2 : Nat.Coprime 2 (Nat.card K - 1) := Nat.coprime_two_left.mpr hoddK
  have h7c : Nat.Coprime 7 (Nat.card K - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)]
    exact h7
  have h14 : Nat.Coprime 14 (Nat.card K - 1) := by
    simpa using Nat.Coprime.mul_left h2 h7c
  exact Nat.Coprime.of_dvd_right (card_statedScalars_subgroupOf_dvd (StatedSL n K)) h14

end CFSG.StandardType.SporadicShape
