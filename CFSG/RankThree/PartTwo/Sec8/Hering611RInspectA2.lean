module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectBridge
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectFam
import CFSG.RankThree.PartTwo.Sec8.Hering418Lin
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL3
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.Sec8.Hering418ROuter
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

section Bound

theorem false_of_bound {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {P : Subgroup X} (hP : IsA6Sub P) {α : MulAut X} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hPC : P ≤ Item426.fixSub α) (N : Subgroup (MulAut X))
    (hinn : (MulAut.conj : X →* MulAut X).range ≤ N) (hαN : α ∈ N)
    (hN : ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → F ≤ N → Nat.card F ≤ 9) : False := by
  classical
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨R, hRP, hR, hR9, -⟩ := hP.exists_elemAbelian_nine
  have hinj := Hering418.conj_injective_of_center_eq_bot hZ
  by_cases hin : ∃ g : X, MulAut.conj g = α
  · obtain ⟨g, hg⟩ := hin
    obtain ⟨hg3, hg1, hgP⟩ := inner_data hZ hα3 hα1 hg hPC
    have hgR : g ∉ R := fun hgR =>
      hg1 (hP.eq_one_of_commute (hRP hgR) hgP
        (by rw [show 9 = 3 * 3 from rfl, pow_mul, hg3, one_pow]))
    obtain ⟨hF, hFcard⟩ := Sec6.isElemAbelian_sup_zpowers_three hR hgR hg3
      (fun k hk => hgP k (hRP hk))
    have hFN : (R ⊔ Subgroup.zpowers g).map (MulAut.conj : X →* MulAut X) ≤ N := by
      rintro _ ⟨y, -, rfl⟩
      exact hinn ⟨y, rfl⟩
    have h := hN _ (Sec4.isElemAbelian_map _ hF) hFN
    rw [Subgroup.card_map_of_injective hinj, hFcard, hR9] at h
    omega
  · set R' : Subgroup (MulAut X) := R.map (MulAut.conj : X →* MulAut X) with hR'
    have hR'ab : IsElemAbelian 3 R' := Sec4.isElemAbelian_map _ hR
    have hαR' : α ∉ R' := by
      rintro ⟨r, -, hr⟩
      exact hin ⟨r, hr⟩
    have hcomm : ∀ k ∈ R', k * α = α * k := by
      rintro _ ⟨r, hr, rfl⟩
      have hαr : α r = r := hPC (hRP hr)
      ext y
      simp [MulAut.conj_apply, hαr]
    obtain ⟨hF, hFcard⟩ := Sec6.isElemAbelian_sup_zpowers_three hR'ab hαR' hα3 hcomm
    have hR'N : R' ≤ N := by
      rintro _ ⟨y, -, rfl⟩
      exact hinn ⟨y, rfl⟩
    have h := hN _ hF (sup_le hR'N ((Subgroup.zpowers_le).mpr hαN))
    have hR'card : Nat.card R' = 9 := by
      rw [hR', Subgroup.card_map_of_injective hinj, hR9]
    omega

end Bound

section Models

theorem exists_bound_L3 {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (he1 : 1 ≤ e) (he2 : e ≤ 2) (φ : X ≃* projSL 3 (GaloisField p e)) :
    Subgroup.center X = ⊥ ∧ ∃ N : Subgroup (MulAut X),
      (MulAut.conj : X →* MulAut X).range ≤ N ∧ (∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ N) ∧
      ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → F ≤ N → Nat.card F ≤ 9 := by
  set F := GaloisField p e with hFdef
  have hFcard : Nat.card F = p ^ e := GaloisField.card p e (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out (by omega) hFcard
  let e' : X ≃* projectiveSL 3 F := φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
  refine ⟨KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e'
    (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := F)
      (le_refl 3)), ?_⟩
  refine Hering418.exists_bound_of_hom (MulAut.congr e').toMonoidHom (MulAut.congr e').injective
    (linearAutGroup 3 F) ?_ ?_ ?_
  · intro x
    rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
    exact KFacts.innAut_le_linearAutGroup 3 F ⟨e' x, rfl⟩
  · intro σ hσ
    exact Hering418.pow_three_mem_linearAutGroup Fact.out (by omega) hFcard (by omega)
      (α := MulAut.congr e' σ) (by rw [← map_pow, hσ, map_one])
  · intro F' hF' hFN
    have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
    rwa [inf_eq_left.mpr hFN] at this

theorem exists_bound_U3 {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (he1 : 1 ≤ e) (he2 : e ≤ 2) (φ : X ≃* projSU 3 p e) :
    Subgroup.center X = ⊥ ∧ ∃ N : Subgroup (MulAut X),
      (MulAut.conj : X →* MulAut X).range ≤ N ∧ (∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ N) ∧
      ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → F ≤ N → Nat.card F ≤ 9 := by
  have hU := Sec4.unitaryFieldData_galoisField p e he1
  have hq : 2 < p ^ e := by
    calc 2 < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he1
  have h3 : (3 : GaloisField p (2 * e)) ≠ 0 :=
    Sec4.three_ne_zero_of_card Fact.out (by omega) (GaloisField.card p (2 * e) (by omega))
  have := hU.finite
  let e' : X ≃* unitaryPSU hU 3 := φ.trans (Sec4.projSUEquivUnitaryPSU p e hU)
  refine ⟨KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e'
    (KFacts.center_unitaryPSU_three_eq_bot hU hq), ?_⟩
  refine Hering418.exists_bound_of_hom (MulAut.congr e').toMonoidHom (MulAut.congr e').injective
    (KFacts.psuConj hU).range ?_ ?_ ?_
  · intro x
    rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
    exact (KFacts.stdPinnedPSU3 hU).inn_le ⟨e' x, rfl⟩
  · intro σ hσ
    exact Hering418.pow_three_mem_psuConj_range hq (by omega) (α := MulAut.congr e' σ)
      (by rw [← map_pow, hσ, map_one])
  · intro F' hF' hFN
    exact Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 F' hF' hFN

end Models

section Main


theorem false_of_isoLThreePi_two {G : Type} [Group G] [Finite G] {K : Subgroup G} {c : G}
    {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hX : IsoLThreePi (K ⧸ aschbacherSolvableCore 3 K) p e) (hA6 : HasA6Cent K c) : False := by
  obtain ⟨hcN, hα3, hα1, P, hP, ⟨e6⟩⟩ := hA6
  have hPsub : IsA6Sub P := ⟨isPerfect_of_mem_thetaComponentsIn hP, ⟨e6⟩⟩
  have hPC : P ≤ Item426.fixSub (Item426.thetaAut K hcN) := le_of_mem_thetaComponentsIn hP
  rcases hX with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · obtain ⟨hZ, N, hinn, h3, hN⟩ := exists_bound_L3 hp3 he1 he2 φ
    exact false_of_bound hZ hPsub hα3 hα1 hPC N hinn (h3 _ hα3) hN
  · obtain ⟨hZ, N, hinn, h3, hN⟩ := exists_bound_U3 hp3 he1 he2 φ
    exact false_of_bound hZ hPsub hα3 hα1 hPC N hinn (h3 _ hα3) hN

theorem false_of_isoLThreePi_four {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {x : G} {P : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} {n : ℕ} (hn : 1 ≤ n)
    (hX : IsoLThreePi (K ⧸ aschbacherSolvableCore 3 K) 2 n) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind K x .diagonal)
    (hxk : KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField)
    (hP : IsA6Sub P) : False := by
  rcases hX with ⟨h1, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hev : Even n := by
      by_contra hodd
      have := CFSG.two_pow_mod_three_of_odd (Nat.not_even_iff_odd.mp hodd)
      omega
    have h := Item82Proof.kF82TwoLThreeKinds_holds G K x n hev hn ⟨φ⟩ hx3 hk
    rcases hxk with hf | hf
    · exact h.1 hf
    · exact h.2 hf
  · exact false_of_projSU hn φ hP

end Main

end CFSG.RankThree.PartTwo.Sec8.Hering611R
