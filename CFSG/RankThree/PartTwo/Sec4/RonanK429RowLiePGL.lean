module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieField
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossUnit
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem eq_of_subnormal_of_equiv {T : Type*} [Group T] {C J : Subgroup G} (ε : C ≃* T)
    {Q : Subgroup T} (hQ : IsSimpleGroup Q) (hcomm : ∀ x y : T, ⁅x, y⁆ ∈ Q)
    (hcube : ∀ x : T, x ^ 3 ∈ Q) (hJC : J ≤ C) [Group.IsPerfect J]
    (hsub : (J.subgroupOf C).IsSubnormal) (h3 : ∃ k ∈ J, k ≠ 1 ∧ k ^ 3 = 1) :
    Nonempty (J ≃* Q) ∧ CFSG.pCore 2 C = ⊥ := by
  set P : Subgroup G := (Q.comap ε.toMonoidHom).map C.subtype with hP
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hPQ : P ≃* Q :=
    ((Q.comap ε.toMonoidHom).equivMapOfInjective C.subtype (Subgroup.subtype_injective C)).symm.trans
      (comapEquiv ε Q)
  have hPs : IsSimpleGroup P := hPQ.isSimpleGroup
  have hnt : J ≠ ⊥ := by
    obtain ⟨k, hk, hk1, -⟩ := h3
    intro hb
    rw [hb, Subgroup.mem_bot] at hk
    exact hk1 hk
  have hJP : J ≤ P := by
    rw [← Subgroup.commutator_eq_self (H := J), Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, hJC ha⟩ : C), ⟨b, hJC hb⟩⁆, ?_, rfl⟩
    show ε ⁅(⟨a, hJC ha⟩ : C), ⟨b, hJC hb⟩⁆ ∈ Q
    rw [map_commutatorElement]
    exact hcomm _ _
  have hJeq := eq_of_subnormal_of_le_simple hJP hPC hsub hPs hnt
  refine ⟨⟨(MulEquiv.subgroupCongr hJeq).trans hPQ⟩, ?_⟩
  refine pCore_two_eq_bot_of_cube_mem hPC hPs (hJeq ▸ h3) fun x hx => ?_
  refine ⟨(⟨x, hx⟩ : C) ^ 3, ?_, rfl⟩
  show ε ((⟨x, hx⟩ : C) ^ 3) ∈ Q
  rw [map_pow]
  exact hcube _

end Abstract

section PGL

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem det_commutator (A B : GL (Fin 3) K) :
    ((⁅A, B⁆ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [← GeneralLinearGroup.val_det_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _), Units.val_one]

theorem commutator_mem_projImage_slPi (hK : PiField π p f K) {x y : ProjGenLinGroup (Fin 3) K}
    (hx : x ∈ projImage (glPi π 3 (p ^ f) K)) (hy : y ∈ projImage (glPi π 3 (p ^ f) K)) :
    ⁅x, y⁆ ∈ projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨B, hB, rfl⟩ := hy
  refine ⟨⁅A, B⁆, ?_, map_commutatorElement _ _ _⟩
  cases π with
  | true => exact (mem_slPi_true _).mpr (det_commutator A B)
  | false =>
    refine (mem_slPi_false hK.unitary).mpr ⟨det_commutator A B, ?_⟩
    have hAB : ⁅A, B⁆ ∈ glPi false 3 (p ^ f) K := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
    exact (mem_glPi_false hK.unitary).mp hAB

theorem pow_three_mem_projImage_slPi (hK : PiField π p f K) {x : ProjGenLinGroup (Fin 3) K}
    (hx : x ∈ projImage (glPi π 3 (p ^ f) K)) : x ^ 3 ∈ projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨A, hA, rfl⟩ := hx
  set u : Kˣ := GeneralLinearGroup.det A with hu
  set B : GL (Fin 3) K := A ^ 3 * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ with hB
  have hmk : ProjGenLinGroup.mk B = ProjGenLinGroup.mk A ^ 3 := by
    rw [hB, map_mul, map_inv, ProjGenLinGroup.mk_scalar, inv_one, mul_one, map_pow]
  have hdet : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hB, map_mul, map_inv, map_pow,
      GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hu, mul_inv_cancel, Units.val_one]
  refine ⟨B, ?_, hmk⟩
  cases π with
  | true => exact (mem_slPi_true _).mpr hdet
  | false =>
    have h := hK.unitary
    refine (mem_slPi_false h).mpr ⟨hdet, (mem_glPi_false h).mp ?_⟩
    have hAU : A ∈ unitaryIsom3 h := mem_unitaryIsom3.mpr ((mem_glPi_false h).mp hA)
    have hnorm : h.norm (u : K) = 1 := by
      have h1 := det_pow_succ_eq_one_of_mem_unitaryIsom3 h hAU
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
      have h2 := congrArg (fun v : Kˣ => (v : K)) h1
      simpa [hu] using h2
    have hsU : GeneralLinearGroup.scalar (Fin 3) u ∈ unitaryIsom3 h :=
      scalar_mem_unitaryIsom3_of_norm hnorm
    have hBU : B ∈ unitaryIsom3 h := mul_mem (pow_mem hAU 3) (inv_mem hsU)
    exact (mem_glPi_false h).mpr (mem_unitaryIsom3.mp hBU)

theorem isSimpleGroup_projImage_slPi (hK : PiField π p f K) (hq : π = true ∨ 2 < p ^ f) :
    IsSimpleGroup (projImage (slPi π 3 (p ^ f) K)) := by
  cases π with
  | true =>
    haveI := CFSG.ComponentClassification.OutcomeLocal.isSimpleGroup_projectiveSL
      (k := K) (n := 3) le_rfl
    exact (Sec4.pslEquivProjective (p ^ f) K).isSimpleGroup
  | false =>
    have hq2 : 2 < p ^ f := by simpa using hq
    haveI := CFSG.RankThree.PartTwo.Sec21.Item211Lie2Proof.isSimpleGroup_unitaryPSU_three
      (h := hK.unitary) hq2
    exact (Sec4.psuEquivUnitary hK.unitary).isSimpleGroup

theorem isoLThreePi_of_projImage_slPi {X : Type} [Group X] {n : ℕ} (hK : PiField π 2 n K)
    (hq : ModThree π (2 ^ n)) (hq2 : π = true ∨ 2 < 2 ^ n)
    (e : X ≃* projImage (slPi π 3 (2 ^ n) K)) : IsoLThreePi X 2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hK.one_le
  have := hK.finite
  cases π with
  | true =>
    have hcard : Nat.card K = 2 ^ n := by simpa [piCard] using hK.card
    have ψ : K ≃+* GaloisField 2 n :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 n (by omega) hcard
    obtain ⟨φ₁⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
    exact Or.inl ⟨hq, ⟨((e.trans (Sec4.pslEquivProjective (2 ^ n) K)).trans
      (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr ψ)).trans φ₁.symm⟩⟩
  | false =>
    have hq2' : 2 < 2 ^ n := by simpa using hq2
    have h := hK.unitary
    have hG : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
    have h₁ : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) := ⟨Nat.prime_two, hn, hG⟩
    have ψ : K ≃+* GaloisField 2 (2 * n) :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 (2 * n) (by omega) h.card
    obtain ⟨φ₁⟩ := nonempty_unitaryPSU_mulEquiv_projSU h₁
    exact Or.inr ⟨hq, ⟨((e.trans (Sec4.psuEquivUnitary h)).trans
      (CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.psuEquiv ψ h₁ h hq2')).trans φ₁⟩⟩

theorem pglCase {G : Type} [Group G] {n : ℕ} (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    {C J : Subgroup G} (ε : C ≃* projImage (glPi π 3 (2 ^ n) K)) (hJC : J ≤ C)
    [Group.IsPerfect J] (hsub : (J.subgroupOf C).IsSubnormal)
    (h3 : ∃ k ∈ J, k ≠ 1 ∧ k ^ 3 = 1) :
    IsoLThreePi J 2 n ∧ CFSG.pCore 2 C = ⊥ := by
  have hle : projImage (slPi π 3 (2 ^ n) K) ≤ projImage (glPi π 3 (2 ^ n) K) := by
    refine Subgroup.map_mono ?_
    cases π with
    | true => exact fun A _ => mem_glPi_true _ A
    | false =>
      intro A hA
      exact (mem_glPi_false hK.unitary).mpr ((mem_slPi_false hK.unitary).mp hA).2
  set Q : Subgroup (projImage (glPi π 3 (2 ^ n) K)) :=
    (projImage (slPi π 3 (2 ^ n) K)).subgroupOf (projImage (glPi π 3 (2 ^ n) K)) with hQ
  have hQe : Q ≃* projImage (slPi π 3 (2 ^ n) K) := Subgroup.subgroupOfEquivOfLe hle
  have hcomm : ∀ x y : projImage (glPi π 3 (2 ^ n) K), ⁅x, y⁆ ∈ Q := fun x y =>
    commutator_mem_projImage_slPi hK x.2 y.2
  have hcube : ∀ x : projImage (glPi π 3 (2 ^ n) K), x ^ 3 ∈ Q := fun x =>
    pow_three_mem_projImage_slPi hK x.2
  by_cases hq2 : π = true ∨ 2 < 2 ^ n
  · haveI := isSimpleGroup_projImage_slPi hK hq2
    have hQs : IsSimpleGroup Q := hQe.isSimpleGroup
    obtain ⟨⟨eJ⟩, hO2⟩ := eq_of_subnormal_of_equiv ε hQs hcomm hcube hJC hsub h3
    exact ⟨isoLThreePi_of_projImage_slPi hK hq hq2 (eJ.trans hQe), hO2⟩
  · exfalso
    push Not at hq2
    obtain ⟨hπ, hq2⟩ := hq2
    have hπ' : π = false := by simpa using hπ
    subst hπ'
    have h2 : 2 ^ n = 2 := by
      have : 2 ≤ 2 ^ n := Nat.le_self_pow (by have := hK.one_le; omega) 2
      omega
    have hsol : Group.IsSolvable (projImage (slPi false 3 (2 ^ n) K)) :=
      Sec13.isSolvable_projImage_slPi_two hK h2
    set P : Subgroup G := (Q.comap ε.toMonoidHom).map C.subtype with hP
    have hJP : J ≤ P := by
      rw [← Subgroup.commutator_eq_self (H := J), Subgroup.commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, hJC ha⟩ : C), ⟨b, hJC hb⟩⁆, ?_, rfl⟩
      show ε ⁅(⟨a, hJC ha⟩ : C), ⟨b, hJC hb⟩⁆ ∈ Q
      rw [map_commutatorElement]
      exact hcomm _ _
    have hPQ : P ≃* Q :=
      ((Q.comap ε.toMonoidHom).equivMapOfInjective C.subtype
        (Subgroup.subtype_injective C)).symm.trans (comapEquiv ε Q)
    haveI : Group.IsSolvable Q :=
      Group.isSolvable_of_surjective (f := hQe.symm.toMonoidHom) hQe.symm.surjective
    haveI : Group.IsSolvable P :=
      Group.isSolvable_of_surjective (f := hPQ.symm.toMonoidHom) hPQ.symm.surjective
    have hsolJ : Group.IsSolvable J :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJP)
        (Subgroup.inclusion_injective hJP)
    have hnt : J ≠ ⊥ := by
      obtain ⟨k, hk, hk1, -⟩ := h3
      intro hb
      rw [hb, Subgroup.mem_bot] at hk
      exact hk1 hk
    haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hnt
    exact Group.IsPerfect.not_isSolvable J hsolJ

end PGL

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
