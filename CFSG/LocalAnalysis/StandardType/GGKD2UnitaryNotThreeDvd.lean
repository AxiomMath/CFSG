module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.LocalAnalysis.StandardType.GGTCJDivUni
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RALabels
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
import CFSG.Goldschmidt.Steps.G37Quot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.Walter.Bender1970.S3.OStar
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.SemisimpleCentralizers.Held

@[expose] def SplitLiftUnitaryNotThreeDvd : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twA → ¬ 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a → SplitLift lab R I ψ e → False)

private theorem ltrcu4_ggLabelIso_typeA_typeA {m : ℕ}
    (h : GGLabelIso (⟨.A, 1, 3⟩ : LargeEvenLabel) (⟨.A, 1, m⟩ : LargeEvenLabel)) :
    m = 3 := by
  rcases h with h | h | h | h | h | h | h | h
  · exact (congrArg LargeEvenLabel.n h).symm
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

private theorem ltrcu4_ggLabelIso_typeA_twA_false {r m : ℕ}
    (h : GGLabelIso (⟨.A, 1, 3⟩ : LargeEvenLabel) (⟨.twA, r, m⟩ : LargeEvenLabel)) :
    False := by
  rcases h with h | h | h | h | h | h | h | h
  · cases h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

private theorem ltrcu4_ggLabelIso_typeA_linear_false {b m : ℕ}
    (h : GGLabelIso (⟨.A, 1, 3⟩ : LargeEvenLabel) (⟨.A, b, m⟩ : LargeEvenLabel))
    (hm : ¬ m = 3) : False := by
  rcases h with h | h | h | h | h | h | h | h
  · exact hm (congrArg LargeEvenLabel.n h).symm
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

theorem splitLiftUnitaryNotThreeDvd_holds :
    SplitLiftUnitaryNotThreeDvd := by
  intro lab hΛ htag hn3 Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq, ?_⟩) hQ
  intro L' _ _ ψ hψ hker hperf e J a hsetup hsplit
  rcases hsplit with ⟨hA, _⟩ | htw
  · rw [htag] at hA; cases hA
  · obtain ⟨_, K, hKf, hKfin, h, M, hMN, hM3, hMgu, θ, hθ, hI⟩ := htw
    letI : Field K := hKf
    letI : Finite K := hKfin
    let S : Subgroup (GL (Fin (lab.rank + 1)) K) := unitarySU 2 lab.n K (lab.rank + 1)
    have hMN' : M ∈ Subgroup.normalizer (S : Set (GL (Fin (lab.rank + 1)) K)) := hMN
    obtain ⟨hp, hp2, he1, hep, hφe, hJcomp, hn2, hJlabel, hae, hφa, haJ, houter⟩ := hsetup
    have hrank2 : 2 ≤ lab.rank := by
      have hΛ' := hΛ
      simp only [LargeEvenInLambda2] at hΛ'
      rw [htag] at hΛ'
      exact hΛ'.2.1
    have hd3 : 3 ≤ lab.rank + 1 := by omega
    have hKcard : Nat.card K = (2 ^ lab.n) ^ 2 := by
      rw [h.card]
      rw [Nat.mul_comm 2 lab.n, ← pow_mul]
    have h2 : (2 : K) = 0 := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.two_eq_zero_of_card hKcard
    have hdQ : (lab.rank + 1, 2 ^ lab.n) ≠ (3, 2) := by
      intro hdQ
      obtain ⟨hd, hQ⟩ := Prod.mk.inj hdQ
      have hr2 : lab.rank = 2 := by omega
      have hn2' : 2 ≤ lab.n := by
        have hΛ' := hΛ
        simp only [LargeEvenInLambda2] at hΛ'
        rw [htag] at hΛ'
        exact hΛ'.2.2 hr2
      have hQ2 : 2 ^ lab.n = 2 := hQ
      have hn1 : lab.n = 1 :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hQ2.trans (pow_one 2).symm)
      omega
    let u : MulAut (LargeEvenProj S) := TableB.projConj S ⟨M, hMN'⟩
    have hpow : u ^ 3 = 1 := by
      change (TableB.projConj S ⟨M, hMN'⟩) ^ 3 = 1
      have hnorm3 : (⟨M, hMN'⟩ : Subgroup.normalizer (S : Set (GL (Fin (lab.rank + 1)) K))) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hM3]
        rfl
      rw [← map_pow, hnorm3, map_one]
    obtain ⟨A, hA, hAconj⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_heldGU_of_GUSet
        (K := K) (d := lab.rank + 1) (n := lab.n) (τ := h.barEquiv)
        (fun x => h.bar_apply x)
        hKcard h.isUnitaryInvolution_barEquiv.invol M hMgu
    let ψ' : L' →* LargeEvenProj S := θ.toMonoidHom.comp ψ
    have hψ' : Function.Surjective ψ' := by
      intro y
      obtain ⟨r, rfl⟩ := θ.surjective y
      obtain ⟨l, rfl⟩ := hψ r
      exact ⟨l, rfl⟩
    have hker' : ψ'.ker ≤ Subgroup.center L' := by
      intro x hx
      have hx1 : θ (ψ x) = 1 := MonoidHom.mem_ker.mp hx
      have hx2 : ψ x = 1 := θ.injective (by rw [hx1, map_one])
      exact hker (MonoidHom.mem_ker.mpr hx2)
    have hc : ∀ l : L', u (ψ' l) = ψ' (e l) := fun l => hθ l
    have hJ' : IsComponentOf (J.map ψ') (ggFix u) :=
      USixTwo.isComponentOf_map_fix hψ' hker' hc hJcomp
    have hJperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJcomp.2.2.1
    let f : ↥J →* ↥(J.map ψ') :=
      (ψ'.comp J.subtype).codRestrict (J.map ψ') (by
        rintro ⟨j, hj⟩
        exact ⟨j, hj, rfl⟩)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨j, hj, hjy⟩ := y.2
      exact ⟨⟨j, hj⟩, Subtype.ext hjy⟩
    have hkerf : f.ker ≤ Subgroup.center ↥J := by
      intro x hx
      have hx1 : ψ' (x : L') = 1 := by
        have := MonoidHom.mem_ker.mp hx
        exact congrArg Subtype.val this
      have hx2 : (x : L') ∈ ψ.ker := by
        apply θ.injective
        rw [map_one]
        exact hx1
      have hx3 : (x : L') ∈ Subgroup.center L' := hker hx2
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hx3 (y : L')
    obtain ⟨eQ⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hJperf f hf hkerf
    have hJlabel0 : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
        (J.map ψ' ⧸ Subgroup.center (J.map ψ')) :=
      ggHasLabel_of_mulEquiv eQ hJlabel
    haveI hsimple : IsSimpleGroup (J.map ψ' ⧸ Subgroup.center (J.map ψ')) := hJ'.2.2.2
    rcases TCJ.tcjUni_component_psu_fixed
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds
      h.isUnitaryInvolution_barEquiv.invol
      (fun x => h.bar_apply x)
      hKcard h2 hd3 hdQ A hA Nat.prime_three (by norm_num) u
      (by
        intro h h' hh'
        have hconj : (h' : GL (Fin (lab.rank + 1)) K) =
            (M : GL (Fin (lab.rank + 1)) K) * (h : GL (Fin (lab.rank + 1)) K) *
              (M : GL (Fin (lab.rank + 1)) K)⁻¹ := by
          rw [hh', hAconj]
        change (TableB.projConj S ⟨M, hMN'⟩) (h : LargeEvenProj S) =
          (h' : LargeEvenProj S)
        rw [TableB.projConj_mk]
        congr 1
        apply Subtype.ext
        exact hconj.symm)
      hpow (J.map ψ') hJ' with
      ⟨a', dd, E, hE, hEf, τ', hτ', ha2, hτ'Q, hcardE, ⟨φ⟩⟩ |
      ⟨b, ee, E, hE, hEf, hb2, hcardE, ⟨φ⟩⟩
    ·
      letI : Field E := hE
      letI : Finite E := hEf
      have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (lab.n * dd) := by
        intro x
        rw [pow_mul]
        exact hτ'Q x
      have hcardm : Nat.card E = (2 ^ (lab.n * dd)) ^ 2 := by
        rw [pow_mul]
        exact hcardE
      have hlamA : LargeEvenInLambda2 (⟨.A, 1, 3⟩ : LargeEvenLabel) := by
        unfold LargeEvenInLambda2
        norm_num
      rcases S2MathAs51600RALabels.admissible_label_of_heldSU_quot_exact τ' hτ' ha2 hτ'm hcardm φ with
        ⟨rfl, hlabC, hlamC⟩ | ⟨ha3, hlabC, hlamC⟩
      · have hiso : GGLabelIso (⟨.A, 1, 3⟩ : LargeEvenLabel)
            (⟨.A, 1, lab.n * dd⟩ : LargeEvenLabel) :=
          ggLabelRigidInput_holds _ _ _ hlamA hlamC hJlabel0 hlabC
        have hm3 : lab.n * dd = 3 := ltrcu4_ggLabelIso_typeA_typeA hiso
        have hdvd : lab.n ∣ 3 := ⟨dd, by rw [← hm3, mul_comm]⟩
        have hcases : lab.n = 1 ∨ lab.n = 3 := (Nat.dvd_prime (by norm_num)).1 hdvd
        rcases hcases with h1 | h3
        · exact hn3 (by rw [h1]; norm_num)
        · exact hn3 (by rw [h3]; norm_num)
      · have hiso : GGLabelIso (⟨.A, 1, 3⟩ : LargeEvenLabel)
            (⟨.twA, a' - 1, lab.n * dd⟩ : LargeEvenLabel) :=
          ggLabelRigidInput_holds _ _ _ hlamA hlamC hJlabel0 hlabC
        exact ltrcu4_ggLabelIso_typeA_twA_false hiso
    ·
      letI : Field E := hE
      letI : Finite E := hEf
      have hcardm : Nat.card E = 2 ^ (lab.n * (2 * ee)) := by
        rw [pow_mul]
        exact hcardE
      obtain ⟨hlamC, hlabC⟩ :=
        CFSG.StandardType.S2MathAs51600RALabels.admissible_typeA_of_psl
          (Q := J.map ψ' ⧸ Subgroup.center (J.map ψ')) (a := b) (m := lab.n * (2 * ee))
          (E := E) hb2 hcardm φ
      have hlamA : LargeEvenInLambda2 (⟨.A, 1, 3⟩ : LargeEvenLabel) := by
        unfold LargeEvenInLambda2
        norm_num
      have hiso : GGLabelIso (⟨.A, 1, 3⟩ : LargeEvenLabel)
          (⟨.A, b - 1, lab.n * (2 * ee)⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds _ _ _ hlamA hlamC hJlabel0 hlabC
      have hm : ¬ lab.n * (2 * ee) = 3 := by
        intro h
        have h2 : 2 ∣ lab.n * (2 * ee) := ⟨lab.n * ee, by ring⟩
        rw [h] at h2
        norm_num at h2
      exact ltrcu4_ggLabelIso_typeA_linear_false hiso hm

end CFSG.StandardType.KD2Pieces1615

end
