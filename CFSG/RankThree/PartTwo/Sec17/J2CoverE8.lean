module

public import CFSG.RankThree.PartTwo.Sec17.PropUGFree
public import CFSG.LargeExtraspecial.S63AJ2Schur
public import Certificates.Certificate724810
import CFSG.RankThree.PartTwo.Sec17.J2CoverE8Lift

public section

namespace CFSG.RankThree.PartTwo.Sec17.J2CoverE8

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ okA eltOf rep_eltOf eq_of_rep rep_mul rep_conj
  commute_of_commA okA_spec rep_one)
open CFSG.Monster.B.Co2 (Rep eqA_iff)

theorem ne_of_rep {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hu : Rep 315 u h.1)
    (hf : eqA 315 t u = false) : g ≠ h := fun he => by
  have := (eqA_iff ht hu).2 (congrArg Subtype.val he)
  rw [hf] at this
  exact Bool.false_ne_true this

theorem chk_parts :
    okA j2E8v1Arr = true ∧ okA j2E8v2Arr = true ∧ okA j2E8sArr = true ∧
    okA j2E8u1Arr = true ∧ okA j2E8u2Arr = true ∧ okA j2E8tArr = true ∧
    eqA 315 (compA 315 j2E8v1Arr j2E8v1Arr) (idA 315) = true ∧
    eqA 315 (conjA 315 j2E8sArr j2E8v1Arr) j2E8v2Arr = true ∧
    eqA 315 (conjA 315 j2E8sArr j2E8v2Arr) j2E8v12Arr = true ∧
    eqA 315 (compA 315 j2E8u1Arr j2E8u1Arr) (idA 315) = true ∧
    eqA 315 (conjA 315 j2E8tArr j2E8u1Arr) j2E8u2Arr = true ∧
    eqA 315 (conjA 315 j2E8tArr j2E8u2Arr) j2E8u12Arr = true ∧
    commA j2E8v1Arr j2E8u1Arr = true ∧ commA j2E8v1Arr j2E8u2Arr = true ∧
    commA j2E8v2Arr j2E8u1Arr = true ∧ commA j2E8v2Arr j2E8u2Arr = true ∧
    commA j2E8v1Arr j2E8tArr = true ∧ commA j2E8v2Arr j2E8tArr = true ∧
    eqA 315 j2E8v1Arr (idA 315) = false ∧ eqA 315 j2E8v2Arr (idA 315) = false ∧
    eqA 315 j2E8v2Arr j2E8v1Arr = false ∧ eqA 315 j2E8v12Arr (idA 315) = false ∧
    eqA 315 j2E8u1Arr (idA 315) = false ∧ eqA 315 j2E8u2Arr (idA 315) = false ∧
    eqA 315 j2E8u2Arr j2E8u1Arr = false ∧ eqA 315 j2E8u12Arr (idA 315) = false ∧
    eqA 315 j2E8u1Arr j2E8v1Arr = false ∧ eqA 315 j2E8u1Arr j2E8v2Arr = false ∧
    eqA 315 j2E8u1Arr j2E8v12Arr = false ∧
    eqA 315 j2E8w1Arr (idA 315) = false ∧ eqA 315 j2E8w2Arr (idA 315) = false ∧
    eqA 315 j2E8w2Arr j2E8w1Arr = false ∧
    eqA 315 (compA 315 j2E8w1Arr j2E8w2Arr) (idA 315) = false := by
  have h := Certificates.certificate724810
  simp only [chkJ2E8, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  exact h


theorem j2CoverHasElemAbelianEight_holds : J2CoverHasElemAbelianEight := by
  intro X _ _ Z _ hZc _ hX ⟨e⟩
  obtain ⟨o1, o2, o3, o4, o5, o6, q1, q2, q3, q4, q5, q6, c1, c2, c3, c4, c5, c6, n1, n2, n3, n4,
    n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := chk_parts
  obtain ⟨π, hπ⟩ : ∃ f : X →* GJ,
      f = (e.trans nativeEquivP).toMonoidHom.comp (QuotientGroup.mk' Z) := ⟨_, rfl⟩
  have hπx : ∀ x : X, π x = (e.trans nativeEquivP) (QuotientGroup.mk' Z x) := fun x => by
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨q, hq⟩ := (e.trans nativeEquivP).surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨x, by rw [hπx]; exact hq⟩
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker, hπx, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hcen : Subgroup.center X = Z := by
    refine le_antisymm (fun c hc => ?_) hZc
    have hπc : π c ∈ Subgroup.center GJ := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := hπs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc y']
    rw [center_P, Subgroup.mem_bot] at hπc
    rw [← hker]
    exact hπc
  have hcard : Nat.card π.ker ≤ 2 := by
    have := LargeExtraspecial.S63.j2SchurInput X hX.commutator_eq_top
      ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans e⟩
    rwa [hcen, ← hker] at this
  have hkerc : π.ker ≤ Subgroup.center X := by rw [hker, hcen]
  have r1 := rep_eltOf o1
  have r2 := rep_eltOf o2
  have r3 := rep_eltOf o3
  have r4 := rep_eltOf o4
  have r5 := rep_eltOf o5
  have r6 := rep_eltOf o6
  obtain ⟨v₁, hv₁⟩ := hπs (eltOf j2E8v1Arr o1)
  obtain ⟨v₂, hv₂⟩ := hπs (eltOf j2E8v2Arr o2)
  obtain ⟨s, hs⟩ := hπs (eltOf j2E8sArr o3)
  obtain ⟨u₁, hu₁⟩ := hπs (eltOf j2E8u1Arr o4)
  obtain ⟨u₂, hu₂⟩ := hπs (eltOf j2E8u2Arr o5)
  obtain ⟨t, ht⟩ := hπs (eltOf j2E8tArr o6)
  have r12 := rep_mul r1 r2
  have r45 := rep_mul r4 r5
  have rw1 := rep_mul r1 r4
  have rw2 := rep_mul r2 r5
  refine exists_elemAbelian_eight_of_lifts π hkerc hcard (v₁ := v₁) (v₂ := v₂) (s := s)
    (u₁ := u₁) (u₂ := u₂) (t := t) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [hv₁, hv₂, hs, hu₁, hu₂, ht]
  · rw [sq]; exact eq_of_rep (rep_mul r1 r1) rep_one q1
  · exact eq_of_rep (rep_conj r3 (okA_spec o3).1 r1) r2 q2
  · exact eq_of_rep (rep_conj r3 (okA_spec o3).1 r2) r12 q3
  · rw [sq]; exact eq_of_rep (rep_mul r4 r4) rep_one q4
  · exact eq_of_rep (rep_conj r6 (okA_spec o6).1 r4) r5 q5
  · exact eq_of_rep (rep_conj r6 (okA_spec o6).1 r5) r45 q6
  · exact (commute_of_commA r1 r4 c1).eq
  · exact (commute_of_commA r1 r5 c2).eq
  · exact (commute_of_commA r2 r4 c3).eq
  · exact (commute_of_commA r2 r5 c4).eq
  · exact (commute_of_commA r1 r6 c5).eq
  · exact (commute_of_commA r2 r6 c6).eq
  · exact ⟨ne_of_rep r1 rep_one n1, ne_of_rep r2 rep_one n2, ne_of_rep r2 r1 n3,
      ne_of_rep r12 rep_one n4, ne_of_rep r4 rep_one n5, ne_of_rep r5 rep_one n6,
      ne_of_rep r5 r4 n7, ne_of_rep r45 rep_one n8, ne_of_rep r4 r1 n9, ne_of_rep r4 r2 n10,
      ne_of_rep r4 r12 n11, ne_of_rep rw1 rep_one n12, ne_of_rep rw2 rep_one n13,
      ne_of_rep rw2 rw1 n14, ne_of_rep (rep_mul rw1 rw2) rep_one n15⟩

end CFSG.RankThree.PartTwo.Sec17.J2CoverE8

end
