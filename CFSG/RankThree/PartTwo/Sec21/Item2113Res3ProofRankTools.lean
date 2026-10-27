module

public import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.PartTwo.Sec6.Item65Two
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Census.TripleCoverLift

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open Subgroup

theorem false_of_components {X : Type} [Group X] [Finite X] (hrank : localRank 3 X ≤ 3)
    {Lb : Subgroup X} (hLb : IsComponent Lb) (hZ : center Lb = ⊥) {Ub : Subgroup X}
    (hUL : Ub ≤ Lb) (hU1 : Ub ≠ ⊥) (hU2 : IsPGroup 2 Ub) {F : Subgroup X} (hFL : F ≤ Lb)
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hFU : F ≤ normalizer (Ub : Set X)) {z : X} (hz : z ∈ center X) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) {N : Subgroup X} (hN : IsComponent N) (hzN : z ∈ N) {y : X} (hyN : y ∈ N)
    (hy3 : y ^ 3 = 1) (hyc : ∃ n ∈ N, y * n ≠ n * y) : False := by
  have hcen : ∀ w ∈ Lb, (∀ l ∈ Lb, l * w = w * l) → w = 1 := by
    intro w hw hc
    have hw' : (⟨w, hw⟩ : Lb) ∈ center Lb :=
      mem_center_iff.mpr fun g => Subtype.ext (hc g g.2)
    rw [hZ, mem_bot] at hw'
    exact congrArg Subtype.val hw'
  have hzL : z ∉ Lb := fun h => hz1 (hcen z h fun l _ => mem_center_iff.mp hz l)
  have hLN : ∀ l ∈ Lb, ∀ n ∈ N, l * n = n * l := by
    rcases LocalCores.distinct_components_commute hLb hN with h | h
    · exact absurd (h ▸ hzN) hzL
    · intro l hl n hn
      have hmem := commutator_mem_commutator hl hn
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
  have hZz : zpowers z ≤ center X := zpowers_le.mpr hz
  have hzc : ∀ β ∈ F, β * z = z * β := fun β _ => mem_center_iff.mp hz β
  obtain ⟨hBe, hBc⟩ := Sec6.isElemAbelian_sup_zpowers_three hFe (fun h => hzL (hFL h)) hz3 hzc
  have hyB : y ∉ F ⊔ zpowers z := by
    intro hy
    have : (zpowers z).Normal := normal_of_le_center hZz
    rw [← SetLike.mem_coe, mul_normal] at hy
    obtain ⟨f, hf, w, hw, rfl⟩ := hy
    have hwN : w ∈ N := zpowers_le.mpr hzN hw
    have hfN : f ∈ N := by
      have h := N.mul_mem hyN (N.inv_mem hwN)
      rwa [mul_inv_cancel_right] at h
    have hf1 : f = 1 := hcen f (hFL hf) fun l hl => hLN l hl f hfN
    obtain ⟨n, -, hyn⟩ := hyc
    apply hyn
    change f * w * n = n * (f * w)
    rw [hf1, one_mul]
    exact (mem_center_iff.mp (hZz hw) n).symm
  have hyBc : ∀ β ∈ F ⊔ zpowers z, β * y = y * β :=
    Sec4.commute_sup_of_commute (fun β hβ => hLN β (hFL hβ) y hyN) fun β hβ =>
      (mem_center_iff.mp (hZz hβ) y).symm
  obtain ⟨hEe, hEc⟩ := Sec6.isElemAbelian_sup_zpowers_three hBe hyB hy3 hyBc
  have hyU : y ∈ normalizer (Ub : Set X) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu => ?_)
    exact hLN u (hUL hu) y hyN
  have hEU : F ⊔ zpowers z ⊔ zpowers y ≤ normalizer (Ub : Set X) :=
    sup_le (sup_le hFU (zpowers_le.mpr (center_le_normalizer _ hz))) (zpowers_le.mpr hyU)
  have h4 := Census.le_localRank_of_le_normalizer (k := 4) Nat.prime_three hU1 hU2 hEe
    (by rw [hEc, hBc, hF9]; norm_num) hEU
  omega

theorem aschbacherSolvableCore_eq_bot_of_normal {Q : Type*} [Group Q] [Finite Q]
    (hQ : aschbacherSolvableCore 3 Q = ⊥) {N : Subgroup Q} (hN : N.Normal) :
    aschbacherSolvableCore 3 N = ⊥ := by
  have h := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hN.isSubnormal
  rw [hQ, inf_bot_eq, inSubgroup] at h
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h

theorem exists_mulEquiv_map_of_normal {H : Type*} [Group H] [Finite H] (I : Subgroup H)
    (hI : (I.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))).Normal) :
    ∃ η : (I ⧸ aschbacherSolvableCore 3 I) ≃*
        I.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)),
      ∀ l : I, (η (l : I ⧸ aschbacherSolvableCore 3 I) : H ⧸ aschbacherSolvableCore 3 H) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) (l : H) := by
  set θ := aschbacherSolvableCore 3 H
  set π := QuotientGroup.mk' θ
  have hX : aschbacherSolvableCore 3 (H ⧸ θ) = ⊥ := theta_quotient_core_and_ranks.1
  obtain ⟨hθsol, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  obtain ⟨hIsol, -, hI3, hImax, -⟩ :=
    solvable_prime_complement_core_characterization (H := I) Nat.prime_three
  refine exists_quotient_mulEquiv_map π I _ fun l => ⟨fun hl => ?_, fun hl => ?_⟩
  · set ψ := π.subgroupMap I
    have hT : (aschbacherSolvableCore 3 I).map ψ = ⊥ := by
      rw [eq_bot_iff, ← aschbacherSolvableCore_eq_bot_of_normal hX hI]
      obtain ⟨-, -, -, hmax, -⟩ :=
        solvable_prime_complement_core_characterization (H := I.map π) Nat.prime_three
      refine hmax _ ((aschbacherSolvableCore_normal 3 I).map ψ (π.subgroupMap_surjective I))
        ?_ ?_
      · exact Group.isSolvable_of_surjective (ψ.subgroupMap_surjective _)
      · exact fun h => hI3 (h.trans (card_map_dvd _ _))
    have h1 : ψ l ∈ (aschbacherSolvableCore 3 I).map ψ := mem_map_of_mem ψ hl
    rw [hT, mem_bot] at h1
    exact congrArg Subtype.val h1
  · have hlθ : (l : H) ∈ θ := (QuotientGroup.eq_one_iff _).mp hl
    have hinj : Function.Injective
        ((I.subtype.comp (θ.subgroupOf I).subtype).codRestrict θ fun x => x.2) := by
      intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    refine hImax (θ.subgroupOf I) normal_subgroupOf ?_ ?_ (mem_subgroupOf.mpr hlθ)
    · exact Group.isSolvable_of_isSolvable_injective hinj
    · exact fun h => hθ3 (h.trans (card_dvd_of_injective _ hinj))

theorem mul_ne_of_conj_eq_inv {S : Type*} [Group S] {s n : S} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hn : n * s * n⁻¹ = s⁻¹) : n * s ≠ s * n := by
  intro h
  apply hs1
  have h2 : s⁻¹ = s := by rw [← hn, h, mul_inv_cancel_right]
  have h3 : s * s = 1 := by rw [mul_eq_one_iff_eq_inv, h2]
  calc s = s ^ 3 * (s * s)⁻¹ := by group
    _ = 1 := by rw [hs3, h3, inv_one, one_mul]

theorem isQuasisimple_and_exists_of_real {P S : Type*} [Group P] [Group S] [IsSimpleGroup S]
    (hP : Group.IsPerfect P) (e : P ⧸ center P ≃* S) {s n : S} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hn : n * s * n⁻¹ = s⁻¹) :
    IsQuasisimple P ∧ ∃ y : P, y ^ 3 = 1 ∧ y ∉ center P := by
  refine ⟨⟨hP, e.isSimpleGroup, e.symm n, e.symm s, fun h => ?_⟩, ?_⟩
  · apply mul_ne_of_conj_eq_inv hs3 hs1 hn
    apply e.symm.injective
    rw [map_mul, map_mul, h]
  · set φ : P →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center P)) with hφ
    have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : φ.ker = center P := by
      ext x
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hy3⟩ := Sec4.Census.TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφs
      hker.le (p := 3) ⟨1, rfl⟩ hs3 hn
    refine ⟨y, hy3, fun hyc => hs1 ?_⟩
    rw [← hy]
    exact MonoidHom.mem_ker.mp (hker ▸ hyc)

theorem quotient_theta_of_isQuasisimple {P : Type*} [Group P] [Finite P] (hP : IsQuasisimple P)
    {y : P} (hy3 : y ^ 3 = 1) (hy : y ∉ center P) :
    IsQuasisimple (P ⧸ aschbacherSolvableCore 3 P) ∧
      ∃ w : P ⧸ aschbacherSolvableCore 3 P, w ^ 3 = 1 ∧
        w ∉ center (P ⧸ aschbacherSolvableCore 3 P) := by
  have hθZ : aschbacherSolvableCore 3 P ≤ center P := by
    rcases LocalCores.quasisimple_normal_subgroups hP (aschbacherSolvableCore_normal 3 P) with
      h | h
    · exfalso
      obtain ⟨hsol, -⟩ := solvable_prime_complement_core_characterization (H := P) Nat.prime_three
      have : Group.IsSolvable (⊤ : Subgroup P) := h ▸ hsol
      have : Group.IsSolvable P :=
        Group.isSolvable_of_isSolvable_injective (f := (topEquiv (G := P)).symm.toMonoidHom)
          (topEquiv (G := P)).symm.injective
      have : Nontrivial P := LocalCores.isQuasisimple_nontrivial hP
      have := hP.1
      exact Group.IsPerfect.not_isSolvable P inferInstance
    · exact h
  obtain ⟨hq, hcomap, -⟩ := LocalCores.quasisimple_central_quotient hP _ hθZ
  refine ⟨hq, QuotientGroup.mk' _ y, by rw [← map_pow, hy3, map_one], fun h => hy ?_⟩
  rw [← hcomap]
  exact h

theorem alternating_six_real : ∃ s n : alternatingGroup (Fin 6),
    s ^ 3 = 1 ∧ s ≠ 1 ∧ n * s * n⁻¹ = s⁻¹ := by
  refine ⟨⟨Equiv.swap 0 2 * Equiv.swap 0 1, ?_⟩, ⟨Equiv.swap 1 2 * Equiv.swap 3 4, ?_⟩, ?_, ?_,
    ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · decide
  · decide
  · decide

theorem alternating_seven_real : ∃ s n : alternatingGroup (Fin 7),
    s ^ 3 = 1 ∧ s ≠ 1 ∧ n * s * n⁻¹ = s⁻¹ := by
  refine ⟨⟨Equiv.swap 0 2 * Equiv.swap 0 1, ?_⟩, ⟨Equiv.swap 1 2 * Equiv.swap 3 4, ?_⟩, ?_, ?_,
    ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · decide
  · decide
  · decide

theorem specialLinear_three_exists (F : Type*) [Field F] :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F, g ^ 3 = 1 ∧
      g ∉ center (Matrix.SpecialLinearGroup (Fin 3) F) := by
  set M : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0] with hM
  have hdet : M.det = 1 := by simp [hM, Matrix.det_fin_three]
  set g : Matrix.SpecialLinearGroup (Fin 3) F := ⟨M, hdet⟩
  have hgM : (g : Matrix (Fin 3) (Fin 3) F) = M := rfl
  refine ⟨g, ?_, fun h => ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hgM, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [hM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  · obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have h10 := congrFun (congrFun hr 1) 0
    rw [hgM] at h10
    simp [hM] at h10

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof
