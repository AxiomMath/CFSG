module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Inner
public import CFSG.RankThree.PartTwo.Sec8.Hering611SBasic
import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

private theorem phi_inv_mul_mem_center {X : Type*} [Group X] {x y : X}
    (h : MulAut.conj x = MulAut.conj y) : x⁻¹ * y ∈ Subgroup.center X := by
  apply Sec12.mem_center_of_conj_eq_one
  rw [map_mul, map_inv, h, inv_mul_cancel]

private theorem phi_mk'_eq_iff {X : Type*} [Group X] (Z : Subgroup X) [Z.Normal] {x y : X} :
    QuotientGroup.mk' Z x = QuotientGroup.mk' Z y ↔ x⁻¹ * y ∈ Z :=
  QuotientGroup.eq

section Phi


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem exists_hom_Phi (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hperf : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K))
    (hJ : Nonempty ((K ⧸ aschbacherSolvableCore 3 K) ⧸
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) ≃* Blueprint.NativeSporadic.J3)) :
    ∃ Φ : A →* (K ⧸ aschbacherSolvableCore 3 K) ⧸
        Subgroup.center (K ⧸ aschbacherSolvableCore 3 K),
      (∀ a : A, Φ a = 1 ↔ (a : G) ∈ Subgroup.zpowers d) ∧
      ∀ (a : A) (k : K), (k : G) = (a : G) →
        Φ a = QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K))
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) := by
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := C.A_le_normalizer_K h45
  have hAe := C.toFrame611.isElemAbelian
  let α : A →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec12.thetaBarAct K).comp (Subgroup.inclusion hAK)
  have hα3 : ∀ a : A, α a ^ 3 = 1 := by
    intro a
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 (a : G) a.2)
    rw [← map_pow, ha3, map_one]
  choose g hg using fun a : A =>
    exists_conj_of_pow_three_cover hperf hJ (α a) (hα3 a)
  have hmul : ∀ a b : A,
      QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) (g (a * b)) =
        QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) (g a) *
          QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) (g b) := by
    intro a b
    rw [← map_mul, phi_mk'_eq_iff]
    apply phi_inv_mul_mem_center
    simp only [map_mul, hg]
  refine ⟨MonoidHom.mk' (fun a => QuotientGroup.mk'
    (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) (g a)) hmul, ?_, ?_⟩
  ·
    intro a
    have h1 : g a ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) ↔ α a = 1 := by
      rw [← hg a]
      exact ⟨Sec12.conj_eq_one_of_mem_center, Sec12.mem_center_of_conj_eq_one⟩
    have h2 : α a = 1 ↔ (a : G) ∈ Sec4.thetaQuotCentralizer K :=
      (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (hAK a.2)).symm
    have h3 : (a : G) ∈ Sec4.thetaQuotCentralizer K ↔ (a : G) ∈ Subgroup.zpowers d := by
      constructor
      · intro h
        rw [← C.cent_K]
        exact Subgroup.mem_inf.mpr ⟨a.2, h⟩
      · intro h
        rw [← C.cent_K] at h
        exact (Subgroup.mem_inf.mp h).2
    show QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) (g a) = 1 ↔
      (a : G) ∈ Subgroup.zpowers d
    exact (QuotientGroup.eq_one_iff (g a)).trans (h1.trans (h2.trans h3))
  ·
    intro a k hka
    have hαk : α a = MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) := by
      have hN : (⟨(a : G), hAK a.2⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨(k : G), Subgroup.le_normalizer k.2⟩ := Subtype.ext hka.symm
      change Sec12.thetaBarAct K ⟨(a : G), hAK a.2⟩ = _
      rw [hN, Sec12.thetaBarAct_of_mem k.2]
    show QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) (g a) =
      QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k)
    rw [phi_mk'_eq_iff]
    apply phi_inv_mul_mem_center
    rw [hg a]
    exact hαk

end Phi

end CFSG.RankThree.PartTwo.Sec8.Hering611
