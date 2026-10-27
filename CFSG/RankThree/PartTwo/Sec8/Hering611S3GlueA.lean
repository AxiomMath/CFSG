module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3KBase
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped Bracket

variable {G : Type} [Group G] [Finite G]

theorem comm_of_imageSub_comm {K P V : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) (hP2 : IsPGroup 2 P)
    (hVP : V ≤ P) (hPK : P ≤ K)
    (hcomm : ∀ x ∈ imageSub K V, ∀ y ∈ imageSub K V, x * y = y * x) :
    ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  intro x hx y hy
  have hxP : x ∈ P := hVP hx
  have hyP : y ∈ P := hVP hy
  have hxK : x ∈ K := hPK hxP
  have hyK : y ∈ K := hPK hyP
  have hcxy := hcomm _ (mk_mem_imageSub (x := (⟨x, hxK⟩ : K)) hx) _
    (mk_mem_imageSub (x := (⟨y, hyK⟩ : K)) hy)
  have hz : (⟨x, hxK⟩ : K) * ⟨y, hyK⟩ * (⟨x, hxK⟩ : K)⁻¹ * (⟨y, hyK⟩ : K)⁻¹ = 1 := by
    refine mk_injOn_of_isPGroup hP2 hθ ?_ P.one_mem ?_
    · show x * y * x⁻¹ * y⁻¹ ∈ P
      exact P.mul_mem (P.mul_mem (P.mul_mem hxP hyP) (P.inv_mem hxP)) (P.inv_mem hyP)
    · rw [map_one, map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcxy
  have hz' : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hz
  exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact hz')

theorem eq_of_imageSub_eq {K A' B : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) (hB2 : IsPGroup 2 B)
    (hAB : A' ≤ B) (hBK : B ≤ K) (h : imageSub K A' = imageSub K B) : A' = B := by
  have hA2 : IsPGroup 2 A' := IsPGroup.to_le hB2 hAB
  have hA := card_imageSub_gen (hAB.trans hBK) hA2 hθ
  have hB := card_imageSub_gen hBK hB2 hθ
  have hc : Nat.card (imageSub K A') = Nat.card (imageSub K B) := by rw [h]
  exact Subgroup.eq_of_le_of_card_ge hAB (by omega)

theorem le_normalizer_of_image {K P Vi Vj : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) (hP2 : IsPGroup 2 P)
    (hPK : P ≤ K) (hViP : Vi ≤ P) (hVjP : Vj ≤ P)
    (hVi : P ⊓ preimageSub K (imageSub K Vi) ≤ Vi)
    (hnorm : imageSub K Vj ≤ Subgroup.normalizer
      (imageSub K Vi : Set (K ⧸ aschbacherSolvableCore 3 K))) :
    Vj ≤ Subgroup.normalizer (Vi : Set G) := by
  intro v hv
  have hvP : v ∈ P := hVjP hv
  have hvK : v ∈ K := hPK hvP
  have hvN := hnorm (mk_mem_imageSub (x := (⟨v, hvK⟩ : K)) hv)
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have hyP : y ∈ P := hViP hy
  have hyK : y ∈ K := hPK hyP
  have hπw : QuotientGroup.mk' (aschbacherSolvableCore 3 K)
      ((⟨v, hvK⟩ : K) * (⟨y, hyK⟩ : K) * (⟨v, hvK⟩ : K)⁻¹) ∈ imageSub K Vi := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hvN _).mp (mk_mem_imageSub (x := (⟨y, hyK⟩ : K)) hy)
  have hwP : v * y * v⁻¹ ∈ P := P.mul_mem (P.mul_mem hvP hyP) (P.inv_mem hvP)
  exact hVi (show v * y * v⁻¹ ∈ P ⊓ preimageSub K (imageSub K Vi) from
    ⟨hwP, (mem_preimageSub_iff_mk_mem ((⟨v, hvK⟩ : K) * (⟨y, hyK⟩ : K) * (⟨v, hvK⟩ : K)⁻¹)).mpr
      hπw⟩)

theorem exists_fixed_moved {K P : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) (hP2 : IsPGroup 2 P)
    (hPK : P ≤ K) {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyP : y ∈ Subgroup.normalizer (P : Set G)) {yb : K ⧸ aschbacherSolvableCore 3 K}
    (hyact : Sec12.thetaBarAct K ⟨y, hyN⟩ = MulAut.conj yb) {a : G} (haK : a ∈ K)
    (haP : a ∈ Subgroup.normalizer (P : Set G)) {w : K ⧸ aschbacherSolvableCore 3 K}
    (hw : w ∈ imageSub K P) (hwy : yb * w * yb⁻¹ = w)
    (hwa : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩ * w *
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩)⁻¹ ≠ w) :
    ∃ s ∈ P, y * s = s * y ∧ a * s ≠ s * a := by
  obtain ⟨z, hzV, hzw⟩ := Subgroup.mem_map.mp hw
  have hzP : (z : G) ∈ P := Subgroup.mem_subgroupOf.mp hzV
  have hyzP : y * (z : G) * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hyP _).mp hzP
  have hπu : QuotientGroup.mk' (aschbacherSolvableCore 3 K)
      (K.normalizerMonoidHom ⟨y, hyN⟩ z) = QuotientGroup.mk' (aschbacherSolvableCore 3 K) z := by
    rw [← Sec12.thetaBarAct_mk, hyact, MulAut.conj_apply, hzw, hwy]
  have hu : K.normalizerMonoidHom ⟨y, hyN⟩ z = z :=
    mk_injOn_of_isPGroup hP2 hθ hyzP hzP hπu
  have hyz : y * (z : G) = (z : G) * y := by
    have h1 : y * (z : G) * y⁻¹ = (z : G) := congrArg Subtype.val hu
    exact mul_inv_eq_iff_eq_mul.mp h1
  refine ⟨(z : G), hzP, hyz, fun haz => hwa ?_⟩
  have hK : (⟨a, haK⟩ : K) * z * (⟨a, haK⟩ : K)⁻¹ = z := by
    apply Subtype.ext
    show a * (z : G) * a⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr haz
  have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 K)
      ((⟨a, haK⟩ : K) * z * (⟨a, haK⟩ : K)⁻¹) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) z := by
    rw [hK]
  rw [map_mul, map_mul, map_inv, hzw] at h2
  exact h2

end CFSG.RankThree.PartTwo.Sec8.Hering611
