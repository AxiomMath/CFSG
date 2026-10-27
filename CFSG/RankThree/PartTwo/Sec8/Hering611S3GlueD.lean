module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3App
public import CFSG.RankThree.PartTwo.Sec8.Hering611SBasic
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section GlueD


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem Cfg611.imageSub_inf_K_eq (C : Cfg611 G A c L E T d S K) {k a : G} (hkA : k ∈ A)
    (hkK : k ∈ K) (haA : a ∈ A) (haK : a ∈ K) (h27 : Nat.card (A ⊓ K : Subgroup G) = 27)
    (hJ1 : Nat.card (Subgroup.centralizer ((Subgroup.closure
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hkK⟩,
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩} :
        Set (K ⧸ aschbacherSolvableCore 3 K)) : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
      Set (K ⧸ aschbacherSolvableCore 3 K))) = 27) :
    imageSub K (A ⊓ K) = Subgroup.centralizer ((Subgroup.closure
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hkK⟩,
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩} :
        Set (K ⧸ aschbacherSolvableCore 3 K)) : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
      Set (K ⧸ aschbacherSolvableCore 3 K)) := by
  have hBK : A ⊓ K ≤ K := inf_le_right
  have hB3 : IsPGroup 3 (A ⊓ K : Subgroup G) :=
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian
      C.toFrame611.isElemAbelian).to_le inf_le_left
  have hcomm : ∀ z u : K, (z : G) ∈ A → (u : G) ∈ A →
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) z *
          QuotientGroup.mk' (aschbacherSolvableCore 3 K) u =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) u *
          QuotientGroup.mk' (aschbacherSolvableCore 3 K) z := by
    intro z u hz hu
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact C.toFrame611.comm_of_mem hz hu
  have hEbar : Subgroup.closure
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hkK⟩,
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩} :
        Set (K ⧸ aschbacherSolvableCore 3 K)) ≤
      Subgroup.centralizer (imageSub K (A ⊓ K) : Set (K ⧸ aschbacherSolvableCore 3 K)) := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe] at hh
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hh
      exact hcomm z ⟨k, hkK⟩ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1 hkA
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe] at hh
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hh
      exact hcomm z ⟨a, haK⟩ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1 haA
  have hle : imageSub K (A ⊓ K) ≤ Subgroup.centralizer ((Subgroup.closure
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hkK⟩,
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩} :
        Set (K ⧸ aschbacherSolvableCore 3 K)) : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
      Set (K ⧸ aschbacherSolvableCore 3 K)) :=
    Subgroup.le_centralizer_iff.mpr hEbar
  apply Subgroup.eq_of_le_of_card_ge hle
  exact le_of_eq (by rw [hJ1, card_imageSub_of_isPGroup hBK hB3, h27])

theorem Cfg611.exists_conj_g (C : Cfg611 G A c L E T d S K) {k : K} {j : ℤ} (hkA : (k : G) ∈ A)
    (hck : c = d ^ j * (k : G)) {a : G} (haA : a ∈ A) (haK : a ∈ K) {m : ℕ}
    (hAdec : ∀ x ∈ A, ∃ k' ∈ A ⊓ K, x * k'⁻¹ ∈ Subgroup.zpowers d)
    (hB0 : imageSub K (A ⊓ K) = Subgroup.centralizer ((Subgroup.closure
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 K) k,
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩} :
        Set (K ⧸ aschbacherSolvableCore 3 K)) : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
      Set (K ⧸ aschbacherSolvableCore 3 K)))
    (hfuse : ∃ gb ∈ Subgroup.normalizer ((Subgroup.centralizer ((Subgroup.closure
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 K) k,
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩} :
        Set (K ⧸ aschbacherSolvableCore 3 K)) : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
      Set (K ⧸ aschbacherSolvableCore 3 K)) : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
      Set (K ⧸ aschbacherSolvableCore 3 K)),
      gb * QuotientGroup.mk' (aschbacherSolvableCore 3 K) k * gb⁻¹ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) k *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩) ^ m) :
    ∃ g ∈ K, g ∈ Subgroup.normalizer (A : Set G) ∧ g * d * g⁻¹ = d ∧ g * c * g⁻¹ = c * a ^ m := by
  have hBK : A ⊓ K ≤ K := inf_le_right
  have hB3 : IsPGroup 3 (A ⊓ K : Subgroup G) :=
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian
      C.toFrame611.isElemAbelian).to_le inf_le_left
  have hkB : (k : G) ∈ A ⊓ K := Subgroup.mem_inf.mpr ⟨hkA, k.2⟩
  have haB : a ∈ A ⊓ K := Subgroup.mem_inf.mpr ⟨haA, haK⟩
  have hfuse' : ∃ gb ∈ Subgroup.normalizer
      (imageSub K (A ⊓ K) : Set (K ⧸ aschbacherSolvableCore 3 K)),
      gb * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨(k : G), hBK hkB⟩ * gb⁻¹ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨(k : G), hBK hkB⟩ *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, hBK haB⟩) ^ m := by
    rw [hB0]
    exact hfuse
  obtain ⟨g, hgK, hgB, hgk⟩ := exists_conj_fuse hBK hB3 hkB haB hfuse'
  have hgd_comm : g * d = d * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (C.K_le_centralizer hgK)
  have hgd : g * d * g⁻¹ = d := by
    rw [hgd_comm, mul_inv_cancel_right]
  have hgz : ∀ z ∈ Subgroup.zpowers d, g * z * g⁻¹ = z := by
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute g d := hgd_comm
    rw [(hc.zpow_right n).eq, mul_inv_cancel_right]
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨k'', hk''B, hxk⟩ := hAdec x hx
    have hzA : x * k''⁻¹ ∈ A := A.mul_mem hx (A.inv_mem (Subgroup.mem_inf.mp hk''B).1)
    have hk''' : g * k'' * g⁻¹ ∈ A ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp hgB k'').mp hk''B
    have e : g * x * g⁻¹ = (g * (x * k''⁻¹) * g⁻¹) * (g * k'' * g⁻¹) := by group
    rw [e, hgz _ hxk]
    exact A.mul_mem hzA (Subgroup.mem_inf.mp hk''').1
  have hgdj : g * d ^ j * g⁻¹ = d ^ j := hgz _ (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)
  have e2 : g * (d ^ j * (k : G)) * g⁻¹ = (g * d ^ j * g⁻¹) * (g * (k : G) * g⁻¹) := by
    group
  refine ⟨g, hgK, hgA, hgd, ?_⟩
  rw [hck, e2, hgdj, hgk, mul_assoc]

end GlueD

end CFSG.RankThree.PartTwo.Sec8.Hering611
