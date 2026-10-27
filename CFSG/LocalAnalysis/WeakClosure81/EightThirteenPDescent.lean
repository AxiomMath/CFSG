module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {Q : Type} [Group Q] [Finite Q]

private theorem wc813pdes_relIndex_inf_sup {R S J : Subgroup Q} [R.Normal] (hRS : R ≤ S) :
    (S ⊓ J).relIndex J = S.relIndex (J ⊔ R) := by
  have hker : MonoidHom.ker (QuotientGroup.mk' R : Q →* Q ⧸ R) = R := QuotientGroup.ker_mk' R
  have hcomap : (S.map (QuotientGroup.mk' R)).comap (QuotientGroup.mk' R) = S := by
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hRS]
  have hmapR : R.map (QuotientGroup.mk' R) = ⊥ :=
    (Subgroup.map_eq_bot_iff R).mpr (le_of_eq hker.symm)
  have hmapJ : (J ⊔ R).map (QuotientGroup.mk' R) = J.map (QuotientGroup.mk' R) := by
    rw [Subgroup.map_sup, hmapR, sup_bot_eq]
  have hSJ : S.relIndex J =
      (S.map (QuotientGroup.mk' R)).relIndex (J.map (QuotientGroup.mk' R)) := by
    conv_lhs => rw [← hcomap]
    exact Subgroup.relIndex_comap (S.map (QuotientGroup.mk' R)) (QuotientGroup.mk' R) (K := J)
  have hSJR : S.relIndex (J ⊔ R) =
      (S.map (QuotientGroup.mk' R)).relIndex (J.map (QuotientGroup.mk' R)) := by
    conv_lhs => rw [← hcomap]
    rw [Subgroup.relIndex_comap (S.map (QuotientGroup.mk' R)) (QuotientGroup.mk' R)
      (K := J ⊔ R), hmapJ]
  rw [Subgroup.inf_relIndex_right, hSJ, ← hSJR]

theorem exists_subgroup_sup_eq_of_odd {R J S : Subgroup Q} [R.Normal]
    (hodd : Odd (Nat.card ↥(J ⊓ R))) (hRS : R ≤ S) (hSL : S ≤ J ⊔ R)
    (h2 : ∀ s ∈ S, ∃ k : ℕ, s ^ (2 ^ k) ∈ R) (hidx : ¬ 2 ∣ S.relIndex (J ⊔ R)) :
    ∃ S' : Subgroup Q, S' ≤ J ∧ (∀ s ∈ S', ∃ k : ℕ, s ^ (2 ^ k) = 1) ∧
      ¬ 2 ∣ S'.relIndex J ∧ S' ⊔ R = S := by
  set M : Subgroup Q := S ⊓ J with hM
  have hMS_le : M ≤ S := hM.le.trans inf_le_left
  have hSM : S = M ⊔ R := by
    apply le_antisymm
    · intro s hs
      obtain ⟨j, hj, r, hr, hjr⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := J) (t := R)).mp (hSL hs)
      have hjS : j ∈ S := by
        have hj_eq : j = s * r⁻¹ := by rw [← hjr]; group
        rw [hj_eq]
        exact S.mul_mem hs (S.inv_mem (hRS hr))
      exact (Subgroup.mem_sup_of_normal_right (s := M) (t := R)).mpr
        ⟨j, hM.le ⟨hjS, hj⟩, r, hr, hjr⟩
    · exact sup_le hMS_le hRS
  haveI hN : (R.subgroupOf M).Normal := Subgroup.Normal.subgroupOf inferInstance M
  let f : ↥M →* ↥M ⧸ (R.subgroupOf M) := QuotientGroup.mk' (R.subgroupOf M)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective (R.subgroupOf M)
  have hX2 : IsPGroup 2 (↥M ⧸ (R.subgroupOf M)) := by
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) x
    obtain ⟨k, hk⟩ := h2 (m : Q) (hM.le m.2).1
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥M)
  let S' : Subgroup Q := (P : Subgroup ↥M).map M.subtype
  have hS'2 : IsPGroup 2 S' := P.2.map M.subtype
  have hS'M : S' ≤ M := by
    rintro x ⟨p, -, rfl⟩
    exact p.2
  have hS'J : S' ≤ J := hS'M.trans (hM.le.trans inf_le_right)
  have hS'pow : ∀ s ∈ S', ∃ k : ℕ, s ^ (2 ^ k) = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := hS'2 ⟨s, hs⟩
    exact ⟨k, by simpa using hk⟩
  have hPtop : (P : Subgroup ↥M).map f = ⊤ := by
    rw [← Sylow.coe_mapSurjective hf P]
    refine Subgroup.index_eq_one.mp ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX2
    obtain ⟨k, -, hk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp
        (hn ▸ Subgroup.index_dvd_card (H := (Sylow.mapSurjective hf P : Subgroup _)))
    rw [hk]
    by_contra hne
    apply Sylow.not_dvd_index (P.mapSurjective hf)
    rw [hk]
    exact dvd_pow_self 2 (by rintro rfl; exact hne (by norm_num))
  have hsup : (P : Subgroup ↥M) ⊔ (R.subgroupOf M) = ⊤ := by
    have h := congrArg (Subgroup.comap f) hPtop
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
  have hMS : M = S' ⊔ (M ⊓ R) := by
    have h := congrArg (Subgroup.map M.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_comm] at h
    exact h.symm
  refine ⟨S', hS'J, hS'pow, ?_, ?_⟩
  · have hsub : S'.subgroupOf M = (P : Subgroup ↥M) := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨p, hp, hpx⟩
        have hpx' : p = x := Subtype.ext hpx
        rwa [hpx'] at hp
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [← Subgroup.relIndex_mul_relIndex (H := S') (K := M) (L := J) hS'M
      (hM.le.trans inf_le_right)]
    refine Nat.prime_two.not_dvd_mul ?_ ?_
    · change ¬ 2 ∣ (S'.subgroupOf M).index
      rw [hsub]
      exact Sylow.not_dvd_index P
    · rw [hM, wc813pdes_relIndex_inf_sup hRS]
      exact hidx
  · rw [hSM, hMS, sup_assoc,
      show (M ⊓ R) ⊔ R = R from sup_eq_right.mpr inf_le_right]

theorem wc813pcomp_isMaxParabolicMod_inf {R J P : Subgroup Q} [R.Normal]
    (hodd : Odd (Nat.card ↥(J ⊓ R))) (hP : IsMaxParabolicMod R (J ⊔ R) P) :
    IsMaxParabolicMod ⊥ J (P ⊓ J) := by
  obtain ⟨hRP, hPL, hmax, S, hRS, hSL, h2, hidx, hN⟩ := hP
  have hP_eq : P = (P ⊓ J) ⊔ R := by
    apply le_antisymm
    · intro p hp
      obtain ⟨j, hj, r, hr, hjr⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := J) (t := R)).mp (hPL.le hp)
      have hjP : j ∈ P := by
        have hj_eq : j = p * r⁻¹ := by rw [← hjr]; group
        rw [hj_eq]
        exact P.mul_mem hp (P.inv_mem (hRP hr))
      exact (Subgroup.mem_sup_of_normal_right (s := P ⊓ J) (t := R)).mpr
        ⟨j, ⟨hjP, hj⟩, r, hr, hjr⟩
    · exact sup_le inf_le_left hRP
  have hlt : P ⊓ J < J := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hJP : J ≤ P := by rw [← heq]; exact inf_le_left
    exact hPL.ne (le_antisymm (sup_le hJP hRP) hPL.le).symm
  have hmax' : ∀ Y : Subgroup Q, P ⊓ J < Y → Y ≤ J → Y = J := by
    intro Y hYlt hYJ
    have hPY : P ≤ Y ⊔ R := by
      rw [hP_eq]
      exact sup_le (hYlt.le.trans le_sup_left) le_sup_right
    have hne : P ≠ Y ⊔ R := by
      intro heq
      have hYPJ : Y ≤ P ⊓ J := by
        rw [heq]
        exact le_inf le_sup_left hYJ
      exact hYlt.ne (le_antisymm hYPJ hYlt.le).symm
    have hEq : Y ⊔ R = J ⊔ R :=
      hmax (Y ⊔ R) (lt_of_le_of_ne hPY hne) (sup_le (hYJ.trans le_sup_left) le_sup_right)
    apply le_antisymm hYJ
    intro j hj
    have hjYR : j ∈ Y ⊔ R := by rw [hEq]; exact Subgroup.mem_sup_left hj
    obtain ⟨y, hy, r, hr, hyr⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := Y) (t := R)).mp hjYR
    have hrJ : r ∈ J := by
      have hr_eq : r = y⁻¹ * j := by rw [← hyr]; group
      rw [hr_eq]
      exact J.mul_mem (J.inv_mem (hYJ hy)) hj
    have hJR_le : J ⊓ R ≤ Y :=
      (le_inf (inf_le_right.trans hRP) inf_le_left).trans hYlt.le
    rw [← hyr]
    exact Y.mul_mem hy (hJR_le ⟨hrJ, hr⟩)
  obtain ⟨S', hS'J, hS'pow, hS'idx, hS'S⟩ :=
    exists_subgroup_sup_eq_of_odd hodd hRS hSL h2 hidx
  refine ⟨bot_le, hlt, hmax', S', bot_le, hS'J, ?_, hS'idx, ?_⟩
  · intro s hs
    obtain ⟨k, hk⟩ := hS'pow s hs
    exact ⟨k, Subgroup.mem_bot.mpr hk⟩
  · intro x hx
    obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxN' : x ∈ Subgroup.normalizer (S : Set Q) := by
      have h1 := Subgroup.normalizer_le_normalizer_sup_normal (H := S') (K := R) hxN
      rwa [hS'S] at h1
    have hxP : x ∈ P := hN (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hxJ, hxN'⟩)
    exact Subgroup.mem_inf.mpr ⟨hxP, hxJ⟩

end CFSG.LocalAnalysis.WeakClosure81

end
