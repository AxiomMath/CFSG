module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3KBase
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem not_three_dvd_card_of_two {H : Type*} [Group H] [Finite H] {W : Subgroup H}
    (hW : IsPGroup 2 W) : ¬ 3 ∣ Nat.card W := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hW
  rw [hk]
  intro h
  have h3 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
  omega

private theorem conj_mem_preimageSub {K : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G))
    {W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)}
    (hW : ∀ w ∈ W, Sec12.thetaBarAct K ⟨x, hxN⟩ w ∈ W) {y : G}
    (hy : y ∈ preimageSub K W) : x * y * x⁻¹ ∈ preimageSub K W := by
  obtain ⟨hyK, hyW⟩ := mem_preimageSub.mp hy
  have hzK : x * y * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxN y).mp hyK
  refine mem_preimageSub.mpr ⟨hzK, ?_⟩
  have h1 := hW _ hyW
  rw [Sec12.thetaBarAct_mk] at h1
  exact h1

private theorem le_normalizer_preimageSub_of_inv {K E' : Subgroup G}
    (hE'K : E' ≤ Subgroup.normalizer (K : Set G))
    {W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)}
    (hWinv : ∀ (x : G) (hx : x ∈ E'), ∀ w ∈ W, Sec12.thetaBarAct K ⟨x, hE'K hx⟩ w ∈ W) :
    E' ≤ Subgroup.normalizer ((preimageSub K W : Subgroup G) : Set G) := by
  intro x hx
  exact mem_normalizer_of_conj_mem fun y hy => conj_mem_preimageSub (hE'K hx) (hWinv x hx) hy

theorem exists_two_lift {K E' : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) (hE3 : IsPGroup 3 E')
    (hE'K : E' ≤ Subgroup.normalizer (K : Set G))
    {W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} (hW2 : IsPGroup 2 W)
    (hWinv : ∀ (x : G) (hx : x ∈ E'), ∀ w ∈ W, Sec12.thetaBarAct K ⟨x, hE'K hx⟩ w ∈ W) :
    ∃ P : Subgroup G, P ≤ K ∧ IsPGroup 2 P ∧ E' ≤ Subgroup.normalizer (P : Set G) ∧
      imageSub K P = W := by
  have hM3 : ¬ 3 ∣ Nat.card (preimageSub K W) := by
    rw [card_preimageSub]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h1
    · exact Sec11.not_three_dvd_card_inSubgroup_theta K h1
    · exact not_three_dvd_card_of_two hW2 h1
  obtain ⟨S, hAS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup
    Nat.prime_three Nat.prime_two hE3 (le_normalizer_preimageSub_of_inv hE'K hWinv) hM3
  set P : Subgroup G := (S : Subgroup (preimageSub K W)).map (preimageSub K W).subtype
    with hPdef
  have hPM : P ≤ preimageSub K W := Subgroup.map_subtype_le _
  have hPK : P ≤ K := hPM.trans (preimageSub_le K W)
  have hP2 : IsPGroup 2 P := S.isPGroup'.map (preimageSub K W).subtype
  refine ⟨P, hPK, hP2, hAS, ?_⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hW2
  have hθ0 : Nat.card (inSubgroup (aschbacherSolvableCore 3) K) ≠ 0 := Nat.card_pos.ne'
  have hW0 : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have hfac : Nat.factorization
      (Nat.card (inSubgroup (aschbacherSolvableCore 3) K) * Nat.card W) 2 = k := by
    rw [Nat.factorization_mul hθ0 hW0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ, hk, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hPcard : Nat.card P = Nat.card W := by
    rw [hPdef, Subgroup.card_map_of_injective (preimageSub K W).subtype_injective,
      Sylow.card_eq_multiplicity S, card_preimageSub, hfac, ← hk]
  apply Subgroup.eq_of_le_of_card_ge
  · exact (imageSub_mono (K := K) hPM).trans (imageSub_preimageSub K W).le
  · exact le_of_eq (by rw [card_imageSub_gen hPK hP2 hθ, hPcard])

theorem sub_lift {K E' P : Subgroup G}
    (hθ : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K))
    (hE'K : E' ≤ Subgroup.normalizer (K : Set G)) (hPK : P ≤ K) (hP2 : IsPGroup 2 P)
    (hE'P : E' ≤ Subgroup.normalizer (P : Set G))
    {V : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} (hVP : V ≤ imageSub K P)
    (hVinv : ∀ (x : G) (hx : x ∈ E'), ∀ w ∈ V, Sec12.thetaBarAct K ⟨x, hE'K hx⟩ w ∈ V) :
    P ⊓ preimageSub K V ≤ P ∧ imageSub K (P ⊓ preimageSub K V) = V ∧
      E' ≤ Subgroup.normalizer ((P ⊓ preimageSub K V : Subgroup G) : Set G) := by
  have hEV := le_normalizer_preimageSub_of_inv hE'K hVinv
  refine ⟨inf_le_left, ?_, fun x hx => mem_normalizer_inf' (hE'P hx) (hEV hx)⟩
  apply le_antisymm
  · exact (imageSub_mono (K := K) inf_le_right).trans (imageSub_preimageSub K V).le
  · intro v hv
    obtain ⟨x, hxP, hxv⟩ := Subgroup.mem_map.mp (hVP hv)
    subst hxv
    have hxV : (x : G) ∈ preimageSub K V := (mem_preimageSub_iff_mk_mem x).mpr hv
    exact mk_mem_imageSub (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxP, hxV⟩)

end CFSG.RankThree.PartTwo.Sec8.Hering611
