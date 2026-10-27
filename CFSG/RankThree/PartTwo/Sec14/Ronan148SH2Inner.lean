module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SComp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S

section Inner


theorem rowH2_of_good425 {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    (hcube : CubeInner S)
    (h : ∀ s : S, orderOf s = 3 → Good425 (Subgroup.centralizer ({s} : Set S))) : RowH2 S := by
  intro Γ _ _ C hC4 hCθ _ A L K d hA hLA hdA hd1 _ hLq hCL hLd hKM hKsn hKq _ hA6 ⟨e⟩ hZL
  exfalso
  have hLC : L ≤ C := hLA ▸ le_sup_left
  have hAC : A ≤ C := hLA ▸ le_sup_right
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hKd : K ≤ Subgroup.centralizer {d} := hKM.trans inf_le_right
  have hZ3 := isPGroup_center_of_normal hCθ hLC hCL hLq
  obtain ⟨z, hzK, hKz, hz3, hZ⟩ := exists_pCore_center_eq_zpowers hKq hA6.1
  have hLz : ¬ L ≤ Subgroup.centralizer {z} := by
    intro hLz
    apply hZL
    rw [hZ, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLz hl)
  obtain ⟨-, hinf, -, -, -⟩ := exists_cq_bar hZ3 hKL hKq hzK hKz hz3 hZ hLz
  have hdN : d ∈ Subgroup.normalizer (L : Set Γ) := hCL (hAC hdA)
  set τ := descAut L ⟨d, hdN⟩ with hτ
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set Γ)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  obtain ⟨y, hy⟩ := cubeInner_of_mulEquiv e hcube τ hτ3
  have hZS : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hex : e x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g']
    rw [hcen, Subgroup.mem_bot] at hex
    exact (map_eq_one_iff e e.injective).mp hex
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hLd
    have hτ1 : τ = 1 := by rw [← hy, map_one]
    have hdC := (descAut_eq_one_iff hLq.1 ⟨d, hdN⟩).mp hτ1
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdC l hl
  have hy3 : y ^ 3 = 1 := by
    have hc : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, hy, hτ3]
    have hmem : y ^ 3 ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) => φ g) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [hg]
        _ = y ^ 3 * g := by group
    rw [hZS, Subgroup.mem_bot] at hmem
    exact hmem
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hfix : autFix τ = Subgroup.centralizer ({y} : Set (↥L ⧸ Subgroup.center ↥L)) := by
    rw [← hy]
    exact RonanK429H.autFix_conj y
  let eB := equivBar hKL hinf
  have hle : (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
      Subgroup.centralizer ({y} : Set (↥L ⧸ Subgroup.center ↥L)) := by
    rw [← hfix]
    exact map_le_autFix hdN hKd
  have hsn := isSubnormal_bar hdN hKM hKsn
  rw [← hτ, hfix] at hsn
  have hgood : Good425 (Subgroup.centralizer ({y} : Set (↥L ⧸ Subgroup.center ↥L))) :=
    good425_centralizer_of_mulEquiv e (h (e y) (by rw [MulEquiv.orderOf_eq]; exact hyo))
  exact hgood _ hle (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hKq) hsn
    (isType425_theta_congr eB (Or.inr (Or.inl hA6.isExtOf)))

theorem rowOfH2_of_good425 {X : Type} [Group X] (hcube : CubeInner X)
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → ∀ s : S, orderOf s = 3 →
        Good425 (Subgroup.centralizer ({s} : Set S))) :
    RowOfH2 X := by
  intro S _ _ hs hna ⟨eX⟩
  exact rowH2_of_good425 (RonanK429H.center_eq_bot_of_simple_nonab hna) (cubeInner_of_mulEquiv eX hcube)
    (h S hs hna ⟨eX⟩)

end Inner

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
