module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofThree
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofKlein
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.Sporadic.J2
public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

variable {G : Type} [Group G]

theorem exists_not_commute_of_isPerfect {X : Type*} [Group X] [Nontrivial X]
    (hX : Group.IsPerfect X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : commutator X = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact h y x
  have ht : commutator X = ⊤ := hX.commutator_eq_top
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  have ha : a ∈ (⊥ : Subgroup X) := hc ▸ ht ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup X) := hc ▸ ht ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  exact hab (ha.trans hb.symm)

theorem star_simple_three [Finite G] (h211 : Item211) (h2131 : Item2131One)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (h27 : Nat.card A = 3 ^ 3)
    [IsSimpleGroup L] :
    Nonempty (starOf A L ≃* DihedralGroup 4) ∧
      starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) ∧
      ((starOf A L : Set (MulAut A)) ∩ dStar A).Nonempty ∧
      ∀ φ ∈ starOf A L, IsReflectionOn φ → ∃ ℓ : Subgroup G, ℓ ≤ L ∧ Nat.card ℓ = 3 ∧
        L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
          L ⊓ Subgroup.centralizer (ℓ : Set G) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hL3 : L ∈ lThreeStar A := ⟨mem_lZeroStar_of_mem_lThreeStarPairs hpair.mem_pair, E,
    hpair.mem_E, U, hpair.mem_U, c, hpair.mem_pair⟩
  have hab := exists_not_commute_of_isPerfect hLp
  have hcL := not_mem_of_isSimpleGroup hab hc1 hLC
  obtain ⟨σ₁, h₁, σ₂, h₂, h11, h22, hr₁, hr₂, hcl, hcase⟩ :=
    star_three_cases h211 h2131 hpair hcA h27
  have hW₁ := commOf_le_comap_of_mem_starOf hAe hcA hLc h₁ h11
  have hW₂ := commOf_le_comap_of_mem_starOf hAe hcA hLc h₂ h22
  rcases hcase with ⟨-, -, hcmem, -⟩ | ⟨he, h9, hcρ, -⟩
  · exact absurd ((sup_le hW₁ hW₂) hcmem) hcL
  · refine ⟨he, eq_closure_inter h₁ h₂ ⟨hr₁, L, hL3, h₁⟩ ⟨hr₂, L, hL3, h₂⟩ hcl,
      ⟨σ₁, h₁, hr₁, L, hL3, h₁⟩, fun φ hφL hφ => ?_⟩
    obtain ⟨d, hdL, hd3, heq⟩ := exists_mem_eq_inf_centralizer_zpowers hAe h27 hcA hc1 hLC h9
      hcρ ((commOf_mul_le σ₁ σ₂).trans (sup_le hW₁ hW₂)) hφL hφ
    exact ⟨Subgroup.zpowers d, Subgroup.zpowers_le.mpr hdL, hd3, heq⟩

theorem star_SL3_three [Finite G] (h211 : Item211)
    (h2131 : Item2131One) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (h27 : Nat.card A = 3 ^ 3) {n : ℕ} (hn : 0 < n) (he : Even n) (eL : L ≃* SL3 n) :
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) ∧ IsTypeCOnBarSL A L ∧
      starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) ∧
      ((starOf A L : Set (MulAut A)) ∩ dStar A).Nonempty ∧
      ∀ φ ∈ starOf A L, IsReflectionOn φ → ∃ b ∈ A, (∃ x ∈ L, x * b ≠ b * x) ∧
        Even (Nat.card (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G)) ∧
        L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
          L ⊓ Subgroup.centralizer ({b} : Set G) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hL3 : L ∈ lThreeStar A := ⟨mem_lZeroStar_of_mem_lThreeStarPairs hpair.mem_pair, E,
    hpair.mem_E, U, hpair.mem_U, c, hpair.mem_pair⟩
  obtain ⟨eB⟩ := nonempty_lBar_mulEquiv_SL3 hn he eL
  obtain ⟨σ₁, h₁, σ₂, h₂, h11, h22, hr₁, hr₂, hcl, hcase⟩ :=
    star_three_cases h211 h2131 hpair hcA h27
  rcases hcase with ⟨hS3, hfix, -, hinfo⟩ | ⟨-, -, -, hinfo⟩
  ·
    have hC : IsTypeCOnBarSL A L := by
      rcases hinfo with heJ | ⟨m, -, -, ⟨⟨eP⟩, -⟩ | ⟨-, hC⟩⟩
      · obtain ⟨eJ⟩ := heJ
        have := CFSG.Sporadic.J2.isSimpleGroup_J2
        exact (false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eJ.symm.trans eB)).elim
      · have := isSimpleGroup_projSL_three (GaloisField 2 m)
        exact (false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eP.symm.trans eB)).elim
      · exact hC
    refine ⟨hS3, hC, eq_closure_inter h₁ h₂ ⟨hr₁, L, hL3, h₁⟩ ⟨hr₂, L, hL3, h₂⟩ hcl,
      ⟨σ₁, h₁, hr₁, L, hL3, h₁⟩, fun φ hφL hφ => ?_⟩
    exact exists_mem_eq_inf_centralizer_singleton hAe h27 hcA hc1 hLC
      ((starOf A L).mul_mem h₁ h₂) hfix hφL hφ
  ·
    exfalso
    rcases hinfo with ((⟨m, hm, hme, heS | heS⟩) | heS) | hX | hX
    · obtain ⟨eS⟩ := heS
      have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
      have := isSimpleGroup_projSp_two hm2
      exact false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eS.symm.trans eB)
    · obtain ⟨eS⟩ := heS
      have := isSimpleGroup_projSU (m := 4) (n := m) le_rfl hm
      exact false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eS.symm.trans eB)
    · obtain ⟨eS⟩ := heS
      have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
      exact false_of_isSimpleGroup_of_mulEquiv_SL3 hn he (eS.symm.trans eB)
    · exact false_of_statedClassicalModel_PSL_of_mulEquiv_SL3 hX hn he eB
    · exact false_of_statedClassicalModel_PSL_of_mulEquiv_SL3 hX hn he eB

theorem star_four [Finite G] (h211 : Item211)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (h81 : Nat.card A = 3 ^ 4)
    {n : ℕ} (hn : 1 < n) (eL : L ≃* projSU 4 2 n) :
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl (by omega)
  have : IsSimpleGroup L := eL.isSimpleGroup
  have eθ := mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot_of_mulEquiv hLp eL)
  have : IsSimpleGroup (lBar L) := eθ.symm.isSimpleGroup
  have hab : ∃ a b : lBar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_not_commute_of_isPerfect hLp
    exact ⟨eθ a, eθ b, fun h => hab (eθ.injective (by rw [map_mul, map_mul, h]))⟩
  rcases h211 G A E U c L hpair with ⟨-, -, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ |
      ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, -, he⟩ |
      ⟨hJ, -, -⟩ | ⟨-, h27, -⟩ | ⟨hSp, -, -⟩
  all_goals first
    | (rw [h81] at h27; norm_num at h27)
    | skip
  · exact he
  · rcases hJ with heJ | hT
    · obtain ⟨eJ⟩ := heJ
      exact (false_of_mulEquiv_projSU_four_of_J3 (by omega) (eθ.symm.trans eL) eJ).elim
    · exact (not_isTripleCover_of_isSimpleGroup hab hT).elim
  · exact (false_of_projSU_four_of_PSp_three (by omega) (eθ.symm.trans eL) hSp).elim

theorem card_inf_eq_of_star_four [Finite G] {A L : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h81 : Nat.card A = 3 ^ 4) {c : G} (hcA : c ∈ A)
    (hcL : c ∉ L) (hLc : L ∈ thetaComponentsAt 3 c) (e : starOf A L ≃* Equiv.Perm (Fin 4)) :
    Nat.card (A ⊓ L : Subgroup G) = 3 ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  obtain ⟨v₁, hv₁, v₂, hv₂, h11, h22, h1, h2, hc, hne, ⟨g, hg, hgv⟩, ⟨g', hg', hg'v⟩⟩ :=
    exists_klein_perm_four e
  have ho₁ : orderOf v₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h11) h1
  have ho₂ : orderOf v₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h22) h2
  have hk₁ : Nat.card (commOf v₁) = Nat.card (commOf (v₁ * v₂)) := by
    rw [← hg'v, commOf_conj, Subgroup.card_map_of_injective g'.injective]
  have hk₂ : Nat.card (commOf v₂) = Nat.card (commOf (v₁ * v₂)) := by
    rw [← hk₁, ← hgv, commOf_conj, Subgroup.card_map_of_injective g.injective]
  set W : Subgroup A := L.comap A.subtype with hWdef
  have h9 := nine_lt_card_of_klein hAc hA3 ho₁ ho₂ hc hne hk₁ hk₂
    (commOf_le_comap_of_mem_starOf hAe hcA hLc hv₁ h11)
    (commOf_le_comap_of_mem_starOf hAe hcA hLc hv₂ h22) (W := W)
  have hWA : Nat.card W ∣ 3 ^ 4 := h81 ▸ Subgroup.card_subgroup_dvd_card W
  obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hWA
  have hW81 : Nat.card W ≠ 3 ^ 4 := by
    intro h
    have htop : W = ⊤ := Subgroup.eq_top_of_card_eq W (by rw [h, h81])
    exact hcL (show (⟨c, hcA⟩ : A) ∈ W from htop ▸ Subgroup.mem_top _)
  have hW27 : Nat.card W = 3 ^ 3 := by
    rw [hWi] at h9 hW81 ⊢
    interval_cases i <;> simp_all
  have hmap : W.map A.subtype = A ⊓ L := by
    rw [hWdef, ← Subgroup.subgroupOf, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← hmap, Subgroup.card_map_of_injective A.subtype_injective, hW27]

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
