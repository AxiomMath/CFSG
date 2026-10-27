module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3_d

namespace CFSG
end CFSG
open CFSG

/-! # Corollary 5.4 from BG Section 5 -/

private theorem CFSG.rank_two_maximal_of_order_p_centralizer_rank_le_two
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] [Finite R]
    (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {S : Subgroup R} (hc : Nat.card S = p)
    (hS : groupRank (Subgroup.centralizer (S : Set R)) ≤ 2) :
    (Ω₁Z p R ⊔ S : Subgroup R) ∈ elementaryAbelianSubgroupsOfRank p 2 R ∧
      (Ω₁Z p R ⊔ S : Subgroup R) ∈ maximalElementaryAbelianSubgroups p R := by
  classical
  let Z : Subgroup R := Ω₁Z p R
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  letI : IsCyclic S := isCyclic_of_prime_card hc
  have hS_elem : IsElementaryAbelian p S := by
    exact isElementaryAbelian_of_prime_card_isCyclic (p := p) (G := S) hc
  letI : IsElementaryAbelian p S := hS_elem
  have hZelem : IsElementaryAbelian p Z := by
    simpa [Z] using omega1Z_isElementaryAbelian (p := p) (R := R)
  letI : IsElementaryAbelian p Z := hZelem
  have hZ_le_C : Z ≤ C := by
    exact (omega1Z_le_center p R).trans (Subgroup.center_le_centralizer (S : Set R))
  have hS_le_C : S ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact setLike_mul_comm (s := S) ht hs
  have hSZ_elem : IsElementaryAbelian p (Z ⊔ S : Subgroup R) := by
    have hS_le_centZ : S ≤ Subgroup.centralizer (Z : Set R) := by
      exact (Subgroup.le_centralizer_iff).mp hZ_le_C
    exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := Z) (C := S) hS_le_centZ
  have hS_not_le_Z : ¬ S ≤ Z := by
    intro hSZ
    have hC_top : C = ⊤ := by
      apply (Subgroup.centralizer_eq_top_iff_subset).2
      intro s hs
      exact (omega1Z_le_center p R) (hSZ hs)
    have hRank_le_two : groupRank R ≤ 2 := by
      have hC_rank_le : groupRank C ≤ 2 := by
        simpa [C] using hS
      have htop : groupRank (⊤ : Subgroup R) ≤ 2 := by
        rw [hC_top] at hC_rank_le
        exact hC_rank_le
      simpa [groupRank_top_subgroup_eq R] using htop
    exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hR hRank_le_two)
  have hdisjSZ : Disjoint Z S := by
    rw [Subgroup.disjoint_def]
    intro x hxZ hxS
    by_contra hx_ne_one
    have hZsub_ne_bot : (Z.subgroupOf S) ≠ ⊥ := by
      intro hbot
      have hxsub : (⟨x, hxS⟩ : S) ∈ Z.subgroupOf S := hxZ
      have hxbot : (⟨x, hxS⟩ : S) ∈ (⊥ : Subgroup S) := by simpa [hbot] using hxsub
      exact hx_ne_one <| by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
    haveI : Fact (Nat.card S).Prime := ⟨by simpa [hc] using (Fact.out : Nat.Prime p)⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Z.subgroupOf S) with hbot | htop
    · exact False.elim (hZsub_ne_bot hbot)
    · exact hS_not_le_Z ((Subgroup.subgroupOf_eq_top).1 htop)
  have hZ_ne_bot : Z ≠ ⊥ := by
    have hR_nontrivial : Nontrivial R := by
      refine not_subsingleton_iff_nontrivial.mp ?_
      intro hsub
      letI : Subsingleton R := hsub
      have hcyc : IsCyclic R := inferInstance
      have hRank_le_one : groupRank R ≤ 1 := groupRank_le_one_of_isCyclic R
      exact (by decide : ¬ 3 ≤ (1 : ℕ)) (le_trans hR hRank_le_one)
    letI : Nontrivial R := hR_nontrivial
    have hZ_nontrivial : Nontrivial (Subgroup.center R) := hpR.center_nontrivial
    have hcenter_p : IsPGroup p (Subgroup.center R) := hpR.to_subgroup (Subgroup.center R)
    have hpdvd_center : p ∣ Nat.card (Subgroup.center R) := by
      rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Subgroup.center R)
          (hG := hcenter_p)).1 hZ_nontrivial with
        ⟨n, hn, hcard⟩
      rw [hcard]
      exact dvd_pow_self p (Nat.ne_of_gt hn)
    simpa [Z, Ω₁Z] using omega₁_map_subtype_ne_bot (M := Subgroup.center R)
      (p := p) hpdvd_center
  have hZcard : Nat.card Z = p := by
    have hZp : IsPGroup p Z := IsElementaryAbelian.isPGroup p Z
    rcases hZp.exists_card_eq with ⟨k, hk⟩
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      apply hZ_ne_bot
      apply (Subgroup.card_eq_one (H := Z)).1
      simpa [hk0] using hk
    have hk_lt_three : k < 3 := by
      by_contra hnot
      have hk3 : 3 ≤ k := by omega
      let Zsub : Subgroup C := Z.subgroupOf C
      have hZsub_card : Nat.card Zsub = p ^ k := by
        rw [natCard_subgroupOf_eq Z C hZ_le_C, hk]
      have hZsub_elem : IsElementaryAbelian p Zsub :=
        IsElementaryAbelian.subgroupOf (p := p) hZ_le_C
      letI : IsElementaryAbelian p Zsub := hZsub_elem
      letI : Fact (IsPGroup p Zsub) := ⟨IsElementaryAbelian.isPGroup p Zsub⟩
      obtain ⟨D, _hDnorm, hD_le_top, hDcard⟩ :=
        lemma_1_22 (G := Zsub) p (⊤ : Subgroup Zsub) inferInstance k
          (by simpa using hZsub_card) 3 hk3
      have hC_rank_ge : 3 ≤ groupRank C := by
        let DmapC : Subgroup C := D.map Zsub.subtype
        have hDmapC_card : Nat.card DmapC = p ^ 3 := by
          calc
            Nat.card DmapC = Nat.card D := by
              symm
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective (f := Zsub.subtype) D
                  Zsub.subtype_injective).toEquiv
            _ = p ^ 3 := hDcard
        have hDmapC_elem : IsElementaryAbelian p DmapC := by
          have hD_elem : IsElementaryAbelian p D := by
            have htop_elem : IsElementaryAbelian p (⊤ : Subgroup Zsub) := by
              exact isElementaryAbelian_top (p := p) (G := Zsub)
            letI : IsElementaryAbelian p (⊤ : Subgroup Zsub) := htop_elem
            exact isElementaryAbelian_of_le (p := p) hD_le_top
          letI : IsElementaryAbelian p D := hD_elem
          simpa [DmapC] using IsElementaryAbelian.map_subtype (p := p) (K := Zsub) (H := D)
        letI : IsElementaryAbelian p DmapC := hDmapC_elem
        exact groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
          (p := p) (G := C) (B := DmapC) hDmapC_card
      exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hC_rank_ge hS)
    have hk_ne_two : k ≠ 2 := by
      intro hk2
      have hZcard_eq : Nat.card Z = p ^ 2 := by simpa [hk2] using hk
      have hSZ_card_p3 : Nat.card (Z ⊔ S : Subgroup R) = p ^ 3 := by
        have hZ_normal : Z.Normal := by simpa [Z] using omega1Z_normal p R
        letI : Z.Normal := hZ_normal
        have hcomp :
            (Z.subgroupOf (Z ⊔ S)).IsComplement' (S.subgroupOf (Z ⊔ S)) := by
          exact isComplement'_of_disjoint_sup_eq_top_of_normal
            (Z.subgroupOf (Z ⊔ S)) (S.subgroupOf (Z ⊔ S))
            (by
              rw [Subgroup.disjoint_def]
              intro x hxZ hxS
              apply Subtype.ext
              exact Subgroup.disjoint_def.mp hdisjSZ hxZ hxS)
            (by
              simpa using
                (Subgroup.subgroupOf_sup (A := Z) (A' := S) (B := Z ⊔ S)
                  le_sup_left le_sup_right).symm)
        have hmul := hcomp.card_mul
        rw [natCard_subgroupOf_eq Z (Z ⊔ S) le_sup_left,
          natCard_subgroupOf_eq S (Z ⊔ S) le_sup_right, hZcard_eq, hc] at hmul
        simpa [pow_succ, pow_two, Nat.mul_assoc] using hmul.symm
      have hC_rank_ge : 3 ≤ groupRank C := by
        have hSZ_le_C : Z ⊔ S ≤ C := sup_le hZ_le_C hS_le_C
        let Dsub : Subgroup C := (Z ⊔ S : Subgroup R).subgroupOf C
        have hDsub_card : Nat.card Dsub = p ^ 3 := by
          rw [natCard_subgroupOf_eq (Z ⊔ S : Subgroup R) C hSZ_le_C, hSZ_card_p3]
        have hDsub_elem : IsElementaryAbelian p Dsub :=
          IsElementaryAbelian.subgroupOf (p := p) hSZ_le_C
        letI : IsElementaryAbelian p Dsub := hDsub_elem
        exact groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
          (p := p) (G := C) (B := Dsub) hDsub_card
      exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hC_rank_ge hS)
    have hk_one : k = 1 := by omega
    simpa [hk_one] using hk
  have hSZ_card : Nat.card (Z ⊔ S : Subgroup R) = p ^ 2 := by
    have hZ_normal : Z.Normal := by simpa [Z] using omega1Z_normal p R
    letI : Z.Normal := hZ_normal
    have hcomp :
        (Z.subgroupOf (Z ⊔ S)).IsComplement' (S.subgroupOf (Z ⊔ S)) := by
      exact isComplement'_of_disjoint_sup_eq_top_of_normal
        (Z.subgroupOf (Z ⊔ S)) (S.subgroupOf (Z ⊔ S))
        (by
          rw [Subgroup.disjoint_def]
          intro x hxZ hxS
          apply Subtype.ext
          exact Subgroup.disjoint_def.mp hdisjSZ hxZ hxS)
        (by
          simpa using
            (Subgroup.subgroupOf_sup (A := Z) (A' := S) (B := Z ⊔ S)
              le_sup_left le_sup_right).symm)
    have hmul := hcomp.card_mul
    rw [natCard_subgroupOf_eq Z (Z ⊔ S) le_sup_left,
      natCard_subgroupOf_eq S (Z ⊔ S) le_sup_right, hZcard, hc] at hmul
    simpa [pow_two] using hmul.symm
  have hSZ_mem : Z ⊔ S ∈ elementaryAbelianSubgroupsOfRank p 2 R := ⟨hSZ_card, hSZ_elem⟩
  have hSZ_max : Z ⊔ S ∈ maximalElementaryAbelianSubgroups p R := by
    refine ⟨hSZ_elem, ?_⟩
    intro B hSZ_le_B hBelem
    letI : IsElementaryAbelian p B := hBelem
    have hB_le_C : B ≤ C := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsB : s ∈ B := hSZ_le_B (Subgroup.mem_sup_right hs)
      exact setLike_mul_comm (s := B) hsB hb
    by_cases hB_eq : B = Z ⊔ S
    · exact hB_eq.symm
    · have hBSZ_ne : Z ⊔ S ≠ B := fun h => hB_eq h.symm
      have hBSZ_lt : Z ⊔ S < B := lt_of_le_of_ne hSZ_le_B hBSZ_ne
      have hcard_lt : Nat.card (Z ⊔ S : Subgroup R) < Nat.card B := by
        have hle_card : Nat.card (Z ⊔ S : Subgroup R) ≤ Nat.card B :=
          Subgroup.card_le_of_le hSZ_le_B
        exact lt_of_le_of_ne hle_card fun hcard_eq =>
          hBSZ_ne <| Subgroup.eq_of_le_of_card_ge hSZ_le_B (le_of_eq hcard_eq.symm)
      rcases hpR.to_subgroup B |>.exists_card_eq with ⟨k, hk⟩
      rw [hSZ_card, hk] at hcard_lt
      have hk_gt_two : 2 < k := by
        exact (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).1 hcard_lt
      have hk_ge_three : 3 ≤ k := by omega
      letI : Fact (IsPGroup p B) := ⟨hpR.to_subgroup B⟩
      obtain ⟨D, _hDnorm, hD_le_B, hDcard⟩ :=
        lemma_1_22 (G := B) p (⊤ : Subgroup B) inferInstance k (by simpa using hk)
          3 hk_ge_three
      have hC_rank_ge : 3 ≤ groupRank C := by
        let DmapR : Subgroup R := D.map B.subtype
        have hDmapR_le_C : DmapR ≤ C := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨d, _hdD, rfl⟩
          exact hB_le_C d.2
        let Dsub : Subgroup C := DmapR.subgroupOf C
        have hDsub_card : Nat.card Dsub = p ^ 3 := by
          rw [natCard_subgroupOf_eq DmapR C hDmapR_le_C]
          calc
            Nat.card DmapR = Nat.card D := by
              symm
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective (f := B.subtype) D B.subtype_injective).toEquiv
            _ = p ^ 3 := hDcard
        have hDsub_elem : IsElementaryAbelian p Dsub := by
          have hDelem : IsElementaryAbelian p D := by
            have hBtop_elem : IsElementaryAbelian p (⊤ : Subgroup B) := by
              exact isElementaryAbelian_top (p := p) (G := B)
            letI : IsElementaryAbelian p (⊤ : Subgroup B) := hBtop_elem
            exact isElementaryAbelian_of_le (p := p) hD_le_B
          letI : IsElementaryAbelian p D := hDelem
          have hDmapR_elem : IsElementaryAbelian p DmapR := by
            simpa [DmapR] using IsElementaryAbelian.map_subtype (p := p) (K := B) (H := D)
          letI : IsElementaryAbelian p DmapR := hDmapR_elem
          exact IsElementaryAbelian.subgroupOf (p := p) hDmapR_le_C
        letI : IsElementaryAbelian p Dsub := hDsub_elem
        exact groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
          (p := p) (G := C) (B := Dsub) hDsub_card
      exact False.elim ((by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hC_rank_ge hS))
  exact ⟨hSZ_mem, hSZ_max⟩

public theorem CFSG.corollary_5_4
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R) :
    IsNarrowPGroup p R ↔ ∃ S : Subgroup R, Nat.card S = p ∧
      groupRank (Subgroup.centralizer (S : Set R)) ≤ 2 := by
  classical
  constructor
  · intro hnarrow
    obtain ⟨E, hE, hEmax⟩ :=
      (theorem_5_3 (p := p) hpodd (R := R) hpR hR).mp hnarrow
    rcases hE with ⟨hEcard, hEelem⟩
    let T : Subgroup R := CΩ₁Z₂ p R
    obtain ⟨hZcard, _hWmem⟩ := lemma_5_2_b (p := p) hpodd (R := R) hpR hR
      ⟨hEcard, hEelem⟩ hEmax
    obtain ⟨hTchar, _hTindex⟩ := lemma_5_2_c (p := p) hpodd (R := R) hpR hR
      ⟨hEcard, hEelem⟩ hEmax
    letI : T.Characteristic := hTchar
    letI : T.Normal := by infer_instance
    have hZ_le_E : Ω₁Z p R ≤ E := omega1Z_le_of_rank_two_maximal hEelem hEmax
    have hZ_le_T : Ω₁Z p R ≤ T := by
      exact (omega1Z_le_center p R).trans
        (Subgroup.center_le_centralizer (Ω₁Z₂ p R : Set R))
    have hE_not_le_T : ¬ E ≤ T := lemma_5_2_a (p := p) hpodd (R := R) hpR hR
      ⟨hEcard, hEelem⟩ hEmax
    obtain ⟨S, _hS_le_E, hScard, _hdisjZS, _hS_not_le_T, hE_eq⟩ :=
      exists_order_p_subgroup_of_rank_two_maximal_not_le
        (p := p) (R := R) (E := E) (T := T) hEcard hZcard hZ_le_E hZ_le_T hE_not_le_T
    exact ⟨S, hScard,
      groupRank_centralizer_le_two_of_rank_two_maximal
        (p := p) hpodd (R := R) hpR ⟨hEcard, hEelem⟩ hEmax hE_eq⟩
  · rintro ⟨S, hScard, hCent_rank⟩
    have hEpack :=
      rank_two_maximal_of_order_p_centralizer_rank_le_two
        (p := p) (R := R) hpR hR hScard hCent_rank
    exact (theorem_5_3 (p := p) hpodd (R := R) hpR hR).mpr
      ⟨Ω₁Z p R ⊔ S, hEpack.1, hEpack.2⟩
