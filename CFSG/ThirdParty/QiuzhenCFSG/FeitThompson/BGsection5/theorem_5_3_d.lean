module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.3(d) from BG Section 5 -/

-- The original inner direct product conclusion is a consequence of the following statements.
public theorem CFSG.theorem_5_3_d
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R) (hR : 3 ≤ groupRank R)
    {S : Subgroup R} (hc : Nat.card S = p) (hS : groupRank (Subgroup.centralizer (S : Set R)) ≤ 2) :
    IsCyclic (subgroupCentralizerIn (CΩ₁Z₂ p R) S) ∧ S ⊓ derivedSubgroup R = ⊥ ∧
      S ⊓ (CΩ₁Z₂ p R) = ⊥ ∧ Subgroup.centralizer S = S ⊔ subgroupCentralizerIn (CΩ₁Z₂ p R) S := by
  classical
  let Z : Subgroup R := Ω₁Z p R
  let T : Subgroup R := CΩ₁Z₂ p R
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hpR : IsPGroup p R := hnarrow.1
  obtain ⟨hZcard, hWmem⟩ := theorem_5_3_b (p := p) hpodd (R := R) hnarrow hR
  obtain ⟨hTchar, hTindex⟩ := theorem_5_3_c (p := p) hpodd (R := R) hnarrow hR
  letI : T.Characteristic := hTchar
  letI : T.Normal := by infer_instance
  letI : IsCyclic S := isCyclic_of_prime_card hc
  have hS_elem : IsElementaryAbelian p S := by
    exact isElementaryAbelian_of_prime_card_isCyclic (p := p) (G := S) hc
  letI : IsElementaryAbelian p S := hS_elem
  have hSZ_elem : IsElementaryAbelian p (Z ⊔ S : Subgroup R) := by
    have hZelem : IsElementaryAbelian p Z := by
      simpa [Z] using omega1Z_isElementaryAbelian (p := p) (R := R)
    letI : IsElementaryAbelian p Z := hZelem
    have hS_le_centZ : S ≤ Subgroup.centralizer (Z : Set R) := by
      exact (Subgroup.le_centralizer_iff).mp <|
        (omega1Z_le_center p R).trans (Subgroup.center_le_centralizer (S : Set R))
    exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := Z) (C := S) hS_le_centZ
  have hS_not_le_Z : ¬ S ≤ Z := by
    intro hSZ
    have hC_top : C = ⊤ := by
      apply (Subgroup.centralizer_eq_top_iff_subset).2
      intro s hs
      exact (omega1Z_le_center p R) (hSZ hs)
    have hcent_top : Subgroup.centralizer (S : Set R) = ⊤ := by
      simpa [C] using hC_top
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
  have hSZ_card : Nat.card (Z ⊔ S : Subgroup R) = p ^ 2 := by
    have hZ_normal : Z.Normal := omega1Z_normal p R
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
  have hS_le_C : S ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact setLike_mul_comm (s := S) ht hs
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
      obtain ⟨D, hDnorm, hD_le_B, hDcard⟩ :=
        lemma_1_22 (G := B) p (⊤ : Subgroup B) inferInstance k (by simpa using hk) 3 hk_ge_three
      have hC_rank_ge : 3 ≤ groupRank C := by
        let DmapR : Subgroup R := D.map B.subtype
        have hDmapR_le_C : DmapR ≤ C := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨d, hdD, rfl⟩
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
  have hSZ_not_le_T : ¬ Z ⊔ S ≤ T :=
    theorem_5_3_a (p := p) hpodd (R := R) hnarrow hR hSZ_mem hSZ_max
  have hZ_le_T : Z ≤ T := by
    exact (omega1Z_le_center p R).trans (Subgroup.center_le_centralizer (Ω₁Z₂ p R : Set R))
  have hS_not_le_T : ¬ S ≤ T := fun hST => hSZ_not_le_T <| sup_le hZ_le_T hST
  have hTS_bot : T.subgroupOf S = ⊥ := by
    haveI : Fact (Nat.card S).Prime := ⟨by simpa [hc] using (Fact.out : Nat.Prime p)⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (T.subgroupOf S) with hbot | htop
    · exact hbot
    · exact False.elim (hS_not_le_T ((Subgroup.subgroupOf_eq_top).1 htop))
  have hdisjST : Disjoint S T := by
    rw [Subgroup.disjoint_def]
    intro x hxS hxT
    have hxsub : (⟨x, hxS⟩ : S) ∈ T.subgroupOf S := hxT
    have hxbot : (⟨x, hxS⟩ : S) ∈ (⊥ : Subgroup S) := by simpa [hTS_bot] using hxsub
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxbot)
  have hquot_card : Nat.card (R ⧸ T) = p := by
    simpa [Subgroup.index_eq_card] using hTindex
  have hST_card : Nat.card S * Nat.card T = Nat.card R := by
    calc
      Nat.card S * Nat.card T = p * Nat.card T := by rw [hc]
      _ = Nat.card (R ⧸ T) * Nat.card T := by rw [hquot_card]
      _ = Nat.card R := (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := T)).symm
  have hSTcomp : S.IsComplement' T :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hST_card hdisjST
  have hR'_le_T : derivedSubgroup R ≤ T := by
    have hquot_comm : IsMulCommutative (R ⧸ T) := by
      letI : IsCyclic (R ⧸ T) := isCyclic_of_prime_card (α := R ⧸ T) hquot_card
      letI : CommGroup (R ⧸ T) := IsCyclic.commGroup
      infer_instance
    have hcomm_le : _root_.commutator R ≤ T :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := T)).1 hquot_comm
    change derivedSeries R 1 ≤ T
    rw [derivedSeries_one]
    exact hcomm_le
  have hsup_le : S ⊔ subgroupCentralizerIn T S ≤ C := by
    refine sup_le hS_le_C ?_
    exact inf_le_right
  have hC_le_sup : C ≤ S ⊔ subgroupCentralizerIn T S := by
    intro x hxC
    have hxST : x ∈ S ⊔ T := by simp [hSTcomp.sup_eq_top]
    rcases (Subgroup.mem_sup_of_normal_right (s := S) (t := T)).1 hxST with
      ⟨s, hsS, t, htT, hst⟩
    have hsC : s ∈ C := hS_le_C hsS
    have htC : t ∈ C := by
      have hs_inv_mul_x : s⁻¹ * x ∈ C := C.mul_mem (C.inv_mem hsC) hxC
      have ht_eq : t = s⁻¹ * x := by
        calc
          t = s⁻¹ * (s * t) := by simp
          _ = s⁻¹ * x := by rw [hst]
      rw [ht_eq]
      exact hs_inv_mul_x
    have hs_sup : s ∈ S ⊔ subgroupCentralizerIn T S := Subgroup.mem_sup_left hsS
    have ht_sup : t ∈ S ⊔ subgroupCentralizerIn T S := Subgroup.mem_sup_right ⟨htT, htC⟩
    have hmul_sup : s * t ∈ S ⊔ subgroupCentralizerIn T S :=
      (S ⊔ subgroupCentralizerIn T S).mul_mem hs_sup ht_sup
    simpa [hst] using hmul_sup
  have hcent_eq : C = S ⊔ subgroupCentralizerIn T S := le_antisymm hC_le_sup hsup_le
  have hR1_cyclic : IsCyclic (subgroupCentralizerIn T S) := by
    by_contra hR1_ncyc
    let R₁ : Subgroup R := subgroupCentralizerIn T S
    letI : Fact (IsPGroup p R₁) := ⟨hpR.to_subgroup R₁⟩
    obtain ⟨U, _hUnorm, hUcard, hUelem⟩ := lemma_4_5_a (R := R₁) (p := p) hpodd hR1_ncyc
    let Umap : Subgroup R := U.map R₁.subtype
    have hUmap_elem : IsElementaryAbelian p Umap := by
      letI : IsElementaryAbelian p U := hUelem
      simpa [Umap] using IsElementaryAbelian.map_subtype (p := p) (K := R₁) (H := U)
    have hUmap_card : Nat.card Umap = p ^ 2 := by
      calc
        Nat.card Umap = Nat.card U := by
          symm
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective (f := R₁.subtype) U R₁.subtype_injective).toEquiv
        _ = p ^ 2 := hUcard
    have hUmap_le_T : Umap ≤ T := by
      exact (Subgroup.map_subtype_le U).trans inf_le_left
    have hUmap_le_C : Umap ≤ C := by
      exact (Subgroup.map_subtype_le U).trans inf_le_right
    have hdisjSU : Disjoint S Umap := hdisjST.mono_right hUmap_le_T
    let D : Subgroup R := S ⊔ Umap
    have hDelem : IsElementaryAbelian p D := by
      letI : IsElementaryAbelian p Umap := hUmap_elem
      exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := S) (C := Umap) hUmap_le_C
    have hD_le_C : D ≤ C := sup_le hS_le_C hUmap_le_C
    have hDcard : Nat.card D = p ^ 3 := by
      letI : IsElementaryAbelian p D := hDelem
      letI : CommGroup D := IsMulCommutative.instCommGroup
      have hdisj_sub : Disjoint (S.subgroupOf D) (Umap.subgroupOf D) := by
        rw [Subgroup.disjoint_def]
        intro x hxS hxU
        apply Subtype.ext
        exact Subgroup.disjoint_def.mp hdisjSU hxS hxU
      have hsup_sub : S.subgroupOf D ⊔ Umap.subgroupOf D = ⊤ := by
        simpa [D] using
          (Subgroup.subgroupOf_sup (A := S) (A' := Umap) (B := D)
            le_sup_left le_sup_right).symm
      letI : (S.subgroupOf D).Normal := by infer_instance
      have hcompDU : (S.subgroupOf D).IsComplement' (Umap.subgroupOf D) :=
        isComplement'_of_disjoint_sup_eq_top_of_normal (S.subgroupOf D) (Umap.subgroupOf D)
          hdisj_sub hsup_sub
      have hmul := hcompDU.card_mul
      rw [natCard_subgroupOf_eq S D le_sup_left,
        natCard_subgroupOf_eq Umap D le_sup_right, hc, hUmap_card] at hmul
      simpa [pow_succ', Nat.mul_assoc] using hmul.symm
    let Dsub : Subgroup C := D.subgroupOf C
    have hDsub_card : Nat.card Dsub = p ^ 3 := by
      rw [natCard_subgroupOf_eq D C hD_le_C, hDcard]
    have hDsub_elem : IsElementaryAbelian p Dsub :=
      IsElementaryAbelian.subgroupOf (p := p) hD_le_C
    letI : IsElementaryAbelian p Dsub := hDsub_elem
    have hC_rank_ge : 3 ≤ groupRank C :=
      groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
        (p := p) (G := C) (B := Dsub) hDsub_card
    exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hC_rank_ge hS)
  refine ⟨hR1_cyclic, ?_, hdisjST.eq_bot, hcent_eq⟩
  exact (hdisjST.mono_right hR'_le_T).eq_bot
