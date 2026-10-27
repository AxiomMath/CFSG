module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_3_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 4.9 from BG Section 4 -/

universe u

section Main

open scoped FixedPoints IsMulCommutative
public theorem CFSG.lemma_4_9 {R : Type u} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hpgt : 3 < p)
    (hOmega : Nat.card (omega₁ (G := R) (p := p)) ≤ p ^ 2) :
    ∀ (T : Subgroup R) (_ : T.Normal),
      Nat.card (omega₁ (G := R ⧸ T) (p := p)) ≤ p ^ 2 := by
  intro T hTnorm
  classical
  have hpodd : p ≠ 2 := by omega
  have hP :
      ∀ n,
        ∀ (G : Type u) [Group G] [Finite G] [Fact (IsPGroup p G)],
          Nat.card G = n →
          Nat.card (omega₁ (G := G) (p := p)) ≤ p ^ 2 →
          ∀ (T : Subgroup G) (_ : T.Normal),
            Nat.card (omega₁ (G := G ⧸ T) (p := p)) ≤ p ^ 2 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G _ _ _ hcardG hOmegaG T hTnorm
    let Q : ℕ → Prop := fun t =>
      ∀ (U : Subgroup G) (_ : U.Normal), Nat.card U = t →
        Nat.card (omega₁ (G := G ⧸ U) (p := p)) ≤ p ^ 2
    have hQ : ∀ t, Q t := by
      intro t
      refine Nat.strong_induction_on t ?_
      intro t ihT U hUnorm hUcard
      by_cases hUbot : U = ⊥
      · let e : G ⧸ U ≃* G := (QuotientGroup.quotientMulEquivOfEq hUbot).trans QuotientGroup.quotientBot
        have hcard_eq :
            Nat.card (omega₁ (G := G ⧸ U) (p := p)) = Nat.card (omega₁ (G := G) (p := p)) := by
          simpa using (natCard_omega₁_eq_of_mulEquiv (p := p) e).symm
        rw [hcard_eq]
        exact hOmegaG
      let ΩU : Subgroup (G ⧸ U) := omega₁ (G := G ⧸ U) (p := p)
      by_cases hgood : Nat.card ΩU ≤ p ^ 2
      · simpa [ΩU] using hgood
      have hUnontriv : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).2 hUbot
      have hUp : IsPGroup p U := (Fact.out : IsPGroup p G).to_subgroup U
      obtain ⟨k, hk_pos, hUcard_pow⟩ :=
        (IsPGroup.nontrivial_iff_card (p := p) (G := U) hUp).mp hUnontriv
      have hk_one_or_two_le : k = 1 ∨ 2 ≤ k := by
        have hk_ge_one : 1 ≤ k := Nat.succ_le_of_lt hk_pos
        omega
      rcases hk_one_or_two_le with hk1 | hkge2
      · have hUcard_p : Nat.card U = p := by simpa [hk1] using hUcard_pow
        let q : G →* G ⧸ U := QuotientGroup.mk' U
        have hQp : IsPGroup p (G ⧸ U) := (Fact.out : IsPGroup p G).to_quotient U
        letI : Fact (IsPGroup p (G ⧸ U)) := ⟨hQp⟩
        have hB_exists :
            ∃ B : Subgroup (G ⧸ U),
              B ≤ ΩU ∧
                Nat.card B = p ^ 3 ∧
                  Nat.card (omega₁ (G := B) (p := p)) = p ^ 3 := by
          by_cases hqrank : 2 < groupRank (G ⧸ U)
          · obtain ⟨E, hEnorm, hEcard, hEelem⟩ :=
              exists_normal_elementaryAbelian_subgroup_order_p_sq_of_two_lt_groupRank
                (R := G ⧸ U) (p := p) hpodd hQp hqrank
            letI : E.Normal := hEnorm
            have hE_le_Ω : E ≤ ΩU := by
              intro e he
              change e ∈ Subgroup.closure {x : G ⧸ U | x ^ (p ^ 1) = 1}
              refine Subgroup.subset_closure ?_
              have he_powE : (⟨e, he⟩ : E) ^ p = 1 :=
                Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (IsElementaryAbelian.exponent_dvd_p p E) ⟨e, he⟩
              simpa [pow_one] using congrArg Subtype.val he_powE
            have hpow_not_subset :
                ¬ {x : G ⧸ U | x ^ (p ^ 1) = 1} ⊆ E := by
              intro hpow_sub
              have hΩU_le_E : ΩU ≤ E := by
                change omega₁ (G := G ⧸ U) (p := p) ≤ E
                rw [omega₁, omega]
                exact (Subgroup.closure_le (K := E)).2 hpow_sub
              have hE_lt_Ω : E < ΩU := by
                refine lt_of_le_of_ne hE_le_Ω ?_
                intro hEq
                have hcard_le : Nat.card ΩU ≤ p ^ 2 := by
                  simp [← hEq, hEcard]
                exact hgood hcard_le
              exact hE_lt_Ω.2 hΩU_le_E
            obtain ⟨y, hy_pow, hy_not_mem⟩ :
                ∃ y : G ⧸ U, y ^ p = 1 ∧ y ∉ E := by
              by_contra hcontra
              push Not at hcontra
              exact hpow_not_subset (by
                intro y hy
                exact hcontra y (by simpa [pow_one] using hy))
            let B : Subgroup (G ⧸ U) := E ⊔ Subgroup.zpowers y
            have hy_ΩU : y ∈ ΩU := by
              exact Subgroup.subset_closure (by simpa [pow_one] using hy_pow)
            have hB_le_ΩU : B ≤ ΩU := by
              refine sup_le hE_le_Ω ?_
              exact (Subgroup.zpowers_le).2 hy_ΩU
            let Esub : Subgroup B := E.subgroupOf B
            have hEsub_card : Nat.card Esub = p ^ 2 := by
              calc
                Nat.card Esub = Nat.card E :=
                  natCard_subgroupOf_eq E B le_sup_left
                _ = p ^ 2 := hEcard
            have hEsub_normal : Esub.Normal := by
              exact Subgroup.Normal.subgroupOf (G := G ⧸ U) (hH := hEnorm) B
            letI : Esub.Normal := hEsub_normal
            let yB : B := ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩
            have hyB_pow : yB ^ p = 1 := by
              apply Subtype.ext
              simpa [yB] using hy_pow
            have hEsub_sup : Esub ⊔ Subgroup.zpowers yB = ⊤ := by
              apply eq_top_iff.2
              intro z _hz
              rcases (Subgroup.mem_sup_of_normal_left
                (x := ((z : B) : G ⧸ U)) (s := E) (t := Subgroup.zpowers y)).1 z.2 with
                ⟨e, he, w, hw, hmul⟩
              rcases Subgroup.mem_zpowers_iff.mp hw with ⟨m, rfl⟩
              refine (Subgroup.mem_sup_of_normal_left
                (x := z) (s := Esub) (t := Subgroup.zpowers yB)).2 ?_
              refine ⟨⟨e, by exact Subgroup.mem_sup_left he⟩, ?_, yB ^ m, ?_, ?_⟩
              · simpa [Esub]
              · exact Subgroup.zpow_mem_zpowers yB m
              · apply Subtype.ext
                simpa [yB, mul_assoc] using hmul
            have hB_card_le : Nat.card B ≤ p ^ 3 := by
              calc
                Nat.card B ≤ p * Nat.card Esub :=
                  natCard_le_prime_mul_of_eq_sup_zpowers
                    (G := B) (p := p) Esub yB hyB_pow hEsub_sup
                _ = p * p ^ 2 := by rw [hEsub_card]
                _ = p ^ 3 := by ring_nf
            have hEsub_lt_top : Esub < ⊤ := by
              refine lt_of_le_of_ne le_top ?_
              intro hEq
              have hyEsub : yB ∈ Esub := by simp [hEq]
              exact hy_not_mem (by
                change (yB : G ⧸ U) ∈ E
                exact (Subgroup.mem_subgroupOf).1 hyEsub)
            have hB_card_gt : p ^ 2 < Nat.card B := by
              have hlt : Nat.card Esub < Nat.card B := by
                simpa using natCard_lt_of_subgroup_lt (H := Esub) (K := (⊤ : Subgroup B)) hEsub_lt_top
              simpa [hEsub_card] using hlt
            have hBp : IsPGroup p B := hQp.to_subgroup B
            obtain ⟨m, hm⟩ := hBp.exists_card_eq
            have hm_ge_three : 3 ≤ m := by
              rw [hm] at hB_card_gt
              have hm_gt_two :
                  2 < m := (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hB_card_gt
              omega
            have hm_le_three : m ≤ 3 := by
              rw [hm] at hB_card_le
              exact (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hB_card_le
            have hm_three : m = 3 := by omega
            have hBcard : Nat.card B = p ^ 3 := by simpa [hm_three] using hm
            have hEsub_le_omega : Esub ≤ omega₁ (G := B) (p := p) := by
              intro e he
              change (e : B) ∈ Subgroup.closure {x : B | x ^ (p ^ 1) = 1}
              refine Subgroup.subset_closure ?_
              have heE : (((e : B) : G ⧸ U) ∈ E) :=
                (Subgroup.mem_subgroupOf).1 he
              have he_powE : (⟨((e : B) : G ⧸ U), heE⟩ : E) ^ p = 1 :=
                Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (IsElementaryAbelian.exponent_dvd_p p E) ⟨((e : B) : G ⧸ U), heE⟩
              have he_powB : (e : B) ^ p = 1 := by
                apply Subtype.ext
                simpa using congrArg Subtype.val he_powE
              simpa [pow_one] using he_powB
            have hyB_mem_omega : yB ∈ omega₁ (G := B) (p := p) := by
              change yB ∈ Subgroup.closure {x : B | x ^ (p ^ 1) = 1}
              refine Subgroup.subset_closure ?_
              simpa [pow_one] using hyB_pow
            have hΩB_top : omega₁ (G := B) (p := p) = ⊤ := by
              apply eq_top_iff.2
              intro z _hz
              have hz_sup : z ∈ Esub ⊔ Subgroup.zpowers yB := by simp [hEsub_sup]
              exact (sup_le hEsub_le_omega ((Subgroup.zpowers_le).2 hyB_mem_omega)) hz_sup
            have hΩB_card : Nat.card (omega₁ (G := B) (p := p)) = p ^ 3 := by
              calc
                Nat.card (omega₁ (G := B) (p := p)) = Nat.card (⊤ : Subgroup B) := by
                  rw [hΩB_top]
                _ = Nat.card B := Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv
                _ = p ^ 3 := hBcard
            exact ⟨B, hB_le_ΩU, hBcard, hΩB_card⟩
          · have hqrank_le : groupRank (G ⧸ U) ≤ 2 := le_of_not_gt hqrank
            have hΩU_exp : Monoid.exponent ↥ΩU = p := by
              rcases proposition_4_8_b (R := G ⧸ U) (p := p) hpgt hqrank_le with h1 | hp
              · haveI : Subsingleton ΩU := (Monoid.exp_eq_one_iff (G := ΩU)).mp h1
                have hΩU_eq_bot : ΩU = ⊥ := by
                  rw [Subgroup.eq_bot_iff_forall]
                  intro z hz
                  have hz' : (⟨z, hz⟩ : ΩU) = 1 := Subsingleton.elim _ _
                  simpa using congrArg Subtype.val hz'
                have hΩU_card : Nat.card ΩU = 1 := by simp [hΩU_eq_bot]
                have hcard_le : Nat.card ΩU ≤ p ^ 2 := by
                  rw [hΩU_card]
                  exact Nat.succ_le_of_lt (pow_pos (Fact.out : Nat.Prime p).pos 2)
                exact False.elim (hgood hcard_le)
              · exact hp
            have hΩU_rank : groupRank ΩU ≤ 2 :=
              (groupRank_le_of_subgroup (R := G ⧸ U) (S := ΩU)).trans hqrank_le
            letI : Fact (IsPGroup p ΩU) := ⟨hQp.to_subgroup ΩU⟩
            have hΩU_card_le : Nat.card ΩU ≤ p ^ 3 :=
              proposition_4_8_a (R := ΩU) (p := p) hΩU_rank hΩU_exp
            have hΩUp : IsPGroup p ΩU := hQp.to_subgroup ΩU
            have hΩU_char : ΩU.Characteristic := by
              simpa [ΩU] using omega₁_characteristic (G := G ⧸ U) (p := p)
            letI : ΩU.Normal := by infer_instance
            obtain ⟨m, hm⟩ := hΩUp.exists_card_eq
            have hm_ge_three : 3 ≤ m := by
              rw [hm] at hgood
              have hm_gt_two :
                  2 < m := (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1
                    (lt_of_not_ge hgood)
              omega
            obtain ⟨B, hBnorm, hB_le, hBcard⟩ :=
              lemma_1_22 (G := G ⧸ U) p ΩU inferInstance m hm 3 hm_ge_three
            letI : B.Normal := hBnorm
            have hΩB_top : omega₁ (G := B) (p := p) = ⊤ := by
              apply omega₁_eq_top_of_forall_pow_eq_one
              intro x
              let xΩ : ΩU := ⟨x, hB_le x.2⟩
              have hxpowΩ : xΩ ^ p = 1 := by
                exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (show Monoid.exponent ↥ΩU ∣ p by simp [hΩU_exp]) xΩ
              apply Subtype.ext
              simpa [xΩ] using congrArg Subtype.val hxpowΩ
            have hΩB_card : Nat.card (omega₁ (G := B) (p := p)) = p ^ 3 := by
              calc
                Nat.card (omega₁ (G := B) (p := p)) = Nat.card (⊤ : Subgroup B) := by
                  rw [hΩB_top]
                _ = Nat.card B := Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv
                _ = p ^ 3 := hBcard
            exact ⟨B, hB_le, hBcard, hΩB_card⟩
        obtain ⟨B, hB_le_ΩU, hBcard, hΩB_card⟩ := hB_exists
        let H : Subgroup G := B.comap q
        have hH_card_le : Nat.card (omega₁ (G := H) (p := p)) ≤ p ^ 2 := by
          exact (natCard_omega₁_subgroup_le_global (G := G) (p := p) H).trans hOmegaG
        have hU_le_H : U ≤ H := by
          simpa [H, q, QuotientGroup.ker_mk'] using (Subgroup.ker_le_comap (f := q) (H := B))
        let Usub : Subgroup H := U.subgroupOf H
        have hUsub_normal : Usub.Normal := by
          exact Subgroup.Normal.subgroupOf (G := G) (hH := hUnorm) H
        letI : Usub.Normal := hUsub_normal
        by_cases hH_top : H = ⊤
        · have hB_top : B = ⊤ := by
            calc
              B = H.map q := by
                    simpa [H] using
                      (Subgroup.map_comap_eq_self_of_surjective (f := q)
                        (h := QuotientGroup.mk'_surjective U) B).symm
              _ = (⊤ : Subgroup G).map q := by rw [hH_top]
              _ = q.range := by rw [MonoidHom.range_eq_map]
              _ = ⊤ := MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective U)
          have hQcard : Nat.card (G ⧸ U) = p ^ 3 := by
            calc
              Nat.card (G ⧸ U) = Nat.card (⊤ : Subgroup (G ⧸ U)) := by
                exact (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ U)) ≃* (G ⧸ U)).toEquiv).symm
              _ = Nat.card B := by rw [hB_top]
              _ = p ^ 3 := hBcard
          have hΩU_top : ΩU = ⊤ := by
            refine le_antisymm le_top ?_
            rw [← hB_top]
            exact hB_le_ΩU
          have hQ_class2 : NilpotencyClassLe 2 (G ⧸ U) :=
            nilpotencyClassLe_of_card_le_p_cubed (R := G ⧸ U) (p := p) (by simp [hQcard])
          have hΩU_exp_one_or_p :
              Monoid.exponent ↥ΩU = 1 ∨ Monoid.exponent ↥ΩU = p :=
            proposition_4_3_a (R := G ⧸ U) (p := p) hpodd (Or.inl hQ_class2)
          have hQ_nontriv : Nontrivial (G ⧸ U) := by
            have hQ_card_gt : 1 < Nat.card (G ⧸ U) := by
              rw [hQcard]
              exact one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt (by decide)
            exact Finite.one_lt_card_iff_nontrivial.mp hQ_card_gt
          let eΩ : ΩU ≃* (G ⧸ U) :=
            (MulEquiv.subgroupCongr hΩU_top).trans (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ U)) ≃* (G ⧸ U))
          have hQ_exp : Monoid.exponent (G ⧸ U) = p := by
            rcases hΩU_exp_one_or_p with h1 | hp
            · have hQ_exp_one : Monoid.exponent (G ⧸ U) = 1 := by
                calc
                  Monoid.exponent (G ⧸ U) = Monoid.exponent ↥ΩU :=
                    (Monoid.exponent_eq_of_mulEquiv eΩ).symm
                  _ = 1 := h1
              haveI : Subsingleton (G ⧸ U) := (Monoid.exp_eq_one_iff (G := G ⧸ U)).mp hQ_exp_one
              exact (False.elim <| (not_nontrivial_iff_subsingleton.mpr ‹Subsingleton (G ⧸ U)›) hQ_nontriv)
            · calc
                Monoid.exponent (G ⧸ U) = Monoid.exponent ↥ΩU :=
                  (Monoid.exponent_eq_of_mulEquiv eΩ).symm
                _ = p := hp
          have hGcard_p4 : Nat.card G = p ^ 4 := by
            calc
              Nat.card G = Nat.card (G ⧸ U) * Nat.card U := by
                simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := U))
              _ = p ^ 3 * p := by rw [hQcard, hUcard_p]
              _ = p ^ 4 := by ring_nf
          have hQ_not_cyclic : ¬ IsCyclic (G ⧸ U) := by
            intro hQcyc
            have hQ_exp_card : Monoid.exponent (G ⧸ U) = Nat.card (G ⧸ U) := by
              simpa using hQcyc.exponent_eq_card
            have hp_lt_p3 : p < p ^ 3 := by
              simpa using (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).2 (by decide : 1 < 3)
            have hp_ne_p3 : p ≠ p ^ 3 := ne_of_lt hp_lt_p3
            have hQ_exp_card' : Monoid.exponent (G ⧸ U) = p ^ 3 := hQ_exp_card.trans hQcard
            exact hp_ne_p3 (hQ_exp.symm.trans hQ_exp_card')
          have hG_not_cyclic : ¬ IsCyclic G := by
            intro hGcyc
            exact hQ_not_cyclic (isCyclic_of_surjective q (QuotientGroup.mk'_surjective U))
          obtain ⟨A, hAnorm, hAcard, hAelem⟩ :=
            lemma_4_5_a (R := G) (p := p) hpodd hG_not_cyclic
          let ΩG : Subgroup G := omega₁ (G := G) (p := p)
          have hA_le_ΩG : A ≤ ΩG := by
            intro a ha
            change a ∈ Subgroup.closure {x : G | x ^ (p ^ 1) = 1}
            refine Subgroup.subset_closure ?_
            simpa [pow_one] using elemPow_eq_one_of_isElementaryAbelian a ha
          have hΩG_card : Nat.card ΩG = p ^ 2 := by
            have hp_sq_le : p ^ 2 ≤ Nat.card ΩG := by
              simpa [hAcard] using Subgroup.card_le_of_le hA_le_ΩG
            exact Nat.le_antisymm hOmegaG hp_sq_le
          have hΩG_quot_card : Nat.card (G ⧸ ΩG) = p ^ 2 := by
            have hmul :
                Nat.card (G ⧸ ΩG) * p ^ 2 = p ^ 2 * p ^ 2 := by
              calc
                Nat.card (G ⧸ ΩG) * p ^ 2
                    = Nat.card (G ⧸ ΩG) * Nat.card ΩG := by rw [hΩG_card]
                _ = Nat.card G := by
                      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := ΩG)).symm
                _ = p ^ 4 := hGcard_p4
                _ = p ^ 2 * p ^ 2 := by ring_nf
            have hmul' : p ^ 2 * Nat.card (G ⧸ ΩG) = p ^ 2 * p ^ 2 := by
              simpa [Nat.mul_comm] using hmul
            exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : Nat.Prime p).pos 2) hmul'
          have hΩGp : IsPGroup p ΩG := (Fact.out : IsPGroup p G).to_subgroup ΩG
          have hΩG_char : ΩG.Characteristic := by
            simpa [ΩG] using omega₁_characteristic (G := G) (p := p)
          letI : ΩG.Normal := by infer_instance
          have hΩG_comm : IsMulCommutative ΩG := by
            exact IsPGroup.isMulCommutative_of_card_eq_prime_sq
              (p := p) (G := ΩG) hΩG_card
          have hΩG_pow : ∀ x : ΩG, x ^ p = 1 := by
            letI : IsMulCommutative ΩG := hΩG_comm
            intro x
            apply Subtype.ext
            refine
              Subgroup.closure_induction (k := {z : G | z ^ (p ^ 1) = 1})
                (p := fun z hz => z ^ p = 1) (x := x.1) ?_ ?_ ?_ ?_ x.2
            · intro z hz
              simpa [pow_one] using hz
            · simp
            · intro y z hyΩ hzΩ hy hz
              let yΩ : ΩG := ⟨y, hyΩ⟩
              let zΩ : ΩG := ⟨z, hzΩ⟩
              have hmulΩ : (yΩ * zΩ : ΩG) ^ p = yΩ ^ p * zΩ ^ p := by
                simpa [yΩ, zΩ] using mul_pow yΩ zΩ p
              have hmul : (y * z) ^ p = y ^ p * z ^ p := by
                exact congrArg Subtype.val hmulΩ
              calc
                (y * z) ^ p = y ^ p * z ^ p := hmul
                _ = 1 := by simp [hy, hz]
            · intro y _ hy
              simpa [inv_pow] using congrArg Inv.inv hy
          have hquot_comm : IsMulCommutative (G ⧸ ΩG) :=
            IsPGroup.isMulCommutative_of_card_eq_prime_sq
              (p := p) (G := G ⧸ ΩG) hΩG_quot_card
          have hder_le_ΩG : derivedSubgroup G ≤ ΩG := by
            simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def] using
              (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := ΩG)).1 hquot_comm
          have hclass3 : NilpotencyClassLe 3 G :=
            nilpotencyClassLe_of_card_le_p_four (R := G) (p := p) (by simp [hGcard_p4])
          obtain ⟨φ, hφ⟩ :=
            proposition_4_3_b (R := G) (p := p) hpodd (Or.inr ⟨hpgt, hclass3⟩) hder_le_ΩG
          have hpow_mem_U : ∀ x : G, x ^ p ∈ U := by
            intro x
            apply (QuotientGroup.eq_one_iff (N := U) (x := x ^ p)).1
            have hxpow : (q x) ^ p = 1 := by
              exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                (show Monoid.exponent (G ⧸ U) ∣ p by simp [hQ_exp]) (q x)
            simpa [q] using hxpow
          have hφ_range_le_U : φ.range ≤ U := by
            intro x hx
            rcases hx with ⟨g, rfl⟩
            rw [hφ]
            exact hpow_mem_U g
          have hφ_range_card_le : Nat.card φ.range ≤ p := by
            calc
              Nat.card φ.range ≤ Nat.card U := Subgroup.card_le_of_le hφ_range_le_U
              _ = p := hUcard_p
          have hφ_ker_eq_ΩG : φ.ker = ΩG := by
            apply le_antisymm
            · intro x hx
              rw [MonoidHom.mem_ker] at hx
              change x ∈ omega₁ (G := G) (p := p)
              rw [omega₁, omega]
              refine Subgroup.subset_closure ?_
              have hxpow : x ^ p = 1 := by simpa [hφ x] using hx
              simpa [pow_one] using hxpow
            · intro x hx
              rw [MonoidHom.mem_ker]
              simpa [hφ x] using congrArg Subtype.val (hΩG_pow ⟨x, hx⟩)
          have hφ_quot_card : Nat.card (G ⧸ φ.ker) = Nat.card φ.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
          have hp_sq_le_p : p ^ 2 ≤ p := by
            calc
              p ^ 2 = Nat.card (G ⧸ ΩG) := hΩG_quot_card.symm
              _ = Nat.card (G ⧸ φ.ker) := by rw [hφ_ker_eq_ΩG]
              _ = Nat.card φ.range := hφ_quot_card
              _ ≤ p := hφ_range_card_le
          have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
          exact False.elim ((not_le_of_gt hp_lt_sq) hp_sq_le_p)
        · have hH_lt : H < ⊤ := lt_of_le_of_ne le_top hH_top
          have hH_card_lt : Nat.card H < n := by
            simpa [hcardG] using natCard_lt_of_subgroup_lt (H := H) (K := (⊤ : Subgroup G)) hH_lt
          letI : Fact (IsPGroup p H) := ⟨(Fact.out : IsPGroup p G).to_subgroup H⟩
          have hind :
              Nat.card (omega₁ (G := H ⧸ Usub) (p := p)) ≤ p ^ 2 :=
            ih (Nat.card H) hH_card_lt H rfl hH_card_le Usub hUsub_normal
          let qH : H →* H.map q := q.subgroupMap H
          have hqH_surj : Function.Surjective qH := MonoidHom.subgroupMap_surjective q H
          have hqH_range_top : qH.range = ⊤ := by
            rw [MonoidHom.range_eq_top]
            exact hqH_surj
          have hqH_ker : qH.ker = Usub := by
            simpa [qH, Usub, q, H] using (Subgroup.ker_subgroupMap (f := q) (H := H))
          have hHmap_eq : H.map q = B := by
            simpa [H] using
              (Subgroup.map_comap_eq_self_of_surjective (f := q)
                (h := QuotientGroup.mk'_surjective U) B)
          let e0 : H ⧸ qH.ker ≃* B :=
            ((QuotientGroup.quotientKerEquivRange qH).trans
              (MulEquiv.subgroupCongr hqH_range_top)).trans
              (Subgroup.topEquiv.trans (MulEquiv.subgroupCongr hHmap_eq))
          let e : H ⧸ Usub ≃* B :=
            (QuotientGroup.quotientMulEquivOfEq hqH_ker).symm.trans e0
          have hωB_le : Nat.card (omega₁ (G := B) (p := p)) ≤ p ^ 2 := by
            calc
              Nat.card (omega₁ (G := B) (p := p))
                  = Nat.card (omega₁ (G := H ⧸ Usub) (p := p)) := by
                      simpa using (natCard_omega₁_eq_of_mulEquiv (p := p) e)
              _ ≤ p ^ 2 := hind
          have hp_sq_lt_cube : p ^ 2 < p ^ 3 := by
            exact (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).2 (by decide : 2 < 3)
          have hp_cube_le_sq : p ^ 3 ≤ p ^ 2 := by
            rw [← hΩB_card]
            exact hωB_le
          exact False.elim ((not_le_of_gt hp_sq_lt_cube) hp_cube_le_sq)
      · obtain ⟨Z, hZnorm, hZ_le_U, hZcard⟩ :=
          lemma_1_22 (G := G) p U hUnorm k hUcard_pow 1 (Nat.succ_le_of_lt hk_pos)
        have hZ_card_lt : Nat.card Z < Nat.card U := by
          rw [hZcard, hUcard_pow]
          exact (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).2 hkge2
        have hZ_card_lt_t : Nat.card Z < t := by simpa [hUcard] using hZ_card_lt
        have hOmegaGZ :
            Nat.card (omega₁ (G := G ⧸ Z) (p := p)) ≤ p ^ 2 :=
          ihT (Nat.card Z) hZ_card_lt_t Z hZnorm rfl
        let q : G →* G ⧸ Z := QuotientGroup.mk' Z
        let Ubar : Subgroup (G ⧸ Z) := U.map q
        have hUbar_normal : Ubar.Normal := by infer_instance
        letI : Ubar.Normal := hUbar_normal
        letI : Fact (IsPGroup p (G ⧸ Z)) := ⟨(Fact.out : IsPGroup p G).to_quotient Z⟩
        have hZ_ne_bot : Z ≠ ⊥ := by
          intro hZbot
          have hcard_one : Nat.card Z = 1 := (Subgroup.eq_bot_iff_card (H := Z)).1 hZbot
          have : p = 1 := by simpa [hZcard] using hcard_one
          exact (Fact.out : Nat.Prime p).ne_one this
        have hGquotZ_lt : Nat.card (G ⧸ Z) < n := by
          simpa [hcardG] using natCard_quotient_lt_natCard_of_ne_bot Z hZ_ne_bot
        have hind :
            Nat.card (omega₁ (G := (G ⧸ Z) ⧸ Ubar) (p := p)) ≤ p ^ 2 :=
          ih (Nat.card (G ⧸ Z)) hGquotZ_lt (G ⧸ Z) rfl hOmegaGZ Ubar hUbar_normal
        let e : (G ⧸ Z) ⧸ Ubar ≃* G ⧸ U :=
          QuotientGroup.quotientQuotientEquivQuotient (N := Z) (M := U) hZ_le_U
        have hcard_eq :
            Nat.card (omega₁ (G := G ⧸ U) (p := p)) =
              Nat.card (omega₁ (G := (G ⧸ Z) ⧸ Ubar) (p := p)) := by
          simpa using (natCard_omega₁_eq_of_mulEquiv (p := p) e)
        exact False.elim (hgood (by rw [hcard_eq]; exact hind))
    exact hQ (Nat.card T) T hTnorm rfl
  simpa using (hP (Nat.card R) R rfl hOmega T hTnorm)

end Main
