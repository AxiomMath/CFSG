module

public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13

open scoped Matrix

section Model

theorem s16c7_exists_seven_fix :
    ∃ Q : Subgroup (MulAut WMod), Q ≤ img ∧ Nat.card Q = 7 ∧ 8 ≤ Nat.card (fixV Q) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ : ∃ a : ↥SL32, mat a = s7m := ⟨slOfMat s7m det_s7m, mat_slOfMat _ _⟩
  obtain ⟨b, hb⟩ : ∃ b : ↥SL32, mat b = s7iᵀ :=
    ⟨slOfMat s7iᵀ (by decide), mat_slOfMat _ _⟩
  have hbT : (mat b)ᵀ = s7i := by rw [hb, Matrix.transpose_transpose]
  have ha7 : a ^ 7 = 1 := by
    apply eq_of_mat_eq
    rw [mat_pow, ha, mat_one]
    decide
  have hb7 : b ^ 7 = 1 := by
    apply eq_of_mat_eq
    rw [mat_pow, hb, mat_one]
    decide
  have hpair7 : (a, b) ^ 7 = 1 := by
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst]; exact ha7
    · rw [Prod.pow_snd]; exact hb7
  have ha1 : a ≠ 1 := fun h => by
    have h1 : mat a = 1 := by rw [h, mat_one]
    rw [ha] at h1
    exact (by decide : s7m ≠ (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
  have hpair1 : (a, b) ≠ 1 := fun h => ha1 (congrArg Prod.fst h)
  have hrho1 : rho (a, b) ≠ 1 := fun h => hpair1 ((map_eq_one_iff rho rho_injective).mp h)
  have hpow : rho (a, b) ^ 7 = 1 := by rw [← map_pow, hpair7, map_one]
  have horder : orderOf (rho (a, b)) = 7 := orderOf_eq_prime hpow hrho1
  refine ⟨Subgroup.zpowers (rho (a, b)), ?_, ?_, ?_⟩
  · exact Subgroup.zpowers_le.mpr (rho_mem_img _)
  · rw [Nat.card_zpowers, horder]
  · have hcard : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
        mat (a, b).1 * X * (mat (a, b).2)ᵀ = X).card = 8 := by
      rw [show mat (a, b).1 = s7m from ha, show (mat (a, b).2)ᵀ = s7i from hbT]
      decide +kernel
    exact le_of_le_of_eq hcard.ge (card_fixV_rho (a, b)).symm

private theorem s16c7_exists_conj_le_sylow_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p G) (E : Subgroup G) (hE : IsPGroup p E) :
    ∃ y : G, E.map (MulAut.conj y).toMonoidHom ≤ Q := by
  obtain ⟨T, hET⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T Q
  refine ⟨g, ?_⟩
  have hgT : (g • T : Sylow p G).toSubgroup = T.toSubgroup.map
      (MulAut.conj g).toMonoidHom := rfl
  rw [hg] at hgT
  rw [hgT]
  exact Subgroup.map_mono hET

theorem exists_sub_of_isPGroup_seven_norm {S : Subgroup (MulAut WMod)} (hS : S ≤ L3Wr.norm)
    (h7 : IsPGroup 7 S) :
    ∃ Q : Subgroup (MulAut WMod), Q ≤ S ∧ Nat.card S ≤ 7 * Nat.card Q ∧
      8 ≤ Nat.card (fixV Q) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (MulAut WMod) := MulEquiv.finite_left
  have hSdvd : Nat.card S ∣ 2 * 168 ^ 2 := by
    rw [← card_norm]
    exact Subgroup.card_dvd_of_le hS
  obtain ⟨k, hk⟩ := h7.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : 7 ^ 3 ∣ 2 * 168 ^ 2 :=
      (pow_dvd_pow 7 (by omega : 3 ≤ k)).trans (hk ▸ hSdvd)
    exact absurd h3 (by decide)
  by_cases hsmall : Nat.card S ≤ 7
  · refine ⟨⊥, bot_le, ?_, ?_⟩
    · rw [Subgroup.card_bot, mul_one]; exact hsmall
    · have htop : fixV (⊥ : Subgroup (MulAut WMod)) = ⊤ := by
        refine le_antisymm le_top fun v _ => ?_
        exact (mem_fixV (X := (⊥ : Subgroup (MulAut WMod)))).mpr
          (fun x hx => by rw [Subgroup.mem_bot.mp hx]; rfl)
      have hcard : Nat.card ↥(fixV (⊥ : Subgroup (MulAut WMod))) = 2 ^ 9 := by
        exact (congrArg (fun K : Subgroup WMod => Nat.card ↥K) htop).trans
          (Subgroup.card_top.trans card_WMod)
      exact le_of_le_of_eq (by norm_num : (8 : ℕ) ≤ 2 ^ 9) hcard.symm
  · have hk_ge2 : 2 ≤ k := by
      by_contra h
      have h01 : k = 0 ∨ k = 1 := by omega
      rcases h01 with rfl | rfl
      · rw [hk] at hsmall; norm_num at hsmall
      · rw [hk] at hsmall; norm_num at hsmall
    have hk_eq2 : k = 2 := by omega
    have hScard : Nat.card S = 49 := by rw [hk, hk_eq2]; norm_num
    have hS₁card : Nat.card ↥(S.subgroupOf L3Wr.norm) = 49 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv, hScard]
    have h7₁ : IsPGroup 7 ↥(S.subgroupOf L3Wr.norm) :=
      h7.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
    have hidx : ¬ 7 ∣ (S.subgroupOf L3Wr.norm).index := by
      have h1 := Subgroup.card_mul_index (S.subgroupOf L3Wr.norm)
      rw [hS₁card, card_norm] at h1
      norm_num at h1
      have h2 : (S.subgroupOf L3Wr.norm).index = 1152 := by omega
      rw [h2]; decide
    obtain ⟨Q₀, hQ₀img, hQ₀card, hQ₀fix⟩ := s16c7_exists_seven_fix
    have hQ₀norm : Q₀ ≤ L3Wr.norm := hQ₀img.trans img_le_norm
    have hEcard : Nat.card ↥(Q₀.subgroupOf L3Wr.norm) = 7 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀norm).toEquiv, hQ₀card]
    have hE : IsPGroup 7 ↥(Q₀.subgroupOf L3Wr.norm) :=
      IsPGroup.of_card (n := 1) (by rw [hEcard]; norm_num)
    let P : Sylow 7 ↥L3Wr.norm := h7₁.toSylow hidx
    obtain ⟨y, hy⟩ := s16c7_exists_conj_le_sylow_of_isPGroup P
      (Q₀.subgroupOf L3Wr.norm) hE
    set n : MulAut WMod := (y : MulAut WMod) with hn
    refine ⟨Q₀.map (MulAut.conj n).toMonoidHom, ?_, ?_, ?_⟩
    · rintro q ⟨q₀, hq₀, rfl⟩
      have hq₀n : q₀ ∈ L3Wr.norm := hQ₀norm hq₀
      have he : (⟨q₀, hq₀n⟩ : ↥L3Wr.norm) ∈ Q₀.subgroupOf L3Wr.norm := hq₀
      have hmemP : (MulAut.conj y ⟨q₀, hq₀n⟩ : ↥L3Wr.norm) ∈ P := hy ⟨_, he, rfl⟩
      have hmemS₁ : (MulAut.conj y ⟨q₀, hq₀n⟩ : ↥L3Wr.norm) ∈ S.subgroupOf L3Wr.norm :=
        hmemP
      have hmemS : ((MulAut.conj y ⟨q₀, hq₀n⟩ : ↥L3Wr.norm) : MulAut WMod) ∈ S :=
        Subgroup.mem_subgroupOf.mp hmemS₁
      convert hmemS using 1
      simp [MulAut.conj_apply, hn]
    · rw [hScard, Subgroup.card_map_of_injective (MulAut.conj n).injective, hQ₀card]
    · have hcard : Nat.card ↥(fixV (Q₀.map (MulAut.conj n).toMonoidHom)) =
          Nat.card ↥(fixV Q₀) :=
        (congrArg (fun K : Subgroup WMod => Nat.card ↥K) (fixV_map_conj_eq Q₀ n)).trans
          (Subgroup.card_map_of_injective n.injective)
      exact le_of_le_of_eq hQ₀fix hcard.symm

end Model

section Abstract

theorem exists_sub_of_isPGroup_seven {V : Type*} [CommGroup V] {H S : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H)
    (hS : S ≤ Subgroup.normalizer (H : Set (MulAut V))) (h7 : IsPGroup 7 S) :
    ∃ Q : Subgroup (MulAut V), Q ≤ S ∧ Nat.card S ≤ 7 * Nat.card Q ∧
      8 ≤ Nat.card (fixV Q) := by
  obtain ⟨e, he⟩ := exists_model hreal
  have h2 : S.map (congrHom e) ≤ L3Wr.norm := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut WMod)) :
          Set (MulAut WMod)) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := congrHom e) hS).trans (le_of_eq h3)
    have h5 := congrArg (fun K : Subgroup (MulAut WMod) => Subgroup.normalizer
      (K : Set (MulAut WMod))) he
    exact h4.trans (le_of_eq h5)
  have h7' : IsPGroup 7 ↥(S.map (congrHom e)) :=
    h7.of_equiv (S.equivMapOfInjective _ (congrHom_injective e))
  obtain ⟨Q', hQ'S, hcard, hfix⟩ := exists_sub_of_isPGroup_seven_norm h2 h7'
  obtain ⟨Q, hQS, rfl⟩ := exists_eq_map_congrHom e hQ'S
  have h6 : Nat.card ↥(S.map (congrHom e)) = Nat.card ↥S := card_map_congrHom e S
  have h7 : Nat.card ↥(Q.map (congrHom e)) = Nat.card ↥Q := card_map_congrHom e Q
  have h8 : fixV (Q.map (congrHom e)) = (fixV Q).map e.toMonoidHom := fixV_map_congrHom e Q
  have h9 : Nat.card ↥((fixV Q).map e.toMonoidHom) = Nat.card ↥(fixV Q) :=
    Subgroup.card_map_of_injective e.injective
  refine ⟨Q, hQS, ?_, ?_⟩
  · exact h6.symm.le.trans (hcard.trans (le_of_eq (congrArg (7 * ·) h7)))
  · rw [h8] at hfix
    exact le_of_le_of_eq hfix h9

end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
