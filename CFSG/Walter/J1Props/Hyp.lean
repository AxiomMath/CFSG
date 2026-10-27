module

public import CFSG.Walter.J1Props.Factor
public import CFSG.Walter.J1Props.Janko
public import CFSG.StronglyEmbedded.Catalog

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word

theorem index_zpowers_F {y : FJ} {q : ℕ} (hy : orderOf y = q) :
    Nat.card (Subgroup.zpowers y) = q ∧ (Subgroup.zpowers y).index * q = 60 := by
  have h := (Subgroup.zpowers y).card_mul_index
  rw [Nat.card_zpowers, hy, card_F] at h
  rw [Nat.card_zpowers, hy]
  exact ⟨rfl, by rw [mul_comm]; exact h⟩

theorem F_isSimpleGroup : IsSimpleGroup FJ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rels_F
  obtain ⟨n1, n2, n3, n4, n5, -⟩ := ne_one_F
  set a : FJ := ⟨xJ, mem_F.1⟩ with ha
  set b : FJ := ⟨x'J, mem_F.2.1⟩ with hb
  set c : FJ := ⟨uJ, mem_F.2.2⟩ with hc
  have : Nontrivial FJ := ⟨⟨a, 1, fun h => n1 (congrArg Subtype.val h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  right
  have hcardN : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN1
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (by omega : Nat.card N ≠ 1)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN
  have hgo : orderOf (g : FJ) = p := by rw [Subgroup.orderOf_coe]; exact hg
  have hp60 : p ∣ 4 * 15 := by
    have := hpN.trans (Subgroup.card_subgroup_dvd_card N)
    rwa [card_F] at this
  have hp235 : p = 2 ∨ p = 3 ∨ p = 5 := by
    rcases (Nat.Prime.dvd_mul hp).mp hp60 with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h))
    · rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 3 * 5 by norm_num; exact h) with h' | h'
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h'))
  have hgN : Subgroup.zpowers (g : FJ) ≤ N := Subgroup.zpowers_le.mpr g.2
  have hcb : orderOf (c * b) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    refine orderOf_eq_prime (Subtype.ext ?_) (fun h => n5 (congrArg Subtype.val h))
    rw [Subgroup.coe_pow]
    exact h6
  have hca : orderOf (c * a) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine orderOf_eq_prime (Subtype.ext ?_) (fun h => n4 (congrArg Subtype.val h))
    rw [Subgroup.coe_pow]
    exact h5
  apply F_eq_top_of_mem
  rcases hp235 with rfl | rfl | rfl
  ·
    let V := (GorensteinWalter.kleinFourOfCommutingInvolutions xJ x'J h1 h2 h4).subgroupOf FJ
    have hVF : GorensteinWalter.kleinFourOfCommutingInvolutions xJ x'J h1 h2 h4 ≤ FJ := by
      intro y hy
      change y ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1) at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact FJ.mul_mem mem_F.1 mem_F.2.1
      · exact mem_F.1
      · exact mem_F.2.1
      · exact FJ.one_mem
    have hV4 : Nat.card V = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVF).toEquiv]
      exact (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions xJ x'J h1 h2 n1 n2 n3
        h4).card_four
    have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
    have hVi : ¬ 2 ∣ V.index := by
      have := V.card_mul_index
      rw [hV4, card_F] at this
      omega
    obtain ⟨P, hP⟩ := (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgo, pow_one]) :
      IsPGroup 2 (Subgroup.zpowers (g : FJ))).exists_le_sylow
    obtain ⟨f, hf⟩ := MulAction.exists_smul_eq FJ P (hV2.toSylow hVi)
    have hfg : f * (g : FJ) * f⁻¹ ∈ V := by
      have hmem : f * (g : FJ) * f⁻¹ ∈ ((f • P : Sylow 2 FJ) : Subgroup FJ) := by
        rw [Sylow.coe_subgroup_smul]
        have := Subgroup.smul_mem_pointwise_smul (g : FJ) (MulAut.conj f) (P : Subgroup FJ)
          (hP (Subgroup.mem_zpowers _))
        simpa [MulAut.smul_def, MulAut.conj_apply] using this
      rw [hf] at hmem
      exact hmem
    have hfgN : f * (g : FJ) * f⁻¹ ∈ N := hN.conj_mem _ g.2 f
    have hfg1 : f * (g : FJ) * f⁻¹ ≠ 1 := by
      intro h1'
      have hg1 : (g : FJ) = 1 := by
        have := congrArg (fun w => f⁻¹ * w * f) h1'
        simpa [mul_assoc] using this
      rw [hg1, orderOf_one] at hgo
      omega
    rw [Subgroup.mem_subgroupOf] at hfg
    change ((f * (g : FJ) * f⁻¹ : FJ) : walterJ1) ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1) at hfg
    rcases hfg with h | h | h | h
    · right; right; left
      convert hfgN using 1
      exact Subtype.ext h.symm
    · left
      convert hfgN using 1
      exact Subtype.ext h.symm
    · right; left
      convert hfgN using 1
      exact Subtype.ext h.symm
    · exact absurd (Subtype.ext (Set.mem_singleton_iff.mp h)) hfg1
  ·
    obtain ⟨hc1, hi1⟩ := index_zpowers_F hgo
    obtain ⟨hc2, hi2⟩ := index_zpowers_F hcb
    have := le_of_isPGroup_of_normal (p := 3) (N := N)
      (IsPGroup.of_card (n := 1) (by rw [hc1, pow_one])) (by omega)
      (IsPGroup.of_card (n := 1) (by rw [hc2, pow_one])) (by omega) hgN
    exact Or.inr (Or.inr (Or.inr (Or.inl (this (Subgroup.mem_zpowers _)))))
  ·
    obtain ⟨hc1, hi1⟩ := index_zpowers_F hgo
    obtain ⟨hc2, hi2⟩ := index_zpowers_F hca
    have := le_of_isPGroup_of_normal (p := 5) (N := N)
      (IsPGroup.of_card (n := 1) (by rw [hc1, pow_one])) (by omega)
      (IsPGroup.of_card (n := 1) (by rw [hc2, pow_one])) (by omega) hgN
    exact Or.inr (Or.inr (Or.inr (Or.inr (this (Subgroup.mem_zpowers _)))))

theorem F_nonempty_mulEquiv :
    Nonempty (FJ ≃* alternatingGroup (Fin 5)) := by
  have := F_isSimpleGroup
  exact CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five card_F

@[expose] noncomputable def jankoHyp₀ : JankoHyp₀ walterJ1 where
  index_ne_two := walterJ1_index_ne_two
  abelian_sylow := hasAbelianSylowTwo
  t := tJ
  orderOf_t := orderOf_tJ
  F := FJ
  le_centralizer := F_le_centralizer
  t_not_mem := tJ_not_mem_F
  centralizer_eq := centralizer_tJ_eq
  iso := Classical.choice F_nonempty_mulEquiv

theorem isSimpleGroup_walterJ1 :
    IsSimpleGroup walterJ1 := jankoHyp₀.isSimpleGroup

@[expose] noncomputable def jankoHyp : J1.JankoHyp walterJ1 :=
  jankoHyp₀.toJankoHyp isSimpleGroup_walterJ1

theorem jankoHyp_t : jankoHyp.t = tJ := rfl

theorem jankoHyp_F : jankoHyp.F = FJ := rfl

end CFSG.Walter.J1Props
