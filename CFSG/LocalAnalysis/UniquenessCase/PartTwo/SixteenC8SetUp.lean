module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSetupB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OrderTwoEmbedding
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c8_exists_v₀ (D : Data G) (h129 : R129_1 D) (h22 : R1622 D) (h26 : R16_26 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h8 : Case167_8 D V₀ V hV L) :
    ∃ v₀ : IntMod V hV, ¬ centralizer ({v₀.val} : Set G) ≤ D.M ∧ mkTil V₀ V hV v₀ ≠ 1 ∧
      IsE64L3 ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)) := by
  obtain ⟨z, hzV, hz1, hzM⟩ := exists_centralizer_not_le D h129 h22 hS.setting.hyp16
  have hval : (IntMod.mk hV ⟨z, hzV⟩).val = z := rfl
  have hne : mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩) ≠ 1 := by
    intro h
    have hzV₀ : z ∈ V₀ := by
      rw [← map_one (mkTil V₀ V hV), mkTil_eq_iff] at h
      simpa [hval] using h
    have hcent : centralizer ({z} : Set G) = centralizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hzM (hcent.symm ▸ centralizer_le_M_of_mem_inf_V₀ D hS.setting.hyp16.hyp125
      (Subgroup.mem_zpowers z) hzV₀ hz1)
  refine ⟨IntMod.mk hV ⟨z, hzV⟩, ?_, hne, ?_⟩
  · simpa [hval] using hzM
  · obtain ⟨⟨Q, hQ, hQi⟩, hall⟩ := h26 V₀ V L hV hS h8
    obtain ⟨hsing, hnons⟩ := hall Q hQ hQi
    by_cases hQw : Q (mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩)) = 0
    · exact hsing (mkTil V₀ V hV (IntMod.mk hV ⟨z, hzV⟩)) hne hQw
    · exact absurd (by simpa [hval] using (hnons _ hQw).2 (IntMod.mk hV ⟨z, hzV⟩) rfl) hzM

theorem c8_sp6InL_centralizer (D : Data G) {L T₀ : Subgroup G} {z : G} (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hzM : ¬ centralizer ({z} : Set G) ≤ D.M)
    (hT₀ : T₀ ≤ centralizer ({z} : Set G)) :
    Sp6InL D L z T₀ (centralizer ({z} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hP : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; norm_num)
  have hloc : IsTwoLocal (centralizer ({z} : Set G)) :=
    ⟨Subgroup.zpowers z, Subgroup.zpowers_ne_bot.2 hz1, hP,
      (CFSG.ShultStronglyClosedTI.normalizer_zpowers_eq_centralizer hzord).symm⟩
  exact ⟨hT₀, inf_le_right, hzM, D.standing.charTwo _ hloc⟩

theorem c8_exists_max_min (D : Data G) {L T₀ K₀ : Subgroup G} {v₀ : G}
    (hK₀ : Sp6InL D L v₀ T₀ K₀) :
    ∃ K : Subgroup G, Sp6InL D L v₀ T₀ K ∧
      (∀ K' : Subgroup G, Sp6InL D L v₀ T₀ K' →
        padicValNat 2 (Nat.card ↥(K' ⊓ D.M)) ≤ padicValNat 2 (Nat.card ↥(K ⊓ D.M))) ∧
      ∀ K' : Subgroup G, Sp6InL D L v₀ T₀ K' →
        padicValNat 2 (Nat.card ↥(K' ⊓ D.M)) = padicValNat 2 (Nat.card ↥(K ⊓ D.M)) →
          K' ≤ K → K' = K := by
  let S : Set (Subgroup G) := {K | Sp6InL D L v₀ T₀ K}
  let f : Subgroup G → ℕ := fun K => padicValNat 2 (Nat.card ↥(K ⊓ D.M))
  obtain ⟨K₁, hK₁, hmax⟩ := Set.exists_max_image S f (Set.toFinite S) ⟨K₀, hK₀⟩
  let S' : Set (Subgroup G) := {K | K ∈ S ∧ f K = f K₁}
  obtain ⟨K, hK, hmin⟩ :=
    Set.exists_min_image S' (fun K => Nat.card K) (Set.toFinite S') ⟨K₁, hK₁, rfl⟩
  refine ⟨K, hK.1, ?_, ?_⟩
  · intro K' hK'
    exact (hmax K' hK').trans (le_of_eq hK.2.symm)
  · intro K' hK' hf hle
    have hK'S' : K' ∈ S' := ⟨hK', hf.trans hK.2⟩
    exact Subgroup.eq_of_le_of_card_ge hle (hmin K' hK'S')

theorem c8_exists_sylow_inf (D : Data G) (K : Subgroup G) :
    ∃ T' : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T' D.M ∧
      IsSylowIn 2 (T' ⊓ K) (D.M ⊓ K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, -⟩ := exists_isSylowIn_ge 2
    (bot_le : (⊥ : Subgroup G) ≤ D.M ⊓ K) IsPGroup.of_bot
  obtain ⟨T', hT', hST'⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge
      (hS.le.trans inf_le_left) hS.isPGroup
  have hT'M : T' ≤ D.M := by
    obtain ⟨Q, hQ⟩ := hT'
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have hT'2 : IsPGroup 2 T' := by
    obtain ⟨Q, hQ⟩ := hT'
    rw [← hQ]
    exact Q.isPGroup'.map _
  refine ⟨T', hT', inf_le_inf_right K hT'M, hT'2.to_inf_left, ?_⟩
  intro hdvd
  exact hS.not_dvd_relIndex (hdvd.trans
    (Subgroup.relIndex_dvd_of_le_left (L := D.M ⊓ K)
      (le_inf hST' (hS.le.trans inf_le_right))))

theorem c8_exists_setUp (D : Data G) (h129 : R129_1 D) (h22 : R1622 D) (h26 : R16_26 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h8 : Case167_8 D V₀ V hV L) :
    ∃ (v₀ : IntMod V hV) (T₀ K T' : Subgroup G), C8SetUp D V₀ V L hV v₀ T₀ K T' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₀, hnot, hne, he64⟩ := c8_exists_v₀ D h129 h22 h26 hS h8
  obtain ⟨T₀, hT₀, -⟩ := exists_isSylowIn_ge 2
    (bot_le : (⊥ : Subgroup G) ≤ D.M ⊓ centralizer ({v₀.val} : Set G)) IsPGroup.of_bot
  have hz1 : v₀.val ≠ 1 := fun h => hne (by rw [show v₀ = 1 from IntMod.val_injective h, map_one])
  have hz2 : v₀.val ^ 2 = 1 := hV.2 _ v₀.val_mem
  have hK₀ := c8_sp6InL_centralizer D (L := L) hz1 hz2 hnot (hT₀.le.trans inf_le_right)
  obtain ⟨K, hK, hmax, hmin⟩ := c8_exists_max_min D hK₀
  obtain ⟨T', hT'M, hT'K⟩ := c8_exists_sylow_inf D K
  exact ⟨v₀, T₀, K, T', hnot, hne, he64, hT₀, hK, hmax, hmin, hT'M, hT'K⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
