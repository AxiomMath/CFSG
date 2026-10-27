module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicCoverCenterOddHolds
public import CFSG.Quasithin.Background.E2TwoProofSporM12
public import CFSG.Quasithin.Vol2.KGFactAutSylowM12
public import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

open CFSG.Quasithin.E2P.SporB CFSG.QuasithinUnique.Vol2Native.A312L.M12Lat in
theorem k_M12SThreePair_holds :
    K_M12SThreePair := by
  intro Y _ _ K hKN hq hodd hM12 _hcent hidx S hS
  have : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hq.1
  obtain ⟨e₀⟩ := hM12
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_perfect_odd_cover e₀ hodd fun π hπ hC hodd' =>
      CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd'
  let eK : ↥K ≃* ↥m12Grp :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      e₀).trans (MulEquiv.subgroupCongr mGens_closure).symm
  obtain ⟨U, P₀, P₁, hU, hU₀, hU₁, h₀, h₁, hgen, hinv⟩ := hasInvPair_M12
  have hX : Nonempty (↥m12Grp ≃* ↥CFSG.Blueprint.NativeSporadic.M12) :=
    ⟨MulEquiv.subgroupCongr mGens_closure⟩
  have hcases : ∀ P : Subgroup ↥m12Grp, U ≤ P → P ≠ ⊤ →
      (Nat.card P = 64 ∧ Nat.card (CFSG.Open.pCoreOf 2 P) = 64) ∨
        (Nat.card P = 192 ∧ Nat.card (CFSG.Open.pCoreOf 2 P) = 32) := by
    intro P hUP hP
    rcases CFSG.Quasithin.H13.KGSporLat.m12_overgroups hX hU hUP with h | ⟨m, hm, hc, ho, -⟩
    · exact absurd h hP
    · simp only [CFSG.Quasithin.H13.KGSporLat.m12Mems, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact Or.inl ⟨hc, ho⟩
      · exact Or.inr ⟨hc, ho⟩
      · exact Or.inr ⟨hc, ho⟩
  have hUtop : U ≠ ⊤ := fun h => h₀ (top_le_iff.mp (h ▸ hU₀))
  have hUc : Nat.card U = 64 := by
    rcases hcases U le_rfl hUtop with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hU.2.1.exists_card_eq
      have h3 : 3 ∣ 2 ^ k := by rw [← hk, h]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at this
  have hmem : ∀ {P P' : Subgroup ↥m12Grp}, U ≤ P → U ≤ P' → P ≠ ⊤ → P' ≠ ⊤ → P ⊔ P' = ⊤ →
      Nat.card P = 192 ∧ Nat.card (CFSG.Open.pCoreOf 2 P) = 32 := by
    intro P P' hUP hUP' hP hP' hPP'
    rcases hcases P hUP hP with ⟨h, -⟩ | h
    · exfalso
      have hPU : P = U := (Subgroup.eq_of_le_of_card_ge hUP (by rw [h, hUc])).symm
      apply hP'
      rw [← hPP', hPU, sup_eq_right.mpr hUP']
    · exact h
  obtain ⟨hc₀, ho₀⟩ := hmem hU₀ hU₁ h₀ h₁ hgen
  obtain ⟨hc₁, ho₁⟩ := hmem hU₁ hU₀ h₁ h₀ (by rw [sup_comm]; exact hgen)
  have hn : ∀ {P : Subgroup ↥m12Grp}, U ≤ P → Nat.card (CFSG.Open.pCoreOf 2 P) = 32 →
      ¬ P ≤ Subgroup.normalizer (U : Set ↥m12Grp) := by
    intro P hUP ho hle
    have hle' : U ≤ CFSG.Open.pCoreOf 2 P :=
      CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hUP
        (fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hle hx) y).mp hy) hU.2.1
    have := Subgroup.card_le_of_le hle'
    rw [hUc, ho] at this
    norm_num at this
  have := hKN
  exact exists_sThree_pair_of_model hidx eK hS hU hU₀ hU₁ (by rw [hc₀, hUc])
    (by rw [hc₁, hUc]) (hn hU₀ ho₀) (hn hU₁ ho₁) hgen hinv



end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
