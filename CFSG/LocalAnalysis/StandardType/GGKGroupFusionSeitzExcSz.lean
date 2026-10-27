module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcTits
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.Blueprint
open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)
open CFSG.RankThree.PartOne.FLM (ten_le_tri)

theorem ggProfile_exp_le_of_dvd_szThirtyTwo {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z)
    (hm : m ∣ 32537600) : N ≤ 10 := by
  obtain ⟨r, -, rfl⟩ := h.two
  have h1 : 2 ^ N ∣ 2 ^ 10 * 31775 := (dvd_mul_right _ _).trans (by simpa using hm)
  have h2 : 2 ^ N ∣ 2 ^ 10 :=
    (Nat.Coprime.pow_left N (by norm_num : Nat.Coprime 2 31775)).dvd_of_dvd_mul_right h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2

theorem ggFifteen_le_tri {n : ℕ} (hn : 6 ≤ n) : 15 ≤ (n - 1) * (n - 1 + 1) / 2 := by
  have h : 5 * 6 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem ggCharTwoOrder_not_dvd_szThirtyTwo {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 2 f) (ht₁ : t ≠ .twistedB2) (ht₂ : t ≠ .twistedF4)
    (ht₃ : t ≠ .Tits) : ¬ charTwoOrder t n f ∣ 32537600 := by
  obtain ⟨-, hf, hrest⟩ := hadm
  intro h
  cases t
  case PSL =>
    obtain ⟨hn, hn22, -⟩ := hrest
    have hN := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordA (n := n - 1) (by omega) hf) h
    change ordA (n - 1) (2 ^ f) ∣ 32537600 at h
    have hmul : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
      Nat.le_mul_of_pos_left _ hf
    rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | rfl | h6
    · have hf2 : 2 ≤ f := by
        by_contra hf2
        obtain rfl : f = 1 := by omega
        exact hn22 rfl
      norm_num at hN
      interval_cases f <;> revert h <;> decide
    · norm_num at hN
      have hf3 : f ≤ 3 := by omega
      interval_cases f <;> revert h <;> decide
    · norm_num at hN
      obtain rfl : f = 1 := by omega
      revert h; decide
    · norm_num at hN
      obtain rfl : f = 1 := by omega
      revert h; decide
    · have := ggFifteen_le_tri h6
      omega
  case PSU =>
    obtain ⟨hn, hne⟩ := hrest
    have hN := ggProfile_exp_le_of_dvd_szThirtyTwo
      (profile_ordTwistedA (n := n - 1) (by omega) hf) h
    change ordTwistedA (n - 1) (2 ^ f) ∣ 32537600 at h
    have hmul : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
      Nat.le_mul_of_pos_left _ hf
    rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | h6
    · have hf2 : 2 ≤ f := by
        by_contra hf2
        obtain rfl : f = 1 := by omega
        exact hne rfl
      norm_num at hN
      have hf3 : f ≤ 3 := by omega
      interval_cases f <;> revert h <;> decide
    · norm_num at hN
      obtain rfl : f = 1 := by omega
      revert h; decide
    · norm_num at hN
      obtain rfl : f = 1 := by omega
      revert h; decide
    · have := ggFifteen_le_tri h6
      omega
  case PSp =>
    obtain ⟨hn, hne⟩ := hrest
    have hN := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordBC (n := n) hf) h
    change ordBC n (2 ^ f) ∣ 32537600 at h
    have hmul : n * n ≤ f * (n * n) := Nat.le_mul_of_pos_left _ hf
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · have hf2 : 2 ≤ f := by
        by_contra hf2
        obtain rfl : f = 1 := by omega
        exact hne rfl
      obtain rfl : f = 2 := by omega
      revert h; decide
    · obtain rfl : f = 1 := by omega
      revert h; decide
    · have : 4 * 4 ≤ n * n := Nat.mul_le_mul h4 h4
      omega
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    have hN := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordD (n := n) (by omega) hf) h
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have hmul : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    omega
  case POmegaMinus =>
    have hN := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordTwistedD (n := n) (by omega) hf) h
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have hmul : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    omega
  case G2 =>
    have hN := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordG2 hf) h
    have hf2 : 2 ≤ f := by
      by_contra hf2
      obtain rfl : f = 1 := by omega
      exact absurd hrest.2 (by norm_num)
    omega
  case F4 =>
    have := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordF4 hf) h
    omega
  case E6 =>
    have := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordE6 hf) h
    omega
  case E7 =>
    have := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordE7 hf) h
    omega
  case E8 =>
    have := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordE8 hf) h
    omega
  case twistedE6 =>
    have := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordTwistedE6 hf) h
    omega
  case trialityD4 =>
    have := ggProfile_exp_le_of_dvd_szThirtyTwo (profile_ordTrialityD4 hf) h
    omega
  case twistedB2 => exact ht₁ rfl
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 => exact ht₂ rfl
  case Tits => exact ht₃ rfl

theorem ggCard_szThirtyTwo {K : Type} [Group K]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : Nat.card K = 32537600 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eS⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  obtain rfl : a = 2 := by omega
  rw [Nat.card_congr (e.trans eS).toEquiv, CFSG.LieType.Ree.suzuki_order hF']
  norm_num

section Hyp

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggSeitzExc_card_quotComponent_dvd
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hyp : GGHypThreeSixteen p H E) {C : Subgroup (GGHypQuot H)}
    (hC : CFSG.Assembly.IsComponentOf C ⊤) :
    Nat.card ↥C ∣ Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set N : Subgroup ↥H := ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker
    with hN
  have hQ := ggIsSolvable_quot_inf_generalizedFitting hSch hyp
  obtain ⟨k, hk⟩ := ggExists_derivedSeries_le_of_isSolvable N hQ
  set Q : Subgroup ↥H := CFSG.pCore 2 ↥H with hQdef
  set π : ↥H →* GGHypQuot H := QuotientGroup.mk' Q with hπ
  have hCN : C ≤ N.map π := by
    have h1 := ggLe_derivedSeries_of_perfect (ggComponent_perfect hC) k
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective Q) k] at h1
    exact h1.trans (Subgroup.map_mono hk)
  calc Nat.card ↥C ∣ Nat.card ↥(N.map π) := Subgroup.card_dvd_of_le hCN
    _ ∣ Nat.card ↥N := Subgroup.card_map_dvd (H := N) π
    _ = Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) :=
      Nat.card_congr (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.toEquiv

end Hyp

section Marked


theorem ggMarkedModel_not_dvd_szThirtyTwo {lab : LargeEvenLabel} (htag : GGChevStTag lab)
    {R : Type} [Group R] (h : MarkedModel lab R) : ¬ Nat.card R ∣ 32537600 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht₁, ht₂, ht₃⟩ := htag
  cases t
  case twB2 => exact absurd rfl ht₁
  case twF4 => exact absurd rfl ht₂
  case twF4der => exact absurd rfl ht₃
  case B2der =>
    obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der rfl h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  case G2der =>
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
    rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
          (by norm_num)]
      decide
    all_goals exact absurd hn (by norm_num)
  all_goals
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
    obtain ⟨hadm, hcard⟩ := card_of_lieModel_two h
    rw [hcard]
    exact ggCharTwoOrder_not_dvd_szThirtyTwo hadm (by first | decide | (split_ifs <;> decide))
      (by first | decide | (split_ifs <;> decide)) (by first | decide | (split_ifs <;> decide))

theorem ggKGroupFusionAt_szThirtyTwo
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) :
    GGKGroupFusionAt GGKFSeitzSzThirtyTwo := by
  rintro W _ _ p H E i ⟨rfl, d, rfl, hd⟩ hyp hL hKH ⟨e⟩
  exfalso
  obtain ⟨C, hC⟩ := ggExists_component_of_layer_ne_bot hL
  obtain ⟨-, hmark⟩ := hyp.2.2.1 C hC
  obtain ⟨lab, -, R, _, I, F, θ, -, -, ⟨htag, -⟩, hmod⟩ :=
    largeEvenMarking_exists_markedModel hmark
  refine ggMarkedModel_not_dvd_szThirtyTwo htag hmod ?_
  rw [← Nat.card_congr θ.toEquiv, ← ggCard_szThirtyTwo d hd e]
  exact (Subgroup.card_quotient_dvd_card _).trans
    ((ggSeitzExc_card_quotComponent_dvd hSch hyp hC).trans (Subgroup.card_subgroup_dvd_card _))

end Marked

end CFSG.StandardType
