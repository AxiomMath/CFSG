module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABDA1B
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]

private theorem s16h_le_stabSub_commSub_of_le_normalizer
    {W : Type} [CommGroup W] {H A : Subgroup (MulAut W)}
    (hN : H ≤ Subgroup.normalizer (A : Set (MulAut W))) :
    H ≤ stabSub (commSub ⊤ A) := by
  intro g hg
  rw [← commV_eq_commSub A, mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : g⁻¹ (g u) ∈ commV A :=
      commV_apply_mem_of_mem_normalizer
        ((Subgroup.normalizer (A : Set (MulAut W))).inv_mem (hN hg)) hu
    simpa using h1
  · intro hu
    exact commV_apply_mem_of_mem_normalizer (hN hg) hu

theorem s16h_sylow_two_eq_sup_of_aut_card
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {N A B P : Subgroup (MulAut W)}
    (hPN : CFSG.ABGLocalTools.IsSylowOf 2 P N)
    (hAN : A ≤ N) (hBN : B ≤ N)
    (hNA : N ≤ normalizer (A : Set (MulAut W)))
    (hNB : N ≤ normalizer (B : Set (MulAut W)))
    (hAB : ⁅A, B⁆ = ⊥)
    (hSL_A : IsSLn ↥A 2 3) (hSL_B : IsSLn ↥B 2 3)
    (hfixA : Nat.card ↥(autSub (Subgroup.centralizer (A : Set (MulAut W))) (commSub ⊤ A)) ∣ 7)
    (hfixB : Nat.card ↥(autSub (Subgroup.centralizer (B : Set (MulAut W))) (commSub ⊤ B)) ∣ 7)
    (hsup : commSub ⊤ A ⊔ commSub ⊤ B = ⊤) :
    P = (P ⊓ A) ⊔ (P ⊓ B) := by
  classical
  have hPA : P ≤ Subgroup.normalizer (A : Set (MulAut W)) := hPN.le.trans hNA
  have hPB : P ≤ Subgroup.normalizer (B : Set (MulAut W)) := hPN.le.trans hNB
  have hSylA : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ A) A :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPN hAN hNA
  have hSylB : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ B) B :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPN hBN hNB
  have hZA : A ⊓ Subgroup.centralizer (A : Set (MulAut W)) = ⊥ :=
    s16h_inf_centralizer_eq_bot_of_center_eq_bot
      (s16h_sl28_center_eq_bot_of_isSLn hSL_A)
  have hZB : B ⊓ Subgroup.centralizer (B : Set (MulAut W)) = ⊥ :=
    s16h_inf_centralizer_eq_bot_of_center_eq_bot
      (s16h_sl28_center_eq_bot_of_isSLn hSL_B)
  have hcardAutA : Nat.card (MulAut ↥A) = 1512 := s16h_sl28_card_mulAut_of_isSLn hSL_A
  have hcardAutB : Nat.card (MulAut ↥B) = 1512 := s16h_sl28_card_mulAut_of_isSLn hSL_B
  have hcardSA : Nat.card ↥(P ⊓ A) = 8 := s16h_card_inf_of_isSylow_sl28 hSylA hSL_A
  have hcardSB : Nat.card ↥(P ⊓ B) = 8 := s16h_card_inf_of_isSylow_sl28 hSylB hSL_B
  have hdec1 : ∀ x ∈ P, ∃ s ∈ P ⊓ A,
      ∃ c ∈ P ⊓ Subgroup.centralizer (A : Set (MulAut W)), x = s * c :=
    s16h_exists_mul_of_mem_of_aut_card hPN.isPGroup hPA hZA hcardAutA hcardSA
  let CA : Subgroup (MulAut W) := P ⊓ Subgroup.centralizer (A : Set (MulAut W))
  have hB_le_CA : B ≤ Subgroup.centralizer (A : Set (MulAut W)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hAB
  have hCAinfB : CA ⊓ B = P ⊓ B := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1.1, hx.2⟩
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨⟨hx.1, hB_le_CA hx.2⟩, hx.2⟩
  have hGCA : IsPGroup 2 CA := hPN.isPGroup.to_inf_left
  have hCA_normalizer_B : CA ≤ Subgroup.normalizer (B : Set (MulAut W)) :=
    inf_le_left.trans hPB
  have hSylCA : CFSG.ABGLocalTools.IsSylowOf 2 (CA ⊓ B) B := by
    rw [hCAinfB]
    exact hSylB
  have hcardCAinfB : Nat.card ↥(CA ⊓ B) = 8 := by
    rw [hCAinfB]
    exact hcardSB
  have hdec2 : ∀ x ∈ CA, ∃ s ∈ CA ⊓ B,
      ∃ c ∈ CA ⊓ Subgroup.centralizer (B : Set (MulAut W)), x = s * c :=
    s16h_exists_mul_of_mem_of_aut_card hGCA hCA_normalizer_B hZB hcardAutB hcardCAinfB
  have hstep3 : CA ⊓ Subgroup.centralizer (B : Set (MulAut W)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgCA, hgB⟩ := hg
    rw [Subgroup.mem_bot]
    have hgP : g ∈ P := hgCA.1
    have hgA : g ∈ Subgroup.centralizer (A : Set (MulAut W)) := hgCA.2
    have hord : ∃ k : ℕ, orderOf g = 2 ^ k := by
      have h := (IsPGroup.iff_orderOf.mp hPN.isPGroup) ⟨g, hgP⟩
      rwa [← Subgroup.orderOf_coe] at h
    have hcentA : g ∈ centSub (commSub ⊤ A) := by
      have hstabA : g ∈ stabSub (commSub ⊤ A) :=
        s16h_le_stabSub_commSub_of_le_normalizer
          (Subgroup.centralizer_le_normalizer (A : Set (MulAut W))) hgA
      have hφmem : resHom (commSub ⊤ A) ⟨g, hstabA⟩ ∈
          autSub (Subgroup.centralizer (A : Set (MulAut W))) (commSub ⊤ A) :=
        mem_autSub.mpr ⟨⟨g, hstabA⟩, hgA, rfl⟩
      have hdvd7 : orderOf (resHom (commSub ⊤ A) ⟨g, hstabA⟩) ∣
          Nat.card ↥(autSub (Subgroup.centralizer (A : Set (MulAut W))) (commSub ⊤ A)) := by
        have h := orderOf_dvd_natCard
          (⟨resHom (commSub ⊤ A) ⟨g, hstabA⟩, hφmem⟩ :
            ↥(autSub (Subgroup.centralizer (A : Set (MulAut W))) (commSub ⊤ A)))
        simpa using h
      have hdvdord : orderOf (resHom (commSub ⊤ A) ⟨g, hstabA⟩) ∣ orderOf g := by
        have h := orderOf_map_dvd (resHom (commSub ⊤ A)) ⟨g, hstabA⟩
        rwa [← Subgroup.orderOf_coe] at h
      have hφ1 : resHom (commSub ⊤ A) ⟨g, hstabA⟩ = 1 := by
        obtain ⟨k, hk⟩ := hord
        have hcop : Nat.Coprime 7 (orderOf g) := by
          rw [hk]
          exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 7)).symm
        have hgcd : orderOf (resHom (commSub ⊤ A) ⟨g, hstabA⟩) ∣ Nat.gcd 7 (orderOf g) :=
          Nat.dvd_gcd (hdvd7.trans hfixA) hdvdord
        rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at hgcd
        exact orderOf_eq_one_iff.mp hgcd
      rw [mem_centSub]
      intro u hu
      have h := congrArg (fun ψ : MulAut ↥(commSub ⊤ A) =>
        ((ψ ⟨u, hu⟩ : ↥(commSub ⊤ A)) : W)) hφ1
      rw [resHom_apply] at h
      simpa using h
    have hcentB : g ∈ centSub (commSub ⊤ B) := by
      have hstabB : g ∈ stabSub (commSub ⊤ B) :=
        s16h_le_stabSub_commSub_of_le_normalizer
          (Subgroup.centralizer_le_normalizer (B : Set (MulAut W))) hgB
      have hφmem : resHom (commSub ⊤ B) ⟨g, hstabB⟩ ∈
          autSub (Subgroup.centralizer (B : Set (MulAut W))) (commSub ⊤ B) :=
        mem_autSub.mpr ⟨⟨g, hstabB⟩, hgB, rfl⟩
      have hdvd7 : orderOf (resHom (commSub ⊤ B) ⟨g, hstabB⟩) ∣
          Nat.card ↥(autSub (Subgroup.centralizer (B : Set (MulAut W))) (commSub ⊤ B)) := by
        have h := orderOf_dvd_natCard
          (⟨resHom (commSub ⊤ B) ⟨g, hstabB⟩, hφmem⟩ :
            ↥(autSub (Subgroup.centralizer (B : Set (MulAut W))) (commSub ⊤ B)))
        simpa using h
      have hdvdord : orderOf (resHom (commSub ⊤ B) ⟨g, hstabB⟩) ∣ orderOf g := by
        have h := orderOf_map_dvd (resHom (commSub ⊤ B)) ⟨g, hstabB⟩
        rwa [← Subgroup.orderOf_coe] at h
      have hφ1 : resHom (commSub ⊤ B) ⟨g, hstabB⟩ = 1 := by
        obtain ⟨k, hk⟩ := hord
        have hcop : Nat.Coprime 7 (orderOf g) := by
          rw [hk]
          exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 7)).symm
        have hgcd : orderOf (resHom (commSub ⊤ B) ⟨g, hstabB⟩) ∣ Nat.gcd 7 (orderOf g) :=
          Nat.dvd_gcd (hdvd7.trans hfixB) hdvdord
        rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at hgcd
        exact orderOf_eq_one_iff.mp hgcd
      rw [mem_centSub]
      intro u hu
      have h := congrArg (fun ψ : MulAut ↥(commSub ⊤ B) =>
        ((ψ ⟨u, hu⟩ : ↥(commSub ⊤ B)) : W)) hφ1
      rw [resHom_apply] at h
      simpa using h
    have hone : g = 1 := by
      ext w
      have hw : w ∈ commSub ⊤ A ⊔ commSub ⊤ B := by
        rw [hsup]
        exact Subgroup.mem_top w
      rw [Subgroup.mem_sup] at hw
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      show g (a * b) = (1 : MulAut W) (a * b)
      rw [map_mul, mem_centSub.mp hcentA a ha, mem_centSub.mp hcentB b hb]
      rfl
    exact hone
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro p hp
  obtain ⟨s, hs, c, hc, rfl⟩ := hdec1 p hp
  obtain ⟨b, hb, d, hd, rfl⟩ := hdec2 c hc
  have hb' : b ∈ P ⊓ B := by
    rwa [hCAinfB] at hb
  have hd' : d = 1 := by
    have : d ∈ (⊥ : Subgroup (MulAut W)) := by rwa [hstep3] at hd
    exact Subgroup.mem_bot.mp this
  rw [hd', mul_one]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hb')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
