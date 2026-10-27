module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLMark
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix

section Main

theorem not_ggNbrClauseFiveMarking_of_inner {G : Type} [Group G] {K' : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) {x : G}
    (hinn : ∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k)
    (hHS : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
      MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') →
        ¬ LargeEvenHalfSplit p lab (Subgroup.center ↥K' = ⊥))
    (hRIF : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markChar lab = 2 →
      MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') → LargeEvenLabelAll lab (GGRawInnField p)) :
    ¬ GGNbrClauseFiveMarking p x K' := by
  intro hmark
  rcases largeEvenMarking_or hmark with hHS' | hPF
  ·
    obtain ⟨lab, hlab, R, _, I, F, θ, -, -, hHS'', hMM⟩ := largeEvenMarking_exists_markedModel hHS'
    have hX : MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') := MarkedModel.of_mulEquiv θ.symm hMM
    by_cases hc : markChar lab = 2
    · exact hHS lab hlab hc hX hHS''
    ·
      obtain ⟨t, l, n⟩ := lab
      cases t
      all_goals first
        | exact absurd rfl hc
        | (obtain ⟨-, hl⟩ := hlab
           obtain ⟨-, hn⟩ := hl
           simp only at hn
           subst hn
           rcases LinNonsplit.halfSplit_cases hHS'' with h1 | h1 | h1 | ⟨h0, -, -⟩ | ⟨h0 | h0, -, -⟩
           · exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using h1))
           · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h1))
           · exact hp3 h1
           all_goals simp at h0)
  ·
    have hS : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
        (θ : ↥K' ⧸ Subgroup.center ↥K' ≃* R),
        (LargeEvenPrimeField p lab I F (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x) ∧
          MarkedModel lab R) →
        (markChar lab = 2 ∧ MarkedModel lab (↥K' ⧸ Subgroup.center ↥K')) ∨ lab.tag = .B2der ∨
          lab.tag = .G2der := by
      intro lab R _ I F θ hP
      have hX : MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') := MarkedModel.of_mulEquiv θ.symm hP.2
      by_cases hc : markChar lab = 2
      · exact Or.inl ⟨hc, hX⟩
      · right
        obtain ⟨t, l, n⟩ := lab
        cases t <;> first | exact absurd rfl hc | simp
    have hall : ∀ lab, LargeEvenInLambda2 lab →
        ((markChar lab = 2 ∧ MarkedModel lab (↥K' ⧸ Subgroup.center ↥K')) ∨ lab.tag = .B2der ∨
          lab.tag = .G2der) →
        LargeEvenLabelAll lab fun R _ I F => (∀ φ ∈ F, φ = 1) ∨ GGRawInnField p R I F := by
      intro lab hlab hS'
      rcases hS' with ⟨hc, hX⟩ | hB | hG2
      · exact LargeEvenLabelAll.mono (fun R _ I F h => Or.inr h) (hRIF lab hlab hc hX)
      · exact largeEvenLabelAll_b2der hB fun K _ _ hK =>
          Or.inl fun φ hφ => matFieldImage_eq_one_of_card_two hK _ hφ
      · exact largeEvenLabelAll_smallExc hlab (Or.inl hG2) fun A K _ _ hK H =>
          Or.inl fun φ hφ => chevFieldImage_eq_one_of_card_two hK H hφ
    have hPF' := largeEvenMarking_and_labelAll hall hS (largeEvenMarking_markedModel hPF)
    obtain ⟨-, lab, hlab, hraw'⟩ := hPF'
    obtain ⟨R, _, I, F, hs, hna, θ, ⟨⟨-, f', hf', u', hu', hord, hind⟩, -⟩, hP'⟩ :=
      largeEvenRawDatum_exists hraw'
    rcases hP' with htriv | hRIF'
    · rw [htriv f' hf', orderOf_one] at hord
      exact hp.one_lt.ne hord
    obtain ⟨-, -, hinnI, hnot⟩ := hRIF' hs hna
    obtain ⟨k, hk, hkx⟩ := hinn
    set r₀ : R := (θ (QuotientGroup.mk (⟨k, hk⟩ : ↥K')))⁻¹ with hr₀
    have hc : u' * f' * u'⁻¹ = MulAut.conj r₀ := by
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl' : k⁻¹ * (l : G) * k ∈ K' :=
        K'.mul_mem (K'.mul_mem (K'.inv_mem hk) l.2) hk
      have h1 := hind l ⟨k⁻¹ * l * k, hl'⟩ (hkx l l.2).symm
      have h2 : (⟨k⁻¹ * l * k, hl'⟩ : ↥K') = (⟨k, hk⟩ : ↥K')⁻¹ * l * ⟨k, hk⟩ := rfl
      rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul,
        map_mul, map_inv, MulAut.conj_apply, hr₀, inv_inv]
    have hf'I : f' ∈ I := by
      have h3 : f' = MulAut.conj (u'⁻¹ r₀) := by
        calc f' = u'⁻¹ * (u' * f' * u'⁻¹) * u' := by group
          _ = u'⁻¹ * MulAut.conj r₀ * u' := by rw [hc]
          _ = MulAut.conj (u'⁻¹ r₀) := by
            ext s
            simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
              MulAut.inv_apply_self]
      rw [h3]
      exact hinnI _
    exact hnot f' hf' hord hf'I

end Main

theorem tag_of_markTag_PSp {lab : LargeEvenLabel} (hT : markTag lab = .PSp) :
    lab.tag = .B ∨ lab.tag = .C := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag] at hT
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | simp at hT
    | (by_cases h3 : l = 3 <;> simp [h3] at hT <;> done)
    | (by_cases h2 : l = 2 <;> by_cases h3 : l = 3 <;> simp [h2, h3] at hT)

theorem not_halfSplit_of_markPSp {lab : LargeEvenLabel} {p f : ℕ} (hp3 : p ≠ 3)
    (hT : markTag lab = .PSp) (hD : markDeg lab = f) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) {c : Prop} : ¬ LargeEvenHalfSplit p lab c := by
  intro h
  have ht := tag_of_markTag_PSp hT
  obtain ⟨t, l, n⟩ := lab
  simp only at ht
  have hn : n = f := by
    rcases ht with rfl | rfl <;> exact hD
  subst hn
  rcases LinNonsplit.halfSplit_cases h with h1 | h1 | h1 | ⟨h0, -, -⟩ | ⟨h0 | h0, -, -⟩
  · exact hq1 h1
  · exact hq2 h1
  · exact hp3 h1
  all_goals (rcases ht with rfl | rfl <;> simp at h0)

section Symplectic

theorem not_ggNbrClauseFiveMarking_sp {G : Type} [Group G] {K' : Subgroup G} {s f : ℕ}
    {F' : Type} [Field F'] (hF' : Nat.card F' = 2 ^ f) (e : ↥K' ≃* StatedSp s F') (hs : 2 ≤ s)
    (hsf : (s, f) ≠ (2, 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) {x : G} (hinn : ∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k) :
    ¬ GGNbrClauseFiveMarking p x K' := by
  have : Finite F' := CFSG.SeitzReduction.LinearPilot.finite_of_card_eq_two_pow hF'
  have : CharP F' 2 := CFSG.SeitzReduction.LinearPilot.charP_two_of_card_eq_two_pow hF'
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hZ : Subgroup.center ↥K' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ Subgroup.center (StatedSp s F') := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w']
    rw [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at hez
    exact Subgroup.mem_bot.mpr (e.injective (hez.trans (map_one e).symm))
  let ε : ↥K' ⧸ Subgroup.center ↥K' ≃* StatedSp s F' :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hL : LieModel (↥K' ⧸ Subgroup.center ↥K') .PSp s 2 f :=
    CFSG.SeitzReduction.SymplecticPilot.lieModel_of_mulEquiv_statedSp ε hF' hs hsf
  have hdet : ∀ lab : LargeEvenLabel, markChar lab = 2 →
      MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') → markTag lab = .PSp ∧ markDeg lab = f := by
    intro lab hc hX
    have hX' : LieModel (↥K' ⧸ Subgroup.center ↥K') (markTag lab) (markRank lab) 2
        (markDeg lab) := by
      have h := hX
      unfold MarkedModel at h
      rwa [hc] at h
    obtain ⟨h1, -, h3⟩ := CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL hX'
    exact ⟨h1, h3⟩
  refine not_ggNbrClauseFiveMarking_of_inner hp hp3 hinn (fun lab _ hc hX => ?_)
    (fun lab hlab hc hX => ?_)
  · obtain ⟨hT, hD⟩ := hdet lab hc hX
    exact not_halfSplit_of_markPSp hp3 hT hD hq1 hq2
  · obtain ⟨hT, -⟩ := hdet lab hc hX
    exact ggRawInnFieldOn_symplectic p hp hp2 lab hlab (tag_of_markTag_PSp hT)

end Symplectic

end ClNonsplit

end CFSG.StandardType
