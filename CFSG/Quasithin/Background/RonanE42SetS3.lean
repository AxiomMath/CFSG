module
public import CFSG.Quasithin.Background.RonanE42SetS2
public import CFSG.Quasithin.Background.RonanE42MinPar
public import CFSG.Quasithin.Background.RonanE42Layer
public import CFSG.Quasithin.Background.RonanE42Om
public section
namespace CFSG.Quasithin.RonanE42.Gen
open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]

open Classical in
theorem card_bad_xt_le {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ xt T K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
      iRank K := by
  have hTX : T ≤ xt T K := le_sup_right
  have hrX : ∀ D : Subgroup G, D ≤ xt T K → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 (xt T K)) ≤ iRank K :=
    fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (xt_rank hT hTK hF)
  refine (Finset.card_le_card ?_).trans
    (card_filter_bad_le (fun c => Wcl Ω c T ≤ pCoreOf 2 (xt T K)) (iRank K) (κ + 1))
  intro c hc
  obtain ⟨hcr, hcH⟩ := Finset.mem_filter.1 hc
  have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
  refine Finset.mem_filter.2 ⟨hcr, fun hQ => hcH (le_stabV_of_le_pCore hΩ hT hTX hQ), ?_⟩
  intro j hj
  by_contra hjQ
  exact hcH (le_stabV_of_good hΩ hel hfix hT hTX hrX
    (fun Y hY hYn hYT => xt_good hT hTK hF hY hYn hYT) hj hcκ hjQ)

theorem e4_2_mixed (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ P R : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hPΔ : P ⊆ Δ)
    (hgen : Subgroup.normalizer (T : Set G) ⊔ ((⨆ H ∈ P, xt T H) ⊔ ⨆ H ∈ Δ \ P, H) = ⊤)
    (hRΔ : R ⊆ Δ) (hR : ∀ H ∈ R, (T ⊓ fStarPre H).relIndex T = 2)
    (hcase : ∀ H ∈ Δ, H ∉ P → H ∉ R →
      H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
        ((T ⊓ fStarPre H).relIndex T = 2 ∧ CFSG.Open.pRank 2 (fStarMod H) < iRank H))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + R.ncard := by
  classical
  have hΔfin : Δ.Finite := Set.toFinite Δ
  set Δf : Finset (Subgroup G) := hΔfin.toFinset with hΔf
  have hmemΔ : ∀ H, H ∈ Δf ↔ H ∈ Δ := fun H => hΔfin.mem_toFinset
  have hRcard : R.ncard = (Δf.filter (· ∈ R)).card := by
    rw [Set.ncard_eq_toFinset_card R (Set.toFinite R)]
    congr 1
    ext H
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, hmemΔ]
    exact ⟨fun h => ⟨hRΔ h, h⟩, fun h => h.2⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin, hRcard]
  set κ := (∑ H ∈ Δf, iRank H) + (Δf.filter (· ∈ R)).card with hκ
  apply aParam_le_of_aSet_empty
  intro A' hA'
  let Ω : Set (Subgroup G) := {A | Om ρ (κ + 1) A}
  have hA₀ : A'.comap ρ ∈ Ω := Om_comap_of_mem_aSet hρ hA'
  have hΩc : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω := fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  let piece : Subgroup G → Subgroup G := fun H => if H ∈ P then xt T H else H
  let bad : Subgroup G → Finset ℕ := fun H =>
    (Finset.range (κ + 1)).filter (fun c => ¬ piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
  have hbad : ∀ H ∈ Δf, (bad H).card ≤ iRank H + if H ∈ R then 1 else 0 := by
    intro H hH
    have hHΔ := (hmemΔ H).1 hH
    obtain ⟨hTH, hF⟩ := hΔT H hHΔ
    by_cases hHP : H ∈ P
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_pos hHP]
      rw [this]
      exact (card_bad_xt_le hΩc hel hfx hT hTH hF).trans (Nat.le_add_right _ _)
    have hbH : bad H = (Finset.range (κ + 1)).filter
        (fun c => ¬ H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
      simp only [bad, piece, if_neg hHP]
    rw [hbH]
    by_cases hspl : H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
    · exact (card_bad_le_of_split hΩc hel hfx hT hTH hF hspl).trans (Nat.le_add_right _ _)
    by_cases hHR : H ∈ R
    · rw [if_pos hHR]
      exact (card_bad_le_of_index_two hΩc hel hfx hT hTH hF (hR H hHR) hspl).1
    · rw [if_neg hHR, add_zero]
      obtain ⟨hidx, hrk⟩ := (hcase H hHΔ hHP hHR).resolve_left hspl
      exact card_bad_le_of_rank hΩc hel hfx hT hTH hF hidx hspl hrk
  have hcard : (Δf.biUnion bad).card < (Finset.range (κ + 1)).card := by
    have h2 : (Δf.biUnion bad).card ≤ κ := by
      refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum hbad).trans ?_)
      rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
    rw [Finset.card_range]
    omega
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hmem : ∀ H ∈ Δ, piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hHΔ
    by_contra hn
    exact hcn (Finset.mem_biUnion.2 ⟨H, (hmemΔ H).2 hHΔ, Finset.mem_filter.2 ⟨hc, hn⟩⟩)
  have hP : (⨆ H ∈ P, xt T H) ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := iSup₂_le fun H hH => by
    have := hmem H (hPΔ hH)
    simpa only [piece, if_pos hH] using this
  have hQ : (⨆ H ∈ Δ \ P, H) ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := iSup₂_le fun H hH => by
    have := hmem H hH.1
    simpa only [piece, if_neg hH.2] using this
  have hall : ∀ g : G, g ∈ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro g
    have hle := sup_le (normalizer_le_stabV hΩc c) (sup_le hP hQ)
    rw [hgen] at hle
    exact hle (Subgroup.mem_top g)
  have hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L := fun W hWT hW =>
    commutator_eq_of_quasisimple_fitting hLF hLq hO2 (hT.isPGroup.to_le hWT) hW
  have hcore := fix_of_level hΩc (fun A hA => (hel A hA).1) (fun A hA => hA.1) hT hA₀ hall hL
  obtain ⟨v, hv, l, hl, hne⟩ := hfix
  exact hne (hcore v hv l hl)

abbrev minParSet (T H : Subgroup G) : Set (Subgroup G) :=
  {P | T ≤ P ∧ P ≤ H ∧ ∃ M : Subgroup G,
    (∀ H' : Subgroup G, T ≤ H' → H' ≤ P → H' ≠ P → H' ≤ M) ∧ ¬ P ≤ M}

theorem good_of_mem_minParSet {T H P : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hP : P ∈ minParSet T H) : (∀ Y : Subgroup G, Y ≤ P → (∀ h ∈ P, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 P) → P ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y)) := by
  obtain ⟨hTP, -, M, hM, hPM⟩ := hP
  exact fun Y hY hYn hYT => good_of_minimalParabolic hT hTP hM hPM hY hYn hYT

theorem e4_2_of_coatom (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      ∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  classical
  set P : Set (Subgroup G) :=
    {H | H ∈ Δ ∧ ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)} with hP
  have hgen : Subgroup.normalizer (T : Set G) ⊔ ((⨆ H ∈ P, xt T H) ⊔ ⨆ H ∈ Δ \ P, H) = ⊤ := by
    set S := Subgroup.normalizer (T : Set G) ⊔ ((⨆ H ∈ P, xt T H) ⊔ ⨆ H ∈ Δ \ P, H) with hS
    rcases IsCoatomic.eq_top_or_exists_le_coatom S with h | ⟨M, hM, hSM⟩
    · exact h
    exfalso
    apply hM.1
    rw [eq_top_iff, ← hΔ]
    refine iSup₂_le fun H hH => ?_
    by_cases hHP : H ∈ P
    · refine hcov H hH hHP.2 M hM ?_
      exact ((le_iSup₂_of_le (f := fun (H : Subgroup G) (_ : H ∈ P) => xt T H) H hHP le_rfl).trans
        (le_sup_left.trans le_sup_right)).trans hSM
    · exact ((le_iSup₂_of_le (f := fun (H : Subgroup G) (_ : H ∈ Δ \ P) => H) H ⟨hH, hHP⟩
        le_rfl).trans (le_sup_right.trans le_sup_right)).trans hSM
  have h := e4_2_mixed G V ρ hρ hO2 T L Δ P ∅ hT hLF hLq hΔT (fun H hH => hH.1) hgen
    (Set.empty_subset _) (fun H hH => hH.elim) (fun H hH hHP _ => by
      left
      by_contra hn
      exact hHP ⟨hH, hn⟩) hfix
  simpa using h

end CFSG.Quasithin.RonanE42.Gen
