module
public import CFSG.Quasithin.Background.RonanE42SetS4
public section
namespace CFSG.Quasithin.RonanE42.Gen
open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
variable {G : Type} [Group G] [Finite G]

theorem level_window_of_bk {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K) {r : ℕ}
    (hrB : ∀ D : Subgroup G, D ≤ bk T K → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 (bk T K)) ≤ r)
    (hgB : ∀ Y : Subgroup G, Y ≤ bk T K → (∀ h ∈ bk T K, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 (bk T K)) → bk T K ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    {c : ℕ} (hcκ : c ≤ κ) (hXc : xt T K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    (hKc : ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T))) :
    ¬ Wcl Ω c T ≤ pCoreOf 2 (bk T K) ∧ ∀ j, j + r ≤ c → Wcl Ω j T ≤ pCoreOf 2 (bk T K) := by
  have hTB : T ≤ bk T K := le_bk hTK
  have hBc : ¬ bk T K ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun h =>
    hKc ((le_sup_bk hT hTK).trans (sup_le (le_sup_left.trans hXc) h))
  refine ⟨fun hW => hBc (le_stabV_of_le_pCore hΩ hT hTB hW), fun j hj => ?_⟩
  by_contra hjB
  exact hBc (le_stabV_of_good hΩ hel hfix hT hTB hrB hgB hj hcκ hjB)

open Classical in
theorem card_bad_le_of_bk_good_rank {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    {r : ℕ}
    (hrB : ∀ D : Subgroup G, D ≤ bk T K → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 (bk T K)) ≤ r)
    (hgB : ∀ Y : Subgroup G, Y ≤ bk T K → (∀ h ∈ bk T K, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 (bk T K)) → bk T K ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    (hBS : pCoreOf 2 (bk T K) ≤ T ⊓ fStarPre K)
    (hfr : CFSG.Open.pRank 2 (fStarMod K) + r ≤ iRank K) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
      iRank K := by
  set k := iRank K with hk
  set f := CFSG.Open.pRank 2 (fStarMod K) with hf
  set R := pCoreOf 2 K with hR
  set X := xt T K with hX
  set B := bk T K with hB
  set PB := pCoreOf 2 B with hPB
  have hTXX : T ≤ X := le_sup_right
  have hTB : T ≤ B := le_bk hTK
  have hRPB : R ≤ PB :=
    (le_inf (pCoreOf_le_of_sylow hT hTK) (pCoreOf_le_fStarPre K)).trans (inf_le_pCoreOf_bk hT hTK)
  have hrX : ∀ D : Subgroup G, D ≤ X → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 X) ≤ k :=
    fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (xt_rank hT hTK hF)
  have hgX : ∀ Y : Subgroup G, Y ≤ X → (∀ h ∈ X, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 X) → X ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
    fun Y hY hYn hYT => xt_good hT hTK hF hY hYn hYT
  have hXR : pCoreOf 2 X ≤ R := pCoreOf_xt_le hTK hF
  have hKXB : ∀ c, X ≤ stabV ρ (Fx ρ (Wcl Ω c T)) → B ≤ stabV ρ (Fx ρ (Wcl Ω c T)) →
      K ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun c hXc hBc =>
    (le_sup_bk hT hTK).trans (sup_le (le_sup_left.trans hXc) hBc)
  set Q : ℕ → Prop := fun c => Wcl Ω c T ≤ R with hQ
  set P : ℕ → Prop := fun c => Wcl Ω c T ≤ PB with hP
  set bad := (Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    with hbad
  have hbadQ : ∀ c ∈ bad, ¬ Q c := fun c hc hQc =>
    (Finset.mem_filter.1 hc).2 (le_stabV_of_le_pCore hΩ hT hTK hQc)
  have hbadXB : ∀ c ∈ bad, (∀ j, j + k ≤ c → Q j) ∨ (¬ P c ∧ ∀ j, j + r ≤ c → P j) := by
    intro c hc
    obtain ⟨hcr, hcK⟩ := Finset.mem_filter.1 hc
    have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
    by_cases hXc : X ≤ stabV ρ (Fx ρ (Wcl Ω c T))
    · right
      have hBc : ¬ B ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun h => hcK (hKXB c hXc h)
      refine ⟨fun hPc => hBc (le_stabV_of_le_pCore hΩ hT hTB hPc), fun j hj => ?_⟩
      by_contra hjP
      exact hBc (le_stabV_of_good hΩ hel hfix hT hTB hrB hgB hj hcκ hjP)
    · left
      intro j hj
      by_contra hjQ
      exact hXc (le_stabV_of_good hΩ hel hfix hT hTXX hrX hgX hj hcκ (fun h => hjQ (h.trans hXR)))
  by_cases hex : ∃ c, ¬ Q c
  swap
  · push Not at hex
    have : bad = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => hbadQ c hc (hex c)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  set a := Nat.find hex with ha
  have haQ : ¬ Q a := Nat.find_spec hex
  have hge : ∀ c ∈ bad, a ≤ c := fun c hc => Nat.find_min' hex (hbadQ c hc)
  by_cases hPa : P a
  ·
    obtain ⟨D, ⟨hDT, A, hA, hDA, hmA⟩, hDR⟩ : ∃ D ∈ {D | D ≤ T ∧ D ∈ Wset Ω a}, ¬ D ≤ R := by
      by_contra h
      push Not at h
      exact haQ (sSup_le h)
    have hDX : D ≤ fStarPre K :=
      ((le_Wcl hDT ⟨A, hA, hDA, hmA⟩).trans (hPa.trans hBS)).trans inf_le_right
    set SB := (Finset.range (κ + 1)).filter (fun c => ¬ P c ∧ ∀ j, j + r ≤ c → P j) with hSB
    have hsub : bad ⊆ Finset.Ico a (a + f) ∪ SB := by
      intro c hc
      obtain ⟨hcr, hcK⟩ := Finset.mem_filter.1 hc
      have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
      by_cases hXc : X ≤ stabV ρ (Fx ρ (Wcl Ω c T))
      · rcases hbadXB c hc with h | h
        ·
          refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hcr, ?_⟩)
          have hBc : ¬ B ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun hB' => hcK (hKXB c hXc hB')
          refine ⟨fun hPc => hBc (le_stabV_of_le_pCore hΩ hT hTB hPc), fun j hj => ?_⟩
          by_contra hjP
          exact hBc (le_stabV_of_good hΩ hel hfix hT hTB hrB hgB hj hcκ hjP)
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hcr, h⟩)
      · refine Finset.mem_union_left _ (Finset.mem_Ico.2 ⟨hge c hc, ?_⟩)
        by_contra hlt
        push Not at hlt
        exact hXc (xt_le_stabV_of_mem hΩ hel hfix hT hTK hF hA hDA hDT hDX hDR hmA hlt hcκ)
    calc bad.card ≤ (Finset.Ico a (a + f) ∪ SB).card := Finset.card_le_card hsub
      _ ≤ (Finset.Ico a (a + f)).card + SB.card := Finset.card_union_le _ _
      _ ≤ f + r := by
          have hSBc : SB.card ≤ r := card_filter_bad_le P r (κ + 1)
          have hIco : (Finset.Ico a (a + f)).card = f := by simp
          omega
      _ ≤ k := hfr
  · have hsub : bad ⊆ Finset.Ico a (a + k) := by
      intro c hc
      refine Finset.mem_Ico.2 ⟨hge c hc, ?_⟩
      by_contra hlt
      push Not at hlt
      rcases hbadXB c hc with h | h
      · exact haQ (h a hlt)
      · exact hPa (h.2 a (by omega))
    calc bad.card ≤ (Finset.Ico a (a + k)).card := Finset.card_le_card hsub
      _ = k := by rw [Nat.card_Ico]; omega

open Classical in
theorem e4_2_of_whole (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (W : Subgroup G → Prop)
    (hW : ∀ H ∈ Δ, W H →
      ((Finset.range ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1)).filter (fun c =>
        ¬ H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          c T)))).card ≤ iRank H)
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H ∨
        Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) T ≤ fStarPre H ∨ W H)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  by_cases hr : ∃ H ∈ Δ, CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H
  · obtain ⟨H, hH, hle⟩ := hr
    have hΔfin : Δ.Finite := Set.toFinite Δ
    rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin]
    exact (aParam_le_pRank hρ).trans (hle.trans
      (Finset.single_le_sum (f := iRank) (fun _ _ => Nat.zero_le _) (hΔfin.mem_toFinset.2 hH)))
  push Not at hr
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ'
  by_contra hbig
  have hΔfin : Δ.Finite := Set.toFinite Δ
  set Δf : Finset (Subgroup G) := hΔfin.toFinset with hΔf
  have hmemΔ : ∀ H, H ∈ Δf ↔ H ∈ Δ := fun H => hΔfin.mem_toFinset
  have hκ : ∑ H ∈ Δf, iRank H = κ := by rw [hκ', finsum_mem_eq_finite_toFinset_sum _ hΔfin]
  set Ω : Set (Subgroup G) := {A | Om ρ (κ + 1) A} with hΩ
  obtain ⟨A', hA'⟩ : ∃ A', A' ∈ aSet (κ + 1) ρ.range := by
    by_contra h
    push Not at h
    exact hbig (aParam_le_of_aSet_empty _ _ h)
  have hA₀ : A'.comap ρ ∈ Ω := Om_comap_of_mem_aSet hρ hA'
  have hΩc : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω := fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  let spl : Subgroup G → Prop := fun H =>
    H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
  let piece : Subgroup G → Subgroup G := fun H => if spl H ∨ W H then H else xt T H
  let bad : Subgroup G → Finset ℕ := fun H =>
    (Finset.range (κ + 1)).filter (fun c => ¬ piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
  have hbad : ∀ H ∈ Δf, (bad H).card ≤ iRank H := by
    intro H hH
    have hHΔ := (hmemΔ H).1 hH
    obtain ⟨hTH, hF⟩ := hΔT H hHΔ
    by_cases hsr : spl H ∨ W H
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_pos hsr]
      rw [this]
      by_cases hspl : spl H
      · exact card_bad_le_of_split hΩc hel hfx hT hTH hF hspl
      · exact hW H hHΔ (hsr.resolve_left hspl)
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_neg hsr]
      rw [this]
      exact card_bad_xt_le hΩc hel hfx hT hTH hF
  have hcard : (Δf.biUnion bad).card < (Finset.range (κ + 1)).card := by
    have h2 : (Δf.biUnion bad).card ≤ κ :=
      Finset.card_biUnion_le.trans ((Finset.sum_le_sum hbad).trans hκ.le)
    rw [Finset.card_range]
    omega
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hc)
  have hmem : ∀ H ∈ Δ, piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hHΔ
    by_contra hn
    exact hcn (Finset.mem_biUnion.2 ⟨H, (hmemΔ H).2 hHΔ, Finset.mem_filter.2 ⟨hc, hn⟩⟩)
  have hsr : ∀ H ∈ Δ, spl H ∨ W H → H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun H hH hs => by
    simpa only [piece, if_pos hs] using hmem H hH
  have hxt : ∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hH
    by_cases hs : spl H ∨ W H
    · exact (sup_le (Subgroup.map_subtype_le _) (hΔT H hH).1).trans (hsr H hH hs)
    · simpa only [piece, if_neg hs] using hmem H hH
  set N := stabV ρ (Fx ρ (Wcl Ω c T)) with hN
  rcases IsCoatomic.eq_top_or_exists_le_coatom N with hNt | ⟨M, hM, hNM⟩
  ·
    have hall : ∀ g : G, g ∈ N := fun g => hNt ▸ Subgroup.mem_top g
    have hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L := fun W hWT hW =>
      commutator_eq_of_quasisimple_fitting hLF hLq hO2 (hT.isPGroup.to_le hWT) hW
    have hcore := fix_of_level hΩc (fun A hA => (hel A hA).1) (fun A hA => hA.1) hT hA₀ hall hL
    obtain ⟨v, hv, l, hl, hne⟩ := hfix
    exact hne (hcore v hv l hl)
  apply hM.1
  rw [eq_top_iff, ← hΔ]
  refine iSup₂_le fun H hH => ?_
  by_cases hs : spl H
  · exact (hsr H hH (Or.inl hs)).trans hNM
  rcases hcov H hH hs with hco | hrk | htop | hwh
  · exact hco M hM ((hxt H hH).trans hNM)
  · exact absurd hrk (Nat.not_le.2 (hr H hH))
  · exact (le_stabV_of_Wcl_le_fStarPre hΩc hT (hΔT H hH).1 (le_sup_left.trans (hxt H hH))
      ((Wcl_mono_level hcκ T).trans htop)).trans hNM
  · exact (hsr H hH (Or.inr hwh)).trans hNM

def BkSlack (T H : Subgroup G) : Prop :=
  ∃ r : ℕ, (∀ D : Subgroup G, D ≤ bk T H → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 (bk T H)) ≤ r) ∧
    (∀ Y : Subgroup G, Y ≤ bk T H → (∀ h ∈ bk T H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 (bk T H)) → bk T H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y)) ∧
    pCoreOf 2 (bk T H) ≤ T ⊓ fStarPre H ∧
    CFSG.Open.pRank 2 (fStarMod H) + r ≤ iRank H

theorem bkSlack_of_index_two {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hidx : (T ⊓ fStarPre H).relIndex T = 2)
    (hns : ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G))
    (hrk : CFSG.Open.pRank 2 (fStarMod H) < iRank H) : BkSlack T H :=
  ⟨1, fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (bk_rank hT hTH hidx),
    fun _ hY hYn hYT => bk_good hT hTH hidx hY hYn hYT, pCoreOf_bk_le hT hTH hidx hns, hrk⟩

open Classical in
theorem e4_2_of_coatom_rank_top_or_slack (G : Type) [Group G] [Finite G] (V : Type)
    [CommGroup V] [Finite V] (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H ∨
        Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) T ≤ fStarPre H ∨ BkSlack T H)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)),
      (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ B : Subgroup G, B ≤ A →
      mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  refine e4_2_of_whole G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT (BkSlack T) ?_ hcov hfix
  rintro H hH ⟨r, hrB, hgB, hBS, hfr⟩
  obtain ⟨hTH, hF⟩ := hΔT H hH
  exact card_bad_le_of_bk_good_rank hΩc hel hfx hT hTH hF hrB hgB hBS hfr

theorem xt_le_stabV_of_gen {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    {D A : Subgroup G} (hA : A ∈ Ω) (hDA : D ≤ A) (hDT : D ≤ T)
    (hDR : ¬ D ≤ pCoreOf 2 K) {f : ℕ} (hm1 : mQuot D (D ⊓ pCoreOf 2 K) ≤ f) {j c : ℕ}
    (hmD : mQuot A D ≤ j) (hjc : j + f ≤ c) (hcκ : c ≤ κ) :
    xt T K ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
  set R := pCoreOf 2 K with hR
  have hRT : R ≤ T := pCoreOf_le_of_sylow hT hTK
  set U : Subgroup V := Fx ρ (Wcl Ω c R) with hU
  have hKst : ∀ g ∈ K, g ∈ stabV ρ U := fun g hg =>
    mem_stabV_Fx_of_conj (conjSubgroup_Wcl_eq hΩ c (conjSubgroup_pCoreOf hg))
  set X := xt T K with hX
  have hXK : X ≤ K := xt_le hTK
  set Y : Subgroup G := X ⊓ cenV ρ U with hY
  have hYX : Y ≤ X := inf_le_left
  have hYn : ∀ g ∈ X, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    refine ⟨X.mul_mem (X.mul_mem hg (hYX hy)) (X.inv_mem hg), fun u hu => ?_⟩
    have hu' : ρ g⁻¹ u ∈ U := (hKst g⁻¹ (K.inv_mem (hXK hg)) u).2 hu
    have hy' : ρ y (ρ g⁻¹ u) = ρ g⁻¹ u := hy.2 _ hu'
    calc ρ (g * y * g⁻¹) u = ρ g (ρ y (ρ g⁻¹ u)) := by
          simp only [map_mul, MulAut.mul_apply]
      _ = ρ g (ρ g⁻¹ u) := by rw [hy']
      _ = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hm : mQuot A (D ⊓ R) ≤ c := by
    have := mQuot_add (inf_le_left : D ⊓ R ≤ D) hDA
    omega
  have hFW : D ⊓ R ≤ Wcl Ω c R := le_Wcl inf_le_right ⟨A, hA, inf_le_left.trans hDA, hm⟩
  have hFx : Fx ρ (D ⊓ R) = Fx ρ A := hfix A hA _ (inf_le_left.trans hDA) (hm.trans hcκ)
  have hUD : U ≤ Fx ρ D := (Fx_anti hFW).trans (hFx.le.trans (Fx_anti hDA))
  have hDY : D ≤ Y := fun d hd =>
    ⟨(le_sup_right : T ≤ X) (hDT hd), fun u hu => mem_Fx.1 (hUD hu) d hd⟩
  have hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 X) := fun h =>
    hDR ((le_inf hDY hDT).trans (h.trans (pCoreOf_xt_le hTK hF)))
  have hYc : Y ≤ cenV ρ (Fx ρ (Wcl Ω c T)) := fun y hy u hu =>
    hy.2 u (Fx_anti (Wcl_mono_base c hRT) hu)
  refine (xt_good hT hTK hF hYX hYn hYT).trans
    (sup_le (normalizer_le_stabV hΩ c) (sup_le ?_ (hYc.trans (cenV_le_stabV ρ _))))
  exact Subgroup.le_normalizer.trans (normalizer_le_stabV hΩ c)

open Classical in
theorem card_bad_le_of_cover {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    {B : Subgroup G} (hTB : T ≤ B) (hKXB : K ≤ xt T K ⊔ B) {r f : ℕ}
    (hrB : ∀ D : Subgroup G, D ≤ B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 B) ≤ r)
    (hgB : ∀ Y : Subgroup G, Y ≤ B → (∀ h ∈ B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 B) → B ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    (hfB : ∀ D : Subgroup G, D ≤ pCoreOf 2 B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 K) ≤ f)
    (hfr : f + r ≤ iRank K) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
      iRank K := by
  set k := iRank K with hk
  set R := pCoreOf 2 K with hR
  set X := xt T K with hX
  set PB := pCoreOf 2 B with hPB
  have hTXX : T ≤ X := le_sup_right
  have hrX : ∀ D : Subgroup G, D ≤ X → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 X) ≤ k :=
    fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (xt_rank hT hTK hF)
  have hgX : ∀ Y : Subgroup G, Y ≤ X → (∀ h ∈ X, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 X) → X ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
    fun Y hY hYn hYT => xt_good hT hTK hF hY hYn hYT
  have hXR : pCoreOf 2 X ≤ R := pCoreOf_xt_le hTK hF
  have hKXB' : ∀ c, X ≤ stabV ρ (Fx ρ (Wcl Ω c T)) → B ≤ stabV ρ (Fx ρ (Wcl Ω c T)) →
      K ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun c hXc hBc => hKXB.trans (sup_le hXc hBc)
  set Q : ℕ → Prop := fun c => Wcl Ω c T ≤ R with hQ
  set P : ℕ → Prop := fun c => Wcl Ω c T ≤ PB with hP
  set bad := (Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    with hbad
  have hbadQ : ∀ c ∈ bad, ¬ Q c := fun c hc hQc =>
    (Finset.mem_filter.1 hc).2 (le_stabV_of_le_pCore hΩ hT hTK hQc)
  have hbadXB : ∀ c ∈ bad, (¬ X ≤ stabV ρ (Fx ρ (Wcl Ω c T)) ∧ ∀ j, j + k ≤ c → Q j) ∨
      (¬ P c ∧ ∀ j, j + r ≤ c → P j) := by
    intro c hc
    obtain ⟨hcr, hcK⟩ := Finset.mem_filter.1 hc
    have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
    by_cases hXc : X ≤ stabV ρ (Fx ρ (Wcl Ω c T))
    · right
      have hBc : ¬ B ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun h => hcK (hKXB' c hXc h)
      refine ⟨fun hPc => hBc (le_stabV_of_le_pCore hΩ hT hTB hPc), fun j hj => ?_⟩
      by_contra hjP
      exact hBc (le_stabV_of_good hΩ hel hfix hT hTB hrB hgB hj hcκ hjP)
    · left
      refine ⟨hXc, fun j hj => ?_⟩
      by_contra hjQ
      exact hXc (le_stabV_of_good hΩ hel hfix hT hTXX hrX hgX hj hcκ (fun h => hjQ (h.trans hXR)))
  by_cases hex : ∃ c, ¬ Q c
  swap
  · push Not at hex
    have : bad = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => hbadQ c hc (hex c)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  set a := Nat.find hex with ha
  have haQ : ¬ Q a := Nat.find_spec hex
  have hge : ∀ c ∈ bad, a ≤ c := fun c hc => Nat.find_min' hex (hbadQ c hc)
  by_cases hPa : P a
  ·
    obtain ⟨D, ⟨hDT, A, hA, hDA, hmA⟩, hDR⟩ : ∃ D ∈ {D | D ≤ T ∧ D ∈ Wset Ω a}, ¬ D ≤ R := by
      by_contra h
      push Not at h
      exact haQ (sSup_le h)
    have hDP : D ≤ PB := (le_Wcl hDT ⟨A, hA, hDA, hmA⟩).trans hPa
    have hD2 : ∀ d ∈ D, d ^ 2 = 1 := fun d hd => (hel A hA).1 d (hDA hd)
    have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
      (hel A hA).2 x (hDA hx) y (hDA hy)
    have hm1 : mQuot D (D ⊓ R) ≤ f := hfB D hDP hD2 hDc
    set SB := (Finset.range (κ + 1)).filter (fun c => ¬ P c ∧ ∀ j, j + r ≤ c → P j) with hSB
    have hsub : bad ⊆ Finset.Ico a (a + f) ∪ SB := by
      intro c hc
      obtain ⟨hcr, -⟩ := Finset.mem_filter.1 hc
      have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
      rcases hbadXB c hc with ⟨hXc, -⟩ | h
      · refine Finset.mem_union_left _ (Finset.mem_Ico.2 ⟨hge c hc, ?_⟩)
        by_contra hlt
        push Not at hlt
        exact hXc (xt_le_stabV_of_gen hΩ hfix hT hTK hF hA hDA hDT hDR hm1 hmA hlt hcκ)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hcr, h⟩)
    calc bad.card ≤ (Finset.Ico a (a + f) ∪ SB).card := Finset.card_le_card hsub
      _ ≤ (Finset.Ico a (a + f)).card + SB.card := Finset.card_union_le _ _
      _ ≤ f + r := by
          have hSBc : SB.card ≤ r := card_filter_bad_le P r (κ + 1)
          have hIco : (Finset.Ico a (a + f)).card = f := by simp
          omega
      _ ≤ k := hfr
  · have hsub : bad ⊆ Finset.Ico a (a + k) := by
      intro c hc
      refine Finset.mem_Ico.2 ⟨hge c hc, ?_⟩
      by_contra hlt
      push Not at hlt
      rcases hbadXB c hc with h | h
      · exact haQ (h.2 a hlt)
      · exact hPa (h.2 a (by omega))
    calc bad.card ≤ (Finset.Ico a (a + k)).card := Finset.card_le_card hsub
      _ = k := by rw [Nat.card_Ico]; omega

def CoverSlack (T H : Subgroup G) : Prop :=
  ∃ (B : Subgroup G) (r f : ℕ), T ≤ B ∧ H ≤ xt T H ⊔ B ∧
    (∀ D : Subgroup G, D ≤ B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 B) ≤ r) ∧
    (∀ Y : Subgroup G, Y ≤ B → (∀ h ∈ B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 B) → B ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y)) ∧
    (∀ D : Subgroup G, D ≤ pCoreOf 2 B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 H) ≤ f) ∧
    f + r ≤ iRank H

theorem coverSlack_of_bkSlack {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (h : BkSlack T H) : CoverSlack T H := by
  obtain ⟨r, hrB, hgB, hBS, hfr⟩ := h
  refine ⟨bk T H, r, CFSG.Open.pRank 2 (fStarMod H), le_bk hTH,
    (le_sup_bk hT hTH).trans (sup_le_sup_right le_sup_left _), hrB, hgB,
    fun D hD hD2 hDc => mQuot_le_pRank_fStarMod ((hD.trans hBS).trans inf_le_right) hD2 hDc, hfr⟩

open Classical in
theorem e4_2_of_coatom_rank_top_or_cover (G : Type) [Group G] [Finite G] (V : Type)
    [CommGroup V] [Finite V] (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H ∨
        Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) T ≤ fStarPre H ∨ CoverSlack T H)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)),
      (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ B : Subgroup G, B ≤ A →
      mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  refine e4_2_of_whole G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT (CoverSlack T) ?_ hcov hfix
  rintro H hH ⟨B, r, f, hTB, hKXB, hrB, hgB, hfB, hfr⟩
  obtain ⟨hTH, hF⟩ := hΔT H hH
  exact card_bad_le_of_cover hΩc hel hfx hT hTH hF hTB hKXB hrB hgB hfB hfr

abbrev bkZ (T K Z : Subgroup G) : Subgroup G :=
  K ⊓ Subgroup.normalizer ((T ⊓ Z : Subgroup G) : Set G)

theorem le_normalizer_of_conj {N Y : Subgroup G} (h : ∀ g ∈ N, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    N ≤ Subgroup.normalizer (Y : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h g hg y, fun hy => ?_⟩
  have := h g⁻¹ (N.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem conj_mem_sup {Z P : Subgroup G} {g : G} (hZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (hP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) : ∀ x ∈ Z ⊔ P, g * x * g⁻¹ ∈ Z ⊔ P := by
  have : Z ⊔ P ≤ (Z ⊔ P).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun z hz => Subgroup.mem_comap.2 (by simpa using le_sup_left (a := Z) (hZ z hz)))
      (fun p hp => Subgroup.mem_comap.2 (by simpa using le_sup_right (b := P) (hP p hp)))
  intro x hx
  simpa using Subgroup.mem_comap.1 (this hx)

theorem le_bkZ {T K Z : Subgroup G} (hTK : T ≤ K) (hZn : ∀ h ∈ K, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z) :
    T ≤ bkZ T K Z := by
  intro t ht
  refine ⟨hTK ht, le_normalizer_of_conj (N := T) (fun g hg y hy => ?_) ht⟩
  exact ⟨T.mul_mem (T.mul_mem hg hy.1) (T.inv_mem hg), hZn g (hTK hg) y hy.2⟩

theorem le_sup_bkZ {T K Z : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K) (hZK : Z ≤ K)
    (hZn : ∀ h ∈ K, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z) : K ≤ Z ⊔ bkZ T K Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK2 : IsSylowIn 2 T K := sylow_of_le hT hTK
  haveI : Finite (Sylow 2 K) :=
    Finite.of_injective (fun P : Sylow 2 K => (P : Set K)) SetLike.coe_injective
  obtain ⟨PK, hPK⟩ : ∃ P : Sylow 2 K, (P : Subgroup K) = T.subgroupOf K :=
    ⟨hTK2.toSylow, IsSylowIn.coe_toSylow hTK2⟩
  have hZn' : (Z.subgroupOf K).Normal :=
    ⟨fun y hy h => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      simpa using hZn h h.2 y hy⟩
  obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal PK hZn'.isSubnormal
  have hN := Sylow.normalizer_sup_eq_top P'
  rw [hP'] at hN
  intro x hx
  have hmem : (⟨x, hx⟩ : K) ∈ Subgroup.normalizer
      (((PK : Subgroup K) ⊓ Z.subgroupOf K : Subgroup K) : Set K) ⊔ Z.subgroupOf K := by
    rw [hN]; exact Subgroup.mem_top _
  obtain ⟨h, hh, m, hm, hhm⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hxe : x = (h : G) * (m : G) := (congrArg Subtype.val hhm).symm
  have hb : (h : G) ∈ bkZ T K Z := by
    refine ⟨h.2, ?_⟩
    show (h : G) ∈ Subgroup.normalizer ((T ⊓ Z : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyK : y ∈ K := hTK hy.1
      have h1 : (⟨y, hyK⟩ : K) ∈ (PK : Subgroup K) ⊓ Z.subgroupOf K :=
        ⟨by rw [hPK]; exact hy.1, hy.2⟩
      have h2 := ((Subgroup.mem_normalizer_iff.1 hh) _).1 h1
      rw [hPK] at h2
      exact ⟨h2.1, h2.2⟩
    · intro hy
      have hyK : y ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem h.2) (hTK hy.1)) h.2
        simpa [mul_assoc] using this
      have hc : h * (⟨y, hyK⟩ : K) * h⁻¹ ∈ (PK : Subgroup K) ⊓ Z.subgroupOf K := by
        rw [hPK]; exact ⟨hy.1, hy.2⟩
      have h2 := ((Subgroup.mem_normalizer_iff.1 hh) ⟨y, hyK⟩).2 hc
      rw [hPK] at h2
      exact ⟨h2.1, h2.2⟩
  have hm' : (m : G) ∈ Z := hm
  rw [hxe, sup_comm]
  exact Subgroup.mul_mem_sup hb hm'

def zSet (T K : Subgroup G) : Set (Subgroup G) :=
  {Z | fStarPre K ≤ Z ∧ Z ≤ xt T K ∧ ∀ h ∈ K, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z}

def IsZCan (T K Z : Subgroup G) : Prop := Z ∈ zSet T K ∧ ∀ Z' ∈ zSet T K, Z' ≤ Z

theorem sup_mem_zSet {T K Z₁ Z₂ : Subgroup G} (h₁ : Z₁ ∈ zSet T K) (h₂ : Z₂ ∈ zSet T K) :
    Z₁ ⊔ Z₂ ∈ zSet T K :=
  ⟨h₁.1.trans le_sup_left, sup_le h₁.2.1 h₂.2.1,
    fun h hh => conj_mem_sup (h₁.2.2 h hh) (h₂.2.2 h hh)⟩

theorem exists_isZCan (T K : Subgroup G) : ∃ Z, IsZCan T K Z := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hne : (zSet T K).Nonempty := ⟨fStarPre K, le_rfl, le_sup_left, fStarPre_conj_mem K⟩
  obtain ⟨Z, hZ⟩ := (Set.toFinite (zSet T K)).exists_maximal hne
  refine ⟨Z, hZ.1, fun Z' hZ' => ?_⟩
  have := hZ.2 (sup_mem_zSet hZ.1 hZ') le_sup_left
  exact le_sup_right.trans this

theorem isZCan_cover {T K Z : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hZ : IsZCan T K Z) :
    T ≤ bkZ T K Z ∧ K ≤ xt T K ⊔ bkZ T K Z ∧ pCoreOf 2 (bkZ T K Z) ≤ T ⊓ Z := by
  obtain ⟨⟨-, hZx, hZn⟩, hmax⟩ := hZ
  have hZK : Z ≤ K := hZx.trans (xt_le hTK)
  set B := bkZ T K Z with hB
  have hTB : T ≤ B := le_bkZ hTK hZn
  have hKZB : K ≤ Z ⊔ B := le_sup_bkZ hT hTK hZK hZn
  refine ⟨hTB, hKZB.trans (sup_le_sup_right hZx _), ?_⟩
  set P := pCoreOf 2 B with hP
  have hPT : P ≤ T := pCoreOf_le_of_sylow hT hTB
  have hZPK : Z ⊔ P ≤ K := sup_le hZK (hPT.trans hTK)
  have hZN : Z ≤ Subgroup.normalizer ((Z ⊔ P : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj fun z hz y hy => ?_
    have hyK : y ∈ K := hZPK hy
    have e : z * y * z⁻¹ = (z * (y * z⁻¹ * y⁻¹)) * y := by group
    rw [e]
    exact (Z ⊔ P).mul_mem
      (le_sup_left (a := Z) (Z.mul_mem hz (hZn y hyK _ (Z.inv_mem hz)))) hy
  have hBN : B ≤ Subgroup.normalizer ((Z ⊔ P : Subgroup G) : Set G) :=
    le_normalizer_of_conj fun b hb => conj_mem_sup (hZn b hb.1) (pCoreOf_conj_mem B b hb)
  have hmem : Z ⊔ P ∈ zSet T K := by
    refine ⟨(hmax _ ⟨le_rfl, le_sup_left, fStarPre_conj_mem K⟩).trans le_sup_left,
      sup_le hZx (hPT.trans le_sup_right), fun h hh y hy => ?_⟩
    have hN := hKZB.trans (sup_le hZN hBN) hh
    exact (Subgroup.mem_normalizer_iff.1 hN y).1 hy
  exact le_inf hPT (le_sup_right.trans (hmax _ hmem))

theorem mQuot_le_pRank_of_le {K Z A : Subgroup G} (hZK : Z ≤ K) (hAZ : A ≤ Z)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    mQuot A (A ⊓ pCoreOf 2 K) ≤
      CFSG.Open.pRank 2 ((Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) := by
  have hAK : A ≤ K := hAZ.trans hZK
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA2 (a : G) a.2)⟩
  set π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set E := (A.subgroupOf K).map π with hE
  have hcard : Nat.card E = 2 ^ mQuot A (A ⊓ pCoreOf 2 K) := by
    have h1 := Subgroup.relIndex_ker (K := A.subgroupOf K) (f := π)
    rw [hπ, QuotientGroup.ker_mk'] at h1
    have h2 := Subgroup.relIndex_map_map_of_injective (f := K.subtype) (CFSG.pCore 2 ↥K)
      (A.subgroupOf K) K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK] at h2
    rw [hE, ← h1, ← h2]
    show (pCoreOf 2 K).relIndex A = _
    rw [← Subgroup.inf_relIndex_left (H := A) (K := pCoreOf 2 K)]
    exact relIndex_eq_two_pow hAp _
  have hEl : IsElemAbelian 2 E := by
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
    unfold IsElemAbelian
    refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu2 : u ^ 2 = 1 :=
      Subtype.ext (by simpa using hA2 (u : G) (Subgroup.mem_subgroupOf.mp hu))
    rw [← map_pow, hu2, map_one]
  have hEF : E ≤ (Z.subgroupOf K).map π :=
    Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.2 (hAZ (Subgroup.mem_subgroupOf.1 hu))
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K),
      E ≤ (Z.subgroupOf K).map π ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card (↥K ⧸ CFSG.pCore 2 ↥K), ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    exact (k.lt_two_pow_self.le).trans
      (hE'.symm.trans_le (Subgroup.card_le_card_group (H := E')))
  unfold CFSG.Open.pRank
  exact le_csSup hbdd ⟨E, hEF, hEl, hcard⟩

theorem coverSlack_of_isZCan {T K Z : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hZ : IsZCan T K Z) {r : ℕ}
    (hrB : ∀ D : Subgroup G, D ≤ bkZ T K Z → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 (bkZ T K Z)) ≤ r)
    (hgB : ∀ Y : Subgroup G, Y ≤ bkZ T K Z → (∀ h ∈ bkZ T K Z, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 (bkZ T K Z)) →
        bkZ T K Z ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    (hfr : CFSG.Open.pRank 2 ((Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) + r ≤
      iRank K) : CoverSlack T K := by
  obtain ⟨hTB, hKXB, hPZ⟩ := isZCan_cover hT hTK hZ
  have hZK : Z ≤ K := hZ.1.2.1.trans (xt_le hTK)
  exact ⟨bkZ T K Z, r, _, hTB, hKXB, hrB, hgB,
    fun D hD hD2 hDc => mQuot_le_pRank_of_le hZK ((hD.trans hPZ).trans inf_le_right) hD2 hDc, hfr⟩

open Classical in
theorem card_bad_le_of_family {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    (ℬ : Finset (Subgroup G)) (r : Subgroup G → ℕ) {f : ℕ} (hTB : ∀ B ∈ ℬ, T ≤ B)
    (hKXB : K ≤ (xt T K ⊔ Subgroup.normalizer (T : Set G)) ⊔ ⨆ B ∈ ℬ, B)
    (hrB : ∀ B ∈ ℬ, ∀ D : Subgroup G, D ≤ B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 B) ≤ r B)
    (hgB : ∀ B ∈ ℬ, ∀ Y : Subgroup G, Y ≤ B → (∀ h ∈ B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 B) → B ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    (hfB : ∀ B ∈ ℬ, ∀ D : Subgroup G, D ≤ pCoreOf 2 B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 K) ≤ f)
    (hfr : f + ∑ B ∈ ℬ, r B ≤ iRank K) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
      iRank K := by
  set k := iRank K with hk
  set R := pCoreOf 2 K with hR
  set X := xt T K with hX
  have hTXX : T ≤ X := le_sup_right
  have hrX : ∀ D : Subgroup G, D ≤ X → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 X) ≤ k :=
    fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (xt_rank hT hTK hF)
  have hgX : ∀ Y : Subgroup G, Y ≤ X → (∀ h ∈ X, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 X) → X ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
    fun Y hY hYn hYT => xt_good hT hTK hF hY hYn hYT
  have hXR : pCoreOf 2 X ≤ R := pCoreOf_xt_le hTK hF
  have hrk : ∀ B ∈ ℬ, r B ≤ k := fun B hB =>
    (Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) hB).trans (by omega)
  set Q : ℕ → Prop := fun c => Wcl Ω c T ≤ R with hQ
  set P : Subgroup G → ℕ → Prop := fun B c => Wcl Ω c T ≤ pCoreOf 2 B with hP
  set SB : Subgroup G → Finset ℕ := fun B =>
    (Finset.range (κ + 1)).filter (fun c => ¬ P B c ∧ ∀ j, j + r B ≤ c → P B j) with hSB
  set bad := (Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    with hbad
  have hbadQ : ∀ c ∈ bad, ¬ Q c := fun c hc hQc =>
    (Finset.mem_filter.1 hc).2 (le_stabV_of_le_pCore hΩ hT hTK hQc)
  have hbadXB : ∀ c ∈ bad, (¬ X ≤ stabV ρ (Fx ρ (Wcl Ω c T)) ∧ ∀ j, j + k ≤ c → Q j) ∨
      ∃ B ∈ ℬ, c ∈ SB B := by
    intro c hc
    obtain ⟨hcr, hcK⟩ := Finset.mem_filter.1 hc
    have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
    by_cases hXc : X ≤ stabV ρ (Fx ρ (Wcl Ω c T))
    · right
      by_contra hno
      push Not at hno
      refine hcK (hKXB.trans (sup_le (sup_le hXc (normalizer_le_stabV hΩ c))
        (iSup₂_le fun B hB => ?_)))
      by_contra hBc
      refine hno B hB (Finset.mem_filter.2 ⟨hcr,
        fun hPc => hBc (le_stabV_of_le_pCore hΩ hT (hTB B hB) hPc), fun j hj => ?_⟩)
      by_contra hjP
      exact hBc (le_stabV_of_good hΩ hel hfix hT (hTB B hB) (hrB B hB) (hgB B hB) hj hcκ hjP)
    · left
      refine ⟨hXc, fun j hj => ?_⟩
      by_contra hjQ
      exact hXc (le_stabV_of_good hΩ hel hfix hT hTXX hrX hgX hj hcκ (fun h => hjQ (h.trans hXR)))
  by_cases hex : ∃ c, ¬ Q c
  swap
  · push Not at hex
    have : bad = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => hbadQ c hc (hex c)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  set a := Nat.find hex with ha
  have haQ : ¬ Q a := Nat.find_spec hex
  have hge : ∀ c ∈ bad, a ≤ c := fun c hc => Nat.find_min' hex (hbadQ c hc)
  have hSBc : (ℬ.biUnion SB).card ≤ ∑ B ∈ ℬ, r B :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun B _ => card_filter_bad_le (P B) (r B) _)
  by_cases hPa : ∃ B ∈ ℬ, P B a
  · obtain ⟨B₀, hB₀, hPa⟩ := hPa
    obtain ⟨D, ⟨hDT, A, hA, hDA, hmA⟩, hDR⟩ : ∃ D ∈ {D | D ≤ T ∧ D ∈ Wset Ω a}, ¬ D ≤ R := by
      by_contra h
      push Not at h
      exact haQ (sSup_le h)
    have hDP : D ≤ pCoreOf 2 B₀ := (le_Wcl hDT ⟨A, hA, hDA, hmA⟩).trans hPa
    have hD2 : ∀ d ∈ D, d ^ 2 = 1 := fun d hd => (hel A hA).1 d (hDA hd)
    have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
      (hel A hA).2 x (hDA hx) y (hDA hy)
    have hm1 : mQuot D (D ⊓ R) ≤ f := hfB B₀ hB₀ D hDP hD2 hDc
    have hsub : bad ⊆ Finset.Ico a (a + f) ∪ ℬ.biUnion SB := by
      intro c hc
      obtain ⟨hcr, -⟩ := Finset.mem_filter.1 hc
      have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
      rcases hbadXB c hc with ⟨hXc, -⟩ | ⟨B, hB, hcB⟩
      · refine Finset.mem_union_left _ (Finset.mem_Ico.2 ⟨hge c hc, ?_⟩)
        by_contra hlt
        push Not at hlt
        exact hXc (xt_le_stabV_of_gen hΩ hfix hT hTK hF hA hDA hDT hDR hm1 hmA hlt hcκ)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨B, hB, hcB⟩)
    calc bad.card ≤ (Finset.Ico a (a + f) ∪ ℬ.biUnion SB).card := Finset.card_le_card hsub
      _ ≤ (Finset.Ico a (a + f)).card + (ℬ.biUnion SB).card := Finset.card_union_le _ _
      _ ≤ f + ∑ B ∈ ℬ, r B := by
          have hIco : (Finset.Ico a (a + f)).card = f := by simp
          omega
      _ ≤ k := hfr
  · push Not at hPa
    have hsub : bad ⊆ Finset.Ico a (a + k) := by
      intro c hc
      refine Finset.mem_Ico.2 ⟨hge c hc, ?_⟩
      by_contra hlt
      push Not at hlt
      rcases hbadXB c hc with h | ⟨B, hB, hcB⟩
      · exact haQ (h.2 a hlt)
      · exact hPa B hB ((Finset.mem_filter.1 hcB).2.2 a (by have := hrk B hB; omega))
    calc bad.card ≤ (Finset.Ico a (a + k)).card := Finset.card_le_card hsub
      _ = k := by rw [Nat.card_Ico]; omega

def FamSlack (T H : Subgroup G) : Prop :=
  ∃ (ℬ : Finset (Subgroup G)) (r : Subgroup G → ℕ) (f : ℕ), (∀ B ∈ ℬ, T ≤ B) ∧
    H ≤ (xt T H ⊔ Subgroup.normalizer (T : Set G)) ⊔ ⨆ B ∈ ℬ, B ∧
    (∀ B ∈ ℬ, ∀ D : Subgroup G, D ≤ B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 B) ≤ r B) ∧
    (∀ B ∈ ℬ, ∀ Y : Subgroup G, Y ≤ B → (∀ h ∈ B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 B) → B ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y)) ∧
    (∀ B ∈ ℬ, ∀ D : Subgroup G, D ≤ pCoreOf 2 B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 H) ≤ f) ∧
    f + ∑ B ∈ ℬ, r B ≤ iRank H

theorem famSlack_of_coverSlack {T H : Subgroup G} (h : CoverSlack T H) : FamSlack T H := by
  obtain ⟨B, r, f, hTB, hHB, hrB, hgB, hfB, hfr⟩ := h
  refine ⟨{B}, fun _ => r, f, by simpa using hTB, ?_, by simpa using hrB, by simpa using hgB,
    by simpa using hfB, by simpa using hfr⟩
  refine hHB.trans (sup_le (le_sup_left.trans le_sup_left) ?_)
  exact le_iSup₂_of_le (f := fun (B' : Subgroup G) (_ : B' ∈ ({B} : Finset (Subgroup G))) => B')
    B (Finset.mem_singleton_self B) le_rfl |>.trans le_sup_right

theorem famSlack_of_minPar {T K Z : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hZ : IsZCan T K Z) (ℬ : Finset (Subgroup G)) (hℬ : ∀ P ∈ ℬ, P ∈ minParSet T (bkZ T K Z))
    (hcov : bkZ T K Z ≤ Subgroup.normalizer (T : Set G) ⊔ ⨆ P ∈ ℬ, P) {f : ℕ}
    (hfB : ∀ P ∈ ℬ, ∀ D : Subgroup G, D ≤ pCoreOf 2 P → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 K) ≤ f)
    (hfr : f + ∑ P ∈ ℬ, iRank P ≤ iRank K) : FamSlack T K := by
  obtain ⟨-, hKXB, -⟩ := isZCan_cover hT hTK hZ
  refine ⟨ℬ, iRank, f, fun P hP => (hℬ P hP).1, ?_, fun P _ D hD hD2 hDc =>
    mQuot_inf_pCoreOf_le hD hD2 hDc, fun P hP => good_of_mem_minParSet hT (hℬ P hP), hfB, hfr⟩
  refine hKXB.trans (sup_le (le_sup_left.trans le_sup_left) (hcov.trans ?_))
  exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

open Classical in
theorem e4_2_of_coatom_rank_top_or_fam (G : Type) [Group G] [Finite G] (V : Type)
    [CommGroup V] [Finite V] (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H ∨
        Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) T ≤ fStarPre H ∨ FamSlack T H)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)),
      (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ B : Subgroup G, B ≤ A →
      mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  refine e4_2_of_whole G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT (FamSlack T) ?_ hcov hfix
  rintro H hH ⟨ℬ, r, f, hTB, hKXB, hrB, hgB, hfB, hfr⟩
  obtain ⟨hTH, hF⟩ := hΔT H hH
  exact card_bad_le_of_family hΩc hel hfx hT hTH hF ℬ r hTB hKXB hrB hgB hfB hfr

open Classical in
theorem card_bad_le_of_famSlack {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hF : CFSG.IsQuasisimple ↥(fStarMod H) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p)
    (h : FamSlack T H) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ H ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
      iRank H := by
  obtain ⟨ℬ, r, f, hTB, hHXB, hrB, hgB, hfB, hfr⟩ := h
  exact card_bad_le_of_family hΩ hel hfix hT hTH hF ℬ r hTB hHXB hrB hgB hfB hfr

theorem famSlack_of_le_xt_sup {T H : Subgroup G}
    (h : H ≤ xt T H ⊔ Subgroup.normalizer (T : Set G)) : FamSlack T H := by
  refine ⟨∅, fun _ => 0, 0, by simp, ?_, by simp, by simp, by simp, by simp⟩
  exact h.trans le_sup_left

def E42Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
    ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
      L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
      (⨆ H ∈ Δ, H) = ⊤ →
      (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
        ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p)) →
      ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
        (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
          CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H ∨ FamSlack T H

theorem e4_2_of_residual (hres : E42Residual) :
    ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
        L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
        (⨆ H ∈ Δ, H) = ⊤ →
        (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)) ∨
          ∃ p : ℕ, p.Prime ∧ Nat.card ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)) = p)) →
        (∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) →
        aParam ρ.range ≤
          ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
            CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  intro G _ _ V _ _ _ ρ hρ hO2 T L Δ hT hLF hLq hLT hΔ hΔT hfix
  refine e4_2_of_coatom_rank_top_or_fam G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT
    (fun H hH hns => ?_) hfix
  rcases hres G hO2 T L Δ hT hLF hLq hLT hΔ hΔT H hH hns with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

def E42ResidualSum : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
    ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
      L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
      (⨆ H ∈ Δ, H) = ⊤ →
      (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
        ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p)) →
      (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) < CFSG.Open.pRank 2 (⊤ : Subgroup G) →
      ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
        (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨ FamSlack T H

theorem e42ResidualSum_of_residual (h : E42Residual) : E42ResidualSum := by
  intro G _ _ hO2 T L Δ hT hLF hLq hLT hΔ hΔT hlt H hH hns
  rcases h G hO2 T L Δ hT hLF hLq hLT hΔ hΔT H hH hns with h1 | h2 | h3
  · exact Or.inl h1
  · exfalso
    have hΔfin : Δ.Finite := Set.toFinite Δ
    have hle : iRank H ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin]
      exact Finset.single_le_sum (f := iRank) (fun _ _ => Nat.zero_le _)
        (hΔfin.mem_toFinset.2 hH)
    omega
  · exact Or.inr h3

theorem e4_2_of_residualSum (hres : E42ResidualSum) :
    ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
        L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
        (⨆ H ∈ Δ, H) = ⊤ →
        (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)) ∨
          ∃ p : ℕ, p.Prime ∧ Nat.card ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)) = p)) →
        (∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) →
        aParam ρ.range ≤
          ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
            CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  intro G _ _ V _ _ _ ρ hρ hO2 T L Δ hT hLF hLq hLT hΔ hΔT hfix
  by_cases hge : CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H
  · exact (aParam_le_pRank hρ).trans hge
  · refine e4_2_of_coatom_rank_top_or_fam G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT
      (fun H hH hns => ?_) hfix
    rcases hres G hO2 T L Δ hT hLF hLq hLT hΔ hΔT (Nat.lt_of_not_le hge) H hH hns with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))

open Classical in
theorem e4_2_of_whole_gen (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (W : Subgroup G → Prop)
    (hW : ∀ H ∈ Δ, W H →
      ((Finset.range ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1)).filter (fun c =>
        ¬ H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          c T)))).card ≤ iRank H)
    (hgen : Subgroup.normalizer (T : Set G) ⊔ ((⨆ H ∈ Δ, xt T H) ⊔
      ⨆ H ∈ {H | H ∈ Δ ∧ (H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
        W H)}, H) = ⊤)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ'
  by_contra hbig
  have hΔfin : Δ.Finite := Set.toFinite Δ
  set Δf : Finset (Subgroup G) := hΔfin.toFinset with hΔf
  have hmemΔ : ∀ H, H ∈ Δf ↔ H ∈ Δ := fun H => hΔfin.mem_toFinset
  have hκ : ∑ H ∈ Δf, iRank H = κ := by rw [hκ', finsum_mem_eq_finite_toFinset_sum _ hΔfin]
  set Ω : Set (Subgroup G) := {A | Om ρ (κ + 1) A} with hΩ
  obtain ⟨A', hA'⟩ : ∃ A', A' ∈ aSet (κ + 1) ρ.range := by
    by_contra h
    push Not at h
    exact hbig (aParam_le_of_aSet_empty _ _ h)
  have hA₀ : A'.comap ρ ∈ Ω := Om_comap_of_mem_aSet hρ hA'
  have hΩc : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω := fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  let spl : Subgroup G → Prop := fun H =>
    H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
  let piece : Subgroup G → Subgroup G := fun H => if spl H ∨ W H then H else xt T H
  let bad : Subgroup G → Finset ℕ := fun H =>
    (Finset.range (κ + 1)).filter (fun c => ¬ piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
  have hbad : ∀ H ∈ Δf, (bad H).card ≤ iRank H := by
    intro H hH
    have hHΔ := (hmemΔ H).1 hH
    obtain ⟨hTH, hF⟩ := hΔT H hHΔ
    by_cases hsr : spl H ∨ W H
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_pos hsr]
      rw [this]
      by_cases hspl : spl H
      · exact card_bad_le_of_split hΩc hel hfx hT hTH hF hspl
      · exact hW H hHΔ (hsr.resolve_left hspl)
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_neg hsr]
      rw [this]
      exact card_bad_xt_le hΩc hel hfx hT hTH hF
  have hcard : (Δf.biUnion bad).card < (Finset.range (κ + 1)).card := by
    have h2 : (Δf.biUnion bad).card ≤ κ :=
      Finset.card_biUnion_le.trans ((Finset.sum_le_sum hbad).trans hκ.le)
    rw [Finset.card_range]
    omega
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hmem : ∀ H ∈ Δ, piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hHΔ
    by_contra hn
    exact hcn (Finset.mem_biUnion.2 ⟨H, (hmemΔ H).2 hHΔ, Finset.mem_filter.2 ⟨hc, hn⟩⟩)
  have hsr : ∀ H ∈ Δ, spl H ∨ W H → H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun H hH hs => by
    simpa only [piece, if_pos hs] using hmem H hH
  have hxt : ∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hH
    by_cases hs : spl H ∨ W H
    · exact (sup_le (Subgroup.map_subtype_le _) (hΔT H hH).1).trans (hsr H hH hs)
    · simpa only [piece, if_neg hs] using hmem H hH
  set N := stabV ρ (Fx ρ (Wcl Ω c T)) with hN
  have hNt : N = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (normalizer_le_stabV hΩc c) (sup_le (iSup₂_le fun H hH => hxt H hH) ?_)
    exact iSup₂_le fun H hH => hsr H hH.1 hH.2
  have hall : ∀ g : G, g ∈ N := fun g => hNt ▸ Subgroup.mem_top g
  have hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L := fun W hWT hW =>
    commutator_eq_of_quasisimple_fitting hLF hLq hO2 (hT.isPGroup.to_le hWT) hW
  have hcore := fix_of_level hΩc (fun A hA => (hel A hA).1) (fun A hA => hA.1) hT hA₀ hall hL
  obtain ⟨v, hv, l, hl, hne⟩ := hfix
  exact hne (hcore v hv l hl)

def E42Joint : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
    ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
      L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
      (⨆ H ∈ Δ, H) = ⊤ →
      (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
        ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p)) →
      (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) < CFSG.Open.pRank 2 (⊤ : Subgroup G) →
      Subgroup.normalizer (T : Set G) ⊔ ((⨆ H ∈ Δ, xt T H) ⊔
        ⨆ H ∈ {H | H ∈ Δ ∧ (H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
          FamSlack T H)}, H) = ⊤

theorem e42Joint_of_residualSum (h : E42ResidualSum) : E42Joint := by
  intro G _ _ hO2 T L Δ hT hLF hLq hLT hΔ hΔT hlt
  set S := Subgroup.normalizer (T : Set G) ⊔ ((⨆ H ∈ Δ, xt T H) ⊔
    ⨆ H ∈ {H | H ∈ Δ ∧ (H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
      FamSlack T H)}, H) with hS
  rcases IsCoatomic.eq_top_or_exists_le_coatom S with hSt | ⟨M, hM, hSM⟩
  · exact hSt
  exfalso
  apply hM.1
  rw [eq_top_iff, ← hΔ]
  refine iSup₂_le fun H hH => ?_
  have hxM : xt T H ≤ M := ((le_iSup₂_of_le (f := fun (H : Subgroup G) (_ : H ∈ Δ) => xt T H) H hH
    le_rfl).trans (le_sup_left.trans le_sup_right)).trans hSM
  have hwhole : H ∈ {H | H ∈ Δ ∧ (H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
      FamSlack T H)} → H ≤ M := fun hm =>
    ((le_iSup₂_of_le (f := fun (H : Subgroup G) (_ : H ∈ {H | H ∈ Δ ∧
      (H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨ FamSlack T H)}) => H)
      H hm le_rfl).trans (le_sup_right.trans le_sup_right)).trans hSM
  by_cases hs : H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
  · exact hwhole ⟨hH, Or.inl hs⟩
  rcases h G hO2 T L Δ hT hLF hLq hLT hΔ hΔT hlt H hH hs with hco | hfs
  · exact hco M hM hxM
  · exact hwhole ⟨hH, Or.inr hfs⟩

theorem e4_2_of_joint (hres : E42Joint) :
    ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
        L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
        (⨆ H ∈ Δ, H) = ⊤ →
        (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)) ∨
          ∃ p : ℕ, p.Prime ∧ Nat.card ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)) = p)) →
        (∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) →
        aParam ρ.range ≤
          ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
            CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  intro G _ _ V _ _ _ ρ hρ hO2 T L Δ hT hLF hLq hLT hΔ hΔT hfix
  by_cases hge : CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H
  · exact (aParam_le_pRank hρ).trans hge
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)),
      (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ B : Subgroup G, B ≤ A →
      mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  refine e4_2_of_whole_gen G V ρ hρ hO2 T L Δ hT hLF hLq hΔT (FamSlack T) ?_
    (hres G hO2 T L Δ hT hLF hLq hLT hΔ hΔT (Nat.lt_of_not_le hge)) hfix
  rintro H hH ⟨ℬ, r, f, hTB, hKXB, hrB, hgB, hfB, hfr⟩
  obtain ⟨hTH, hF⟩ := hΔT H hH
  exact card_bad_le_of_family hΩc hel hfx hT hTH hF ℬ r hTB hKXB hrB hgB hfB hfr

end CFSG.Quasithin.RonanE42.Gen
