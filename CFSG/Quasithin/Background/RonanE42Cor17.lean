module

public import CFSG.Quasithin.Background.RonanE42Gen
public import CFSG.Quasithin.Background.RonanE42Group
public import CFSG.Quasithin.Background.RonanE42Rank

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
open CFSG.Quasithin.RonanE42.Gen
open scoped commutatorElement

variable {G V : Type} [Group G] [Finite G] [CommGroup V]

section Levels

variable {ρ : G →* MulAut V} {T : Subgroup G} {Ω : Set (Subgroup G)}

theorem normalizer_le_stabV (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω) (c : ℕ) :
    Subgroup.normalizer (T : Set G) ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun _ hg =>
  mem_stabV_Fx_of_conj (conjSubgroup_Wcl_eq hΩ c (conjSubgroup_eq_iff_mem_normalizer.2 hg))

theorem le_stabV_of_le_pCore (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω) {H : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) {c : ℕ} (hc : Wcl Ω c T ≤ pCoreOf 2 H) :
    H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
  intro g hg
  have hRT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow hT hTH
  have heq : Wcl Ω c T = Wcl Ω c (pCoreOf 2 H) := Wcl_eq_of_le hRT hc
  have hconj : conjSubgroup (Wcl Ω c T) g = Wcl Ω c T := by
    rw [heq]
    exact conjSubgroup_Wcl_eq hΩ c (conjSubgroup_pCoreOf hg)
  exact mem_stabV_Fx_of_conj hconj

theorem le_stabV_of_not_le (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hF : CFSG.IsQuasisimple ↥(fStarMod H) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p)
    {j c : ℕ} (hjc : j + iRank H ≤ c) (hcκ : c ≤ κ) (hnot : ¬ Wcl Ω j T ≤ pCoreOf 2 H) (e : ℕ)
    (hcase : H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
      ∃ X₀ : Subgroup G, (∀ Y : Subgroup G, Y ≤ H → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
        fStarPre H ≤ Y ⊔ pCoreOf 2 H → X₀ ≤ Y) ∧ X₀.relIndex T ≤ 2 ^ e)
    (hce : c + e ≤ κ) :
    H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
  set R := pCoreOf 2 H with hR
  have hRT : R ≤ T := pCoreOf_le_of_sylow hT hTH
  set U : Subgroup V := Fx ρ (Wcl Ω c R) with hU
  have hHst : ∀ g ∈ H, g ∈ stabV ρ U := fun g hg =>
    mem_stabV_Fx_of_conj (conjSubgroup_Wcl_eq hΩ c (conjSubgroup_pCoreOf hg))
  set Y : Subgroup G := H ⊓ cenV ρ U with hY
  have hYH : Y ≤ H := inf_le_left
  have hYn : ∀ g ∈ H, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    refine ⟨H.mul_mem (H.mul_mem hg (hYH hy)) (H.inv_mem hg), fun u hu => ?_⟩
    have hu' : ρ g⁻¹ u ∈ U := (hHst g⁻¹ (H.inv_mem hg) u).2 hu
    have hy' : ρ y (ρ g⁻¹ u) = ρ g⁻¹ u := hy.2 _ hu'
    calc ρ (g * y * g⁻¹) u = ρ g (ρ y (ρ g⁻¹ u)) := by
          simp only [map_mul, MulAut.mul_apply]
      _ = ρ g (ρ g⁻¹ u) := by rw [hy']
      _ = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hWjY : Wcl Ω j T ≤ Y := by
    refine sSup_le fun B hB => ?_
    obtain ⟨hBT, A, hAΩ, hBA, hmA⟩ := hB
    have hBH : B ≤ H := hBT.trans hTH
    have hB2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb => (hel A hAΩ).1 b (hBA hb)
    have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      (hel A hAΩ).2 a (hBA ha) b (hBA hb)
    have hDA : B ⊓ R ≤ A := inf_le_left.trans hBA
    have hmD : mQuot A (B ⊓ R) ≤ c := by
      have h1 := mQuot_add (inf_le_left : B ⊓ R ≤ B) hBA
      have h2 : mQuot B (B ⊓ R) ≤ iRank H := mQuot_inf_pCoreOf_le hBH hB2 hBc
      omega
    have hFx : Fx ρ (B ⊓ R) = Fx ρ A := hfix A hAΩ _ hDA (hmD.trans hcκ)
    have hDW : B ⊓ R ≤ Wcl Ω c R := le_Wcl inf_le_right ⟨A, hAΩ, hDA, hmD⟩
    have hUB : U ≤ Fx ρ B := (Fx_anti hDW).trans (hFx.le.trans (Fx_anti hBA))
    exact fun b hb => ⟨hBH hb, fun u hu => (mem_Fx.1 (hUB hu)) b hb⟩
  have hYT : ¬ (Y ⊓ T ≤ R) := fun hle => hnot ((le_inf hWjY (Wcl_le_self Ω j T)).trans hle)
  have hYV : Y ≤ cenV ρ (Fx ρ (Wcl Ω c T)) := fun y hy u hu =>
    hy.2 u (Fx_anti (Wcl_mono_base c hRT) hu)
  rcases hcase with hspl | ⟨X₀, hX₀, hidx⟩
  ·
    have hg := good_of_split hT hTH hF hspl hYH hYn hYT
    refine hg.trans (sup_le (normalizer_le_stabV hΩ c) (sup_le ?_ (hYV.trans (cenV_le_stabV ρ _))))
    exact Subgroup.le_normalizer.trans (normalizer_le_stabV hΩ c)
  ·
    have hXY : X₀ ≤ Y := hX₀ Y hYH hYn (fStarPre_le hT.isPGroup hTH hF hYH hYn hYT)
    have hWY : Wcl Ω c T ≤ Y := by
      refine sSup_le fun D hD => ?_
      obtain ⟨hDT, A, hAΩ, hDA, hmA⟩ := hD
      have hDp : IsPGroup 2 D := hT.isPGroup.to_le hDT
      have hm1 : mQuot D (D ⊓ Y) ≤ e := by
        have h1 := relIndex_eq_two_pow hDp (D ⊓ Y)
        rw [Subgroup.inf_relIndex_left] at h1
        have h2 : Y.relIndex D ≤ Y.relIndex T :=
          Subgroup.relIndex_le_of_le_right hDT (relIndex_ne_zero' T Y)
        have h3 : Y.relIndex T ≤ X₀.relIndex T :=
          Subgroup.relIndex_le_of_le_left hXY (relIndex_ne_zero' T X₀)
        have h4 : 2 ^ mQuot D (D ⊓ Y) ≤ 2 ^ e := h1 ▸ (h2.trans (h3.trans hidx))
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
      have hEA : D ⊓ Y ≤ A := inf_le_left.trans hDA
      have hmE : mQuot A (D ⊓ Y) ≤ κ := by
        have := mQuot_add (inf_le_left : D ⊓ Y ≤ D) hDA
        omega
      have hFx : Fx ρ (D ⊓ Y) = Fx ρ A := hfix A hAΩ _ hEA hmE
      have hUE : U ≤ Fx ρ (D ⊓ Y) := fun u hu => mem_Fx.2 fun x hx => hx.2.2 u hu
      have hUD : U ≤ Fx ρ D := (hUE.trans hFx.le).trans (Fx_anti hDA)
      exact fun d hd => ⟨hTH (hDT hd), fun u hu => (mem_Fx.1 (hUD hu)) d hd⟩
    have hFxeq : Fx ρ (Wcl Ω c T) = U := by
      refine le_antisymm (Fx_anti (Wcl_mono_base c hRT)) ?_
      intro u hu
      exact mem_Fx.2 fun w hw => (hWY hw).2 u hu
    rw [hFxeq]
    exact fun g hg => hHst g hg

theorem fix_of_level (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (h2 : ∀ A ∈ Ω, ∀ a ∈ A, a ^ 2 = 1) (hne : ∀ A ∈ Ω, A ≠ ⊥) (hT : IsSylowIn 2 T ⊤)
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ Ω) {c : ℕ} (hall : ∀ g : G, g ∈ stabV ρ (Fx ρ (Wcl Ω c T)))
    {L : Subgroup G} (hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L) :
    ∀ v ∈ Fx ρ T, ∀ l ∈ L, ρ l v = v := by
  obtain ⟨A₁, hA₁Ω, hA₁T⟩ := exists_mem_le_of_sylow hT hΩ h2 hA₀
  have hW : Wcl Ω c T ≠ ⊥ := by
    intro hbot
    have hle : A₁ ≤ Wcl Ω c T :=
      le_Wcl hA₁T ⟨A₁, hA₁Ω, le_rfl, by simp [mQuot_self]⟩
    rw [hbot] at hle
    exact hne A₁ hA₁Ω (le_bot_iff.1 hle)
  have hcomm : ⁅L, Wcl Ω c T⁆ = L := hL _ (Wcl_le_self Ω c T) hW
  have hcen : ⁅L, Wcl Ω c T⁆ ≤ cenV ρ (Fx ρ (Wcl Ω c T)) := by
    rw [Subgroup.commutator_le]
    intro l _ w hw u hu
    have hw' : ρ w⁻¹ u = u := mem_Fx.1 hu w⁻¹ ((Wcl Ω c T).inv_mem hw)
    have hu' : ρ l⁻¹ u ∈ Fx ρ (Wcl Ω c T) := (hall l⁻¹ u).2 hu
    have hw'' : ρ w (ρ l⁻¹ u) = ρ l⁻¹ u := mem_Fx.1 hu' w hw
    calc ρ ⁅l, w⁆ u = ρ l (ρ w (ρ l⁻¹ (ρ w⁻¹ u))) := by
          simp only [commutatorElement_def, map_mul, MulAut.mul_apply]
      _ = ρ l (ρ w (ρ l⁻¹ u)) := by rw [hw']
      _ = ρ l (ρ l⁻¹ u) := by rw [hw'']
      _ = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [hcomm] at hcen
  intro v hv l hl
  exact hcen hl v (Fx_anti (Wcl_le_self Ω c T) hv)

end Levels

open Classical in
theorem card_filter_bad_le (Q : ℕ → Prop) (i n : ℕ) :
    ((Finset.range n).filter (fun c => ¬ Q c ∧ ∀ j, j + i ≤ c → Q j)).card ≤ i := by
  set S := (Finset.range n).filter (fun c => ¬ Q c ∧ ∀ j, j + i ≤ c → Q j) with hS
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h]
    simp
  · have hmS : S.min' h ∈ S := S.min'_mem h
    have hsub : S ⊆ Finset.Ico (S.min' h) (S.min' h + i) := by
      intro c hc
      rw [Finset.mem_Ico]
      refine ⟨S.min'_le c hc, ?_⟩
      by_contra hlt
      push Not at hlt
      exact (Finset.mem_filter.1 hmS).2.1 ((Finset.mem_filter.1 hc).2.2 _ hlt)
    calc S.card ≤ (Finset.Ico (S.min' h) (S.min' h + i)).card := Finset.card_le_card hsub
      _ = i := by simp

end CFSG.Quasithin.RonanE42.Gen
