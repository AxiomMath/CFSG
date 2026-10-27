module

public import CFSG.Quasithin.Background.RonanE42Cor17
public import CFSG.Quasithin.Background.RonanE42AddR

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
open CFSG.Quasithin.RonanE42.Gen

variable {G V : Type} [Group G] [Finite G] [CommGroup V]

section Levels

variable {ρ : G →* MulAut V} {T : Subgroup G} {Ω : Set (Subgroup G)}

theorem le_stabV_of_good (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) {r : ℕ}
    (hrank : ∀ B : Subgroup G, B ≤ H → (∀ b ∈ B, b ^ 2 = 1) →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → mQuot B (B ⊓ pCoreOf 2 H) ≤ r)
    (hgood : ∀ Y : Subgroup G, Y ≤ H → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 H) → H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    {j c : ℕ} (hjc : j + r ≤ c) (hcκ : c ≤ κ) (hnot : ¬ Wcl Ω j T ≤ pCoreOf 2 H) :
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
      have h2 : mQuot B (B ⊓ R) ≤ r := hrank B hBH hB2 hBc
      omega
    have hFx : Fx ρ (B ⊓ R) = Fx ρ A := hfix A hAΩ _ hDA (hmD.trans hcκ)
    have hDW : B ⊓ R ≤ Wcl Ω c R := le_Wcl inf_le_right ⟨A, hAΩ, hDA, hmD⟩
    have hUB : U ≤ Fx ρ B := (Fx_anti hDW).trans (hFx.le.trans (Fx_anti hBA))
    exact fun b hb => ⟨hBH hb, fun u hu => (mem_Fx.1 (hUB hu)) b hb⟩
  have hYT : ¬ (Y ⊓ T ≤ R) := fun hle => hnot ((le_inf hWjY (Wcl_le_self Ω j T)).trans hle)
  have hYV : Y ≤ cenV ρ (Fx ρ (Wcl Ω c T)) := fun y hy u hu =>
    hy.2 u (Fx_anti (Wcl_mono_base c hRT) hu)
  refine (hgood Y hYH hYn hYT).trans
    (sup_le (normalizer_le_stabV hΩ c) (sup_le ?_ (hYV.trans (cenV_le_stabV ρ _))))
  exact Subgroup.le_normalizer.trans (normalizer_le_stabV hΩ c)

end Levels

theorem pCoreOf_xt_le {T H : Subgroup G} (hTH : T ≤ H)
    (hF : CFSG.IsQuasisimple ↥(fStarMod H) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p) :
    pCoreOf 2 (xt T H) ≤ pCoreOf 2 H := by
  classical
  have hXH : xt T H ≤ H := xt_le hTH
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2)
  set ι : ↥(xt T H) →* ↥H := Subgroup.inclusion hXH
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set φ : ↥(xt T H) →* ↥H ⧸ CFSG.pCore 2 ↥H := π.comp ι with hφ
  have hO2 : CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_quotient_eq_bot (G := ↥H) 2
  have h1 : CFSG.pCore 2 ↥(xt T H) ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    refine eq_bot_of_normalized hO2 hF ((CFSG.pCore_isPGroup (p := 2) (G := _)).map φ) ?_
    intro f hf r hr
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) f
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hr
    have hhX : (h : G) ∈ xt T H :=
      le_sup_left (a := fStarPre H) (Subgroup.mem_map.mpr ⟨h, Subgroup.mem_comap.mpr hf, rfl⟩)
    let x : ↥(xt T H) := ⟨h, hhX⟩
    have hx : ι x = h := Subtype.ext rfl
    refine Subgroup.mem_map.mpr
      ⟨x * y * x⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥(xt T H))).conj_mem y hy x, ?_⟩
    rw [map_mul, map_mul, map_inv]
    simp only [hφ, MonoidHom.comp_apply, hx]
    rfl
  rintro _ ⟨y, hy, rfl⟩
  have hk : φ y = 1 := h1 hy
  have hmem : ι y ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).1 hk
  exact Subgroup.mem_map.mpr ⟨ι y, hmem, rfl⟩

theorem pCoreOf_le_fStarPre (H : Subgroup G) : pCoreOf 2 H ≤ fStarPre H := by
  rintro _ ⟨y, hy, rfl⟩
  refine Subgroup.mem_map.mpr ⟨y, Subgroup.mem_comap.mpr ?_, rfl⟩
  have : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y = 1 := (QuotientGroup.eq_one_iff _).2 hy
  rw [this]
  exact Subgroup.one_mem _

theorem pCoreOf_bk_le {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hidx : (T ⊓ fStarPre H).relIndex T = 2)
    (hns : ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)) :
    pCoreOf 2 (bk T H) ≤ T ⊓ fStarPre H := by
  set P := pCoreOf 2 (bk T H) with hP
  set S := T ⊓ fStarPre H with hS
  have hPT : P ≤ T := pCoreOf_le_of_sylow hT (le_bk hTH)
  have hSP : S ≤ P := inf_le_pCoreOf_bk hT hTH
  have hmul := Subgroup.relIndex_mul_relIndex S P T hSP hPT
  rw [hidx] at hmul
  rcases (Nat.prime_two.eq_one_or_self_of_dvd _ (Dvd.intro _ hmul)) with h | h
  · exact Subgroup.relIndex_eq_one.1 h
  · exfalso
    rw [h] at hmul
    have h1 : P.relIndex T = 1 := by omega
    have hTP : T ≤ P := Subgroup.relIndex_eq_one.1 h1
    have hPeq : P = T := le_antisymm hPT hTP
    apply hns
    have hBN : bk T H ≤ Subgroup.normalizer (T : Set G) := by
      intro b hb
      have := conjSubgroup_pCoreOf (H := bk T H) hb
      rw [← hP, hPeq] at this
      exact conjSubgroup_eq_iff_mem_normalizer.1 this
    refine (le_sup_bk hT hTH).trans (sup_le ?_ ?_)
    · exact le_sup_left.trans Subgroup.le_normalizer
    · intro b hb
      have hbH : b ∈ H := hb.1
      have hbT : b ∈ Subgroup.normalizer (T : Set G) := hBN hb
      have hbX : b ∈ Subgroup.normalizer ((fStarPre H : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        refine ⟨fun hz => fStarPre_conj_mem H b hbH z hz, fun hz => ?_⟩
        have := fStarPre_conj_mem H b⁻¹ (H.inv_mem hbH) _ hz
        simpa [mul_assoc] using this
      have hX : conjSubgroup (fStarPre H) b = fStarPre H :=
        conjSubgroup_eq_iff_mem_normalizer.2 hbX
      have hT' : conjSubgroup T b = T := conjSubgroup_eq_iff_mem_normalizer.2 hbT
      refine conjSubgroup_eq_iff_mem_normalizer.1 ?_
      exact (Subgroup.map_sup _ _ _).trans (congrArg₂ (· ⊔ ·) hX hT')

end CFSG.Quasithin.RonanE42.Gen
