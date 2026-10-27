module

public import CFSG.Timmesfeld.Transvection.OddUnitary
public import CFSG.Timmesfeld.Transvection.OddBC2Statement

import CFSG.Timmesfeld.Transvection.GenerateMax
import CFSG.Timmesfeld.Transvection.OddPairsGenerate
import CFSG.Timmesfeld.Transvection.OddPairsCone
import CFSG.Timmesfeld.Transvection.OddPairsBC2
import CFSG.Timmesfeld.Transvection.OddPairsFrame
import CFSG.Timmesfeld.Transvection.OddSpExclusion
import CFSG.Timmesfeld.Transvection.OddResidueBlock
import CFSG.Timmesfeld.Transvection.MaxFrame
import CFSG.LieType.CurtisTits.Unitary

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres

private theorem exists_frame_of_eq {F : Type} [Field F] {σ : F ≃+* F} {H : Type} [Group H]
    {Δ : Set (Subgroup H)} {s r : ℕ} (h : s = r) {P Q : Fin r → Subgroup H}
    (hF : IsMaxFrame Δ P Q) {k : Fin r} (hns : ¬ IsSmallFrame Δ P Q k)
    {R : SURelations r σ H} (hR : R.HasFrameImages Δ P Q) (k' : Fin s) (hk : k'.val = k.val) :
    ∃ (P' Q' : Fin s → Subgroup H) (R' : SURelations s σ H), IsMaxFrame Δ P' Q' ∧
      ¬ IsSmallFrame Δ P' Q' k' ∧ R'.HasFrameImages Δ P' Q' := by
  subst h
  obtain rfl : k' = k := Fin.ext hk
  exact ⟨P, Q, R, hF, hns, hR⟩

private theorem ker_eq_center_and_mem_iff {H : Type} [Group H] {Δ : Set (Subgroup H)}
    (h : TransvectionHyp H Δ) {f : ℕ} (hf : 1 ≤ f) {r : ℕ} (h2 : 2 ≤ 2 * r + 1)
    {A : Subgroup H} (hA : A ∈ Δ)
    {Φ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (2 * r + 1) →* H}
    (hsurj : Function.Surjective Φ) (hker : Φ.ker ≤ Subgroup.center _)
    (hZ : Subgroup.center H = (Subgroup.center _).map Φ)
    (hX₀ : ((Unitary.rootDatum (card_galoisField_two_mul hf)
      (2 * r + 1)).rootGroup (unitaryLongRoot (2 * r + 1) h2)).map Φ = A) :
    Φ.ker = Subgroup.center _ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
      ∃ g, X = (conjSub ((Unitary.rootDatum
        (card_galoisField_two_mul hf) (2 * r + 1)).rootGroup
          (unitaryLongRoot (2 * r + 1) h2)) g).map Φ := by
  refine ⟨le_antisymm hker ((Subgroup.map_eq_bot_iff _).1 (hZ.symm.trans h.center)),
    fun X => ⟨fun hX => ?_, ?_⟩⟩
  · have hA' : ((Unitary.rootDatum (card_galoisField_two_mul hf)
        (2 * r + 1)).rootGroup (unitaryLongRoot (2 * r + 1) h2)).map Φ ∈ Δ := by
      simpa only [hX₀] using hA
    obtain ⟨y, rfl⟩ := h.cls.root.exists_conjSub_eq hA' hX
    obtain ⟨g, rfl⟩ := hsurj y
    exact ⟨g, ModelRank.conjSub_map _ _ _⟩
  · rintro ⟨g, rfl⟩
    rw [← ModelRank.conjSub_map, hX₀]
    exact h.cls.root.conjSub_mem hA _


theorem oddUnitaryStatement_of_bc2 (hBC : OddFrameBC2Statement) : OddUnitaryStatement := by
  intro H _ Δ h hML hq r hr P Q k hF hns
  obtain ⟨hF₁, hns₁⟩ := hF.exists_not_small_last hns
  obtain ⟨f, hf, hcard, R₁, hR₁⟩ :=
    hF₁.exists_suRelations_of_not_isSmallFrame h hML hq hr hns₁
  have hf1 : 1 ≤ f := by omega
  have hFn : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    card_galoisField_two_mul hf1
  obtain ⟨P', Q', R, hF', hns', hR⟩ := exists_frame_of_eq (s := 2 * r / 2) (by omega)
    hF₁ hns₁ hR₁ (cLastIdx r hr) (show 2 * r / 2 - 1 = r - 1 by omega)
  have hm : 4 ≤ 2 * r := by omega
  obtain ⟨θ₀, hθr₀, hθk₀, hθodd₀, hθc₀, hθmem₀⟩ :=
    hF'.exists_su3_residue_last (even_two_mul r) hm h hML hq hns' hFn hcard R hR
  have htr : ∀ X ∈ frameResidue Δ P' Q' (cLastIdx r hr),
      ∃ g ∈ residueGroup Δ P' Q' (cLastIdx r hr), conjSub (P' (cLastIdx r hr)) g = X :=
    fun X hX => hF'.exists_conjSub_eq_of_mem_frameResidue h hML hq _ hX
  have htop₀ := hR.range_toHom_sup_residueGroup_eq_top hFn (even_two_mul r) hm h hML hq
    hF'.toIsFrame htr
  obtain ⟨θ, hθr, hθc, hpos⟩ := hBC H Δ h hML hq (GaloisField 2 (2 * f)) f hFn hf hcard
    r hr hm P' Q' hF' hns' R hR htop₀ htr θ₀ hθr₀ hθk₀ hθodd₀ hθc₀ hθmem₀
    (hR.oddFrameCompatible_toHom hFn hr hm hθr₀ hθc₀)
  have hd := hR.oddFrameCompatible_toHom hFn hr hm hθr hθc
  have hgen := closure_range_oddFrameMap_eq_top hFn hr (R.toHom hFn (even_two_mul r) hm) θ
    (by rw [hθr]; exact htop₀) (R.map_rankOne_last_le_range hFn (even_two_mul r) hm hθc)
  obtain ⟨Φ, hΦ, -, hsurj, hker, -, hZ, -⟩ := exists_surjective_of_frame
    (CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0}
      (statedLieAdmissible_psu_odd hr hf1) hFn)
    (leviConePresented_unitary hFn (by omega))
    (oddFrameMap hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    (hd.extendsToHom_cone_of_pos hpos)
    (extendsToHom_rankOne_oddFrameMap hFn hr _ θ)
    hgen
    (hR.exists_oddFrameMap_toHom_ne_one hFn hr hm hd (h.cls.root.ne_bot _ (hF'.memP _)))
  exact ⟨f, hf1, hcard, Φ, hsurj, ker_eq_center_and_mem_iff h hf1 (by omega)
    (hF'.memP (cLastIdx r hr)) hsurj hker hZ
    (hR.map_rootGroup_unitaryLongRoot_eq hFn hr hm hd (hΦ _) (by omega))⟩

end CFSG.Timmesfeld.Transvection
