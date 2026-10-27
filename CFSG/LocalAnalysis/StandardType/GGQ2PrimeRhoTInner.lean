module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInnerForm
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate3600

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (autT T46_le_autT)

theorem rhoT_mem_T46_iff
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m : Fin 7} (h : CoordCtx B Bs x L A κ m) {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {b : G}
    (hb : b ∈ Bs) : ρ ⟨b, h.setting.Bs_norm hb⟩ ∈ T46 ↔ κ m ⟨b, hb⟩ = 1 := by
  classical
  obtain ⟨c₀, hc₀B, hc₀⟩ := rhoTInner_exists_not_mem h hρ
  obtain ⟨-, -, -, hLc, -, -, -, -⟩ := ggThmIHyp_unpack h.setting.hyp
  have hBN : Bs ≤ normalizer (L : Set G) := h.setting.Bs_norm
  have hW : WeylCoords Bs A x κ m := h.coords
  obtain ⟨Ê, -⟩ := exists_permEquiv_of_ggWeylOfType_A h.weyl5
  have hALcard : Nat.card (ggAutomizer L Bs) = 720 := by
    rw [← Nat.card_congr Ê.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hfixx : ∀ φ ∈ ggAutomizer L Bs, φ ⟨x, hW.x_mem⟩ = ⟨x, hW.x_mem⟩ := fun φ hφ =>
    ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hW.x_mem⟩) hLc.1 hφ
  have hN : (T46.subgroupOf autT).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer T46_le_autT).2 le_rfl
  let R' : Bs →* autT :=
    (ρ.comp (inclusion hBN)).codRestrict autT fun d => hρ.mem_autT (inclusion hBN d)
  let ν : Bs →* autT ⧸ T46.subgroupOf autT :=
    (QuotientGroup.mk' (T46.subgroupOf autT)).comp R'
  have hν : ∀ d : Bs, ν d = 1 ↔ ρ (inclusion hBN d) ∈ T46 := fun d =>
    (QuotientGroup.eq_one_iff (R' d)).trans Iff.rfl
  have hinv : ∀ φ ∈ ggAutomizer L Bs, ∀ d : Bs, ν (φ d) = ν d := fun φ hφ d => by
    obtain ⟨q, hq, hqc⟩ := rhoTInner_exists_conj_of_mem_automizer hBN hρ hφ
    have hq1 : QuotientGroup.mk' (T46.subgroupOf autT) ⟨q, T46_le_autT hq⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 hq
    have hR' : R' (φ d) = ⟨q, T46_le_autT hq⟩ * R' d * ⟨q, T46_le_autT hq⟩⁻¹ :=
      Subtype.ext (hqc d).symm
    simp only [ν, MonoidHom.comp_apply]
    rw [hR', map_mul, map_mul, map_inv, hq1, one_mul, inv_one, mul_one]
  have hne : ∃ d : Bs, ν d ≠ 1 := ⟨⟨c₀, hc₀B⟩, fun h1 => hc₀ ((hν _).1 h1)⟩
  have key := ker_eq_of_invariant hW h.AL_le hfixx hALcard ν hinv hne
  exact (hν ⟨b, hb⟩).symm.trans (key ⟨b, hb⟩)

end CFSG.GGQ2Prime
