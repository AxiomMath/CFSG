module

public import CFSG.Quasithin.Vol2.Ch10SecD12S
public import CFSG.Quasithin.Vol2.Ch10SecB3Five
public import CFSG.Quasithin.Vol2.Ch10SecD12R
public import CFSG.Quasithin.Vol2.Ch10SecQ9G10

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] {T L I : Subgroup G}

theorem not_le_centralizer_of_natural {W : Subgroup G} [IsMulCommutative ↥W]
    (hnat : BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ 3 1) :
    ¬ W ≤ Subgroup.centralizer (L : Set G) := by
  intro hWL
  obtain ⟨D⟩ := hnat.toL3Coord
  have h1 : ∀ γ : L3.Γ, D.rho γ = 1 := by
    intro γ
    obtain ⟨⟨l, hlN⟩, hlL, hlσ⟩ := D.rho_mem γ
    rw [← hlσ, conjAct_eq_one_iff']
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hWL hx) l (Subgroup.mem_subgroupOf.mp hlL)).symm
  let γ0 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
  have h2 : γ0 = 1 := D.rho_injective ((h1 _).trans (map_one _).symm)
  have h3 := congrArg (fun g : L3.Γ => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1) h2
  revert h3
  decide

theorem inf_centralizer_eq_bot_of_case5 [Finite G] (hyp : Hyp10 G T L I)
    (h5 : Case10_1_1Five T L I) :
    fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨-, s, -, hsL, W, hWV1, hLW, hsup, hinf, ⟨hWc, hWnat⟩, -⟩ := h5
  have hirr : IrrG L W := by
    obtain ⟨K, _, _, -, π, hD⟩ := hWnat
    exact irrG_of_isIrrSec (B5.isIrr_of_realizes (by norm_num) hD).2
  have hirr' := irrG_conjugate hirr hsL
  have hLW' := le_normalizer_conjugate_of' hsL hLW
  have hWsV1 : CFSG.conjugate W s ≤ fsuUL T L I := hsup ▸ le_sup_right
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hc : ∀ a ∈ W, ∀ b ∈ CFSG.conjugate W s, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV (hV1V (hWV1 ha)) (hV1V (hWsV1 hb))
  have hfix : ∀ X : Subgroup G, IrrG L X → L ≤ Subgroup.normalizer (X : Set G) →
      ¬ X ≤ Subgroup.centralizer (L : Set G) → X ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    intro X hX hLX hXL
    rcases hX.2 _ inf_le_left (fun l hl => mem_normalizer_inf' (hLX hl)
      (mem_normalizer_centralizer' (Subgroup.le_normalizer hl))) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hXL
  have hW0 := hfix W hirr hLW (not_le_centralizer_of_natural hWnat)
  have hWs0 := hfix _ hirr' hLW' (fun h => not_le_centralizer_of_natural hWnat
    ((SecB.le_centralizer_conjugate_iff hsL).mp h))
  rw [eq_bot_iff]
  rintro x ⟨hxV1, hxL⟩
  rw [← hsup] at hxV1
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hxV1
  have hab : ∀ l ∈ L, l * a * l⁻¹ = a := by
    intro l hl
    have h1 : l * (a * b) * l⁻¹ = a * b := by
      rw [Subgroup.mem_centralizer_iff.mp hxL l hl, mul_inv_cancel_right]
    have hla : l * a * l⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW hl) a).mp ha
    have hlb : l * b * l⁻¹ ∈ CFSG.conjugate W s :=
      (Subgroup.mem_normalizer_iff.mp (hLW' hl) b).mp hb
    have h2 : a⁻¹ * (l * a * l⁻¹) ∈ W ⊓ CFSG.conjugate W s := by
      refine ⟨W.mul_mem (W.inv_mem ha) hla, ?_⟩
      have e1 : a⁻¹ * (l * a * l⁻¹) = b * (l * b * l⁻¹)⁻¹ := by
        have e2 : l * a * l⁻¹ * (l * b * l⁻¹) = a * b := by rw [← h1]; group
        calc a⁻¹ * (l * a * l⁻¹) = a⁻¹ * (l * a * l⁻¹ * (l * b * l⁻¹)) * (l * b * l⁻¹)⁻¹ := by
              group
          _ = b * (l * b * l⁻¹)⁻¹ := by rw [e2]; group
      rw [e1]
      exact (CFSG.conjugate W s).mul_mem hb ((CFSG.conjugate W s).inv_mem hlb)
    rw [hinf, Subgroup.mem_bot] at h2
    calc l * a * l⁻¹ = a * (a⁻¹ * (l * a * l⁻¹)) := by group
      _ = a := by rw [h2, mul_one]
  have haC : a ∈ W ⊓ Subgroup.centralizer (L : Set G) := ⟨ha, Subgroup.mem_centralizer_iff.mpr
    fun l hl => by
      calc l * a = l * a * l⁻¹ * l := by group
        _ = a * l := by rw [hab l hl]⟩
  rw [hW0, Subgroup.mem_bot] at haC
  subst haC
  rw [one_mul] at hxL ⊢
  have hbC : b ∈ CFSG.conjugate W s ⊓ Subgroup.centralizer (L : Set G) := ⟨hb, hxL⟩
  rw [hWs0] at hbC
  exact hbC

theorem cV1_eq_bot_of_case5 [Finite G] (hyp : Hyp10 G T L I) (h5 : Case10_1_1Five T L I) :
    cV1 T L I = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  have h1 : (x : G) ∈ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨x.2, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (SecA.le_fsuL0 T L)) hx⟩
  rw [inf_centralizer_eq_bot_of_case5 hyp h5, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem card_fsuUL_of_case5 [Finite G] (hyp : Hyp10 G T L I) (h5 : Case10_1_1Five T L I) :
    Nat.card (fsuUL T L I) = 64 := by
  obtain ⟨-, s, -, -, W, hWV1, -, hsup, hinf, ⟨hWc, hnat⟩, -⟩ := h5
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hWsV1 : CFSG.conjugate W s ≤ fsuUL T L I := hsup ▸ le_sup_right
  have hW8 : Nat.card W = 8 := by
    obtain ⟨K, _, _, hK, hreal⟩ := hnat
    have := SecD.card_of_realizes_nat hreal
    rw [Subgroup.card_top, hK, Fintype.card_fin, Subgroup.card_bot] at this
    simpa using this
  have hWs8 : Nat.card ↥(CFSG.conjugate W s) = 8 := by
    rw [← hW8]
    exact Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective
  rw [← hsup, SecD.card_sup_of_comm (fun x hx y hy => B2F.isElemAbelian_comm hV (hV1V (hWV1 hx))
    (hV1V (hWsV1 hy))) hinf, hW8, hWs8]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
