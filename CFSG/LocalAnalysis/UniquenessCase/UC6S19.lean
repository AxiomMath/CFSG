module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S37

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

theorem frattini_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H L P : Subgroup G} (hLH : L ≤ H) (hLn : H ≤ normalizer (L : Set G))
    (hP : IsSylowOf p P L) : H = L ⊔ (H ⊓ normalizer (P : Set G)) := by
  refine le_antisymm (fun h hh => ?_) (sup_le hLH inf_le_left)
  set P' : Subgroup G := P.map (MulAut.conj h).toMonoidHom with hP'
  have hP'L : P' ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    have := (mem_normalizer_iff.1 (hLn hh) x).1 (hP.le hx)
    simpa using this
  have hP'card : Nat.card P' = Nat.card P := Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hP'syl : IsSylowOf p P' L :=
    isSylowOf_of_card hP'L (by rw [hP'card, hP.card_eq])
  obtain ⟨k, hkL, hk⟩ := hP.exists_mem_conj hP'syl
  have hkh : k⁻¹ * h ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : h * x * h⁻¹ ∈ P' := ⟨x, hx, by simp⟩
      have h2 := (hk (h * x * h⁻¹)).1 h1
      simpa [mul_assoc] using h2
    · intro hx
      have h1 : k⁻¹ * (h * x * h⁻¹) * k ∈ P := by
        have : k⁻¹ * h * x * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * x * h⁻¹) * k := by group
        rw [← this]; exact hx
      have h2 : h * x * h⁻¹ ∈ P' := (hk _).2 h1
      obtain ⟨y, hy, hyx⟩ := h2
      have : y = x := by
        have h3 : h * y * h⁻¹ = h * x * h⁻¹ := by simpa using hyx
        simpa using h3
      exact this ▸ hy
  have hkhH : k⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hLH hkL)) hh
  have : h = k * (k⁻¹ * h) := by group
  rw [this]
  exact mul_mem_sup hkL ⟨hkhH, hkh⟩

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem H_le_normalizer_L : m.H ≤ normalizer (m.L : Set G) := by
  intro h hh
  have hD : ∀ x ∈ inftyOf m.H, h * x * h⁻¹ ∈ inftyOf m.H := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(⟨h, hh⟩ : ↥m.H) * x * (⟨h, hh⟩ : ↥m.H)⁻¹, ?_, by simp⟩
    exact (derivedSeries_normal ↥m.H (Nat.card m.H)).conj_mem x hx ⟨h, hh⟩
  have hgen : ∀ g ∈ m.H, ∀ x ∈ m.L, g * x * g⁻¹ ∈ m.L := by
    intro g hg x hx
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ m.L) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨hy, k, hk⟩
      refine subset_closure ⟨?_, k, ?_⟩
      ·
        have : ∀ z ∈ inftyOf m.H, g * z * g⁻¹ ∈ inftyOf m.H := by
          rintro _ ⟨x', hx', rfl⟩
          refine ⟨(⟨g, hg⟩ : ↥m.H) * x' * (⟨g, hg⟩ : ↥m.H)⁻¹, ?_, by simp⟩
          exact (derivedSeries_normal ↥m.H (Nat.card m.H)).conj_mem x' hx' ⟨g, hg⟩
        exact this y hy
      · have hord : orderOf (g * y * g⁻¹) = orderOf y := by
          simpa [MulAut.conj_apply] using
            orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
        rw [hord]; exact hk
    · simp
    · intro a b _ _ ha hb
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact m.L.mul_mem ha hb
    · intro a _ ha
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact m.L.inv_mem ha
  rw [mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hgen h hh x hx, fun hx => by
    have := hgen h⁻¹ (m.H.inv_mem hh) _ hx
    simpa [mul_assoc] using this⟩

theorem E_inf_L_ne_bot (h620 : m.C620) : m.E ⊓ m.L ≠ ⊥ := by
  intro hbot
  have hEA : m.E ≤ m.A := m.E_le_A
  have hdisj : m.E ⊓ (m.A ⊓ m.L) = ⊥ := by
    rw [← inf_assoc, inf_of_le_left hEA]; exact hbot
  have hcomm : ∀ x ∈ m.E, ∀ y ∈ m.A ⊓ m.L, x * y = y * x := fun x hx y hy =>
    (m.isElemAbelian_A.1.is_comm.comm ⟨x, hEA hx⟩ ⟨y, hy.1⟩ |> congrArg Subtype.val)
  have hcard := card_sup_of_commute_of_disjoint hcomm hdisj
  rw [m.d.E_card, m.card_A_inf_L h620] at hcard
  have hle : Nat.card ↥(m.E ⊔ (m.A ⊓ m.L)) ≤ Nat.card ↥m.A :=
    Subgroup.card_le_of_le (sup_le hEA inf_le_left)
  rw [hcard, m.card_A] at hle
  have hr := m.hr
  have h1 : m.r ^ 2 * m.r ^ 2 = m.r ^ 4 := by ring
  rw [h1] at hle
  have := Nat.pow_le_pow_iff_right hr.one_lt |>.1 hle
  omega

theorem six19 (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620) : m.C619 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hRH : m.R ≤ m.H := m.hZ.R_le_centralizer h69
  have hRsyl : IsSylowOf m.r m.R m.H := m.hZ.R_sylow hRH
  have hLH : m.L ≤ m.H := m.L_le_H
  have hLn := m.H_le_normalizer_L
  have hP : IsSylowOf m.r (m.R ⊓ m.L) m.L := hRsyl.inf_of_le_normalizer hLH hLn
  have hfr := frattini_of_isSylowOf hLH hLn hP
  have hXS : m.E ⊓ m.L ≤ m.R ⊓ m.L := inf_le_inf_right _ m.E_le_R
  have hNM : normalizer ((m.R ⊓ m.L : Subgroup G) : Set G) ≤ m.M :=
    m.d.normalizer_le_of_le_pGroup m.hC inf_le_left (m.E_inf_L_ne_bot h620) hXS
      (m.d.sylow.isPGroup.to_inf_left)
  refine le_antisymm (fun h hh => ?_) (sup_le hLH inf_le_left)
  rw [hfr] at hh
  have hle : m.H ⊓ normalizer ((m.R ⊓ m.L : Subgroup G) : Set G) ≤ m.H ⊓ m.M :=
    fun x hx => ⟨hx.1, hNM hx.2⟩
  exact (sup_le_sup_left hle m.L) hh

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
