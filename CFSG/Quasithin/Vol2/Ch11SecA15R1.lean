module

public import CFSG.Quasithin.Vol2.Ch11SecA15MS3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem T_le_normalizer_L1 (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) :
    T ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
  T_le_normalizer_lOf h.normal (IsVi.le_normalizer hU)

theorem pCoreOf_lOf_le_ROf (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) :
    pCoreOf 2 (LOf L V₁) ≤ ROf T L V₁ :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      ((T_le_normalizer_L1 h hU).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem commutator_lOf_ROf_mem (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) {l r : G}
    (hl : l ∈ LOf L V₁) (hr : r ∈ ROf T L V₁) : r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (LOf L V₁) := by
  have hrL : r ∈ Subgroup.normalizer (LOf L V₁ : Set G) := T_le_normalizer_L1 h hU (ROf_le_T h hr)
  have hlR : l ∈ Subgroup.normalizer (ROf T L V₁ : Set G) :=
    (le_sup_left.trans lOf_sup_le_normalizer_ROf) hl
  have h1 : r * l * r⁻¹ * l⁻¹ ∈ LOf L V₁ :=
    (LOf L V₁).mul_mem ((Subgroup.mem_normalizer_iff.mp hrL l).mp hl) ((LOf L V₁).inv_mem hl)
  have h2 : r * l * r⁻¹ * l⁻¹ ∈ ROf T L V₁ := by
    have : l * r⁻¹ * l⁻¹ ∈ ROf T L V₁ :=
      (Subgroup.mem_normalizer_iff.mp hlR _).mp ((ROf T L V₁).inv_mem hr)
    simpa [mul_assoc] using (ROf T L V₁).mul_mem hr this
  have hle : LOf L V₁ ⊓ ROf T L V₁ ≤ pCoreOf 2 (LOf L V₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, (le_sup_left.trans lOf_sup_le_normalizer_ROf) hx⟩)
      (isPGroup_ROf.to_le inf_le_right)
  exact hle ⟨h1, h2⟩

theorem fsuV_le_ROf (h : Hyp11 G T L I n) : fsuV T I ≤ ROf T L V₁ :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((fsuV_le_T h).trans le_sup_right)
    (sup_le (lOf_le_L.trans (L_le_normalizer_fsuV h)) (T_le_normalizer_fsuV T I))
    (isPGroup_fsuV h)

theorem inf_centralizer_le_ROf (h : Hyp11 G T L I n) :
    T ⊓ Subgroup.centralizer (L : Set G) ≤ ROf T L V₁ := by
  have hp : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (L : Set G)) :=
    h.fsu.sylow.1.to_le inf_le_left
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
    (sup_le ?_ ?_) hp
  · intro l hl
    have hlL : l ∈ L := lOf_le_L hl
    have key : ∀ c ∈ Subgroup.centralizer (L : Set G), l * c * l⁻¹ = c := fun c hc => by
      rw [Subgroup.mem_centralizer_iff.mp hc l hlL, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [key c hc.2]
      exact hc
    · intro hc
      have h1 := key _ hc.2
      have h2 : l * c * l⁻¹ = c := by
        calc l * c * l⁻¹ = l⁻¹ * (l * (l * c * l⁻¹) * l⁻¹) * l := by group
          _ = l⁻¹ * (l * c * l⁻¹) * l := by rw [h1]
          _ = c := by group
      rw [h2] at hc
      exact hc
  · exact (le_inf Subgroup.le_normalizer (h.normal.trans
      (fun t ht => mem_normalizer_centralizer ht))).trans
      Subgroup.inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Vol2.Ch11.SecA
