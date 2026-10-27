module

public import CFSG.Quasithin.Vol2.Ch3T325P
public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch3T325A

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjClosure_bot (M : Subgroup G) : conjClosure (⊥ : Subgroup G) M = ⊥ :=
  le_bot_iff.mp (conjClosure_le fun m _ z hz => by
    rw [Subgroup.mem_bot.mp hz, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _)

theorem card_conjugate (H : Subgroup G) (g : G) :
    Nat.card ↥(CFSG.conjugate H g) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem le_normalizer_conjugate {L V₀ : Subgroup G} {t : G}
    (hL : L ≤ Subgroup.normalizer (V₀ : Set G)) (ht : t ∈ Subgroup.normalizer (L : Set G)) :
    L ≤ Subgroup.normalizer (CFSG.conjugate V₀ t : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have htl : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht l).mp hl
  rw [mem_conjugate_iff, mem_conjugate_iff]
  have e : t * (l * x * l⁻¹) * t⁻¹ = (t * l * t⁻¹) * (t * x * t⁻¹) * (t * l * t⁻¹)⁻¹ := by
    group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (hL htl) _

theorem isTISetUnder_of_inf_centralizer_eq_bot [Finite G] {T L I : Subgroup G}
    (hfsu : FSU G T L I) (hC : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) :
    IsTISetUnder I (fsuM T L) := by
  intro g hg hgn
  have hL0I : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hfsu.irrPlus.2.2.1
  have hirr := hfsu.irrPlus.2.2.2.2.2.1
  rw [hC] at hirr
  set J := I ⊓ CFSG.conjugate I g with hJ
  have hJL : fsuL0 T L ≤ Subgroup.normalizer (J : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ l' ∈ fsuL0 T L, ∀ x ∈ J, l' * x * l'⁻¹ ∈ J := by
      intro l' hl' x hx
      have hgl' : g * l' * g⁻¹ ∈ fsuL0 T L := (Subgroup.mem_normalizer_iff.mp hg l').mp hl'
      have hx1 : x ∈ I := hx.1
      have hx2 : g * x * g⁻¹ ∈ I := mem_conjugate_iff.mp hx.2
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hL0I hl') x).mp hx1, mem_conjugate_iff.mpr ?_⟩
      have e : g * (l' * x * l'⁻¹) * g⁻¹ =
          (g * l' * g⁻¹) * (g * x * g⁻¹) * (g * l' * g⁻¹)⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hL0I hgl') _).mp hx2
    intro x
    refine ⟨key l hl x, fun hx => ?_⟩
    have h1 := key l⁻¹ (inv_mem hl) _ hx
    have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
    rwa [e] at h1
  rcases hirr J bot_le inf_le_left hJL with h1 | h1
  · exact h1
  · exfalso
    apply hgn
    have hJc : J ≤ CFSG.conjugate I g := inf_le_right
    have hle : I ≤ CFSG.conjugate I g := h1 ▸ hJc
    have heq : CFSG.conjugate I g = I :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjugate])).symm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff (H := I) (g := g), heq]

namespace Ctx

variable [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem isTISetUnder (hC : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ g ∈ Subgroup.normalizer (L : Set G), g ∉ Subgroup.normalizer (V₀ : Set G) →
      V₀ ⊓ CFSG.conjugate V₀ g = ⊥ := by
  have hC' : V₀ ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
    show V₀ ⊓ Subgroup.centralizer (conjClosure L T : Set G) = ⊥
    rw [c.eqL]
    exact hC
  have h := isTISetUnder_of_inf_centralizer_eq_bot c.fsu hC'
  intro g hg hgn
  refine h g ?_ hgn
  show g ∈ Subgroup.normalizer (conjClosure L T : Set G)
  rw [c.eqL]
  exact hg

theorem case_two (hC : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hV : V₀ = conjClosure V₀ T) :
    V₀ = conjClosure V₀ T ∧ V₀ ≤ T ∧ T ≤ Subgroup.normalizer (V₀ : Set G) ∧
      V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      ∀ g ∈ Subgroup.normalizer (L : Set G), g ∉ Subgroup.normalizer (V₀ : Set G) →
        V₀ ⊓ CFSG.conjugate V₀ g = ⊥ := by
  have hT : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    have h := T_le_NV T V₀
    rwa [← hV] at h
  exact ⟨hV, c.V₀_le_T, hT, hC, c.isTISetUnder hC⟩

end Ctx

end CFSG.Quasithin.H13.T325
