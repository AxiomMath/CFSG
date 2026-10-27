module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Quot
public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Ch3E213M

namespace E217R4

variable {G : Type} [Group G] [Finite G]

theorem false_of_star {H T M V : Subgroup G} (h : E2.Hyp28 H T M V) (hchar : CharTwo H)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI h.elem H)) (hV16 : Nat.card V = 2 ^ 4)
    (hJ : kerIn M H = pCoreOf 2 H) {A T₀ : Subgroup (E2.StarQuot M H)} (hA9 : Nat.card A = 9)
    (hT₀T : T₀ ≤ E2.star M H T) (hT₀A : T₀ ≤ Subgroup.normalizer (A : Set (E2.StarQuot M H)))
    (hirr : ∀ C : Subgroup (E2.StarQuot M H), C ≤ A →
      T₀ ≤ Subgroup.normalizer (C : Set (E2.StarQuot M H)) → C = ⊥ ∨ C = A)
    {x : G} (hx : x ∈ V) (hVT₀ : (V.subgroupOf H).map (E2P.starMap M H) ≤ T₀)
    (hinv : ∀ a ∈ A, E2P.starMap M H ⟨x, h.le_H hx⟩ * a *
      (E2P.starMap M H ⟨x, h.le_H hx⟩)⁻¹ * a = 1) : False := by
  have hMH : M ≤ H := h.minParabolic.maximal.1.le
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hD
  set π := QuotientGroup.mk' D with hπ
  set e := starEquiv hMH with he
  have hDeq : D = (pCoreOf 2 H).subgroupOf H :=
    (kerIn_subgroupOf_top_eq hMH).trans (by rw [hJ])
  have hπe : ∀ y : ↥H, e (π y) = E2P.starMap M H y := fun y => rfl
  refine false_of_quotient h hchar hq hV16 (D := D) hDeq (Ā := A.comap e.toMonoidHom)
    (T₀b := T₀.comap e.toMonoidHom) ?_ ?_ ?_ ?_ hx ?_ ?_
  · rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective e.symm.injective]
    exact hA9
  · intro y hy
    have hyT : e y ∈ E2.star M H T := hT₀T hy
    rw [← map_barIn_starEquiv hMH T] at hyT
    obtain ⟨b, hb, hby⟩ := hyT
    have : b = y := e.injective hby
    rwa [← this]
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := Subgroup.mem_normalizer_iff.1 (hT₀A (show e y ∈ T₀ from hy)) (e z)
    simpa using this
  · intro C hCA hCN
    set C' : Subgroup (E2.StarQuot M H) := C.comap e.symm.toMonoidHom with hC'
    have hC'A : C' ≤ A := fun z hz => by
      have : e (e.symm z) ∈ A := hCA hz
      simpa using this
    have hC'N : T₀ ≤ Subgroup.normalizer (C' : Set (E2.StarQuot M H)) := by
      intro t ht
      have hy : e.symm t ∈ T₀.comap e.toMonoidHom := by
        show e (e.symm t) ∈ T₀
        simpa using ht
      have hN := Subgroup.mem_normalizer_iff.1 (hCN hy)
      rw [Subgroup.mem_normalizer_iff]
      intro z
      show e.symm z ∈ C ↔ e.symm (t * z * t⁻¹) ∈ C
      rw [map_mul, map_mul, map_inv]
      exact hN (e.symm z)
    rcases hirr C' hC'A hC'N with h0 | h0
    · left
      rw [eq_bot_iff]
      intro c hc
      have : e c ∈ C' := by
        show e.symm (e c) ∈ C
        simpa using hc
      rw [h0, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (e.injective (by simpa using this))
    · right
      ext c
      constructor
      · intro hc
        have : e c ∈ C' := by
          show e.symm (e c) ∈ C
          simpa using hc
        rw [h0] at this
        exact this
      · intro hc
        have : e c ∈ C' := by
          rw [h0]
          exact hc
        have h1 : e.symm (e c) ∈ C := this
        simpa using h1
  · rintro _ ⟨y, hy, rfl⟩
    exact hVT₀ ⟨y, hy, rfl⟩
  · intro a ha
    apply e.injective
    simp only [map_mul, map_inv, map_one]
    rw [hπe]
    exact hinv (e a) ha

end E217R4

end CFSG.Quasithin
