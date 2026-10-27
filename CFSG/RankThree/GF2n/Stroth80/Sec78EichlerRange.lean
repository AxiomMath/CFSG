module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem eichlerRangeCard_holds :
    ∀ (K : Type) [Field K] [Finite K] (V : Type) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
      ∀ u w : V, Q u = 0 → polar Q u w = 0 → LinearIndependent K ![u, w] →
        Nat.card {x : V // ∃ v : V, x = (eichlerG Q u w).app v - v} = Nat.card K ^ 2 := by
  intro K _ _ V _ _ _ Q hQ u w hu hw hli
  obtain ⟨T, hT⟩ : ∃ T : K × K →ₗ[K] V, ∀ a b : K, T (a, b) = a • u + b • w :=
    ⟨LinearMap.smulRight (LinearMap.fst K K K) u + LinearMap.smulRight (LinearMap.snd K K K) w,
      fun a b => by simp⟩
  have hTker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    rw [hT] at h
    obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.mp hli a b h
    simp [ha, hb]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hTker
  have hgu : g u = (1, 0) := by
    simpa [hT] using LinearMap.congr_fun hg (1, 0)
  have hgw : g w = (0, 1) := by
    simpa [hT] using LinearMap.congr_fun hg (0, 1)
  have hsurj : ∀ a c : K, ∃ v : V, polar Q v u = a ∧ polar Q v w = c := by
    intro a c
    obtain ⟨F, hFu, hFw⟩ : ∃ F : V →ₗ[K] K, F u = a ∧ F w = c :=
      ⟨(a • LinearMap.fst K K K + c • LinearMap.snd K K K).comp g, by simp [hgu],
        by simp [hgw]⟩
    obtain ⟨v, hv⟩ := (LinearMap.BilinForm.toDual (polarBilin Q) hQ).surjective F
    have hpol : ∀ x : V, polar Q v x = F x := by
      intro x
      have h1 : polar Q v x = (LinearMap.BilinForm.toDual (polarBilin Q) hQ v) x := rfl
      rw [h1, hv]
    exact ⟨v, by rw [hpol u, hFu], by rw [hpol w, hFw]⟩
  have hE : ∀ v : V, (eichlerG Q u w).app v - v =
      polar Q v u • w - (polar Q v w + Q w * polar Q v u) • u := by
    intro v
    rw [eichlerG_app hu hw v]
    abel
  have hset : ∀ x : V, (∃ v : V, x = (eichlerG Q u w).app v - v) ↔
      x ∈ Set.range (fun p : K × K => p.1 • w - p.2 • u) := by
    intro x
    constructor
    · rintro ⟨v, rfl⟩
      exact Set.mem_range.mpr ⟨(polar Q v u, polar Q v w + Q w * polar Q v u), (hE v).symm⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      obtain ⟨v, hv1, hv2⟩ := hsurj a (b - Q w * a)
      refine ⟨v, ?_⟩
      show a • w - b • u = (eichlerG Q u w).app v - v
      rw [hE v, hv1, hv2, sub_add_cancel]
  have hinj : Function.Injective (fun p : K × K => p.1 • w - p.2 • u) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have h0 : a • w - b • u - (c • w - d • u) = 0 := sub_eq_zero.mpr h
    have e : (d - b) • u + (a - c) • w = a • w - b • u - (c • w - d • u) := by module
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hli (d - b) (a - c) (e.trans h0)
    have hac : a = c := sub_eq_zero.mp h2
    have hbd : b = d := (sub_eq_zero.mp h1).symm
    rw [hac, hbd]
  have hcard : Nat.card {x : V // ∃ v : V, x = (eichlerG Q u w).app v - v} =
      Nat.card (K × K) :=
    (Nat.card_congr (Equiv.subtypeEquivRight hset)).trans (Nat.card_range_of_injective hinj)
  rw [hcard, Nat.card_prod, pow_two]

end CFSG.RankThree.GF2n.Stroth80
