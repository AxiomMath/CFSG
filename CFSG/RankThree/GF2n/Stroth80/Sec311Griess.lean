module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Cover
public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

@[expose] def GriessCoverStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (E : Type) [Group E] [Finite E] (Y : Subgroup E), Y ≤ Subgroup.center E →
    commutator E = ⊤ →
  (∀ m : ℕ, 2 ≤ m → ∀ π : E →* GL (Fin m) K, π.range = StatedSL m K → π.ker = Y →
    Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
        e ∈ Subgroup.normalizer (A : Set E)) →
      Nat.card A < (if Nat.card K = 4 then (if m = 2 then 4 else if m = 3 then 16 else 0)
        else 0)) ∧
  (∀ m : ℕ, 1 ≤ m → ∀ π : E →* GL (Fin m ⊕ Fin m) K, π.range = StatedSp m K → π.ker = Y →
    Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
        e ∈ Subgroup.normalizer (A : Set E)) →
      Nat.card A < (if Nat.card K = 4 ∧ m = 1 then 4 else 0)) ∧
  (∀ m : ℕ, 2 ≤ m → ∀ π : E →* GL (Fin m ⊕ Fin m) K,
    π.range = StatedOmega (StatedQuadPlus m K) → π.ker = Y →
    Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
        e ∈ Subgroup.normalizer (A : Set E)) →
      Nat.card A < (if Nat.card K = 4 ∧ m = 2 then 16 else 0)) ∧
  (∀ (m : ℕ) (b c : K), 2 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ π : E →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K,
    π.range = StatedOmega (StatedQuadMinus m K b c) → π.ker = Y → Y = ⊥)

variable {R : Type} [Group R]

theorem le_of_perfect_cover [Finite R] (N N₀ L : Subgroup R) [N₀.Normal]
    (hN₀N : N₀ ≤ N) (hgen : ⨆ g : R, conjSubgroup g L = ⊤)
    (hcomm : ∀ (g : R), ∀ n ∈ N, ∀ l ∈ conjSubgroup g L, ⁅n, l⁆ ∈ N₀) (hLN : L ⊓ N ≤ N₀)
    (hab : ∀ l ∈ L, ∀ l' ∈ L, ⁅l, l'⁆ ∈ N ∧ l ^ 2 ∈ N) {τ : R}
    (hτL : τ ∈ Subgroup.normalizer (L : Set R)) (hτ : ∀ l ∈ L, ⁅τ, l⁆ ∈ N → l ∈ N)
    (hnorm : ∀ r : R, r ∈ Subgroup.normalizer ((L ⊔ N : Subgroup R) : Set R) →
      r ∈ Subgroup.normalizer (L : Set R))
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : R →* GL ι K)
    (hker : φ.ker = N) (b : ℕ)
    (hP : ∀ (E : Type) [Group E] [Finite E] (Y : Subgroup E) (π : E →* GL ι K),
      π.range = φ.range → π.ker = Y → Y ≤ Subgroup.center E → commutator E = ⊤ →
      ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
        (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
          e ∈ Subgroup.normalizer (A : Set E)) → b ≤ Nat.card A → Y = ⊥)
    (hb : b ≤ Nat.card (L.map φ)) : N ≤ N₀ := by
  obtain ⟨hperf, hcen, hinf, hel, hnormE⟩ :=
    exists_cover_data N N₀ L hN₀N hgen hcomm hLN hab hτL hτ hnorm
  set π₀ := QuotientGroup.mk' N₀ with hπ₀
  have hle : N₀ ≤ φ.ker := hker ▸ hN₀N
  set π : R ⧸ N₀ →* GL ι K := QuotientGroup.lift N₀ φ hle with hπ
  have hrange : π.range = φ.range := by
    have h1 : π.comp π₀ = φ := QuotientGroup.lift_comp_mk' N₀ φ hle
    conv_rhs => rw [← h1]
    rw [MonoidHom.range_comp, QuotientGroup.range_mk', ← MonoidHom.range_eq_map]
  have hkerπ : π.ker = N.map π₀ := by
    rw [hπ, QuotientGroup.ker_lift, hker]
  have hY : N.map π₀ = ⊥ := by
    refine hP (R ⧸ N₀) (N.map π₀) π hrange hkerπ hcen hperf (L.map π₀) hinf hel hnormE ?_
    have hcard : Nat.card (L.map π₀) = Nat.card (L.map φ) := by
      refine card_map_eq_of_ker L π₀ φ fun x hx => ?_
      rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← MonoidHom.mem_ker, hker]
      exact ⟨fun h => hN₀N h, fun h => hLN ⟨hx, h⟩⟩
    rw [hcard]
    exact hb
  intro n hn
  have : π₀ n = 1 := by
    have : π₀ n ∈ (⊥ : Subgroup (R ⧸ N₀)) := hY ▸ Subgroup.mem_map_of_mem π₀ hn
    exact this
  exact (QuotientGroup.eq_one_iff n).mp this

end CFSG.RankThree.GF2n.Stroth80
