module

public import CFSG.Walter.J1.Signalizer

public section

namespace CFSG.Walter.J1

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_isPGroup_of_normalizer {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P ≤ Q)
    (hN : ∀ g ∈ Subgroup.normalizer (P : Set G), (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ P) : Q = P := by
  by_contra hne
  have : Group.IsNilpotent Q := hQ.isNilpotent
  set P' := P.subgroupOf Q
  have hlt : P' < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    apply le_antisymm _ hPQ
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ P' := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨q, hqN, hqP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent P' hlt)
  apply hqP
  have hqNG : (q : G) ∈ Subgroup.normalizer (P : Set G) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hxQ : (⟨x, hPQ hx⟩ : Q) ∈ P' := hx
    have := (Subgroup.mem_normalizer_iff.mp hqN _).mp hxQ
    exact this
  obtain ⟨k, hk⟩ := hQ q
  exact hN _ hqNG ⟨k, by simpa using congrArg Subtype.val hk⟩

@[expose] noncomputable def sylowOfNormalizer {p : ℕ} [Fact p.Prime] (P : Subgroup G)
    (hP : IsPGroup p P)
    (hN : ∀ g ∈ Subgroup.normalizer (P : Set G), (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ P) :
    Sylow p G :=
  ⟨P, hP, fun hQ hPQ => eq_of_isPGroup_of_normalizer hQ hPQ hN⟩

@[simp] theorem coe_sylowOfNormalizer {p : ℕ} [Fact p.Prime] (P : Subgroup G)
    (hP : IsPGroup p P)
    (hN : ∀ g ∈ Subgroup.normalizer (P : Set G), (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ P) :
    (sylowOfNormalizer P hP hN : Subgroup G) = P := rfl

theorem exists_normalizer_conj {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [IsMulCommutative (P : Subgroup G)] {x g : G} (hx : x ∈ P) (hgx : g * x * g⁻¹ ∈ P) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  obtain ⟨n, hn, hnx⟩ := Sylow.conj_eq_normalizer_conj_of_mem P x g⁻¹ hx (by simpa using hgx)
  exact ⟨n⁻¹, Subgroup.inv_mem _ hn, by simpa using hnx.symm⟩

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

theorem map_conj_le_F {X : Subgroup G} (hodd : Odd (Nat.card X)) {g : G}
    (hX : X ≤ Subgroup.centralizer ({(h.conj g).t} : Set G)) :
    X.map (MulAut.conj g⁻¹).toMonoidHom ≤ h.F := by
  have hXF : X ≤ (h.conj g).F := (h.conj g).le_F_of_odd hX hodd
  rw [conj_F] at hXF
  have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hXF
  rwa [map_conj_inv_map_conj] at this

include h in
theorem exists_conj_of_good {p : ℕ} (hp : p = 3 ∨ p = 5) {X Y : Subgroup G}
    (hX : Nat.card X = p) (hY : Nat.card Y = p) {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hXx : X ≤ Subgroup.centralizer ({x} : Set G))
    (hYy : Y ≤ Subgroup.centralizer ({y} : Set G)) :
    ∃ g : G, X.map (MulAut.conj g).toMonoidHom = Y := by
  have hodd : Odd p := by rcases hp with rfl | rfl <;> decide
  obtain ⟨g₁, hg₁⟩ := h.exists_conj_t_eq hx
  obtain ⟨g₂, hg₂⟩ := h.exists_conj_t_eq hy
  have hX₀ := h.map_conj_le_F (X := X) (hX ▸ hodd) (g := g₁) (hg₁ ▸ hXx)
  have hY₀ := h.map_conj_le_F (X := Y) (hY ▸ hodd) (g := g₂) (hg₂ ▸ hYy)
  obtain ⟨f, -, hf⟩ := A5Sub.exists_conj_eq h.iso hX₀ hY₀ hp
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g₁⁻¹).injective, hX])
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g₂⁻¹).injective, hY])
  refine ⟨g₂ * f * g₁⁻¹, ?_⟩
  rw [map_conj_mul, map_conj_mul, hf]
  have := map_conj_inv_map_conj Y g₂⁻¹
  rwa [inv_inv] at this

end JankoHyp

end CFSG.Walter.J1
