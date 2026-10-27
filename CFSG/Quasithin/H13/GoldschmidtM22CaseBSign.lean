module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBRho
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBS5

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Quasithin

variable {G : Type} [Group G] {V L : Subgroup G}

@[expose] def IsOTwoPerfect (L : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ L → (X.subgroupOf L).Normal → (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ X) → X = L

namespace PermRho

variable (ρ : PermRho V)

theorem sign_conj {l x : G} (hl : l ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    Equiv.Perm.sign (ρ (l * x * l⁻¹)) = Equiv.Perm.sign (ρ x) := by
  rw [apply_conj hl hx, _root_.map_mul, _root_.map_mul, _root_.map_inv,
    mul_comm (Equiv.Perm.sign (ρ l)), mul_assoc, mul_inv_cancel, mul_one]

theorem sign_eq_one_of_mem (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hLO : IsOTwoPerfect L) :
    ∀ l ∈ L, Equiv.Perm.sign (ρ l) = 1 := by
  let X : Subgroup G :=
    { carrier := {x | x ∈ L ∧ Equiv.Perm.sign (ρ x) = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
        exact ⟨L.mul_mem hx hy, by
          rw [apply_mul (hLN hx) (hLN hy), _root_.map_mul, hx1, hy1, one_mul]⟩
      one_mem' := ⟨L.one_mem, by rw [apply_one, _root_.map_one]⟩
      inv_mem' := by
        rintro x ⟨hx, hx1⟩
        exact ⟨L.inv_mem hx, by rw [apply_inv (hLN hx), _root_.map_inv, hx1, inv_one]⟩ }
  have hXL : X ≤ L := fun x hx => hx.1
  have hnorm : (X.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXL]
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx, hx1⟩
      exact ⟨L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl), by rw [sign_conj ρ (hLN hl) (hLN hx), hx1]⟩
    · rintro ⟨hx, hx1⟩
      have hxL : x ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
        simpa [mul_assoc] using this
      exact ⟨hxL, by rw [← sign_conj ρ (hLN hl) (hLN hxL), hx1]⟩
  have hX : X = L := hLO X hXL hnorm fun x hx => ⟨1, L.pow_mem hx _, by
    rw [pow_one, pow_two, apply_mul (hLN hx) (hLN hx), _root_.map_mul, ← sq]
    exact Int.units_pow_two _⟩
  intro l hl
  have : l ∈ X := hX ▸ hl
  exact this.2

theorem exists_eq_of_alternating (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLO : IsOTwoPerfect L) (hLQ : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    ∀ σ ∈ alternatingGroup (Fin 5), ∃ l ∈ L, ρ l = σ := by
  let K : Subgroup (Equiv.Perm (Fin 5)) :=
    { carrier := {σ | ∃ l ∈ L, ρ l = σ}
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, rfl⟩
        exact ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, apply_mul (hLN hl₁) (hLN hl₂)⟩
      one_mem' := ⟨1, L.one_mem, apply_one⟩
      inv_mem' := by
        rintro _ ⟨l, hl, rfl⟩
        exact ⟨l⁻¹, L.inv_mem hl, apply_inv (hLN hl)⟩ }
  have hKn : K.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨l, hl, rfl⟩ τ
    obtain ⟨n, hn, rfl⟩ := ρ.exists_eq τ
    exact ⟨n * l * n⁻¹, (Subgroup.mem_normalizer_iff.mp (hNL hn) l).mp hl, apply_conj hn (hLN hl)⟩
  have hKA : K ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨l, hl, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (sign_eq_one_of_mem ρ hLN hLO l hl)
  have hKne : K ≠ ⊥ := by
    obtain ⟨l, hl, hlQ⟩ := Set.not_subset.mp hLQ
    intro hbot
    have : ρ l ∈ K := ⟨l, hl, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hlQ ((eq_one_iff (hLN hl)).mp this)
  have hKeq := perm5_eq_alternating_of_normal K hKA hKne
  intro σ hσ
  have : σ ∈ K := by rw [hKeq]; exact hσ
  exact this

theorem exists_odd_of_not_le {X : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hA : ∀ σ ∈ alternatingGroup (Fin 5), ∃ l ∈ L, ρ l = σ)
    (hnot : ¬ autOn X V ≤ autOn L V) :
    ∃ a ∈ X, Equiv.Perm.sign (ρ a) = -1 := by
  obtain ⟨φ, hφX, hφL⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨a, haX, rfl⟩ := CFSG.Quasithin.H13.mem_autOn_iff.mp hφX
  refine ⟨a, haX, ?_⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ a)) with h1 | h1
  · exfalso
    obtain ⟨l, hl, hρ⟩ := hA (ρ a) (Equiv.Perm.mem_alternatingGroup.mpr h1)
    apply hφL
    refine CFSG.Quasithin.H13.mem_autOn_iff.mpr ⟨⟨l, hLN hl⟩, hl, ?_⟩
    have hq : l⁻¹ * (a : G) ∈ Subgroup.centralizer (V : Set G) :=
      (eq_iff (hLN hl) a.2).mp hρ
    ext v
    rw [CFSG.Quasithin.H13.conjAct_apply_coe, CFSG.Quasithin.H13.conjAct_apply_coe]
    have hc := Subgroup.mem_centralizer_iff.mp hq (v : G) v.2
    calc l * (v : G) * l⁻¹ = l * ((v : G) * (l⁻¹ * (a : G)) * (l⁻¹ * (a : G))⁻¹) * l⁻¹ := by
          group
      _ = l * ((l⁻¹ * (a : G)) * v * (l⁻¹ * (a : G))⁻¹) * l⁻¹ := by rw [hc]
      _ = (a : G) * v * (a : G)⁻¹ := by group
  · exact h1

end PermRho

end CFSG.Quasithin.H13.GM22
