module

public import CFSG.Quasithin.EmptyFaithful.S153E59P
public import CFSG.Quasithin.EmptyFaithful.S153E55B

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace S153EN8

variable {G : Type} [Group G]

theorem sl2_eq_one_of_smul : ∀ B : SL(2, ZMod 2), (∀ w : Fin 2 → ZMod 2, B • w = w) → B = 1 := by
  decide +kernel

theorem fpf_P₁ {I P V N₁ N₂ P₁ P₂ : Subgroup G} (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂)
    (h₁ : IsSumOfNatSL2ModulesN153 1 N₁ P₁ P V)
    {d n₁ n₂ : G} (hd : d = n₁ * n₂) (hn₁ : n₁ ∈ N₁) (hn₂ : n₂ ∈ N₂) (hn₁P : n₁ ∉ P)
    {k : ℕ} (hdk : d ^ 3 ^ k = 1) {p : G} (hp : p ∈ P₁) (hpd : d * p * d⁻¹ * p⁻¹ ∈ V) : p ∈ V := by
  obtain ⟨β, φ, hβs, hβk, hφs, hφk, hrel⟩ := h₁
  have hdI : d ∈ I := hd ▸ I.mul_mem (pd.N₁_le_I hn₁) (pd.N₂_le_I hn₂)
  let π : ↥P₁ → (Fin 2 → ZMod 2) := fun x => Multiplicative.toAdd (φ x) 0
  have hπadd : ∀ x y : ↥P₁, π (x * y) = π x + π y := by
    intro x y
    simp [π, map_mul]
  have hπs : Function.Surjective π := by
    intro w
    obtain ⟨x, hx⟩ := hφs (Multiplicative.ofAdd (fun _ => w))
    exact ⟨x, by simp [π, hx]⟩
  have hπk : ∀ x : ↥P₁, π x = 0 ↔ (x : G) ∈ V := by
    intro x
    rw [← hφk]
    constructor
    · intro h
      have : Multiplicative.toAdd (φ x) = 0 := by
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        rw [hj]
        exact h
      exact Multiplicative.toAdd.injective this
    · intro h
      have : Multiplicative.toAdd (φ x) = 0 := by rw [h]; rfl
      simp [π, this]
  set B := β ⟨n₁, hn₁⟩ with hB
  have hB1 : B ≠ 1 := fun h => hn₁P ((hβk _).1 h)
  have hcl : ∀ x : ↥P₁, d * x * d⁻¹ ∈ P₁ := fun x => pd.conj_P₁ hdI x.2
  let f : ↥P₁ → ↥P₁ := fun x => ⟨d * x * d⁻¹, hcl x⟩
  have hcent : ∀ y : G, y ∈ P₁ → y * n₂ * y⁻¹ * n₂⁻¹ ∈ V := by
    intro y hy
    have hy' := hy
    rw [pd.cent₁] at hy'
    exact hy'.2.2 n₂ hn₂
  have hact : ∀ x : ↥P₁, π (f x) = B • π x := by
    intro x
    have hn₂P₁ : n₂ * x * n₂⁻¹ ∈ P₁ := pd.conj_P₁ (pd.N₂_le_I hn₂) x.2
    have hxc : (x : G) * n₂ * (x : G)⁻¹ * n₂⁻¹ ∈ V := hcent x x.2
    have hV' : n₂ * x * n₂⁻¹ * (x : G)⁻¹ ∈ V := by
      have e : n₂ * (x : G) * n₂⁻¹ * (x : G)⁻¹ = ((x : G) * n₂ * (x : G)⁻¹ * n₂⁻¹)⁻¹ := by group
      rw [e]
      exact V.inv_mem hxc
    have hπ' : π ⟨n₂ * x * n₂⁻¹, hn₂P₁⟩ = π x := by
      have hmem : (⟨n₂ * x * n₂⁻¹, hn₂P₁⟩ : ↥P₁) = ⟨n₂ * x * n₂⁻¹ * (x : G)⁻¹, P₁.mul_mem hn₂P₁
          (P₁.inv_mem x.2)⟩ * x := by
        apply Subtype.ext
        simp
      rw [hmem, hπadd, (hπk _).2 hV', zero_add]
    have hrel' := hrel ⟨n₁, hn₁⟩ ⟨n₂ * x * n₂⁻¹, hn₂P₁⟩ (f x) (by
      show d * (x : G) * d⁻¹ = n₁ * (n₂ * (x : G) * n₂⁻¹) * n₁⁻¹
      rw [hd]
      group)
    have : π (f x) = B • π ⟨n₂ * x * n₂⁻¹, hn₂P₁⟩ := by
      simp only [π, hrel', toAdd_ofAdd]
      rfl
    rw [this, hπ']
  have hiter : ∀ (j : ℕ) (x : ↥P₁), ((f^[j] x : ↥P₁) : G) = d ^ j * x * (d ^ j)⁻¹ ∧
      π (f^[j] x) = B ^ j • π x := by
    intro j
    induction j with
    | zero =>
      intro x
      simp
    | succ j ih =>
      intro x
      obtain ⟨h1, h2⟩ := ih x
      rw [Function.iterate_succ_apply']
      refine ⟨?_, ?_⟩
      · show d * ((f^[j] x : ↥P₁) : G) * d⁻¹ = _
        rw [h1]
        group
      · rw [hact, h2, ← mul_smul, ← pow_succ']
  have hB3k : B ^ 3 ^ k = 1 := by
    apply sl2_eq_one_of_smul
    intro w
    obtain ⟨x, rfl⟩ := hπs w
    obtain ⟨h1, h2⟩ := hiter (3 ^ k) x
    have h3 : f^[3 ^ k] x = x := by
      apply Subtype.ext
      rw [h1, hdk]
      simp
    rw [← h2, h3]
  have hB3 : B ^ 3 = 1 := S153E59.sl2_pow_three_of_pow hB3k
  have hfix : B • π ⟨p, hp⟩ = π ⟨p, hp⟩ := by
    rw [← hact]
    have hmem : f ⟨p, hp⟩ = ⟨d * p * d⁻¹ * p⁻¹, P₁.mul_mem (hcl ⟨p, hp⟩) (P₁.inv_mem hp)⟩ * ⟨p, hp⟩ := by
      apply Subtype.ext
      simp [f]
    rw [hmem, hπadd, (hπk _).2 hpd, zero_add]
  have h0 : π ⟨p, hp⟩ = 0 := S153E59.sl2_fpf B hB1 hB3 _ hfix
  exact (hπk _).1 h0

theorem fixed_mem_V {I P V N₁ N₂ P₁ P₂ : Subgroup G} (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂)
    (h₁ : IsSumOfNatSL2ModulesN153 1 N₁ P₁ P V) (h₂ : IsSumOfNatSL2ModulesN153 1 N₂ P₂ P V)
    {d n₁ n₂ n₂' n₁' : G} (hd : d = n₁ * n₂) (hn₁ : n₁ ∈ N₁) (hn₂ : n₂ ∈ N₂) (hn₁P : n₁ ∉ P)
    (hd' : d = n₂' * n₁') (hn₂' : n₂' ∈ N₂) (hn₁' : n₁' ∈ N₁) (hn₂'P : n₂' ∉ P)
    {k : ℕ} (hdk : d ^ 3 ^ k = 1) {x : G} (hx : x ∈ P) (hdx : d * x * d⁻¹ = x) : x ∈ V := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := pd.exists_mul hx
  have hdI : d ∈ I := hd ▸ I.mul_mem (pd.N₁_le_I hn₁) (pd.N₂_le_I hn₂)
  have ha : d * p₁ * d⁻¹ ∈ P₁ := pd.conj_P₁ hdI hp₁
  have hb : d * p₂ * d⁻¹ ∈ P₂ := pd.conj_P₂ hdI hp₂
  have hab : (d * p₁ * d⁻¹) * (d * p₂ * d⁻¹) = p₁ * p₂ := by
    rw [← hdx]
    group
  have hu : p₁⁻¹ * (d * p₁ * d⁻¹) = p₂ * (d * p₂ * d⁻¹)⁻¹ := by
    calc p₁⁻¹ * (d * p₁ * d⁻¹) = p₁⁻¹ * ((d * p₁ * d⁻¹) * (d * p₂ * d⁻¹)) * (d * p₂ * d⁻¹)⁻¹ := by
          group
      _ = p₁⁻¹ * (p₁ * p₂) * (d * p₂ * d⁻¹)⁻¹ := by rw [hab]
      _ = p₂ * (d * p₂ * d⁻¹)⁻¹ := by group
  have huV : p₁⁻¹ * (d * p₁ * d⁻¹) ∈ V := by
    rw [← pd.inf]
    exact ⟨P₁.mul_mem (P₁.inv_mem hp₁) ha, by rw [hu]; exact P₂.mul_mem hp₂ (P₂.inv_mem hb)⟩
  have hp₁V : p₁ ∈ V := by
    refine fpf_P₁ pd h₁ hd hn₁ hn₂ hn₁P hdk hp₁ ?_
    have e : d * p₁ * d⁻¹ * p₁⁻¹ = p₁ * (p₁⁻¹ * (d * p₁ * d⁻¹)) * p₁⁻¹ := by group
    rw [e]
    exact pd.conj_V (pd.P_le_I (pd.P₁_le_P hp₁)) huV
  have hp₂V : p₂ ∈ V := by
    refine fpf_P₁ pd.symm h₂ hd' hn₂' hn₁' hn₂'P hdk hp₂ ?_
    have e : d * p₂ * d⁻¹ * p₂⁻¹ = (p₂ * (d * p₂ * d⁻¹)⁻¹)⁻¹ := by group
    rw [e, ← hu]
    exact V.inv_mem huV
  exact V.mul_mem hp₁V hp₂V

end S153EN8

end CFSG.Quasithin
