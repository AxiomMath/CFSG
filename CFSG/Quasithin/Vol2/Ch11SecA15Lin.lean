module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_natural {L U V L₁ P V₁ : Subgroup G} {F : Type} [Field F] [Fintype F]
    {k : ℕ} (α : ↥L →* ↥(StatedSL 3 F)) (β : ↥U →* Multiplicative (Fin k → Fin 3 → F))
    (hβi : Function.Injective β)
    (hβ : ∀ (l : ↥L) (u v : ↥U), (v : G) = l * u * l⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Multiplicative.toAdd (β u) i)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hVU : V ≤ U)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ V → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = V)
    (hV : V ≠ ⊥) (hcard : Nat.card V = Fintype.card F ^ 3) (hPL : P ≤ L) (hL₁L : L₁ ≤ L)
    (hfix : ∀ v ∈ V, (∀ t ∈ P, t * v * t⁻¹ = v) → v ∈ V₁)
    (hL₁ : L₁ ≤ Subgroup.centralizer (V₁ : Set G)) {u₀ : G} (hu₀ : u₀ ∈ U)
    (hP : ∀ t ∈ P, t * u₀ * t⁻¹ = u₀) : ∀ l ∈ L₁, l * u₀ * l⁻¹ = u₀ := by
  classical
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
  have hβv₀ : β ⟨v₀, hVU hv₀⟩ ≠ 1 := by
    intro h1
    apply hv₀1
    have := hβi (h1.trans (map_one β).symm)
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have h0 : Multiplicative.toAdd (β ⟨v₀, hVU hv₀⟩) ≠ 0 := fun h =>
    hβv₀ (Multiplicative.toAdd.injective (h.trans toAdd_one.symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
  rw [Pi.zero_apply] at hi
  let q : ↥V →* Multiplicative (Fin 3 → F) :=
    { toFun := fun w => Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨w, hVU w.2⟩) i)
      map_one' := by
        have : (⟨((1 : ↥V) : G), hVU (1 : ↥V).2⟩ : ↥U) = 1 := rfl
        rw [this, map_one, toAdd_one]
        rfl
      map_mul' := by
        intro x y
        have : (⟨((x * y : ↥V) : G), hVU (x * y).2⟩ : ↥U) =
            ⟨(x : G), hVU x.2⟩ * ⟨(y : G), hVU y.2⟩ := rfl
        simp only [this, map_mul, toAdd_mul, Pi.add_apply, ofAdd_add] }
  have hq : ∀ w : ↥V, Multiplicative.toAdd (q w) = Multiplicative.toAdd (β ⟨w, hVU w.2⟩) i :=
    fun _ => rfl
  have hqeq : ∀ (l : G) (hl : l ∈ L) (w w' : ↥V), (w' : G) = l * w * l⁻¹ →
      Multiplicative.toAdd (q w') =
        ((α ⟨l, hl⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Multiplicative.toAdd (q w) := by
    intro l hl w w' hw
    rw [hq, hq]
    exact hβ ⟨l, hl⟩ ⟨w, hVU w.2⟩ ⟨w', hVU w'.2⟩ hw i
  set J : Subgroup G := q.ker.map V.subtype with hJ
  have hJmem : ∀ x : G, x ∈ J ↔ ∃ w : ↥V, q w = 1 ∧ (w : G) = x := by
    intro x
    rw [hJ, Subgroup.mem_map]
    simp [MonoidHom.mem_ker]
  have hfwd : ∀ l ∈ L, ∀ x ∈ J, l * x * l⁻¹ ∈ J := by
    intro l hl x hx
    obtain ⟨w, hw1, rfl⟩ := (hJmem x).mp hx
    have hmem : l * (w : G) * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) w).mp w.2
    refine (hJmem _).mpr ⟨⟨_, hmem⟩, ?_, rfl⟩
    apply Multiplicative.toAdd.injective
    rw [hqeq l hl w ⟨_, hmem⟩ rfl, hw1, toAdd_one, Matrix.mulVec_zero]
  have hJN : L ≤ Subgroup.normalizer (J : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd l hl x, fun hx => ?_⟩
    have := hfwd l⁻¹ (L.inv_mem hl) _ hx
    simpa [mul_assoc] using this
  have hJV : J ≤ V := Subgroup.map_subtype_le _
  have hJbot : J = ⊥ := by
    rcases hirr J hJV hJN with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨w, hw1, hw⟩ := (hJmem v₀).mp (h0 ▸ hv₀)
      apply hi
      have hw' : w = ⟨v₀, hv₀⟩ := Subtype.ext hw
      have := congrArg Multiplicative.toAdd hw1
      rw [hq, hw', toAdd_one] at this
      exact this
  have hqi : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    have : (w : G) ∈ J := (hJmem _).mpr ⟨w, hw, rfl⟩
    rw [hJbot, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have : Fintype ↥V := Fintype.ofFinite _
  have hqb : Function.Bijective q := by
    refine (Fintype.bijective_iff_injective_and_card q).mpr ⟨hqi, ?_⟩
    have h1 : Fintype.card (Multiplicative (Fin 3 → F)) = Fintype.card F ^ 3 := by
      simp
    rw [h1, ← hcard, Nat.card_eq_fintype_card]
  have hcoord : ∀ (j : Fin k) (l : G) (hl : l ∈ L₁),
      ((α ⟨l, hL₁L hl⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β ⟨u₀, hu₀⟩) j = Multiplicative.toAdd (β ⟨u₀, hu₀⟩) j := by
    intro j l hl
    obtain ⟨w, hw⟩ := hqb.2 (Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨u₀, hu₀⟩) j))
    have hwP : ∀ t ∈ P, t * (w : G) * t⁻¹ = w := by
      intro t ht
      have hmem : t * (w : G) * t⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV (hPL ht)) w).mp w.2
      have hu : t * u₀ * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLU (hPL ht)) u₀).mp hu₀
      have h1 := hqeq t (hPL ht) w ⟨_, hmem⟩ rfl
      have h2 := hβ ⟨t, hPL ht⟩ ⟨u₀, hu₀⟩ ⟨_, hu⟩ rfl j
      have h3 : (⟨t * u₀ * t⁻¹, hu⟩ : ↥U) = ⟨u₀, hu₀⟩ := Subtype.ext (hP t ht)
      rw [h3] at h2
      have h4 : q ⟨_, hmem⟩ = q w := by
        apply Multiplicative.toAdd.injective
        rw [h1, hw]
        exact h2.symm
      exact congrArg Subtype.val (hqi h4)
    have hwV₁ := hfix w w.2 hwP
    have hlw : l * (w : G) * l⁻¹ = w := by
      rw [← Subgroup.mem_centralizer_iff.mp (hL₁ hl) w hwV₁, mul_inv_cancel_right]
    have hmem : l * (w : G) * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV (hL₁L hl)) w).mp w.2
    have h1 := hqeq l (hL₁L hl) w ⟨_, hmem⟩ rfl
    have h5 : (⟨l * (w : G) * l⁻¹, hmem⟩ : ↥V) = w := Subtype.ext hlw
    rw [h5, hw] at h1
    exact h1.symm
  intro l hl
  have hu : l * u₀ * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLU (hL₁L hl)) u₀).mp hu₀
  have hβeq : β ⟨_, hu⟩ = β ⟨u₀, hu₀⟩ := by
    apply Multiplicative.toAdd.injective
    funext j
    rw [hβ ⟨l, hL₁L hl⟩ ⟨u₀, hu₀⟩ ⟨_, hu⟩ rfl j]
    exact hcoord j l hl
  exact congrArg Subtype.val (hβi hβeq)

end CFSG.Quasithin.Vol2.Ch11.SecA
