module

public import CFSG.Permutation.UnitaryThreeRecognition.Basic

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

abbrev SwapSet (G : Type*) [Group G] [MulAction G Ω] (j : G) (a b : Ω) : Type _ :=
  {g : G // j • (g • a) = g • b}

abbrev ConjSwap (G : Type*) [Group G] [MulAction G Ω] (j : G) (a b : Ω) : Type _ :=
  {h : G // (∃ k : G, h = k⁻¹ * j * k) ∧ h • a = b}

theorem card_swapSet_eq_pairStab_mul [Finite G] [Finite Ω] {a b : Ω} (hab : a ≠ b)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w) (j : G) :
    Nat.card (SwapSet G j a b) =
      Nat.card (pairStab G a b) * Nat.card {x : Ω // j • x ≠ x} := by
  classical
  have hpre : ∀ x : {x : Ω // j • x ≠ x}, ∃ g : G, g • a = x.1 ∧ g • b = j • x.1 :=
    fun x => htwo hab (fun h => x.2 h.symm)
  choose rep hrep using hpre
  have hne : ∀ g : SwapSet G j a b, j • ((g : G) • a) ≠ (g : G) • a := by
    intro g
    rw [g.2]
    intro h
    have := congrArg ((g : G)⁻¹ • ·) h
    simp only [inv_smul_smul] at this
    exact hab this.symm
  let pt : SwapSet G j a b → {x : Ω // j • x ≠ x} := fun g => ⟨(g : G) • a, hne g⟩
  have hmem : ∀ g : SwapSet G j a b, (rep (pt g))⁻¹ * g ∈ pairStab G a b := by
    intro g
    refine ⟨?_, ?_⟩
    · change ((rep (pt g))⁻¹ * (g : G)) • a = a
      rw [mul_smul, inv_smul_eq_iff, (hrep (pt g)).1]
    · change ((rep (pt g))⁻¹ * (g : G)) • b = b
      rw [mul_smul, inv_smul_eq_iff, (hrep (pt g)).2, ← g.2]
  have hψmem : ∀ p : pairStab G a b × {x : Ω // j • x ≠ x},
      j • ((rep p.2 * p.1 : G) • a) = (rep p.2 * p.1 : G) • b := by
    rintro ⟨t, x⟩
    rw [mul_smul, mul_smul, t.property.1, t.property.2, (hrep x).1, (hrep x).2]
  let φ : SwapSet G j a b → pairStab G a b × {x : Ω // j • x ≠ x} := fun g =>
    (⟨(rep (pt g))⁻¹ * g, hmem g⟩, pt g)
  let ψ : pairStab G a b × {x : Ω // j • x ≠ x} → SwapSet G j a b := fun p =>
    ⟨rep p.2 * p.1, hψmem p⟩
  have hpt : ∀ p : pairStab G a b × {x : Ω // j • x ≠ x}, pt (ψ p) = p.2 := by
    rintro ⟨t, x⟩
    apply Subtype.ext
    change (rep x * (t : G)) • a = x.1
    rw [mul_smul, t.property.1, (hrep x).1]
  have hφψ : ∀ p, φ (ψ p) = p := by
    intro p
    have h2 := hpt p
    refine Prod.ext ?_ h2
    apply Subtype.ext
    change (rep (pt (ψ p)))⁻¹ * (rep p.2 * p.1 : G) = p.1
    rw [h2]
    group
  have hψφ : ∀ g, ψ (φ g) = g := by
    intro g
    apply Subtype.ext
    change rep (pt g) * ((rep (pt g))⁻¹ * (g : G)) = g
    group
  rw [← Nat.card_prod]
  exact Nat.card_congr ⟨φ, ψ, hψφ, hφψ⟩

theorem card_swapSet_eq_centralizer_mul [Finite G] (a b : Ω) (j : G) :
    Nat.card (SwapSet G j a b) =
      Nat.card (Subgroup.centralizer ({j} : Set G)) * Nat.card (ConjSwap G j a b) := by
  classical
  have hpre : ∀ h : ConjSwap G j a b, ∃ k : G, h.1 = k⁻¹ * j * k := fun h => h.2.1
  choose rep hrep using hpre
  have hrepS : ∀ h : ConjSwap G j a b, j • (rep h • a) = rep h • b := by
    intro h
    have h2 : ((rep h)⁻¹ * j * rep h) • a = b := by rw [← hrep h]; exact h.2.2
    have := congrArg (rep h • ·) h2
    simp only [mul_smul, smul_inv_smul] at this
    exact this
  have memC : ∀ c : G, c ∈ Subgroup.centralizer ({j} : Set G) ↔ c * j = j * c := by
    intro c
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  let cj : SwapSet G j a b → ConjSwap G j a b := fun g =>
    ⟨(g : G)⁻¹ * j * g, ⟨g, rfl⟩, by rw [mul_smul, mul_smul, g.2, inv_smul_smul]⟩
  have hcmem : ∀ g : SwapSet G j a b,
      (g : G) * (rep (cj g))⁻¹ ∈ Subgroup.centralizer ({j} : Set G) := by
    intro g
    rw [memC]
    have e : (g : G)⁻¹ * j * g = (rep (cj g))⁻¹ * j * rep (cj g) := hrep (cj g)
    have : j = ((g : G) * (rep (cj g))⁻¹) * j * ((g : G) * (rep (cj g))⁻¹)⁻¹ := by
      calc j = g * ((g : G)⁻¹ * j * g) * (g : G)⁻¹ := by group
        _ = g * ((rep (cj g))⁻¹ * j * rep (cj g)) * (g : G)⁻¹ := by rw [e]
        _ = ((g : G) * (rep (cj g))⁻¹) * j * ((g : G) * (rep (cj g))⁻¹)⁻¹ := by group
    calc ((g : G) * (rep (cj g))⁻¹) * j
        = ((g : G) * (rep (cj g))⁻¹) * j * ((g : G) * (rep (cj g))⁻¹)⁻¹ *
            ((g : G) * (rep (cj g))⁻¹) := by group
      _ = j * ((g : G) * (rep (cj g))⁻¹) := by rw [← this]
  have hΨmem : ∀ p : Subgroup.centralizer ({j} : Set G) × ConjSwap G j a b,
      j • ((p.1 * rep p.2 : G) • a) = (p.1 * rep p.2 : G) • b := by
    rintro ⟨c, h⟩
    have hc : (c : G) * j = j * c := (memC c).mp c.property
    change j • (((c : G) * rep h) • a) = ((c : G) * rep h) • b
    rw [mul_smul, mul_smul, ← mul_smul j, ← hc, mul_smul, hrepS h]
  let Φ : SwapSet G j a b → Subgroup.centralizer ({j} : Set G) × ConjSwap G j a b :=
    fun g => (⟨g * (rep (cj g))⁻¹, hcmem g⟩, cj g)
  let Ψ : Subgroup.centralizer ({j} : Set G) × ConjSwap G j a b → SwapSet G j a b :=
    fun p => ⟨p.1 * rep p.2, hΨmem p⟩
  have hcj : ∀ p, cj (Ψ p) = p.2 := by
    rintro ⟨c, h⟩
    apply Subtype.ext
    have hc : (c : G) * j = j * c := (memC c).mp c.property
    change ((c : G) * rep h)⁻¹ * j * (c * rep h) = h.1
    rw [hrep h]
    calc ((c : G) * rep h)⁻¹ * j * (c * rep h)
        = (rep h)⁻¹ * ((c : G)⁻¹ * ((c : G) * j)) * rep h := by rw [hc]; group
      _ = (rep h)⁻¹ * j * rep h := by group
  have hΦΨ : ∀ p, Φ (Ψ p) = p := by
    intro p
    have h2 := hcj p
    refine Prod.ext ?_ h2
    apply Subtype.ext
    change (p.1 * rep p.2 : G) * (rep (cj (Ψ p)))⁻¹ = p.1
    rw [h2]
    group
  have hΨΦ : ∀ g, Ψ (Φ g) = g := by
    intro g
    apply Subtype.ext
    change (g : G) * (rep (cj g))⁻¹ * rep (cj g) = g
    group
  rw [← Nat.card_prod]
  exact Nat.card_congr ⟨Φ, Ψ, hΨΦ, hΦΨ⟩

end CFSG.UnitaryThreeRecognition
