module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Additive
public import CFSG.ClassicalGroups.F2Fixed

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed

section Alg

variable {Γ M : Type*} [Group Γ] [AddCommGroup M] [DistribMulAction Γ M]

theorem comm_range_le_fixedSub (h2 : ∀ m : M, m + m = 0) {x : Γ} (hx : ∀ m : M, x • x • m = m) :
    (comm M x).range ≤ fixedSub M {x} := by
  rintro _ ⟨m, rfl⟩ g hg
  rw [Set.mem_singleton_iff.mp hg, comm_apply, smul_sub, hx, sub_eq_add_of_exp2 h2 (x • m) m,
    sub_eq_add_of_exp2 h2 m (x • m), add_comm]

theorem range_comm_facts [Finite M] (h2 : ∀ m : M, m + m = 0) (V A : AddSubgroup M) (x : Γ)
    (hVA : V ≤ A) (hV : ∀ v ∈ V, x • v = v) (hxsq : ∀ m : M, x • x • m = m)
    (hfull : ∀ a ∈ A, ∃ m : M, a - (x • m - m) ∈ V)
    (hcard : Nat.card ↥A ^ 2 = Nat.card M * Nat.card ↥V) :
    fixedSub M {x} = A ∧ (comm M x).range ≤ A ∧ (comm M x).range ⊔ V = A ∧
      (comm M x).range ⊓ V = ⊥ := by
  set R : AddSubgroup M := (comm M x).range with hR
  set K : AddSubgroup M := fixedSub M {x} with hK
  have hRK : R ≤ K := comm_range_le_fixedSub h2 hxsq
  have hVK : V ≤ K := fun v hv g hg => by rw [Set.mem_singleton_iff.mp hg]; exact hV v hv
  have hAR : A ≤ R ⊔ V := by
    intro a ha
    obtain ⟨m, hm⟩ := hfull a ha
    have : a = (x • m - m) + (a - (x • m - m)) := by abel
    rw [this]
    exact AddSubgroup.add_mem_sup ⟨m, rfl⟩ hm
  have hAK : A ≤ K := hAR.trans (sup_le hRK hVK)
  have hMK : Nat.card M = Nat.card ↥K * Nat.card ↥R := card_eq_card_fixedSub_mul_card_range x
  have hprod := card_sup_mul_card_inf_addSubgroup R V
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hAle : Nat.card ↥A ≤ Nat.card ↥(R ⊔ V) := Nat.card_mono (Set.toFinite _) hAR
  have hRV : Nat.card ↥(R ⊔ V) ≤ Nat.card ↥R * Nat.card ↥V := by
    rw [← hprod]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hKA : Nat.card ↥K ≤ Nat.card ↥A := by
    have h1 : Nat.card ↥K * Nat.card ↥A ≤ Nat.card ↥A * Nat.card ↥A := by
      calc Nat.card ↥K * Nat.card ↥A ≤ Nat.card ↥K * (Nat.card ↥R * Nat.card ↥V) :=
            Nat.mul_le_mul_left _ (hAle.trans hRV)
        _ = Nat.card M * Nat.card ↥V := by rw [hMK]; ring
        _ = Nat.card ↥A * Nat.card ↥A := by rw [← sq, hcard]
    exact Nat.le_of_mul_le_mul_right h1 hApos
  have hKeq : A = K := AddSubgroup.eq_of_le_of_card_ge hAK hKA
  have hRA : R ≤ A := hKeq ▸ hRK
  have hsupA : R ⊔ V = A := le_antisymm (sup_le hRA hVA) hAR
  refine ⟨hKeq.symm, hRA, hsupA, ?_⟩
  have hinf1 : Nat.card ↥(R ⊓ V) = 1 := by
    have h3 : Nat.card ↥A * Nat.card ↥(R ⊓ V) = Nat.card ↥R * Nat.card ↥V := by
      rw [← hsupA]; exact hprod
    have h4 : Nat.card ↥A * Nat.card ↥A * Nat.card ↥(R ⊓ V) =
        Nat.card ↥A * Nat.card ↥A * 1 := by
      calc Nat.card ↥A * Nat.card ↥A * Nat.card ↥(R ⊓ V)
          = Nat.card ↥A * (Nat.card ↥A * Nat.card ↥(R ⊓ V)) := by ring
        _ = Nat.card ↥A * (Nat.card ↥R * Nat.card ↥V) := by rw [h3]
        _ = (Nat.card ↥K * Nat.card ↥R) * Nat.card ↥V := by rw [hKeq]; ring
        _ = Nat.card M * Nat.card ↥V := by rw [hMK]
        _ = Nat.card ↥A * Nat.card ↥A * 1 := by rw [← sq, hcard, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hApos hApos) h4
  exact AddSubgroup.card_eq_one.mp hinf1

theorem exists_complement_of_full_commutators [Finite M] (h2 : ∀ m : M, m + m = 0)
    (V A₁ A₂ : AddSubgroup M) (L₁ L₂ : Set Γ) (x₁ x₂ : Γ)
    (hV : ∀ g : Γ, ∀ v ∈ V, g • v = v) (hVA₁ : V ≤ A₁) (hVA₂ : V ≤ A₂)
    (hinf : A₁ ⊓ A₂ = V) (hsup : A₁ ⊔ A₂ = ⊤)
    (hx₁sq : ∀ m : M, x₁ • x₁ • m = m) (hx₂sq : ∀ m : M, x₂ • x₂ • m = m)
    (hx₁full : ∀ a ∈ A₁, ∃ m : M, a - (x₁ • m - m) ∈ V)
    (hx₂full : ∀ a ∈ A₂, ∃ m : M, a - (x₂ • m - m) ∈ V)
    (hcard₁ : Nat.card ↥A₁ ^ 2 = Nat.card M * Nat.card ↥V)
    (hcard₂ : Nat.card ↥A₂ ^ 2 = Nat.card M * Nat.card ↥V)
    (hK₁ : ∀ l ∈ L₁, ∀ m : M, ∃ m' : M, l • m - m = x₁ • m' - m')
    (hK₂ : ∀ l ∈ L₂, ∀ m : M, ∃ m' : M, l • m - m = x₂ • m' - m') :
    ∃ Y : AddSubgroup M, Y ⊓ V = ⊥ ∧ Y ⊔ V = ⊤ ∧ ∀ l ∈ L₁ ∪ L₂, ∀ y ∈ Y, l • y ∈ Y := by
  obtain ⟨-, hR₁A, hR₁sup, hR₁inf⟩ := range_comm_facts h2 V A₁ x₁ hVA₁ (hV x₁) hx₁sq hx₁full
    hcard₁
  obtain ⟨-, hR₂A, hR₂sup, hR₂inf⟩ := range_comm_facts h2 V A₂ x₂ hVA₂ (hV x₂) hx₂sq hx₂full
    hcard₂
  set R₁ : AddSubgroup M := (comm M x₁).range with hR₁
  set R₂ : AddSubgroup M := (comm M x₂).range with hR₂
  have hmemR₁ : ∀ m m' : M, x₁ • m' - m' = m → m ∈ R₁ := fun m m' h => ⟨m', h⟩
  have hmemR₂ : ∀ m m' : M, x₂ • m' - m' = m → m ∈ R₂ := fun m m' h => ⟨m', h⟩
  refine ⟨R₁ ⊔ R₂, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyY, hyV⟩ := hy
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := AddSubgroup.mem_sup.mp hyY
    have hr₂A₁ : r₂ ∈ A₁ := by
      have : r₂ = (r₁ + r₂) - r₁ := by abel
      rw [this]
      exact A₁.sub_mem (hVA₁ hyV) (hR₁A hr₁)
    have hr₂V : r₂ ∈ V := by rw [← hinf]; exact ⟨hr₂A₁, hR₂A hr₂⟩
    have hr₂0 : r₂ = 0 := by
      have : r₂ ∈ R₂ ⊓ V := ⟨hr₂, hr₂V⟩
      rw [hR₂inf] at this
      exact this
    subst hr₂0
    have hr₁V : r₁ ∈ V := by simpa using hyV
    have : r₁ ∈ R₁ ⊓ V := ⟨hr₁, hr₁V⟩
    rw [hR₁inf] at this
    have h0 : r₁ = 0 := this
    simp [h0]
  · rw [eq_top_iff, ← hsup]
    have h1 : A₁ ≤ (R₁ ⊔ R₂) ⊔ V := by
      rw [← hR₁sup]
      exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
    have h2' : A₂ ≤ (R₁ ⊔ R₂) ⊔ V := by
      rw [← hR₂sup]
      exact sup_le (le_sup_of_le_left le_sup_right) le_sup_right
    exact sup_le h1 h2'
  · intro l hl y hy
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := AddSubgroup.mem_sup.mp hy
    rcases hl with hl | hl
    · obtain ⟨c₁, hc₁⟩ := hK₁ l hl r₁
      obtain ⟨c₂, hc₂⟩ := hK₁ l hl r₂
      have e : l • (r₁ + r₂) = (r₁ + (x₁ • c₁ - c₁)) + r₂ + (x₁ • c₂ - c₂) := by
        rw [smul_add, ← hc₁, ← hc₂]; abel
      rw [e]
      exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left
        (AddSubgroup.add_mem _ hr₁ (hmemR₁ _ c₁ rfl))) (AddSubgroup.mem_sup_right hr₂))
        (AddSubgroup.mem_sup_left (hmemR₁ _ c₂ rfl))
    · obtain ⟨c₁, hc₁⟩ := hK₂ l hl r₁
      obtain ⟨c₂, hc₂⟩ := hK₂ l hl r₂
      have e : l • (r₁ + r₂) = r₁ + (x₂ • c₁ - c₁) + (r₂ + (x₂ • c₂ - c₂)) := by
        rw [smul_add, ← hc₁, ← hc₂]; abel
      rw [e]
      exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left hr₁)
        (AddSubgroup.mem_sup_right (hmemR₂ _ c₁ rfl)))
        (AddSubgroup.mem_sup_right (AddSubgroup.add_mem _ hr₂ (hmemR₂ _ c₂ rfl)))

end Alg

end CFSG.RankThree.GF2n.Stroth80
