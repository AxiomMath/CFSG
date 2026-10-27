module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF8
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayer
import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19

section Plain

theorem exists_sl2_involution {k : Type*} [Field k] (h2 : (2 : k) = 0) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) k, t ^ 2 = 1 ∧ t ≠ 1 := by
  have h2' : (1 : k) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  let t : Matrix.SpecialLinearGroup (Fin 2) k := ⟨!![1, 1; 0, 1], by simp⟩
  refine ⟨t, ?_, ?_⟩
  · apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [t, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | exact h2' | done
  · intro h
    have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) k =>
      (y : Matrix (Fin 2) (Fin 2) k) 0 1) h
    simp [t] at this

theorem mem_centralizer_conj_iff {G : Type*} [Group G] (g a k : G) :
    k ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set G) ↔
      g⁻¹ * k * g ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * k * g * a = g⁻¹ * (k * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * k) * g := by rw [h]
      _ = a * (g⁻¹ * k * g) := by group
  · intro h
    calc k * (g * a * g⁻¹) = g * ((g⁻¹ * k * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * k * g)) * g⁻¹ := by rw [h]
      _ = (g * a * g⁻¹) * k := by group

theorem centralizer_le_of_mem_zpowers {G : Type*} [Group G] {a b : G}
    (h : a ∈ Subgroup.zpowers b) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
  exact (Commute.zpow_right (show Commute k b from hk) m).eq

theorem zpowers_eq_of_mem_zpowers_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a b : G}
    (ha : a ^ p = 1) (ha1 : a ≠ 1) (hb : b ^ p = 1) (hb1 : b ≠ 1) (h : a ∈ Subgroup.zpowers b) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  have hcard : Nat.card (Subgroup.zpowers b) = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hb hb1]
  have hcarda : Nat.card (Subgroup.zpowers a) = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]
  haveI : Finite (Subgroup.zpowers b) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  exact Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr h) (by rw [hcard, hcarda])

theorem commutator_self_le {G : Type*} [Group G] (C : Subgroup G) : ⁅C, C⁆ ≤ C := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

end Plain

section ClassX


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem three_conj_dichotomy (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x : C0 σ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    IsClassX σ x ∨ ∃ g : C0 σ, g * x * g⁻¹ ∈ Bsub σ := by
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds X (2 ^ n) σ hX hσ h3 x hx3 hx1
  rcases hg with hA | hB
  · exact Or.inl ⟨hx3, hx1, g, hA⟩
  · exact Or.inr ⟨g, hB⟩

theorem IsClassX.conj_mem {x : C0 σ} (hx : IsClassX σ x) (h : C0 σ) :
    IsClassX σ (h * x * h⁻¹) := by
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  refine ⟨?_, ?_, g * h⁻¹, ?_⟩
  · rw [conj_pow, hx3]; group
  · intro e
    apply hx1
    have := congrArg (fun y => h⁻¹ * y * h) e
    simpa [mul_assoc] using this
  · have : g * h⁻¹ * (h * x * h⁻¹) * (g * h⁻¹)⁻¹ = g * x * g⁻¹ := by group
    rw [this]; exact hg

theorem classX_conj {n : ℕ} (P : D4Par n X σ) {x z : C0 σ} (hx : IsClassX σ x)
    (hz : IsClassX σ z) : ∃ g : C0 σ, g * x * g⁻¹ = z := by
  obtain ⟨hx3, hx1, u, hu⟩ := hx
  obtain ⟨hz3, hz1, v, hv⟩ := hz
  have hux3 : (u * x * u⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  have hvz3 : (v * z * v⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3]; group
  have hux1 : u * x * u⁻¹ ≠ 1 := fun e => hx1 (by
    have := congrArg (fun y => u⁻¹ * y * u) e
    simpa [mul_assoc] using this)
  have hvz1 : v * z * v⁻¹ ≠ 1 := fun e => hz1 (by
    have := congrArg (fun y => v⁻¹ * y * v) e
    simpa [mul_assoc] using this)
  obtain ⟨a, -, ha⟩ := exists_conj_Asub P hu hux3 hux1 hv hvz3 hvz1
  refine ⟨v⁻¹ * a * u, ?_⟩
  have : v⁻¹ * a * u * x * (v⁻¹ * a * u)⁻¹ = v⁻¹ * (a * (u * x * u⁻¹) * a⁻¹) * v := by group
  rw [this, ha]; group

theorem classX_even_centralizer {n : ℕ} (P : D4Par n X σ) {x : C0 σ} (hx : IsClassX σ x) :
    Even (Nat.card (Subgroup.centralizer ({x} : Set (C0 σ)))) := by
  haveI := P.charP
  have hK : ringChar X = 2 := ringChar.eq X 2
  have h2 : (2 : fixSubfield σ) = 0 := KFacts.two_eq_zero_fixSubfield σ hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht2, ht1⟩ := exists_sl2_involution h2
  set b : Bsub σ := bsubEquiv P t with hbdef
  have hb2 : b ^ 2 = 1 := by rw [hbdef, ← map_pow, ht2, map_one]
  have hb1 : b ≠ 1 := fun h => ht1 ((bsubEquiv P).injective (by rw [← hbdef, h, map_one]))
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hcomm : (g * x * g⁻¹) * (b : C0 σ) = (b : C0 σ) * (g * x * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp b.2 _ hg
  have hu : g⁻¹ * (b : C0 σ) * g ∈ Subgroup.centralizer ({x} : Set (C0 σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : g⁻¹ * (b : C0 σ) * g * x = x * (g⁻¹ * (b : C0 σ) * g) := by
      have h1 : (b : C0 σ) * (g * x * g⁻¹) = (g * x * g⁻¹) * b := hcomm.symm
      calc g⁻¹ * (b : C0 σ) * g * x = g⁻¹ * ((b : C0 σ) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * b) * g := by rw [h1]
        _ = x * (g⁻¹ * (b : C0 σ) * g) := by group
    exact this
  have hord : orderOf (⟨g⁻¹ * (b : C0 σ) * g, hu⟩ :
      Subgroup.centralizer ({x} : Set (C0 σ))) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      show (g⁻¹ * (b : C0 σ) * g) ^ 2 = 1
      have hb2' : ((b : C0 σ)) ^ 2 = 1 := by
        have := congrArg (fun y : Bsub σ => (y : C0 σ)) hb2
        simpa using this
      have : (g⁻¹ * (b : C0 σ) * g) ^ 2 = g⁻¹ * (b : C0 σ) ^ 2 * g := by
        rw [pow_two, pow_two]; group
      rw [this, hb2']
      group
    · intro h
      apply hb1
      apply Subtype.ext
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      have h3 : (b : C0 σ) = g * (g⁻¹ * (b : C0 σ) * g) * g⁻¹ := by group
      have hb_one : (b : C0 σ) = 1 := by rw [h3, this]; group
      simpa using hb_one
  exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)

theorem classX_centralizer_inj {n : ℕ} (P : D4Par n X σ) (hn : 2 ≤ n) {x₁ x₂ : C0 σ}
    (h1 : IsClassX σ x₁) (h2 : IsClassX σ x₂)
    (hc : Subgroup.centralizer ({x₁} : Set (C0 σ)) = Subgroup.centralizer ({x₂} : Set (C0 σ))) :
    Subgroup.zpowers x₁ = Subgroup.zpowers x₂ := by
  obtain ⟨-, hz⟩ := classX_layer σ P hn h1
  obtain ⟨hx2D, -⟩ := classX_layer σ P hn h2
  rw [← hc] at hx2D
  have hD : ⁅Subgroup.centralizer ({x₁} : Set (C0 σ)), Subgroup.centralizer ({x₁} : Set (C0 σ))⁆ ≤
      Subgroup.centralizer ({x₁} : Set (C0 σ)) := commutator_self_le _
  have hx2 : x₂ ∈ Subgroup.zpowers x₁ := by
    refine hz x₂ hx2D h2.1 (fun d hd => ?_)
    have hd2 : d ∈ Subgroup.centralizer ({x₂} : Set (C0 σ)) := hc ▸ hD hd
    exact (Subgroup.mem_centralizer_singleton_iff.mp hd2).symm
  exact (zpowers_eq_of_mem_zpowers_prime Nat.prime_three h2.1 h2.2.1 h1.1 h1.2.1 hx2).symm

end ClassX

end CFSG.RankThree.PartTwo.Sec19
