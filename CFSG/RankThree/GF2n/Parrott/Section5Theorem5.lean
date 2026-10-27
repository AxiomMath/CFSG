module

public import CFSG.RankThree.GF2n.Parrott.Section5Simple
public import CFSG.RankThree.GF2n.Parrott.Section5Lemma52
public import CFSG.RankThree.GF2n.Parrott.Section5Lemma54Fusion
public import CFSG.RankThree.GF2n.Parrott.Section5Lemma54Orbits
public import CFSG.RankThree.GF2n.Parrott.Section5Lemma57T1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem mul_self_eq_one_of_parrottHyp (h : Tim79a.ParrottHyp z) : z * z = 1 := by
  have hz := pow_orderOf_eq_one z
  rwa [h.1, pow_two] at hz

private theorem ne_one_of_parrottHyp (h : Tim79a.ParrottHyp z) : z ≠ 1 := by
  intro hz
  have hordz : orderOf z = 2 := h.1
  rw [hz, orderOf_one] at hordz
  exact absurd hordz (by norm_num)

private theorem mul_comm_of_mem_centerIn_J (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) : z * z₁ = z₁ * z :=
  (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) z₁ (J_le_H hz₁.1)).symm

private theorem orbit23_facts {W : Subgroup G} {O : Fin 7 → Finset G}
    (hW2 : ∀ a ∈ W, a * a = 1)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    {a : G} (haO : a ∈ O 2 ∨ a ∈ O 3) :
    a ∈ W ∧ a ≠ 1 ∧ a ∈ J z ∧ orderOf a = 2 ∧ a ∉ O 0 ∧ a ∉ O 1 := by
  have hnot0 : a ∉ O 0 := by
    rcases haO with h2 | h3
    · exact fun h => Finset.disjoint_left.mp (hdisj 2 0 (by decide)) h2 h
    · exact fun h => Finset.disjoint_left.mp (hdisj 3 0 (by decide)) h3 h
  have hnot1 : a ∉ O 1 := by
    rcases haO with h2 | h3
    · exact fun h => Finset.disjoint_left.mp (hdisj 2 1 (by decide)) h2 h
    · exact fun h => Finset.disjoint_left.mp (hdisj 3 1 (by decide)) h3 h
  rcases haO with h2 | h3
  · refine ⟨(hOW 2 a h2).1, (hOW 2 a h2).2, hJ 2 (by norm_num) a h2, ?_, hnot0, hnot1⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2)
      (by simpa [pow_two] using hW2 a (hOW 2 a h2).1) (hOW 2 a h2).2
  · refine ⟨(hOW 3 a h3).1, (hOW 3 a h3).2, hJ 3 (by norm_num) a h3, ?_, hnot0, hnot1⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2)
      (by simpa [pow_two] using hW2 a (hOW 3 a h3).1) (hOW 3 a h3).2

private theorem not_isConj_z1_of_mem_orbits [DecidableEq G]
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hK : ∀ j ∈ J z, orderOf j = 2 → j ∉ centerIn (J z) →
      ∀ K : Subgroup G, IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)) →
        Nat.card K = 2 ^ 16 ∧ centerIn K = Subgroup.closure {z, j})
    {O : Fin 7 → Finset G} {a : G} (hO1 : O 1 = {z₁, z₁ * z})
    (haJ : a ∈ J z) (ha2 : orderOf a = 2) (hnot1 : a ∉ O 1)
    (hzz₁ : z * z₁ = z₁ * z) : ¬ IsConj z₁ a := by
  have haz₁ : a ≠ z₁ := by
    intro heq
    apply hnot1
    rw [hO1, heq]
    simp
  have hazz₁ : a ≠ z * z₁ := by
    intro heq
    apply hnot1
    rw [hO1, heq, hzz₁]
    simp
  exact not_isConj_z1_of_mem_J h hZ hz₁ hz₁z hord hK haJ ha2 haz₁ hazz₁

private theorem mul_z_mem_J_not_centerIn [DecidableEq G] (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {O : Fin 7 → Finset G} (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hO2z : ∀ a ∈ O 2, a * z ∈ O 2) (hO3z : ∀ a ∈ O 3, a * z ∈ O 3)
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    {a : G} (haO : a ∈ O 2 ∨ a ∈ O 3) (ha1 : a ≠ 1) (hnot0 : a ∉ O 0)
    (hnot1 : a ∉ O 1) (hzz₁ : z * z₁ = z₁ * z) :
    a * z ∈ J z ∧ a * z ∉ centerIn (J z) := by
  have hzz : z * z = 1 := mul_self_eq_one_of_parrottHyp h
  refine ⟨?_, ?_⟩
  · rcases haO with h2 | h3
    · exact hJ 2 (by norm_num) (a * z) (hO2z a h2)
    · exact hJ 3 (by norm_num) (a * z) (hO3z a h3)
  · intro hmem
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hmem with h1 | h1 | h1 | h1
    · apply hnot0
      have haz : a = z := by
        calc a = (a * z) * z := by rw [mul_assoc, hzz, mul_one]
          _ = 1 * z := by rw [h1]
          _ = z := one_mul z
      rw [hO0, haz]
      simp
    · exact ha1 (by
        have h := congrArg (fun x => x * z) h1
        simpa [mul_assoc, hzz] using h)
    · apply hnot1
      rw [hO1]
      have haz : a = z₁ * z := by
        calc a = (a * z) * z := by rw [mul_assoc, hzz, mul_one]
          _ = z₁ * z := by rw [h1]
      rw [haz]
      simp
    · apply hnot1
      rw [hO1]
      have haz : a = z₁ := by
        calc a = (a * z) * z := by rw [mul_assoc, hzz, mul_one]
          _ = (z * z₁) * z := by rw [h1]
          _ = z₁ := by rw [hzz₁, mul_assoc, hzz, mul_one]
      rw [haz]
      simp

private theorem conj_z_data_of_mem_normalizer (h : Tim79a.ParrottHyp z) {z₁ σ g : G}
    {W T₂ : Subgroup G} (hz₁ : z₁ ∈ centerIn (J z))
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G))) (hWT : W ≤ T₂)
    {O : Fin 7 → Finset G} (hO0 : O 0 = {z})
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hgN : g ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G))
    (hgz₁ : g * z₁ * g⁻¹ = z₁) (hgH : g ∉ H z) :
    g ∈ centralizer ({z₁} : Set G) ∧
      g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G) ∧ g * z * g⁻¹ ≠ z := by
  have hgC : g ∈ centralizer ({z₁} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z₁ = (g * z₁ * g⁻¹) * g := by group
      _ = z₁ * g := by rw [hgz₁]
  have hzC : z ∈ centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) z₁ (J_le_H hz₁.1)).symm
  have hzW : z ∈ W := by
    have hzO0 : z ∈ O 0 := by rw [hO0]; simp
    exact (hOW 0 z hzO0).1
  have hgzW : g * z * g⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp hgN.1 z).mp hzW
  have hgzH : g * z * g⁻¹ ∈ H z := (hT₂.le (hWT hgzW)).1
  have hgzC : g * z * g⁻¹ ∈ centralizer ({z₁} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC hzC) (Subgroup.inv_mem _ hgC)
  have hgz : g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hgzH, hgzC⟩
  have hgz' : g * z * g⁻¹ ≠ z := by
    intro heq
    apply hgH
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [heq]
  exact ⟨hgC, hgz, hgz'⟩

private theorem conj_mem_centralizer_z1_of_conj {z₁ b n y : G}
    (hn : n * z₁ * n⁻¹ = b) (hy : y ∈ centralizer ({b} : Set G)) :
    n⁻¹ * y * (n⁻¹)⁻¹ ∈ centralizer ({z₁} : Set G) := by
  have hbC : b * y = y * b := (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hz₁b : z₁ = n⁻¹ * b * n := by
    calc z₁ = n⁻¹ * (n * z₁ * n⁻¹) * n := by group
      _ = n⁻¹ * b * n := by rw [hn]
  rw [Subgroup.mem_centralizer_singleton_iff, inv_inv]
  calc (n⁻¹ * y * n) * z₁ = n⁻¹ * (y * b) * n := by rw [hz₁b]; group
    _ = n⁻¹ * (b * y) * n := by rw [hbC]
    _ = z₁ * (n⁻¹ * y * n) := by rw [hz₁b]; group

private theorem isConj_of_mem_O4 {σ : G} {W : Subgroup G} {O : Fin 7 → Finset G}
    (hc1 : ∀ a ∈ O 4, ∃ n ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G),
      n * z * n⁻¹ = a)
    {a : G} (ha : a ∈ O 4) : IsConj z a := by
  obtain ⟨n, -, hnz⟩ := hc1 a ha
  exact isConj_iff.mpr ⟨n, hnz⟩

private theorem centerIn_S₀_conj_z_eq (h : Tim79a.ParrottHyp z) {σ : G}
    {T₂ W S₀ : Subgroup G} {O : Fin 7 → Finset G}
    (hP4 : ∀ t ∈ H z ⊓ centralizer ({σ} : Set G), orderOf t = 2 → IsConj z t →
      ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G)))
    (hWT : W ≤ T₂) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hW2 : ∀ a ∈ W, a * a = 1) (hWc : Nat.card W = 32)
    (hWu : ∀ E : Subgroup G, E ≤ T₂ → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E = 32 → E = W)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hZS₀ : ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e ∈ O 5 ∨ e ∈ O 6)
    (hc3 : ∀ a, a ∈ O 5 ∨ a ∈ O 6 →
      ∀ n ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G), n * z * n⁻¹ ≠ a) :
    ∀ e ∈ centerIn S₀, IsConj z e → e = z := by
  intro e he hconj
  rcases hZS₀ e he with h1 | h1 | h1 | h1
  · exfalso
    exact ne_one_of_parrottHyp h (isConj_one_left.mp (h1 ▸ hconj))
  · exact h1
  · exfalso
    obtain ⟨n, hnN, hnz⟩ :=
      exists_normalizer_conj_of_mem_W h hP4 hT₂ hWT hWab hW2 hWc hWu (hOW 5 e h1).1 hconj
    exact hc3 e (Or.inl h1) n hnN hnz
  · exfalso
    obtain ⟨n, hnN, hnz⟩ :=
      exists_normalizer_conj_of_mem_W h hP4 hT₂ hWT hWab hW2 hWc hWu (hOW 6 e h1).1 hconj
    exact hc3 e (Or.inr h1) n hnN hnz

section Certified

theorem parrott_theorem5 [DecidableEq G] (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hHO : centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2)
    (hT2 : (∃ g ∈ centralizer ({z₁} : Set G),
        g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G) ∧ g * z * g⁻¹ ≠ z) →
      ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal)
        (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥(centralizer ({z₁} : Set G)) ⧸
            (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X))
    (hK : ∀ j ∈ J z, orderOf j = 2 → j ∉ centerIn (J z) →
      ∀ K : Subgroup G, IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)) →
        Nat.card K = 2 ^ 16 ∧ centerIn K = Subgroup.closure {z, j})
    {σ₁ σ σ₃ w w₁ : G} {T₁ T₂ T₃ : Subgroup G}
    (hσ₁ : orderOf σ₁ = 3) (hσ₁H : σ₁ ∈ H z) (hσ : orderOf σ = 3) (hσH : σ ∈ H z)
    (hcls : ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ h ∈ H z, CFSG.conjugate R h = zpowers σ₁ ∨ CFSG.conjugate R h = zpowers σ ∨
        CFSG.conjugate R h = zpowers σ₃)
    (hwH : w ∈ H z) (hw : w * σ * w⁻¹ = σ⁻¹) (hw₁H : w₁ ∈ H z) (hw₁ : w₁ * σ₁ * w₁⁻¹ = σ₁⁻¹)
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ centralizer ({σ₁} : Set G))) (hT₁c : Nat.card T₁ = 2 ^ 7)
    (hZ₁ : Nat.card (centerIn T₁) = 8) (hZ₁e : ∀ x ∈ centerIn T₁, x * x = 1)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G))) (hT₂c : Nat.card T₂ = 2 ^ 8)
    (hZ₂ : centerIn T₂ = zpowers z)
    (hT₃ : IsSylowOf 2 T₃ (H z ⊓ centralizer ({σ₃} : Set G))) (hz₃ : z ∈ ⁅T₃, T₃⁆)
    (hT₂₃ : ∀ y : G, y ∈ ⁅T₂ ⊓ centralizer ({y} : Set G), T₂ ⊓ centralizer ({y} : Set G)⁆ →
      Nat.card T₃ < Nat.card ↥(T₂ ⊓ centralizer ({y} : Set G)))
    {W : Subgroup G}
    (hJT : ∀ j ∈ J z, orderOf j = 2 → j ≠ z → ∃ c ∈ H z, c * j * c⁻¹ ∈ T₂)
    (hbad : ∀ y ∈ H z, orderOf y = 2 → y ≠ z → (∀ c ∈ H z, c * y * c⁻¹ ∉ T₂) →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y)
    (hWT : W ≤ T₂) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (hWc : Nat.card W = 32)
    (hWu : ∀ E : Subgroup G, E ≤ T₂ → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E = 32 → E = W)
    (hJY : ∀ j ∈ J z ⊓ centralizer ({σ} : Set G), orderOf j = 2 → j ≠ z →
      ∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * j * c⁻¹ ∈ W)
    (hKL : ∀ x ∈ H z ⊓ centralizer ({σ} : Set G), orderOf x = 2 →
      (∀ c ∈ H z ⊓ centralizer ({σ} : Set G), c * x * c⁻¹ ∉ W) →
      ∀ K : Subgroup G,
        IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) →
        Nat.card K < 2 ^ 8 ∧
        ((∃ a ∈ centerIn K, a ≠ 1 ∧ a ≠ z ∧
            (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * a * c⁻¹ ∈ W) ∧
            (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * (a * z) * c⁻¹ ∈ W) ∧
            ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨ ∃ c ∈ H z, c * x * c⁻¹ = e) ∨
          (z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)) ∧
            Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z)))
    (O : Fin 7 → Finset G)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (horb : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i,
      ∃ c ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G) ⊓ H z, c * a * c⁻¹ = b)
    (hinv : ∀ i, ∀ a ∈ O i,
      ∀ c ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G) ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hcard : ∀ i, (O i).card = lemma54Sizes i)
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO2z : ∀ a ∈ O 2, a * z ∈ O 2) (hO3z : ∀ a ∈ O 3, a * z ∈ O 3)
    (hgen : J z ⊓ W ≤ Subgroup.closure ((O 2 : Set G) ∪ (O 3 : Set G)))
    (hO56 : ∀ a, a ∈ O 5 ∨ a ∈ O 6 →
      ∃ y ∈ H z ⊓ centralizer ({a} : Set G), y ∉ centralizer ({z₁} : Set G))
    {t : G} {S₀ : Subgroup G}
    (hE₃ : (∃ E : Subgroup G, E ≤ centralizer ({σ₃} : Set G) ∧ Nat.card E = 16 ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1) ∨
      ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({σ₃} : Set G)) ∧ Nat.card T = 2 ^ 5)
    (hnoE : ∀ F : Subgroup G, F ≤ T₁ → Nat.card F = 16 →
      ¬ ((∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1))
    (hS₀ : IsSylowOf 2 S₀ (H z ⊓ normalizer (zpowers σ₁ : Set G))) (hTS : T₁ ≤ S₀)
    (hz₁T : z₁ ∈ centerIn T₁) (htT : t ∈ centerIn T₁)
    (hT₁O : (∃ u ∈ H z, ∃ a ∈ O 5, u * a * u⁻¹ ∈ O 6) ∨
      ((∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e ∈ O 5 ∨ e ∈ O 6) ∧ t ∈ O 4 ∧ t * z ∈ O 4))
    (hsq : z₁ ∈ ⁅T₁, T₁⁆ ∨
      {k : G | k ∈ T₁ ∧ k * k = z}.ncard ≠ {k : G | k ∈ T₁ ∧ k * k = t}.ncard ∨
      {k : G | k ∈ T₁ ∧ k * k = z}.ncard ≠ {k : G | k ∈ T₁ ∧ k * k = t * z}.ncard) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by

  have hz₁z' : ¬ IsConj z₁ z :=
    fun hc => not_isConj_z_z1 h hZ hz₁ hz₁z hord hc.symm
  have hzz₁ : z * z₁ = z₁ * z := mul_comm_of_mem_centerIn_J h hz₁
  have hz₁j : ∀ a, a ∈ O 2 ∨ a ∈ O 3 → ¬ IsConj z₁ a := by
    intro a haO
    obtain ⟨-, -, haJ, ha2, -, hnot1⟩ := orbit23_facts hW2 hOW hdisj hJ haO
    exact not_isConj_z1_of_mem_orbits h hZ hz₁ hz₁z hord hK hO1 haJ ha2 hnot1 hzz₁
  have hP4 : ∀ t ∈ H z ⊓ centralizer ({σ} : Set G), orderOf t = 2 → IsConj z t →
      ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z := by
    intro t ht ht2 hzt
    exact exists_centralizer_sigma_conj h hT₁ hT₁c hZ₁ hZ₁e hT₂ hT₂c hZ₂ hT₃ hz₃ hT₂₃
      hσ hσH hcls hwH hw ht2 ht.1 ht.2 hzt
  have hk : ∃ n ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G), n ∉ H z :=
    exists_mem_normalizer_not_mem_H h hHO hP4 hT₂ hT₂c hJT hbad hWT hWab hW2 hWc hWu hJY hKL
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ :=
    lemma54_orbits (z₁ := z₁) (W := W)
      (N := normalizer (W : Set G) ⊓ centralizer ({σ} : Set G))
      inf_le_left hWab hW2 O hOW hcover hdisj horb hinv hcard hO0 hO1 hJ hnJ hO2z hO3z
      hgen hz₁z' hz₁j hk
  obtain ⟨hZS₀, htO, htzO⟩ := hT₁O.resolve_left fun ⟨u, _, a, ha5, hua⟩ =>
    lemma54_orbits_five_six (z₁ := z₁) (W := W)
      (N := normalizer (W : Set G) ⊓ centralizer ({σ} : Set G))
      inf_le_left hWab hW2 O hOW hcover hdisj horb hinv hcard hO0 hO1 hJ hnJ hO2z hO3z
      hgen hz₁z' hz₁j hk a ha5 _ hua (isConj_iff.mpr ⟨u, rfl⟩)
  obtain ⟨a, haO, n, _, hnz⟩ := hc2
  obtain ⟨-, ha1, -, ha2, hnot0, hnot1⟩ := orbit23_facts hW2 hOW hdisj hJ haO
  have hzt' : IsConj z a := isConj_iff.mpr ⟨n, hnz⟩
  obtain ⟨hj₀, hj₀c⟩ :=
    mul_z_mem_J_not_centerIn h hz₁ hz₁z hord hO0 hO1 hO2z hO3z hJ haO ha1 hnot0 hnot1 hzz₁
  have hconj : IsConj (a * z) (a * z) := IsConj.refl _
  obtain ⟨g, hgN, hgz₁, hgH⟩ := hc5
  obtain ⟨hgC, hgz, hgz'⟩ :=
    conj_z_data_of_mem_normalizer h hz₁ hT₂ hWT hO0 hOW hgN hgz₁ hgH
  obtain ⟨b, hbO, n, _, hnz⟩ := hc4
  obtain ⟨y, hy, hyz₁⟩ := hO56 b hbO
  have huy := conj_mem_centralizer_z1_of_conj hnz hy.2
  have hσσ₁ : ∀ g : G, CFSG.conjugate (zpowers σ) g ≠ zpowers σ₁ :=
    (lemma53 h hT₁ hT₁c hZ₁ hZ₁e hT₂ hT₂c hZ₂ hT₃ hz₃ hT₂₃).2.1
  have hZS₀' : ∀ e ∈ centerIn S₀, IsConj z e → e = z :=
    centerIn_S₀_conj_z_eq h hP4 hT₂ hWT hWab hW2 hWc hWu hOW hZS₀ hc3
  have hzt : IsConj z t := isConj_of_mem_O4 hc1 htO
  have hztz : IsConj z (t * z) := isConj_of_mem_O4 hc1 htzO
  have hder :=
    mem_commutator_centralizer_z1 h hσ₁ hσ₁H hw₁H hw₁ hcls hσσ₁ hE₃ hT₁ hT₁c hnoE
      hS₀ hTS hZS₀' hz₁T htT hzt hztz hsq
  exact fi22_of_section5_fusion h hZ hz₁ hz₁z hord hT2 hgC hgz hgz' hder ha2 hzt' hj₀ hj₀c
    hconj hy.1 hyz₁ huy


end Certified

end CFSG.RankThree.GF2n.Parrott
