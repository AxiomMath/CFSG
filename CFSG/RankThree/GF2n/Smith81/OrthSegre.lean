module

public import CFSG.RankThree.GF2n.Smith81.OrthModel
public import CFSG.RankThree.GF2n.Stroth80.GlobalModelData

public section

namespace CFSG.RankThree.GF2n.Smith81

section Segre

variable {K : Type} [Field K] {ι : Type}

@[expose] def SingTensor (q : QuadraticForm K (ι → K)) (w : (ι → K) × (ι → K)) : Prop :=
  ∃ (c₁ c₂ : K) (u : ι → K), q u = 0 ∧ w = (c₁ • u, c₂ • u)

theorem singTensor_iff (q : QuadraticForm K (ι → K)) (w : (ι → K) × (ι → K)) :
    SingTensor q w ↔ w = 0 ∨ PairTypeA q w := by
  constructor
  · rintro ⟨c₁, c₂, u, hu, rfl⟩
    by_cases h : c₁ = 0 ∧ c₂ = 0
    · left
      obtain ⟨rfl, rfl⟩ := h
      simp
    · by_cases hu0 : u = 0
      · left
        subst hu0
        simp
      · right
        exact ⟨c₁, c₂, u, not_and_or.mp h |>.imp (fun h => h) (fun h => h), hu0, hu, rfl⟩
  · rintro (rfl | ⟨c₁, c₂, u, _, _, hu, rfl⟩)
    · exact ⟨0, 0, 0, QuadraticMap.map_zero _, Prod.ext (by simp) (by simp)⟩
    · exact ⟨c₁, c₂, u, hu, rfl⟩

section Char2

variable [CharP K 2]

private theorem seg_two : (2 : K) = 0 := CharTwo.two_eq_zero

private theorem seg_add_self {V : Type*} [AddCommGroup V] [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K v, seg_two, zero_smul]

private theorem seg_polar_self (q : QuadraticForm K (ι → K)) (v : ι → K) :
    QuadraticMap.polar q v v = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

private theorem seg_q_add (q : QuadraticForm K (ι → K)) (a b : ι → K) :
    q (a + b) = q a + q b + QuadraticMap.polar q a b := QuadraticMap.map_add q a b

private theorem seg_polar_comb (q : QuadraticForm K (ι → K)) (a b c d : ι → K) (x y z t : K) :
    QuadraticMap.polar q (x • a + y • b) (z • c + t • d) =
      x * z * QuadraticMap.polar q a c + x * t * QuadraticMap.polar q a d +
        y * z * QuadraticMap.polar q b c + y * t * QuadraticMap.polar q b d := by
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul]
  ring

private theorem seg_q_comb (q : QuadraticForm K (ι → K)) (a b : ι → K) (x y : K) :
    q (x • a + y • b) = x * x * q a + y * y * q b + x * y * QuadraticMap.polar q a b := by
  rw [seg_q_add, QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]
  ring

private theorem seg_mem_of_singular (q : QuadraticForm K (ι → K)) (s y y' : ι → K)
    (hy : q y = 0) (hy' : q y' = 0) (hyy' : QuadraticMap.polar q y y' = 1)
    (hys : QuadraticMap.polar q y s = 0) (hy's : QuadraticMap.polar q y' s = 0)
    (N : Submodule K (ι → K))
    (hN : ∀ z, q z = 0 → QuadraticMap.polar q z s = 0 → z ∈ N) :
    ∀ x, QuadraticMap.polar q x s = 0 → x ∈ N := by
  intro x hx
  have hy'y : QuadraticMap.polar q y' y = 1 := by rw [QuadraticMap.polar_comm]; exact hyy'
  have hyy0 := seg_polar_self q y
  have hy'y'0 := seg_polar_self q y'
  have h2 : (2 : K) = 0 := seg_two
  obtain ⟨a, ha⟩ : ∃ a, a = QuadraticMap.polar q x y' := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = QuadraticMap.polar q x y := ⟨_, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x', x' = x + a • y + b • y' := ⟨_, rfl⟩
  have hx'y : QuadraticMap.polar q x' y = 0 := by
    rw [hx', QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, hy'y, hyy0, ← hb]
    simp only [smul_eq_mul]
    linear_combination b * h2
  have hx'y' : QuadraticMap.polar q x' y' = 0 := by
    rw [hx', QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, hyy', hy'y'0, ← ha]
    simp only [smul_eq_mul]
    linear_combination a * h2
  have hx's : QuadraticMap.polar q x' s = 0 := by
    rw [hx', QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, hys, hy's, hx]
    simp
  obtain ⟨z, hz⟩ : ∃ z, z = x' + y + q x' • y' := ⟨_, rfl⟩
  have hzq : q z = 0 := by
    have e1 : q (x' + y) = q x' := by rw [seg_q_add, hy, hx'y]; ring
    have e2 : QuadraticMap.polar q (x' + y) (q x' • y') = q x' := by
      rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_add_left, hx'y', hyy']
      simp
    rw [hz, seg_q_add, e1, QuadraticMap.map_smul, hy', e2]
    simp only [smul_eq_mul, mul_zero]
    linear_combination (q x') * h2
  have hzs : QuadraticMap.polar q z s = 0 := by
    rw [hz, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      hx's, hys, hy's]
    simp
  have hid : x = z + y + q x' • y' + a • y + b • y' := by
    have e1 := seg_add_self (K := K) y
    have e2 := seg_add_self (K := K) (q x' • y')
    have e3 := seg_add_self (K := K) (a • y)
    have e4 := seg_add_self (K := K) (b • y')
    calc x = x + (a • y + a • y) + (b • y' + b • y') + (y + y) + (q x' • y' + q x' • y') := by
          rw [e1, e2, e3, e4]; simp
      _ = z + y + q x' • y' + a • y + b • y' := by rw [hz, hx']; abel
  rw [hid]
  exact N.add_mem (N.add_mem (N.add_mem (N.add_mem (hN z hzq hzs) (hN y hy hys))
    (N.smul_mem _ (hN y' hy' hy's))) (N.smul_mem _ (hN y hy hys))) (N.smul_mem _ (hN y' hy' hy's))

@[expose] def PolarFormNondeg (q : QuadraticForm K (ι → K)) : Prop :=
  ∀ u : ι → K, (∀ v : ι → K, QuadraticMap.polar q u v = 0) → u = 0

private theorem seg_exists_one (q : QuadraticForm K (ι → K)) (hnd : PolarFormNondeg q)
    {u : ι → K} (hu : u ≠ 0) : ∃ v, QuadraticMap.polar q u v = 1 := by
  by_contra hcon
  push Not at hcon
  apply hu
  apply hnd
  intro v
  by_contra hv
  apply hcon ((QuadraticMap.polar q u v)⁻¹ • v)
  rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hv]

private theorem seg_hyp_partner (q : QuadraticForm K (ι → K)) {y v : ι → K} (hy : q y = 0)
    (hv : QuadraticMap.polar q y v = 1) :
    q (v + q v • y) = 0 ∧ QuadraticMap.polar q y (v + q v • y) = 1 := by
  have h2 : (2 : K) = 0 := seg_two
  refine ⟨?_, ?_⟩
  · rw [seg_q_add, QuadraticMap.map_smul, hy, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_comm q v y, hv]
    simp only [smul_eq_mul, mul_zero, mul_one]
    linear_combination (q v) * h2
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, seg_polar_self, hv]
    simp

private theorem seg_singular_partner (q : QuadraticForm K (ι → K)) (hnd : PolarFormNondeg q)
    {u : ι → K} (hu0 : u ≠ 0) (hu : q u = 0) :
    ∃ v, q v = 0 ∧ QuadraticMap.polar q u v = 1 := by
  obtain ⟨v, hv⟩ := seg_exists_one q hnd hu0
  exact ⟨v + q v • u, (seg_hyp_partner q hu hv).1, (seg_hyp_partner q hu hv).2⟩

private theorem seg_span_sing (q : QuadraticForm K (ι → K)) (hnd : PolarFormNondeg q)
    (hsing : ∃ u : ι → K, u ≠ 0 ∧ q u = 0) :
    ∀ x : ι → K, x ∈ Submodule.span K {u : ι → K | q u = 0} := by
  obtain ⟨u, hu0, hu⟩ := hsing
  obtain ⟨v, hv, huv⟩ := seg_singular_partner q hnd hu0 hu
  intro x
  refine seg_mem_of_singular q 0 u v hu hv huv (by simp) (by simp) _
    (fun z hz _ => Submodule.subset_span hz) x (by simp)

private theorem seg_exists_pair (q : QuadraticForm K (ι → K)) (hnd : PolarFormNondeg q)
    {y s : ι → K} (hind : ∀ a b : K, a • y + b • s = 0 → a = 0 ∧ b = 0) :
    ∃ v, QuadraticMap.polar q y v = 1 ∧ QuadraticMap.polar q s v = 0 := by
  let f : (ι → K) →ₗ[K] K × K :=
    LinearMap.prod (QuadraticMap.polarBilin q y) (QuadraticMap.polarBilin q s)
  have hf : LinearMap.range f = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_le_ker_of_lt_top (LinearMap.range f) (lt_top_iff_ne_top.mpr hne)
    apply hφ0
    have key : ∀ v, φ (1, 0) * QuadraticMap.polar q y v +
        φ (0, 1) * QuadraticMap.polar q s v = 0 := by
      intro v
      have h := hφ ⟨v, rfl⟩
      have h' : φ (QuadraticMap.polar q y v, QuadraticMap.polar q s v) = 0 := h
      have : (QuadraticMap.polar q y v, QuadraticMap.polar q s v) =
          QuadraticMap.polar q y v • ((1 : K), (0 : K)) +
            QuadraticMap.polar q s v • ((0 : K), (1 : K)) := by
        ext <;> simp
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h'
      linear_combination h'
    have hz : φ (1, 0) • y + φ (0, 1) • s = 0 := by
      apply hnd
      intro v
      rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left]
      simpa using key v
    obtain ⟨h1, h2⟩ := hind _ _ hz
    refine LinearMap.ext fun ⟨a, b⟩ => ?_
    have : (a, b) = a • ((1 : K), (0 : K)) + b • ((0 : K), (1 : K)) := by ext <;> simp
    rw [this, map_add, map_smul, map_smul, h1, h2]
    simp
  have h10 : ((1 : K), (0 : K)) ∈ LinearMap.range f := by rw [hf]; trivial
  obtain ⟨v, hv⟩ := h10
  refine ⟨v, ?_, ?_⟩
  · have := congrArg Prod.fst hv
    simpa [f] using this
  · have := congrArg Prod.snd hv
    simpa [f] using this

private theorem seg_par {x₁ x₂ y₁ y₂ : K} (hy : y₁ ≠ 0 ∨ y₂ ≠ 0) (h : x₁ * y₂ = x₂ * y₁) :
    ∃ l : K, x₁ = l * y₁ ∧ x₂ = l * y₂ := by
  by_cases h1 : y₁ = 0
  · have h2 : y₂ ≠ 0 := hy.resolve_left (not_not.mpr h1)
    subst h1
    refine ⟨x₂ / y₂, ?_, ?_⟩
    · have : x₁ * y₂ = 0 := by rw [h]; ring
      rw [(mul_eq_zero.mp this).resolve_right h2]; ring
    · field_simp
  · refine ⟨x₁ / y₁, ?_, ?_⟩
    · field_simp
    · field_simp
      linear_combination -h

private theorem seg_pure_sum {c₁ c₂ c₁' c₂' d₁ d₂ : K} (hD : c₁ * c₂' - c₂ * c₁' ≠ 0)
    {x y z : ι → K} (h1 : c₁ • x + c₁' • y = d₁ • z) (h2 : c₂ • x + c₂' • y = d₂ • z) :
    ∃ l m : K, x = l • z ∧ y = m • z := by
  have ex : (c₁ * c₂' - c₂ * c₁') • x = (c₂' * d₁ - c₁' * d₂) • z := by
    calc (c₁ * c₂' - c₂ * c₁') • x = c₂' • (c₁ • x + c₁' • y) - c₁' • (c₂ • x + c₂' • y) := by
          module
      _ = _ := by rw [h1, h2]; module
  have ey : (c₁ * c₂' - c₂ * c₁') • y = (c₁ * d₂ - c₂ * d₁) • z := by
    calc (c₁ * c₂' - c₂ * c₁') • y = c₁ • (c₂ • x + c₂' • y) - c₂ • (c₁ • x + c₁' • y) := by
          module
      _ = _ := by rw [h1, h2]; module
  refine ⟨(c₁ * c₂' - c₂ * c₁')⁻¹ * (c₂' * d₁ - c₁' * d₂),
    (c₁ * c₂' - c₂ * c₁')⁻¹ * (c₁ * d₂ - c₂ * d₁), ?_, ?_⟩
  · rw [mul_smul, ← ex, inv_smul_smul₀ hD]
  · rw [mul_smul, ← ey, inv_smul_smul₀ hD]

private theorem seg_singTensor_vec {q : QuadraticForm K (ι → K)} {c₁ c₂ : K} (hc : c₁ ≠ 0 ∨ c₂ ≠ 0)
    {x : ι → K} (h : SingTensor q (c₁ • x, c₂ • x)) : q x = 0 := by
  obtain ⟨d₁, d₂, u, hu, he⟩ := h
  have h1 : c₁ • x = d₁ • u := congrArg Prod.fst he
  have h2 : c₂ • x = d₂ • u := congrArg Prod.snd he
  rcases hc with hc | hc
  · have : x = (c₁⁻¹ * d₁) • u := by
      rw [mul_smul, ← h1, inv_smul_smul₀ hc]
    rw [this, QuadraticMap.map_smul, hu, smul_zero]
  · have : x = (c₂⁻¹ * d₂) • u := by
      rw [mul_smul, ← h2, inv_smul_smul₀ hc]
    rw [this, QuadraticMap.map_smul, hu, smul_zero]

private theorem seg_tens_cancel {c₁ c₂ : K} (hc : c₁ ≠ 0 ∨ c₂ ≠ 0) {x y : ι → K}
    (h : (c₁ • x, c₂ • x) = (c₁ • y, c₂ • y)) : x = y := by
  have h1 : c₁ • x = c₁ • y := congrArg Prod.fst h
  have h2 : c₂ • x = c₂ • y := congrArg Prod.snd h
  rcases hc with hc | hc
  · exact smul_right_injective _ hc h1
  · exact smul_right_injective _ hc h2

private theorem seg_two_tensors (q : QuadraticForm K (ι → K)) {p p' : (ι → K) × (ι → K)}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hS : ∀ a b : K, SingTensor q (a • p + b • p'))
    (hI : ∀ a b : K, a • p + b • p' = 0 → a = 0 ∧ b = 0) :
    (∃ (u' : ι → K) (a b c d : K), q u' = 0 ∧ u' ≠ 0 ∧ a * d - b * c ≠ 0 ∧
        p = (a • u', b • u') ∧ p' = (c • u', d • u')) ∨
    (∃ (a₁ a₂ : K) (s s'' : ι → K), (a₁ ≠ 0 ∨ a₂ ≠ 0) ∧ q s = 0 ∧ q s'' = 0 ∧
        QuadraticMap.polar q s s'' = 0 ∧ (∀ a b : K, a • s + b • s'' = 0 → a = 0 ∧ b = 0) ∧
        p = (a₁ • s, a₂ • s) ∧ p' = (a₁ • s'', a₂ • s'')) := by
  obtain ⟨a₁, a₂, s, hs, hpe⟩ : SingTensor q p := by simpa using hS 1 0
  obtain ⟨b₁, b₂, s', hs', hpe'⟩ : SingTensor q p' := by simpa using hS 0 1
  have hA : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hp
    rw [hpe, hcon.1, hcon.2]
    simp
  have hs0 : s ≠ 0 := by
    intro h0
    apply hp
    rw [hpe, h0]
    simp
  have hs'0 : s' ≠ 0 := by
    intro h0
    apply hp'
    rw [hpe', h0]
    simp
  have hpp := hS 1 1
  rw [hpe, hpe'] at hpp
  obtain ⟨d₁, d₂, z, hz, he⟩ := hpp
  have e1 : a₁ • s + b₁ • s' = d₁ • z := by simpa using congrArg Prod.fst he
  have e2 : a₂ • s + b₂ • s' = d₂ • z := by simpa using congrArg Prod.snd he
  by_cases hD : a₁ * b₂ - a₂ * b₁ = 0
  ·
    right
    obtain ⟨κ, hκ1, hκ2⟩ := seg_par (x₁ := b₁) (x₂ := b₂) (y₁ := a₁) (y₂ := a₂) hA
      (by linear_combination -hD)
    refine ⟨a₁, a₂, s, κ • s', hA, hs, ?_, ?_, ?_, hpe, ?_⟩
    · rw [QuadraticMap.map_smul, hs', smul_zero]
    · have hq : q (s + κ • s') = 0 := by
        apply seg_singTensor_vec hA (c₁ := a₁) (c₂ := a₂)
        have := hS 1 1
        rw [hpe, hpe', hκ1, hκ2] at this
        convert this using 1
        exact Prod.ext (by simp; module) (by simp; module)
      rw [seg_q_add, hs, QuadraticMap.map_smul, hs', smul_zero] at hq
      simpa using hq
    · intro a b hab
      apply hI a b
      have : a • p + b • p' = (a₁ • (a • s + b • (κ • s')), a₂ • (a • s + b • (κ • s'))) := by
        rw [hpe, hpe', hκ1, hκ2]
        exact Prod.ext (by simp; module) (by simp; module)
      rw [this, hab]
      simp
    · rw [hpe', hκ1, hκ2]
      exact Prod.ext (by simp [smul_smul, mul_comm]) (by simp [smul_smul, mul_comm])
  ·
    left
    obtain ⟨l, m, hl, hm⟩ := seg_pure_sum hD e1 e2
    have hl0 : l ≠ 0 := by
      rintro rfl
      apply hs0
      rw [hl, zero_smul]
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hs'0
      rw [hm, zero_smul]
    have hz' : z = l⁻¹ • s := by rw [hl, inv_smul_smul₀ hl0]
    have hs'' : s' = (m * l⁻¹) • s := by rw [hm, hz', smul_smul]
    refine ⟨s, a₁, a₂, b₁ * (m * l⁻¹), b₂ * (m * l⁻¹), hs, hs0, ?_, hpe, ?_⟩
    · have : a₁ * (b₂ * (m * l⁻¹)) - a₂ * (b₁ * (m * l⁻¹)) =
          (a₁ * b₂ - a₂ * b₁) * (m * l⁻¹) := by ring
      rw [this]
      exact mul_ne_zero hD (mul_ne_zero hm0 (inv_ne_zero hl0))
    · rw [hpe', hs'']
      exact Prod.ext (by simp [smul_smul]) (by simp [smul_smul])

private theorem singTensor_swap {q : QuadraticForm K (ι → K)} {x y : ι → K}
    (h : SingTensor q (x, y)) : SingTensor q (y, x) := by
  obtain ⟨c₁, c₂, u, hu, he⟩ := h
  exact ⟨c₂, c₁, u, hu, Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)⟩

private theorem seg_sing_aux {q : QuadraticForm K (ι → K)} {u x y : ι → K} (hu : u ≠ 0)
    (h1 : SingTensor q (x, y)) (h2 : SingTensor q (u + x, y)) : ∃ b : K, y = b • u := by
  obtain ⟨d₁, d₂, z, hz, he⟩ := h1
  obtain ⟨e₁, e₂, w, hw, he'⟩ := h2
  have hx : x = d₁ • z := congrArg Prod.fst he
  have hy : y = d₂ • z := congrArg Prod.snd he
  have hx' : u + x = e₁ • w := congrArg Prod.fst he'
  have hy' : y = e₂ • w := congrArg Prod.snd he'
  by_cases hd : y = 0
  · exact ⟨0, by rw [hd, zero_smul]⟩
  · have he2 : e₂ ≠ 0 := by
      rintro rfl
      exact hd (by rw [hy', zero_smul])
    have hw' : w = e₂⁻¹ • y := by rw [hy', inv_smul_smul₀ he2]
    have hu' : u = (e₁ * e₂⁻¹ * d₂ - d₁) • z := by
      have : u = e₁ • w - x := by rw [← hx']; abel
      rw [this, hw', hy, hx]
      module
    have hκ : (e₁ * e₂⁻¹ * d₂ - d₁) ≠ 0 := by
      intro h0
      apply hu
      rw [hu', h0, zero_smul]
    refine ⟨d₂ * (e₁ * e₂⁻¹ * d₂ - d₁)⁻¹, ?_⟩
    rw [hy, mul_smul]
    congr 1
    rw [hu', inv_smul_smul₀ hκ]

structure IsSegreMap (q : QuadraticForm K (ι → K)) (σ : K ≃+* K) (ρ : K)
    (F : (ι → K) × (ι → K) → (ι → K) × (ι → K)) : Prop where
  ρ_ne : ρ ≠ 0
  bij : Function.Bijective F
  add : ∀ p p', F (p + p') = F p + F p'
  smul : ∀ (c : K) p, F (c • p) = σ c • F p
  form : ∀ p, QuadraticMap.polar q (F p).1 (F p).2 = ρ * σ (QuadraticMap.polar q p.1 p.2)
  typeA : ∀ p, PairTypeA q (F p) ↔ PairTypeA q p

namespace IsSegreMap

variable {q : QuadraticForm K (ι → K)} {σ : K ≃+* K} {ρ : K}
  {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)}

theorem map_zero (hF : IsSegreMap q σ ρ F) : F 0 = 0 := by
  have := hF.add 0 0
  simpa using this

theorem singTensor_map_iff (hF : IsSegreMap q σ ρ F) (w : (ι → K) × (ι → K)) :
    SingTensor q (F w) ↔ SingTensor q w := by
  have h0 : F w = 0 ↔ w = 0 :=
    ⟨fun h => hF.bij.1 (h.trans hF.map_zero.symm), fun h => h ▸ hF.map_zero⟩
  rw [_root_.CFSG.RankThree.GF2n.Smith81.singTensor_iff,
    _root_.CFSG.RankThree.GF2n.Smith81.singTensor_iff, hF.typeA, h0]

theorem exists_inv (hF : IsSegreMap q σ ρ F) :
    ∃ G : (ι → K) × (ι → K) → (ι → K) × (ι → K), (∀ p, F (G p) = p) ∧ (∀ w, G (F w) = w) ∧
      (∀ p p', G (p + p') = G p + G p') ∧ (∀ (c : K) p, G (c • p) = σ.symm c • G p) := by
  obtain ⟨G, hG⟩ := hF.bij.2.hasRightInverse
  have hGF : ∀ w, G (F w) = w := fun w => hF.bij.1 (hG (F w))
  refine ⟨G, hG, hGF, fun p p' => ?_, fun c p => ?_⟩
  · apply hF.bij.1
    rw [hG, hF.add, hG, hG]
  · apply hF.bij.1
    rw [hG, hF.smul, hG, RingEquiv.apply_symm_apply]

end IsSegreMap

private def segT (q : QuadraticForm K (ι → K)) (p : (ι → K) × (ι → K)) :
    Set ((ι → K) × (ι → K)) :=
  {y | SingTensor q y ∧ ∀ a b : K, SingTensor q (a • p + b • y)}

private def segM (q : QuadraticForm K (ι → K)) (p : (ι → K) × (ι → K)) :
    Submodule K ((ι → K) × (ι → K)) :=
  Submodule.span K (segT q p)

private def segTensL (a₁ a₂ : K) : (ι → K) →ₗ[K] (ι → K) × (ι → K) :=
  LinearMap.prod (a₁ • LinearMap.id) (a₂ • LinearMap.id)

private theorem segTensL_apply (a₁ a₂ : K) (x : ι → K) : segTensL a₁ a₂ x = (a₁ • x, a₂ • x) :=
  rfl

private theorem seg_segM_snd {q : QuadraticForm K (ι → K)} {u : ι → K} (hu : u ≠ 0)
    {y : (ι → K) × (ι → K)} (hy : y ∈ segM q ((u, 0) : (ι → K) × (ι → K))) :
    ∃ b : K, y.2 = b • u := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y₁, y₂⟩ := y
    obtain ⟨h1, h2⟩ := hy
    have h3 := h2 1 1
    have h4 : SingTensor q (u + y₁, y₂) := by simpa using h3
    exact seg_sing_aux hu h1 h4
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨b, hb⟩ := ihx
    obtain ⟨b', hb'⟩ := ihy
    exact ⟨b + b', by rw [Prod.snd_add, hb, hb', add_smul]⟩
  | smul c x _ ihx =>
    obtain ⟨b, hb⟩ := ihx
    exact ⟨c * b, by rw [Prod.smul_snd, hb, smul_smul]⟩

private theorem seg_segM_fst {q : QuadraticForm K (ι → K)} {u : ι → K} (hu : u ≠ 0)
    {y : (ι → K) × (ι → K)} (hy : y ∈ segM q ((0, u) : (ι → K) × (ι → K))) :
    ∃ b : K, y.1 = b • u := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y₁, y₂⟩ := y
    obtain ⟨h1, h2⟩ := hy
    have h3 := h2 1 1
    have h4 : SingTensor q (u + y₂, y₁) := singTensor_swap (by simpa using h3)
    exact seg_sing_aux hu (singTensor_swap h1) h4
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨b, hb⟩ := ihx
    obtain ⟨b', hb'⟩ := ihy
    exact ⟨b + b', by rw [Prod.fst_add, hb, hb', add_smul]⟩
  | smul c x _ ihx =>
    obtain ⟨b, hb⟩ := ihx
    exact ⟨c * b, by rw [Prod.smul_fst, hb, smul_smul]⟩

private theorem seg_segM_inv {q : QuadraticForm K (ι → K)} {σ : K ≃+* K} {ρ : K}
    {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)} (hF : IsSegreMap q σ ρ F)
    {G : (ι → K) × (ι → K) → (ι → K) × (ι → K)} (hG1 : ∀ p, F (G p) = p)
    (hGadd : ∀ p p', G (p + p') = G p + G p')
    (hGsmul : ∀ (c : K) p, G (c • p) = σ.symm c • G p) {p₀ y : (ι → K) × (ι → K)}
    (hy : y ∈ segM q (F p₀)) : G y ∈ segM q p₀ := by
  have hG0 : G 0 = 0 := by
    have := hGadd 0 0
    simpa using this
  induction hy using Submodule.span_induction with
  | mem y hy =>
    refine Submodule.subset_span ⟨?_, fun a b => ?_⟩
    · exact (hF.singTensor_map_iff _).mp (by rw [hG1]; exact hy.1)
    · refine (hF.singTensor_map_iff _).mp ?_
      rw [hF.add, hF.smul, hF.smul, hG1]
      exact hy.2 (σ a) (σ b)
  | zero => rw [hG0]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [hGadd]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx => rw [hGsmul]; exact Submodule.smul_mem _ _ ihx

private theorem seg_tens_mem_segM (q : QuadraticForm K (ι → K)) (hnd : PolarFormNondeg q)
    {s s'' : ι → K} (hs : q s = 0) (hs'' : q s'' = 0) (hss : QuadraticMap.polar q s s'' = 0)
    (hind : ∀ a b : K, a • s'' + b • s = 0 → a = 0 ∧ b = 0) (a₁ a₂ : K) :
    ∀ x, QuadraticMap.polar q x s = 0 → (a₁ • x, a₂ • x) ∈
      segM q ((a₁ • s, a₂ • s) : (ι → K) × (ι → K)) := by
  obtain ⟨v, hv1, hv2⟩ := seg_exists_pair q hnd hind
  obtain ⟨hy'q, hy'1⟩ := seg_hyp_partner q hs'' hv1
  have hy's : QuadraticMap.polar q (v + q v • s'') s = 0 := by
    rw [QuadraticMap.polar_comm, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hv2,
      hss]
    simp
  have hs''s : QuadraticMap.polar q s'' s = 0 := by rw [QuadraticMap.polar_comm]; exact hss
  have := seg_mem_of_singular q s s'' (v + q v • s'') hs'' hy'q hy'1 hs''s hy's
    ((segM q ((a₁ • s, a₂ • s) : (ι → K) × (ι → K))).comap (segTensL a₁ a₂)) (fun z hz hzs => by
      refine Submodule.subset_span ⟨⟨a₁, a₂, z, hz, rfl⟩, fun a b =>
        ⟨a₁, a₂, a • s + b • z, ?_, ?_⟩⟩
      · rw [seg_q_comb, hs, hz, QuadraticMap.polar_comm q s z, hzs]
        ring
      · exact Prod.ext (by simp only [segTensL_apply, Prod.fst_add, Prod.smul_fst]; module)
          (by simp only [segTensL_apply, Prod.snd_add, Prod.smul_snd]; module))
  exact this

private theorem seg_no_plane [Fintype ι] {q : QuadraticForm K (ι → K)} {σ : K ≃+* K} {ρ : K}
    {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)} (hF : IsSegreMap q σ ρ F) (hnd : PolarFormNondeg q)
    (hn : 5 ≤ Fintype.card ι) {u : ι → K} (hu0 : u ≠ 0) {a₁ a₂ : K} (hA : a₁ ≠ 0 ∨ a₂ ≠ 0)
    {s s'' : ι → K} (hs : q s = 0) (hs'' : q s'' = 0) (hss : QuadraticMap.polar q s s'' = 0)
    (hind : ∀ a b : K, a • s + b • s'' = 0 → a = 0 ∧ b = 0)
    (h1 : F (u, 0) = (a₁ • s, a₂ • s)) (h2 : F (0, u) = (a₁ • s'', a₂ • s'')) : False := by
  obtain ⟨G, hG1, hG2, hGadd, hGsmul⟩ := hF.exists_inv
  have key : ∀ x, QuadraticMap.polar q x s = 0 → QuadraticMap.polar q x s'' = 0 →
      ∃ a b : K, x = a • s + b • s'' := by
    intro x hxs hxs''
    have hind' : ∀ a b : K, a • s'' + b • s = 0 → a = 0 ∧ b = 0 := fun a b h =>
      (hind b a (by rw [add_comm]; exact h)).symm
    have t1 : (a₁ • x, a₂ • x) ∈ segM q (F (u, 0)) := by
      rw [h1]; exact seg_tens_mem_segM q hnd hs hs'' hss hind' a₁ a₂ x hxs
    have t2 : (a₁ • x, a₂ • x) ∈ segM q (F (0, u)) := by
      rw [h2]
      exact seg_tens_mem_segM q hnd hs'' hs (by rw [QuadraticMap.polar_comm]; exact hss)
        hind a₁ a₂ x hxs''
    have g1 := seg_segM_inv hF hG1 hGadd hGsmul t1
    have g2 := seg_segM_inv hF hG1 hGadd hGsmul t2
    obtain ⟨b, hb⟩ := seg_segM_snd hu0 g1
    obtain ⟨b', hb'⟩ := seg_segM_fst hu0 g2
    have hGt : G (a₁ • x, a₂ • x) = (b' • u, b • u) := Prod.ext hb' hb
    have h3 : (a₁ • x, a₂ • x) = F (b' • u, b • u) := by rw [← hGt, hG1]
    have e : ((b' • u, b • u) : (ι → K) × (ι → K)) = b' • (u, 0) + b • (0, u) := by
      ext <;> simp
    rw [e, hF.add, hF.smul, hF.smul, h1, h2] at h3
    refine ⟨σ b', σ b, ?_⟩
    apply seg_tens_cancel hA (c₁ := a₁) (c₂ := a₂)
    rw [h3]
    exact Prod.ext (by simp; module) (by simp; module)
  let lam : (ι → K) →ₗ[K] K × K :=
    LinearMap.prod (QuadraticMap.polarBilin q s) (QuadraticMap.polarBilin q s'')
  have hker : LinearMap.ker lam ≤ Submodule.span K {s, s''} := by
    intro x hx
    have e1 : QuadraticMap.polar q s x = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp hx)
    have e2 : QuadraticMap.polar q s'' x = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp hx)
    obtain ⟨a, b, hab⟩ := key x (by rw [QuadraticMap.polar_comm]; exact e1)
      (by rw [QuadraticMap.polar_comm]; exact e2)
    rw [hab]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hrank := LinearMap.finrank_range_add_finrank_ker lam
  have h1 : Module.finrank K (LinearMap.range lam) ≤ 2 := by
    calc Module.finrank K (LinearMap.range lam) ≤ Module.finrank K (K × K) :=
          Submodule.finrank_le _
      _ = 2 := by simp
  have h2 : Module.finrank K (LinearMap.ker lam) ≤ 2 := by
    classical
    calc Module.finrank K (LinearMap.ker lam) ≤ Module.finrank K (Submodule.span K {s, s''}) :=
          Submodule.finrank_mono hker
      _ ≤ 2 := by
          have := finrank_span_finset_le_card (R := K) ({s, s''} : Finset (ι → K))
          simp only [Finset.coe_insert, Finset.coe_singleton] at this
          exact this.trans Finset.card_le_two
  have h3 : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  omega

@[expose] def NoTotallySingularPlane (q : QuadraticForm K (ι → K)) : Prop :=
  ∀ s t : ι → K, q s = 0 → q t = 0 → QuadraticMap.polar q s t = 0 →
    ¬ ∀ a b : K, a • s + b • t = 0 → a = 0 ∧ b = 0

private theorem seg_step1 [Fintype ι] {q : QuadraticForm K (ι → K)} {σ : K ≃+* K} {ρ : K}
    {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)} (hF : IsSegreMap q σ ρ F) (hnd : PolarFormNondeg q)
    (hdim : 5 ≤ Fintype.card ι ∨ NoTotallySingularPlane q) {u : ι → K} (hu0 : u ≠ 0)
    (hu : q u = 0) :
    ∃ (u' : ι → K) (a b c d : K), q u' = 0 ∧ u' ≠ 0 ∧ a * d - b * c ≠ 0 ∧
      F (u, 0) = (a • u', b • u') ∧ F (0, u) = (c • u', d • u') := by
  have hp : F (u, 0) ≠ 0 := by
    intro h
    have := hF.bij.1 (h.trans hF.map_zero.symm)
    exact hu0 (congrArg Prod.fst this)
  have hp' : F (0, u) ≠ 0 := by
    intro h
    have := hF.bij.1 (h.trans hF.map_zero.symm)
    exact hu0 (congrArg Prod.snd this)
  have hcomb : ∀ a b : K, a • F (u, 0) + b • F (0, u) =
      F (σ.symm a • u, σ.symm b • u) := by
    intro a b
    have e : ((σ.symm a • u, σ.symm b • u) : (ι → K) × (ι → K)) =
        σ.symm a • (u, 0) + σ.symm b • (0, u) := by ext <;> simp
    rw [e, hF.add, hF.smul, hF.smul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hS : ∀ a b : K, SingTensor q (a • F (u, 0) + b • F (0, u)) := by
    intro a b
    rw [hcomb, hF.singTensor_map_iff]
    exact ⟨σ.symm a, σ.symm b, u, hu, rfl⟩
  have hI : ∀ a b : K, a • F (u, 0) + b • F (0, u) = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    rw [hcomb] at h
    have h0 := hF.bij.1 (h.trans hF.map_zero.symm)
    have h1 : σ.symm a • u = 0 := congrArg Prod.fst h0
    have h2 : σ.symm b • u = 0 := congrArg Prod.snd h0
    have ha : σ.symm a = 0 := (smul_eq_zero.mp h1).resolve_right hu0
    have hb : σ.symm b = 0 := (smul_eq_zero.mp h2).resolve_right hu0
    exact ⟨σ.symm.injective (ha.trans (map_zero σ.symm).symm),
      σ.symm.injective (hb.trans (map_zero σ.symm).symm)⟩
  rcases seg_two_tensors q hp hp' hS hI with
    ⟨u', a, b, c, d, hu', hu'0, hdet, h1, h2⟩ | ⟨a₁, a₂, s, s'', hA, hs, hs'', hss, hind, h1, h2⟩
  · exact ⟨u', a, b, c, d, hu', hu'0, hdet, h1, h2⟩
  · exfalso
    rcases hdim with h5 | hno
    · exact seg_no_plane hF hnd h5 hu0 hA hs hs'' hss hind h1 h2
    · exact hno s s'' hs hs'' hss hind

private def SegRep (σ : K ≃+* K) (F : (ι → K) × (ι → K) → (ι → K) × (ι → K)) (u u' : ι → K)
    (g : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ c₁ c₂ : K, F (c₁ • u, c₂ • u) =
    ((g 0 0 * σ c₁ + g 0 1 * σ c₂) • u', (g 1 0 * σ c₁ + g 1 1 * σ c₂) • u')

private theorem seg_rep_of_step1 {q : QuadraticForm K (ι → K)} {σ : K ≃+* K} {ρ : K}
    {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)} (hF : IsSegreMap q σ ρ F) {u u' : ι → K}
    {a b c d : K} (h1 : F (u, 0) = (a • u', b • u')) (h2 : F (0, u) = (c • u', d • u')) :
    SegRep σ F u u' !![a, c; b, d] := by
  intro c₁ c₂
  have e : ((c₁ • u, c₂ • u) : (ι → K) × (ι → K)) = c₁ • (u, 0) + c₂ • (0, u) := by
    ext <;> simp
  rw [e, hF.add, hF.smul, hF.smul, h1, h2]
  exact Prod.ext (by simp; module) (by simp; module)

private theorem seg_three_point {g h : Matrix (Fin 2) (Fin 2) K} (hh : h.det ≠ 0)
    (H : ∀ C₁ C₂ : K, (g 0 0 * C₁ + g 0 1 * C₂) * (h 1 0 * C₁ + h 1 1 * C₂) =
      (g 1 0 * C₁ + g 1 1 * C₂) * (h 0 0 * C₁ + h 0 1 * C₂)) :
    ∃ l : K, ∀ i j, g i j = l * h i j := by
  have hD : h 0 0 * h 1 1 - h 0 1 * h 1 0 ≠ 0 := by rwa [Matrix.det_fin_two] at hh
  have hc1 : h 0 0 ≠ 0 ∨ h 1 0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hD
    rw [hcon.1, hcon.2]
    ring
  have hc2 : h 0 1 ≠ 0 ∨ h 1 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hD
    rw [hcon.1, hcon.2]
    ring
  obtain ⟨l₁, e1, e2⟩ := seg_par (x₁ := g 0 0) (x₂ := g 1 0) (y₁ := h 0 0) (y₂ := h 1 0) hc1
    (by have := H 1 0; linear_combination this)
  obtain ⟨l₂, e3, e4⟩ := seg_par (x₁ := g 0 1) (x₂ := g 1 1) (y₁ := h 0 1) (y₂ := h 1 1) hc2
    (by have := H 0 1; linear_combination this)
  have P3 := H 1 1
  rw [e1, e2, e3, e4] at P3
  have hl : l₁ = l₂ := by
    have : (l₁ - l₂) * (h 0 0 * h 1 1 - h 0 1 * h 1 0) = 0 := by linear_combination P3
    have := (mul_eq_zero.mp this).resolve_right hD
    linear_combination this
  subst hl
  refine ⟨l₁, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simpa using by assumption

private theorem seg_polar_uv (q : QuadraticForm K (ι → K)) (u v : ι → K) (c₁ c₂ c₁' c₂' : K) :
    QuadraticMap.polar q (c₁ • u + c₁' • v) (c₂ • u + c₂' • v) =
      (c₁ * c₂' + c₁' * c₂) * QuadraticMap.polar q u v := by
  rw [seg_polar_comb, seg_polar_self, seg_polar_self, QuadraticMap.polar_comm q v u]
  ring

private theorem seg_rep_prop {q : QuadraticForm K (ι → K)} {σ : K ≃+* K} {ρ : K}
    {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)} (hF : IsSegreMap q σ ρ F) {u v u' v' : ι → K}
    {g h : Matrix (Fin 2) (Fin 2) K} (hh : h.det ≠ 0) (huv : QuadraticMap.polar q u v ≠ 0)
    (hgu : SegRep σ F u u' g) (hhv : SegRep σ F v v' h) :
    ∃ l : K, ∀ i j, g i j = l * h i j := by
  have h2 : (2 : K) = 0 := seg_two
  have E : ∀ C₁ C₂ C₁' C₂' : K,
      ((g 0 0 * C₁ + g 0 1 * C₂) * (h 1 0 * C₁' + h 1 1 * C₂') +
        (h 0 0 * C₁' + h 0 1 * C₂') * (g 1 0 * C₁ + g 1 1 * C₂)) * QuadraticMap.polar q u' v' =
      ρ * ((C₁ * C₂' + C₁' * C₂) * σ (QuadraticMap.polar q u v)) := by
    intro C₁ C₂ C₁' C₂'
    have hFp : F (σ.symm C₁ • u + σ.symm C₁' • v, σ.symm C₂ • u + σ.symm C₂' • v) =
        ((g 0 0 * C₁ + g 0 1 * C₂) • u' + (h 0 0 * C₁' + h 0 1 * C₂') • v',
          (g 1 0 * C₁ + g 1 1 * C₂) • u' + (h 1 0 * C₁' + h 1 1 * C₂') • v') := by
      have e : ((σ.symm C₁ • u + σ.symm C₁' • v, σ.symm C₂ • u + σ.symm C₂' • v) :
          (ι → K) × (ι → K)) = (σ.symm C₁ • u, σ.symm C₂ • u) + (σ.symm C₁' • v, σ.symm C₂' • v) :=
        rfl
      rw [e, hF.add, hgu, hhv]
      simp only [RingEquiv.apply_symm_apply]
      exact Prod.ext (by simp [add_smul]) (by simp [add_smul])
    have hform := hF.form (σ.symm C₁ • u + σ.symm C₁' • v, σ.symm C₂ • u + σ.symm C₂' • v)
    rw [hFp, seg_polar_comb, seg_polar_uv, seg_polar_self, seg_polar_self,
      QuadraticMap.polar_comm q v' u'] at hform
    rw [map_mul, map_add, map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at hform
    linear_combination hform
  have hne : QuadraticMap.polar q u' v' ≠ 0 := by
    intro h0
    have := E 1 0 0 1
    rw [h0, mul_zero] at this
    have hσ : σ (QuadraticMap.polar q u v) ≠ 0 := fun h =>
      huv (σ.injective (h.trans (map_zero σ).symm))
    have : ρ * σ (QuadraticMap.polar q u v) = 0 := by linear_combination -this
    exact mul_ne_zero hF.ρ_ne hσ this
  apply seg_three_point hh
  intro C₁ C₂
  have h3 : (C₁ * C₂ + C₁ * C₂) = 0 := by linear_combination (C₁ * C₂) * h2
  have h5 : ((g 0 0 * C₁ + g 0 1 * C₂) * (h 1 0 * C₁ + h 1 1 * C₂) +
        (h 0 0 * C₁ + h 0 1 * C₂) * (g 1 0 * C₁ + g 1 1 * C₂)) *
          QuadraticMap.polar q u' v' = 0 := by
    rw [E C₁ C₂ C₁ C₂, h3, zero_mul, mul_zero]
  have h4 := (mul_eq_zero.mp h5).resolve_right hne
  linear_combination h4 - ((h 0 0 * C₁ + h 0 1 * C₂) * (g 1 0 * C₁ + g 1 1 * C₂)) * h2

private theorem seg_common_partner (q : QuadraticForm K (ι → K)) (hnd : PolarFormNondeg q)
    {u v : ι → K} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu : q u = 0)
    (huv : QuadraticMap.polar q u v = 0) :
    ∃ w, q w = 0 ∧ QuadraticMap.polar q u w ≠ 0 ∧ QuadraticMap.polar q v w ≠ 0 := by
  have h2 : (2 : K) = 0 := seg_two
  obtain ⟨a, ha⟩ := seg_exists_one q hnd hu0
  obtain ⟨b, hb⟩ := seg_exists_one q hnd hv0
  have h0 : ∃ w₀, QuadraticMap.polar q u w₀ ≠ 0 ∧ QuadraticMap.polar q v w₀ ≠ 0 := by
    by_cases h1 : QuadraticMap.polar q v a = 0
    · by_cases h3 : QuadraticMap.polar q u b = 0
      · refine ⟨a + b, ?_, ?_⟩
        · rw [QuadraticMap.polar_add_right, ha, h3]; simp
        · rw [QuadraticMap.polar_add_right, h1, hb]; simp
      · exact ⟨b, h3, by rw [hb]; exact one_ne_zero⟩
    · exact ⟨a, by rw [ha]; exact one_ne_zero, h1⟩
  obtain ⟨w₀, h1, h3⟩ := h0
  have hvu : QuadraticMap.polar q v u = 0 := by rw [QuadraticMap.polar_comm]; exact huv
  refine ⟨w₀ + (q w₀ * (QuadraticMap.polar q u w₀)⁻¹) • u, ?_, ?_, ?_⟩
  · rw [seg_q_add, QuadraticMap.map_smul, hu, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_comm q w₀ u, smul_eq_mul, smul_eq_mul]
    have : q w₀ * (QuadraticMap.polar q u w₀)⁻¹ * QuadraticMap.polar q u w₀ = q w₀ := by
      field_simp
    rw [this]
    linear_combination (q w₀) * h2
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, seg_polar_self]
    simpa using h1
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hvu]
    simpa using h3

private theorem seg_rep_all [Fintype ι] {q : QuadraticForm K (ι → K)} {σ : K ≃+* K} {ρ : K}
    {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)} (hF : IsSegreMap q σ ρ F) (hnd : PolarFormNondeg q)
    (hdim : 5 ≤ Fintype.card ι ∨ NoTotallySingularPlane q) {u v u' v' : ι → K}
    {g h : Matrix (Fin 2) (Fin 2) K} (hu0 : u ≠ 0) (hu : q u = 0) (hv0 : v ≠ 0)
    (hh : h.det ≠ 0) (hgu : SegRep σ F u u' g) (hhv : SegRep σ F v v' h) :
    ∃ l : K, ∀ i j, g i j = l * h i j := by
  by_cases huv : QuadraticMap.polar q u v = 0
  · obtain ⟨w, hw, h1, h2⟩ := seg_common_partner q hnd hu0 hv0 hu huv
    have hw0 : w ≠ 0 := fun h => h1 (by rw [h]; simp)
    obtain ⟨w', a, b, c, d, hw', hw'0, hdet, e1, e2⟩ := seg_step1 hF hnd hdim hw0 hw
    have hk : (!![a, c; b, d] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      intro h0
      apply hdet
      linear_combination h0
    have hkw := seg_rep_of_step1 hF e1 e2
    obtain ⟨l₁, hl₁⟩ := seg_rep_prop hF hk h1 hgu hkw
    obtain ⟨l₂, hl₂⟩ := seg_rep_prop hF hh (by rw [QuadraticMap.polar_comm]; exact h2) hkw hhv
    exact ⟨l₁ * l₂, fun i j => by rw [hl₁, hl₂, mul_assoc]⟩
  · exact seg_rep_prop hF hh huv hgu hhv

private theorem seg_rigid_core [Fintype ι] {q : QuadraticForm K (ι → K)} (hnd : PolarFormNondeg q)
    (hsing : ∃ u : ι → K, u ≠ 0 ∧ q u = 0)
    (hdim : 5 ≤ Fintype.card ι ∨ NoTotallySingularPlane q)
    {σ : K ≃+* K} {ρ : K} {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)}
    (hF : IsSegreMap q σ ρ F) :
    ∃ (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K)) (ρ' : K),
      g.det ≠ 0 ∧ ρ' ≠ 0 ∧ Function.Bijective o ∧ (∀ u v, o (u + v) = o u + o v) ∧
      (∀ (c : K) u, o (c • u) = σ c • o u) ∧ (∀ u, q (o u) = ρ' * σ (q u)) ∧
      ∀ p, F p = orthTensor g o p := by
  have h2 : (2 : K) = 0 := seg_two
  obtain ⟨u₀, hu₀0, hu₀⟩ := hsing
  obtain ⟨u₀', a₀, b₀, c₀, d₀, hu₀', hu₀'0, hdet₀, e₁, e₂⟩ := seg_step1 hF hnd hdim hu₀0 hu₀
  obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin 2) (Fin 2) K, g = !![a₀, c₀; b₀, d₀] := ⟨_, rfl⟩
  have hgdet : g.det ≠ 0 := by
    rw [hg, Matrix.det_fin_two_of]
    intro h0
    apply hdet₀
    linear_combination h0
  have hgrep : SegRep σ F u₀ u₀' g := by rw [hg]; exact seg_rep_of_step1 hF e₁ e₂
  have hsing' : ∀ u : ι → K, q u = 0 → ∃ y : ι → K, q y = 0 ∧
      F (u, 0) = (g 0 0 • y, g 1 0 • y) ∧ F (0, u) = (g 0 1 • y, g 1 1 • y) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      refine ⟨0, QuadraticMap.map_zero _, ?_, ?_⟩
      · have : ((0 : ι → K), (0 : ι → K)) = 0 := rfl
        rw [this, hF.map_zero]
        exact Prod.ext (by simp) (by simp)
      · have : ((0 : ι → K), (0 : ι → K)) = 0 := rfl
        rw [this, hF.map_zero]
        exact Prod.ext (by simp) (by simp)
    · obtain ⟨u', a, b, c, d, hu', hu'0, hdet, f₁, f₂⟩ := seg_step1 hF hnd hdim hu0 hu
      have hrep := seg_rep_of_step1 hF f₁ f₂
      obtain ⟨l, hl⟩ := seg_rep_all hF hnd hdim hu0 hu hu₀0 hgdet hrep hgrep
      have ha : a = l * g 0 0 := by simpa using hl 0 0
      have hb : b = l * g 1 0 := by simpa using hl 1 0
      have hc : c = l * g 0 1 := by simpa using hl 0 1
      have hd : d = l * g 1 1 := by simpa using hl 1 1
      refine ⟨l • u', ?_, ?_, ?_⟩
      · rw [QuadraticMap.map_smul, hu', smul_zero]
      · rw [f₁, ha, hb]
        exact Prod.ext (by simp [smul_smul, mul_comm]) (by simp [smul_smul, mul_comm])
      · rw [f₂, hc, hd]
        exact Prod.ext (by simp [smul_smul, mul_comm]) (by simp [smul_smul, mul_comm])
  have hcol : g 0 0 ≠ 0 ∨ g 1 0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hgdet
    rw [Matrix.det_fin_two, hcon.1, hcon.2]
    ring
  obtain ⟨α', β', hαβ⟩ : ∃ α' β' : K, α' * g 0 0 + β' * g 1 0 = 1 := by
    rcases hcol with h | h
    · exact ⟨(g 0 0)⁻¹, 0, by field_simp; ring⟩
    · exact ⟨0, (g 1 0)⁻¹, by field_simp; ring⟩
  obtain ⟨o, ho_def⟩ : ∃ o : (ι → K) → (ι → K),
      ∀ x, o x = α' • (F (x, 0)).1 + β' • (F (x, 0)).2 := ⟨fun x => _, fun x => rfl⟩
  have ho_pure : ∀ x y, F (x, 0) = (g 0 0 • y, g 1 0 • y) → o x = y := by
    intro x y h
    rw [ho_def, h]
    simp only
    rw [smul_smul, smul_smul, ← add_smul, hαβ, one_smul]
  have ho_add : ∀ x y, o (x + y) = o x + o y := by
    intro x y
    have e : ((x + y, 0) : (ι → K) × (ι → K)) = (x, 0) + (y, 0) := by simp
    rw [ho_def, ho_def, ho_def, e, hF.add]
    simp only [Prod.fst_add, Prod.snd_add, smul_add]
    abel
  have ho_zero : o 0 = 0 := by
    have := ho_add 0 0
    simpa using this
  have ho_smul : ∀ (c : K) x, o (c • x) = σ c • o x := by
    intro c x
    have e : ((c • x, 0) : (ι → K) × (ι → K)) = c • (x, 0) := by simp
    rw [ho_def, ho_def, e, hF.smul]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_add]
    rw [smul_comm α' (σ c), smul_comm β' (σ c)]
  have hspan := seg_span_sing q hnd ⟨u₀, hu₀0, hu₀⟩
  have key1 : ∀ x, ∃ y, F (x, 0) = (g 0 0 • y, g 1 0 • y) := by
    intro x
    have hx := hspan x
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, _, h1, _⟩ := hsing' x hx
      exact ⟨y, h1⟩
    | zero =>
      refine ⟨0, ?_⟩
      have e : ((0 : ι → K), (0 : ι → K)) = 0 := rfl
      rw [e, hF.map_zero]
      exact Prod.ext (by simp) (by simp)
    | add x y _ _ ihx ihy =>
      obtain ⟨y₁, h₁⟩ := ihx
      obtain ⟨y₂, h₂⟩ := ihy
      refine ⟨y₁ + y₂, ?_⟩
      have e : ((x + y, 0) : (ι → K) × (ι → K)) = (x, 0) + (y, 0) := by simp
      rw [e, hF.add, h₁, h₂]
      exact Prod.ext (by simp [smul_add]) (by simp [smul_add])
    | smul c x _ ihx =>
      obtain ⟨y₁, h₁⟩ := ihx
      refine ⟨σ c • y₁, ?_⟩
      have e : ((c • x, 0) : (ι → K) × (ι → K)) = c • (x, 0) := by simp
      rw [e, hF.smul, h₁]
      exact Prod.ext (smul_comm _ _ _) (smul_comm _ _ _)
  have ho_col1 : ∀ x, F (x, 0) = (g 0 0 • o x, g 1 0 • o x) := by
    intro x
    obtain ⟨y, hy⟩ := key1 x
    rw [ho_pure x y hy]
    exact hy
  have hosing : ∀ u, q u = 0 → q (o u) = 0 ∧ F (0, u) = (g 0 1 • o u, g 1 1 • o u) := by
    intro u hu
    obtain ⟨y, hyq, h1, h2⟩ := hsing' u hu
    rw [ho_pure u y h1]
    exact ⟨hyq, h2⟩
  have ho_col2 : ∀ x, F (0, x) = (g 0 1 • o x, g 1 1 • o x) := by
    intro x
    have hx := hspan x
    induction hx using Submodule.span_induction with
    | mem x hx => exact (hosing x hx).2
    | zero =>
      have e : ((0 : ι → K), (0 : ι → K)) = 0 := rfl
      rw [e, hF.map_zero, ho_zero]
      exact Prod.ext (by simp) (by simp)
    | add x y _ _ ihx ihy =>
      have e : ((0, x + y) : (ι → K) × (ι → K)) = (0, x) + (0, y) := by simp
      rw [e, hF.add, ihx, ihy, ho_add]
      exact Prod.ext (by simp [smul_add]) (by simp [smul_add])
    | smul c x _ ihx =>
      have e : ((0, c • x) : (ι → K) × (ι → K)) = c • (0, x) := by simp
      rw [e, hF.smul, ihx, ho_smul]
      exact Prod.ext (smul_comm _ _ _) (smul_comm _ _ _)
  have hFo : ∀ p, F p = orthTensor g o p := by
    rintro ⟨a, b⟩
    have e : ((a, b) : (ι → K) × (ι → K)) = (a, 0) + (0, b) := by simp
    rw [e, hF.add, ho_col1, ho_col2]
    exact Prod.ext (by simp [orthTensor]) (by simp [orthTensor])
  have hD : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by rwa [Matrix.det_fin_two] at hgdet
  have ho_ker : ∀ x, o x = 0 → x = 0 := by
    intro x hx
    have h1 := ho_col1 x
    rw [hx] at h1
    have h0 : F (x, 0) = F 0 := by
      rw [h1, hF.map_zero]
      exact Prod.ext (by simp) (by simp)
    exact congrArg Prod.fst (hF.bij.1 h0)
  have ho_inj : Function.Injective o := by
    intro x y hxy
    have h1 : o (x + y) = 0 := by rw [ho_add, hxy]; exact seg_add_self (K := K) _
    have h3 := ho_ker _ h1
    calc x = x + (y + y) := by rw [seg_add_self (K := K), add_zero]
      _ = (x + y) + y := by rw [add_assoc]
      _ = y := by rw [h3, zero_add]
  have ho_surj : Function.Surjective o := by
    intro y
    obtain ⟨p, hp⟩ := hF.bij.2 (g 0 0 • y, g 1 0 • y)
    rw [hFo] at hp
    have e1 : g 0 0 • o p.1 + g 0 1 • o p.2 = g 0 0 • y := congrArg Prod.fst hp
    have e2 : g 1 0 • o p.1 + g 1 1 • o p.2 = g 1 0 • y := congrArg Prod.snd hp
    refine ⟨p.1, ?_⟩
    have : (g 0 0 * g 1 1 - g 0 1 * g 1 0) • o p.1 = (g 0 0 * g 1 1 - g 0 1 * g 1 0) • y := by
      calc (g 0 0 * g 1 1 - g 0 1 * g 1 0) • o p.1
          = g 1 1 • (g 0 0 • o p.1 + g 0 1 • o p.2) - g 0 1 • (g 1 0 • o p.1 + g 1 1 • o p.2) := by
            module
        _ = g 1 1 • (g 0 0 • y) - g 0 1 • (g 1 0 • y) := by rw [e1, e2]
        _ = (g 0 0 * g 1 1 - g 0 1 * g 1 0) • y := by module
    exact smul_right_injective _ hD this
  have hBo : ∀ a b, QuadraticMap.polar q (o a) (o b) =
      (ρ * (g 0 0 * g 1 1 - g 0 1 * g 1 0)⁻¹) * σ (QuadraticMap.polar q a b) := by
    intro a b
    have h3 := hF.form (a, b)
    rw [hFo] at h3
    simp only [orthTensor] at h3
    rw [seg_polar_comb, seg_polar_self, seg_polar_self, QuadraticMap.polar_comm q (o b) (o a)] at h3
    have h4 : (g 0 0 * g 1 1 - g 0 1 * g 1 0) * QuadraticMap.polar q (o a) (o b) =
        ρ * σ (QuadraticMap.polar q a b) := by
      linear_combination h3 - (g 0 1 * g 1 0 * QuadraticMap.polar q (o a) (o b)) * h2
    field_simp
    linear_combination h4
  have hρ₂ : ρ * (g 0 0 * g 1 1 - g 0 1 * g 1 0)⁻¹ ≠ 0 := mul_ne_zero hF.ρ_ne (inv_ne_zero hD)
  obtain ⟨ρ₂, hρ₂def⟩ : ∃ ρ₂ : K, ρ₂ = ρ * (g 0 0 * g 1 1 - g 0 1 * g 1 0)⁻¹ := ⟨_, rfl⟩
  rw [← hρ₂def] at hρ₂ hBo
  have hq : ∀ x, q (o x) = ρ₂ * σ (q x) := by
    intro x
    have hx := hspan x
    induction hx using Submodule.span_induction with
    | mem x hx => rw [(hosing x hx).1, hx, map_zero, mul_zero]
    | zero => rw [ho_zero, QuadraticMap.map_zero, map_zero, mul_zero]
    | add x y _ _ ihx ihy =>
      rw [ho_add, seg_q_add, hBo, ihx, ihy, seg_q_add (q := q) x y, map_add, map_add]
      ring
    | smul c x _ ihx =>
      rw [ho_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, ihx]
      simp only [smul_eq_mul, map_mul]
      ring
  exact ⟨g, o, ρ₂, hgdet, hρ₂, ⟨ho_inj, ho_surj⟩, ho_add, ho_smul, hq, hFo⟩

private theorem seg_card_ge_four [Fintype ι] (q : QuadraticForm K (ι → K)) (hnd : PolarFormNondeg q)
    {s t : ι → K} (hst : QuadraticMap.polar q s t = 0)
    (hind : ∀ a b : K, a • s + b • t = 0 → a = 0 ∧ b = 0) : 4 ≤ Fintype.card ι := by
  have hind' : ∀ a b : K, a • t + b • s = 0 → a = 0 ∧ b = 0 := fun a b h =>
    (hind b a (by rw [add_comm]; exact h)).symm
  have hts : QuadraticMap.polar q t s = 0 := by rw [QuadraticMap.polar_comm]; exact hst
  obtain ⟨v, hv1, hv2⟩ := seg_exists_pair q hnd hind
  obtain ⟨v', hv1', hv2'⟩ := seg_exists_pair q hnd hind'
  have hli : LinearIndependent K ![s, t, v, v'] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
    have e1 := congrArg (QuadraticMap.polar q s) hg
    have e2 := congrArg (QuadraticMap.polar q t) hg
    simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_zero_right, seg_polar_self, hst, hv1, hv2', hts, hv2, hv1',
      smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at e1 e2
    have hg3 : g 3 = 0 := e2
    have hg2 : g 2 = 0 := e1
    rw [hg2, hg3, zero_smul, zero_smul, add_zero, add_zero] at hg
    obtain ⟨h0, h1⟩ := hind _ _ hg
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact hg2
    · exact hg3
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin, Module.finrank_fintype_fun_eq_card K] at this

theorem segre_rigid [Fintype ι] {q : QuadraticForm K (ι → K)}
    (hnd : PolarFormNondeg q) (hsing : ∃ u : ι → K, u ≠ 0 ∧ q u = 0)
    (hdim : Fintype.card ι ≠ 4 ∨ NoTotallySingularPlane q)
    {σ : K ≃+* K} {ρ : K} {F : (ι → K) × (ι → K) → (ι → K) × (ι → K)}
    (hF : IsSegreMap q σ ρ F) :
    ∃ (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K)) (ρ' : K),
      g.det ≠ 0 ∧ ρ' ≠ 0 ∧ Function.Bijective o ∧ (∀ u v, o (u + v) = o u + o v) ∧
      (∀ (c : K) u, o (c • u) = σ c • o u) ∧ (∀ u, q (o u) = ρ' * σ (q u)) ∧
      ∀ p, F p = orthTensor g o p := by
  refine seg_rigid_core hnd hsing ?_ hF
  rcases hdim with h | h
  · by_cases hno : NoTotallySingularPlane q
    · exact Or.inr hno
    · left
      have hno' := hno
      unfold NoTotallySingularPlane at hno'
      push Not at hno'
      obtain ⟨s, t, _, _, hst, hind⟩ := hno'
      have := seg_card_ge_four q hnd hst hind
      omega
  · exact Or.inr h

end Char2

end Segre

section Bridge

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem orthCoords_sim_of_act {M Q Z : Subgroup G} {K : Type} [Field K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}
    (hfr : OrthFrame Q Z M₀ qU φ) (hmod : GlobalModelData M Q Z γ M₀)
    (hQ : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q)
    (hroot : ∃ z ∈ Z, z ≠ 1 ∧ ∃ x ∈ Q, x ∉ Z ∧ IsConj z x)
    (hdim : Fintype.card ι ≠ 4 ∨ NoTotallySingularPlane qU) :
    ∀ m ∈ M, ∃ (σ : K ≃+* K) (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K)) (ρ : K),
      g.det ≠ 0 ∧ ρ ≠ 0 ∧ Function.Bijective o ∧ (∀ u v, o (u + v) = o u + o v) ∧
        (∀ (c : K) u, o (c • u) = σ c • o u) ∧ (∀ u, qU (o u) = ρ * σ (qU u)) ∧
        ∀ x ∈ Q, φ (M₀.π (m * x * m⁻¹)) = orthTensor g o (φ (M₀.π x)) := by
  intro m hm
  obtain ⟨σ, a, T, hTsmul, hTπ, -, hTQ⟩ := hmod.act m hm
  obtain ⟨z, hzZ, hz1, x₀, hx₀Q, hx₀Z, hx₀c⟩ := hroot
  have hsing : ∃ u : ι → K, u ≠ 0 ∧ qU u = 0 := by
    obtain ⟨c₁, c₂, u, _, hu0, hu, _⟩ := (hfr.root z hzZ hz1 x₀ hx₀Q hx₀Z).mp hx₀c
    exact ⟨u, hu0, hu⟩
  have hF0 : φ (T (φ.symm 0)) = 0 := by simp
  have hSeg : IsSegreMap qU σ (a : K) (fun p => φ (T (φ.symm p))) :=
    { ρ_ne := a.ne_zero
      bij := φ.bijective.comp (T.bijective.comp φ.symm.bijective)
      add := fun p p' => by simp
      smul := fun c p => by simp [hTsmul]
      form := fun p => by
        have h1 := hfr.qf (T (φ.symm p))
        have h2 := hfr.qf (φ.symm p)
        rw [hTQ, h2] at h1
        simpa using h1.symm
      typeA := fun p => by
        obtain ⟨x, hxQ, hx⟩ := M₀.π_surj (φ.symm p)
        have hp : p = φ (M₀.π x) := by rw [hx, LinearEquiv.apply_symm_apply]
        have hFp : φ (T (φ.symm p)) = φ (M₀.π (m * x * m⁻¹)) := by rw [hTπ x hxQ, hx]
        by_cases hxZ : x ∈ Z
        · have h0 : M₀.π x = 0 := (M₀.π_ker x hxQ).mpr hxZ
          have hp0 : p = 0 := by rw [hp, h0, map_zero]
          subst hp0
          simp only [hF0]
        · have hmQ := hQ m hm x hxQ
          have hmZ : m * x * m⁻¹ ∉ Z := by
            intro h
            have h0 := (M₀.π_ker _ hmQ).mpr h
            rw [hTπ x hxQ] at h0
            have : M₀.π x = 0 := T.injective (by rw [h0, map_zero])
            exact hxZ ((M₀.π_ker x hxQ).mp this)
          show PairTypeA qU (φ (T (φ.symm p))) ↔ PairTypeA qU p
          rw [hFp, hp, ← hfr.root z hzZ hz1 _ hmQ hmZ, ← hfr.root z hzZ hz1 x hxQ hxZ]
          exact ⟨fun h => h.trans (isConj_iff.mpr ⟨m⁻¹, by group⟩),
            fun h => h.trans (isConj_iff.mpr ⟨m, rfl⟩)⟩ }
  obtain ⟨g, o, ρ', hg, hρ', hbij, hadd, hsmul, hq, hFo⟩ :=
    segre_rigid hfr.nondeg hsing hdim hSeg
  refine ⟨σ, g, o, ρ', hg, hρ', hbij, hadd, hsmul, hq, fun x hx => ?_⟩
  rw [hTπ x hx]
  have := hFo (φ (M₀.π x))
  simpa using this

end Bridge

end CFSG.RankThree.GF2n.Smith81
