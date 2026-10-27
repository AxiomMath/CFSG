module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLift

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Lift

variable {G : Type*} [Group G] [Finite G]

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem inv_inverts {τ : G} (hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹) :
    ∀ y ∈ BO b₁ b₂ b₃, τ⁻¹ * y * τ⁻¹⁻¹ = y⁻¹ := by
  intro y hy
  have h := hτ y⁻¹ (inv_mem hy)
  rw [inv_inv] at h
  calc τ⁻¹ * y * τ⁻¹⁻¹ = τ⁻¹ * (τ * y⁻¹ * τ⁻¹) * τ⁻¹⁻¹ := by rw [h]
    _ = y⁻¹ := by group

theorem fix_tau {τ : G} (hτb : τ * b * τ⁻¹ = b) (hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹)
    {z : G} (hz : z ∈ BB b b₁ b₂ b₃) (hzτ : τ * z * τ⁻¹ = z) : ∃ n : ℕ, z = b ^ n := by
  obtain ⟨n, -, y, hy, rfl⟩ := D.exists_of_mem_B hz
  refine ⟨n, ?_⟩
  have e : τ * (b ^ n * y) * τ⁻¹ = b ^ n * y⁻¹ := by
    rw [show τ * (b ^ n * y) * τ⁻¹ = (τ * b * τ⁻¹) ^ n * (τ * y * τ⁻¹) by rw [conj_pow]; group,
      hτb, hτ y hy]
  rw [e] at hzτ
  have hyy : y⁻¹ = y := mul_left_cancel hzτ
  rw [D.eq_one_of_eq_inv (D.B₁3 y hy) hyy, mul_one]

theorem exists_frattini {τ : G}
    (hτN : τ ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hτb : τ * b * τ⁻¹ = b) (hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹) {g : G}
    (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) :
    ∃ a ∈ Ahat (BO b₁ b₂ b₃) b,
      (a⁻¹ * g) * τ * (a⁻¹ * g)⁻¹ * τ⁻¹ ∈
        Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
  set δ := g * τ * g⁻¹ * τ⁻¹ with hδdef
  have hτ' := D.inv_inverts hτ
  have hg' := inv_mem hg
  have hδA : δ ∈ Ahat (BO b₁ b₂ b₃) b := by
    refine ⟨fun y hy => ?_, ?_⟩
    · have hy₁ : g⁻¹ * y⁻¹ * g⁻¹⁻¹ ∈ BO b₁ b₂ b₃ := D.B₁N _ hg' _ (inv_mem hy)
      have e : δ * y * δ⁻¹ =
          g * (τ * (g⁻¹ * (τ⁻¹ * y * τ⁻¹⁻¹) * g⁻¹⁻¹) * τ⁻¹) * g⁻¹ := by
        rw [hδdef]; group
      rw [e, hτ' y hy, hτ _ hy₁]
      group
    · have hz : g⁻¹ * b * g⁻¹⁻¹ ∈ BB b b₁ b₂ b₃ := D.conj_mem_B hg' D.b_mem_B
      obtain ⟨n, -, y, hy, hzy⟩ := D.exists_of_mem_B hz
      have hτz : τ * (g⁻¹ * b * g⁻¹⁻¹) * τ⁻¹ = (g⁻¹ * b * g⁻¹⁻¹) * (y⁻¹ * y⁻¹) := by
        rw [hzy, show τ * (b ^ n * y) * τ⁻¹ = (τ * b * τ⁻¹) ^ n * (τ * y * τ⁻¹) by
          rw [conj_pow]; group, hτb, hτ y hy]
        group
      have hτbi : τ⁻¹ * b * τ⁻¹⁻¹ = b := by
        calc τ⁻¹ * b * τ⁻¹⁻¹ = τ⁻¹ * (τ * b * τ⁻¹) * τ⁻¹⁻¹ := by rw [hτb]
          _ = b := by group
      have e : δ * b * δ⁻¹ * b⁻¹ =
          g * (τ * (g⁻¹ * b * g⁻¹⁻¹) * τ⁻¹) * g⁻¹ * b⁻¹ := by
        rw [hδdef]
        calc g * τ * g⁻¹ * τ⁻¹ * b * (g * τ * g⁻¹ * τ⁻¹)⁻¹ * b⁻¹
            = g * (τ * (g⁻¹ * (τ⁻¹ * b * τ⁻¹⁻¹) * g⁻¹⁻¹) * τ⁻¹) * g⁻¹ * b⁻¹ := by group
          _ = _ := by rw [hτbi]
      rw [e, hτz, show g * (g⁻¹ * b * g⁻¹⁻¹ * (y⁻¹ * y⁻¹)) * g⁻¹ * b⁻¹ =
          b * (g * (y⁻¹ * y⁻¹) * g⁻¹) * b⁻¹ by group]
      have h1 : g * (y⁻¹ * y⁻¹) * g⁻¹ ∈ BO b₁ b₂ b₃ :=
        D.B₁N g hg _ (mul_mem (inv_mem hy) (inv_mem hy))
      rw [D.bB₁ _ h1, mul_inv_cancel_right]
      exact h1
  obtain ⟨a, ha⟩ : ∃ a : G, a = δ ^ 2 := ⟨_, rfl⟩
  have haA : a ∈ Ahat (BO b₁ b₂ b₃) b := ha ▸ pow_mem hδA 2
  have hβa : beta b a = beta b δ ^ 2 := by rw [ha, D.beta_pow hδA]
  refine ⟨a, haA, ?_⟩
  have hτaA : τ * a * τ⁻¹ ∈ Ahat (BO b₁ b₂ b₃) b := D.conj_mem_Ahat hτN haA
  have e : (a⁻¹ * g) * τ * (a⁻¹ * g)⁻¹ * τ⁻¹ = a⁻¹ * δ * (τ * a * τ⁻¹) := by
    rw [hδdef]; group
  rw [e]
  refine D.mem_cen_of_beta (mul_mem (mul_mem (inv_mem haA) hδA) hτaA) ?_
  rw [beta_mul D.B₁ab (mul_mem (inv_mem haA) hδA) hτaA, beta_mul D.B₁ab (inv_mem haA) hδA,
    D.beta_inv haA, beta_conj hτb, hτ _ (beta_mem haA), hβa]
  have h3 : beta b δ ^ 3 = 1 := D.B₁3 _ (beta_mem hδA)
  have hc : Commute (beta b δ ^ 2)⁻¹ (beta b δ) :=
    ((Commute.refl (beta b δ)).pow_left 2).inv_left
  calc (beta b δ ^ 2)⁻¹ * beta b δ * (beta b δ ^ 2)⁻¹
      = (beta b δ ^ 2)⁻¹ * (beta b δ ^ 2)⁻¹ * beta b δ := by
        rw [mul_assoc, (hc.symm).eq, ← mul_assoc]
    _ = (beta b δ ^ 3)⁻¹ * (beta b δ ^ 3)⁻¹ * beta b δ ^ 3 := by group
    _ = 1 := by rw [h3]; group

theorem conj_b_pm {τ c : G}
    (hτN : τ ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hτb : τ * b * τ⁻¹ = b) (hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹)
    (hc : c ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hcτ : c * τ * c⁻¹ * τ⁻¹ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) :
    c * b * c⁻¹ = b ∨ c * b * c⁻¹ = b⁻¹ := by
  have hz : c * b * c⁻¹ ∈ BB b b₁ b₂ b₃ := D.conj_mem_B hc D.b_mem_B
  have hfix : τ * (c * b * c⁻¹) * τ⁻¹ = c * b * c⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp hcτ _ hz
    have e1 : (c * τ * c⁻¹) * (c * b * c⁻¹) * (c * τ * c⁻¹)⁻¹ = c * b * c⁻¹ := by
      calc (c * τ * c⁻¹) * (c * b * c⁻¹) * (c * τ * c⁻¹)⁻¹ = c * (τ * b * τ⁻¹) * c⁻¹ := by group
        _ = c * b * c⁻¹ := by rw [hτb]
    have e2 : (c * τ * c⁻¹) * (c * b * c⁻¹) * (c * τ * c⁻¹)⁻¹ =
        (c * τ * c⁻¹ * τ⁻¹) * (τ * (c * b * c⁻¹) * τ⁻¹) * (c * τ * c⁻¹ * τ⁻¹)⁻¹ := by group
    rw [e2] at e1
    have e3 : (c * τ * c⁻¹ * τ⁻¹) * (τ * (c * b * c⁻¹) * τ⁻¹) * (c * τ * c⁻¹ * τ⁻¹)⁻¹ =
        τ * (c * b * c⁻¹) * τ⁻¹ := by
      have hz' : τ * (c * b * c⁻¹) * τ⁻¹ ∈ BB b b₁ b₂ b₃ := D.conj_mem_B hτN hz
      have h2 := Subgroup.mem_centralizer_iff.mp hcτ _ hz'
      rw [← h2, mul_inv_cancel_right]
    rw [e3] at e1
    exact e1
  obtain ⟨n, hn⟩ := D.fix_tau hτb hτ hz hfix
  have hb3 := D.b3
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · exfalso
    rw [pow_eq_pow_mod n hb3, h, pow_zero] at hn
    have : b = 1 := by
      calc b = c⁻¹ * (c * b * c⁻¹) * c := by group
        _ = 1 := by rw [hn]; group
    exact D.b_not_mem (this ▸ one_mem _)
  · left; rw [hn, pow_eq_pow_mod n hb3, h, pow_one]
  · right
    rw [hn, pow_eq_pow_mod n hb3, h]
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hb3]

theorem mono_of_mem {τ : G}
    (hτN : τ ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hτb : τ * b * τ⁻¹ = b) (hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹)
    (hmono : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    {g : G} (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) :
    ∀ x ∈ ({b₁, b₂, b₃} : Set G), g * x * g⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
  obtain ⟨a, haA, hc⟩ := D.exists_frattini hτN hτb hτ hg
  have hcN : a⁻¹ * g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) :=
    mul_mem (inv_mem (D.Ahat_le_N haA)) hg
  have hcm := hmono _ hcN (D.conj_b_pm hτN hτb hτ hcN hc)
  intro x hx
  have hxB : x ∈ BO b₁ b₂ b₃ := Subgroup.subset_closure hx
  have h1 := hcm x hx
  have hmem : (a⁻¹ * g) * x * (a⁻¹ * g)⁻¹ ∈ BO b₁ b₂ b₃ := D.B₁N _ hcN x hxB
  have e : g * x * g⁻¹ = a * ((a⁻¹ * g) * x * (a⁻¹ * g)⁻¹) * a⁻¹ := by group
  rw [e, haA.1 _ hmem]
  exact h1

end Data0

theorem eq_pow_sq {n : G} {k : ℕ} (hn : n ^ (3 ^ k) = 1) : n = (n ^ 2) ^ ((3 ^ k + 1) / 2) := by
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  rw [← pow_mul, show 2 * ((3 ^ k + 1) / 2) = 3 ^ k + 1 by omega, pow_succ, hn, one_mul]

theorem fix_of_pm {n x : G} {k : ℕ} (hn : n ^ (3 ^ k) = 1)
    (hx : n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹) : n * x * n⁻¹ = x := by
  have h2 : n ^ 2 * x * (n ^ 2)⁻¹ = x := by
    rw [pow_two, show n * n * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ by group]
    rcases hx with e | e
    · rw [e, e]
    · rw [e, show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group, e, inv_inv]
  have := pow_conj_fix h2 ((3 ^ k + 1) / 2)
  rwa [← eq_pow_sq hn] at this

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem triv_mul {g h : G} (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hgb : g * b * g⁻¹ * b⁻¹ ∈ BO b₁ b₂ b₃) (hhb : h * b * h⁻¹ * b⁻¹ ∈ BO b₁ b₂ b₃) :
    (g * h) * b * (g * h)⁻¹ * b⁻¹ ∈ BO b₁ b₂ b₃ := by
  have e : (g * h) * b * (g * h)⁻¹ * b⁻¹ =
      (g * (h * b * h⁻¹ * b⁻¹) * g⁻¹) * (g * b * g⁻¹ * b⁻¹) := by group
  rw [e]
  exact mul_mem (D.B₁N g hg _ hhb) hgb

theorem triv_pow {g : G} (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hgb : g * b * g⁻¹ * b⁻¹ ∈ BO b₁ b₂ b₃) (m : ℕ) :
    g ^ m * b * (g ^ m)⁻¹ * b⁻¹ ∈ BO b₁ b₂ b₃ := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ]; exact D.triv_mul (pow_mem hg m) ih hgb

theorem triv_of_three {n : G} (hnN : n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    {k : ℕ} (hn3 : n ^ (3 ^ k) = 1) : n * b * n⁻¹ * b⁻¹ ∈ BO b₁ b₂ b₃ := by
  obtain ⟨j, hj, y, hy, hjy⟩ := D.exists_of_mem_B (D.conj_mem_B hnN D.b_mem_B)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hjy
    apply D.b_not_mem
    have := D.B₁N _ (inv_mem hnN) _ (hjy ▸ hy : n * b * n⁻¹ ∈ BO b₁ b₂ b₃)
    rwa [show n⁻¹ * (n * b * n⁻¹) * n⁻¹⁻¹ = b by group] at this
  have hny : n * y * n⁻¹ ∈ BO b₁ b₂ b₃ := D.B₁N n hnN y hy
  have hbc : ∀ z ∈ BO b₁ b₂ b₃, Commute b z := fun z hz => D.bB₁ z hz
  have h2 : n ^ 2 * b * (n ^ 2)⁻¹ * b⁻¹ ∈ BO b₁ b₂ b₃ := by
    have e1 : n ^ 2 * b * (n ^ 2)⁻¹ = (b ^ j * y) ^ j * (n * y * n⁻¹) := by
      calc n ^ 2 * b * (n ^ 2)⁻¹ = n * (n * b * n⁻¹) * n⁻¹ := by rw [pow_two]; group
        _ = n * (b ^ j * y) * n⁻¹ := by rw [hjy]
        _ = (n * b ^ j * n⁻¹) * (n * y * n⁻¹) := by group
        _ = (n * b * n⁻¹) ^ j * (n * y * n⁻¹) := by rw [conj_pow]
        _ = (b ^ j * y) ^ j * (n * y * n⁻¹) := by rw [hjy]
    rw [e1, ((hbc y hy).pow_left j).mul_pow, ← pow_mul]
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
    · rw [show (1 : ℕ) * 1 = 1 by rfl, pow_one, pow_one,
        show b * y * (n * y * n⁻¹) * b⁻¹ = b * (y * (n * y * n⁻¹)) * b⁻¹ by group,
        hbc _ (mul_mem hy hny) |>.eq, mul_inv_cancel_right]
      exact mul_mem hy hny
    · rw [show 2 * 2 = 3 + 1 by rfl, pow_succ, D.b3, one_mul,
        show b * y ^ 2 * (n * y * n⁻¹) * b⁻¹ = b * (y ^ 2 * (n * y * n⁻¹)) * b⁻¹ by group,
        hbc _ (mul_mem (pow_mem hy 2) hny) |>.eq, mul_inv_cancel_right]
      exact mul_mem (pow_mem hy 2) hny
  have := D.triv_pow (pow_mem hnN 2) h2 ((3 ^ k + 1) / 2)
  rwa [← eq_pow_sq hn3] at this

theorem mem_Ahat_of_three {n : G}
    (hnN : n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    {k : ℕ} (hn3 : n ^ (3 ^ k) = 1)
    (hmn : ∀ x ∈ ({b₁, b₂, b₃} : Set G),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (h1 : n * b₁ * n⁻¹ = b₁ ∨ n * b₁ * n⁻¹ = b₁⁻¹) : n ∈ Ahat (BO b₁ b₂ b₃) b := by
  obtain ⟨n21, n21', n31, n31', n32, n32'⟩ := D.gens_ne
  have hiv : ∀ x : G, n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := fun _ => by group
  have hinj : ∀ {u v : G}, n * u * n⁻¹ = n * v * n⁻¹ → u = v := fun e =>
    mul_left_cancel (mul_right_cancel e)
  have hinj' : ∀ {u v : G}, n * u * n⁻¹ = (n * v * n⁻¹)⁻¹ → u = v⁻¹ := fun e =>
    hinj (e.trans (hiv _).symm)
  have hb₁ : n * b₁ * n⁻¹ = b₁ := fix_of_pm hn3 h1
  have hb₂pm : n * b₂ * n⁻¹ = b₂ ∨ n * b₂ * n⁻¹ = b₂⁻¹ := by
    have hcase : (n * b₂ * n⁻¹ = b₂ ∨ n * b₂ * n⁻¹ = b₂⁻¹) ∨
        (n * b₂ * n⁻¹ = b₃ ∨ n * b₂ * n⁻¹ = b₃⁻¹) := by
      rcases hmn b₂ (by simp) with e | e | e | e | e | e
      · exact absurd (hinj (e.trans hb₁.symm)) n21
      · exact absurd (hinj' (e.trans (by rw [hb₁]))) n21'
      · exact Or.inl (Or.inl e)
      · exact Or.inl (Or.inr e)
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
    rcases hcase with h | he
    · exact h
    exfalso
    have hb₃pm : n * b₃ * n⁻¹ = b₂ ∨ n * b₃ * n⁻¹ = b₂⁻¹ := by
      rcases hmn b₃ (by simp) with f | f | f | f | f | f
      · exact absurd (hinj (f.trans hb₁.symm)) n31
      · exact absurd (hinj' (f.trans (by rw [hb₁]))) n31'
      · exact Or.inl f
      · exact Or.inr f
      · exfalso
        rcases he with e | e
        · exact n32 (hinj (f.trans e.symm))
        · have h23 : b₂ = b₃⁻¹ := hinj' (e.trans (by rw [f]))
          exact n32' (by rw [h23, inv_inv])
      · exfalso
        rcases he with e | e
        · have h23 : b₂ = b₃⁻¹ := hinj' (e.trans (by rw [f, inv_inv]))
          exact n32' (by rw [h23, inv_inv])
        · exact n32 (hinj (f.trans e.symm))
    have hn2 : (n ^ 2) ^ (3 ^ k) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hn3, one_pow]
    have e2 : n ^ 2 * b₂ * (n ^ 2)⁻¹ = n * (n * b₂ * n⁻¹) * n⁻¹ := by rw [pow_two]; group
    have h2pm : n ^ 2 * b₂ * (n ^ 2)⁻¹ = b₂ ∨ n ^ 2 * b₂ * (n ^ 2)⁻¹ = b₂⁻¹ := by
      rw [e2]
      rcases he with e | e <;> rcases hb₃pm with f | f <;> rw [e]
      · exact Or.inl f
      · exact Or.inr f
      · exact Or.inr (by rw [hiv, f])
      · exact Or.inl (by rw [hiv, f, inv_inv])
    have h2fix : n ^ 2 * b₂ * (n ^ 2)⁻¹ = b₂ := fix_of_pm hn2 h2pm
    have hnfix : n * b₂ * n⁻¹ = b₂ := by
      have := pow_conj_fix h2fix ((3 ^ k + 1) / 2)
      rwa [← eq_pow_sq hn3] at this
    rcases he with e | e
    · exact n32 (e.symm.trans hnfix)
    · have h23 : b₂ = b₃⁻¹ := hnfix.symm.trans e
      exact n32' (by rw [h23, inv_inv])
  have hb₂ : n * b₂ * n⁻¹ = b₂ := fix_of_pm hn3 hb₂pm
  have hb₃ : n * b₃ * n⁻¹ = b₃ := by
    refine fix_of_pm hn3 ?_
    rcases hmn b₃ (by simp) with f | f | f | f | f | f
    · exact absurd (hinj (f.trans hb₁.symm)) n31
    · exact absurd (hinj' (f.trans (by rw [hb₁]))) n31'
    · exact absurd (hinj (f.trans hb₂.symm)) n32
    · exact absurd (hinj' (f.trans (by rw [hb₂]))) n32'
    · exact Or.inl f
    · exact Or.inr f
  refine ⟨conj_eq_of_closure ?_, D.triv_of_three hnN hn3⟩
  rintro x (rfl | rfl | rfl)
  exacts [hb₁, hb₂, hb₃]

end Data0

theorem line_conj {r x y v : G} (h : r * x * r⁻¹ = y ∨ r * x * r⁻¹ = y⁻¹)
    (hv : v = y ∨ v = y⁻¹) : r⁻¹ * v * r = x ∨ r⁻¹ * v * r = x⁻¹ := by
  rcases hv with hv | hv <;> rw [hv] <;> rcases h with h | h
  · left; rw [← h]; group
  · right; rw [← inv_inv y, ← h]; group
  · right; rw [← h]; group
  · left; rw [← h]; group

namespace Data0

variable {b b₁ b₂ b₃ : G} (D : Data0 b b₁ b₂ b₃)
include D

theorem exists_normalize {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G} (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hN : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      ∀ x ∈ ({b₁, b₂, b₃} : Set G), n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    {NL : Subgroup G} (hNL : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ NL)
    {g : G} (hg : g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) :
    ∃ h ∈ NL, ∀ x ∈ ({b₁, b₂, b₃} : Set G), (h * g) * x * (h * g)⁻¹ = x := by
  set N := Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) with hNdef
  obtain ⟨hι₁N, hι₂N, hι₃N, hσ₁₂N, hσ₂₃N, hγN⟩ :
      ι₁ ∈ N ∧ ι₂ ∈ N ∧ ι₃ ∈ N ∧ σ₁₂ ∈ N ∧ σ₂₃ ∈ N ∧ γ ∈ N :=
    ⟨(M.mem ι₁ (by simp)).1, (M.mem ι₂ (by simp)).1, (M.mem ι₃ (by simp)).1,
      (M.mem σ₁₂ (by simp)).1, (M.mem σ₂₃ (by simp)).1, (M.mem γ (by simp)).1⟩
  obtain ⟨hι₁L, hι₂L, hι₃L, hσ₁₂L, hσ₂₃L, hγL⟩ :
      ι₁ ∈ NL ∧ ι₂ ∈ NL ∧ ι₃ ∈ NL ∧ σ₁₂ ∈ NL ∧ σ₂₃ ∈ NL ∧ γ ∈ NL :=
    ⟨hNL ι₁ (by simp), hNL ι₂ (by simp), hNL ι₃ (by simp), hNL σ₁₂ (by simp),
      hNL σ₂₃ (by simp), hNL γ (by simp)⟩
  have hcm : ∀ h k x : G, (h * k) * x * (h * k)⁻¹ = h * (k * x * k⁻¹) * h⁻¹ := fun _ _ _ => by
    group
  have hiv : ∀ h x : G, h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := fun _ _ => by group
  obtain ⟨n21, n21', n31, n31', n32, n32'⟩ := D.gens_ne
  have step1 : ∀ y ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G),
      ∃ h ∈ NL, h ∈ N ∧ h * y * h⁻¹ = b₁ := by
    rintro y (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, one_mem _, by simp⟩
    · exact ⟨ι₁, hι₁L, hι₁N, by rw [hiv, M.s₁.1, inv_inv]⟩
    · exact ⟨σ₁₂, hσ₁₂L, hσ₁₂N, M.p₁₂.2.1⟩
    · exact ⟨σ₁₂ * ι₂, mul_mem hσ₁₂L hι₂L, mul_mem hσ₁₂N hι₂N,
        by rw [hcm, hiv, M.s₂.2.1, inv_inv, M.p₁₂.2.1]⟩
    · exact ⟨γ, hγL, hγN, M.cyc.2.2⟩
    · exact ⟨γ * ι₃, mul_mem hγL hι₃L, mul_mem hγN hι₃N,
        by rw [hcm, hiv, M.s₃.2.2, inv_inv, M.cyc.2.2]⟩
  obtain ⟨h₁, hh₁L, hh₁N, hh₁⟩ := step1 _ (hN g hg b₁ (by simp))
  have hg₂N : h₁ * g ∈ N := mul_mem hh₁N hg
  have hg₂1 : (h₁ * g) * b₁ * (h₁ * g)⁻¹ = b₁ := by rw [hcm, hh₁]
  set g₂ := h₁ * g with hg₂def
  have hne : ∀ {u v : G}, u ≠ v → g₂ * u * g₂⁻¹ ≠ g₂ * v * g₂⁻¹ := fun huv e =>
    huv (mul_left_cancel (mul_right_cancel e))
  have hy2 := hN _ hg₂N b₂ (by simp)
  obtain ⟨h₂, hh₂L, hh₂N, hh₂1, hh₂⟩ : ∃ h ∈ NL, h ∈ N ∧ h * b₁ * h⁻¹ = b₁ ∧
      h * (g₂ * b₂ * g₂⁻¹) * h⁻¹ = b₂ := by
    rcases hy2 with e | e | e | e | e | e
    · exact absurd (e.trans hg₂1.symm) (hne n21)
    · exact absurd (e.trans (by rw [hiv, hg₂1])) (hne n21')
    · exact ⟨1, one_mem _, one_mem _, by simp, by rw [e]; simp⟩
    · exact ⟨ι₂, hι₂L, hι₂N, M.s₂.1, by rw [e, hiv, M.s₂.2.1, inv_inv]⟩
    · exact ⟨σ₂₃, hσ₂₃L, hσ₂₃N, M.p₂₃.1, by rw [e, M.p₂₃.2.2]⟩
    · exact ⟨σ₂₃ * ι₃, mul_mem hσ₂₃L hι₃L, mul_mem hσ₂₃N hι₃N,
        by rw [hcm, M.s₃.1, M.p₂₃.1], by rw [e, hcm, hiv, M.s₃.2.2, inv_inv, M.p₂₃.2.2]⟩
  have hg₃N : h₂ * g₂ ∈ N := mul_mem hh₂N hg₂N
  have hg₃1 : (h₂ * g₂) * b₁ * (h₂ * g₂)⁻¹ = b₁ := by rw [hcm, hg₂1, hh₂1]
  have hg₃2 : (h₂ * g₂) * b₂ * (h₂ * g₂)⁻¹ = b₂ := by rw [hcm, hh₂]
  set g₃ := h₂ * g₂ with hg₃def
  have hne3 : ∀ {u v : G}, u ≠ v → g₃ * u * g₃⁻¹ ≠ g₃ * v * g₃⁻¹ := fun huv e =>
    huv (mul_left_cancel (mul_right_cancel e))
  have hy3 := hN _ hg₃N b₃ (by simp)
  obtain ⟨h₃, hh₃L, hh₃1, hh₃2, hh₃⟩ : ∃ h ∈ NL, h * b₁ * h⁻¹ = b₁ ∧
      h * b₂ * h⁻¹ = b₂ ∧ h * (g₃ * b₃ * g₃⁻¹) * h⁻¹ = b₃ := by
    rcases hy3 with e | e | e | e | e | e
    · exact absurd (e.trans hg₃1.symm) (hne3 n31)
    · exact absurd (e.trans (by rw [hiv, hg₃1])) (hne3 n31')
    · exact absurd (e.trans hg₃2.symm) (hne3 n32)
    · exact absurd (e.trans (by rw [hiv, hg₃2])) (hne3 n32')
    · exact ⟨1, one_mem _, by simp, by simp, by rw [e]; simp⟩
    · exact ⟨ι₃, hι₃L, M.s₃.1, M.s₃.2.1, by rw [e, hiv, M.s₃.2.2, inv_inv]⟩
  refine ⟨h₃ * h₂ * h₁, mul_mem (mul_mem hh₃L hh₂L) hh₁L, ?_⟩
  have e : h₃ * h₂ * h₁ * g = h₃ * g₃ := by rw [hg₃def, hg₂def]; group
  rw [e]
  rintro y (rfl | rfl | rfl)
  · rw [hcm, hg₃1, hh₃1]
  · rw [hcm, hg₃2, hh₃2]
  · rw [hcm, hh₃]

theorem gen_of_no_inv {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G} (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hmono : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hno : ∀ g ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      g * b * g⁻¹ * b ∉ BO b₁ b₂ b₃)
    {NL : Subgroup G} (hNLN : NL ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hNLb : ∀ l ∈ NL, l * b * l⁻¹ = b)
    (hNL : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ NL)
    {n : G} (hn : n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) :
    ∃ l ∈ NL, n * l⁻¹ ∈ Ahat (BO b₁ b₂ b₃) b := by
  obtain ⟨hτN, hτb⟩ := M.mem τ (by simp)
  have hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹ := by
    refine conj_inv_of_closure D.B₁ab ?_
    rintro x (rfl | rfl | rfl)
    exacts [M.inv.1, M.inv.2.1, M.inv.2.2]
  obtain ⟨a, haA, hc⟩ := D.exists_frattini hτN hτb hτ hn
  have hcN : a⁻¹ * n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) :=
    mul_mem (inv_mem (D.Ahat_le_N haA)) hn
  have hcb : (a⁻¹ * n) * b * (a⁻¹ * n)⁻¹ = b := by
    rcases D.conj_b_pm hτN hτb hτ hcN hc with e | e
    · exact e
    · exfalso
      apply hno _ hcN
      rw [e, inv_mul_cancel]
      exact one_mem _
  obtain ⟨h, hhL, hh⟩ :=
    D.exists_normalize M (fun m hm => D.mono_of_mem hτN hτb hτ hmono hm) hNL hcN
  have hhN := hNLN hhL
  have hhb := hNLb h hhL
  have hhc : h * (a⁻¹ * n) ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
    refine D.mem_cen_of_gens ?_
    intro z hz
    rcases hz with hz | hz
    · rw [hz, show h * (a⁻¹ * n) * b * (h * (a⁻¹ * n))⁻¹ =
          h * ((a⁻¹ * n) * b * (a⁻¹ * n)⁻¹) * h⁻¹ by group, hcb, hhb]
    · exact hh z hz
  refine ⟨h⁻¹, inv_mem hhL, ?_⟩
  have e : n * h⁻¹⁻¹ = a * (h⁻¹ * (h * (a⁻¹ * n)) * h⁻¹⁻¹) := by group
  rw [e]
  exact mul_mem haA (D.conj_mem_Ahat (inv_mem hhN) (D.cen_le_Ahat hhc))

theorem surj_of_move {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G} (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hirr : ∀ H : Subgroup G, H ≤ BO b₁ b₂ b₃ → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        H = BO b₁ b₂ b₃)
    (hmove : ∃ m ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      m * b * m⁻¹ ∉ Subgroup.zpowers b) :
    ∀ y ∈ BO b₁ b₂ b₃, ∃ a : G, (∀ z ∈ BO b₁ b₂ b₃, a * z * a⁻¹ = z) ∧ a * b * a⁻¹ = y * b := by
  let I : Subgroup G :=
    { carrier := {y | ∃ a ∈ Ahat (BO b₁ b₂ b₃) b, beta b a = y}
      one_mem' := ⟨1, one_mem _, D.beta_one⟩
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        exact ⟨a * a', mul_mem ha ha', beta_mul D.B₁ab ha ha'⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨a⁻¹, inv_mem ha, D.beta_inv ha⟩ }
  have hIle : I ≤ BO b₁ b₂ b₃ := by
    rintro _ ⟨a, ha, rfl⟩
    exact beta_mem ha
  obtain ⟨hτN, hτb⟩ := M.mem τ (by simp)
  have hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹ := by
    refine conj_inv_of_closure D.B₁ab ?_
    rintro x (rfl | rfl | rfl)
    exacts [M.inv.1, M.inv.2.1, M.inv.2.2]
  have hIne : I ≠ ⊥ := by
    intro hI
    obtain ⟨m, hm, hmb⟩ := hmove
    obtain ⟨a, haA, hc⟩ := D.exists_frattini hτN hτb hτ hm
    have hcN : a⁻¹ * m ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) :=
      mul_mem (inv_mem (D.Ahat_le_N haA)) hm
    have hβa : beta b a = 1 := by
      have h1 : beta b a ∈ I := ⟨a, haA, rfl⟩
      rw [hI] at h1
      exact Subgroup.mem_bot.mp h1
    have hab : a * b * a⁻¹ = b := by rw [conj_b, hβa, one_mul]
    apply hmb
    have e : m * b * m⁻¹ = a * ((a⁻¹ * m) * b * (a⁻¹ * m)⁻¹) * a⁻¹ := by group
    rcases D.conj_b_pm hτN hτb hτ hcN hc with h | h
    · rw [e, h, hab]
      exact Subgroup.mem_zpowers b
    · rw [e, h, show a * b⁻¹ * a⁻¹ = (a * b * a⁻¹)⁻¹ by group, hab]
      exact inv_mem (Subgroup.mem_zpowers b)
  have hIinv : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ I, g * x * g⁻¹ ∈ I := by
    rintro g hg _ ⟨a, ha, rfl⟩
    obtain ⟨hgN, hgb⟩ := M.mem g (Set.mem_insert_of_mem τ hg)
    exact ⟨g * a * g⁻¹, D.conj_mem_Ahat hgN ha, beta_conj hgb a⟩
  have hIeq := hirr I hIle hIne hIinv
  intro y hy
  rw [← hIeq] at hy
  obtain ⟨a, ha, hay⟩ := hy
  exact ⟨a, ha.1, by rw [conj_b, hay]⟩

theorem toData {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G} (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hirr : ∀ H : Subgroup G, H ≤ BO b₁ b₂ b₃ → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        H = BO b₁ b₂ b₃)
    (hmove : ∃ m ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      m * b * m⁻¹ ∉ Subgroup.zpowers b) :
    Data b b₁ b₂ b₃ :=
  { toData0 := D
    surj := D.surj_of_move M hirr hmove }

end Data0

namespace Data

variable {b b₁ b₂ b₃ : G} (D : Data b b₁ b₂ b₃)
include D

theorem card_le_of_isPGroup {τ : G}
    (hτN : τ ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hτb : τ * b * τ⁻¹ = b) (hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹)
    (hmono : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (R : Subgroup G) (hRN : R ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))
    (hR : IsPGroup 3 R) : Nat.card R ≤ 3 ^ 8 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Â := Ahat (BO b₁ b₂ b₃) b with hÂdef
  have hBp : IsPGroup 3 ↥((BB b b₁ b₂ b₃).subgroupOf Â) := D.isPGroup_B.comap_subtype
  obtain ⟨S, hSle⟩ := hBp.exists_le_sylow
  have hS : BB b b₁ b₂ b₃ ≤ (S : Subgroup ↥Â).map Â.subtype := fun z hz =>
    ⟨⟨z, D.B_le_Ahat hz⟩, hSle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hRA : Nat.card ↥(R ⊓ Â) ≤ 3 ^ 7 := by
    obtain ⟨k, -, hkQ⟩ := exists_conj_le S (inf_le_right : R ⊓ Â ≤ Â) (hR.to_le inf_le_left)
    rw [← D.card_A0 hS]
    refine Nat.card_le_card_of_injective (fun q => ⟨k⁻¹ * q * k, hkQ q q.2⟩) ?_
    intro q q' e
    have e' : k⁻¹ * (q : G) * k = k⁻¹ * q' * k := congrArg Subtype.val e
    exact Subtype.ext (mul_left_cancel (mul_right_cancel e'))
  let f : ↥R → Fin 3 := fun r =>
    if (r : G) * b₁ * (r : G)⁻¹ = b₁ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₁⁻¹ then 0
    else if (r : G) * b₁ * (r : G)⁻¹ = b₂ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₂⁻¹ then 1 else 2
  have hfdef : ∀ r : ↥R, f r =
      if (r : G) * b₁ * (r : G)⁻¹ = b₁ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₁⁻¹ then 0
      else if (r : G) * b₁ * (r : G)⁻¹ = b₂ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₂⁻¹ then 1 else 2 :=
    fun _ => rfl
  have hf : ∀ r : ↥R,
      (f r = 0 ∧ ((r : G) * b₁ * (r : G)⁻¹ = b₁ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₁⁻¹)) ∨
      (f r = 1 ∧ ((r : G) * b₁ * (r : G)⁻¹ = b₂ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₂⁻¹)) ∨
      (f r = 2 ∧ ((r : G) * b₁ * (r : G)⁻¹ = b₃ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₃⁻¹)) := by
    intro r
    by_cases h1 : (r : G) * b₁ * (r : G)⁻¹ = b₁ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₁⁻¹
    · exact Or.inl ⟨by rw [hfdef, if_pos h1], h1⟩
    by_cases h2 : (r : G) * b₁ * (r : G)⁻¹ = b₂ ∨ (r : G) * b₁ * (r : G)⁻¹ = b₂⁻¹
    · exact Or.inr (Or.inl ⟨by rw [hfdef, if_neg h1, if_pos h2], h2⟩)
    refine Or.inr (Or.inr ⟨by rw [hfdef, if_neg h1, if_neg h2], ?_⟩)
    rcases D.mono_of_mem hτN hτb hτ hmono (hRN r.2) b₁ (by simp) with e | e | e | e | e | e
    · exact absurd (Or.inl e) h1
    · exact absurd (Or.inr e) h1
    · exact absurd (Or.inl e) h2
    · exact absurd (Or.inr e) h2
    · exact Or.inl e
    · exact Or.inr e
  have key : ∀ r s : ↥R, f r = f s → (r : G)⁻¹ * s ∈ Â := by
    intro r s e
    have hrs : (r : G)⁻¹ * s ∈ R := mul_mem (inv_mem r.2) s.2
    have hline : ∃ y : G, ((r : G) * b₁ * (r : G)⁻¹ = y ∨ (r : G) * b₁ * (r : G)⁻¹ = y⁻¹) ∧
        ((s : G) * b₁ * (s : G)⁻¹ = y ∨ (s : G) * b₁ * (s : G)⁻¹ = y⁻¹) := by
      rcases hf r with ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ <;>
        rcases hf s with ⟨hs, h'⟩ | ⟨hs, h'⟩ | ⟨hs, h'⟩
      · exact ⟨_, h, h'⟩
      · rw [hr, hs] at e; exact absurd e (by decide)
      · rw [hr, hs] at e; exact absurd e (by decide)
      · rw [hr, hs] at e; exact absurd e (by decide)
      · exact ⟨_, h, h'⟩
      · rw [hr, hs] at e; exact absurd e (by decide)
      · rw [hr, hs] at e; exact absurd e (by decide)
      · rw [hr, hs] at e; exact absurd e (by decide)
      · exact ⟨_, h, h'⟩
    obtain ⟨y, hy, hy'⟩ := hline
    obtain ⟨k, hk⟩ := hR ⟨_, hrs⟩
    have hk' : ((r : G)⁻¹ * s) ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine D.mem_Ahat_of_three (hRN hrs) hk' (D.mono_of_mem hτN hτb hτ hmono (hRN hrs)) ?_
    rw [show (r : G)⁻¹ * s * b₁ * ((r : G)⁻¹ * s)⁻¹ =
      (r : G)⁻¹ * ((s : G) * b₁ * (s : G)⁻¹) * r by group]
    exact line_conj hy hy'
  haveI : Nonempty ↥R := ⟨1⟩
  let rep : Fin 3 → ↥R := Function.invFun f
  have hrep : ∀ r : ↥R, f (rep (f r)) = f r := fun r => Function.invFun_eq ⟨r, rfl⟩
  let φ : ↥R → Fin 3 × ↥(R ⊓ Â) := fun r =>
    (f r, ⟨((rep (f r) : ↥R) : G)⁻¹ * r,
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (rep (f r)).2) r.2, key _ _ (hrep r)⟩⟩)
  have hφ : Function.Injective φ := by
    intro r s e
    have e1 : f r = f s := congrArg Prod.fst e
    have e2 : ((rep (f r) : ↥R) : G)⁻¹ * r = ((rep (f s) : ↥R) : G)⁻¹ * s :=
      congrArg (fun p : Fin 3 × ↥(R ⊓ Â) => ((p.2 : ↥(R ⊓ Â)) : G)) e
    rw [e1] at e2
    exact Subtype.ext (mul_left_cancel e2)
  calc Nat.card ↥R ≤ Nat.card (Fin 3 × ↥(R ⊓ Â)) := Nat.card_le_card_of_injective φ hφ
    _ = 3 * Nat.card ↥(R ⊓ Â) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    _ ≤ 3 * 3 ^ 7 := Nat.mul_le_mul_left 3 hRA
    _ = 3 ^ 8 := by norm_num

end Data

theorem four_le_localRank_of_mono {b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G}
    (D : Data b b₁ b₂ b₃) (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hirr : ∀ H : Subgroup G, H ≤ BO b₁ b₂ b₃ → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        H = BO b₁ b₂ b₃)
    (hmono : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    {L : Subgroup G} (hML : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ L)
    (hself : L ⊓ Subgroup.centralizer ((BO b₁ b₂ b₃ : Subgroup G) : Set G) ≤ BO b₁ b₂ b₃)
    (hbG : b ∈ commutator G) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  obtain ⟨hτN, hτb⟩ := M.mem τ (by simp)
  have hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹ := by
    refine conj_inv_of_closure D.B₁ab ?_
    rintro x (rfl | rfl | rfl)
    exacts [M.inv.1, M.inv.2.1, M.inv.2.2]
  refine four_le_localRank_of_lift D M hirr
    (fun R hRN hR => D.card_le_of_isPGroup hτN hτb hτ hmono R hRN hR) ?_ hbG
  refine D.hbt_of M (fun n hn hnb => hmono n hn (Or.inr hnb)) fun hno => ?_
  obtain ⟨K, hKN, hKC, hK3, hCK⟩ := D.exists_K
  set NL := L ⊓ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ⊓
    Subgroup.centralizer ({b} : Set G) with hNLdef
  have hNLN : NL ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) :=
    fun l hl => hl.1.2
  have hNLb : ∀ l ∈ NL, l * b * l⁻¹ = b := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff.mp hl.2, mul_inv_cancel_right]
  have hNL : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ NL := by
    intro g hg
    obtain ⟨hgN, hgb⟩ := M.mem g (Set.mem_insert_of_mem τ hg)
    exact ⟨⟨hML g hg, hgN⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgb)⟩
  refine ⟨K, NL,
    { KN := hKN
      KC := hKC
      K3 := hK3
      CK := hCK
      NLN := hNLN
      NLb := hNLb
      NLC := fun x hx => hself ⟨hx.1.1.1, Subgroup.centralizer_le D.B₁_le_B hx.2⟩
      gen := fun n hn => D.gen_of_no_inv M hmono hno hNLN hNLb hNL hn }⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.Lift
