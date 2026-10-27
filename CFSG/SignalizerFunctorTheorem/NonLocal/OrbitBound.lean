module

public import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianLift
public import CFSG.SignalizerFunctorTheorem.NonLocal.ModuleOfV

public section

open Module
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem pow_le_card_of_normalizing {X Γ : Type*} [Group X] [Group Γ] (φ : Γ →* X)
    (V : Subgroup X) [Finite V] [IsMulCommutative V] {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hexp : ∀ v ∈ V, v ^ s = 1)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V)
    (E : Subgroup Γ) [Finite E] (hE : IsMulCommutative E) (hEexp : ∀ g ∈ E, g ^ r = 1)
    (n : Γ) (hnE : ∀ e ∈ E, n * e * n⁻¹ ∈ E) (hn : ∀ e ∈ E, n ^ r * e = e * n ^ r)
    (hnt : ∃ e ∈ E, n * e * n⁻¹ ≠ e)
    (hfaith : ∀ g ∈ E, (∀ v ∈ V, φ g * v * (φ g)⁻¹ = v) → g = 1) :
    s ^ r ≤ Nat.card V := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  have : Fact r.Prime := ⟨hr⟩
  let F := AlgebraicClosure (ZMod s)
  obtain ⟨m, ρ, hcard, hρ1⟩ := exists_rep_of_elementary_abelian φ V hs hexp hnorm F
  have hpow : ∀ i : ℕ, ∀ e ∈ E, n ^ i * e * (n ^ i)⁻¹ ∈ E := by
    intro i
    induction i with
    | zero => intro e he; simpa using he
    | succ i ih =>
      intro e he
      have h1 := hnE _ (ih e he)
      have : n ^ (i + 1) * e * (n ^ (i + 1))⁻¹ = n * (n ^ i * e * (n ^ i)⁻¹) * n⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [this]
      exact h1
  have hpowr : ∀ t : ℕ, ∀ e ∈ E, n ^ (r * t) * e * (n ^ (r * t))⁻¹ = e := by
    intro t e he
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 : n ^ (r * (t + 1)) = n ^ r * n ^ (r * t) := by rw [mul_add, mul_one, pow_add]; group
      have h2 : n ^ (r * t) * e * (n ^ (r * t))⁻¹ = e := ih
      have h3 : n ^ r * e = e * n ^ r := hn e he
      calc n ^ (r * (t + 1)) * e * (n ^ (r * (t + 1)))⁻¹
          = n ^ r * (n ^ (r * t) * e * (n ^ (r * t))⁻¹) * (n ^ r)⁻¹ := by
            rw [h1, mul_inv_rev]; group
        _ = n ^ r * e * (n ^ r)⁻¹ := by rw [h2]
        _ = e := by rw [h3]; group
  have hErp : IsPGroup r E := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ r := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
    rcases (Nat.dvd_prime hr).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hinv : (Nat.card E : F) ≠ 0 := by
    obtain ⟨k, hk⟩ := hErp.exists_card_eq
    rw [hk, Ne, CharP.cast_eq_zero_iff F s]
    intro h
    exact hrs ((Nat.prime_dvd_prime_iff_eq hs hr).mp (hs.dvd_of_dvd_pow h)).symm
  by_contra hcon
  have hmr : m < r := by
    by_contra h
    exact hcon (by rw [hcard]; exact Nat.pow_le_pow_right hs.pos (not_lt.mp h))
  have hinvariant : ∀ χ : E → F, IsWeight ρ E χ →
      ∀ e : E, χ ⟨n * e * n⁻¹, hnE e e.2⟩ = χ e := by
    intro χ hχ
    obtain ⟨w, hw0, hw⟩ := hχ
    let χi : ℕ → E → F := fun i a => χ ⟨n ^ i * a * (n ^ i)⁻¹, hpow i a a.2⟩
    have hev : ∀ (i : Fin r) (a : E),
        ρ a (ρ ((n ^ (i : ℕ))⁻¹) w) = χi i a • ρ ((n ^ (i : ℕ))⁻¹) w := by
      intro i a
      have h1 : ρ (a : Γ) * ρ ((n ^ (i : ℕ))⁻¹) =
          ρ ((n ^ (i : ℕ))⁻¹) * ρ (n ^ (i : ℕ) * a * (n ^ (i : ℕ))⁻¹) := by
        rw [← map_mul, ← map_mul]
        congr 1
        group
      have h2 : ρ (n ^ (i : ℕ) * a * (n ^ (i : ℕ))⁻¹) w = χi i a • w :=
        hw ⟨n ^ (i : ℕ) * a * (n ^ (i : ℕ))⁻¹, hpow i a a.2⟩
      have h3 : ρ (a : Γ) (ρ ((n ^ (i : ℕ))⁻¹) w) =
          ρ ((n ^ (i : ℕ))⁻¹) (ρ (n ^ (i : ℕ) * a * (n ^ (i : ℕ))⁻¹) w) := by
        rw [← Module.End.mul_apply, h1, Module.End.mul_apply]
      rw [h3, h2, map_smul]
    have hw0' : ∀ i : Fin r, ρ ((n ^ (i : ℕ))⁻¹) w ≠ 0 := by
      intro i h
      apply hw0
      have h1 : ρ (n ^ (i : ℕ)) (ρ ((n ^ (i : ℕ))⁻¹) w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← h1, h, map_zero]
    by_cases hinj : Function.Injective (fun i : Fin r => χi i)
    · exfalso
      have hli := linearIndependent_of_distinct_weights ρ E hE
        (fun i : Fin r => ρ ((n ^ (i : ℕ))⁻¹) w) (fun i => χi i) hw0' hev hinj
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, Module.finrank_fin_fun] at this
      omega
    ·
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hχeq, hne⟩ := hinj
      have hij' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
      have key : ∀ i j : ℕ, i < j → j < r → χi i = χi j → ∀ e : E,
          χ ⟨n * e * n⁻¹, hnE e e.2⟩ = χ e := by
        intro i j hlt hjr hχχ e
        let k := j - i
        have hk0 : 0 < k := by omega
        have hkr : k < r := by omega
        have h1 : ∀ b : E, χ ⟨n ^ k * b * (n ^ k)⁻¹, hpow k b b.2⟩ = χ b := by
          intro b
          have hb' : n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹ ∈ E := hpow _ _ b.2
          have h2 := congrFun hχχ ⟨n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹, hb'⟩
          simp only [χi] at h2
          have e1 : n ^ i * (n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹) * (n ^ i)⁻¹ = b := by
            have h3 : n ^ r * (b : Γ) * (n ^ r)⁻¹ = b := by
              have := hpowr 1 b b.2
              simpa using this
            calc n ^ i * (n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹) * (n ^ i)⁻¹
                = n ^ (i + (r - i)) * (b : Γ) * (n ^ (i + (r - i)))⁻¹ := by
                  rw [pow_add, mul_inv_rev]; group
              _ = b := by rw [Nat.add_sub_cancel' (by omega)]; exact h3
          have e2 : n ^ j * (n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹) * (n ^ j)⁻¹ =
              n ^ k * b * (n ^ k)⁻¹ := by
            have h3 : n ^ r * (b : Γ) * (n ^ r)⁻¹ = b := by
              have := hpowr 1 b b.2
              simpa using this
            have hjk : j + (r - i) = k + r := by omega
            calc n ^ j * (n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹) * (n ^ j)⁻¹
                = n ^ (j + (r - i)) * (b : Γ) * (n ^ (j + (r - i)))⁻¹ := by
                  rw [pow_add, mul_inv_rev]; group
              _ = n ^ (k + r) * (b : Γ) * (n ^ (k + r))⁻¹ := by rw [hjk]
              _ = n ^ k * (n ^ r * (b : Γ) * (n ^ r)⁻¹) * (n ^ k)⁻¹ := by
                  rw [pow_add, mul_inv_rev]; group
              _ = n ^ k * b * (n ^ k)⁻¹ := by rw [h3]
          have h4 : χ b = χ ⟨n ^ k * b * (n ^ k)⁻¹, hpow k b b.2⟩ := by
            have h5 : (⟨n ^ i * (n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹) * (n ^ i)⁻¹,
                hpow i _ hb'⟩ : E) = b := Subtype.ext e1
            have h6 : (⟨n ^ j * (n ^ (r - i) * (b : Γ) * (n ^ (r - i))⁻¹) * (n ^ j)⁻¹,
                hpow j _ hb'⟩ : E) = ⟨n ^ k * b * (n ^ k)⁻¹, hpow k b b.2⟩ := Subtype.ext e2
            rw [← h5, h2, h6, h5]
          exact h4.symm
        obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime
          ((Nat.Prime.coprime_iff_not_dvd hr).mpr (Nat.not_dvd_of_pos_of_lt hk0 hkr)).symm
          hr.one_lt
        have h2 : ∀ t : ℕ, ∀ b : E, χ ⟨n ^ (k * t) * b * (n ^ (k * t))⁻¹, hpow _ b b.2⟩ = χ b := by
          intro t
          induction t with
          | zero => intro b; simp
          | succ t ih =>
            intro b
            have hb' : n ^ (k * t) * (b : Γ) * (n ^ (k * t))⁻¹ ∈ E := hpow _ _ b.2
            have h3 := h1 ⟨n ^ (k * t) * (b : Γ) * (n ^ (k * t))⁻¹, hb'⟩
            have e3 : n ^ k * (n ^ (k * t) * (b : Γ) * (n ^ (k * t))⁻¹) * (n ^ k)⁻¹ =
                n ^ (k * (t + 1)) * b * (n ^ (k * (t + 1)))⁻¹ := by
              rw [mul_add, mul_one, pow_add, mul_inv_rev]; group
            have h4 : (⟨n ^ k * (n ^ (k * t) * (b : Γ) * (n ^ (k * t))⁻¹) * (n ^ k)⁻¹,
                hpow k _ hb'⟩ : E) =
                ⟨n ^ (k * (t + 1)) * b * (n ^ (k * (t + 1)))⁻¹, hpow _ b b.2⟩ := Subtype.ext e3
            rw [← h4, h3, ih b]
        have hak : n ^ (k * a) * (e : Γ) * (n ^ (k * a))⁻¹ = n * e * n⁻¹ := by
          have hka : k * a = 1 + r * (k * a / r) := by
            have := Nat.div_add_mod (k * a) r
            have hmod : k * a % r = 1 := ha
            omega
          rw [hka, pow_add, mul_inv_rev]
          have h3 := hpowr (k * a / r) e e.2
          set q := k * a / r with hq
          calc n ^ 1 * n ^ (r * q) * (e : Γ) * ((n ^ (r * q))⁻¹ * (n ^ 1)⁻¹)
              = n ^ 1 * (n ^ (r * q) * (e : Γ) * (n ^ (r * q))⁻¹) * (n ^ 1)⁻¹ := by group
            _ = n * e * n⁻¹ := by rw [h3]; group
        have := h2 a e
        have h5 : (⟨n ^ (k * a) * (e : Γ) * (n ^ (k * a))⁻¹, hpow _ e e.2⟩ : E) =
            ⟨n * e * n⁻¹, hnE e e.2⟩ := Subtype.ext hak
        rw [h5] at this
        exact this
      rcases lt_or_gt_of_ne hij' with hlt | hgt
      · exact key i j hlt j.2 hχeq
      · exact key j i hgt i.2 hχeq.symm
  obtain ⟨e₀, he₀, hne₀⟩ := hnt
  apply hne₀
  have hg : n * e₀ * n⁻¹ * e₀⁻¹ ∈ E := E.mul_mem (hnE e₀ he₀) (E.inv_mem he₀)
  have hρg : ρ (n * e₀ * n⁻¹ * e₀⁻¹) = (1 : F) • (1 : Module.End F (Fin m → F)) := by
    refine eq_smul_one_of_weights ρ E hE hinv _ 1 (fun χ hχ w hw => ?_)
    have hχ' := hinvariant χ hχ ⟨e₀, he₀⟩
    have h1 : ρ (n * e₀ * n⁻¹) w = χ ⟨n * e₀ * n⁻¹, hnE e₀ he₀⟩ • w :=
      hw ⟨n * e₀ * n⁻¹, hnE e₀ he₀⟩
    have h2 : ρ e₀⁻¹ w = χ ⟨e₀⁻¹, E.inv_mem he₀⟩ • w := hw ⟨e₀⁻¹, E.inv_mem he₀⟩
    have h3 : χ ⟨e₀⁻¹, E.inv_mem he₀⟩ = (χ ⟨e₀, he₀⟩)⁻¹ := hχ.inv ⟨e₀, he₀⟩
    have h4 : ρ (n * e₀ * n⁻¹ * e₀⁻¹) w = ρ (n * e₀ * n⁻¹) (ρ e₀⁻¹ w) := by
      rw [map_mul, Module.End.mul_apply]
    rw [h4, h2, map_smul, h1, smul_smul, h3, hχ']
    simp [inv_mul_cancel₀ (hχ.ne_zero ⟨e₀, he₀⟩)]
  have hρg1 : ρ (n * e₀ * n⁻¹ * e₀⁻¹) = 1 := by rw [hρg, one_smul]
  have := hfaith _ hg (hρ1 _ hρg1)
  exact mul_inv_eq_one.mp this

end CFSG.SignalizerFunctorTheorem.NonLocal
