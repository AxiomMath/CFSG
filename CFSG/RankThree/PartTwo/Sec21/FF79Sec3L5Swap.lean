module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

section SwapAux

variable {A U₁ U₂ : Subgroup G}

lemma swap_comm (hA : IsElemAb 3 4 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := by
  haveI := hA.1
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

lemma swap_cube (hA : IsElemAb 3 4 A) {x : G} (hx : x ∈ A) : x ^ 3 = 1 := by
  haveI := hA.1
  exact elemPow_eq_one_of_isElementaryAbelian x hx

lemma swap_eq_one_of_sq (hA : IsElemAb 3 4 A) {x : G} (hx : x ∈ A) (h : x * x = 1) :
    x = 1 := by
  have h3 := swap_cube hA hx
  have : x = x ^ 3 * (x * x)⁻¹ := by group
  rw [this, h3, h]; simp

lemma swap_mem_sup (hA : IsElemAb 3 4 A) (hU₁ : U₁ ≤ A) (hU₂ : U₂ ≤ A) {x : G}
    (hx : x ∈ U₁ ⊔ U₂) : ∃ u ∈ U₁, ∃ v ∈ U₂, u * v = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, x, hx, by simp⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := ihx
    obtain ⟨u', hu', v', hv', rfl⟩ := ihy
    refine ⟨u * u', mul_mem hu hu', v * v', mul_mem hv hv', ?_⟩
    have := swap_comm hA (hU₂ hv) (hU₁ hu')
    calc u * u' * (v * v') = u * (u' * v) * v' := by group
      _ = u * (v * u') * v' := by rw [this]
      _ = u * v * (u' * v') := by group
  | inv x _ ih =>
    obtain ⟨u, hu, v, hv, rfl⟩ := ih
    refine ⟨u⁻¹, inv_mem hu, v⁻¹, inv_mem hv, ?_⟩
    have := swap_comm hA (hU₂ hv) (hU₁ hu)
    calc u⁻¹ * v⁻¹ = (v * u)⁻¹ := by group
      _ = (u * v)⁻¹ := by rw [this]

variable {σ : G}

lemma swap_conj_mul (a b : G) : σ * (a * b) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * b * σ⁻¹) := by group

lemma swap_cent (hA : IsElemAb 3 4 A) (hU₁ : U₁ ≤ A) (hU₂ : U₂ ≤ A) (hsup : U₁ ⊔ U₂ = A)
    (hσ₁ : ∀ x ∈ U₁, σ * x * σ⁻¹ = x) (hσ₂ : ∀ x ∈ U₂, σ * x * σ⁻¹ = x⁻¹) {y : G} (hy : y ∈ A)
    (hfix : σ * y * σ⁻¹ = y) : y ∈ U₁ := by
  rw [← hsup] at hy
  obtain ⟨u, hu, v, hv, rfl⟩ := swap_mem_sup hA hU₁ hU₂ hy
  rw [swap_conj_mul, hσ₁ u hu, hσ₂ v hv] at hfix
  have h1 : v⁻¹ = v := mul_left_cancel hfix
  have h2 : v * v = 1 := mul_eq_one_iff_eq_inv.mpr h1.symm
  have := swap_eq_one_of_sq hA (hU₂ hv) h2
  subst this
  simpa using hu

lemma swap_inv (hA : IsElemAb 3 4 A) (hU₁ : U₁ ≤ A) (hU₂ : U₂ ≤ A) (hsup : U₁ ⊔ U₂ = A)
    (hσ₁ : ∀ x ∈ U₁, σ * x * σ⁻¹ = x) (hσ₂ : ∀ x ∈ U₂, σ * x * σ⁻¹ = x⁻¹) {y : G} (hy : y ∈ A)
    (hinv : σ * y * σ⁻¹ = y⁻¹) : y ∈ U₂ := by
  rw [← hsup] at hy
  obtain ⟨u, hu, v, hv, rfl⟩ := swap_mem_sup hA hU₁ hU₂ hy
  rw [swap_conj_mul, hσ₁ u hu, hσ₂ v hv] at hinv
  have hc := swap_comm hA (hU₁ hu) (hU₂ hv)
  have h0 : (u * v)⁻¹ = u⁻¹ * v⁻¹ := by rw [hc, mul_inv_rev]
  rw [h0] at hinv
  have h1 : u = u⁻¹ := mul_right_cancel hinv
  have h2 : u * u = 1 := mul_eq_one_iff_eq_inv.mpr h1
  have := swap_eq_one_of_sq hA (hU₁ hu) h2
  subst this
  simpa using hv

end SwapAux

lemma dih8_comm_mem_center {D' : Subgroup G} (hD8 : Nat.card D' = 8 ∧ ¬ IsMulCommutative D')
    (g h : D') : (g * h)⁻¹ * (h * g) ∈ Subgroup.center D' := by
  have hp : IsPGroup 2 D' := IsPGroup.of_card (n := 3) (by simpa using hD8.1)
  haveI : Nontrivial D' := by
    haveI : Finite D' := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hD8.1]; omega)
  haveI : Nontrivial (Subgroup.center D') := hp.center_nontrivial
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center D')
  rw [hD8.1] at hmul
  have hZ : 1 < Nat.card (Subgroup.center D') := Finite.one_lt_card
  have hQdvd : Nat.card (D' ⧸ Subgroup.center D') ∣ 8 := ⟨_, hmul⟩
  have hQ4 : Nat.card (D' ⧸ Subgroup.center D') = 4 := by
    by_contra hne
    have hle : Nat.card (D' ⧸ Subgroup.center D') ≤ 2 := by
      have : Nat.card (D' ⧸ Subgroup.center D') ≤ 4 := by
        by_contra hgt
        push Not at hgt
        nlinarith
      have h8 := Nat.le_of_dvd (by norm_num) hQdvd
      interval_cases hq : Nat.card (D' ⧸ Subgroup.center D') <;> simp_all <;> omega
    haveI : IsCyclic (D' ⧸ Subgroup.center D') := by
      by_cases h1 : Nat.card (D' ⧸ Subgroup.center D') = 1
      · haveI : Subsingleton (D' ⧸ Subgroup.center D') := Finite.card_le_one_iff_subsingleton.mp
          (by omega)
        infer_instance
      · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact isCyclic_of_prime_card (p := 2) (by
          have : 0 < Nat.card (D' ⧸ Subgroup.center D') := Nat.card_pos
          omega)
    exact hD8.2 (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center D'))
      (by simp))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := D' ⧸ Subgroup.center D')
    (by simpa using hQ4)
  have := IsMulCommutative.is_comm.comm (QuotientGroup.mk g : D' ⧸ Subgroup.center D')
    (QuotientGroup.mk h)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at this
  exact this

theorem sec35_swap {A U₁ U₂ D' : Subgroup G} {σ : G} (hA : IsElemAb 3 4 A) (hU₁ : U₁ ≤ A)
    (hU₂ : U₂ ≤ A) (hsup : U₁ ⊔ U₂ = A) (hinf : U₁ ⊓ U₂ = ⊥) (hc₁ : Nat.card U₁ = 9)
    (hc₂ : Nat.card U₂ = 9) (hD8 : Nat.card D' = 8 ∧ ¬ IsMulCommutative D')
    (hDA : D' ≤ Nor A)
    (hz : ∀ z ∈ Subgroup.center D', z ≠ 1 → ∀ x ∈ A, z * x * z⁻¹ = x⁻¹)
    (hσD : σ ∈ D') (hσ2 : orderOf σ = 2) (hσ₁ : ∀ x ∈ U₁, σ * x * σ⁻¹ = x)
    (hσ₂ : ∀ x ∈ U₂, σ * x * σ⁻¹ = x⁻¹) :
    ∃ d ∈ D', conjBy d U₁ = U₂ ∧ conjBy d U₂ = U₁ := by
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    simp at hσ2
  have hnc : ∃ d ∈ D', d * σ * d⁻¹ ≠ σ := by
    by_contra hall
    push Not at hall
    have hcen : (⟨σ, hσD⟩ : D') ∈ Subgroup.center D' := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have := hall g g.2
      simp only [Subgroup.coe_mul]
      calc (g : G) * σ = g * σ * (g : G)⁻¹ * g := by group
        _ = σ * g := by rw [this]
    have hne : (⟨σ, hσD⟩ : D') ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
    have hinvA := hz _ hcen hne
    have hU1 : U₁ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have h1 := hσ₁ x hx
      have h2 : σ * x * σ⁻¹ = x⁻¹ := hinvA x (hU₁ hx)
      rw [h1] at h2
      exact swap_eq_one_of_sq hA (hU₁ hx) (mul_eq_one_iff_eq_inv.mpr h2)
    rw [hU1] at hc₁
    simp at hc₁
  obtain ⟨d, hd, hdσ⟩ := hnc
  refine ⟨d, hd, ?_⟩
  have hzc := dih8_comm_mem_center hD8 ⟨d, hd⟩⁻¹ ⟨σ, hσD⟩
  set z : D' := ((⟨d, hd⟩⁻¹ * ⟨σ, hσD⟩ : D')⁻¹ * (⟨σ, hσD⟩ * ⟨d, hd⟩⁻¹ : D')) with hzdef
  have hzG : (z : G) = σ⁻¹ * (d * σ * d⁻¹) := by
    simp [hzdef]
    group
  have hzne : z ≠ 1 := by
    intro h1
    have : (z : G) = 1 := by rw [h1]; rfl
    rw [hzG] at this
    apply hdσ
    exact (inv_mul_eq_one.mp this).symm
  have hzA := hz z hzc hzne
  have hdd : d * σ * d⁻¹ = σ * z := by rw [hzG]; group
  have hdA : ∀ x ∈ A, d * x * d⁻¹ ∈ A := by
    intro x hx
    have := hDA hd
    rw [Subgroup.mem_set_normalizer_iff] at this
    exact (this x).mp hx
  have hkey : ∀ x ∈ A, (σ * (d * x * d⁻¹) * σ⁻¹)⁻¹ = d * (σ * x * σ⁻¹) * d⁻¹ := by
    intro x hx
    have hy := hdA x hx
    have h1 : (z : G) * (d * x * d⁻¹) * (z : G)⁻¹ = (d * x * d⁻¹)⁻¹ := hzA _ hy
    calc (σ * (d * x * d⁻¹) * σ⁻¹)⁻¹ = (σ * (z * (d * x * d⁻¹) * (z : G)⁻¹) * σ⁻¹) := by
          rw [h1]; group
      _ = (σ * z) * (d * x * d⁻¹) * (σ * z)⁻¹ := by group
      _ = (d * σ * d⁻¹) * (d * x * d⁻¹) * (d * σ * d⁻¹)⁻¹ := by rw [hdd]
      _ = _ := by group
  have h21 : conjBy d U₂ ≤ U₁ := by
    rintro _ ⟨x, hx, rfl⟩
    show d * x * d⁻¹ ∈ U₁
    have hk := hkey x (hU₂ hx)
    rw [hσ₂ x hx] at hk
    have : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
    rw [this] at hk
    have hk' : σ * (d * x * d⁻¹) * σ⁻¹ = d * x * d⁻¹ := inv_injective hk
    exact swap_cent hA hU₁ hU₂ hsup hσ₁ hσ₂ (hdA x (hU₂ hx)) hk'
  have h12 : conjBy d U₁ ≤ U₂ := by
    rintro _ ⟨x, hx, rfl⟩
    show d * x * d⁻¹ ∈ U₂
    have hk := hkey x (hU₁ hx)
    rw [hσ₁ x hx] at hk
    have hk' : σ * (d * x * d⁻¹) * σ⁻¹ = (d * x * d⁻¹)⁻¹ := inv_eq_iff_eq_inv.mp hk
    exact swap_inv hA hU₁ hU₂ hsup hσ₁ hσ₂ (hdA x (hU₁ hx)) hk'
  have hcard : ∀ U : Subgroup G, Nat.card (conjBy d U) = Nat.card U := fun U =>
    Subgroup.card_map_of_injective (MulAut.conj d).injective
  exact ⟨Subgroup.eq_of_le_of_card_ge h12 (by rw [hcard, hc₁, hc₂]),
    Subgroup.eq_of_le_of_card_ge h21 (by rw [hcard, hc₁, hc₂])⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
