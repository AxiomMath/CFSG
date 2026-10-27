module

public import CFSG.Quasithin.Background.Harris.R1.AbelIndex

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

variable {G : Type} [Group G]

theorem centralizes_of_conj_eq {E : Subgroup G} {t u : G} {n k : ℕ} (hn : Odd n) (ht : t ^ n = 1)
    (hu : u ^ 2 ^ k = 1) (huE : ∀ e ∈ E, u * e * u⁻¹ ∈ E)
    (hconj : ∀ e ∈ E, t * e * t⁻¹ = u * e * u⁻¹) :
    ∀ e ∈ E, t * e * t⁻¹ = e := by
  have hpow : ∀ m : ℕ, ∀ e ∈ E, u ^ m * e * (u ^ m)⁻¹ ∈ E ∧
      t ^ m * e * (t ^ m)⁻¹ = u ^ m * e * (u ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro e he; simp [he]
    | succ m ih =>
      intro e he
      obtain ⟨h1, h2⟩ := ih e he
      have e1 : u ^ (m + 1) * e * (u ^ (m + 1))⁻¹ = u * (u ^ m * e * (u ^ m)⁻¹) * u⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      have e2 : t ^ (m + 1) * e * (t ^ (m + 1))⁻¹ = t * (t ^ m * e * (t ^ m)⁻¹) * t⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      refine ⟨by rw [e1]; exact huE _ h1, ?_⟩
      rw [e2, e1, h2, hconj _ h1]
  have hcentn : ∀ e ∈ E, u ^ n * e * (u ^ n)⁻¹ = e := by
    intro e he
    rw [← (hpow n e he).2, ht]; simp
  have hord : Nat.Coprime n (orderOf u) :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hn)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hu)
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hord
  have hcentu : ∀ e ∈ E, u * e * u⁻¹ = e := by
    intro e he
    have key : ∀ j : ℕ, (u ^ n) ^ j * e * ((u ^ n) ^ j)⁻¹ = e := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have e1 : (u ^ n) ^ (j + 1) * e * ((u ^ n) ^ (j + 1))⁻¹ =
            (u ^ n) ^ j * (u ^ n * e * (u ^ n)⁻¹) * ((u ^ n) ^ j)⁻¹ := by
          rw [pow_succ, mul_inv_rev]; group
        rw [e1, hcentn e he, ih]
    have := key a
    rwa [ha] at this
  intro e he
  rw [hconj e he]
  exact hcentu e he

@[expose] def invs3 : Finset (Equiv.Perm (Fin 3)) :=
  Finset.univ.filter fun x => x * x = 1 ∧ x ≠ 1

theorem invs3_card : invs3.card = 3 := by decide

theorem perm3_cases : ∀ x : Equiv.Perm (Fin 3),
    x = 1 ∨ x ∈ invs3 ∨ ∃ a ∈ invs3, ∃ b ∈ invs3, x = a * b := by decide

theorem mulAut_perm3_pow_seven (α : MulAut (Equiv.Perm (Fin 3))) (h : α ^ 7 = 1) : α = 1 := by
  classical
  have hmem : ∀ (β : MulAut (Equiv.Perm (Fin 3))) (x : Equiv.Perm (Fin 3)), x ∈ invs3 →
      β x ∈ invs3 := by
    intro β x hx
    simp only [invs3, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨by rw [← map_mul, hx.1, map_one], fun h1 => hx.2 ?_⟩
    exact β.injective (by rw [h1, map_one])
  let ρ : MulAut (Equiv.Perm (Fin 3)) → Equiv.Perm ↥invs3 := fun β =>
    { toFun := fun x => ⟨β x.1, hmem β x.1 x.2⟩
      invFun := fun x => ⟨β⁻¹ x.1, hmem β⁻¹ x.1 x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hρ : ∀ (n : ℕ) (x : ↥invs3), (((ρ α) ^ n) x).1 = (α ^ n) x.1 := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, MulAut.mul_apply]
      have := ih ((ρ α) x)
      rw [this]
      rfl
  have h7 : (ρ α) ^ 7 = 1 := by
    ext x
    rw [hρ, h]
    rfl
  have h6 : (ρ α) ^ 6 = 1 := by
    have := pow_card_eq_one (G := Equiv.Perm ↥invs3) (x := ρ α)
    rw [Fintype.card_perm, Fintype.card_coe, invs3_card] at this
    simpa [Nat.factorial] using this
  have h1 : ρ α = 1 := by
    have e : (ρ α) ^ 7 = (ρ α) ^ 6 * ρ α := pow_succ _ _
    rw [h7, h6, one_mul] at e
    exact e.symm
  have hfix : ∀ x ∈ invs3, α x = x := by
    intro x hx
    have := congrArg (fun p : Equiv.Perm ↥invs3 => (p ⟨x, hx⟩).1) h1
    simpa [ρ] using this
  refine MulEquiv.ext fun x => ?_
  rcases perm3_cases x with rfl | hx | ⟨a, ha, b, hb, rfl⟩
  · simp
  · simpa using hfix x hx
  · simp [map_mul, hfix a ha, hfix b hb]

theorem commutator_mem_pCoreOf_of_pow_seven {L : Subgroup G}
    (hs3 : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (h7 : t ^ 7 = 1) {l : G} (hl : l ∈ L) :
    t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  obtain ⟨e⟩ := hs3
  have hN : Subgroup.zpowers t ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.zpowers_le).2 ht
  let g : ↥(Subgroup.zpowers t) := ⟨t, Subgroup.mem_zpowers t⟩
  have hg7 : g ^ 7 = 1 := Subtype.ext (by simpa using h7)
  let α : MulAut (OTwoQuot L) := conjOTwoQuot L (Subgroup.zpowers t) hN g
  have hα7 : α ^ 7 = 1 := by
    show (conjOTwoQuot L (Subgroup.zpowers t) hN g) ^ 7 = 1
    rw [← map_pow, hg7, map_one]
  have hα : α = 1 := by
    have h1 : (MulAut.congr e α) ^ 7 = 1 := by rw [← map_pow, hα7, map_one]
    have := mulAut_perm3_pow_seven _ h1
    exact (MulAut.congr e).injective (by rw [this, map_one])
  exact commutator_mem_of_conjOTwoQuot_eq_one hN hα hl

theorem le_normalizer_sup_aux {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ A ⊔ B, x * y * x⁻¹ ∈ A ⊔ B := by
    intro x hx
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · show x * a * x⁻¹ ∈ A ⊔ B
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hA hx) a).mp ha)
      · show x * b * x⁻¹ ∈ A ⊔ B
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hB hx) b).mp hb)
    intro y hy
    exact hle hy
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun h => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ h
  simpa [mul_assoc] using this

end CFSG.Quasithin.Background.Harris.R1
