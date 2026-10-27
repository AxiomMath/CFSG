module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Torus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOne
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits Subgroup

theorem uc22pwsu3_odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := Nat.one_le_two_pow (n := k)
  exact ⟨2 ^ k - 1, by rw [pow_succ]; omega⟩

theorem uc22pwsu3_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact ⟨2 ^ k, by rw [pow_succ]; ring⟩

theorem uc22pwsu3_coprime_two_pow {n : ℕ} (hn : 1 ≤ n) : Nat.Coprime (2 ^ n - 1) (2 ^ n + 1) := by
  have h1 : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h1, Nat.coprime_self_add_right]
  exact (uc22pwsu3_odd_two_pow_sub_one hn).coprime_two_right

theorem uc22pwsu3_sq_sub_one {n : ℕ} (hn : 1 ≤ n) : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  rw [hm, Nat.add_sub_cancel]
  ring_nf
  omega

section Frob

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem uc22pwsu3_frob_core {K : Type} [Field K] [Finite K] [CharP K 2] (ϑ : K ≃+ K)
    (h : ∀ c : Kˣ, ∃ d : K, ∀ x : K, ϑ ((c : K) * x) = d * ϑ x) :
    ∃ i : ℕ, ∀ c d : K, (∀ x : K, ϑ (c * x) = d * ϑ x) → d = c ^ 2 ^ i := by
  obtain ⟨a, σ', hσ'⟩ := uc22pwr1_semilinear ϑ h
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow σ'
  refine ⟨i, fun c d hd => ?_⟩
  have h1 := hd 1
  rw [mul_one] at h1
  have h2 : (a : K) * σ' c = d * ((a : K) * σ' 1) := by rw [← hσ', ← hσ']; exact h1
  rw [map_one, mul_one] at h2
  have h3 : σ' c = d := mul_left_cancel₀ a.ne_zero (by rw [h2, mul_comm])
  rw [← h3, hi]

include hσ in
theorem uc22pwsu3_sigma_eq_of_pow {n : ℕ} (hσn : ∀ c : F, σ c = c ^ 2 ^ n) {x : F}
    (hx : x ^ (2 ^ n - 1) = 1) : σ x = x := by
  have h1 : x ^ 2 ^ n = x ^ (2 ^ n - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  rw [hσn, h1, hx, one_mul]

theorem uc22pwsu3_entry_pow_eq_one {h : SU σ 3} (hh : h ∈ uc22pwsu3H σ) {t : F}
    (hmat : mat σ 3 h 0 0 = t) {m : ℕ} (hpow : h ^ m = 1) : t ^ m = 1 := by
  have h1 := uc22pwsu3_mat_pow_entry hh m
  rw [hpow, hmat] at h1
  simpa using h1.symm

end Frob

section Shape

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem uc22pwsu3_frob (n : ℕ) (hσn : ∀ c : F, σ c = c ^ 2 ^ n)
    (hnorm : ∀ x : F, σ x = x → ∃ a, σ a * a = x)
    (htop : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ 3) (0 : Fin (3 / 2)) = ⊤)
    (hHcard : Nat.card (uc22pwsu3H σ) = Nat.card Fˣ) (ψ : MulAut (SU σ 3))
    (hψ : ∀ x, x ∈ uc22pwsu3X hσ ↔ ψ x ∈ uc22pwsu3X hσ) :
    ∃ i : ℕ, ∀ h ∈ uc22pwsu3H σ, h ^ (2 ^ n - 1) = 1 →
      ∃ u ∈ uc22pwsu3X hσ, ψ h = u * h ^ 2 ^ i := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : traceZero σ, (ζ : F) ≠ 0 :=
    ⟨⟨1, by rw [mem_traceZero, map_one]; exact CharTwo.add_self_eq_zero 1⟩, one_ne_zero⟩
  let K₀ : Subfield F := σ.toRingHom.eqLocusField (RingHom.id F)
  haveI : CharP K₀ 2 := inferInstance
  have hfix : ∀ β : K₀, σ (β : F) = β := fun β => β.2
  let yE : K₀ → SU σ 3 := fun β => uc22pwsu3Y (β : F) (hfix β)
  have hyE_add : ∀ β β', yE (β + β') = yE β * yE β' := fun β β' =>
    (uc22pwsu3Y_mul _ _ _ _ _).symm
  have hyE_inj : Function.Injective yE := fun β β' h => Subtype.ext (uc22pwsu3Y_inj h)
  have hyE0 : yE 0 = 1 := uc22pwsu3Y_one
  have hψY : ∀ β : K₀, ∃ γ : K₀, ψ (yE β) = yE γ := by
    intro β
    have hX : ψ (yE β) ∈ uc22pwsu3X hσ := (hψ _).1 (uc22pwsu3Y_mem hσ _ _)
    have hsq : ψ (yE β) * ψ (yE β) = 1 := by
      rw [← map_mul, ← hyE_add, CharTwo.add_self_eq_zero, hyE0, map_one]
    obtain ⟨γ, hγ, hy⟩ := uc22pwsu3_exists_Y_of_sq hσ hX hsq
    exact ⟨⟨γ, hγ⟩, hy⟩
  choose ϑ hϑ using hψY
  have hϑadd : ∀ β β', ϑ (β + β') = ϑ β + ϑ β' := by
    intro β β'
    apply hyE_inj
    rw [← hϑ, hyE_add, map_mul, hϑ, hϑ, ← hyE_add]
  have hϑ0 : ϑ 0 = 0 := by
    apply hyE_inj
    rw [← hϑ, hyE0, map_one]
  have hϑinj : Function.Injective ϑ := by
    intro β β' h
    apply hyE_inj
    apply ψ.injective
    rw [hϑ, hϑ, h]
  let ϑh : K₀ →+ K₀ := { toFun := ϑ, map_zero' := hϑ0, map_add' := hϑadd }
  let ϑe : K₀ ≃+ K₀ := AddEquiv.ofBijective ϑh ⟨hϑinj, Finite.injective_iff_surjective.1 hϑinj⟩
  have hexist := uc22pwsu3H_exists_entry hHcard
  have hdiag : ∀ t : Fˣ, ∀ i : Fin 3, (![(t : F), σ t / t, (σ t)⁻¹] : Fin 3 → F) i ≠ 0 := by
    intro t i
    fin_cases i <;> simp
  have hnormfix : ∀ a : F, σ (σ a * a) = σ a * a := fun a => by rw [map_mul, hσ, mul_comm]
  let nm : F → K₀ := fun a => ⟨σ a * a, show σ (σ a * a) = σ a * a from hnormfix a⟩
  have hact : ∀ (h : SU σ 3) (t : Fˣ), h ∈ uc22pwsu3H σ →
      mat σ 3 h = diagonal ![(t : F), σ t / t, (σ t)⁻¹] →
      ∃ (h' u : SU σ 3) (ν : Fˣ), h' ∈ uc22pwsu3H σ ∧ u ∈ uc22pwsu3X hσ ∧
        mat σ 3 h' = diagonal ![(ν : F), σ ν / ν, (σ ν)⁻¹] ∧ ψ h = h' * u ∧
        ∀ β : K₀, ϑ (nm t * β) = nm ν * ϑ β := by
    intro h t hh hmat
    have hN := uc22pwr1_mem_normalizer_aut ψ hψ (uc22pwsu3_levelTorus_le_normalizer hσ hh)
    obtain ⟨h', hh', u, hu, hψh⟩ := uc22pwsu3_normalizer_decomp hσ hnorm htop hζ hN
    obtain ⟨ν, hν⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh'
    refine ⟨h', u, ν, hh', hu, hν, hψh, fun β => ?_⟩
    apply hyE_inj
    have e1 : h * yE β * h⁻¹ = yE (nm t * β) :=
      uc22pwsu3Y_conj (hdiag t) hmat _ (hfix β) _ (hfix _) (by rw [uc22pwsu3_diag_ratio]; rfl)
    have e2 : h' * yE (ϑ β) * h'⁻¹ = yE (nm ν * ϑ β) :=
      uc22pwsu3Y_conj (hdiag ν) hν _ (hfix _) _ (hfix _) (by rw [uc22pwsu3_diag_ratio]; rfl)
    have hc : u * yE (ϑ β) = yE (ϑ β) * u := uc22pwsu3Y_comm hσ hu _ _
    rw [← hϑ, ← e1, map_mul, map_mul, map_inv, hϑ, hψh, ← e2]
    calc h' * u * yE (ϑ β) * (h' * u)⁻¹ = h' * (u * yE (ϑ β) * u⁻¹) * h'⁻¹ := by group
      _ = h' * yE (ϑ β) * h'⁻¹ := by rw [hc]; group
  have hsemi : ∀ c : K₀ˣ, ∃ d : K₀, ∀ x : K₀, ϑe ((c : K₀) * x) = d * ϑe x := by
    intro c
    obtain ⟨t, ht⟩ := hnorm (c : F) (hfix c)
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact c.ne_zero (Subtype.ext (by rw [← ht]; simp))
    obtain ⟨h, hh, hmat⟩ := hexist (Units.mk0 t ht0)
    obtain ⟨-, -, ν, -, -, -, -, hrel⟩ := hact h (Units.mk0 t ht0) hh hmat
    refine ⟨nm ν, fun x => ?_⟩
    have hc : (c : K₀) = nm (Units.mk0 t ht0 : Fˣ) := Subtype.ext (by simp [nm, ht])
    change ϑ ((c : K₀) * x) = _ * ϑ x
    rw [hc]
    exact hrel x
  obtain ⟨i, hi⟩ := uc22pwsu3_frob_core ϑe hsemi
  refine ⟨i, fun h hh hpow => ?_⟩
  obtain ⟨t, hmat⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh
  have hσt : σ (t : F) = t := by
    refine uc22pwsu3_sigma_eq_of_pow hσ hσn (uc22pwsu3_entry_pow_eq_one hh ?_ hpow)
    simp [hmat]
  obtain ⟨h', u, ν, hh', hu, hν, hψh, hrel⟩ := hact h t hh hmat
  have hν1 : (ν : F) ^ (2 ^ n - 1) = 1 := by
    obtain ⟨a, b, -, hum⟩ := (mem_rootGroup_three hσ).1 hu
    have h10 : mat σ 3 (h' * u) 1 0 = 0 := by
      rw [map_mul, hν, hum]; simp [Matrix.mul_apply, Fin.sum_univ_three]
    have h20 : mat σ 3 (h' * u) 2 0 = 0 := by
      rw [map_mul, hν, hum]; simp [Matrix.mul_apply, Fin.sum_univ_three]
    have h00 : mat σ 3 (h' * u) 0 0 = ν := by
      rw [map_mul, hν, hum]; simp [Matrix.mul_apply, Fin.sum_univ_three]
    have hcol := (uc22pwsu3_pow_firstCol h10 h20 (2 ^ n - 1)).2.2
    have hone : (h' * u) ^ (2 ^ n - 1) = 1 := by rw [← hψh, ← map_pow, hpow, map_one]
    rw [hone, map_one, h00] at hcol
    simpa using hcol.symm
  have hσν : σ (ν : F) = ν := uc22pwsu3_sigma_eq_of_pow hσ hσn hν1
  have hnu : (ν : F) = (t : F) ^ 2 ^ i := by
    have h1 := congrArg (fun z : K₀ => (z : F)) (hi (nm t) (nm ν) (fun x => hrel x))
    simp only [nm, hσt, hσν, SubmonoidClass.coe_pow] at h1
    rw [mul_pow] at h1
    rcases mul_self_eq_mul_self_iff.1 h1 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  have hh'eq : h' = h ^ 2 ^ i := by
    have e1 : uc22pwsu3HEntry σ ⟨h', hh'⟩ = ν := by simp [uc22pwsu3HEntry, hν]
    have e2 : uc22pwsu3HEntry σ ⟨h ^ 2 ^ i, pow_mem hh _⟩ = (t : F) ^ 2 ^ i := by
      simp [uc22pwsu3HEntry, uc22pwsu3_mat_pow_entry hh, hmat]
    exact congrArg Subtype.val (uc22pwsu3HEntry_injective (e1.trans (hnu.trans e2.symm)))
  refine ⟨h ^ 2 ^ i * u * (h ^ 2 ^ i)⁻¹, ?_, ?_⟩
  · exact (mem_normalizer_iff.1 (uc22pwsu3_levelTorus_le_normalizer hσ (pow_mem hh _)) u).1 hu
  · rw [hψh, hh'eq, inv_mul_cancel_right]

end Shape

section Datum

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem uc22pwsu3_hnorm (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∀ x : F, unitaryInvolution F 2 n x = x → ∃ a, unitaryInvolution F 2 n a * a = x := by
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hx hx0

theorem uc22pwsu3X_isPGroup (hF : Nat.card F = (2 ^ n) ^ 2) :
    IsPGroup 2 (uc22pwsu3X (unitaryInvolution_involutive hF)) :=
  IsPGroup.of_card (n := 3 * n) (by rw [card_rootGroup_three hF, ← pow_mul, mul_comm])

theorem uc22pwsu3X_index (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    ¬ 2 ∣ (uc22pwsu3X (unitaryInvolution_involutive hF)).index := by
  have h1 := Subgroup.card_mul_index (uc22pwsu3X (unitaryInvolution_involutive hF))
  rw [card_rootGroup_three hF, card_SU_three hF] at h1
  have hpos : 0 < (2 ^ n) ^ 3 := by positivity
  have h2 : (uc22pwsu3X (unitaryInvolution_involutive hF)).index =
      ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) :=
    Nat.eq_of_mul_eq_mul_left hpos (h1.trans (by ring))
  rw [h2, uc22pwsu3_sq_sub_one hn]
  have heven : Even ((2 ^ n) ^ 3) :=
    Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
  have hodd : Odd ((2 ^ n - 1) * (2 ^ n + 1) * ((2 ^ n) ^ 3 + 1)) :=
    ((uc22pwsu3_odd_two_pow_sub_one hn).mul (uc22pwsu3_odd_two_pow_add_one hn)).mul heven.add_one
  intro hd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd)

theorem uc22pwr1_datum_su3 (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    UC22pwR1Datum (SU (unitaryInvolution F 2 n) 3)
      (uc22pwsu3X (unitaryInvolution_involutive hF)) n := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hnorm := uc22pwsu3_hnorm hF
  have htop := rankOne_three_eq_top hF
  have hcard : Nat.card (uc22pwsu3H (unitaryInvolution F 2 n)) = (2 ^ n) ^ 2 - 1 :=
    card_levelTorus_three hF
  have hHcard : Nat.card (uc22pwsu3H (unitaryInvolution F 2 n)) = Nat.card Fˣ := by
    rw [hcard, CFSG.ClassicalGroups.Unitary.card_units_of_card hF]
  have hσn : ∀ c : F, unitaryInvolution F 2 n c = c ^ 2 ^ n := unitaryInvolution_apply F 2 n
  refine ⟨uc22pwsu3H _, uc22pwsu3W hσ ζ, uc22pwsu3H_cyclic, ?_,
    uc22pwsu3_levelTorus_le_normalizer hσ, ?_, uc22pwsu3_levelWeyl_sq hσ hζ, ?_,
    uc22pwsu3_normalizer_sup_eq_top hσ hnorm htop hζ, ?_⟩
  · rw [hcard, uc22pwsu3_sq_sub_one hn]
    exact (uc22pwsu3_odd_two_pow_sub_one hn).mul (uc22pwsu3_odd_two_pow_add_one hn)
  · intro p _ hpd
    rw [hcard, uc22pwsu3_sq_sub_one hn]
    exact hpd.mul_right _
  · intro t ht htpow
    obtain ⟨τ, hτ⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three ht
    have h1 : (τ : F) ^ (2 ^ n - 1) = 1 :=
      uc22pwsu3_entry_pow_eq_one ht (by simp [hτ]) htpow
    exact uc22pwsu3_levelWeyl_conj hσ hζ τ.ne_zero hτ (uc22pwsu3_sigma_eq_of_pow hσ hσn h1)
  · intro ψ hψ
    exact uc22pwsu3_frob hσ n hσn hnorm htop hHcard ψ hψ

end Datum

end CFSG.LocalAnalysis.UniquenessCase.UC22
