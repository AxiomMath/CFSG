module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G11

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

abbrev A4 : Type := ↥(alternatingGroup (Fin 4))

theorem a4_pow_six : ∀ x : A4, x ^ 6 = 1 := by decide +kernel

theorem a4_inv : ∀ a a' : A4, a ^ 3 = 1 → a ≠ 1 → (a' * a * a'⁻¹ * a) ^ 2 ≠ 1 := by
  decide +kernel

theorem card_A4 : Nat.card A4 = 12 := by rw [Nat.card_eq_fintype_card]; decide

theorem a4_sq_of_two {x : A4} {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ^ 2 = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have h6 : 2 ^ i ∣ 6 := hi ▸ orderOf_dvd_of_pow_eq_one (a4_pow_six x)
  have hi1 : i ≤ 1 := by
    by_contra h
    have : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega)).trans h6
    norm_num at this
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hi]
  exact Nat.pow_dvd_pow 2 hi1 |>.trans (by norm_num)

theorem false_of_A4xL32 {K Q : Type*} [Group K] [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Nat.card Q = 168) (eA : K ≃* (A4 × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (θ : Q →* K) (hθ : Function.Injective θ) {y r : K} (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1)
    (hyc : ∀ q, y * θ q = θ q * y) (hz : ∃ k : ℕ, (r * y * r⁻¹ * y) ^ 2 ^ k = 1) : False := by
  set φ := (MonoidHom.fst _ _).comp (eA.toMonoidHom.comp θ) with hφ
  set ψ := (MonoidHom.snd _ _).comp (eA.toMonoidHom.comp θ) with hψ
  have hφ1 : ∀ q, φ q = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff _).mp h
      have := Nat.card_le_card_of_injective φ hinj
      rw [hQ, card_A4] at this
      omega
    · intro q
      exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top q)
  have hψinj : Function.Injective ψ := by
    intro q₁ q₂ h
    apply hθ
    apply eA.injective
    exact Prod.ext ((hφ1 q₁).trans (hφ1 q₂).symm) h
  have hψsurj : Function.Surjective ψ := by
    have h1 := Nat.card_le_card_of_injective ψ hψinj
    have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
      rw [Matrix.card_SL_field]
      simp [Fin.prod_univ_three, ZMod.card]
    exact (hψinj.bijective_of_nat_card_le (by rw [hQ, h2])).2
  have hb : (eA y).2 = 1 := by
    have hcen : (eA y).2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro b'
      obtain ⟨q, rfl⟩ := hψsurj b'
      have h1 := congrArg (fun k => (eA k).2) (hyc q)
      simp only [map_mul, Prod.snd_mul] at h1
      exact h1.symm
    rw [center_SL_eq_bot 3, Subgroup.mem_bot] at hcen
    exact hcen
  have ha1 : (eA y).1 ≠ 1 := fun h => hy1 (eA.injective (Prod.ext
    (by rw [h, map_one, Prod.fst_one]) (by rw [hb, map_one, Prod.snd_one])))
  have ha3 : (eA y).1 ^ 3 = 1 := by
    have := congrArg (fun k => (eA k).1) hy3
    simpa using this
  obtain ⟨k, hk⟩ := hz
  have hk' : ((eA r).1 * (eA y).1 * (eA r).1⁻¹ * (eA y).1) ^ 2 ^ k = 1 := by
    have := congrArg (fun x => (eA x).1) hk
    simpa using this
  exact a4_inv _ (eA r).1 ha3 ha1 (a4_sq_of_two hk')

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
