module

public import CFSG.RankThree.PartOne.KEXC.D8Scalar

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KEXC

variable {p : ℕ} {K : Type} [Field K]

theorem not_smallVec_of_fixed_odd {w : D8Mod p K} {j : ZMod 4} (hj : j = 1 ∨ j = 3)
    (hfix : d8Act (DihedralGroup.sr j) w = w) : ¬ SmallVec w := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · rcases hj with rfl | rfl
    · rw [d8Act_sr_one] at hfix
      have h3 : w.2⁻¹ = w.1 := congrArg Prod.fst hfix
      exact h2 (inv_eq_one.mp (h3.trans h1))
    · rw [d8Act_sr_three] at hfix
      have h3 : w.2 = w.1 := congrArg Prod.fst hfix
      exact h2 (h3.trans h1)
  · rcases hj with rfl | rfl
    · rw [d8Act_sr_one] at hfix
      have h3 : w.1⁻¹ = w.2 := congrArg Prod.snd hfix
      exact h2 (inv_eq_one.mp (h3.trans h1))
    · rw [d8Act_sr_three] at hfix
      have h3 : w.2 = w.1 := congrArg Prod.fst hfix
      exact h2 (h3.symm.trans h1)

theorem sr_conj_affine (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (φ : MulAut (D8Mod p K)) (θ : ZMod 4 → ZMod 4)
    (hθ : ∀ i, φ * d8Act (DihedralGroup.sr i) * φ⁻¹ = d8Act (DihedralGroup.sr (θ i))) :
    ∃ δ : ZMod 4, (δ = 1 ∨ δ = 3) ∧ ∀ i, θ i = θ 0 + i * δ := by
  have hinj : Function.Injective (d8Act : DihedralGroup 4 →* MulAut (D8Mod p K)) :=
    d8Act_injective hp hp2 hζ
  have hrot : ∀ i : ZMod 4, φ * d8Act (DihedralGroup.r 1) * φ⁻¹ =
      d8Act (DihedralGroup.r (θ (i + 1) - θ i)) := by
    intro i
    have h1 : (DihedralGroup.sr i * DihedralGroup.sr (i + 1) : DihedralGroup 4) =
        DihedralGroup.r 1 := by
      rw [DihedralGroup.sr_mul_sr]
      congr 1
      ring
    have h2 : (DihedralGroup.sr (θ i) * DihedralGroup.sr (θ (i + 1)) : DihedralGroup 4) =
        DihedralGroup.r (θ (i + 1) - θ i) := DihedralGroup.sr_mul_sr _ _
    calc φ * d8Act (DihedralGroup.r 1) * φ⁻¹
        = φ * d8Act (DihedralGroup.sr i * DihedralGroup.sr (i + 1)) * φ⁻¹ := by rw [h1]
      _ = (φ * d8Act (DihedralGroup.sr i) * φ⁻¹) *
            (φ * d8Act (DihedralGroup.sr (i + 1)) * φ⁻¹) := by rw [map_mul]; group
      _ = d8Act (DihedralGroup.sr (θ i) * DihedralGroup.sr (θ (i + 1))) := by
          rw [hθ i, hθ (i + 1), map_mul]
      _ = d8Act (DihedralGroup.r (θ (i + 1) - θ i)) := by rw [h2]
  obtain ⟨δ, hδ⟩ : ∃ δ : ZMod 4, δ = θ 1 - θ 0 := ⟨_, rfl⟩
  have hstep : ∀ i : ZMod 4, θ (i + 1) - θ i = δ := by
    intro i
    have h := (hrot i).symm.trans (hrot 0)
    have h' := hinj h
    have h'' := DihedralGroup.r.inj h'
    rw [zero_add] at h''
    rw [hδ]
    exact h''
  have hodd : δ = 1 ∨ δ = 3 := by
    have h11 : (1 : ZMod 4) + 1 = 2 := by decide
    have hsq : (φ * d8Act (DihedralGroup.r 1) * φ⁻¹) * (φ * d8Act (DihedralGroup.r 1) * φ⁻¹) =
        φ * d8Act (DihedralGroup.r 2) * φ⁻¹ := by
      have : (DihedralGroup.r 1 * DihedralGroup.r 1 : DihedralGroup 4) = DihedralGroup.r 2 := by
        rw [DihedralGroup.r_mul_r, h11]
      rw [← this, map_mul]
      group
    have hr : φ * d8Act (DihedralGroup.r 1) * φ⁻¹ = d8Act (DihedralGroup.r δ) := by
      rw [hrot 0, zero_add, hδ]
    rw [hr, ← map_mul, DihedralGroup.r_mul_r] at hsq
    by_contra hne
    have key : ∀ d : ZMod 4, ¬ (d = 1 ∨ d = 3) → d + d = 0 := by decide
    rw [key δ hne] at hsq
    have h0 : (d8Act (DihedralGroup.r 0) : MulAut (D8Mod p K)) = 1 := by
      rw [← DihedralGroup.one_def, map_one]
    rw [h0] at hsq
    have h1 : (d8Act (DihedralGroup.r 2) : MulAut (D8Mod p K)) = 1 := by
      calc (d8Act (DihedralGroup.r 2) : MulAut (D8Mod p K))
          = φ⁻¹ * (φ * d8Act (DihedralGroup.r 2) * φ⁻¹) * φ := by group
        _ = φ⁻¹ * 1 * φ := by rw [← hsq]
        _ = 1 := by group
    have h3 := hinj (h1.trans (map_one _).symm)
    have h4 := DihedralGroup.r.inj (h3.trans DihedralGroup.one_def)
    revert h4
    decide
  refine ⟨δ, hodd, fun i => ?_⟩
  have h1 : θ 1 = θ 0 + δ := by rw [hδ]; ring
  have h2 : θ 2 = θ 0 + 2 * δ := by
    have := hstep 1
    have h1' : (1 : ZMod 4) + 1 = 2 := by decide
    rw [h1'] at this
    linear_combination this + h1
  have h3 : θ 3 = θ 0 + 3 * δ := by
    have := hstep 2
    have h1' : (2 : ZMod 4) + 1 = 3 := by decide
    rw [h1'] at this
    linear_combination this + h2
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl
  · simp
  · rw [h1]; ring
  · exact h2
  · exact h3

theorem sq_hcls (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (φ : MulAut (D8Mod p K))
    (hnorm : ∀ w : DihedralGroup 4, ∃ w' : DihedralGroup 4, φ * d8Act w * φ⁻¹ = d8Act w') :
    ∀ v : D8Mod p K, BigVec v → ¬ SmallVec ((φ * φ) v) := by
  classical
  choose θ hθ using exists_sr_conj hp hp2 hζ φ hnorm
  obtain ⟨δ, hδ, haff⟩ := sr_conj_affine hp hp2 hζ φ θ hθ
  have hconj : ∀ (j : ZMod 4) (w : D8Mod p K),
      d8Act (DihedralGroup.sr (θ j)) (φ w) = φ (d8Act (DihedralGroup.sr j) w) := by
    intro j w
    have := congrArg (fun m : MulAut (D8Mod p K) => m (φ w)) (hθ j)
    simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using this.symm
  intro v hv hsm
  obtain ⟨i, hi, hvfix⟩ : ∃ i : ZMod 4, (i = 1 ∨ i = 3) ∧
      d8Act (DihedralGroup.sr i) v = v := by
    rcases hv with ⟨-, h2 | h2⟩
    · exact ⟨3, Or.inr rfl, by rw [d8Act_sr_three]; exact Prod.ext h2 h2.symm⟩
    · exact ⟨1, Or.inl rfl, by
        rw [d8Act_sr_one]
        exact Prod.ext (by rw [h2, inv_inv]) h2.symm⟩
  have hfix2 : d8Act (DihedralGroup.sr (θ (θ i))) ((φ * φ) v) = (φ * φ) v := by
    rw [MulAut.mul_apply, hconj, hconj, hvfix]
  have hθθ : θ (θ i) = 1 ∨ θ (θ i) = 3 := by
    have key : ∀ t0 d j : ZMod 4, (d = 1 ∨ d = 3) → (j = 1 ∨ j = 3) →
        (t0 + (t0 + j * d) * d = 1 ∨ t0 + (t0 + j * d) * d = 3) := by decide
    rw [haff (θ i), haff i]
    exact key (θ 0) δ i hδ hi
  exact not_smallVec_of_fixed_odd hθθ hfix2 hsm

theorem exists_d8Act_mul_pow_sq (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ : MulAut (D8Mod p K))
    (hnorm : ∀ w : DihedralGroup 4, ∃ w' : DihedralGroup 4, φ * d8Act w * φ⁻¹ = d8Act w') :
    ∃ (γ : DihedralGroup 4) (k : ℤ), ∀ v, (φ * φ) v = d8Act γ (v ^ k) := by
  refine exists_d8Act_mul_pow hp hp2 hζ (φ * φ) (fun w => ?_) (sq_hcls hp hp2 hζ φ hnorm)
  obtain ⟨w1, hw1⟩ := hnorm w
  obtain ⟨w2, hw2⟩ := hnorm w1
  refine ⟨w2, ?_⟩
  calc φ * φ * d8Act w * (φ * φ)⁻¹ = φ * (φ * d8Act w * φ⁻¹) * φ⁻¹ := by group
    _ = d8Act w2 := by rw [hw1, hw2]

end CFSG.RankThree.PartOne.SP4C
