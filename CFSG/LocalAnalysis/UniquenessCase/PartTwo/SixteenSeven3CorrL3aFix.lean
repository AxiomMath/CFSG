module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aOrb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private theorem s16c167_mulAut_pow_apply {W : Type*} [Monoid W] (g : MulAut W) {u : W}
    (hu : g u = u) : ∀ n : ℕ, (g ^ n) u = u := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, hu]
      exact ih

theorem s16c167_central_fixed_point_free {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) {ℓ : ↥L} (hℓ : ℓ ∈ Subgroup.center ↥L) (hℓ1 : ℓ ≠ 1) {x : W}
    (hx : (ℓ : MulAut W) x = x) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥L
  let z : MulAut W := (ℓ : MulAut W)
  have hz3 : z * z * z = 1 := by
    have h := congrArg (fun y : ↥L => (y : MulAut W)) (hL.2.2 ℓ)
    simpa [z, Subgroup.coe_pow, pow_three'] using h
  have hzz3 : ∀ a : W, z (z (z a)) = a := by
    intro a
    have h := congrArg (fun f : MulAut W => f a) hz3
    simpa [MulAut.mul_apply] using h
  have hz1 : z ≠ 1 := by
    rintro h
    exact hℓ1 (Subtype.ext (by simpa [z] using h))
  have hzcomm : ∀ y ∈ L, y * z = z * y := by
    intro y hy
    have h := congrArg (fun y : ↥L => (y : MulAut W))
      (Subgroup.mem_center_iff.1 hℓ ⟨y, hy⟩)
    simpa [z, Subgroup.coe_mul] using h
  let φ : W →* W := MonoidHom.id W * (z : W →* W)
  have hφ : ∀ y : W, φ y = y * z y := fun _ => rfl
  let R : Subgroup W := φ.range
  have hRinv : ∀ ℓ'' ∈ L, ∀ u ∈ R, ℓ'' u ∈ R := by
    intro ℓ'' hℓ'' u hu
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hu
    refine MonoidHom.mem_range.2 ⟨ℓ'' y, ?_⟩
    have hc : ℓ'' * z = z * ℓ'' := hzcomm ℓ'' hℓ''
    have h1 : z (ℓ'' y) = ℓ'' (z y) := by
      have h2 := congrArg (fun f : MulAut W => f y) hc
      simpa [MulAut.mul_apply] using h2.symm
    rw [hφ (ℓ'' y), hφ y, map_mul, h1]
  have hRfix : ∀ u ∈ R, z u = u → u = 1 := by
    intro u hu hzu
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hu
    have hzφ : z (φ y) = z y * z (z y) := by rw [hφ y, map_mul]
    have hzzφ : z (z (φ y)) = z (z y) * y := by
      rw [hzφ, map_mul, hzz3 y]
    have key : φ y * z (φ y) * z (z (φ y)) = 1 := by
      rw [hzzφ, hzφ, hφ y]
      have h1 : y * y = 1 := hW y
      have h2 : z y * z y = 1 := hW (z y)
      have h3 : z (z y) * z (z y) = 1 := hW (z (z y))
      calc (y * z y) * (z y * z (z y)) * (z (z y) * y)
          = (y * y) * (z y * z y) * (z (z y) * z (z y)) := by ac_rfl
        _ = 1 := by rw [h1, h2, h3, one_mul, one_mul]
    have key2 : φ y * φ y * φ y = 1 := by
      rw [hzu] at key
      rw [hzu] at key
      exact key
    rw [hW (φ y), one_mul] at key2
    exact key2
  have hfix : ∀ ℓ' : ↥L, ℓ' ∈ Subgroup.center ↥L → ℓ' ≠ 1 →
      ∀ u ∈ R, (ℓ' : MulAut W) u = u → u = 1 := by
    intro ℓ' hℓ' hℓ'1 u hu hfixu
    have hmem : (⟨ℓ, hℓ⟩ : Subgroup.center ↥L) ∈
        Submonoid.powers (⟨ℓ', hℓ'⟩ : Subgroup.center ↥L) :=
      mem_powers_of_prime_card (G := Subgroup.center ↥L) hZcard
        (g := (⟨ℓ', hℓ'⟩ : Subgroup.center ↥L))
        (g' := (⟨ℓ, hℓ⟩ : Subgroup.center ↥L))
        (by intro h; exact hℓ'1 (Subtype.ext_iff.1 h))
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 hmem
    have hn' : (ℓ' : MulAut W) ^ n = z := by
      have h := congrArg (fun y : Subgroup.center ↥L => ((y : ↥L) : MulAut W)) hn
      simpa [z, Subgroup.coe_pow] using h
    have hzu : z u = u := by
      rw [← hn']
      exact s16c167_mulAut_pow_apply (ℓ' : MulAut W) hfixu n
    exact hRfix u hu hzu
  have hmain := s16c167_invariant_eq_bot_or_card (W := W) hW hcard (L := L) hL R hRinv hfix
  have hRtop : R = ⊤ := by
    rcases hmain with hRbot | hRcard
    · exfalso
      apply hz1
      apply MulEquiv.ext
      intro y
      have hy : φ y ∈ R := MonoidHom.mem_range.2 ⟨y, rfl⟩
      rw [hRbot, Subgroup.mem_bot, hφ y] at hy
      have hzy : z y = y⁻¹ := eq_inv_of_mul_eq_one_right hy
      rw [hzy]
      exact (eq_inv_of_mul_eq_one_right (hW y)).symm
    · exact Subgroup.eq_top_of_card_eq R (by rw [hRcard, hcard])
  have hxR : x ∈ R := by rw [hRtop]; exact Subgroup.mem_top x
  exact hRfix x hxR hx

theorem s16c167_eq_one_of_commute_involution {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) {t : MulAut W} (ht : t * t = 1)
    (hcomm : ∀ ℓ ∈ L, t * ℓ = ℓ * t) : t = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht2 : ∀ y : W, t (t y) = y := by
    intro y
    have h := congrArg (fun f : MulAut W => f y) ht
    simpa [MulAut.mul_apply] using h
  let ψ : W →* W := MonoidHom.id W * (t : W →* W)
  have hψ : ∀ y : W, ψ y = y * t y := fun _ => rfl
  let U : Subgroup W := ψ.range
  have hUinv : ∀ ℓ ∈ L, ∀ u ∈ U, ℓ u ∈ U := by
    intro ℓ hℓ u hu
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hu
    refine MonoidHom.mem_range.2 ⟨ℓ y, ?_⟩
    have h1 : t (ℓ y) = ℓ (t y) := by
      have h2 := congrArg (fun f : MulAut W => f y) (hcomm ℓ hℓ)
      simpa [MulAut.mul_apply] using h2
    rw [hψ (ℓ y), hψ y, map_mul, h1]
  have hfix : ∀ ℓ' : ↥L, ℓ' ∈ Subgroup.center ↥L → ℓ' ≠ 1 →
      ∀ u ∈ U, (ℓ' : MulAut W) u = u → u = 1 :=
    fun ℓ' hℓ' hℓ'1 u _ hu =>
      s16c167_central_fixed_point_free (W := W) hW hcard (L := L) hL (ℓ := ℓ') hℓ' hℓ'1 hu
  have hmain := s16c167_invariant_eq_bot_or_card (W := W) hW hcard (L := L) hL U hUinv hfix
  rcases hmain with hUbot | hUcard
  · apply MulEquiv.ext
    intro y
    have hy : ψ y ∈ U := MonoidHom.mem_range.2 ⟨y, rfl⟩
    rw [hUbot, Subgroup.mem_bot, hψ y] at hy
    have hty : t y = y⁻¹ := eq_inv_of_mul_eq_one_right hy
    rw [hty]
    exact (eq_inv_of_mul_eq_one_right (hW y)).symm
  · have hUtop : U = ⊤ := Subgroup.eq_top_of_card_eq U (by rw [hUcard, hcard])
    apply MulEquiv.ext
    intro w
    have hw : w ∈ U := by rw [hUtop]; exact Subgroup.mem_top w
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hw
    rw [← hy, hψ y, map_mul, ht2 y]
    exact mul_comm (t y) y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
