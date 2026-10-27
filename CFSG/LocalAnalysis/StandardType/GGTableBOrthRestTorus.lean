module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace OrthRest

section Lift

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem pow_card_ker_eq_one {z : L'} (hz : z ∈ ψ.ker) : z ^ Nat.card ψ.ker = 1 := by
  have h := pow_card_eq_one' (G := ψ.ker) (x := ⟨z, hz⟩)
  exact congrArg Subtype.val h

theorem eq_of_lift_of_coprime (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ}
    (hcop : Nat.Coprime p (Nat.card ψ.ker)) {x y : L'} (hxy : ψ x = ψ y) (hx : x ^ p = 1)
    (hy : y ^ p = 1) : x = y := by
  set z := x⁻¹ * y with hz
  have hzk : z ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hxz : x * z = z * x := Subgroup.mem_center_iff.mp (hker hzk) x
  have hyxz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p = 1 := by
    have h1 : y ^ p = x ^ p * z ^ p := by rw [hyxz, (Commute.mul_pow hxz p)]
    rw [hx, hy, one_mul] at h1
    exact h1.symm
  have hz1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzp)
    (orderOf_dvd_of_pow_eq_one (pow_card_ker_eq_one hzk))
  rw [orderOf_eq_one_iff] at hz1
  rw [hyxz, hz1, mul_one]

theorem exists_section_of_exponent_coprime (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {m : ℕ} (hm : 1 < m)
    (hcop : Nat.Coprime m (Nat.card ψ.ker)) {H : Type} [Group H]
    (β : H →* R) (hβcomm : ∀ x y, Commute (β x) (β y))
    (hβpow : ∀ x, β x ^ m = 1) :
    ∃ σ : H →* L', ∀ x, ψ (σ x) = β x := by
  set N := Nat.card ψ.ker with hN
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hm
  choose l hl using fun e : H => hψ (β e)
  set s : H → L' := fun e => l e ^ (N * k) with hs
  have hsψ : ∀ e, ψ (s e) = β e := by
    intro e
    rw [hs, map_pow, hl, ← Nat.mod_add_div (N * k) m, pow_add, pow_mul, hβpow e, one_pow,
      mul_one, hk, pow_one]
  have hsp : ∀ e, s e ^ m = 1 := by
    intro e
    have h1 : l e ^ m ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hl, hβpow e]
    calc s e ^ m = ((l e ^ m) ^ N) ^ k := by
          rw [hs]
          simp only [← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [pow_card_ker_eq_one h1, one_pow]
  have hcomm : ∀ e e', s e * s e' = s e' * s e := by
    intro e e'
    set c := s e * s e' * (s e)⁻¹ * (s e')⁻¹ with hc
    have hck : c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hc]
      simp only [map_mul, map_inv, hsψ]
      rw [(hβcomm e e').eq]
      group
    have h1 := TableBSymp.pow_conj_eq_of_central (hker hck) m
    rw [hsp e, one_mul, inv_one, mul_one] at h1
    have hcp : c ^ m = 1 := by
      have h2 : c ^ m * s e' * (s e')⁻¹ = s e' * (s e')⁻¹ := by rw [← h1]
      rwa [mul_inv_cancel_right, mul_inv_cancel] at h2
    have hc1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hcp)
      (orderOf_dvd_of_pow_eq_one (pow_card_ker_eq_one hck))
    rw [orderOf_eq_one_iff, hc] at hc1
    calc s e * s e' = s e * s e' * (s e)⁻¹ * (s e')⁻¹ * (s e' * s e) := by group
      _ = s e' * s e := by rw [hc1, one_mul]
  refine ⟨MonoidHom.mk' s fun e e' => ?_, hsψ⟩
  refine eq_of_lift_of_coprime hker hcop ?_ (hsp _) ?_
  · rw [map_mul, hsψ, hsψ, hsψ, map_mul]
  · rw [Commute.mul_pow (hcomm e e') m, hsp, hsp, one_mul]

theorem exists_section_of_coprime (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card ψ.ker)) {E : Subgroup R} (hE : IsElemAbelian p E) :
    ∃ σ : E →* L', ∀ e, ψ (σ e) = e := by
  exact exists_section_of_exponent_coprime hψ hker hp.one_lt hcop E.subtype
    (fun x y => TableB.IsElemAbelian.comm hE x.2 y.2) (fun x => hE.2 x x.2)

end Lift

section TorusLift

variable {R : Type} [Group R] {p r : ℕ}

theorem ggTorusLift_of_R (hp : p.Prime) (hZ : Subgroup.center R = ⊥) (hZp : GGCenterPrime p R)
    {U E : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set R)) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ r) : GGTorusLift p r R := by
  intro L' _ _ ψ hψ hker hperf
  have hkc := TableBUR.ker_eq_center_of_surjective hψ hker hZ
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    rw [hkc]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (hZp L' ψ hψ hker hperf)
  obtain ⟨σ, hσ⟩ := exists_section_of_coprime hψ hker hp hcop hE
  have hσi : Function.Injective σ := fun a b hab => Subtype.ext (by rw [← hσ a, ← hσ b, hab])
  obtain ⟨T, hT, hT2, hET⟩ := TableBSymp.exists_twoSubgroup_lift (E := σ.range) hψ hker hU hU2
    (by
      rintro _ ⟨e, rfl⟩ u hu
      rw [hσ]
      exact (Subgroup.mem_normalizer_iff.mp (hEU e.2) u).mp hu)
  refine ⟨T, σ.range, hT, hT2, hET, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨_, a', rfl⟩ := a
    obtain ⟨_, b', rfl⟩ := b
    apply Subtype.ext
    change σ a' * σ b' = σ b' * σ a'
    have hab : a' * b' = b' * a' := Subtype.ext (TableB.IsElemAbelian.comm hE a'.2 b'.2)
    rw [← map_mul, ← map_mul, hab]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow, show e ^ p = 1 from Subtype.ext (hE.2 e e.2), map_one]
  · rw [← hcard, ← Nat.card_congr (MonoidHom.ofInjective hσi).toEquiv]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨e, rfl⟩, he⟩
    have h1 : ψ (σ e) = 1 := he
    rw [hσ] at h1
    have h2 : e = 1 := Subtype.ext h1
    rw [h2, map_one]
    exact Subgroup.one_mem _

end TorusLift

end OrthRest

@[expose] def GGOrthRestTorusInput : Prop :=
  GGOrthRestAll fun p r R _ => ∃ U E : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧
    E ≤ Subgroup.normalizer (U : Set R) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ r

theorem ggOrthRestTorusLiftInput_of_torus (hZ : GGOrthRestCenterInput)
    (h : GGOrthRestTorusInput) : GGOrthRestTorusLiftInput := by
  refine ⟨fun K _ _ n m p b c hK hm hp hpn hbc => ?_, fun K _ _ m hK hm => ?_⟩
  · obtain ⟨U, E, hU, hU2, hEU, hE, hc⟩ := h.1 K n m p b c hK hm hp hpn hbc
    obtain ⟨hZ1, hZp⟩ := hZ.1 K n m p b c hK hm hp hpn hbc
    exact OrthRest.ggTorusLift_of_R hp hZ1 hZp hU hU2 hEU hE hc
  · obtain ⟨U, E, hU, hU2, hEU, hE, hc⟩ := h.2 K m hK hm
    obtain ⟨hZ1, hZp⟩ := hZ.2 K m hK hm
    exact OrthRest.ggTorusLift_of_R Nat.prime_three hZ1 hZp hU hU2 hEU hE hc

end CFSG.StandardType
