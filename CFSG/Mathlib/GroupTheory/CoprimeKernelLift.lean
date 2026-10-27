module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CoprimeKernel

variable {N Q : Type*} [Group N] [Group Q]

theorem exists_lift_centralizing [Finite N] {f : N →* Q} {U : Subgroup N} {p : ℕ} [Fact p.Prime]
    (hU : IsPGroup p U) (hpZ : ¬ p ∣ Nat.card f.ker) {n : N}
    (hcomm : ∀ u ∈ U, f u * f n = f n * f u) :
    ∃ n' : N, f n' = f n ∧ ∀ u ∈ U, u * n' = n' * u := by
  classical
  letI : MulAction U N := MulAction.compHom N (ConjAct.toConjAct.toMonoidHom.comp U.subtype)
  have hsmul : ∀ (u : U) (g : N), u • g = (u : N) * g * (u : N)⁻¹ := fun u g => rfl
  obtain ⟨S, hS⟩ : ∃ S : SubMulAction U N, ∀ g, g ∈ S ↔ f g = f n :=
    ⟨{ carrier := {g | f g = f n}
       smul_mem' := by
        intro u g hg
        change f (u • g) = f n
        rw [hsmul, map_mul, map_mul, map_inv]
        have hg' : f g = f n := hg
        rw [hg', hcomm u u.2]
        group }, fun _ => Iff.rfl⟩
  have hcard : Nat.card S = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun g => ⟨n⁻¹ * g.1, ?_⟩
        invFun := fun z => ⟨n * z.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [MonoidHom.mem_ker, map_mul, map_inv, (hS g.1).1 g.2, inv_mul_cancel]
    · have hz : f z.1 = 1 := z.2
      refine (hS _).2 ?_
      rw [map_mul, hz, mul_one]
    · intro g
      apply Subtype.ext
      simp
    · intro z
      apply Subtype.ext
      simp
  have hmod := hU.card_modEq_card_fixedPoints S
  by_contra hno
  push Not at hno
  have hfix : Nat.card (MulAction.fixedPoints U S) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨s, hs⟩ => ?_⟩
    obtain ⟨u, hu, hne⟩ := hno s.1 ((hS s.1).1 s.2)
    apply hne
    have h1 : (⟨u, hu⟩ : U) • s = s := MulAction.mem_fixedPoints.1 hs ⟨u, hu⟩
    have h3 : ((⟨u, hu⟩ : U) • s).1 = s.1 := congrArg Subtype.val h1
    rw [SubMulAction.val_smul, hsmul] at h3
    have h3' : u * s.1 * u⁻¹ = s.1 := h3
    calc u * s.1 = u * s.1 * u⁻¹ * u := by group
      _ = s.1 * u := by rw [h3']
  rw [hfix, hcard] at hmod
  exact hpZ ((Nat.modEq_zero_iff_dvd).1 hmod)

theorem inf_ker_eq_bot_of_coprime [Finite N] {f : N →* Q} {U : Subgroup N}
    (hcop : Nat.Coprime (Nat.card f.ker) (Nat.card U)) : U ⊓ f.ker = ⊥ := by
  have h1 : Nat.card ↥(U ⊓ f.ker) ∣ Nat.card U := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(U ⊓ f.ker) ∣ Nat.card f.ker := Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.card ↥(U ⊓ f.ker) ∣ Nat.gcd (Nat.card f.ker) (Nat.card U) := Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h3)

theorem injective_of_coprime [Finite N] {f : N →* Q} {U : Subgroup N}
    (hcop : Nat.Coprime (Nat.card f.ker) (Nat.card U)) :
    Function.Injective (fun u : U => f (u : N)) := by
  intro u₁ u₂ h
  have hmem : (u₁ : N)⁻¹ * (u₂ : N) ∈ U ⊓ f.ker := by
    refine Subgroup.mem_inf.2 ⟨U.mul_mem (U.inv_mem u₁.2) u₂.2, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h' : f (u₁ : N) = f (u₂ : N) := h
    rw [h', inv_mul_cancel]
  rw [inf_ker_eq_bot_of_coprime hcop, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact Subtype.ext hmem

theorem exists_pow_lift [Finite N] {f : N →* Q} {p : ℕ} (hp : p.Prime) (hpZ : ¬ p ∣ Nat.card f.ker)
    {n : N} (hn : (f n) ^ p = 1) : ∃ m : ℕ, f (n ^ m) = f n ∧ (n ^ m) ^ p = 1 := by
  have hcop : Nat.Coprime (Nat.card f.ker) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpZ).symm
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨Nat.card f.ker * t, ?_, ?_⟩
  · rw [map_pow]
    have h1 : Nat.card f.ker * t = p * (Nat.card f.ker * t / p) + 1 := by
      have := Nat.div_add_mod (Nat.card f.ker * t) p
      rw [ht] at this
      exact this.symm
    rw [h1, pow_add, pow_mul, hn, one_pow, one_mul, pow_one]
  · have hz : n ^ p ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, hn]
    have hzc : (⟨n ^ p, hz⟩ : f.ker) ^ Nat.card f.ker = 1 := pow_card_eq_one'
    have hzc' : (n ^ p) ^ Nat.card f.ker = 1 := by
      have := congrArg Subtype.val hzc
      simpa using this
    calc (n ^ (Nat.card f.ker * t)) ^ p = ((n ^ p) ^ Nat.card f.ker) ^ t := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hzc', one_pow]

theorem commute_of_perfect {f : N →* Q} {L : Subgroup N} (hL : Group.IsPerfect L)
    (hZL : f.ker ≤ L) (hZc : ∀ z ∈ f.ker, ∀ l ∈ L, l * z = z * l) {b : N}
    (hb : ∀ l ∈ L, f b * f l = f l * f b) : ∀ l ∈ L, b * l = l * b := by
  have hmem : ∀ l : L, (l : N)⁻¹ * b * l * b⁻¹ ∈ f.ker := by
    intro l
    rw [MonoidHom.mem_ker]
    have h1 := hb l l.2
    simp only [map_mul, map_inv]
    calc (f l)⁻¹ * f b * f l * (f b)⁻¹ = (f l)⁻¹ * (f b * f l) * (f b)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  let c : L →* f.ker :=
    { toFun := fun l => ⟨(l : N)⁻¹ * b * l * b⁻¹, hmem l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l₁ l₂ => by
        apply Subtype.ext
        have hc : Commute (l₂ : N) ((l₁ : N)⁻¹ * b * l₁ * b⁻¹) := hZc _ (hmem l₁) l₂ l₂.2
        have hc' : (l₂ : N)⁻¹ * ((l₁ : N)⁻¹ * b * l₁ * b⁻¹) =
            ((l₁ : N)⁻¹ * b * l₁ * b⁻¹) * (l₂ : N)⁻¹ := hc.inv_left.eq
        change ((l₁ * l₂ : L) : N)⁻¹ * b * ((l₁ * l₂ : L) : N) * b⁻¹ =
          ((l₁ : N)⁻¹ * b * l₁ * b⁻¹) * ((l₂ : N)⁻¹ * b * l₂ * b⁻¹)
        rw [Subgroup.coe_mul]
        calc ((l₁ : N) * l₂)⁻¹ * b * ((l₁ : N) * l₂) * b⁻¹
            = (l₂ : N)⁻¹ * ((l₁ : N)⁻¹ * b * l₁ * b⁻¹) * (b * l₂ * b⁻¹) := by group
          _ = ((l₁ : N)⁻¹ * b * l₁ * b⁻¹) * (l₂ : N)⁻¹ * (b * l₂ * b⁻¹) := by rw [hc']
          _ = ((l₁ : N)⁻¹ * b * l₁ * b⁻¹) * ((l₂ : N)⁻¹ * b * l₂ * b⁻¹) := by group }
  have hA : ∀ a a' : f.ker, a * a' = a' * a := fun a a' =>
    Subtype.ext (hZc a' a'.2 a (hZL a.2))
  have hφ : (⊤ : Subgroup L) ≤ c.ker := by
    rw [← hL.commutator_eq_top]
    refine Subgroup.commutator_le.mpr fun a _ a' _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hA (c a) (c a'),
      mul_inv_cancel_right, mul_inv_cancel]
  intro l hl
  have h1 : c ⟨l, hl⟩ = 1 := hφ (Subgroup.mem_top _)
  have h2 := congrArg Subtype.val h1
  change l⁻¹ * b * l * b⁻¹ = 1 at h2
  calc b * l = l * (l⁻¹ * b * l * b⁻¹) * b := by group
    _ = l * b := by rw [h2]; group

end CFSG.CoprimeKernel

end
