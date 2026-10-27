module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE8

public section

namespace CFSG.StandardType

namespace NoOffE8Five

local instance noOffE8FiveFactFiveFB : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem card_centralizer_lt_of_automizer {C : Type*} [Group C] {lam : ZMod 5}
    (hlam : lam * lam = -1) (ι : Multiplicative (NoOffRest.eigE8 5 lam) →* C)
    (hι : Function.Injective ι) {a : C}
    (hu : ∃ u : NoOffRest.centE8W, ∀ s : NoOffRest.eigE8 5 lam,
      a * ι (Multiplicative.ofAdd s) * a⁻¹ =
        ι (Multiplicative.ofAdd (NoOffRest.eigPerm 5 lam u s)))
    (ha5 : a ^ 5 = 1) (hnc : ∃ x ∈ ι.range, a * x ≠ x * a) :
    Nat.card {x : ι.range // a * (x : C) = (x : C) * a} < 5 ^ 3 := by
  classical
  obtain ⟨u, hu⟩ := hu
  have hiter : ∀ k : ℕ, ∀ s : NoOffRest.eigE8 5 lam,
      ι (Multiplicative.ofAdd (((NoOffRest.eigPerm 5 lam u) ^ k) s)) =
        a ^ k * ι (Multiplicative.ofAdd s) * (a ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
        intro s
        rw [pow_succ', Equiv.Perm.mul_apply,
          ← hu (((NoOffRest.eigPerm 5 lam u) ^ k) s), ih s, pow_succ']
        group
  have hρ5 : (NoOffRest.eigPerm 5 lam u) ^ 5 = 1 := by
    refine Equiv.ext fun s => ?_
    have h := hiter 5 s
    rw [ha5] at h
    simp at h
    simpa using hι h
  have hu5 : u ^ 5 = 1 := by
    apply NoOffRest.eigPerm_injective hlam
    rw [map_pow, hρ5, map_one]
  have hu1 : u ≠ 1 := by
    intro hu1
    obtain ⟨x, hxmem, hxnc⟩ := hnc
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hxmem
    refine hxnc ?_
    rw [← hs]
    have h := hu (Multiplicative.toAdd s)
    rw [hu1] at h
    simp only [map_one, Equiv.Perm.one_apply, ofAdd_toAdd] at h
    exact (mul_inv_eq_iff_eq_mul).mp h
  have hA : CFSG.Assembly.IsElemAbelian 5 (Subgroup.zpowers u) := by
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    calc (u ^ k) ^ (5 : ℕ) = (u ^ k) ^ (5 : ℤ) := rfl
      _ = (u ^ (5 : ℤ)) ^ k := zpow_comm u k 5
      _ = 1 := by
        rw [show u ^ (5 : ℤ) = 1 by simpa using hu5, one_zpow]
  have hA1 : Subgroup.zpowers u ≠ ⊥ := by
    intro h
    have hmem : u ∈ (⊥ : Subgroup NoOffRest.centE8W) := by
      rw [← h]
      exact Subgroup.mem_zpowers u
    exact hu1 (Subgroup.mem_bot.mp hmem)
  have hAcard : Nat.card (Subgroup.zpowers u) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu5 hu1]
  have hno := NoOffRest.actNoOffender_eigPerm hlam (Subgroup.zpowers u) hA hA1
  rw [hAcard, NoOffRest.card_eigE8 (p := 5) (by norm_num) hlam] at hno
  have hfix_lt : Nat.card {v : NoOffRest.eigE8 5 lam //
      ∀ b ∈ Subgroup.zpowers u, NoOffRest.eigPerm 5 lam b v = v} < 5 ^ 3 := by
    have h4 : (5 : ℕ) ^ 4 = 5 * 125 := by norm_num
    have h3 : (5 : ℕ) ^ 3 = 125 := by norm_num
    rw [h4] at hno
    rw [h3]
    omega
  let f : {x : ι.range // a * (x : C) = (x : C) * a} →
      {v : NoOffRest.eigE8 5 lam //
        ∀ b ∈ Subgroup.zpowers u, NoOffRest.eigPerm 5 lam b v = v} :=
    fun x =>
      let s := Classical.choose (MonoidHom.mem_range.mp x.1.2)
      have hs : ι s = (x.1 : C) := Classical.choose_spec (MonoidHom.mem_range.mp x.1.2)
      ⟨Multiplicative.toAdd s, by
        have hcomm : a * ι (Multiplicative.ofAdd (Multiplicative.toAdd s)) =
            ι (Multiplicative.ofAdd (Multiplicative.toAdd s)) * a := by
          rw [ofAdd_toAdd, hs]
          exact x.2
        have hρ : NoOffRest.eigPerm 5 lam u (Multiplicative.toAdd s) =
            Multiplicative.toAdd s := by
          have h := hu (Multiplicative.toAdd s)
          have h1 : ι (Multiplicative.ofAdd
                (NoOffRest.eigPerm 5 lam u (Multiplicative.toAdd s))) =
              ι (Multiplicative.ofAdd (Multiplicative.toAdd s)) := by
            rw [← h, hcomm]
            group
          exact hι h1
        intro b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [map_zpow]
        exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hρ k⟩
  haveI : Finite ι.range := (Set.finite_range ι).to_subtype
  have hf_inj : Function.Injective f := by
    intro x x' hxx
    have hs : Classical.choose (MonoidHom.mem_range.mp x.1.2) =
        Classical.choose (MonoidHom.mem_range.mp x'.1.2) := by
      have hval := congrArg Subtype.val hxx
      exact Multiplicative.toAdd.injective hval
    apply Subtype.ext
    apply Subtype.ext
    rw [← Classical.choose_spec (MonoidHom.mem_range.mp x.1.2),
      ← Classical.choose_spec (MonoidHom.mem_range.mp x'.1.2), hs]
  calc Nat.card {x : ι.range // a * (x : C) = (x : C) * a}
      ≤ Nat.card {v : NoOffRest.eigE8 5 lam //
          ∀ b ∈ Subgroup.zpowers u, NoOffRest.eigPerm 5 lam b v = v} :=
        Nat.card_le_card_of_injective f hf_inj
    _ < 5 ^ 3 := hfix_lt

end NoOffE8Five

end CFSG.StandardType
