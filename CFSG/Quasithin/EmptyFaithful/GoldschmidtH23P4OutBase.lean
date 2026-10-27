module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H23Out

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Out5Pow (X : Type*) [Group X] : Prop :=
  ∀ (φ : MulAut X) (a : ℕ), φ ^ 5 ^ a = 1 → ∃ g : X, ∀ x, φ x = g * x * g⁻¹

@[expose] def NoFiveOut (X : Type*) [Group X] : Prop :=
  ¬ 5 ∣ Nat.card (Outer X)

theorem Out5Pow.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : Out5Pow X) :
    Out5Pow Y := by
  intro φ a hφ
  have h1 : ((MulAut.congr e).symm φ) ^ 5 ^ a = 1 := by
    rw [← map_pow, hφ, map_one]
  obtain ⟨g, hg⟩ := h _ a h1
  refine ⟨e g, fun y => ?_⟩
  have h2 : e.symm (φ y) = g * e.symm y * g⁻¹ := by
    have h2 := hg (e.symm y)
    rwa [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      e.apply_symm_apply] at h2
  have h3 : φ y = e (g * e.symm y * g⁻¹) := by
    rw [← h2, e.apply_symm_apply]
  rw [h3, map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem NoFiveOut.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoFiveOut Y) : NoFiveOut X := by
  unfold NoFiveOut at h ⊢
  rwa [Nat.card_congr (equivalence e).toEquiv]

theorem Out5Pow.of_noFiveOut {X : Type*} [Group X] [Finite X] (h : NoFiveOut X) : Out5Pow X := by
  intro φ a hφ
  have : Finite (MulAut X) := inferInstance
  have : Finite (Outer X) := inferInstance
  set q : Outer X := QuotientGroup.mk' (inner X) φ with hq
  have hqa : orderOf q ∣ 5 ^ a :=
    orderOf_dvd_of_pow_eq_one (by rw [hq, ← map_pow, hφ, map_one])
  have hqc : orderOf q ∣ Nat.card (Outer X) := orderOf_dvd_natCard q
  have hq1 : orderOf q = 1 := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hqa
    rcases m with _ | m
    · simpa using hm
    · have h5 : 5 ∣ orderOf q := by
        rw [hm]
        exact dvd_pow_self 5 (Nat.succ_ne_zero m)
      exact absurd (h5.trans hqc) h
  have hq2 : q = 1 := orderOf_eq_one_iff.mp hq1
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff φ).mp hq2
  exact ⟨g, fun x => by rw [← hg]; rfl⟩

theorem NoFiveOut.of_card_outer_le_four {X : Type*} [Group X] [Finite X]
    (h : Nat.card (Outer X) ≤ 4) : NoFiveOut X := by
  intro h5
  have : Finite (MulAut X) := inferInstance
  have : Finite (Outer X) := inferInstance
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  have := Nat.le_of_dvd hpos h5
  omega

theorem NoFiveOut.of_equiv_card_outer_le {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : Nat.card (Outer Y) ≤ 4) : NoFiveOut X :=
  NoFiveOut.of_card_outer_le_four (by rwa [Nat.card_congr (equivalence e).toEquiv])

theorem NoFiveOut.of_card_mulAut_le {X : Type*} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hA : Nat.card (MulAut X) ≤ 4 * Nat.card X) : NoFiveOut X := by
  apply NoFiveOut.of_card_outer_le_four
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
    have hcen : g ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut X => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hZ, Subgroup.mem_bot] at hcen
  have hinn : Nat.card (inner X) = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx := (inner X).index_mul_card
  rw [hinn] at hidx
  have hpos : 0 < Nat.card X := Nat.card_pos
  have h1 : (inner X).index * Nat.card X ≤ 4 * Nat.card X := hidx ▸ hA
  exact Nat.le_of_mul_le_mul_right h1 hpos

theorem NoFiveOut.of_equiv_card_mulAut_le {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (hZ : Subgroup.center Y = ⊥) (hA : Nat.card (MulAut Y) ≤ 4 * Nat.card Y) :
    NoFiveOut X := by
  have hZX : Subgroup.center X = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    have h1 : e g ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg x]
    rw [hZ, Subgroup.mem_bot] at h1
    exact e.injective (h1.trans (map_one e).symm)
  refine NoFiveOut.of_card_mulAut_le hZX ?_
  rwa [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]

theorem Out5Pow.range_le_inner {X : Type*} [Group X] (h : Out5Pow X) {Y : Type*} [Group Y]
    (hY : IsPGroup 5 Y) (ρ : Y →* MulAut X) :
    ρ.range ≤ (MulAut.conj : X →* MulAut X).range := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := hY y
  obtain ⟨g, hg⟩ := h (ρ y) a (by rw [← map_pow, ha, map_one])
  exact ⟨g, MulEquiv.ext fun x => (hg x).symm⟩

end CFSG.Quasithin.H23Out
