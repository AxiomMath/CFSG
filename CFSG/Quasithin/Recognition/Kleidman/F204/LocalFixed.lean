module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalBall

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem card_fixed_nbrs_three (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = true) {t : G} (ht : t ∈ stab δ) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    Nat.card {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S) // μ ∈ nbrs δ ∧ t ∈ stab μ} = 2 := by
  classical
  have hA := Amal.of_frame F
  obtain ⟨hG0, hfix⟩ := mem_stab.mp ht
  set tg : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨t, hG0⟩ with htg
  have hmem : ∀ x, x ∈ nbrs δ → tg • x ∈ nbrs δ := by
    intro x hx
    have := (smul_adj tg).mpr hx
    rwa [hfix] at this
  set α := {x : Geo (P1 L1 L2 S) (P2 L1 L2 S) // x ∈ nbrs δ} with hα
  have hcard : Nat.card α = 5 := hA.card_nbrs δ
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype α := Fintype.ofFinite α
  let f : Function.End α := fun x => ⟨tg • x.1, hmem _ x.2⟩
  have hpow : ∀ (n : ℕ) (x : α), ((f ^ n) x).1 = (tg ^ n) • x.1 := by
    intro n
    induction n with
    | zero => intro x; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, mul_smul]
      show ((f ^ n) (f x)).1 = _
      rw [ih]
  have htg3 : tg ^ 3 = 1 := Subtype.ext (by simpa using ht3)
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hpow, htg3, one_smul]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (α := α) hf3
  rw [Fintype.card_eq_nat_card, hcard] at hmod
  set c := Fintype.card f.fixedPoints with hc
  have hc5 : c ≤ 5 := by
    rw [hc, Fintype.card_eq_nat_card]
    calc Nat.card f.fixedPoints ≤ Nat.card α := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 5 := hcard
  have hc_mod : c % 3 = 2 := by
    have := hmod
    unfold Nat.ModEq at this
    omega
  have hcne : c ≠ 5 := by
    intro h5
    apply ht1
    have hall : ∀ x : α, f x = x := by
      intro x
      by_contra hx
      have hlt := Finite.card_subtype_lt (p := fun y : α => f y = y) hx
      have hceq : Nat.card {y : α // f y = y} = c := by
        rw [hc, Fintype.card_eq_nat_card]; rfl
      omega
    have hball : t ∈ ballStab 1 δ := by
      rw [mem_ballStab]
      intro ε hε
      rcases (dist_le_one_iff rfl).mp hε with rfl | hadj
      · exact ht
      · exact mem_stab_of_smul_eq (g := tg) (congrArg Subtype.val (hall ⟨ε, hadj⟩))
    rw [ballStab_one_true F hδ] at hball
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (stab δ)) ⟨t, hball⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk', ht3⟩
    rwa [hg, pow_one] at this
  have hc2 : c = 2 := by omega
  let e : {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S) // μ ∈ nbrs δ ∧ t ∈ stab μ} ≃ f.fixedPoints :=
    { toFun := fun μ => ⟨⟨μ.1, μ.2.1⟩, Subtype.ext (smul_eq_of_mem_stab (g := tg) μ.2.2)⟩
      invFun := fun x => ⟨x.1.1, x.1.2,
        mem_stab_of_smul_eq (g := tg) (congrArg Subtype.val x.2)⟩
      left_inv := fun μ => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, ← hc, hc2]

end CFSG.Quasithin.Kleidman.F204
