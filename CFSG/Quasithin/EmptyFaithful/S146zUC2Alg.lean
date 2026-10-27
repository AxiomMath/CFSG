module

import CFSG.Quasithin.EmptyFaithful.SzN15Nat
import CFSG.Quasithin.EmptyFaithful.S153LKsA2
import CFSG.Open.MatrixFixedVectors
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.S146zU.UC2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Alg

theorem card_eq_card_ker_mul_card_range {G Q : Type} [Group G] [Group Q] (f : G →* Q) :
    Nat.card G = Nat.card ↥f.ker * Nat.card ↥f.range := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]

theorem card_multiplicative_fin_two_fun (K : Type) [Finite K] :
    Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
  simp

@[expose] def fixNat {K : Type} [Field K] (B : Subgroup ↥(StatedSL 2 K)) :
    Subgroup (Multiplicative (Fin 2 → K)) where
  carrier := {x | ∀ g ∈ B, natAct (StatedSL 2 K) g x = x}
  one_mem' := fun g _ => by simp [natAct]
  mul_mem' := fun {a b} ha hb g hg => by
    rw [SzN15.natAct_mul_elt, ha g hg, hb g hg]
  inv_mem' := fun {a} ha g hg => by
    rw [SzN15.natAct_inv_elt, ha g hg]

theorem card_natAct_fixed_le {K : Type} [Field K] [Finite K] (g : ↥(StatedSL 2 K))
    (hg : g ≠ 1) :
    Nat.card {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) g x = x} ≤ Nat.card K :=
  (Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)).le.trans
    (CFSG.Open.StatedAPI.card_mulVec_fixed_le fun h => hg (Subtype.ext (Units.ext h)))

theorem card_fixNat_le_of_ne_bot {K : Type} [Field K] [Finite K] {B : Subgroup ↥(StatedSL 2 K)}
    (hB : B ≠ ⊥) : Nat.card ↥(fixNat B) ≤ Nat.card K := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hg1 : (a : ↥(StatedSL 2 K)) ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : ↥(fixNat B) => (⟨x.1, x.2 (a : ↥(StatedSL 2 K)) a.2⟩ :
      {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) (a : ↥(StatedSL 2 K)) x = x}))
    ?_) (card_natAct_fixed_le _ hg1)
  intro x y h
  have h1 : (x : Multiplicative (Fin 2 → K)) = (y : Multiplicative (Fin 2 → K)) :=
    congrArg (fun z : {x : Multiplicative (Fin 2 → K) //
      natAct (StatedSL 2 K) (a : ↥(StatedSL 2 K)) x = x} => (z : Multiplicative (Fin 2 → K))) h
  exact Subtype.ext h1

theorem card_statedSL_two (K : Type) [Field K] [Finite K] :
    Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem card_field_eq_sixteen {K : Type} [Field K] [Finite K]
    (h : Nat.card ↥(StatedSL 2 K) = 4080) : Nat.card K = 16 := by
  rw [card_statedSL_two] at h
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  generalize Nat.card K = q at h h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · interval_cases q <;> omega
  · have h3 : 17 ≤ q := hgt
    have h4 : q ^ 2 - 1 ≥ 288 := by
      have : q ^ 2 ≥ 17 * 17 := Nat.pow_le_pow_left h3 2
      omega
    have : q * (q ^ 2 - 1) ≥ 17 * 288 := Nat.mul_le_mul h3 h4
    omega

theorem card_le_field_of_exp_two {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (B : Subgroup ↥(StatedSL 2 K)) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card ↥B ≤ Nat.card K := by
  have hdvd : Nat.card ↥B ∣ Nat.card ↥(StatedSL 2 K) := Subgroup.card_subgroup_dvd_card B
  have hcard : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
    card_statedSL_two K
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, Subtype.ext (by simpa using hB g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hm0, pow_zero] at hK
    omega
  have hodd : Odd (Nat.card K ^ 2 - 1) := by
    rw [hK, ← pow_mul]
    exact S153L.ks_odd_two_pow_sub_one (by omega)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K ^ 2 - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  rw [hk, hcard] at hdvd
  have h2 : 2 ^ k ∣ Nat.card K := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd Nat.card_pos h2

theorem card_mul_card_fixNat_le {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (B : Subgroup ↥(StatedSL 2 K)) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card ↥B * Nat.card ↥(fixNat B) ≤ Nat.card K ^ 2 := by
  by_cases hbot : B = ⊥
  · subst hbot
    rw [Subgroup.card_bot, one_mul]
    calc Nat.card ↥(fixNat (⊥ : Subgroup ↥(StatedSL 2 K))) ≤
          Nat.card (Multiplicative (Fin 2 → K)) := Subgroup.card_le_card_group _
      _ = Nat.card K ^ 2 := card_multiplicative_fin_two_fun K
  · calc Nat.card ↥B * Nat.card ↥(fixNat B) ≤ Nat.card K * Nat.card K :=
          Nat.mul_le_mul (card_le_field_of_exp_two hK B hB) (card_fixNat_le_of_ne_bot hbot)
      _ = Nat.card K ^ 2 := (sq _).symm

theorem card_eq_field_of_mul_card_fixNat {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) {B : Subgroup ↥(StatedSL 2 K)} (hB : ∀ x ∈ B, x ^ 2 = 1)
    (hbot : B ≠ ⊥) (heq : Nat.card ↥B * Nat.card ↥(fixNat B) = Nat.card K ^ 2) :
    Nat.card ↥B = Nat.card K ∧ Nat.card ↥(fixNat B) = Nat.card K := by
  have h1 := card_le_field_of_exp_two hK B hB
  have h2 := card_fixNat_le_of_ne_bot hbot
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h3 : Nat.card K * Nat.card K ≤ Nat.card ↥B * Nat.card ↥(fixNat B) := by
    rw [heq, sq]
  have h4 : Nat.card ↥B = Nat.card K := by
    refine le_antisymm h1 (le_of_not_gt fun hlt => ?_)
    have := Nat.mul_lt_mul_of_lt_of_le hlt h2 hpos
    omega
  refine ⟨h4, le_antisymm h2 (le_of_not_gt fun hlt => ?_)⟩
  have := Nat.mul_lt_mul_of_le_of_lt h1 hlt hpos
  omega

theorem card_le_of_map_le {V N : Type} [Group V] [Group N] [Finite V] [Finite N] (Θ : V →* N)
    {C : Subgroup V}
    (hk : ∀ v, Θ v = 1 ↔ v ∈ C) (D : Subgroup V) (F : Subgroup N) (hDF : D.map Θ ≤ F) :
    Nat.card ↥D ≤ Nat.card ↥C * Nat.card ↥F := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥D →* ↥F, ∀ d, ((θ d : ↥F) : N) = Θ (d : V) :=
    ⟨(Θ.comp D.subtype).codRestrict F (fun d => hDF ⟨d, d.2, rfl⟩), fun d => rfl⟩
  rw [card_eq_card_ker_mul_card_range θ]
  refine Nat.mul_le_mul ?_ (Subgroup.card_le_card_group _)
  have hker : ∀ c : ↥θ.ker, ((c : ↥D) : V) ∈ C := fun c => by
    have h1 : θ (c : ↥D) = 1 := c.2
    have h2 : Θ ((c : ↥D) : V) = 1 := by
      rw [← hθ, h1]
      rfl
    exact (hk _).mp h2
  refine Nat.card_le_card_of_injective (fun c : ↥θ.ker => (⟨((c : ↥D) : V), hker c⟩ : ↥C)) ?_
  intro c d h
  have h1 : ((c : ↥D) : V) = ((d : ↥D) : V) := congrArg (fun z : ↥C => (z : V)) h
  exact Subtype.ext (Subtype.ext h1)

theorem exists_theta {V M₁ M₂ : Type} [CommGroup V] [Group M₁] [Group M₂]
    {W₁ W₂ C : Subgroup V} (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ ≤ C) (hC₁ : C ≤ W₁)
    (β₁ : ↥W₁ →* M₁) (β₂ : ↥W₂ →* M₂) (hk₁ : ∀ u : ↥W₁, β₁ u = 1 ↔ (u : V) ∈ C)
    (hk₂ : ∀ u : ↥W₂, β₂ u = 1 ↔ (u : V) ∈ C) (hs₁ : Function.Surjective β₁)
    (hs₂ : Function.Surjective β₂) :
    ∃ Θ : V →* M₁ × M₂, Function.Surjective Θ ∧ (∀ v, Θ v = 1 ↔ v ∈ C) ∧
      ∀ (x : V) (hx : x ∈ W₁) (y : V) (hy : y ∈ W₂), Θ (x * y) = (β₁ ⟨x, hx⟩, β₂ ⟨y, hy⟩) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥W₁ × ↥W₂ →* V, ∀ p, Ψ p = (p.1 : V) * (p.2 : V) :=
    ⟨W₁.subtype.coprod W₂.subtype, fun p => rfl⟩
  have hΨs : Function.Surjective Ψ := by
    intro v
    have hv : v ∈ W₁ ⊔ W₂ := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hΨ _⟩
  have hker : Ψ.ker ≤ (β₁.prodMap β₂).ker := by
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, hΨ] at hxy
    have hxy' : (x : V) * (y : V) = 1 := hxy
    have hx : (x : V) ∈ C := by
      refine hinf ⟨x.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hxy']
      exact W₂.inv_mem y.2
    have hy : (y : V) ∈ C := by
      rw [eq_inv_of_mul_eq_one_right hxy']
      exact C.inv_mem hx
    rw [MonoidHom.mem_ker]
    exact Prod.ext ((hk₁ x).mpr hx) ((hk₂ y).mpr hy)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : V →* M₁ × M₂, ∀ p, Θ (Ψ p) = (β₁ p.1, β₂ p.2) :=
    ⟨MonoidHom.liftOfSurjective Ψ hΨs ⟨β₁.prodMap β₂, hker⟩, fun p =>
      MonoidHom.liftOfRightInverse_comp_apply Ψ (Function.surjInv hΨs)
        (Function.rightInverse_surjInv hΨs) ⟨β₁.prodMap β₂, hker⟩ p⟩
  have hform : ∀ (x : V) (hx : x ∈ W₁) (y : V) (hy : y ∈ W₂),
      Θ (x * y) = (β₁ ⟨x, hx⟩, β₂ ⟨y, hy⟩) := fun x hx y hy => by
    have := hΘ (⟨x, hx⟩, ⟨y, hy⟩)
    rw [hΨ] at this
    exact this
  refine ⟨Θ, ?_, ?_, hform⟩
  · rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := hs₁ a
    obtain ⟨y, rfl⟩ := hs₂ b
    exact ⟨(x : V) * (y : V), hform x x.2 y y.2⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨⟨x, y⟩, rfl⟩ := hΨs v
      rw [hΘ] at hv
      have hx : (x : V) ∈ C := (hk₁ x).mp (congrArg Prod.fst hv)
      have hy : (y : V) ∈ C := (hk₂ y).mp (congrArg Prod.snd hv)
      rw [hΨ]
      exact C.mul_mem hx hy
    · intro hv
      have h1 := hform v (hC₁ hv) 1 W₂.one_mem
      rw [mul_one] at h1
      rw [h1]
      refine Prod.ext ?_ ?_
      · exact (hk₁ ⟨v, hC₁ hv⟩).mpr hv
      · exact map_one β₂

end Alg

section Offender

variable {V : Type} [CommGroup V] [Finite V]

theorem card_le_of_isFFStarOffender {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    Nat.card V ≤ Nat.card ↥A * Nat.card ↥(fixV A) := by
  have h1 := hA.2.2.2 ⊥ bot_le
  rwa [B1.card_bot_mul_card_fixV] at h1

end Offender

end CFSG.Quasithin.S146zU.UC2
