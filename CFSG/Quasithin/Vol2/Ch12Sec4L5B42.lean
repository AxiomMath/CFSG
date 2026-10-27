module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Aux
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem card_eq_of_realizes {V : Type} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
    (h : D.Realizes H ⊤ ⊥) : Nat.card V = Nat.card D.Mod := by
  obtain ⟨π, hπ⟩ := h
  have h1 := G64.RealizesVia.card_eq hπ
  rwa [Subgroup.card_top, Subgroup.card_bot, mul_one] at h1

theorem card_mod_extSq (K : Type) [Field K] [Finite K] (d : ℕ) :
    Nat.card (FFModel.extSq K d).Mod = Nat.card K ^ d.choose 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.extSq K d).ker.subgroupOf (FFModel.extSq K d).sec)
  have h1 : Nat.card ↥((FFModel.extSq K d).ker.subgroupOf (FFModel.extSq K d).sec) = 1 := by
    rw [Subgroup.card_eq_one]
    exact Subgroup.bot_subgroupOf _
  rw [h1, mul_one] at h
  rw [← h]
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (⋀[K]^2 (Fin d → K)))) = _
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
    Module.natCard_eq_pow_finrank (K := K), exteriorPower.finrank_eq, Module.finrank_fin_fun]

theorem card_zornO0 (K : Type) [Field K] [Finite K] :
    Nat.card ↥(zornO0 K) = Nat.card K ^ 7 := by
  let e : ↥(zornO0 K) ≃ K × (Fin 3 → K) × (Fin 3 → K) :=
    { toFun := fun x => ((Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1,
        (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.1,
        (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.2.1)
      invFun := fun y => ⟨Multiplicative.ofAdd (y.1, y.2.1, y.2.2, -y.1), by
        show y.1 + -y.1 = 0
        exact add_neg_cancel _⟩
      left_inv := fun x => by
        have hx : (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1 +
            (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.2.2 = 0 := x.2
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd]
        ext <;> simp [eq_neg_of_add_eq_zero_right hx]
      right_inv := fun y => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

theorem card_zornR (K : Type) [Field K] : Nat.card ↥(zornR K) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : K => (⟨Multiplicative.ofAdd (c, 0, 0, c), ⟨c, rfl⟩⟩ : ↥(zornR K))) ⟨?_, ?_⟩)).symm
  · intro c d hcd
    have h1 := congrArg (fun x : ↥(zornR K) => (Multiplicative.toAdd
      (x : Multiplicative (quasithinZorn K))).1) hcd
    simpa using h1
  · rintro ⟨x, c, hc⟩
    refine ⟨c, Subtype.ext ?_⟩
    show Multiplicative.ofAdd (c, 0, 0, c) = x
    rw [← hc]
    rfl

theorem card_mod_zornQ {K : Type} [Field K] [Finite K] [CharP K 2]
    (Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)) :
    Nat.card (FFModel.zornQ Γ).Mod = Nat.card K ^ 6 := by
  have hRO : zornR K ≤ zornO0 K := by
    rintro x ⟨c, hc⟩
    show (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2.2.2 = 0
    rw [hc]
    exact CharTwo.add_self_eq_zero c
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((zornR K).subgroupOf (zornO0 K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRO).toEquiv, card_zornR, card_zornO0] at h
  have hpos : 0 < Nat.card K := Nat.card_pos
  show Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) = _
  have h2 : Nat.card K ^ 7 = Nat.card K ^ 6 * Nat.card K := by ring
  rw [h2] at h
  exact (Nat.eq_of_mul_eq_mul_right hpos h).symm

theorem eq_of_two_pow_eq {a b : ℕ} (h : 2 ^ a = 2 ^ b) : a = b :=
  Nat.pow_right_injective (le_refl 2) h

theorem b42Case11_of_card {V : Type} [CommGroup V] [Finite V] (hcard : Nat.card V = 2 ^ 10)
    {X L A : Subgroup (MulAut V)} (hL : Nat.card ↥L = 9999360) (h : B42Conclusion X L A) :
    B42Case11 X L A := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  ·
    exfalso
    obtain ⟨-, ⟨m, hm⟩, -, -⟩ := h1
    obtain ⟨K', _, _, hK', ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hm
    obtain ⟨K, _, _, hK, hR⟩ := hm
    have hV := card_eq_of_realizes hR
    rw [card_mod_nat, hK, Fintype.card_fin, ← pow_mul, hcard] at hV
    have hm5 : m = 5 := by have := eq_of_two_pow_eq hV; omega
    subst hm5
    have hLc : Nat.card ↥L = Nat.card K' * (Nat.card K' ^ 2 - 1) := by
      rw [← Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K').toEquiv]
      exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K'
    rw [hK', hL] at hLc
    norm_num at hLc
  ·
    exfalso
    obtain ⟨-, ⟨m, K, _, _, hK, hR⟩, -⟩ := h2
    have hV := card_eq_of_realizes hR
    rw [card_mod_nat, hK, Fintype.card_fin, ← pow_mul, hcard] at hV
    have := eq_of_two_pow_eq hV
    omega
  ·
    exfalso
    obtain ⟨⟨m, ⟨K, _, _, hK, hR⟩, -⟩, -⟩ := h3
    have hV := card_eq_of_realizes hR
    rw [card_mod_nat, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul, hcard] at hV
    have := eq_of_two_pow_eq hV
    omega
  ·
    exfalso
    obtain ⟨⟨m, ⟨K, _, _, hK, hR⟩, -, -⟩, -⟩ := h4
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
    have hV := card_eq_of_realizes hR
    rw [card_mod_zornQ, hK, ← pow_mul, hcard] at hV
    have := eq_of_two_pow_eq hV
    omega
  ·
    exfalso
    obtain ⟨⟨m, hm, π, hπ, -⟩, -⟩ := h5
    have hV := card_eq_of_realizes (D := FFModel.symDn m) ⟨π, hπ⟩
    have hm1 : 1 ≤ m := by rcases hm with rfl | rfl <;> norm_num
    rw [G64.card_symDn_mod hm1, hcard] at hV
    rcases hm with rfl | rfl <;> norm_num [Nat.even_iff] at hV
  ·
    exfalso
    obtain ⟨-, hR, -⟩ := h6
    have hV := card_eq_of_realizes hR
    rw [card_mod_altDn (by decide) (by norm_num), hcard] at hV
    norm_num at hV
  ·
    exfalso
    obtain ⟨-, -, -, h4, -⟩ := h7
    rw [hcard] at h4
    norm_num at h4
  ·
    exfalso
    obtain ⟨-, h6, -⟩ := h8
    rw [hcard] at h6
    norm_num at h6
  ·
    exfalso
    obtain ⟨-, m, hm, hnat, -⟩ := h9
    have hV := G64.BinaryNaturalSL.card_eq hnat
    rw [hcard] at hV
    rcases hm with rfl | rfl <;> norm_num at hV
  ·
    exfalso
    obtain ⟨hR, -⟩ := h10
    have hV := card_eq_of_realizes hR
    rw [card_mod_extSq, Nat.card_zmod, hcard] at hV
    norm_num [Nat.choose] at hV
  · exact h11

end CFSG.Quasithin.H13
