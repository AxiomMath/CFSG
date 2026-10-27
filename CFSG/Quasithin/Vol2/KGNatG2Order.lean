module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Two
public import CFSG.Quasithin.Background.JonesParshallG2Perfect
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall Matrix
open CFSG.QuasithinUnique.Bridge.Alt57Model

variable {K : Type} [Field K]

theorem charP_two_of_card {n : ℕ} [Finite K] (hn : n ≠ 0) (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have h : Nat.card K • (1 : K) = 0 := card_nsmul_eq_zero'
  rw [hK, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ((pow_eq_zero_iff hn).mp h)

theorem exists_ne_zero_ne_one [Finite K] (h : 2 < Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx]
  have h1 := Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

section CharTwo

variable [CharP K 2]

theorem eq_of_singular {x : quasithinZorn K} (htr : cayleyTr x = 0) (hN : cayleyNorm x = 0) :
    x.2.2.2 = x.1 ∧ x.1 ^ 2 = x.2.1 ⬝ᵥ x.2.2.1 := by
  obtain ⟨r, u, v, s⟩ := x
  have hs : s = r := by
    have h : r + s = 0 := htr
    rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
  refine ⟨hs, ?_⟩
  have h : r * s + ∑ i, u i * v i = 0 := hN
  rw [hs] at h
  rw [sq, eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  rfl

variable [Finite K]

theorem mem_singular_sqrt (p : (Fin 3 → K) × (Fin 3 → K)) :
    (((frobeniusEquiv K 2).symm (p.1 ⬝ᵥ p.2), p.1, p.2, (frobeniusEquiv K 2).symm (p.1 ⬝ᵥ p.2)) :
      quasithinZorn K) ∈ {x : quasithinZorn K | cayleyTr x = 0 ∧ cayleyNorm x = 0} := by
  set r := (frobeniusEquiv K 2).symm (p.1 ⬝ᵥ p.2) with hr
  have hr2 : r * r = p.1 ⬝ᵥ p.2 := by
    rw [← sq, ← frobenius_def, ← frobeniusEquiv_apply, hr, RingEquiv.apply_symm_apply]
  refine ⟨?_, ?_⟩
  · show r + r = 0
    exact CharTwo.add_self_eq_zero r
  · show r * r + ∑ i, p.1 i * p.2 i = 0
    rw [hr2]
    exact CharTwo.add_self_eq_zero _

theorem ncard_singular :
    {x : quasithinZorn K | cayleyTr x = 0 ∧ cayleyNorm x = 0}.ncard = Nat.card K ^ 6 := by
  set Y : Set (quasithinZorn K) := {x | cayleyTr x = 0 ∧ cayleyNorm x = 0}
  let e : Y ≃ (Fin 3 → K) × (Fin 3 → K) :=
    { toFun := fun x => (x.1.2.1, x.1.2.2.1)
      invFun := fun p => ⟨_, mem_singular_sqrt p⟩
      left_inv := fun x => by
        obtain ⟨⟨r, u, v, s⟩, htr, hN⟩ := x
        obtain ⟨hs, hr⟩ := eq_of_singular htr hN
        simp only at hs hr
        have hr' : (frobeniusEquiv K 2).symm (u ⬝ᵥ v) = r := by
          rw [RingEquiv.symm_apply_eq, frobeniusEquiv_apply, frobenius_def, hr]
        apply Subtype.ext
        simp only [hr', hs]
      right_inv := fun p => rfl }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

theorem card_nullPts : (nullPts K).ncard = Nat.card K ^ 6 - 1 := by
  have h0 : (0 : quasithinZorn K) ∈ {x : quasithinZorn K | cayleyTr x = 0 ∧ cayleyNorm x = 0} :=
    ⟨by simp [cayleyTr], by simp [cayleyNorm]⟩
  have hX : nullPts K = {x : quasithinZorn K | cayleyTr x = 0 ∧ cayleyNorm x = 0} \ {0} := by
    ext x
    simp only [nullPts, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [hX, Set.ncard_sdiff_singleton_of_mem h0, ncard_singular]

omit [Finite K] in
theorem card_stabilizer_zU0 :
    Nat.card (MulAction.stabilizer ↥(cayleyGroup K) (zU0 K)) =
      Nat.card K ^ 3 * Nat.card ↥(S0 K) := by
  let Φ : K × K × K × ↥(S0 K) → ↥(MulAction.stabilizer ↥(cayleyGroup K) (zU0 K)) :=
    fun p => ⟨stabElt p, MulAction.mem_stabilizer_iff.2 (stabElt_zU0 p)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro p q h
      exact stabElt_injective (congrArg Subtype.val h)
    · rintro ⟨g, hg⟩
      have hg' : cgE g (zU0 K) = zU0 K := MulAction.mem_stabilizer_iff.1 hg
      obtain ⟨α, β, γ, A, hA, rfl⟩ := eq_uW_mul_g2A hg'
      exact ⟨(α, β, γ, ⟨A, hA⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

omit [CharP K 2] [Finite K] in
theorem orbit_e0_eq : MulAction.orbit (SL3 K) (e0 : Fin 3 → K) = {v | v ≠ 0} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩ h0
    change g • (e0 : Fin 3 → K) = 0 at h0
    have he : (e0 : Fin 3 → K) = 0 := by
      rw [← inv_smul_smul g (e0 : Fin 3 → K), h0, smul_zero]
    exact one_ne_zero ((e0_zero (F := K)).symm.trans (congrFun he 0))
  · exact mulVec3_e0_mem_orbit v

omit [CharP K 2] in
theorem card_S0 : Nat.card ↥(S0 K) = Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) := by
  have h1 := Subgroup.card_mul_index (S0 K)
  have hset : ({v | v ≠ 0} : Set (Fin 3 → K)) = Set.univ \ {0} := by
    ext v
    simp
  rw [MulAction.index_stabilizer, orbit_e0_eq, hset,
    Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, Nat.card_fun,
    Nat.card_fin, CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num)] at h1
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq3 : 1 < Nat.card K ^ 3 := Nat.one_lt_pow (by norm_num) hq
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card K ^ 3 - 1 by omega)
  rw [h1]
  norm_num
  ring

theorem card_cayleyGroup :
    Nat.card ↥(cayleyGroup K) =
      Nat.card K ^ 6 * ((Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1)) := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(cayleyGroup K) (zU0 K))
  rw [MulAction.index_stabilizer, orbit_zU0_eq, card_nullPts, card_stabilizer_zU0,
    card_S0] at h1
  rw [← h1]
  ring

end CharTwo

theorem factG2DerivedOrder_holds : Ch11.SecA.FactG2DerivedOrder := by
  intro K _ _ n hn hK
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K) (by rw [hK]; omega)
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    cayley_commutator_eq hc0 hc1, card_cayleyGroup, hK]

end CFSG.Quasithin.Vol2.KGNat
