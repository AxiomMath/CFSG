module

public import CFSG.GH74.GLS.Stage4.HexModelD4
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2CardU
import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.H13.F431.D4q.Hex

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.Open


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσq

theorem exists_d4Model_equiv :
    Nonempty ((twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hZ := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    (σ := σ.toRingHom) hq hK hσq
  have hm : (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← commutator_twistedFixedGroup_eq_map σ.toRingHom hq hK hσq]
    exact (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hf K hK σ.toRingHom
      hσq).2.2.1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot (G := twistedGroup σ.toRingHom))).trans
    ((Subgroup.equivMapOfInjective (twistedGroup σ.toRingHom) (adjointGroup d4 K).subtype
        Subtype.val_injective).trans (MulEquiv.subgroupCongr hm))⟩

theorem d4ModelSystem_isSylow (hq : 2 ≤ 2 ^ f) :
    IsSylowTwoOf (d4ModelSystem σ.toRingHom hq hK hσq).U ⊤ := by
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card hK hσq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eC⟩ := exists_d4Model_equiv σ hf hK hσq
  have hU : Nat.card (d4ModelSystem σ.toRingHom hq hK hσq).U = (2 ^ f) ^ 12 := by
    have h := (hexQuotRGD2 (twistedData σ.toRingHom hσ3)).card_U
    rw [show (d4ModelSystem σ.toRingHom hq hK hσq).U =
      (posUnipotent (g2Shape (twistedX σ.toRingHom))).map (hexProj ↥(twistedGroup σ.toRingHom))
        from rfl, h]
    have hr : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ((hexGroup (twistedX σ.toRingHom) i).map
        (hexProj ↥(twistedGroup σ.toRingHom))) = if i % 2 = 1 then (2 ^ f) ^ 3 else 2 ^ f :=
      fun i h1 h6 => card_d4ModelSystem_root σ.toRingHom hq hK hσq h1 h6
    have hl : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide
    rw [hl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    rw [hr 1 (by norm_num) (by norm_num), hr 2 (by norm_num) (by norm_num),
      hr 3 (by norm_num) (by norm_num), hr 4 (by norm_num) (by norm_num),
      hr 5 (by norm_num) (by norm_num), hr 6 (by norm_num) (by norm_num)]
    norm_num
    ring
  have hp : IsPGroup 2 ↥(d4ModelSystem σ.toRingHom hq hK hσq).U :=
    IsPGroup.of_card (n := f * 12) (by rw [hU, ← pow_mul])
  have hX : Nat.card (twistedGroup σ.toRingHom ⧸ Subgroup.center (twistedGroup σ.toRingHom)) =
      (2 ^ f) ^ 12 *
        (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1))) := by
    rw [Nat.card_congr eC.toEquiv]
    have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by rw [pow_one]; exact hσq c
    have h := (triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1
      (Or.inl rfl) σ.toRingHom hσ').1
    rw [h]
    ring
  have hidx : (d4ModelSystem σ.toRingHom hq hK hσq).U.index =
      ((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1)) := by
    have h := Subgroup.card_mul_index (d4ModelSystem σ.toRingHom hq hK hσq).U
    rw [hU, hX] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  refine ⟨le_top, hp, ?_⟩
  change ¬ 2 ∣ (d4ModelSystem σ.toRingHom hq hK hσq).U.relIndex ⊤
  rw [Subgroup.relIndex_top_right, hidx]
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hq6 : 1 ≤ (2 ^ f) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have e2 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow h2 (by norm_num)
  have e6 : 2 ∣ (2 ^ f) ^ 6 := dvd_pow h2 (by norm_num)
  have e8 : 2 ∣ (2 ^ f) ^ 8 := dvd_pow h2 (by norm_num)
  have e4 : 2 ∣ (2 ^ f) ^ 4 := dvd_pow h2 (by norm_num)
  have o2 : ¬ 2 ∣ (2 ^ f) ^ 2 - 1 := by omega
  have o6 : ¬ 2 ∣ (2 ^ f) ^ 6 - 1 := by omega
  have o8 : ¬ 2 ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 := by omega
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
  · exact o2 h
  · rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact o6 h
    · exact o8 h

end CFSG.Quasithin.H13.F431.D4q.Hex
