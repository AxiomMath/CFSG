module

public import CFSG.Quasithin.Background.SimsE2Defs
public import CFSG.Quasithin.Vol2.E2Eleven
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.SimsE2.E213M

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

theorem exists_antiSp_of_isSp4Full {X : Type} [Group X] {k : ℕ} (h : IsSp4Full k X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ k ∧
      Nonempty (X ≃* antiSp K) := by
  rcases h with ⟨-, K, _, _, hK, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := by
      have : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    exact ⟨K, inferInstance, inferInstance, inferInstance, hK,
      ⟨(e.trans (CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := K) (n := 2) (by norm_num))).trans
        (antiSpEquiv K).symm⟩⟩
  · obtain ⟨σ⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
      (k := ZMod 2) (ZMod.card 2)
    exact ⟨ZMod 2, inferInstance, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
      ⟨(e.trans σ.symm).trans (antiSpEquiv (ZMod 2)).symm⟩⟩

theorem sq_add_one_dvd_card {X : Type} [Group X] {k : ℕ} (h : IsSp4Full k X) :
    (2 ^ k) ^ 2 + 1 ∣ Nat.card X := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_antiSp_of_isSp4Full h
  rw [Nat.card_congr e.toEquiv, card_antiSp hK]
  have h1 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ (2 ^ k) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  have h4 : (2 ^ k) ^ 4 - 1 = ((2 ^ k) ^ 2 + 1) * ((2 ^ k) ^ 2 - 1) := by
    zify [h1, h2]
    ring
  rw [h4]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.intro _ rfl) _) _

theorem card_le_of_le_centralizer {X : Type} [Group X] [Finite X] {k : ℕ} (h : IsSp4Full k X)
    {S W : Subgroup X} (hS : IsSylowTwoOf S ⊤) (hWS : W ≤ S)
    (hWC : W ≤ Subgroup.centralizer (S : Set X)) : Nat.card W ≤ 2 ^ (2 * k) := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_antiSp_of_isSp4Full h
  have : Finite (antiSp K) := Finite.of_equiv X e.toEquiv
  have hS' := E2.isSylowTwoOf_map_equiv e hS
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj
    (card_and_isSylowTwoOf_antiUnipotent (K := K)).2 hS'
  have hle : B6.conjSub c⁻¹ (W.map (e : X →* antiSp K)) ≤ antiUnipotentCenter K := by
    intro x hx
    rw [B6.mem_conjSub, inv_inv] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have hxe : x = c⁻¹ * e w * c := by
      rw [show (e : X →* antiSp K) w = e w from rfl] at hwx
      rw [hwx]
      group
    have hwU : e w ∈ B6.conjSub c (antiUnipotent K) := hc ▸ ⟨w, hWS hw, rfl⟩
    rw [B6.mem_conjSub] at hwU
    rw [mem_antiUnipotentCenter_iff_central, hxe]
    refine ⟨hwU, fun u hu => ?_⟩
    have hcu : c * u * c⁻¹ ∈ S.map (e : X →* antiSp K) := by
      rw [hc, B6.mem_conjSub]
      simpa [mul_assoc] using hu
    obtain ⟨s, hs, hse⟩ := hcu
    have hsw : s * w = w * s := Subgroup.mem_centralizer_iff.1 (hWC hw) s hs
    have h1 : (c * u * c⁻¹) * e w = e w * (c * u * c⁻¹) := by
      rw [← hse, show (e : X →* antiSp K) s = e s from rfl, ← map_mul, ← map_mul, hsw]
    calc c⁻¹ * e w * c * u = c⁻¹ * (e w * (c * u * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * u * c⁻¹) * e w) * c := by rw [h1]
      _ = u * (c⁻¹ * e w * c) := by group
  have hcard : Nat.card (B6.conjSub c⁻¹ (W.map (e : X →* antiSp K))) = Nat.card W := by
    rw [show B6.conjSub c⁻¹ (W.map (e : X →* antiSp K)) =
        (W.map (e : X →* antiSp K)).map (MulAut.conj c⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective,
      Subgroup.card_map_of_injective e.injective]
  calc Nat.card W = Nat.card (B6.conjSub c⁻¹ (W.map (e : X →* antiSp K))) := hcard.symm
    _ ≤ Nat.card (antiUnipotentCenter K) := Subgroup.card_le_of_le hle
    _ = Nat.card K ^ 2 := (card_radicals (K := K)).2.2.2
    _ = 2 ^ (2 * k) := by rw [hK, ← pow_mul, mul_comm]

end CFSG.Quasithin.SimsE2.E213M
