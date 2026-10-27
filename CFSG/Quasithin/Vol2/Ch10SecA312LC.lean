module

public import CFSG.Quasithin.Vol2.Ch10SecA312LB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.Dihedral.Glauberman.DicksonMaxSubfield

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312LF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem dvd_of_isG2
    {G : Type} [Group G] [Finite G] {L P : Subgroup G} {f : ℕ} (hL : IsG2 2 f ↥L)
    (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ} (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) :
    f ∣ n := by
  obtain ⟨hf2, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨hQ, hQtop, hn'⟩ := transport e hP hPL hn
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  refine dvd_of_leviField hU₀ G2_residualOvergroupsAt (fun j => ?_) hQ hQtop hn'
  obtain ⟨g, hg, hker⟩ := exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hf2 (g2Index j)
  exact Or.inr (Or.inl ⟨K, inferInstance, inferInstance, inferInstance, f, hK, dvd_rfl, hf2, g,
    hg, hker⟩)

section D4

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem pow_apply_eq {σ : K ≃+* K} {q : ℕ} (hσ : ∀ c, σ c = c ^ q) (d : ℕ) (c : K) :
    (σ.toRingHom ^ d) c = c ^ q ^ d := by
  rw [RingHom.coe_pow]
  induction d generalizing c with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply, ih]
    change (σ c) ^ q ^ d = c ^ q ^ (d + 1)
    rw [hσ, ← pow_mul, pow_succ, mul_comm]

theorem orbit_card_dvd_three (a : Fin TwistTag.D4.foldedTag.rank) :
    (TwistTag.D4.orbit a).card ∣ 3 := by
  revert a
  decide

theorem dvd_card_orbitField [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (a : Fin TwistTag.D4.foldedTag.rank) {m : ℕ}
    (hm : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 2 ^ m) : f ∣ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3 : (TwistTag.D4.orbit a).card ∣ 3 := orbit_card_dvd_three a
  have hd0 : (TwistTag.D4.orbit a).card ≠ 0 := fun h => by
    rw [h] at hd3
    omega
  have heq : orbitField TwistTag.D4 K σ.toRingHom a =
      CFSG.Glauberman.Dickson.MaxSubfield.fixField K 2 (f * (TwistTag.D4.orbit a).card) := by
    ext c
    rw [mem_orbitField, CFSG.Glauberman.Dickson.MaxSubfield.mem_fixField, pow_apply_eq hσ,
      ← pow_mul]
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hdvd : f * (TwistTag.D4.orbit a).card ∣ 3 * f := by
    rw [mul_comm 3 f]
    exact Nat.mul_dvd_mul_left f hd3
  have hcard := CFSG.Glauberman.Dickson.MaxSubfield.card_fixField hK3 hdvd
    (Nat.mul_ne_zero (by omega) hd0)
  rw [← heq, hm] at hcard
  exact ⟨_, Nat.pow_right_injective (le_refl 2) hcard⟩

theorem leviField_D4
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (a : Fin TwistTag.D4.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)) :
    LeviField f ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 2 ^ m := by
    have : Fintype ↥(orbitField TwistTag.D4 K σ.toRingHom a) := Fintype.ofFinite _
    obtain ⟨n, -, hn⟩ := FiniteField.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hfm := dvd_card_orbitField hf σ hK hσ a hm
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hpos : 1 < Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) := Finite.one_lt_card
    have hm1 : m = 1 := by
      rcases Nat.lt_or_ge m 1 with h0 | h1
      · have h00 : m = 0 := by omega
        rw [h00, pow_zero] at hm
        omega
      · omega
    subst hm1
    have hf1 : f = 1 := Nat.dvd_one.mp hfm
    rcases fixed_leviData σ a hU with h | ⟨K', _, _, _, m', hK', hm', g, hg, hker⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨K', inferInstance, inferInstance, inferInstance, m', hK',
        hf1 ▸ one_dvd m', hm', g, hg, hker⟩)
  · have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hm]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    obtain ⟨g, hg, hker⟩ := exists_levi_hom_fixed σ a hU hL4
    exact Or.inr (Or.inl ⟨↥(orbitField TwistTag.D4 K σ.toRingHom a), inferInstance,
      inferInstance, inferInstance, m, hm, hfm, hm2, g, hg, hker⟩)

end D4

theorem dvd_of_is3D4
    {G : Type} [Group G] [Finite G] {L P : Subgroup G} {f : ℕ} (hL : Is3D4 2 f ↥L)
    (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ} (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) :
    f ∣ n := by
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hL
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨hQ, hQtop, hn'⟩ := transport e hP hPL hn
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  exact dvd_of_leviField (isSylowTwoOf_subgroupOf_top hUsyl) (triality_residualOvergroupsAt σ)
    (fun j => leviField_D4 hf σ hK hσ (d4Index j) hUsyl.2.1) hQ hQtop hn'

end CFSG.Quasithin.Vol2.Ch10.A312LF
