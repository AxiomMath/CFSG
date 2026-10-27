module

public import CFSG.RankThree.PartOne.S11c.HeisenbergSylow
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralSylow
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.RankThree.PartOne.HNRed

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.TrialityCover CFSG.Assembly.LowTwoRank CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD

theorem not_five_dvd_ordTrialityD4 {q : ℕ} (hq5 : ¬ 5 ∣ q) (hq : q ^ 2 % 5 = 4) :
    ¬ 5 ∣ CFSG.Open.ordTrialityD4 q := by
  have hpos : 1 ≤ q := Nat.pos_of_ne_zero (by rintro rfl; exact hq5 (dvd_zero 5))
  have h3 : q ^ 6 % 5 = 4 := by
    rw [show q ^ 6 = (q ^ 2) ^ 3 by ring, Nat.pow_mod, hq]
  have h4 : q ^ 4 % 5 = 1 := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, Nat.pow_mod, hq]
  have h8 : q ^ 8 % 5 = 1 := by
    rw [show q ^ 8 = (q ^ 4) ^ 2 by ring, Nat.pow_mod, h4]
  unfold CFSG.Open.ordTrialityD4
  intro h
  have hp : Nat.Prime 5 := Nat.prime_five
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hq5 (hp.dvd_of_dvd_pow h)
      · omega
    · have : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hpos
      omega
  · have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hpos
    omega

theorem sixteen_pow_mod_five (m : ℕ) : 16 ^ m % 5 = 1 := by
  rw [Nat.pow_mod]
  norm_num

section Even

variable {Kf : Type} [Field Kf] [Finite Kf] {σ : Kf ≃+* Kf}

omit [Finite Kf] in
theorem triality_split_fiveSubgroupsCommute
    {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card Kf = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (h5 : 5 ∣ 2 ^ f - 1) :
    FiveSubgroupsCommute (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom) := by
  classical
  obtain ⟨hsyl, ⟨et, -⟩, -, -⟩ := triality_split_prime_toral_Sylow Nat.prime_two hf Kf hK σ hσ
    Nat.prime_five (by norm_num) h5
  let C := graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom
  let H : Subgroup C := (graphFixedRootTorus TwistTag.D4 Kf σ.toRingHom).subgroupOf C
  have hHab : ∀ x y : ↥(graphFixedRootTorus TwistTag.D4 Kf σ.toRingHom), x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := et.surjective x
    obtain ⟨b, rfl⟩ := et.surjective y
    rw [← map_mul, ← map_mul, mul_comm a b]
  refine fiveSubgroupsCommute_of_conj_abelian H ?_ fun P hP => ?_
  · intro x hx y hy
    have h := hHab ⟨(x : ModGL TwistTag.D4.tag Kf), hx⟩ ⟨(y : ModGL TwistTag.D4.tag Kf), hy⟩
    have h2 : (x : ModGL TwistTag.D4.tag Kf) * (y : ModGL TwistTag.D4.tag Kf) =
        (y : ModGL TwistTag.D4.tag Kf) * (x : ModGL TwistTag.D4.tag Kf) := congrArg Subtype.val h
    exact Subtype.ext h2
  · obtain ⟨g, hg⟩ := hsyl P hP
    exact ⟨g, fun x hx => hg ⟨x, hx, rfl⟩⟩

theorem triality_qplus_fiveSubgroupsCommute
    [CharP Kf 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card Kf = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (h5 : (5 : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) + 1) :
    FiveSubgroupsCommute (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := AlgebraicClosure Kf
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap Kf L).injective 2
  obtain ⟨g0, -, -, -, hconj⟩ := d4Q_frame (ℓ := 2) hf Kf hK σ hσ Nat.prime_five (by norm_num) h5 L
  let Hc : Subgroup (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom) :=
    (torusGroup TwistTag.D4.tag L).comap
      ((MulAut.conj g0⁻¹).toMonoidHom.comp (triEmb Kf σ L))
  refine fiveSubgroupsCommute_of_conj_abelian Hc ?_ fun P hP => ?_
  · intro x hx y hy
    have hc : (MulAut.conj g0⁻¹) (triEmb Kf σ L x) * (MulAut.conj g0⁻¹) (triEmb Kf σ L y) =
        (MulAut.conj g0⁻¹) (triEmb Kf σ L y) * (MulAut.conj g0⁻¹) (triEmb Kf σ L x) :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hx)
        (torusGroup_le_diagonalGroup hy)
    have hc' : (MulAut.conj g0⁻¹) (triEmb Kf σ L (x * y)) =
        (MulAut.conj g0⁻¹) (triEmb Kf σ L (y * x)) := by
      rw [map_mul, map_mul, map_mul, map_mul]
      exact hc
    exact triEmb_injective ((MulAut.conj g0⁻¹).injective hc')
  · obtain ⟨c, hc⟩ := hconj P hP
    refine ⟨c, fun y hy => ?_⟩
    have h1 := (mem_twistedTorusOf.1 (hc y hy)).1
    show (MulAut.conj g0⁻¹) (triEmb Kf σ L (c * y * c⁻¹)) ∈ torusGroup TwistTag.D4.tag L
    rw [MulAut.conj_apply, inv_inv]
    exact h1

end Even

theorem triality_five_fixed_absurd
    {T : Type} [Group T] (K : Subgroup T) (hK : StatedClassicalModel K .PSU 3 5 1) {f : ℕ}
    (hf : 1 ≤ f) (h : TwistedChevalleyModel T .D4 (2 ^ f)) : False := by
  classical
  obtain ⟨Kf, _, _, _, σ, hσ3, hσ, hKc, hk, ⟨e⟩⟩ := triality_model hf h
  have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hf h
  have hdvd : (126000 : ℕ) ∣ Nat.card T := by
    have h1 := Subgroup.card_subgroup_dvd_card K
    rwa [(CFSG.RankThree.Classical.unitary_three_five_model K hK).1] at h1
  let ι : ↥K →* graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom := e.toMonoidHom.comp K.subtype
  have hι : Function.Injective ι := e.injective.comp K.subtype_injective
  have h16 : ∀ m, 16 ^ m % 5 = 1 := sixteen_pow_mod_five
  rcases Nat.even_or_odd f with hev | hodd
  · have hm : f % 4 = 0 ∨ f % 4 = 2 := by
      obtain ⟨m, hm⟩ := hev
      omega
    rcases hm with hm | hm
    · obtain ⟨m, rfl⟩ : ∃ m, f = 4 * m := ⟨f / 4, by omega⟩
      have hpow : 2 ^ (4 * m) = 16 ^ m := by rw [pow_mul]; norm_num
      have h5 : 5 ∣ 2 ^ (4 * m) - 1 := by
        rw [hpow]
        have := h16 m
        have h1 : 1 ≤ 16 ^ m := Nat.one_le_pow _ _ (by norm_num)
        omega
      exact no_unitary_three_five_of_fiveSubgroupsCommute
        (triality_split_fiveSubgroupsCommute hf hKc hσ h5) hK ι hι
    · obtain ⟨m, rfl⟩ : ∃ m, f = 4 * m + 2 := ⟨f / 4, by omega⟩
      have hpow : 2 ^ (4 * m + 2) = 4 * 16 ^ m := by rw [pow_add, pow_mul]; norm_num; ring
      have h5 : (5 : ℤ) ∣ ((2 ^ (4 * m + 2) : ℕ) : ℤ) + 1 := by
        have h6 : 5 ∣ 2 ^ (4 * m + 2) + 1 := by
          rw [hpow]
          have := h16 m
          omega
        exact_mod_cast h6
      exact no_unitary_three_five_of_fiveSubgroupsCommute
        (triality_qplus_fiveSubgroupsCommute hf hKc hσ h5) hK ι hι
  · have hq5 : ¬ 5 ∣ 2 ^ f := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
      omega
    have hq : (2 ^ f) ^ 2 % 5 = 4 := by
      obtain ⟨m, rfl⟩ := hodd
      have : (2 ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
        rw [← pow_mul, show (2 * m + 1) * 2 = 2 + 4 * m by ring, pow_add, pow_mul]
        norm_num
      rw [this]
      have := h16 m
      omega
    rw [hcard] at hdvd
    exact not_five_dvd_ordTrialityD4 hq5 hq (Nat.dvd_trans (by norm_num : 5 ∣ 126000) hdvd)

end CFSG.RankThree.PartOne.HNRed
