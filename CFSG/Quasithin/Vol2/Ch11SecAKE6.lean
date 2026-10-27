module

public import CFSG.Quasithin.Vol2.Ch11SecAKE5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem not_three_dvd_suzuki (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  intro h
  generalize 2 ^ (2 * a + 1) = q at hq hq2 h
  generalize hQ : q ^ 2 = Q at hq2 h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2 <;> omega
  · omega


theorem not_isPSL_tits
    {X : Type} [Group X] [Finite X]
    (hX : IsTits X) {P : Subgroup X} (hP : IsMaxParabolic2 ⊤ P) {m : ℕ} :
    ¬ IsPSL 2 2 m (ModO2 (perfectCore P)) := by
  obtain ⟨⟨-, S, hS, hNP⟩, hPtop, -⟩ := hP
  have hSP : S ≤ P := fun x hx => hNP ⟨Subgroup.mem_top x, Subgroup.le_normalizer hx⟩
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice X hX S hS
  have hs : Group.IsSolvable ↥P := by
    rcases hlat P hSP with rfl | rfl | rfl | rfl
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := hS.2.1.isNilpotent
      infer_instance
    · exact hHs
    · exact hNs
    · exact absurd rfl hPtop
  exact not_isPSL_modO2_bot ((isSolvable_iff_perfectCore_eq_bot P).mp hs)


theorem param_G2 {X : Type} [Group X] [Finite X] {f : ℕ} (hX : IsG2 2 f X) {P : Subgroup X}
    (hP : IsMaxParabolic2 ⊤ P) {m : ℕ} (hm : IsPSL 2 2 m (ModO2 (perfectCore P))) : m = f := by
  obtain ⟨hf, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨hP', hm'⟩ := maxParabolic_map e hP hm
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  refine param_of_residual (R := fun n => n = f) G2_residualOvergroupsAt hU₀ (fun j => ?_) hP'
    hm'
  obtain ⟨g, hg, hker⟩ :=
    Vol2Native.A312L.exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hf (g2Index j)
  exact LeviParam.of_sl2 hK hf rfl g hg hker

theorem param_F4 {X : Type} [Group X] [Finite X] {f : ℕ} (hX : Is2F4 f X) {P : Subgroup X}
    (hP : IsMaxParabolic2 ⊤ P) {m : ℕ} (hm : IsPSL 2 2 m (ModO2 (perfectCore P))) : m = f := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  obtain ⟨hP', hm'⟩ := maxParabolic_map e hP hm
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := hUsyl.2.1
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  refine param_of_residual (R := fun n => n = 2 * a + 1) (large_Ree_residualOvergroupsAt hK)
    (isSylowTwoOf_subgroupOf_top hUsyl) (fun j => ?_) hP' hm'
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (f4Index j) with hj | hj
  · have hs := isSimpleGroup_rankOneGroupOne ha hK
    have := hs.1
    obtain ⟨g, hg, hk⟩ := Vol2Native.A312L.ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq) hs.2
    let e' : ↥(rankOneGroupOne K a) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (rankOneEquivSL K a hK).symm
    refine LeviParam.of_sl2 hK (by omega) rfl (e'.toMonoidHom.comp g) (e'.surjective.comp hg) ?_
    have hkerEq : (e'.toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact MulEquiv.map_eq_one_iff e'
    rw [hkerEq]
    exact hk
  · have hs := isSimpleGroup_rankOneGroupTwo ha hK
    have := hs.1
    obtain ⟨g, hg, hk⟩ := Vol2Native.A312L.ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq) hs.2
    refine LeviParam.of_three hs.2 ?_ g hg hk
    rw [Nat.card_congr (rankOneEquivSuzuki K a ha hK).toEquiv, suzuki_order hK]
    exact not_three_dvd_suzuki a

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
