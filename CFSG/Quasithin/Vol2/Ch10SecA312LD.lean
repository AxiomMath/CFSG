module

public import CFSG.Quasithin.Vol2.Ch10SecA312LC
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312LF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem three_dvd_two_pow_mul (m : ℕ) : 3 ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have h : ((2 : ℕ) ^ m) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ ((2 : ℕ) ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  exact Dvd.dvd.mul_left (by omega) _

theorem not_three_dvd_suzuki (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  · omega

theorem dvd_of_is2F4
    {G : Type} [Group G] [Finite G] {L P : Subgroup G} {f : ℕ} (hL : Is2F4 f ↥L)
    (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ} (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) :
    f ∣ n := by
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hL
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hchar : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  obtain ⟨hQ, hQtop, hn'⟩ := transport e hP hPL hn
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K a)
      (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := hUsyl.2.1
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  refine dvd_of_leviField (isSylowTwoOf_subgroupOf_top hUsyl)
    (large_Ree_residualOvergroupsAt hK) (fun j => ?_) hQ hQtop hn'
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (f4Index j) with hj | hj
  ·
    have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq)
      (isSimpleGroup_rankOneGroupOne ha hK).2
    let e₁ : ↥(rankOneGroupOne K a) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (rankOneEquivSL K a hK).symm
    refine Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hchar, 2 * a + 1, hK, dvd_rfl,
      by omega, e₁.toMonoidHom.comp g, e₁.surjective.comp hg, ?_⟩)
    have hkerEq : (e₁.toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact MulEquiv.map_eq_one_iff e₁
    rw [hkerEq]
    exact hk
  ·
    have : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq)
      (isSimpleGroup_rankOneGroupTwo ha hK).2
    refine Or.inr (Or.inr fun m hm => ?_)
    obtain ⟨-, K', _, _, _, hK', ⟨e₂⟩⟩ := exists_sl2_of_isPSL hm
    have hc := Nat.card_congr ((e₂.symm.trans (modO2EquivOfHom
      (isSimpleGroup_rankOneGroupTwo ha hK).2 g hg hk)).trans
      (rankOneEquivSuzuki K a ha hK)).toEquiv
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK', suzuki_order hK] at hc
    exact not_three_dvd_suzuki a (hc ▸ three_dvd_two_pow_mul m)

theorem false_of_isTits
    {G : Type} [Group G] [Finite G] {L P : Subgroup G} (hL : IsTits ↥L)
    (hP : IsParabolic2 L P) (hPL : P ≠ L) {n : ℕ} (hn : IsPSL 2 2 n (ModO2 (perfectCore P))) :
    False := by
  obtain ⟨hQ, hQtop, hn'⟩ := transport (MulEquiv.refl ↥L) hP hPL hn
  generalize (P.subgroupOf L).map (MulEquiv.refl ↥L).toMonoidHom = Q at hQ hQtop hn'
  obtain ⟨-, S, hS, hN⟩ := hQ
  have hSQ : S ≤ Q := fun s hs => hN ⟨trivial, Subgroup.le_normalizer hs⟩
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice (↥L) hL S hS
  have hsol : Group.IsSolvable ↥Q := by
    rcases hlat Q hSQ with rfl | rfl | rfl | h
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := hS.2.1.isNilpotent
      infer_instance
    · exact hHs
    · exact hNs
    · exact absurd h hQtop
  have := subsingleton_modO2_of_eq_bot ((isSolvable_iff_perfectCore_eq_bot Q).mp hsol)
  exact not_isPSL_of_subsingleton hn'

theorem a312LeviField_holds
    : A312LeviField := by
  rintro X _ _ B L ⟨⟨n, hn⟩, hR, P, ⟨hP, hPL, -⟩, rfl⟩
  rcases hR with ⟨f, h1 | h2 | h3 | h4 | h5 | h6⟩ | hT
  · exact ⟨f, n, dvd_of_isPSL3 h1.2 hP hPL hn, hn, Or.inl h1⟩
  · exact ⟨f, n, dvd_of_isSL3 h2.1 h2.2 hP hPL hn, hn, Or.inr (Or.inl h2)⟩
  · exact ⟨f, n, dvd_of_isPSp4 h3.1 h3.2 hP hPL hn, hn, Or.inr (Or.inr (Or.inl h3))⟩
  · exact ⟨f, n, dvd_of_isG2 h4.2 hP hPL hn, hn, Or.inr (Or.inr (Or.inr (Or.inl h4)))⟩
  · exact ⟨f, n, dvd_of_is3D4 h5.2 hP hPL hn, hn,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))⟩
  · exact ⟨f, n, dvd_of_is2F4 h6.2.2 hP hPL hn, hn,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))⟩
  · exact (false_of_isTits hT hP hPL hn).elim

end CFSG.Quasithin.Vol2.Ch10.A312LF
