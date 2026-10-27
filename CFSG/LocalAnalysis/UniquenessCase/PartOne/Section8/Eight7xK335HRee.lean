module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HSylRange
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem k335hr_centralizer_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (w : X) :
    Nonempty (↥(Subgroup.centralizer ({w} : Set X)) ≃*
      ↥(Subgroup.centralizer ({e w} : Set Y))) := by
  have hmap : (Subgroup.centralizer ({w} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e w} : Set Y) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hy
  exact ⟨((Subgroup.centralizer ({w} : Set X)).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr hmap)⟩

theorem k335ReeLocal_holds
    : K335ReeLocal := by
  intro X _ _ f hLie
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hR⟩ := hLie.reeTitsModel (by decide)
  obtain ⟨-, a, ha, hf, K₀, hK₀f, hK₀fin, hK₀char, hK₀card, ⟨e₀⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  subst hf
  obtain ⟨u, v, hu1, hu3, -, -, -⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.reeGamma_exists_e9 a K₀ hK₀card
  have hu : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have h3dvd : 3 ∣ Nat.card X := by
    rw [Nat.card_congr e₀.toEquiv, ← hu]
    exact orderOf_dvd_natCard u
  obtain ⟨S⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hScard : 3 ∣ Nat.card (S : Subgroup X) := by
    rw [Sylow.card_eq_multiplicity]
    exact dvd_pow_self 3 (Nat.Prime.factorization_pos_of_dvd Nat.prime_three
      (Nat.card_pos.ne') h3dvd).ne'
  have hSnt : Nontrivial (S : Subgroup X) := by
    have : Nat.card (S : Subgroup X) ≠ 1 := by
      intro h1
      rw [h1] at hScard
      exact absurd (Nat.le_of_dvd one_pos hScard) (by norm_num)
    exact Finite.one_lt_card_iff_nontrivial.mp (by
      have := Nat.card_pos (α := (S : Subgroup X))
      omega)
  have hZnt : Nontrivial (Subgroup.center (S : Subgroup X)) :=
    (S.isPGroup').center_nontrivial
  have hZp : IsPGroup 3 (Subgroup.center (S : Subgroup X)) :=
    (S.isPGroup').to_subgroup _
  have h3Z : 3 ∣ Nat.card (Subgroup.center (S : Subgroup X)) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd h ((Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne')
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3Z
  have hordw : orderOf ((w : (S : Subgroup X)) : X) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw
  have hy : orderOf (e₀ ((w : (S : Subgroup X)) : X)) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hordw
  obtain ⟨E'⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a
    K₀ hK₀card _ hy
  obtain ⟨E''⟩ := k335hr_centralizer_equiv e₀ ((w : (S : Subgroup X)) : X)
  have hSw : (S : Subgroup X) ≤
      Subgroup.centralizer ({((w : (S : Subgroup X)) : X)} : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨s, hs⟩).symm
  obtain ⟨φ, hφ, S', hS', hS'φ⟩ :=
    k335_exists_sylow_le_range (k335_isSylowOf_top S) hSw (E''.trans E')
  refine ⟨GaloisField 2 (2 * (2 * a + 1)), inferInstance, Fintype.ofFinite _, ?_, φ, hφ, S', hS',
    hS'φ⟩
  rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
