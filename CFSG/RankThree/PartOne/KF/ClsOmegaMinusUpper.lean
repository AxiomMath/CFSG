module

public import CFSG.RankThree.PartOne.KF.ClsAltOdd
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRankOmega

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

section Polar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] noncomputable def polarBilin (F : ReflForm K V) (hσ : F.σ = RingEquiv.refl K) :
    V →ₗ[K] V →ₗ[K] K :=
  LinearMap.mk₂ K F.β F.add_left
    (fun c u v => by rw [F.smul_left, hσ, smul_eq_mul]; rfl) F.add_right F.smul_right

theorem polarBilin_apply (F : ReflForm K V) (hσ : F.σ = RingEquiv.refl K) (u v : V) :
    polarBilin F hσ u v = F.β u v := rfl

end Polar

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

omit [Finite K] in
theorem statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot :
    (StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 4 K b c)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.mp hx
  have hpres := orthGroup_preserves (StatedQuadMinus 4 K b c)
    (statedOmega_le_orthGroup (StatedQuadMinus 4 K b c) x.2)
  have hxz : ((x : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) =
      Matrix.scalar _ (z : K) := by
    rw [← hz, Matrix.GeneralLinearGroup.coe_scalar]
  have hv := hpres (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr (Sum.inl 0)) 1)
  have e : ∀ w : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K,
      (Matrix.scalar (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (z : K)).mulVec w = (z : K) • w := by
    intro w
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hxz, e] at hv
  have hz1 : (z : K) = 1 := by
    refine eq_one_of_sq_eq_one_charTwo ?_
    rw [PartTwo.KFacts.KS21LocalRank.quadMinus_apply, PartTwo.KFacts.KS21LocalRank.quadMinus_apply]
      at hv
    simp at hv
    linear_combination hv
  have hz' : z = 1 := Units.ext hz1
  rw [hz', map_one] at hz
  rw [Subgroup.mem_bot]
  exact Subtype.ext hz.symm

theorem localRank_statedOmegaMinus_four_le_one (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h1 : ¬ p ∣ Nat.card K - 1) (h2 : ¬ p ∣ Nat.card K + 1) :
    localRank p ↥(StatedOmega (StatedQuadMinus 4 K b c)) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hlt
  have hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm (⟨g, hg⟩ : E) ⟨h, hh⟩)
  have hexp : ∀ g ∈ E, g ^ p = 1 := fun g hg =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian g hg
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_ne_two hp hp2
  let Φ := quadMinusForm 4 K b c hirr
  have hρ : IsIsometric Φ.polar (natRep (StatedOmega (StatedQuadMinus 4 K b c))) :=
    isIsometric_natRep_statedOmega Φ
  have hdim : Module.finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  by_cases h3 : p ∣ Nat.card K ^ 3 - 1
  · have hdiv3 : ∀ i : ℕ, 0 < i → i < 3 → ¬ p ∣ Nat.card K ^ i - 1 := by
      intro i hi hid
      interval_cases i
      · simpa using h1
      · exact not_dvd_sq_sub_one hp hq h1 h2
    let ρ := natRep (StatedOmega (StatedQuadMinus 4 K b c))
    let σ := FlagSplit.repAut ρ
    have hσinj : Function.Injective σ := by
      intro g h hgh
      apply natRep_injective
      apply LinearMap.ext
      intro v
      exact LinearEquiv.congr_fun hgh v
    let B := polarBilin Φ.polar Φ.polar_σ
    have hBnd : ∀ v, (∀ w, B v w = 0) → v = 0 := Φ.polar.nondeg
    have hBalt : ∀ v, B v v = 0 := by
      intro v
      rw [polarBilin_apply, Φ.polar_self, CharTwo.two_eq_zero, zero_mul]
    let E' := E.map σ
    have : Finite E' := Finite.of_equiv E (Subgroup.equivMapOfInjective E σ hσinj).toEquiv
    have hcardE' : Nat.card E' = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hσinj]
      exact hEc
    have hcommE' : ∀ g ∈ E', ∀ h ∈ E', g * h = h * g := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha a' ha']
    have hexpE' : ∀ g ∈ E', g ^ p = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hexp a ha, map_one]
    have hpresE' : ∀ g ∈ E', ∀ u w, B (g u) (g w) = B u w := by
      rintro _ ⟨a, ha, rfl⟩ u w
      exact hρ a u w
    have hbound := card_le_pow_div_alt_odd hp hpK (d := 3) (by norm_num) (by decide) hdiv3 h3 8
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) hdim B hBnd hBalt E' hcommE' hexpE' hpresE'
    rw [hcardE'] at hbound
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hbound
    omega
  · obtain ⟨a, ha1, ha2, hcard⟩ := card_le_of_normalizes Φ.polar
      (natRep (StatedOmega (StatedQuadMinus 4 K b c))) hρ (natRep_injective _) hp hp2 hpK
      (d := 4) (by norm_num)
      (fun i hi hid => by
        interval_cases i
        · simpa using h1
        · exact not_dvd_sq_sub_one hp hq h1 h2
        · exact h3) hU2 hU0 hEU hcomm hexp
    rw [hdim] at ha2 hcard
    rw [hEc, ← pow_add] at hcard
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
    omega

theorem localRank_statedProj_statedOmegaMinus_four_le_one
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : ¬ p ∣ Nat.card K - 1) (h2 : ¬ p ∣ Nat.card K + 1) :
    localRank p (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) ≤ 1 := by
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (equivProjOfScalarsBot _ (statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot (K := K)
      (b := b) (c := c))) hp]
  exact localRank_statedOmegaMinus_four_le_one hirr hp hp2 h1 h2

end CFSG.RankThree.PartOne.KFU
