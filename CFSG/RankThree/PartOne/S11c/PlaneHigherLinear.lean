module

public import CFSG.RankThree.PartOne.S11c.MatrixModelLift
public import CFSG.RankThree.PartOne.S11c.HigherLinearSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Core
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.CatFactsL4U4 (det_eq_one_of_mem_statedSL)
open scoped MatrixGroups

@[expose] def DegreeFourPlane : Prop :=
  ∀ (k : Type) [Field k], (2 : k) ≠ 0 → ∀ (n : ℕ), n ≤ 4 → ∀ (Q E : Subgroup (GL (Fin n) k))
    [Finite Q], IsPGroup 2 Q → ∀ (p : ℕ), p.Prime → 3 < p →
      (∀ x ∈ E, (x : Matrix (Fin n) (Fin n) k).det = 1) → IsElementaryAbelian p E →
      Nat.card E = p ^ 2 → E ≤ Subgroup.normalizer (Q : Set (GL (Fin n) k)) → ⁅E, Q⁆ = ⊥

@[expose] def DegreeSixPrimes : Prop :=
  ∀ (k : Type) [Field k], (2 : k) ≠ 0 → ∀ (n : ℕ), n ≤ 6 → ∀ (Q P : Subgroup (GL (Fin n) k))
    [Finite Q], IsPGroup 2 Q → ∀ (p : ℕ), p.Prime → 5 < p → ∀ [Finite P], IsPGroup p P →
      P ≤ Subgroup.normalizer (Q : Set (GL (Fin n) k)) → ⁅P, Q⁆ = ⊥

theorem no_plane_of_card {T : Type} [Group T] [Finite T] (hZ : Subgroup.center T = ⊥) {p : ℕ}
    (hp : p.Prime) {E : Subgroup (MulAut T)} (hE : Nat.card E = p ^ 2) (hpT : ¬ p ∣ Nat.card T)
    {m : ℕ} (hout : Nat.card (Outer T) ∣ m) (hpm : ¬ p ^ 2 ∣ m) : False := by
  have hinj := conj_injective_of_center_bot hZ
  have h1 : Nat.card (inner T) = Nat.card T := by
    change Nat.card (MulAut.conj : T →* MulAut T).range = Nat.card T
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 : Nat.card (inner T) * Nat.card (Outer T) = Nat.card (MulAut T) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner T)
    rw [this, mul_comm]
  have h3 : p ^ 2 ∣ Nat.card T * Nat.card (Outer T) := by
    rw [← h1, h2, ← hE]
    exact Subgroup.card_subgroup_dvd_card E
  have hcop : Nat.Coprime (p ^ 2) (Nat.card T) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpT)
  exact hpm ((hcop.dvd_of_dvd_mul_left h3).trans hout)

theorem not_dvd_card_GL_three_243 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 5) :
    ¬ 5 ∣ Nat.card (GL (Fin 3) K) := by
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 243 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  rw [Matrix.card_GL_field, hq]
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num

theorem not_dvd_card_GL_five_six {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {n : ℕ}
    (hn : n = 5 ∨ n = 6) : ¬ 25 ∣ Nat.card (GL (Fin n) K) := by
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Matrix.card_GL_field, hq]
  rcases hn with rfl | rfl
  · simp only [Fin.prod_univ_five, Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num
  · simp only [Fin.prod_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num

theorem planeCentralizes_psl_higher {H : Type} [Group H] [Finite H] {X : Subgroup H}
    (hXqs : CFSG.IsQuasisimple X) {n ℓ f : ℕ} (hn : 3 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL n ℓ f)
    (hrank : localRank ℓ H ≤ 3) {p : ℕ} {E : Subgroup (MulAut (↥X ⧸ Subgroup.center ↥X))}
    {U : Subgroup (↥X ⧸ Subgroup.center ↥X)} (hplane : PlaneOn p E U)
    (hA : DegreeFourPlane) (hB : DegreeSixPrimes) : PlaneCentralizes E U := by
  classical
  obtain ⟨hs1, hs2⟩ := linear_small_parameters (X := H) (Y := X) hn hℓ hℓ2 hmod hrank
  have hf : 1 ≤ f := hmod.1.2.1
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    omega
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := hplane.elementary
  have hZ := center_eq_bot_of_isQuasisimple hXqs
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := ↥X ⧸ Subgroup.center ↥X) (Or.inl rfl) hn hℓ hf hmod
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have hout' : Nat.card (Outer (↥X ⧸ Subgroup.center ↥X)) ∣ 2 * f * Nat.gcd n (ℓ ^ f - 1) := hout
  have hdn : Nat.gcd n (ℓ ^ f - 1) ∣ n := Nat.gcd_dvd_left _ _
  have hdpos : 0 < Nat.gcd n (ℓ ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd4 : Nat.gcd n (ℓ ^ f - 1) ≤ 4 := by
    rcases hs1 with h4 | ⟨rfl, rfl, -⟩
    · exact (Nat.le_of_dvd (by omega) hdn).trans h4
    · have h2 : Nat.gcd n (3 ^ 1 - 1) ∣ 3 ^ 1 - 1 := Nat.gcd_dvd_right _ _
      have := Nat.le_of_dvd (by norm_num) h2
      omega
  have hpd : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1) := fun h => by
    have := Nat.le_of_dvd hdpos h
    omega
  by_cases hexc : p = 5 ∧ ℓ = 3 ∧ n = 3 ∧ f = 5
  · exfalso
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hexc
    have hT5 : ¬ 5 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
      have h1 : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ Nat.card (GL (Fin 3) K) := by
        rw [Nat.card_congr e.toEquiv]
        exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
      exact fun h => not_dvd_card_GL_three_243 hK (h.trans h1)
    refine no_plane_of_card hZ hp hplane.card hT5 hout' ?_
    norm_num
  · have hpf : ¬ p ∣ f := by
      intro h
      have hfp : p ≤ f := Nat.le_of_dvd (by omega) h
      rcases hs2 with h3 | ⟨hℓ3, hn3, h45⟩
      · omega
      · rcases h45 with h4 | h5
        · omega
        · have hp5' : p = 5 :=
            (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (h5 ▸ h)
          exact hexc ⟨hp5', hℓ3, hn3, h5⟩
    have hpm : ¬ p ∣ 2 * f * Nat.gcd n (ℓ ^ f - 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · have := Nat.le_of_dvd (by norm_num) h
          omega
        · exact hpf h
      · exact hpd h
    have hEinner := le_inner_of_not_dvd_outer hp hout' hpm (IsElementaryAbelian.isPGroup p E)
    have h2 : (2 : K) ≠ 0 := by
      have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
      intro h0
      have h1 := (CharP.cast_eq_zero_iff K ℓ 2).mp (by exact_mod_cast h0)
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
    refine planeCentralizes_of_matrix_model hZ (StatedSL n K) e hplane hEinner
      (d := Nat.gcd n (ℓ ^ f - 1)) ?_ hpd ?_
    ·
      intro c hc
      have hdet := det_eq_one_of_mem_statedSL (n := n) hc
      have h1 : c ^ n = 1 := by
        have := congrArg Units.val (Matrix.GeneralLinearGroup.det_scalar (n := Fin n) c)
        rw [Matrix.GeneralLinearGroup.val_det_apply, Fintype.card_fin] at this
        exact Units.ext (by rw [Units.val_one]; exact this.symm.trans hdet)
      have h2 : c ^ (ℓ ^ f - 1) = 1 := by
        have := pow_card_eq_one' (G := Kˣ) (x := c)
        rwa [Nat.card_units, hK] at this
      exact (pow_gcd_eq_one (a := c)).2 ⟨h1, h2⟩
    · intro F V hFM hFel hFcard hV2 hFnorm x hx u hu
      have hdet : ∀ y ∈ F, (y : Matrix (Fin n) (Fin n) K).det = 1 := fun y hy =>
        det_eq_one_of_mem_statedSL (hFM hy)
      have : Finite V := Finite.of_injective (Subgroup.subtype V) (Subgroup.subtype_injective V)
      have hcomm : ⁅F, V⁆ = ⊥ := by
        rcases hs1 with h4 | ⟨hℓ3, hf1, h56⟩
        · exact hA K h2 n (by omega) V F hV2 p hp hp3 hdet hFel hFcard hFnorm
        · by_cases hp5' : p = 5
          · exfalso
            subst hℓ3
            subst hf1
            have hK3 : Nat.card K = 3 := by simpa using hK
            refine not_dvd_card_GL_five_six hK3 h56 ?_
            have h25 : 25 ∣ Nat.card F := ⟨1, by rw [hFcard, hp5']; norm_num⟩
            exact h25.trans (Subgroup.card_subgroup_dvd_card F)
          · have hp6 : 5 < p := by omega
            have hFp : IsPGroup p F := IsElementaryAbelian.isPGroup p F
            have : Finite F :=
              Finite.of_injective (Subgroup.subtype F) (Subgroup.subtype_injective F)
            exact hB K h2 n (by omega) V F hV2 p hp hp6 hFp hFnorm
      have := Subgroup.commutator_mem_commutator hx hu
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this

end CFSG.RankThree.PartOne
