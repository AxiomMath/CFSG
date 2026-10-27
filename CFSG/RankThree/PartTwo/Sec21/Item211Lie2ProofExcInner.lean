module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofExc
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem mem_range_conj_of_card_outer_dvd {X : Type*} [Group X] {k : ℕ}
    (h : Nat.card (Outer X) ∣ 2 ^ k) (τ : MulAut X) (hτ : τ ^ 3 = 1) :
    τ ∈ (MulAut.conj : X →* MulAut X).range := by
  set a : Outer X := (τ : MulAut X ⧸ inner X) with ha
  have h1 : orderOf a ∣ 2 ^ k := (orderOf_dvd_natCard a).trans h
  have h2 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (by
    rw [ha, ← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one])
  have hcop : Nat.Coprime (orderOf a) 3 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (by norm_num))
  have h3 : orderOf a = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
  rw [orderOf_eq_one_iff, ha, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
  rw [hY, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.mpr (e.injective (hex.trans (map_one e).symm))

theorem mem_range_conj_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ τ : MulAut Y, τ ^ 3 = 1 → τ ∈ (MulAut.conj : Y →* MulAut Y).range)
    (τ : MulAut X) (hτ : τ ^ 3 = 1) : τ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, hy⟩ := hY (MulAut.congr e τ) (by rw [← map_pow, hτ, map_one])
  refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
  have h1 : y * e x * y⁻¹ = e (τ x) := by
    have h2 := congrArg (fun σ : MulAut Y => σ (e x)) hy
    simpa only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] using h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem ringEquiv_eq_one_of_card_prime {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (σ : K ≃+* K) : σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hp.ne_zero)
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = p := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K p := charP_of_card_eq_prime hK'
  have hbij := ZMod.castHom_bijective K hK'
  have hcomp : (σ : K →+* K).comp (ZMod.castHom (dvd_refl p) K) = ZMod.castHom (dvd_refl p) K :=
    Subsingleton.elim _ _
  ext x
  obtain ⟨y, rfl⟩ := hbij.2 x
  exact RingHom.congr_fun hcomp y

theorem excInner_G2
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hm : ChevalleyExceptionalModel X .G2 p 1) :
    Subgroup.center X = ⊥ ∧ ∀ τ : MulAut X, τ ^ 3 = 1 →
      τ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hu : UntwistedChevalleyModel X .G2 (p ^ 1) := hm.2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hu
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  refine ⟨center_eq_bot_of_mulEquiv e hZ, mem_range_conj_of_mulEquiv e fun τ _ => ?_⟩
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form hp
      (by omega) le_rfl K hK .G2 (Or.inr ⟨rfl, by omega⟩)
  have hτ : τ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker]
    exact ringEquiv_eq_one_of_card_prime hp (by rw [hK, pow_one]) _
  rw [hker] at hτ
  exact hτ

theorem excInner_PSp {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hq : IsQuasisimple X) (e : X ≃* projSp 2 (GaloisField p 1)) :
    Subgroup.center X = ⊥ ∧ ∀ τ : MulAut X, τ ^ 3 = 1 →
      τ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  set e' := e.trans (Sec4.projSpEquivStatedProj 2 (GaloisField p 1)) with he'
  have : IsSimpleGroup (StatedProj (StatedSp 2 (GaloisField p 1))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp _ 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hK, pow_one]; omega)))
  refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e', fun τ hτ => ?_⟩
  have hT : StatedClassicalModel X .PSp 2 p 1 :=
    ⟨⟨hp, le_rfl, le_rfl, fun h => by
      have h2 : p ^ 1 = 2 := (Prod.mk.inj h).2
      rw [pow_one] at h2
      omega⟩, GaloisField p 1, inferInstance, inferInstance, hK, ⟨e'⟩⟩
  obtain ⟨-, hout, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound X 2 p 1 hT
  refine mem_range_conj_of_card_outer_dvd (k := 2) (hout.trans ?_) τ hτ
  have hg : Nat.gcd 2 (p ^ 1 - 1) ∣ 2 := Nat.gcd_dvd_left _ _
  calc 2 * 1 * Nat.gcd 2 (p ^ 1 - 1) ∣ 2 * 1 * 2 := Nat.mul_dvd_mul_left _ hg
    _ = 2 ^ 2 := by norm_num

theorem excInner_PSU {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (hq : IsQuasisimple X) (e : X ≃* projSU 4 p 1) :
    Subgroup.center X = ⊥ ∧ ∀ τ : MulAut X, τ ^ 3 = 1 →
      τ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p (2 * 1)) = (p ^ 1) ^ 2 := by
    rw [GaloisField.card p (2 * 1) (by norm_num), ← pow_mul, mul_comm]
  set e' := e.trans (Sec4.projSUEquivStatedProj 4 p 1) with he'
  have : IsSimpleGroup (StatedProj (StatedSU 4 (p ^ 1) (GaloisField p (2 * 1)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU _ p 1 hK 4 (by norm_num)
      (fun h => absurd (Prod.mk.inj h).1 (by norm_num))
  refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e', fun τ hτ => ?_⟩
  have hT : StatedClassicalModel X .PSU 4 p 1 :=
    ⟨⟨hp, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩,
      GaloisField p (2 * 1), inferInstance, inferInstance, hK, ⟨e'⟩⟩
  obtain ⟨-, -, hout, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound X 4 p 1 hT
  refine mem_range_conj_of_card_outer_dvd (k := 3) ?_ τ hτ
  rw [hout]
  have hg : Nat.gcd 4 (p ^ 1 + 1) ∣ 4 := Nat.gcd_dvd_left _ _
  calc 2 * 1 * Nat.gcd 4 (p ^ 1 + 1) ∣ 2 * 1 * 4 := Nat.mul_dvd_mul_left _ hg
    _ = 2 ^ 3 := by norm_num

noncomputable def projSLEquivStatedProj (n : ℕ) (F : Type) [Field F] :
    projSL n F ≃* StatedProj (StatedSL n F) :=
  CFSG.PGLModel.projSLEquivStatedProj n F

theorem excInner_PSL {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (hq : IsQuasisimple X) (e : X ≃* projSL 4 (GaloisField p 1)) :
    Subgroup.center X = ⊥ ∧ ∀ τ : MulAut X, τ ^ 3 = 1 →
      τ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (GaloisField p 1)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 4 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have : IsSimpleGroup (projSL 4 (GaloisField p 1)) :=
    (Sec4.projSLEquivPSLn 4 (GaloisField p 1)).isSimpleGroup
  refine ⟨Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq e, fun τ hτ => ?_⟩
  have hT : StatedClassicalModel X .PSL 4 p 1 :=
    ⟨⟨hp, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
      fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩,
      GaloisField p 1, inferInstance, inferInstance, hK,
      ⟨e.trans (projSLEquivStatedProj 4 (GaloisField p 1))⟩⟩
  obtain ⟨-, -, -, -, hout⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 4 p 1 hT
  refine mem_range_conj_of_card_outer_dvd (k := 3) ((hout (by norm_num)).trans ?_) τ hτ
  have hg : Nat.gcd 4 (p ^ 1 - 1) ∣ 4 := Nat.gcd_dvd_left _ _
  calc 2 * 1 * Nat.gcd 4 (p ^ 1 - 1) ∣ 2 * 1 * 4 := Nat.mul_dvd_mul_left _ hg
    _ = 2 ^ 3 := by norm_num

end Item211Lie2Proof

open Item211Lie2Proof

theorem ks211ExcInner_holds :
    KS211ExcInner := by
  intro X _ _ hq hX
  obtain ⟨p, hp, hp3, hcase⟩ := hX
  rcases hcase with hG2 | he | ⟨-, he⟩ | ⟨-, he⟩
  · exact excInner_G2 hp.out hp3 hG2
  · exact excInner_PSp hp3 hq he.some
  · exact excInner_PSU hq he.some
  · exact excInner_PSL hq he.some

end CFSG.RankThree.PartTwo.Sec21
