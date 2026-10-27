module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2Tools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG Matrix
open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartTwo.KFacts (stdPinnedPSL2)
open scoped MatrixGroups

namespace Res413Cover

theorem mem_range_toPGL_of_pow_three {K : Type} [Field K] {g : PGL2 K} (hg : g ^ 3 = 1) :
    g ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_three hg
  exact ⟨x, hx⟩

theorem mem_range_conj_of_mem_range_pglAction {K : Type} [Field K] [Finite K] {τ : MulAut (PSL2 K)}
    (hτ : τ ∈ (pglAction K).range) (hτ3 : τ ^ 3 = 1) :
    τ ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range := by
  obtain ⟨g, rfl⟩ := hτ
  have hg3 : g ^ 3 = 1 := by
    apply Item434CharThree.pglAction_injective K
    rw [map_pow, hτ3, map_one]
  obtain ⟨x, rfl⟩ := mem_range_toPGL_of_pow_three hg3
  exact ⟨x, (pglAction_toPGL K x).symm⟩

theorem pow_three_eq_one_of_commute {e : ℕ} (he : e ≠ 0) {b y : PSL2 (GaloisField 3 e)}
    (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) (hyb : y * b = b * y) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (PGL2 (GaloisField 3 e)) := Item434CharThree.finite_pgl2
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField 3 e) with hι
  have hιinj : Function.Injective ι := ProjectiveSpecialLinearGroup.toPGL_injective
  have hb3' : ι b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hb1' : ι b ≠ 1 := fun h => hb1 (hιinj (h.trans (map_one ι).symm))
  have hZ : IsPGroup 3 (Subgroup.zpowers (ι b)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime hb3' hb1')
  obtain ⟨h, hh⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := Item434CharThree.unipPGL _)
    (by rw [Item434CharThree.card_unipPGL_galois he, Item434CharThree.factorization_card_pgl2 he])
    hZ
  have hbW := hh (Subgroup.mem_zpowers (ι b))
  have hyW := Item434CharThree.mem_map_conj_unipPGL_of_commute (c := ι y) hbW hb1'
    (by rw [← map_mul, ← map_mul, hyb])
  have h3 := Item434CharThree.pow_three_eq_one_of_mem_map_conj hyW
  apply hιinj
  rw [map_pow, h3, map_one]

theorem card_le_three_mul_inf_pglAction {e : ℕ} (he : e ≠ 0)
    {E : Subgroup (MulAut (PSL2 (GaloisField 3 e)))} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ (pglAction (GaloisField 3 e)).range : Subgroup _) := by
  set K := GaloisField 3 e with hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKc : Nat.card K = 3 ^ e := GaloisField.card 3 e he
  set S := semilinearEquivAut K with hS
  set E' : Subgroup (PGammaL2 K) := E.comap S.toMonoidHom with hE'
  have hE'map : E'.map S.toMonoidHom = E := Subgroup.map_comap_eq_self_of_surjective S.surjective E
  have hE'card : Nat.card E' = Nat.card E := by
    rw [← hE'map, Subgroup.card_map_of_injective (f := S.toMonoidHom) S.injective]
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
    Item434Kit.isElemAbelian_of_map_injective S.injective (hE'map ▸ hE)
  set ρ : PGammaL2 K →* (K ≃+* K) := SemidirectProduct.rightHom with hρ
  have hcyc : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K hKc).2
  have hρ3 : Nat.card (E'.map ρ) ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨_, y, hy, rfl⟩ := x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hE'e.2 y hy, map_one]
  have hcardE := Item434Alt.card_eq_card_inf_ker_mul_card_map ρ E'
  have hd := Nat.le_of_dvd (by norm_num) hρ3
  have hle : (E' ⊓ ρ.ker).map S.toMonoidHom ≤ E ⊓ (pglAction K).range := by
    rintro _ ⟨x, ⟨hxE, hxk⟩, rfl⟩
    refine ⟨hxE, ?_⟩
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at hxk
    obtain ⟨g, rfl⟩ := hxk
    exact ⟨g, (semilinearAction_inl K g).symm⟩
  have h1 : Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) ≤
      Nat.card (E ⊓ (pglAction K).range : Subgroup _) := by
    rw [← Subgroup.card_map_of_injective (f := S.toMonoidHom) S.injective]
    exact Subgroup.card_le_of_le hle
  rw [← hE'card, hcardE]
  calc Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) * Nat.card (E'.map ρ)
      ≤ Nat.card (E ⊓ (pglAction K).range : Subgroup _) * 3 := Nat.mul_le_mul h1 hd
    _ = 3 * Nat.card (E ⊓ (pglAction K).range : Subgroup _) := mul_comm _ _

theorem card_le_of_forall_fixed {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {P : Subgroup (PGL2 K)} (hP : IsPGroup 3 P) (hfix : ∀ g ∈ P, pgl2FieldAut K σ g = g) {n : ℕ}
    (hn : Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ) =
      3 ^ n) : Nat.card P ≤ 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set k := CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ with hk
  set f := CFSG.ComponentClassification.CatalogueBHigherLinearField.subfieldPGLMap (Fin 2) K k
    with hf
  have hPf : P ≤ f.range := by
    intro g hg
    have h := hfix g hg
    rw [← CFSG.ComponentClassification.CatalogueBHigherLinearField.pglFieldAut_two] at h
    exact (CFSG.ComponentClassification.CatalogueBHigherLinearField.pgl_fixed_iff_mem_subfield_range
      (Fin 2) K σ g).mp h
  have hPmap : (P.comap f).map f = P := Subgroup.map_comap_eq_self hPf
  have hdvd1 : Nat.card P ∣ Nat.card (P.comap f) := by
    conv_lhs => rw [← hPmap]
    exact Subgroup.card_map_dvd _ _
  have hdvd2 : Nat.card (P.comap f) ∣ Nat.card (PGL2 k) := Subgroup.card_subgroup_dvd_card _
  have : Finite k := Subtype.finite
  rw [pgl2_card_formula, hn] at hdvd2
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  rw [ha] at hdvd1 ⊢
  have hcop : Nat.Coprime (3 ^ a) ((3 ^ n) ^ 2 - 1) := by
    refine Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
    intro h3
    have h1 : 3 ∣ (3 ^ n) ^ 2 := dvd_pow (dvd_pow_self 3 (by
      rintro rfl
      have := Finite.one_lt_card (α := k)
      rw [hn, pow_zero] at this
      omega)) two_ne_zero
    have h2 : 1 ≤ (3 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right (hdvd1.trans hdvd2))

end Res413Cover

end CFSG.RankThree.PartTwo.Sec4
