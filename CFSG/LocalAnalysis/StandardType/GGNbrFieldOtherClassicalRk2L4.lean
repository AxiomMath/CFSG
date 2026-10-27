module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.Alternating.Multipliers.Main
public import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggSCWeylIrredTwoL4_specialLinear {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpK0 : (p : K) ≠ 0) (hpK : ¬ p ∣ Nat.card K - 1) :
    GGSCWeylIrredTwoLU4 p (Matrix.SpecialLinearGroup (Fin d) K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E hE _ hsc
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := K) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζ : AdjoinRoot.root g ^ p = 1 := (CoordSL.root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hC : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat hp hpK hpK0 hgd
  have hCp : CoordSL.rootMat g ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  have hSc : ∀ x ∈ Set.range (fun b : E =>
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)),
      ∀ y ∈ Set.range (fun b : E =>
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)),
      Commute x y := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    change ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((c : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((c : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      TableB.IsElemAbelian.comm hE b.2 c.2]
  have hSp : ∀ x ∈ Set.range (fun b : E =>
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)),
      x ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← Matrix.SpecialLinearGroup.coe_pow,
      hE.2 (b : Matrix.SpecialLinearGroup (Fin d) K) b.2,
      Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨s, r, ε, A₀, hframe⟩ := CoordSL.exists_frame (g := g) hp hpK0 hgd
    (Set.range fun b : E => ((b : Matrix.SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K)) hSc hSp
  have hframeE : ∀ b ∈ E, ∃ k : Fin s → ℕ,
      b = SLRep.ggFrame (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀
        (SLNS.nsSL ε hC k) := by
    intro b hb
    obtain ⟨k, hk⟩ := hframe ((b : Matrix.SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) ⟨⟨b, hb⟩, rfl⟩
    refine ⟨k, ?_⟩
    have h1 : b * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
    have h2 : b = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by rw [← h1, mul_inv_cancel_right]
    rw [SLRep.ggFrame_apply, MonoidHom.id_apply]
    exact h2
  have hscE : ∀ x ∈ Subgroup.centralizer (E : Set _), x ^ p = 1 → x ∈ E := fun x hx hxp =>
    hsc x (fun e he => (Subgroup.mem_centralizer_iff.mp hx e he).symm) hxp
  have hrange : (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hC hCp).range = E :=
    CoordSL.range_frameHom_of_sc _ A₀ ε hC hCp hscE hframeE
  rw [← hrange]
  refine ggWeylIrred_of_monomialModel
    (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp)
    (CoordSL.galExp g hζ) (galExp_ne_bot hp hpK0 hpK g hζ) ?_
  intro π η hη
  obtain ⟨w, hw, hws⟩ := CoordSL.exists_move_mem g
    (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp hζ hrange π η hη
  refine ⟨w, ?_, hws⟩
  rw [hrange]
  exact (Subgroup.mem_inf.mp hw).2

theorem ggSCWeylIrredTwoL4_projectiveSL {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpK0 : (p : K) ≠ 0) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 0 < d) :
    GGSCWeylIrredTwoLU4 p (projectiveSL d K) := by
  refine ggSCWeylIrredTwoLU4_of_centralQuotient hp (proj d K) (proj_surjective d K) ?_ ?_
    (ggSCWeylIrredTwoL4_specialLinear hp hpK0 hpK)
  · intro g hg
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hg
  · intro h
    exact hpK (h.trans (card_center_specialLinear_dvd hd))

theorem ggCenterPrime_projectiveSL_of_sectionsL4 {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hsec : TypeA.SLHasSections d K) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 3 ≤ d) :
    GGCenterPrime p (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf hpZ
  obtain ⟨φ, hφsurj, hφ⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  have hZker : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center (projectiveSL d K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := d) (k := K) hd,
      Subgroup.mem_bot] at hzc
    exact hzc
  have hkerMap : ψ.ker ≤ (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)).map φ := by
    intro l hl
    obtain ⟨g, rfl⟩ := hφsurj l
    rw [MonoidHom.mem_ker, hφ g] at hl
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    rw [← scalars_eq_center d K]
    exact proj_eq_one_iff.mp hl
  have hdvd : Nat.card (Subgroup.center L') ∣ Nat.card K - 1 :=
    (Subgroup.card_dvd_of_le (hZker.trans hkerMap)).trans <|
      (Subgroup.card_map_dvd
        (H := Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)) φ).trans <|
        card_center_specialLinear_dvd (K := K) (by omega)
  exact hpK (dvd_trans hpZ hdvd)

theorem ggCenterPrime_of_alt8L4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (e : R ≃* alternatingGroup (Fin 8)) (hZ : Subgroup.center R = ⊥) : GGCenterPrime p R := by
  intro L' _ _ ψ hψ hker hperf hpZ
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  set ψ' : L' →* alternatingGroup (Fin 8) := e.toMonoidHom.comp ψ with hψ'
  have hker' : ψ'.ker = ψ.ker := TypeA.ker_comp_mulEquiv e ψ
  have hψ's : Function.Surjective ψ' := e.surjective.comp hψ
  have hdvdM : Nat.card ψ'.ker ∣ 2 := by
    rw [← CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (n := 8) le_rfl]
    exact Subgroup.card_dvd_of_surjective
      (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective ψ' hψ's (hker' ▸ hker))
  have hZker : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  have hdvd : Nat.card (Subgroup.center L') ∣ 2 :=
    (Subgroup.card_dvd_of_le hZker).trans (hker' ▸ hdvdM)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (dvd_trans hpZ hdvd))

theorem nonempty_recipe_mulEquiv_alt8L4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (LargeEvenProj (LargeEvenSLGroup (Fin 4) K) ≃* alternatingGroup (Fin 8)) := by
  have key : ∀ H : Subgroup (GL (Fin 4) K), H = CFSG.Open.StatedSL 4 K →
      Nonempty (LargeEvenProj H ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 4 K)) := by
    rintro H rfl
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨eS⟩ := key _ (largeEvenSLGroup_eq_statedSL 4)
  refine (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).mp ?_
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, K,
    inferInstance, inferInstance, by rw [hK, pow_one], ⟨eS⟩⟩

section L4

variable {n p : ℕ} {K : Type} [Field K] [Finite K]

theorem ggTorusNoLineTwoL4_linear (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) :
    GGTorusNoLineTwo p (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) Set.univ) := by
  haveI : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  have hpK0 : (p : K) ≠ 0 := fun hzero =>
    hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp hzero)).symm)
  have hpK1 : p ∣ Nat.card K + 1 := by rwa [hK]
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hdvd : p ∣ 2 := by
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have hpos : 1 ≤ Nat.card K := by rw [hK]; exact Nat.one_le_two_pow
        omega
      rw [← hsub]
      exact Nat.dvd_sub hpK1 hK1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  let e := TypeA.recipeEquiv 4 K
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 4) (k := K)
      (by norm_num)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (f := (e : LargeEvenProj (LargeEvenSLGroup (Fin 4) K) →* projectiveSL 4 K))
        e.injective).mp h1
  have hcp : GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
    rcases Nat.lt_or_ge 1 n with h2 | h1
    · have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      have hev : 2 ∣ Nat.card K := by
        rw [hK]
        exact dvd_pow_self 2 (by omega)
      refine ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL_of_sectionsL4
        (TypeA.slHasSections_of_card (by norm_num) (by omega) (by omega) ?_) hpK (by norm_num))
      rintro ⟨-, h3⟩
      omega
    · have hK2 : Nat.card K = 2 := by
        rw [hK, show n = 1 by omega, pow_one]
      obtain ⟨e₈⟩ := nonempty_recipe_mulEquiv_alt8L4 hK2
      exact ggCenterPrime_of_alt8L4 hp hp2 e₈ hZ
  exact ggTorusNoLineTwo_of_scWeylIrredTwoLU4 hp hZ
    (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_linear hp hpK (by norm_num) φ hφ hφp) hcp
    (ggSCWeylIrredTwoLU4_of_mulEquiv e
      (ggSCWeylIrredTwoL4_projectiveSL hp hpK0 hpK (by norm_num)))

theorem recipeLinear_rowPlainTwoL4 (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeLinear 4 (2 ^ n) Q) :
    LargeEvenRecipeLinear 4 (2 ^ n) fun R _ I F => Q R I F ∧ GGNbrWeylRowPlainTwo p 0 R I F := by
  obtain ⟨K', _, _, hK, hQ'⟩ := hQ
  haveI : CharP K' 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  refine ⟨K', inferInstance, inferInstance, hK, hQ', fun g => ?_, ?_, fun _ _ =>
    ggTorusNoLineTwoL4_linear hK hn hp hp2 hpq⟩
  · rw [← RecipeFieldLinear.coe_recI]
    exact RecipeFieldLinear.conj_mem_recI g
  · exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 4 K')
      (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (d := 4) (by norm_num)))

end L4

theorem largeEvenLabelAll_rowPlainTwo_l4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .A ∨ lab.tag = .D) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  obtain ⟨hT, hl, hpq⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hT hl hpq
  subst hl
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases hT with rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · exact recipeLinear_rowPlainTwoL4 hn hp hp2 hpq hQ
  · simp only [↓reduceIte] at hQ ⊢
    exact recipeLinear_rowPlainTwoL4 hn hp hp2 hpq hQ

end CFSG.StandardType

end
