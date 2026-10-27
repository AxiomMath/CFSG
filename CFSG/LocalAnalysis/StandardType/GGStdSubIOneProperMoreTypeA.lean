module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreLabels
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGINormAbove (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
    p ^ (r + 1) ≤ Nat.card X → p ^ 4 ≤ Nat.card X →
    ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U

theorem ggINormAbove_of_iRankLe {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} (hp : 1 < p)
    (h : GGIRankLe p r R I) : GGINormAbove p r R I := fun X hXI hX hr h4 =>
  absurd ((hr.trans (h X hXI hX h4))) (not_le.mpr (Nat.pow_lt_pow_right hp (Nat.lt_succ_self r)))

theorem ggINormAbove_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGINormAbove p r R' I') : GGINormAbove p r R I := by
  intro X hXI hX hr h4
  set c := MulAut.congr e with hc
  obtain ⟨U, hU, hU2, hXU⟩ := h (X.map c.toMonoidHom)
    (by rintro _ ⟨φ, hφ, rfl⟩; exact hI φ (hXI hφ)) (TableB.isElemAbelian_map hX _)
    (by rw [card_map_congr]; exact hr) (by rw [card_map_congr]; exact h4)
  refine ⟨U.comap e.toMonoidHom, ?_, hU2.comap_of_injective _ e.injective, fun φ hφ u hu => ?_⟩
  · intro hbot
    apply hU
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective U, hbot,
      Subgroup.map_bot]
  · have h1 := hXU (c φ) ⟨φ, hφ, rfl⟩ (e u) hu
    change e (φ u) ∈ U
    have h2 : c φ (e u) = e (φ u) := by
      rw [hc, MulAut.congr_apply]
      change e (φ (e.symm (e u))) = e (φ u)
      rw [MulEquiv.symm_apply_apply]
    rwa [h2] at h1

section Config

variable {G : Type} [Group G] [Finite G]

theorem bstar_eq_of_bound_norm {p r₁ r₂ : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift₁ : GGTorusLift p r₁ R) (hbound : GGInnerDiagBound p r₁ R I)
    (hlift₂ : GGTorusLift p r₂ R) (hnorm : GGINormAbove p r₂ R I) : B = Bs := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBsN := bstar_le_normalizer_of_sstar hS hBs hnc
  have hcB := card_range_ggBeta_mul L θ hp hS hL hBN
  have hcE := card_range_ggBeta_mul_of hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1 hS.2.2.2.1.1
    hS.2.2.2.2 hL θ hBsN
  have hB4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
  by_contra hne
  have hfin : ∀ {U : Subgroup R}, U ≠ ⊥ → IsPGroup 2 U →
      (∀ φ ∈ (ggBeta L θ hBsN).range, ∀ u ∈ U, φ u ∈ U) → False := by
    intro U hU hU2 hEU
    obtain ⟨T, hTne, hT2, hBsT⟩ := exists_twoSubgroup_of_normalizes θ hBsN hU hU2
      (fun e he u hu => hEU _ ⟨⟨e, he⟩, rfl⟩ u hu)
    have hc := card_le_of_twoLocal hp ⟨T, hTne, hT2, rfl⟩ hBsT hBs.2.1
    rw [← hS.1.2.1] at hc
    exact hne (Subgroup.eq_of_le_of_card_ge hBs.1 hc)
  by_cases hsub : ((ggBeta L θ hBsN).range : Set (MulAut R)) ⊆ I
  · have hpB := mul_card_le_card_of_lt hp hBs.2.1 (lt_of_le_of_ne hBs.1 hne)
    have hEh : Nat.card B ≤ Nat.card (ggBeta L θ hBsN).range := by
      refine Nat.le_of_mul_le_mul_left ?_ hp.pos
      rw [mul_comm p (Nat.card (ggBeta L θ hBsN).range), hcE]
      exact hpB
    have h1 := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1
      hL θ hlift₂
    have h2 : p ^ (r₂ + 1) ≤ Nat.card B := by
      rw [hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    obtain ⟨U, hU, hU2, hEU⟩ := hnorm _ hsub (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN)
      (h2.trans hEh) (hB4.trans hEh)
    exact hfin hU hU2 hEU
  · have hEbI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
      rintro _ ⟨b, rfl⟩
      exact ggBeta_mem L θ hBN h3 b
    have hEb3 : p ^ 3 ≤ Nat.card (ggBeta L θ hBN).range := by
      have h := hB4
      rw [← hcB, pow_succ] at h
      exact Nat.le_of_mul_le_mul_right h hp.pos
    have hcard : Nat.card (ggBeta L θ hBsN).range ≤ p * Nat.card (ggBeta L θ hBN).range := by
      have h1 : Nat.card (ggBeta L θ hBsN).range * p ≤
          p * Nat.card (ggBeta L θ hBN).range * p := by
        rw [hcE, mul_assoc, hcB]
        exact hBs.2.2.1
      exact Nat.le_of_mul_le_mul_right h1 hp.pos
    obtain ⟨U, hU, hU2, hEU⟩ := hbound _ _ hEbI (isElemAbelian_range_ggBeta θ hS.1.1 hBN)
      (pow_le_card_range_ggBeta hp hS hL θ hBN hlift₁) hEb3 (range_ggBeta_le θ hBs.1 hBN hBsN)
      (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN) hcard hsub
    exact hfin hU hU2 hEU

end Config

theorem ggStdSubIOneProperInputOn_of_bstarEqNorm {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
          ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) :
    GGStdSubIOneProperInputOn S := by
  intro G _ _ p B Bs x L hT hBs hne hM
  have hnc := ha₀ G p B x L hT
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, ⟨r₁, hl₁, hb⟩, r₂, hl₂, hr⟩ :=
    largeEvenRawDatum_exists hraw
  exact absurd (bstar_eq_of_bound_norm hT hBs hnc hL θ hBN h3 hl₁ hb hl₂ hr) hne

namespace IOneMore

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification TypeA

variable {d p : ℕ} {K : Type} [Field K] [Finite K]

theorem mem_range_conjAut_of_pow (hd : 3 ≤ d) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f) {φ : MulAut (projectiveSL d K)}
    (hφ : φ ^ p = 1) : φ ∈ Set.range (conjAut d K) := by
  have : (linearAutGroup d K).Normal := linearAutGroup_normal hd
  have hodd : Odd (orderOf φ) := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hφ) with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.odd_of_ne_two hp2
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp
    (UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd hd hodd)
  have hcard : Nat.card (K ≃+* K) = f := by
    obtain ⟨-, -, -, -, hc, -⟩ := finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
    exact hc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  set π := QuotientGroup.mk' (linearAutGroup d K) with hπ
  have h0 : π (conjAut d K A) = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact conjAut_mem_linearAutGroup A
  have h1 : π φ = π (fieldAut d K σ) := by
    rw [hAσ, map_mul, h0, one_mul]
  have hσf : σ ^ f = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have e1 : (π φ) ^ p = 1 := by rw [← map_pow, hφ, map_one]
  have e2 : (π φ) ^ f = 1 := by rw [h1, ← map_pow, ← map_pow, hσf, map_one, map_one]
  have hcop : Nat.Coprime p f := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpf
  have h3 : π φ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one e1) (orderOf_dvd_of_pow_eq_one e2))
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  obtain ⟨A', hA'⟩ := mem_linearAutGroup_iff.mp h3
  exact ⟨A', hA'⟩

omit [Finite K] in
theorem exists_twoSubgroup_of_toral [CharP K 2] (hd : 2 ≤ d)
    {X : Subgroup (MulAut (projectiveSL d K))}
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) {A₀ : GL (Fin d) K}
    (hA₀ : ∀ A : GL (Fin d) K, conjAut d K A ∈ X → ∀ i j, i ≠ j →
      ((A₀ : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) :
    ∃ U : Subgroup (projectiveSL d K), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U := by
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  set c₀ := CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ with hc₀
  set U₀ := (SpecialLinearGroup.transvectionHom h01 : Multiplicative K →* _).range with hU₀
  set U := (U₀.map c₀.toMonoidHom).map (proj d K) with hU
  refine ⟨U, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : proj d K (c₀ (SpecialLinearGroup.transvection h01 1)) ∈ U :=
      ⟨_, ⟨_, ⟨Multiplicative.ofAdd 1, by
        rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]⟩, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 := mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp hmem)
    obtain ⟨c, -, hc⟩ := mem_scalars.mp h2
    have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, by omega⟩ ⟨1, by omega⟩) hc
    simp [CFSG.LinearGroups.coe_transvection] at h4
  · refine IsPGroup.map (IsPGroup.map (fun x => ⟨1, ?_⟩) c₀.toMonoidHom) (proj d K)
    obtain ⟨y, c, hc⟩ := x
    have h2 : y ^ 2 = 1 := by
      rw [← hc, SpecialLinearGroup.transvectionHom_apply,
        CFSG.RankThree.CALinearPlane.transvection_pow, Nat.cast_ofNat, CharTwo.two_eq_zero,
        zero_mul]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero h01
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact h2
  · intro φ hφ u hu
    obtain ⟨A, rfl⟩ := hXI hφ
    obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩ := hu
    set D := A₀ * A * A₀⁻¹ with hD
    have hDdiag : (D : Matrix (Fin d) (Fin d) K) =
        diagonal fun i => (D : Matrix (Fin d) (Fin d) K) i i := by
      refine CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag fun i j hij => ?_
      rw [hD, Units.val_mul, Units.val_mul]
      exact hA₀ A hφ i j hij
    have h2 : CatalogueBHigherLinearAction.slConjugation d K A (c₀
        (SpecialLinearGroup.transvectionHom h01 c)) =
        c₀ (CatalogueBHigherLinearAction.slConjugation d K D
          (SpecialLinearGroup.transvectionHom h01 c)) := by
      rw [hc₀, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hD]
      congr 2
      group
    refine ⟨_, ⟨_, ⟨Multiplicative.ofAdd
      ((D : Matrix (Fin d) (Fin d) K) ⟨0, by omega⟩ ⟨0, by omega⟩ * Multiplicative.toAdd c *
        ((D : Matrix (Fin d) (Fin d) K) ⟨1, by omega⟩ ⟨1, by omega⟩)⁻¹), rfl⟩, rfl⟩, ?_⟩
    rw [conjAut_proj]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [h2]
    simp only [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]
    rw [slConjugation_transvection_of_diagonal hDdiag h01]

theorem ggINormAbove_dvd [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hpd : p ∣ d) (hd : 2 ≤ d) {r : ℕ} (hr : d - 2 ≤ r + 1) :
    GGINormAbove p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro X hXI hX hcard h4
  obtain ⟨A₀, hA₀⟩ := ggPGLToralityInput_holds p d K hp hp2 hpK hpd X hX hXI
    ((Nat.pow_le_pow_right hp.pos hr).trans hcard)
    ((Nat.pow_le_pow_right hp.pos (by norm_num)).trans h4)
  exact exists_twoSubgroup_of_toral hd hXI hA₀

end IOneMore

open IOneMore TypeA CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem recipeLinear_bstarEqNorm_dvd {d m p : ℕ} (hp : p.Prime) (hpN : p ∣ 2 ^ m - 1)
    (hpm : ¬ p ∣ m) (hd : 2 ≤ d) (hpd : p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d (2 ^ m) Q) :
    LargeEvenRecipeLinear d (2 ^ m) fun R _ I F => Q R I F ∧
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hd3 : 3 ≤ d := hp3.trans (Nat.le_of_dvd (by omega) hpd)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  have hvac : ∀ r, GGInnerDiagBound p r (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) :=
    fun r => ggInnerDiagBound_of_forall_mem fun φ hφ => TypeA.mem_of_congr_recipeEquiv_mem
      (mem_range_conjAut_of_pow hd3 hm hK hp hp2 hpm (by rw [← map_pow, hφ, map_one]))
  rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h3 | h4 | h5
  · subst h3
    have hlift : GGTorusLift p 0 (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) :=
      TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num)))
    exact ⟨⟨0, hlift, hvac 0⟩, 0, hlift, ggINormAbove_of_mulEquiv (TypeA.recipeEquiv 3 K) hI
      (ggINormAbove_dvd hp hp2 hpK hpd (by norm_num) (by norm_num))⟩
  · subst h4
    exfalso
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · have hsec : TypeA.SLHasSections d K := TypeA.slHasSections_of_five_le h5
    have hlift := TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
      (TypeA.ggTorusLift_sub_two hp hpK hd hsec)
    exact ⟨⟨d - 2, hlift, hvac _⟩, d - 2, hlift, ggINormAbove_of_mulEquiv (TypeA.recipeEquiv d K)
      hI (ggINormAbove_dvd hp hp2 hpK hpd hd (by omega))⟩

@[expose] def GGIOneMoreTypeACoprimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1 ∧ ¬ p ∣ lab.n

theorem largeEvenLabelAll_bstarEqNorm_typeACoprime {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreTypeACoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpn, hpl, hpn'⟩ := h
  dsimp only at ht hpn hpl hpn'
  subst ht
  intro Q hQ
  have hl1 : 1 ≤ l := hlab.2.1
  exact recipeLinear_bstarEqNorm_dvd hp hpn hpn' (by omega) hpl hQ

theorem ggStdSubIOneProperInputOn_typeACoprime (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneMoreTypeACoprimeLabel :=
  ggStdSubIOneProperInputOn_of_bstarEqNorm ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_bstarEqNorm_typeACoprime hp hlab h

end CFSG.StandardType
