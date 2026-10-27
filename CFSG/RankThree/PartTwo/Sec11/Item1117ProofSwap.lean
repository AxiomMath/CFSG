module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Proof
import CFSG.RankThree.PartTwo.Sec4.Item413Orders

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Statements

@[expose] def Gap1117SymmetrySwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      g * x * g⁻¹ * x⁻¹ ∈ A → g * x * g⁻¹ * x⁻¹ ∉ Subgroup.closure {c, d} →
      (∀ a' ∈ Subgroup.closure ({g * x * g⁻¹ * x⁻¹, d} : Set G), a' ∉ Subgroup.zpowers d →
        ∀ Y' ∈ thetaComponentsAt 3 a', sec11K L a' ≤ Y' → KFacts.InducesStdKind Y' c .field) →
      ∀ (Ye R' Y'' : Subgroup G), Ye ∈ thetaComponentsAt 3 (g * x * g⁻¹ * x⁻¹) →
        sec11K L (g * x * g⁻¹ * x⁻¹) ≤ Ye →
        Sec11Std G A (g * x * g⁻¹ * x⁻¹) Ye c R' Y'' → False

end Statements

namespace Item1117Proof

theorem isSolvable_projSL_two_two :
    Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 1)) := by
  have : Finite (CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 1)) :=
    Finite.of_equiv _ (Sec4.projSLEquivPSLn 2 (GaloisField 2 1)).symm.toEquiv
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h1 := Sec4.card_projSL_dvd 2 (GaloisField 2 1)
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)] at h1
  norm_num [Fin.prod_univ_succ] at h1
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 (h1.trans (by norm_num : 6 ∣ 2 ^ 1 * 3 ^ 1))
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype (CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 1)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem hyp81_swap (h45 : Sec4.Item4_5) (h118 : Item118) (h : Sec11Data G A c L a R Y d x s r g)
    {a' : G} (ha'A : a' ∈ A) (ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 a') (hKY' : sec11K L a' ≤ Y')
    (hf : KFacts.InducesStdKind Y' c .field) : Sec8.Hyp81 G A a' Y' c := by
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq ha'A ha'cd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha'A ha'cd
  exact
    { toPartTwoStanding := h.toPartTwoStanding
      mem_partTwoF := h.mem_partTwoF
      mem_A := ha'A
      ne_one := hstd.a_ne_one
      mem_thetaComponentsAt := hY'
      sectionCentralizer_eq := (h118 G A c L a' R Y' hstd d g h.inf_eq hA' h.g_mem.2 h.g_not_mem
        h.conj_mem).2.2
      a_mem := h.mem_A
      a_ne_one := h.ne_one
      inducesStdKind := Or.inl hf
      exists_invariant_two := fun h27 => absurd h.card_eq (Nat.ne_of_gt h27)
      partTwoE_eq := h.partTwoE_eq }

theorem notSmall_swap (h45 : Sec4.Item4_5) (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) {a' : G} (ha'A : a' ∈ A)
    (ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 a') (hKY' : sec11K L a' ≤ Y')
    (hf : KFacts.InducesStdKind Y' c .field) :
    ¬ Nonempty (Y' ⧸ aschbacherSolvableCore 3 Y' ≃*
        CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) ∧
      ¬ Sec4.IsSLThreePiAt (Y' ⧸ aschbacherSolvableCore 3 Y') 8 := by
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq ha'A ha'cd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha'A ha'cd
  have hK := mem_thetaComponentsIn_sec11K_inf hstd
  have hT := kType119 G A c L a' R Y' hstd d h.inf_eq hA'
  have hc3 : c ^ 3 = 1 := pow_three_of_mem_A h h.mem_A
  refine ⟨?_, fun h8 => ?_⟩
  · rintro ⟨e8⟩
    have h81 := hyp81_swap h45 h118 h ha'A ha'cd hY' hKY' hf
    have hcN := h81.a_mem_normalizer
    set τ := Sec4.thetaQuotMulAut Y' (Sec4.compAction Y' ⟨c, hcN⟩) with hτ
    have hτ3 : τ ^ 3 = 1 := by
      have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (Y' : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hc3)
      rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
    have hout : ¬ KFacts.IsInnerAut τ := h81.not_isInnerAut_induced
    obtain ⟨eC⟩ := KFacts.nonempty_eqLocus_mulEquiv_projSL_two (p := 2) (m := 1) le_rfl e8 hτ3
      hout
    have hsolv : Group.IsSolvable (τ.toMonoidHom.eqLocus
        (MonoidHom.id (Y' ⧸ aschbacherSolvableCore 3 Y'))) := by
      have := isSolvable_projSL_two_two
      exact Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
    exact fieldCent_false_of_isSolvable hcN hc3 hK hsolv
  · exact FieldCentRigid82.false_of_isSLThreePiAt (m := 1) le_rfl (by norm_num; exact h8) hf hc3
      hK hT

theorem hyp91_swap (h45 : Sec4.Item4_5) (h118 : Item118) (h : Sec11Data G A c L a R Y d x s r g)
    {a' : G} (ha'A : a' ∈ A) (ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 a') (hKY' : sec11K L a' ≤ Y')
    (hf : KFacts.InducesStdKind Y' c .field) {R' : Subgroup G}
    (hR' : IsSylowOf 3 R' (Subgroup.normalizer (Subgroup.zpowers a' : Set G)))
    (hR'W : IsSylowOf 3 (R' ⊓ Subgroup.normalizer (A : Set G))
      (Subgroup.normalizer (Subgroup.zpowers a' : Set G) ⊓ Subgroup.normalizer (A : Set G))) :
    Sec9.Hyp91 G A a' Y' c R' where
  toHyp81 := hyp81_swap h45 h118 h ha'A ha'cd hY' hKY' hf
  card_eq := h.card_eq
  invTwo_or_commutator := Or.inr (notSmall_swap h45 h118 h ha'A ha'cd hY' hKY' hf)
  isSylowOf := hR'
  isSylowOf_inf := hR'W
  not_mem_partTwoT_or_mem_partTwoS := h.not_mem_partTwoT_or_mem_partTwoS

theorem exists_sec11Std_swap (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h118 : Item118) (h1016 : Sec10.Item1016) (h : Sec11Data G A c L a R Y d x s r g) {a' : G}
    (ha'A : a' ∈ A) (ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 a') (hKY' : sec11K L a' ≤ Y')
    (hf : KFacts.InducesStdKind Y' c .field) :
    ∃ R' Y'' : Subgroup G, Sec11Std G A a' Y' c R' Y'' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R', hR', hR'W⟩ := exists_isSylowOf_inf 3
    (Subgroup.normalizer (Subgroup.zpowers a' : Set G)) (Subgroup.normalizer (A : Set G))
  have hswap := hyp91_swap h45 h118 h ha'A ha'cd hY' hKY' hf hR' hR'W
  have hl := h1016 G A a' Y' c R' hswap
  obtain ⟨h3, hd⟩ := h97 G A a' Y' c R' hswap
  obtain ⟨d', hd'⟩ := exists_zpowers_eq_inf h3
  have hA'' := hd d' hd'
  have hd'A : d' ∈ A := by
    have : d' ∈ A ⊓ Y' := by
      rw [hd']
      exact Subgroup.mem_zpowers d'
    exact this.1
  obtain ⟨Y'', hY'', hKY''⟩ := exists_mem_thetaComponentsAt_sec11K_le_hyp91 h45 h48 hswap hl hd'
    hA'' h.mem_A (a_not_mem_closure_of_hyp91 hswap hd'A hA'')
  exact ⟨R', Y'',
    { toHyp91 := hswap
      isList1016 := hl
      mem_thetaComponentsAt_Y := hY''
      sec11K_le := hKY'' }⟩

end Data

end Item1117Proof

section Main

open Item1117Proof in
theorem gap1117Symmetry_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h118 : Item118) (h1016 : Sec10.Item1016) (hsw : Gap1117SymmetrySwap) : Gap1117Symmetry := by
  intro G _ _ A c L a R Y d x s r g h hsc hrs heA hecd
  by_contra hne
  push Not at hne
  have hsym : ∀ a' ∈ Subgroup.closure ({g * x * g⁻¹ * x⁻¹, d} : Set G),
      a' ∉ Subgroup.zpowers d → ∀ Y' ∈ thetaComponentsAt 3 a', sec11K L a' ≤ Y' →
        KFacts.InducesStdKind Y' c .field := by
    intro a' ha' had Y' hY' hKY'
    by_contra hnf
    exact hne a' ha' had ⟨Y', hY', hKY', hnf⟩
  obtain ⟨Ye, hYe, hKYe⟩ := exists_mem_thetaComponentsAt_sec11K_le_hyp91 h45 h48 h.toHyp91
    h.isList1016 h.inf_eq h.closure_eq heA hecd
  have hed : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.closure ({g * x * g⁻¹ * x⁻¹, d} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hnd : g * x * g⁻¹ * x⁻¹ ∉ Subgroup.zpowers d := fun hd =>
    hecd (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hd)
  have hf := hsym _ hed hnd Ye hYe hKYe
  obtain ⟨R', Y'', hstd⟩ := exists_sec11Std_swap h45 h48 h97 h118 h1016 h heA hecd hYe hKYe hf
  exact hsw G A c L a R Y d x s r g h hsc hrs heA hecd hsym Ye R' Y'' hYe hKYe hstd

theorem item1117_of_swap (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119) (h82 : Sec8.Item82One)
    (h1016 : Sec10.Item1016) (hNA : Gap1117NotActX) (hsw : Gap1117SymmetrySwap)
    (hND : KFact1117Cube) : Item1117 :=
  item1117_of h45 h113 h117 h118 h119 h82 hNA (gap1117Symmetry_of h45 h48 h97 h118 h1016 hsw) hND

end Main

end CFSG.RankThree.PartTwo.Sec11
