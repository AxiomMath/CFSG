module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowSp4
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddL28Abstract
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SBasic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec11
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Group

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_le_quasisimple {Y N C : Subgroup G} (hYN : Y ≤ N) (hNC : N ≤ C)
    (hsub : (Y.subgroupOf C).IsSubnormal) (hN : CFSG.IsQuasisimple ↥N) (h3N : 3 ∣ Nat.card N)
    (hp : Group.IsPerfect ↥Y) (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hsN : (Y.subgroupOf N).IsSubnormal := by
    have h := hsub.comap (Subgroup.inclusion hNC)
    have heq : (Y.subgroupOf C).comap (Subgroup.inclusion hNC) = Y.subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsN with h | h
  · exfalso
    apply h3
    have hNY : N ≤ Y := by
      intro x hx
      have : (⟨x, hx⟩ : ↥N) ∈ Y.subgroupOf N := h ▸ Subgroup.mem_top _
      exact this
    exact h3N.trans (Subgroup.card_dvd_of_le hNY)
  ·
    have hcomm : ∀ a b : ↥Y, a * b = b * a := by
      intro a b
      have hb : (⟨b, hYN b.2⟩ : ↥N) ∈ Subgroup.center ↥N := h (show (⟨b, hYN b.2⟩ : ↥N) ∈
        Y.subgroupOf N from b.2)
      apply Subtype.ext
      have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hb) ⟨a, hYN a.2⟩)
      exact this
    have hYY := commutator_self_eq_of_isPerfect hp
    have hbot : ⁅Y, Y⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨x, hx⟩)
    rwa [hYY] at hbot

theorem le_of_commutators_mem {Y N C : Subgroup G} (hYC : Y ≤ C) (hp : Group.IsPerfect ↥Y)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ N) : Y ≤ N := by
  rw [← commutator_self_eq_of_isPerfect hp, Subgroup.commutator_le]
  intro x hx y hy
  exact hcomm x (hYC hx) y (hYC hy)

end Group

theorem eq_bot_of_le_sl2 {G : Type} [Group G] {F : Type} [Field F]
    [Finite F] {M Y : Subgroup G} (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥M) (hYM : Y ≤ M)
    (hp : Group.IsPerfect ↥Y) (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  set f : ↥M →* GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f :=
    Matrix.SpecialLinearGroup.toGL_injective.comp e.symm.injective
  set H : Subgroup (GL (Fin 2) F) := (Y.subgroupOf M).map f with hH
  let eY : ↥(Y.subgroupOf M) ≃* ↥H := (Y.subgroupOf M).equivMapOfInjective f hfinj
  let eY' : ↥Y ≃* ↥(Y.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hYM).symm
  have hHp : Group.IsPerfect ↥H := Group.IsPerfect.ofSurjective (f := (eY'.trans eY).toMonoidHom)
    (eY'.trans eY).surjective
  have hH3 : ¬ 3 ∣ Nat.card H := by
    rwa [← Nat.card_congr (eY'.trans eY).toEquiv]
  have hHb := CFSG.RankThree.PartTwo.Sec6.BThreeCensus.eq_bot_of_isPerfect_of_glTwo H hHp hH3
  rw [eq_bot_iff]
  intro y hy
  have hmem : f ⟨y, hYM hy⟩ ∈ H := ⟨⟨y, hYM hy⟩, hy, rfl⟩
  rw [hHb, Subgroup.mem_bot] at hmem
  have h1 : (⟨y, hYM hy⟩ : ↥M) = 1 := hfinj (by rw [hmem, map_one])
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val h1)

theorem isSimpleGroup_adjointGroup_of_perfect
    (τ : Tag) (k : Type) [Field k] [Finite k]
    (hperf : Group.IsPerfect (adjointGroup τ k)) : IsSimpleGroup (adjointGroup τ k) := by
  have hnc := (opposite_simple_root_noncommutativity τ k).2.2.1
  have : Nontrivial (adjointGroup τ k) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  refine IsSimpleGroup.mk fun M hM => ?_
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center (adjointGroup τ k) := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := (noncentral_normal_solvable_quotient τ k M hnot).2.1
    by_contra htop
    have : Nontrivial (adjointGroup τ k ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

theorem noSz_centralizer_of_conj {S : Type} [Group S] [Finite S] (g z : S)
    (h : ∀ Y : Subgroup S, Y ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set S) →
      (Y.subgroupOf (Subgroup.centralizer ({g * z * g⁻¹} : Set S))).IsSubnormal →
      Group.IsPerfect ↥Y → ¬ 3 ∣ Nat.card Y → Y = ⊥)
    (Y : Subgroup S) (hY : Y ≤ Subgroup.centralizer ({z} : Set S))
    (hsn : (Y.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal)
    (hp : Group.IsPerfect ↥Y) (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  set φ : S ≃* S := MulAut.conj g with hφ
  set C := Subgroup.centralizer ({z} : Set S) with hCdef
  have hCφ : C.map (φ : S →* S) = Subgroup.centralizer ({g * z * g⁻¹} : Set S) := by
    rw [hCdef, Ronan148S.map_centralizer_singleton_equiv φ z]
    rfl
  have hYφ : Y.map (φ : S →* S) ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set S) := by
    rw [← hCφ]
    exact Subgroup.map_mono hY
  let eC : ↥C ≃* ↥(C.map (φ : S →* S)) := C.equivMapOfInjective _ φ.injective
  have heq : (Y.subgroupOf C).map (eC : ↥C →* ↥(C.map (φ : S →* S))) =
      (Y.map (φ : S →* S)).subgroupOf (C.map (φ : S →* S)) := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨y, hyY, hyx⟩
      refine ⟨y, hyY, ?_⟩
      have := congrArg Subtype.val hyx
      simpa [eC] using this
    · rintro ⟨y, hyY, rfl⟩
      refine ⟨⟨y, hY hyY⟩, hyY, Subtype.ext ?_⟩
      simp [eC]
  have hsn' : ((Y.map (φ : S →* S)).subgroupOf (C.map (φ : S →* S))).IsSubnormal := by
    rw [← heq]
    exact hsn.map eC.surjective
  rw [hCφ] at hsn'
  have eY : ↥Y ≃* ↥(Y.map (φ : S →* S)) := Y.equivMapOfInjective _ φ.injective
  have hp' : Group.IsPerfect ↥(Y.map (φ : S →* S)) :=
    Group.IsPerfect.ofSurjective (f := eY.toMonoidHom) eY.surjective
  have h3' : ¬ 3 ∣ Nat.card (Y.map (φ : S →* S)) := by
    rwa [← Nat.card_congr eY.toEquiv]
  have hb := h _ hYφ hsn' hp' h3'
  rwa [Subgroup.map_eq_bot_iff_of_injective _ φ.injective] at hb

section G2Two


theorem three_dvd_card_g2_two {k : Type} [Field k] [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m)
    (hm : 1 ≤ m) : 3 ∣ Nat.card (adjointGroup Tag.G2 k) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  unfold CFSG.Open.ordG2
  refine Dvd.dvd.mul_left ?_ _
  have h : 3 ∣ (2 ^ m) ^ 2 - 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) m
  exact h

theorem eq_bot_of_le_g2Two {G : Type} [Group G] [Finite G] {k : Type} [Field k] [Finite k] {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m) {C Y : Subgroup G} (eC : ↥C ≃* adjointGroup Tag.G2 k)
    (hYC : Y ≤ C) (hsub : (Y.subgroupOf C).IsSubnormal) (hp : Group.IsPerfect ↥Y)
    (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hcardC : Nat.card C = CFSG.Open.ordG2 (2 ^ m) := by
    rw [Nat.card_congr eC.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  ·
    have hdvd : Nat.card Y ∣ 2 ^ 6 * 7 ^ 1 := by
      have h1 : Nat.card Y ∣ 12096 := by
        have := Subgroup.card_dvd_of_le hYC
        rw [hcardC] at this
        simpa [CFSG.Open.ordG2] using this
      have hcop : Nat.Coprime (Nat.card Y) (3 ^ 3) := by
        refine Nat.Coprime.pow_right 3 ?_
        exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
      have h2 : Nat.card Y ∣ 3 ^ 3 * (2 ^ 6 * 7 ^ 1) := by norm_num; exact h1
      exact hcop.dvd_of_dvd_mul_left h2
    have hpf := RonanK429H.primeFactors_card_le_two_of_dvd Nat.prime_two (by norm_num) hdvd
    haveI := hp
    haveI := RonanK429H.subsingleton_of_isPerfect_of_card_primeFactors hpf
    exact Subgroup.eq_bot_of_subsingleton Y
  · have hk3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    haveI hS : IsSimpleGroup (adjointGroup .G2 k) :=
      isSimpleGroup_adjointGroup_of_perfect .G2 k
        (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card k hk3)
    have hCs : IsSimpleGroup C := eC.isSimpleGroup
    by_contra hne
    have hYC' : Y = C := RonanK429Lie.eq_of_subnormal_of_le_simple hYC le_rfl hsub hCs hne
    apply h3
    rw [hYC', Nat.card_congr eC.toEquiv]
    exact three_dvd_card_g2_two hk (by omega)

theorem g2Two_noSz {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) :
    ∀ β : MulAut (adjointGroup Tag.G2 F), β ^ 3 = 1 → ∀ C Y : Subgroup (adjointGroup Tag.G2 F),
      (∀ z, z ∈ C ↔ β z = z) → Y ≤ C → (Y.subgroupOf C).IsSubnormal → Group.IsPerfect ↥Y →
      ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  intro β hβ C Y hC hYC hsub hp h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F = 2 := by
    have := Fintype.ofFinite F
    have hp2 : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card, hF])
    exact ringChar.eq F 2
  have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hZ : Subgroup.center (adjointGroup Tag.G2 F) = ⊥ := center_adjointGroup_eq_bot
  by_cases hβ1 : β = 1
  · subst hβ1
    have hCtop : C = ⊤ := Subgroup.ext fun z => by simp [hC]
    subst hCtop
    exact eq_bot_of_le_g2Two hF (by omega) Subgroup.topEquiv hYC hsub hp h3
  by_cases hin : IsInnerAut β
  · obtain ⟨z, rfl⟩ := hin
    have hCz : C = Subgroup.centralizer ({z} : Set (adjointGroup Tag.G2 F)) := by
      ext x
      rw [hC, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
      constructor
      · intro h
        calc x * z = z * x * z⁻¹ * z := by rw [h]
          _ = z * x := by group
      · intro h
        rw [← h]
        group
    subst hCz
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact hβ1 (by rw [map_one])
    have hz3 : z ^ 3 = 1 := by
      have hc : MulAut.conj (z ^ 3) = 1 := by rw [map_pow, hβ]
      have hmem : z ^ 3 ∈ Subgroup.center (adjointGroup Tag.G2 F) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg := congrArg (fun φ : MulAut (adjointGroup Tag.G2 F) => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at hg
        calc g * z ^ 3 = z ^ 3 * g * (z ^ 3)⁻¹ * z ^ 3 := by rw [hg]
          _ = z ^ 3 * g := by group
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds F hchar3 h4 z hz3 hz1
    refine noSz_centralizer_of_conj g z ?_ Y hYC hsub hp h3
    intro Y' hY' hsn' hp' h3'
    have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz3, map_one]
    have hz'1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : MulAut.conj g z = MulAut.conj g 1 := by rw [map_one]; exact h
      exact (MulAut.conj g).injective this
    rcases hg with hS | hM
    ·
      obtain ⟨N, hNC, hcomm, hNq, x, hxN, hxc, hx1, hx3⟩ :=
        KS11Lie7Proof.g2ThreeACent_holds F hchar3 h4 _ hS hz'3 hz'1
      have hYN := le_of_commutators_mem hY' hp' hcomm
      have h3N : 3 ∣ Nat.card N := by
        have hxo : orderOf (⟨x, hxN⟩ : ↥N) = 3 := by
          have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
          refine orderOf_eq_prime (Subtype.ext (by simpa using hx3)) ?_
          intro h
          exact hx1 (congrArg Subtype.val h)
        rw [← hxo]
        exact orderOf_dvd_natCard _
      exact eq_bot_of_le_quasisimple hYN hNC hsn' hNq h3N hp' h3'
    ·
      obtain ⟨hcomm, -⟩ := KS11Lie4Proof.g2ThreeBCent_holds F hchar3 h4 _ hM hz'3 hz'1
      have hYM := le_of_commutators_mem hY' hp' hcomm
      obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := F)
      exact eq_bot_of_le_sl2 e hYM hp' h3'
  ·
    obtain ⟨φ, hφ, k, hβk⟩ := g2_order_three_field_descent hchar3 h4 hβ hin
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ
    obtain ⟨m, rfl⟩ := h3n
    have hcard : Nat.card (fixSubfield φ) = 2 ^ m := by
      have h := card_fixSubfield_pow φ
      rw [hφ, hF, show 2 ^ (3 * m) = (2 ^ m) ^ 3 by rw [← pow_mul, mul_comm]] at h
      exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
    have hfixeq : Sec4.autFix (g2FieldHom F φ) = (g2Incl φ).range := by
      ext h
      rw [Sec4.mem_autFix, mem_range_g2Incl_iff hchar φ]
    have hCeq : C = Sec4.autFix β := Subgroup.ext fun z => (hC z).trans Sec4.mem_autFix.symm
    have eα : Sec4.autFix β ≃* adjointGroup Tag.G2 (fixSubfield φ) := by
      rw [hβk]
      exact ((RonanK429Lie.autFixConjEquiv (MulAut.conj k) (g2FieldHom F φ)).trans
        (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (g2Incl_injective φ)).symm
    subst hCeq
    exact eq_bot_of_le_g2Two hcard (by omega) eα hYC hsub hp h3

theorem isSolvable_outer_g2Two {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) : Group.IsSolvable (Outer (adjointGroup Tag.G2 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hdC : ∀ a : Fin Tag.G2.rank → Fˣ, rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 F :=
    fun a => by
      obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner Tag.G2 (Or.inl rfl) F
      exact (hrest B hB a).2.2.1
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ := inner_field_automorphism_normal_form_of_params
    Nat.prime_two (by omega) hF (fun β hβ => even_G2_exists_exactNormalAut_zero_eq h4 hβ) hdC
  let φ : Outer (adjointGroup Tag.G2 F) ≃* (F ≃+* F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  haveI : IsCyclic (F ≃+* F) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  exact Group.isSolvable_of_comm fun a b => φ.injective (by
    rw [map_mul, map_mul]
    exact (IsCyclic.commGroup (α := F ≃+* F)).mul_comm _ _)

theorem kT1_seven_G2 (q : PrimePower) (hq2 : q.p = 2) (hq : (LieTypeIndex.G2 q).Valid) :
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro S _ _ hs hna ⟨e⟩ _
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hq
  have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1
  have hKn : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq2]
  have hn : 2 ≤ q.exponent := by
    by_contra h
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [TauCeti.PrimePower.card_def, hq2, h1] at hq3
    norm_num at hq3
  let τ : S ≃* adjointGroup Tag.G2 K := e.trans eK
  have hOut : Group.IsSolvable (Outer S) := by
    have := isSolvable_outer_g2Two hKn hn
    exact solvable_of_surjective (f := (equivalence τ).symm.toMonoidHom)
      (equivalence τ).symm.surjective
  refine row143_of_inner_kgroup hs hna
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOut P hPp)
    fun β hβ Y hY hsn _ hp h3Y => ?_
  exact sp4R148_bot_of_mulEquiv τ (g2Two_noSz hKn hn) β hβ (Sec4.autFix β) Y (fun z => Iff.rfl)
    hY hsn hp h3Y

end G2Two

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
