module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVacLabel
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup

theorem tableBPosition_card_inf_centralizer_le {p : ℕ} (hp : p.Prime) {M : Type} [Group M]
    [Finite M] {L' E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (h : GGTableBPosition p L' E I θ hE) :
    Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) ≤ p := by
  obtain ⟨-, hEel, -, -, hcyc, -, -⟩ := h
  have := Fact.mk hp
  set S : Subgroup M := E ⊓ Subgroup.centralizer (L' : Set M) with hS
  have hSE : S ≤ E ⊔ L' := inf_le_left.trans le_sup_left
  have hSel : IsElemAbelian p S := isElemAbelian_mono hEel inf_le_left
  have hScyc : IsCyclic S := hcyc S hSE inf_le_right (isPGroup_of_isElemAbelian hSel)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
  have h1 : orderOf g = Nat.card S := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ p = 1 := Subtype.ext (hSel.2 g g.2)
  rw [← h1]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one h2)

theorem tableBPosition_pow_three_le_card_range {p : ℕ} (hp : p.Prime) {M : Type} [Group M]
    [Finite M] {L' E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (h : GGTableBPosition p L' E I θ hE) {T : Type} [Group T] (α : ↥E →* T)
    (hker : α.ker ≤ (E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E) :
    p ^ 3 ≤ Nat.card α.range := by
  have hSle := tableBPosition_card_inf_centralizer_le hp h
  obtain ⟨-, -, h4, -⟩ := h
  have hk : Nat.card α.ker ≤ p := by
    have := Subgroup.card_le_of_le hker
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : E ⊓ Subgroup.centralizer (L' : Set M) ≤ E)).toEquiv] at this
    exact this.trans hSle
  have h1 := Subgroup.card_ker_mul_card_range α
  have h3 : p ^ 4 ≤ p * Nat.card α.range :=
    h4.trans (h1 ▸ Nat.mul_le_mul_right _ hk)
  have h5 : p * p ^ 3 ≤ p * Nat.card α.range := by
    have : p * p ^ 3 = p ^ 4 := by rw [← pow_succ']
    omega
  exact Nat.le_of_mul_le_mul_left h5 hp.pos

theorem exists_large_of_tableBPosition {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M]
    {L' E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (h : GGTableBPosition p L' E I θ hE) :
    ∃ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p X ∧
      p ^ 3 ≤ Nat.card X := by
  obtain ⟨hperf, hEel, -, hI, -, -, -⟩ := id h
  have := Fact.mk hp
  set α : ↥E →* MulAut R := (ggLAut L' θ).comp (Subgroup.inclusion hE) with hα
  refine ⟨α.range, ?_, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact hI e
  · exact isElemAbelian_range (fun a b => hEel.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hEel.2 a a.2)) α
  · refine tableBPosition_pow_three_le_card_range hp h α fun b hb => ?_
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf]
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one L' θ hperf (g := ⟨b, hE b.2⟩) hb⟩

theorem exists_large_lift_of_tableBPosition {p : ℕ} (hp : p.Prime) {M : Type} [Group M]
    [Finite M] {L' E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (h : GGTableBPosition p L' E I θ hE) :
    ∃ A : Subgroup (MulAut L'), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A ∧
      ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
  obtain ⟨-, hEel, -, hI, -, -, -⟩ := id h
  have := Fact.mk hp
  set γ : ↥E →* MulAut L' := ggGamma L' hE with hγ
  refine ⟨γ.range, isElemAbelian_range (fun a b => hEel.1.is_comm.comm a b)
    (fun a => Subtype.ext (by simpa using hEel.2 a a.2)) γ, ?_, ?_⟩
  · refine tableBPosition_pow_three_le_card_range hp h γ fun b hb => ?_
    rw [MonoidHom.mem_ker, hγ, ggGamma_eq_one_iff] at hb
    rw [Subgroup.mem_subgroupOf]
    exact ⟨b.2, hb⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L' θ hE b, hI b, fun l => ggBeta_ggQuotHom L' hE θ b l⟩

theorem ggTableBForms_of_noPosition {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (key : ∀ {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
      {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)},
      GGTableBPosition p L' E I θ hE → False) :
    GGCoverPTableB p R I ∧ GGIrredTableB p R I ∧ GGTorusGenTableB p R I ∧
      GGIrredModTableB p R I ∧ GGWPlusTableB p R I :=
  ⟨fun M _ _ L' E θ hE hpos => (key hpos).elim,
    fun M _ _ L' E θ hE hpos => (key hpos).elim,
    fun M _ _ L' E E₁ D' J' d θ hE hpos => (key hpos).elim,
    fun M _ _ L' E θ hE hpos => (key hpos).elim,
    fun M _ _ L' E θ hE hpos => (key hpos).elim⟩

theorem ggTableBForms_of_vac {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I : Set (MulAut R)}
    (hvac : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3) :
    GGCoverPTableB p R I ∧ GGIrredTableB p R I ∧ GGTorusGenTableB p R I ∧
      GGIrredModTableB p R I ∧ GGWPlusTableB p R I := by
  refine ggTableBForms_of_noPosition fun {M _ _ L' E θ hE} hpos => ?_
  obtain ⟨X, hXI, hXel, hX3⟩ := exists_large_of_tableBPosition hp hpos
  exact absurd (hvac X hXI hXel) (not_lt.2 hX3)

theorem ggTableBForms_of_vacLift {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)}
    (hvac : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'),
      IsElemAbelian p A → (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        Nat.card A < p ^ 3) :
    GGCoverPTableB p R I ∧ GGIrredTableB p R I ∧ GGTorusGenTableB p R I ∧
      GGIrredModTableB p R I ∧ GGWPlusTableB p R I := by
  refine ggTableBForms_of_noPosition fun {M _ _ L' E θ hE} hpos => ?_
  obtain ⟨A, hAel, hA3, hAI⟩ := exists_large_lift_of_tableBPosition hp hpos
  obtain ⟨hperf, -⟩ := id hpos
  exact absurd (hvac L' (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf A
    hAel hAI) (not_lt.2 hA3)

theorem ggL48TBVac_ne_two_of_dvd {p n : ℕ} (hn : 1 ≤ n)
    (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases h with h | h <;> omega

theorem ggL48TBVac_ne_two_of_split {p : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab) : p ≠ 2 := by
  obtain ⟨hn, -⟩ := hΛ
  rcases hS with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, rfl⟩
  · exact ggL48TBVac_ne_two_of_dvd hn (Or.inl h)
  · exact ggL48TBVac_ne_two_of_dvd hn (Or.inr h)
  · exact ggL48TBVac_ne_two_of_dvd hn (Or.inl h)
  · norm_num

theorem ggL48TBVac_simple_linear_two {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) ∧
      ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin 2) K), a * b ≠ b * a := by
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  have hna : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    exact Group.IsPerfect.not_isMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      ⟨⟨fun a b => hab a b⟩⟩
  refine ⟨(NbrGraphLinear.recipeEquivTwo K).isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨(NbrGraphLinear.recipeEquivTwo K).symm a, (NbrGraphLinear.recipeEquivTwo K).symm b,
    fun h => hab ?_⟩
  simpa using congrArg (NbrGraphLinear.recipeEquivTwo K) h

theorem largeEvenLabelAll_simple_linearTwo {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGLinearTwoLabel lab) :
    LargeEvenLabelAll lab fun R _ _ _ => IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases h with ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht hl <;> subst ht hl
  · obtain ⟨hn, -, hl22⟩ := hlab
    dsimp only at hn hl22
    have hn2 : 2 ≤ n := hl22 rfl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ggL48TBVac_simple_linear_two ?_) hQ
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  · obtain ⟨hn, -⟩ := hlab
    dsimp only at hn
    simp only [LargeEvenRawDatum, ↓reduceIte] at hQ ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ggL48TBVac_simple_linear_two ?_) hQ
    rw [hK]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2 2

theorem largeEvenLabelAll_card_lt_linearTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGLinearTwoLabel lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 :=
  (largeEvenLabelAll_and (largeEvenLabelAll_autRankLeTwo_linearTwo hp hp2 h)
    (largeEvenLabelAll_simple_linearTwo hlab h)).mono
      fun _ _ _ _ ⟨hrk, hs, hna⟩ X _ hX =>
        (hrk hs hna X hX).trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num))

section Certs

theorem largeEvenLabelAll_tableBForms_l48Vac {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (h : GGL48TableBVacLabel p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I ∧ GGIrredTableB p R I ∧
      GGTorusGenTableB p R I ∧ GGIrredModTableB p R I ∧ GGWPlusTableB p R I := by
  have hp2 : p ≠ 2 := ggL48TBVac_ne_two_of_split hlab hs
  rcases h with h | ⟨ht, hp3⟩ | h | ⟨ht, hl⟩ | h | ⟨ht, hl⟩
  · exact (largeEvenLabelAll_card_lt_corFourTwoSmall hp hlab h hs).mono fun _ _ _ _ hvac =>
      ggTableBForms_of_vac hp hvac
  · subst hp3
    exact (TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of
      (fun a ha K _ _ _ hK _ E hE => TwF4SUThree.ggTwF4ThreeRankInput_holds a ha K hK E hE)
      hp hlab ht hs).mono fun _ _ _ _ hvac => ggTableBForms_of_vac hp hvac
  · exact (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall h).mono
      fun _ _ _ _ hvac => ggTableBForms_of_vac hp hvac
  · exact (largeEvenLabelAll_card_lt_A2_all hp hp2 ht hl).mono fun _ _ _ _ hvac =>
      ggTableBForms_of_vac hp hvac
  · exact (largeEvenLabelAll_card_lt_linearTwo hp hp2 hlab h).mono fun _ _ _ _ hvac =>
      ggTableBForms_of_vac hp hvac
  · exact (largeEvenLabelAll_lift_card_lt_unitaryThree_all hp hp2 hlab ht hl).mono
      fun _ _ _ _ hvac => ggTableBForms_of_vacLift hp hvac

end Certs

end CFSG.StandardType

end
