module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FAbstract
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FDecomp
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FRational
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL7
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.RankThree.PartOne.CTP (slSub mem_slSub)

section Setup

variable {F : Type} [Field F]

noncomputable abbrev fieldLine (H : GL (Fin 3) F) (σ : F ≃+* F) : MulAut (projectiveSL 3 F) :=
  conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹

@[expose] noncomputable def lineSub (H : GL (Fin 3) F) (k : Subfield F) : Subgroup (projectiveSL 3 F) :=
  ((slSub 3 k).map (slConjugation 3 F H).toMonoidHom).map (proj 3 F)

theorem mem_lineSub {H : GL (Fin 3) F} {k : Subfield F} {x : projectiveSL 3 F} :
    x ∈ lineSub H k ↔ ∃ S ∈ slSub 3 k, proj 3 F (slConjugation 3 F H S) = x := by
  constructor
  · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨S, hS, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨_, ⟨S, hS, rfl⟩, rfl⟩

end Setup

section Decomposition

variable {F : Type} [Field F] [Finite F]

theorem not_le_linearAutGroup_of_card (h3 : (3 : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 F))} (hE : IsElemAbelian 3 E) (hc : 9 < Nat.card E) :
    ¬ E ≤ linearAutGroup 3 F := by
  intro hL
  have h9 := Sec4.card_inf_linearAutGroup_three_le h3 hE
  rw [inf_eq_left.mpr hL] at h9
  omega

theorem card_le_three_mul_card_inf_linear (h3 : (3 : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 F))} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ linearAutGroup 3 F : Subgroup _) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' F
  have hcycK := (card_ringAut_and_isCyclic hp F (by rw [Nat.card_eq_fintype_card, hK])).2
  have hcyc : IsCyclic (fieldAut 3 F).range :=
    isCyclic_of_surjective (fieldAut 3 F).rangeRestrict (fieldAut 3 F).rangeRestrict_surjective
  have hCN : (fieldAut 3 F).range ≤
      Subgroup.normalizer
        ((linearAutGroup 3 F : Subgroup _) : Set (MulAut (projectiveSL 3 F))) := by
    have key : ∀ σ : F ≃+* F, ∀ x ∈ linearAutGroup 3 F,
        fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹ ∈ linearAutGroup 3 F := by
      intro σ x hx
      rw [Sec4.linearAutGroup_three_eq_range] at hx ⊢
      obtain ⟨A, rfl⟩ := hx
      refine ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) A, ?_⟩
      rw [fieldAut_mul_conjAut, mul_inv_cancel_right]
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key σ x, fun hx => ?_⟩
    have h := key σ⁻¹ (fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹) hx
    rw [map_inv] at h
    have e : (fieldAut 3 F σ)⁻¹ * (fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹) *
        ((fieldAut 3 F σ)⁻¹)⁻¹ = x := by group
    rw [e] at h
    exact h
  have hBNC : ∀ b ∈ E, ∃ n ∈ linearAutGroup 3 F, ∃ c ∈ (fieldAut 3 F).range, b = n * c := by
    intro b hb
    by_cases hbN : b ∈ linearAutGroup 3 F
    · exact ⟨b, hbN, 1, one_mem _, (mul_one b).symm⟩
    · obtain ⟨σ, -, H, hH⟩ :=
        KFacts.linear_order_three_field_descent (by norm_num) b (hE.2 b hb) hbN
      refine ⟨conjAut 3 F H * conjAut 3 F (Matrix.GeneralLinearGroup.map (σ : F →+* F) H⁻¹),
        ?_, fieldAut 3 F σ, ⟨σ, rfl⟩, ?_⟩
      · rw [Sec4.linearAutGroup_three_eq_range]
        exact ⟨_, map_mul _ _ _⟩
      · rw [hH, ← map_inv, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc]
  exact Sec4.card_le_three_mul_card_inf hE hcyc hCN hBNC

theorem card_inf_linearAutGroup_eq_nine (h3 : (3 : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 F))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    Nat.card (E ⊓ linearAutGroup 3 F : Subgroup _) = 9 := by
  have h1 := card_le_three_mul_card_inf_linear h3 hE
  have h2 := Sec4.card_inf_linearAutGroup_three_le h3 hE
  omega

theorem exists_eq_mul_zpow (h3 : (3 : F) ≠ 0) {E : Subgroup (MulAut (projectiveSL 3 F))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) {φ : MulAut (projectiveSL 3 F)}
    (hφE : φ ∈ E) (hφN : φ ∉ linearAutGroup 3 F) :
    ∀ e ∈ E, ∃ b ∈ E ⊓ linearAutGroup 3 F, ∃ a : ℤ, e = b * φ ^ a :=
  exists_eq_mul_zpow_of_card hE hc (card_inf_linearAutGroup_eq_nine h3 hE hc) hφE hφN

end Decomposition

section Claim4

variable {F : Type} [Field F] [Finite F]

theorem exists_rational_rep {σ : F ≃+* F} (hσ : orderOf σ = 3) {k : Subfield F}
    (hk : ∀ x, x ∈ k ↔ σ x = x) {g₁ : GL (Fin 3) F}
    (h : conjAut 3 F g₁ * fieldAut 3 F σ = fieldAut 3 F σ * conjAut 3 F g₁) :
    ∃ (u : Fˣ) (g' : GL (Fin 3) F), g₁ = GeneralLinearGroup.scalar (Fin 3) u * g' ∧
      ∀ i j, (g' : Matrix (Fin 3) (Fin 3) F) i j ∈ k := by
  have h1 : conjAut 3 F g₁ = conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) g₁) := by
    have h2 := fieldAut_mul_conjAut (n := 3) σ g₁
    exact mul_right_cancel (h.trans h2)
  have h2 : conjAut 3 F (g₁⁻¹ * GeneralLinearGroup.map (σ : F →+* F) g₁) = 1 := by
    rw [map_mul, map_inv, ← h1, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).1 h2
  have hmap : GeneralLinearGroup.map (σ : F →+* F) g₁ = g₁ * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hc]
    group
  exact exists_rational_rep_of_map hσ hk hmap

omit [Finite F] in
theorem slConjugation_scalar_one (u : Fˣ) :
    slConjugation 3 F (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext g : 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]
  rfl

omit [Finite F] in
theorem slConjugation_scalar_mul (u : Fˣ) (g : GL (Fin 3) F) :
    slConjugation 3 F (GeneralLinearGroup.scalar (Fin 3) u * g) = slConjugation 3 F g := by
  rw [map_mul, slConjugation_scalar_one, one_mul]

omit [Finite F] in
theorem mem_slSub_iff_map {σ : F ≃+* F} {k : Subfield F} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {S : SpecialLinearGroup (Fin 3) F} :
    S ∈ slSub 3 k ↔ (S : Matrix (Fin 3) (Fin 3) F).map σ = S := by
  rw [mem_slSub]
  constructor
  · intro h
    ext i j
    exact (hk _).1 (h i j)
  · intro h i j
    exact (hk _).2 (congrFun (congrFun h i) j)

omit [Finite F] in
theorem slConjugation_mem_slSub {σ : F ≃+* F} {k : Subfield F} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {g' : GL (Fin 3) F} (hg' : ∀ i j, (g' : Matrix (Fin 3) (Fin 3) F) i j ∈ k)
    {S : SpecialLinearGroup (Fin 3) F} (hS : S ∈ slSub 3 k) :
    slConjugation 3 F g' S ∈ slSub 3 k := by
  have hg'm : (g' : Matrix (Fin 3) (Fin 3) F).map σ = g' := by
    ext i j
    exact (hk _).1 (hg' i j)
  have hinv := inv_map_eq_of_map_eq hg'm
  rw [mem_slSub_iff_map hk] at hS ⊢
  rw [coe_slConjugation]
  rw [Matrix.map_mul, Matrix.map_mul, hg'm, hS, hinv]

theorem normalizes_lineSub {σ : F ≃+* F} (hσ : orderOf σ = 3) {k : Subfield F}
    (hk : ∀ x, x ∈ k ↔ σ x = x) {H : GL (Fin 3) F} {b : MulAut (projectiveSL 3 F)}
    (hbN : b ∈ linearAutGroup 3 F) (hcomm : b * fieldLine H σ = fieldLine H σ * b)
    {S : SpecialLinearGroup (Fin 3) F} (hS : S ∈ slSub 3 k) :
    ∃ S' ∈ slSub 3 k,
      b (proj 3 F (slConjugation 3 F H S)) = proj 3 F (slConjugation 3 F H S') := by
  rw [Sec19.linearAutGroup_eq_range_conjAut] at hbN
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hbN
  have hc1 : conjAut 3 F (H⁻¹ * g * H) * fieldAut 3 F σ =
      fieldAut 3 F σ * conjAut 3 F (H⁻¹ * g * H) := by
    simp only [map_mul, map_inv]
    set a := conjAut 3 F H
    set b := conjAut 3 F g
    set f := fieldAut 3 F σ
    calc (a⁻¹ * b * a) * f = a⁻¹ * (b * (a * f * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * f * a⁻¹) * b) * a := by rw [hcomm]
      _ = f * (a⁻¹ * b * a) := by group
  obtain ⟨u, g', hg₁, hg'k⟩ := exists_rational_rep hσ hk hc1
  refine ⟨slConjugation 3 F g' S, slConjugation_mem_slSub hk hg'k hS, ?_⟩
  have hgH : g * H = H * (GeneralLinearGroup.scalar (Fin 3) u * g') := by
    rw [← hg₁]
    group
  rw [conjAut_proj, ← MulAut.mul_apply, ← map_mul, hgH, map_mul,
    slConjugation_scalar_mul, MulAut.mul_apply]

end Claim4

section LineProps

variable {F : Type} [Field F] [Finite F]

theorem fieldLine_fixes_lineSub {σ : F ≃+* F} {k : Subfield F} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {H : GL (Fin 3) F} {l : projectiveSL 3 F} (hl : l ∈ lineSub H k) :
    fieldLine H σ l = l := by
  obtain ⟨S, hS, rfl⟩ := mem_lineSub.1 hl
  exact Sec19.fixed_conjSub_of_fieldAut hk hS

theorem lineSub_invariant (h3 : (3 : F) ≠ 0) {E : Subgroup (MulAut (projectiveSL 3 F))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {k : Subfield F} (hk : ∀ x, x ∈ k ↔ σ x = x) {H : GL (Fin 3) F}
    (hφE : fieldLine H σ ∈ E) (hφN : fieldLine H σ ∉ linearAutGroup 3 F) :
    ∀ e ∈ E, ∀ l ∈ lineSub H k, e l ∈ lineSub H k := by
  intro e he l hl
  obtain ⟨b, hb, a, rfl⟩ := exists_eq_mul_zpow h3 hE hc hφE hφN e he
  have hfix : (fieldLine H σ ^ a) l = l := zpow_apply_eq_of_fixes (fieldLine_fixes_lineSub hk hl) a
  rw [MulAut.mul_apply, hfix]
  obtain ⟨S, hS, rfl⟩ := mem_lineSub.1 hl
  have hcomm : b * fieldLine H σ = fieldLine H σ * b := by
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨b, hb.1⟩ : E) ⟨_, hφE⟩)
  obtain ⟨S', hS', hbS⟩ := normalizes_lineSub hσ hk hb.2 hcomm hS
  rw [hbS]
  exact mem_lineSub.2 ⟨S', hS', rfl⟩

theorem lineSub_ker (h3 : (3 : F) ≠ 0) {E : Subgroup (MulAut (projectiveSL 3 F))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) {σ : F ≃+* F}
    {k : Subfield F} (hk : ∀ x, x ∈ k ↔ σ x = x) {H : GL (Fin 3) F}
    (hφE : fieldLine H σ ∈ E) (hφN : fieldLine H σ ∉ linearAutGroup 3 F) :
    ∀ e ∈ E, (∀ l ∈ lineSub H k, e l = l) → e ∈ Subgroup.zpowers (fieldLine H σ) := by
  intro e he hfix
  obtain ⟨b, hb, a, rfl⟩ := exists_eq_mul_zpow h3 hE hc hφE hφN e he
  have hb1 : b = 1 := by
    refine Sec19.eq_one_of_fixes_conj_slSub h3 (k := k) (H := H) hb.2 fun S hS => ?_
    have hl : proj 3 F (slConjugation 3 F H S) ∈ lineSub H k := mem_lineSub.2 ⟨S, hS, rfl⟩
    have h1 := hfix _ hl
    rw [MulAut.mul_apply, zpow_apply_eq_of_fixes (fieldLine_fixes_lineSub hk hl) a] at h1
    exact h1
  rw [hb1, one_mul]
  exact Subgroup.zpow_mem_zpowers _ a

end LineProps

section Iso

variable {F : Type} [Field F]

@[expose] noncomputable def subMap (k : Subfield F) :
    SpecialLinearGroup (Fin 3) k →* SpecialLinearGroup (Fin 3) F :=
  SpecialLinearGroup.map (k.subtype : k →+* F)

theorem subMap_apply_coe (k : Subfield F) (S : SpecialLinearGroup (Fin 3) k) (i j : Fin 3) :
    ((subMap k S : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
      ((S : Matrix (Fin 3) (Fin 3) k) i j : F) := by
  simp [subMap, SpecialLinearGroup.map_apply_coe]

@[expose] noncomputable def Psi (H : GL (Fin 3) F) (k : Subfield F) :
    SpecialLinearGroup (Fin 3) k →* projectiveSL 3 F :=
  (proj 3 F).comp ((slConjugation 3 F H).toMonoidHom.comp (subMap k))

theorem range_Psi (H : GL (Fin 3) F) (k : Subfield F) : (Psi H k).range = lineSub H k := by
  ext x
  constructor
  · rintro ⟨S, rfl⟩
    exact mem_lineSub.2 ⟨subMap k S, ⟨S, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨T, ⟨S, rfl⟩, rfl⟩ := mem_lineSub.1 hx
    exact ⟨S, rfl⟩

theorem Psi_eq_one_of_mem_scalars (H : GL (Fin 3) F) (k : Subfield F)
    {S : SpecialLinearGroup (Fin 3) k} (hS : S ∈ scalars 3 k) : Psi H k S = 1 := by
  obtain ⟨c, hc3, hSc⟩ := hS
  set T := subMap k S with hT
  have hTm : (T : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) ((c : k) : F) := by
    ext i j
    rw [hT, subMap_apply_coe, hSc]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hconj : slConjugation 3 F H T = T := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_slConjugation, hTm]
    have hcomm : Commute (Matrix.scalar (Fin 3) ((c : k) : F)) (H : Matrix (Fin 3) (Fin 3) F) :=
      Matrix.scalar_commute _ (fun r' => Commute.all _ r') _
    rw [← hcomm.eq, mul_assoc, Units.mul_inv, mul_one]
  show proj 3 F (slConjugation 3 F H T) = 1
  rw [hconj, proj_eq_one_iff]
  refine ⟨Units.map (k.subtype : k →* F) c, ?_, hTm⟩
  rw [← map_pow, hc3, map_one]

theorem mem_scalars_of_Psi_eq_one (H : GL (Fin 3) F) (k : Subfield F)
    {S : SpecialLinearGroup (Fin 3) k} (h : Psi H k S = 1) : S ∈ scalars 3 k := by
  set T := subMap k S with hT
  have h1 : proj 3 F (slConjugation 3 F H T) = 1 := h
  obtain ⟨c', hc3, hcT⟩ := proj_eq_one_iff.1 h1
  set A : Matrix (Fin 3) (Fin 3) F := (H : Matrix (Fin 3) (Fin 3) F) with hA
  set B : Matrix (Fin 3) (Fin 3) F := ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hB
  have hAB : A * B = 1 := Units.mul_inv H
  have hBA : B * A = 1 := Units.inv_mul H
  have h2 : A * (T : Matrix (Fin 3) (Fin 3) F) * B = Matrix.scalar (Fin 3) (c' : F) := by
    rw [← hcT, coe_slConjugation]
  have hcomm : Commute (Matrix.scalar (Fin 3) (c' : F)) A :=
    Matrix.scalar_commute _ (fun r' => Commute.all _ r') _
  have hTm : (T : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (c' : F) := by
    calc (T : Matrix (Fin 3) (Fin 3) F) = (B * A) * T * (B * A) := by rw [hBA, one_mul, mul_one]
      _ = B * (A * T * B) * A := by simp only [mul_assoc]
      _ = B * Matrix.scalar (Fin 3) (c' : F) * A := by rw [h2]
      _ = Matrix.scalar (Fin 3) (c' : F) := by
        rw [mul_assoc, hcomm.eq, ← mul_assoc, hBA, one_mul]
  have hentry : ∀ i j, ((S : Matrix (Fin 3) (Fin 3) k) i j : F) =
      Matrix.scalar (Fin 3) (c' : F) i j := by
    intro i j
    rw [← hTm, hT, subMap_apply_coe]
  have hcK : (c' : F) ∈ k := by
    have := hentry 0 0
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    rw [← this]
    exact (S : Matrix (Fin 3) (Fin 3) k) 0 0 |>.2
  set c0 : k := ⟨(c' : F), hcK⟩ with hc0
  have hc0ne : c0 ≠ 0 := fun h0 => (Units.ne_zero c') (congrArg Subtype.val h0)
  refine ⟨Units.mk0 c0 hc0ne, ?_, ?_⟩
  · apply Units.ext
    apply Subtype.ext
    have := congrArg Units.val hc3
    simpa [hc0] using this
  · ext i j
    rw [hentry i j]
    by_cases hij : i = j
    · subst hij
      simp [hc0]
    · simp [hij]

theorem ker_Psi (H : GL (Fin 3) F) (k : Subfield F) : (Psi H k).ker = scalars 3 k := by
  ext S
  exact ⟨mem_scalars_of_Psi_eq_one H k, Psi_eq_one_of_mem_scalars H k⟩

noncomputable def lineSubEquiv (H : GL (Fin 3) F) (k : Subfield F) :
    projectiveSL 3 k ≃* lineSub H k :=
  (QuotientGroup.quotientMulEquivOfEq (ker_Psi H k).symm).trans
    ((QuotientGroup.quotientKerEquivRange (Psi H k)).trans
      (MulEquiv.subgroupCongr (range_Psi H k)))

theorem isoLThreePi_lineSub (H : GL (Fin 3) F) (k : Subfield F) {m : ℕ} [Finite F]
    (hk : Nat.card k = 2 ^ m) (hmod : 2 ^ m % 3 = 1) :
    IsoLThreePi (lineSub H k) 2 m := by
  have hm : m ≠ 0 := by
    rintro rfl
    have : Fintype k := Fintype.ofFinite k
    have h1 : Nat.card k = 1 := hk
    have := Fintype.one_lt_card (α := k)
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have hcard : Nat.card k = Nat.card (GaloisField 2 m) := by
    rw [hk, GaloisField.card 2 m hm]
  have : Finite k := inferInstance
  have : Fintype k := Fintype.ofFinite k
  have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hcard' : Fintype.card k = Fintype.card (GaloisField 2 m) := by
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  let ι : k ≃+* GaloisField 2 m := FiniteField.ringEquivOfCardEq hcard'
  exact Or.inl ⟨hmod, ⟨((lineSubEquiv H k).symm.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (n := 3) ι)).trans
    (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 m)).symm⟩⟩

end Iso

section Pair

variable {F : Type} [Field F] [Finite F]

theorem lineSub_sup_eq_top {k : Subfield F}
    (hF : Nat.card F = Nat.card k ^ 3) (hk3 : 3 ≤ Nat.card k) {H H' : GL (Fin 3) F}
    (hne : (slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom ≠ slSub 3 k) :
    lineSub H k ⊔ lineSub H' k = ⊤ := by
  have hpair := CFSG.LieType.SeitzGeneration.subfieldPairSL_odd Nat.prime_three (by norm_num) hF
    hk3 (le_refl 3) (H⁻¹ * H') hne
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq] at hpair
  have hcomp : (slConjugation 3 F H).toMonoidHom.comp (slConjugation 3 F (H⁻¹ * H')).toMonoidHom =
      (slConjugation 3 F H').toMonoidHom := by
    refine MonoidHom.ext fun S => ?_
    show slConjugation 3 F H (slConjugation 3 F (H⁻¹ * H') S) = slConjugation 3 F H' S
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
  have h1 : (slSub 3 k).map (slConjugation 3 F H).toMonoidHom ⊔
      (slSub 3 k).map (slConjugation 3 F H').toMonoidHom = ⊤ := by
    have := congrArg (Subgroup.map (slConjugation 3 F H).toMonoidHom) hpair
    rw [Subgroup.map_sup, Subgroup.map_map, hcomp,
      Subgroup.map_top_of_surjective _ (slConjugation 3 F H).surjective] at this
    exact this
  show ((slSub 3 k).map (slConjugation 3 F H).toMonoidHom).map (proj 3 F) ⊔
    ((slSub 3 k).map (slConjugation 3 F H').toMonoidHom).map (proj 3 F) = ⊤
  rw [← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective _ (proj_surjective 3 F)]

end Pair

section Assembly

variable {F : Type} [Field F] [Finite F]

theorem slSub_conj_ne (h3 : (3 : F) ≠ 0) {σ σ' : F ≃+* F} {k : Subfield F}
    (hk : ∀ x, x ∈ k ↔ σ x = x) (hk' : ∀ x, x ∈ k ↔ σ' x = x) {H H' : GL (Fin 3) F}
    {y : MulAut (projectiveSL 3 F)} (hyN : y ∈ linearAutGroup 3 F) (hy1 : y ≠ 1)
    (hψH : fieldLine H σ * y = fieldLine H' σ') :
    (slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom ≠ slSub 3 k := by
  intro hmap
  have hfix : ∀ S ∈ slSub 3 k,
      y (proj 3 F (slConjugation 3 F H S)) = proj 3 F (slConjugation 3 F H S) := by
    intro S hS
    have hS' : S ∈ (slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom := by
      rw [hmap]
      exact hS
    obtain ⟨T, hT, hTS⟩ := Subgroup.mem_map.mp hS'
    have hcT : slConjugation 3 F H S = slConjugation 3 F H' T := by
      rw [← hTS]
      show slConjugation 3 F H (slConjugation 3 F (H⁻¹ * H') T) = slConjugation 3 F H' T
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    have h1 := Sec19.fixed_conjSub_of_fieldAut (H := H) hk hS
    have h2 : fieldLine H' σ' (proj 3 F (slConjugation 3 F H S)) =
        proj 3 F (slConjugation 3 F H S) := by
      rw [hcT]
      exact Sec19.fixed_conjSub_of_fieldAut hk' hT
    have h4 : fieldLine H σ (y (proj 3 F (slConjugation 3 F H S))) =
        proj 3 F (slConjugation 3 F H S) := by
      have hx : fieldLine H σ (y (proj 3 F (slConjugation 3 F H S))) =
          fieldLine H' σ' (proj 3 F (slConjugation 3 F H S)) :=
        DFunLike.congr_fun hψH (proj 3 F (slConjugation 3 F H S))
      rw [hx, h2]
    apply (fieldLine H σ).injective
    rw [h4, h1]
  exact hy1 (Sec19.eq_one_of_fixes_conj_slSub h3 hyN hfix)

theorem seitz27_projectiveSL_cubic (hA : Sec19.SeitzThreeLThreePi)
    (h3 : (3 : F) ≠ 0) {m : ℕ} (hm : 4 ≤ m) (hmod : 2 ^ m % 3 = 1)
    (hF : Nat.card F = 2 ^ (3 * m)) : Seitz27 (projectiveSL 3 F) := by
  intro E hE hc27
  have hc : Nat.card E = 3 ^ 3 := by rw [hc27]; norm_num
  have hZ : Subgroup.center (projectiveSL 3 F) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (le_refl 3)
  have hnL := not_le_linearAutGroup_of_card h3 hE (by omega)
  obtain ⟨phi, hphiE, hphiN⟩ : ∃ phi ∈ E, phi ∉ linearAutGroup 3 F := by
    by_contra hcon
    push Not at hcon
    exact hnL fun x hx => hcon x hx
  obtain ⟨σ, hσ3, H, hphiH⟩ :=
    KFacts.linear_order_three_field_descent (le_refl 3) phi (hE.2 phi hphiE) hphiN
  subst hphiH
  have hcardA := card_inf_linearAutGroup_eq_nine h3 hE hc27
  obtain ⟨y, hyA, hy1⟩ : ∃ y ∈ E ⊓ linearAutGroup 3 F, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E ⊓ linearAutGroup 3 F = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hcardA
    omega
  obtain ⟨σ', H', hσ'3, hψH0, -, hfix'⟩ :=
    Sec19.exists_second_field_element hE hσ3 hphiE hphiN hyA.1 hyA.2
  have hψH : fieldLine H σ * y = fieldLine H' σ' := hψH0
  obtain ⟨k, hk, hFk, hk1⟩ := Sec19.exists_fixedSubfield_of_orderOf_three hσ3
  have hk' : ∀ x, x ∈ k ↔ σ' x = x := fun x => (hk x).trans (hfix' x).symm
  have hkcard : Nat.card k = 2 ^ m := by
    have h1 : Nat.card k ^ 3 = (2 ^ m) ^ 3 := by rw [← hFk, hF, ← pow_mul, mul_comm]
    exact Nat.pow_left_injective (by norm_num) h1
  have h16 : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hk3 : 3 ≤ Nat.card k := by rw [hkcard]; omega
  have hψE : fieldLine H' σ' ∈ E := by
    rw [← hψH]
    exact E.mul_mem hphiE hyA.1
  have hψN : fieldLine H' σ' ∉ linearAutGroup 3 F := by
    intro hm'
    apply hphiN
    rw [← hψH] at hm'
    have := (linearAutGroup 3 F).mul_mem hm' ((linearAutGroup 3 F).inv_mem hyA.2)
    rwa [mul_inv_cancel_right] at this
  have hφN : fieldLine H σ ∉ linearAutGroup 3 F := hphiN
  have hφ1 : fieldLine H σ ≠ 1 := fun h => hφN (by rw [h]; exact (linearAutGroup 3 F).one_mem)
  have hψ1 : fieldLine H' σ' ≠ 1 := fun h => hψN (by rw [h]; exact (linearAutGroup 3 F).one_mem)
  have hne := slSub_conj_ne h3 hk hk' hyA.2 hy1 hψH
  have hgen := lineSub_sup_eq_top hFk hk3 hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact seitzHyperGamma_eq_top_of_two_subfield_lines hA (p := 2) (m := m) (by omega)
    (by omega) (by omega) hZ hE hc hphiE hψE hφ1 hψ1
    (isoLThreePi_lineSub H k hkcard hmod) (isoLThreePi_lineSub H' k hkcard hmod)
    (lineSub_invariant h3 hE hc27 hσ3 hk hphiE hphiN)
    (lineSub_invariant h3 hE hc27 hσ'3 hk' hψE hψN)
    (fun l hl => fieldLine_fixes_lineSub hk hl) (fun l hl => fieldLine_fixes_lineSub hk' hl)
    (lineSub_ker h3 hE hc27 hk hphiE hphiN) (lineSub_ker h3 hE hc27 hk' hψE hψN) hgen

end Assembly

end CFSG.RankThree.PartTwo.Sec4.E27
