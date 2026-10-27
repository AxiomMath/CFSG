module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KCen
public import CFSG.RankThree.PartTwo.Sec12.Hering129KOut
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open Matrix
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Unitriangular

variable {F : Type} [Field F]

@[expose] def uElt (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem uElt_add (s t : F) : uElt (s + t) = uElt s * uElt t := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uElt, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uElt_zero : uElt (0 : F) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uElt]

theorem uElt_injective : Function.Injective (uElt : F → SpecialLinearGroup (Fin 2) F) := by
  intro a b h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uElt] using this

@[expose] def upperHom (F : Type) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun t := uElt (Multiplicative.toAdd t)
  map_one' := uElt_zero
  map_mul' s t := uElt_add _ _

theorem upperHom_injective : Function.Injective (upperHom F) := fun a b h =>
  Multiplicative.toAdd.injective (uElt_injective h)

@[expose] def lElt (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def negOne (F : Type) [Field F] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩

theorem negOne_comm (A : SpecialLinearGroup (Fin 2) F) : negOne F * A = A * negOne F := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [negOne, Matrix.mul_apply, Fin.sum_univ_two]

theorem negOne_mul_self : negOne F * negOne F = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [negOne, Matrix.mul_apply, Fin.sum_univ_two]

theorem negOne_ne_one (h2 : (2 : F) ≠ 0) : negOne F ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [negOne] at this
  apply h2
  linear_combination -this

theorem eq_zero_of_uElt_comm_lElt {x : F} (h : uElt x * lElt 1 = lElt 1 * uElt x) : x = 0 := by
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  simpa [uElt, lElt, Matrix.mul_apply, Fin.sum_univ_two] using this

end Unitriangular

section TwoLocal

theorem mem_normalizer_zpowers_of_comm {Z : Type} [Group Z] {w t : Z} (hw : w * t = t * w) :
    w ∈ Subgroup.normalizer (Subgroup.zpowers t : Set Z) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hw' : ∀ x ∈ Subgroup.zpowers t, w * x * w⁻¹ = x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [(Commute.zpow_right (hw : Commute w t) n).eq, mul_inv_cancel_right]
  constructor
  · intro hg
    rw [hw' g hg]
    exact hg
  · intro hg
    have h1 := hw' _ hg
    have h2 : g = w * g * w⁻¹ := by
      have := congrArg (fun y => w⁻¹ * y * w) h1
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
      simpa [mul_assoc] using this.symm
    rw [h2]
    exact hg

theorem exists_isTwoLocal_pRank_ge {Z : Type} [Group Z] [Finite Z] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] {p : ℕ} [hp : Fact p.Prime] [CharP F₁ p] [CharP F₂ p]
    (hp2 : p ≠ 2) {a b : ℕ} (hF₁ : Nat.card F₁ = p ^ a) (hF₂ : Nat.card F₂ = p ^ b)
    (ι : SpecialLinearGroup (Fin 2) F₁ →* Z) (η : SpecialLinearGroup (Fin 2) F₂ →* Z)
    (hι : Function.Injective ι) (hη : Function.Injective η)
    (hcomm : ∀ A B, ι A * η B = η B * ι A) :
    ∃ H : Subgroup Z, CFSG.Open.IsTwoLocal H ∧ a + b ≤ CFSG.Open.pRank p H := by
  have h2 : (2 : F₁) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : F₁) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F₁ p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  set t : Z := ι (negOne F₁) with ht
  have ht1 : t ≠ 1 := fun h => negOne_ne_one h2 (hι (by rw [← ht, h, map_one]))
  have ht2 : t ^ 2 = 1 := by
    rw [ht, pow_two, ← map_mul, negOne_mul_self, map_one]
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hP : IsPGroup 2 (Subgroup.zpowers t) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hP1 : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    exact ht1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers t))
  refine ⟨Subgroup.normalizer (Subgroup.zpowers t : Set Z), ⟨_, hP1, hP, rfl⟩, ?_⟩
  have hc1 : ∀ x : Multiplicative F₁, ∀ y : Multiplicative F₂,
      Commute ((ι.comp (upperHom F₁)) x) ((η.comp (upperHom F₂)) y) := fun x y =>
    hcomm _ _
  let f : Multiplicative F₁ × Multiplicative F₂ →* Z :=
    (ι.comp (upperHom F₁)).noncommCoprod (η.comp (upperHom F₂)) hc1
  have hf : ∀ x y, f (x, y) = ι (upperHom F₁ x) * η (upperHom F₂ y) := fun x y => by
    simp [f, MonoidHom.noncommCoprod_apply]
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    rw [hf] at hxy
    have hxl : ι (upperHom F₁ x) = (η (upperHom F₂ y))⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hcent : ι (upperHom F₁ x) * ι (lElt (1 : F₁)) = ι (lElt (1 : F₁)) * ι (upperHom F₁ x) := by
      rw [hxl]
      exact (Commute.inv_right (hcomm (lElt 1) (upperHom F₂ y) : Commute _ _)).symm.eq
    have hx0 : Multiplicative.toAdd x = 0 := by
      apply eq_zero_of_uElt_comm_lElt
      apply hι
      rw [map_mul, map_mul]
      exact hcent
    have hx : x = 1 := Multiplicative.toAdd.injective (by simpa using hx0)
    subst hx
    rw [map_one, map_one, one_mul] at hxy
    have h1 : upperHom F₂ y = 1 := hη (by rw [hxy, map_one])
    have h2' := upperHom_injective (h1.trans (map_one _).symm)
    simp [h2']
  have hrange : f.range ≤ Subgroup.normalizer (Subgroup.zpowers t : Set Z) := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hf]
    apply mem_normalizer_zpowers_of_comm
    have h1 : ι (upperHom F₁ x) * t = t * ι (upperHom F₁ x) := by
      rw [ht, ← map_mul, ← map_mul, negOne_comm]
    have h2' : η (upperHom F₂ y) * t = t * η (upperHom F₂ y) := (hcomm _ _).symm
    calc ι (upperHom F₁ x) * η (upperHom F₂ y) * t
        = ι (upperHom F₁ x) * (η (upperHom F₂ y) * t) := by rw [mul_assoc]
      _ = ι (upperHom F₁ x) * (t * η (upperHom F₂ y)) := by rw [h2']
      _ = (ι (upperHom F₁ x) * t) * η (upperHom F₂ y) := by rw [mul_assoc]
      _ = (t * ι (upperHom F₁ x)) * η (upperHom F₂ y) := by rw [h1]
      _ = t * (ι (upperHom F₁ x) * η (upperHom F₂ y)) := by rw [mul_assoc]
  have hpow : ∀ z : Multiplicative F₁ × Multiplicative F₂, z ^ p = 1 := by
    intro z
    have hp1 : ∀ (F : Type) [Field F] [CharP F p] (w : Multiplicative F), w ^ p = 1 := by
      intro F _ _ w
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    exact Prod.ext (hp1 F₁ z.1) (hp1 F₂ z.2)
  have hcard : Nat.card (Multiplicative F₁ × Multiplicative F₂) = p ^ (a + b) := by
    rw [Nat.card_prod, pow_add, ← hF₁, ← hF₂]
    rfl
  exact CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt (fun x y => mul_comm x y) hpow hcard f
    hfinj hrange

end TwoLocal


section Glue

variable {G : Type} [Group G] [Finite G]

theorem sectionFourHyp_quot_of_mem_thetaComponentsAt (h1 : Sec4.Item4_1LargePrime)
    (hG : TheoremFourHyp G) {x : G} (hx1 : x ≠ 1) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 x) : SectionFourHyp (Y ⧸ aschbacherSolvableCore 3 Y) := by
  obtain ⟨L', hL', rfl⟩ := hY
  have hS4 : SectionFourHyp (Subgroup.centralizer ({x} : Set G)) :=
    hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hx1)
  exact Sec4.Census.sectionFourHyp_of_mulEquiv
    (Sec13.thetaQuotEquivSub (Subgroup.centralizer ({x} : Set G)) L')
    (Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h1 hS4 hL')

end Glue

section Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem exists_isTwoLocal_pRank_ge_d4 {X : Type} [Group X] [Finite X] {r : TauCeti.PrimePower}
    (hodd : r.p ≠ 2) (h : IsG2D4 X r 3) :
    ∃ H : Subgroup X, CFSG.Open.IsTwoLocal H ∧ 4 ≤ CFSG.Open.pRank r.p H := by
  rcases h with ⟨h1, -⟩ | ⟨-, hr, ⟨f⟩⟩
  · exact absurd h1 (by norm_num)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Hering129KModels.exists_d4_model f
  haveI : Fact r.p.Prime := ⟨r.prime_p⟩
  have hK' : Nat.card K = r.p ^ (3 * r.exponent) := by
    rw [hK, TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]
  haveI : CharP K r.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic r.prime_p
      (by have := r.exponent_pos; omega) hK'
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ3
  haveI : CharP (fixSubfield σ) r.p := inferInstance
  haveI : Finite (fixSubfield σ) := inferInstance
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 1 ≤ b ∧ Nat.card (fixSubfield σ) = r.p ^ b := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    obtain ⟨n, -, hn⟩ := FiniteField.card (fixSubfield σ) r.p
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨H, hH, hrank⟩ := exists_isTwoLocal_pRank_ge hodd hK' hb.2
    (e.symm.toMonoidHom.comp ι) (e.symm.toMonoidHom.comp η)
    (e.symm.injective.comp hι) (e.symm.injective.comp hη)
    (fun A B => by
      show e.symm (ι A) * e.symm (η B) = e.symm (η B) * e.symm (ι A)
      rw [← map_mul, ← map_mul, hcomm A B])
  refine ⟨H, hH, le_trans ?_ hrank⟩
  have := r.exponent_pos
  omega

theorem exists_isTwoLocal_pRank_ge_g2 {X : Type} [Group X] [Finite X] {r : TauCeti.PrimePower}
    (hodd : r.p ≠ 2) (h : IsG2D4 X r 1) :
    ∃ H : Subgroup X, CFSG.Open.IsTwoLocal H ∧ 2 * r.exponent ≤ CFSG.Open.pRank r.p H := by
  rcases h with ⟨-, hX⟩ | ⟨h3, -⟩
  swap
  · exact absurd h3 (by norm_num)
  obtain ⟨K, _, _, hK, hKp, ⟨e⟩⟩ := Hering129KModels.exists_adjoint_model hX
  haveI : Fact r.p.Prime := ⟨r.prime_p⟩
  have hK' : Nat.card K = r.p ^ r.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  haveI : CharP K r.p := ringChar.of_eq hKp
  obtain ⟨eS⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
  obtain ⟨eM⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := K)
  let ι : SpecialLinearGroup (Fin 2) K →* X :=
    e.symm.toMonoidHom.comp ((Sec11.KS11Lie4Proof.g2ShortSL2 K).subtype.comp eS.toMonoidHom)
  let η : SpecialLinearGroup (Fin 2) K →* X :=
    e.symm.toMonoidHom.comp ((Sec11.KS11Lie4Proof.g2LongSL2 K).subtype.comp eM.toMonoidHom)
  have hι : Function.Injective ι :=
    e.symm.injective.comp (Subtype.val_injective.comp eS.injective)
  have hη : Function.Injective η :=
    e.symm.injective.comp (Subtype.val_injective.comp eM.injective)
  obtain ⟨H, hH, hrank⟩ := exists_isTwoLocal_pRank_ge hodd hK' hK' ι η hι hη (fun A B => by
    have := Sec11.KS11Lie4Proof.g2Short_commute_g2Long (eS A).2 (eM B).2
    show e.symm ((eS A : adjointGroup .G2 K)) * e.symm ((eM B : adjointGroup .G2 K)) =
      e.symm ((eM B : adjointGroup .G2 K)) * e.symm ((eS A : adjointGroup .G2 K))
    rw [← map_mul, ← map_mul, this])
  refine ⟨H, hH, ?_⟩
  have : r.exponent + r.exponent = 2 * r.exponent := by ring
  omega


theorem p_eq_two_of_sectionFourHyp_d4 {X : Type} [Group X] [Finite X] (hX : SectionFourHyp X)
    {r : TauCeti.PrimePower} (h : IsG2D4 X r 3) : r.p = 2 := by
  by_contra hodd
  obtain ⟨H, hH, hrank⟩ := exists_isTwoLocal_pRank_ge_d4 hodd h
  have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r.p r.prime_p hodd H hH
  have h3 := hX.evenRank_le
  omega

theorem p_eq_two_or_exponent_eq_one_of_sectionFourHyp_g2 {X : Type} [Group X] [Finite X]
    (hX : SectionFourHyp X) {r : TauCeti.PrimePower} (h : IsG2D4 X r 1) :
    r.p = 2 ∨ r.exponent = 1 := by
  by_cases hodd : r.p = 2
  · exact Or.inl hodd
  right
  obtain ⟨H, hH, hrank⟩ := exists_isTwoLocal_pRank_ge_g2 hodd h
  have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r.p r.prime_p hodd H hH
  have h3 := hX.evenRank_le
  have := r.exponent_pos
  omega

theorem gap127D4Even_of (h1 : Sec4.Item4_1LargePrime) : Gap127D4Even := by
  intro G _ _ A c L b a K S cfg q hq hD4
  obtain ⟨hq', ⟨f⟩⟩ := hD4
  obtain ⟨-, -, -, hb1, -⟩ := cfg.point_facts
  have hG : IsG2D4 (K ⧸ CFSG.pCore 2 K) q 3 := Or.inr ⟨rfl, hq', ⟨f⟩⟩
  have hθ : aschbacherSolvableCore 3 K = CFSG.pCore 2 K :=
    Hering129KOut.aschbacherSolvableCore_eq_pCore_two hG
  have hS4 := sectionFourHyp_quot_of_mem_thetaComponentsAt h1 cfg.std.toTheoremFourHyp hb1 cfg.hK
  exact p_eq_two_of_sectionFourHyp_d4
    (Sec4.Census.sectionFourHyp_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hθ) hS4) hG


end Models


end Hering129L

end CFSG.RankThree.PartTwo.Sec12
