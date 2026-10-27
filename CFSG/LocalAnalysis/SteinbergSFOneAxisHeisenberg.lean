module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisSecondRadical
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisHeisenberg

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem conj_mem_pCore_map {N : Subgroup G} {g d : G} (hg : g ∈ N)
    (hd : d ∈ (CFSG.pCore 2 N).map N.subtype) : g * d * g⁻¹ ∈ (CFSG.pCore 2 N).map N.subtype := by
  obtain ⟨p, hp, rfl⟩ := hd
  exact ⟨⟨g, hg⟩ * p * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem p hp ⟨g, hg⟩, rfl⟩

theorem le_normalizer_pCore_map [Finite G] {N : Subgroup G} :
    N ≤ normalizer (((CFSG.pCore 2 N).map N.subtype : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_of_conj_le fun _ hd => conj_mem_pCore_map hg hd

theorem mem_map_mk_iff {S H B : Subgroup G} [(B.subgroupOf S).Normal] (hBH : B ≤ H) (s : S) :
    (s : ↥S ⧸ B.subgroupOf S) ∈ (H.subgroupOf S).map (QuotientGroup.mk' (B.subgroupOf S)) ↔
      (s : G) ∈ H := by
  constructor
  · rintro ⟨s', hs', he⟩
    have h1 := mem_subgroupOf.mp (QuotientGroup.eq.mp he)
    have h2 := mul_mem (mem_subgroupOf.mp hs') (hBH h1)
    simpa using h2
  · intro hs
    exact ⟨s, mem_subgroupOf.mpr hs, rfl⟩

theorem conj_conj_eq {t j d : G} (hjt : j * t = t * j) :
    t⁻¹ * ((j⁻¹ * d * j)⁻¹ * t * (j⁻¹ * d * j)) = j⁻¹ * (t⁻¹ * (d⁻¹ * t * d)) * j := by
  have h1 : t = j⁻¹ * t * j := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  conv_lhs => rw [h1]
  group

theorem exists_quotient_mulEquiv {H M : Type*} [Group H] [Group M] {N : Subgroup H} [N.Normal]
    (χ : H →* M) (hker : χ.ker = N) (hsurj : Function.Surjective χ) :
    ∃ θ : H ⧸ N ≃* M, ∀ h : H, θ h = χ h :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hsurj), fun _ => rfl⟩

end General

section Heis

variable {K : Type} [Field K]

theorem unipU_inj' {a b c a' b' c' : K} (h : unipU K a b c = unipU K a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_unipU] at h'
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrFun (congrFun h' 0) 1
  · simpa using congrFun (congrFun h' 1) 2
  · simpa using congrFun (congrFun h' 0) 2

theorem unipU_apply_zero_one (a b c : K) :
    ((unipU K a b c : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = a := by
  simp [coe_unipU]

theorem unipU_apply_one_two (a b c : K) :
    ((unipU K a b c : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = b := by
  simp [coe_unipU]

theorem unipU_apply_zero_two (a b c : K) :
    ((unipU K a b c : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = c := by
  simp [coe_unipU]

theorem unipU_mul_self [CharP K 2] (a b c : K) :
    unipU K a b c * unipU K a b c = unipU K 0 0 (a * b) := by
  rw [unipU_mul]
  congr 1
  · exact CharTwo.add_self_eq_zero a
  · exact CharTwo.add_self_eq_zero b
  · rw [CharTwo.add_self_eq_zero, zero_add]

theorem exists_unipU_eq (g : unipAll K) :
    ∃ a b c, (g : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K a b c := by
  obtain ⟨a, b, c, h⟩ := g.2
  exact ⟨a, b, c, h.symm⟩

theorem card_unipAll' : Nat.card (unipAll K) = Nat.card K ^ 3 := by
  have hbij : Function.Bijective fun p : K × K × K =>
      (⟨unipU K p.1 p.2.1 p.2.2, _, _, _, rfl⟩ : unipAll K) := by
    refine ⟨fun p p' h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := unipU_inj' (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨a, b, c, h⟩ := exists_unipU_eq g
      exact ⟨(a, b, c), Subtype.ext h.symm⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_prod]
  ring

theorem heis_structure [CharP K 2] {H : Type*} [Group H] (θ : H ≃* unipAll K)
    (E₁ E₂ : Subgroup H)
    (h₁ : ∀ g, g ∈ E₁ ↔
      ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (h₂ : ∀ g, g ∈ E₂ ↔
      ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) :
    (∀ E : Subgroup H,
      Maximal (fun F : Subgroup H => IsElementaryAbelian 2 F) E ↔ E = E₁ ∨ E = E₂) ∧ E₁ ≠ E₂ ∧
    (∀ g : H, g ^ 2 = 1 → g ∈ E₁ ∨ g ∈ E₂) ∧
    E₁ ⊓ E₂ = center H ∧ Nat.card (center H) = Nat.card K := by
  have hmul : ∀ g h : H, (θ (g * h) : Matrix.SpecialLinearGroup (Fin 3) K) =
      (θ g : Matrix.SpecialLinearGroup (Fin 3) K) * θ h := fun g h => by
    rw [map_mul, Subgroup.coe_mul]
  have hinj : ∀ g h : H, (θ g : Matrix.SpecialLinearGroup (Fin 3) K) = θ h → g = h :=
    fun g h e => θ.injective (Subtype.ext e)
  have hE₁ : ∀ g, g ∈ E₁ ↔ ∃ a c, (θ g : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K a 0 c := by
    intro g
    obtain ⟨a, b, c, hg⟩ := exists_unipU_eq (θ g)
    rw [h₁, hg, unipU_apply_one_two]
    constructor
    · rintro rfl
      exact ⟨a, c, rfl⟩
    · rintro ⟨a', c', e⟩
      exact (unipU_inj' e).2.1
  have hE₂ : ∀ g, g ∈ E₂ ↔ ∃ b c, (θ g : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K 0 b c := by
    intro g
    obtain ⟨a, b, c, hg⟩ := exists_unipU_eq (θ g)
    rw [h₂, hg, unipU_apply_zero_one]
    constructor
    · rintro rfl
      exact ⟨b, c, rfl⟩
    · rintro ⟨b', c', e⟩
      exact (unipU_inj' e).1
  have hsq : ∀ g : H, g ^ 2 = 1 → g ∈ E₁ ∨ g ∈ E₂ := by
    intro g hg
    obtain ⟨a, b, c, hθ⟩ := exists_unipU_eq (θ g)
    have h1 : unipU K 0 0 (a * b) = unipU K 0 0 0 := by
      rw [← unipU_mul_self, ← hθ, ← hmul, ← pow_two, hg, map_one, unipU_zero]
      rfl
    rcases mul_eq_zero.mp (unipU_inj' h1).2.2 with ha | hb
    · exact Or.inr ((hE₂ g).mpr ⟨b, c, by rw [hθ, ha]⟩)
    · exact Or.inl ((hE₁ g).mpr ⟨a, c, by rw [hθ, hb]⟩)
  have hEA : ∀ E : Subgroup H, (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ 2 = 1) →
      IsElementaryAbelian 2 E := fun E hc hs =>
    { is_comm := ⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hs g g.2) }
  have hEA₁ : IsElementaryAbelian 2 E₁ := by
    refine hEA E₁ (fun g hg h hh => hinj _ _ ?_) fun g hg => hinj _ _ ?_
    · obtain ⟨a, c, ha⟩ := (hE₁ g).mp hg
      obtain ⟨a', c', ha'⟩ := (hE₁ h).mp hh
      rw [hmul, hmul, ha, ha', unipU_mul, unipU_mul]
      congr 1 <;> ring
    · obtain ⟨a, c, ha⟩ := (hE₁ g).mp hg
      rw [pow_two, hmul, ha, unipU_mul_self, mul_zero, map_one, unipU_zero]
      rfl
  have hEA₂ : IsElementaryAbelian 2 E₂ := by
    refine hEA E₂ (fun g hg h hh => hinj _ _ ?_) fun g hg => hinj _ _ ?_
    · obtain ⟨b, c, hb⟩ := (hE₂ g).mp hg
      obtain ⟨b', c', hb'⟩ := (hE₂ h).mp hh
      rw [hmul, hmul, hb, hb', unipU_mul, unipU_mul]
      congr 1 <;> ring
    · obtain ⟨b, c, hb⟩ := (hE₂ g).mp hg
      rw [pow_two, hmul, hb, unipU_mul_self, zero_mul, map_one, unipU_zero]
      rfl
  have hle : ∀ F : Subgroup H, IsElementaryAbelian 2 F → F ≤ E₁ ∨ F ≤ E₂ := fun F hF =>
    subgroup_le_of_subset_union fun f hf => hsq f (elemPow_eq_one_of_isElementaryAbelian f hf)
  set g₁ : H := θ.symm ⟨unipU K 1 0 0, 1, 0, 0, rfl⟩ with hg₁
  set g₂ : H := θ.symm ⟨unipU K 0 1 0, 0, 1, 0, rfl⟩ with hg₂
  have hθ₁ : (θ g₁ : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K 1 0 0 := by
    rw [hg₁, MulEquiv.apply_symm_apply]
  have hθ₂ : (θ g₂ : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K 0 1 0 := by
    rw [hg₂, MulEquiv.apply_symm_apply]
  have hn12 : ¬ E₁ ≤ E₂ := fun h => by
    have := (h₂ g₁).mp (h ((h₁ g₁).mpr (by rw [hθ₁, unipU_apply_one_two])))
    rw [hθ₁, unipU_apply_zero_one] at this
    exact one_ne_zero this
  have hn21 : ¬ E₂ ≤ E₁ := fun h => by
    have := (h₁ g₂).mp (h ((h₂ g₂).mpr (by rw [hθ₂, unipU_apply_zero_one])))
    rw [hθ₂, unipU_apply_one_two] at this
    exact one_ne_zero this
  have hcent : ∀ g : H, g ∈ center H ↔ ∃ c, (θ g : Matrix.SpecialLinearGroup (Fin 3) K) =
      unipU K 0 0 c := by
    intro g
    rw [Subgroup.mem_center_iff]
    obtain ⟨a, b, c, hθ⟩ := exists_unipU_eq (θ g)
    constructor
    · intro hc
      have e1 := congrArg (fun x : H => (θ x : Matrix.SpecialLinearGroup (Fin 3) K)) (hc g₂)
      have e2 := congrArg (fun x : H => (θ x : Matrix.SpecialLinearGroup (Fin 3) K)) (hc g₁)
      simp only [hmul, hθ, hθ₁, hθ₂, unipU_mul] at e1 e2
      have ha := (unipU_inj' e1).2.2
      have hb := (unipU_inj' e2).2.2
      refine ⟨c, ?_⟩
      rw [hθ]
      congr 1
      · linear_combination -ha
      · linear_combination hb
    · rintro ⟨c', hc'⟩ h
      apply hinj
      obtain ⟨a', b', c'', hh⟩ := exists_unipU_eq (θ h)
      rw [hmul, hmul, hc', hh, unipU_mul, unipU_mul]
      congr 1 <;> ring
  refine ⟨fun E => ⟨fun ⟨hE, hmax⟩ => ?_, ?_⟩, fun h => hn12 h.le, hsq, ?_, ?_⟩
  · rcases hle E hE with h | h
    · exact Or.inl (le_antisymm h (hmax hEA₁ h))
    · exact Or.inr (le_antisymm h (hmax hEA₂ h))
  · rintro (rfl | rfl)
    · refine ⟨hEA₁, fun F hF hEF => ?_⟩
      rcases hle F hF with h | h
      · exact h
      · exact absurd (hEF.trans h) hn12
    · refine ⟨hEA₂, fun F hF hEF => ?_⟩
      rcases hle F hF with h | h
      · exact absurd (hEF.trans h) hn21
      · exact h
  · ext g
    rw [mem_inf, hcent, hE₁, hE₂]
    constructor
    · rintro ⟨⟨a, c, ha⟩, ⟨b, c', hb⟩⟩
      refine ⟨c, ?_⟩
      rw [ha]
      rw [ha] at hb
      rw [(unipU_inj' hb).1]
    · rintro ⟨c, hc⟩
      exact ⟨⟨0, c, hc⟩, ⟨0, c, hc⟩⟩
  · let f : K → center H := fun c => ⟨θ.symm ⟨unipU K 0 0 c, 0, 0, c, rfl⟩,
      (hcent _).mpr ⟨c, by rw [MulEquiv.apply_symm_apply]⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun c c' e => ?_, fun g => ?_⟩
      · have e' := congrArg (fun x : center H => (θ x : Matrix.SpecialLinearGroup (Fin 3) K)) e
        simp only [f, MulEquiv.apply_symm_apply] at e'
        exact (unipU_inj' e').2.2
      · obtain ⟨c, hc⟩ := (hcent g).mp g.2
        refine ⟨c, Subtype.ext ?_⟩
        apply hinj
        simp only [f, MulEquiv.apply_symm_apply]
        exact hc.symm
    exact (Nat.card_eq_of_bijective f hf).symm

end Heis

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem uElt_conj_uElt (a' b' c' d' a b : K) :
    uElt a' b' c' d' * uElt a b 0 0 * (uElt a' b' c' d')⁻¹ = uElt a (b + d' * a) 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_inv, uElt_mul, uElt_mul]
  congr 1
  · linear_combination a' * h2
  · linear_combination (b' + a' * d') * h2
  · linear_combination (c' + a' * b + a * b' + a' * b' + a' ^ 2 * d' + a * a' * d') * h2
  · linear_combination d' * h2

theorem uElt_conj_aElt (a' b' c' d' : K) (v : Fin 2 → K) :
    uElt a' b' c' d' * aElt v 0 * (uElt a' b' c' d')⁻¹ = aElt ![v 0 + d' * v 1 + 0, v 1 + 0] 0 := by
  rw [aElt, aElt, uElt_conj_uElt]
  simp

theorem eq_one_of_mul_self_eq_one {x : K} (h : x * x = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (x + 1) * (x + 1) = 0 := by linear_combination h + (x + 1) * h2
  linear_combination mul_self_eq_zero.mp h1 - h2

end Model

section Act

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def HAct (φ : L ≃* antiSp K) (t g : G) (x y d : K) : Prop :=
  ∀ v : Fin 2 → K, g * coord φ t (qgPoint v) * g⁻¹ =
    coord φ t (qgPoint ![v 0 + d * v 1 + y, v 1 + x])

@[expose] def SAct (φ : L ≃* antiSp K) (t g : G) (σ : K ≃+* K) : Prop :=
  ∃ (v₀ : Fin 2 → K) (M : GL (Fin 2) K), ∀ v : Fin 2 → K, g * coord φ t (qgPoint v) * g⁻¹ =
    coord φ t (qgPoint (v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i)))

variable {φ : L ≃* antiSp K} {t : G}

theorem hAct_iff {g : G} {x y d : K} : HAct φ t g x y d ↔ ∀ a b : K,
    g * (t * ((φ.symm (uElt a b 0 0) : L) : G)) * g⁻¹ =
      t * ((φ.symm (uElt (a + x) (b + d * a + y) 0 0) : L) : G) := by
  constructor
  · intro h a b
    have := h ![b, a]
    rwa [coord_qgPoint, coord_qgPoint] at this
  · intro h v
    rw [coord_qgPoint, coord_qgPoint]
    exact h (v 1) (v 0)

theorem HAct.mul {g g' : G} {x y d x' y' d' : K} (h : HAct φ t g x y d)
    (h' : HAct φ t g' x' y' d') : HAct φ t (g * g') (x + x') (y + y' + d * x') (d + d') := by
  intro v
  rw [show g * g' * coord φ t (qgPoint v) * (g * g')⁻¹ =
    g * (g' * coord φ t (qgPoint v) * g'⁻¹) * g⁻¹ by group, h', h]
  congr 2
  ext i
  fin_cases i <;> simp <;> ring

theorem HAct.sAct {g : G} {x y d : K} (h : HAct φ t g x y d) :
    SAct φ t g (RingEquiv.refl K) := by
  refine ⟨![y, x], Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, d; 0, 1]
    (by simp [Matrix.det_fin_two_of]), fun v => ?_⟩
  rw [h v]
  congr 2
  ext i
  fin_cases i <;>
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, dotProduct, Fin.sum_univ_two] <;> ring

theorem HAct.congr {g : G} {x y d x' y' d' : K} (h : HAct φ t g x y d) (hx : x = x') (hy : y = y')
    (hd : d = d') : HAct φ t g x' y' d' := by
  subst hx hy hd
  exact h

theorem SAct.of_smul {g : G} {l : K} (hl : l ≠ 0)
    (h : ∀ v, g * coord φ t (qgPoint v) * g⁻¹ = coord φ t (qgPoint (l • v))) :
    SAct φ t g (RingEquiv.refl K) := by
  refine ⟨0, Matrix.GeneralLinearGroup.mkOfDetNeZero !![l, 0; 0, l]
    (by simpa [Matrix.det_fin_two_of] using hl), fun v => ?_⟩
  rw [h v]
  congr 2
  ext i
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, dotProduct, Fin.sum_univ_two]

theorem SAct.mul {g g' : G} {σ σ' τ : K ≃+* K} (h : SAct φ t g σ) (h' : SAct φ t g' σ')
    (hτ : ∀ x, τ x = σ (σ' x)) : SAct φ t (g * g') τ := by
  obtain ⟨v₀, M, hM⟩ := h
  obtain ⟨v₀', M', hM'⟩ := h'
  refine ⟨v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ (v₀' i)),
    M * Matrix.GeneralLinearGroup.map σ.toRingHom M', fun v => ?_⟩
  rw [show g * g' * coord φ t (qgPoint v) * (g * g')⁻¹ =
    g * (g' * coord φ t (qgPoint v) * g'⁻¹) * g⁻¹ by group, hM', hM]
  congr 2
  have e1 : (fun i => σ ((v₀' + (M' : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => σ' (v j)) i)) =
      (fun i => σ (v₀' i)) + ((M' : Matrix (Fin 2) (Fin 2) K).map σ.toRingHom) *ᵥ
        fun i => τ (v i) := by
    ext i
    simp only [Pi.add_apply, map_add]
    congr 1
    have := RingHom.map_mulVec σ.toRingHom (M' : Matrix (Fin 2) (Fin 2) K) (fun j => σ' (v j)) i
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
    rw [this]
    congr 1
    ext j
    simp [hτ]
  rw [e1, Matrix.mulVec_add, add_assoc, Units.val_mul, ← Matrix.mulVec_mulVec]
  rfl

variable {n : ℕ}

theorem coord_qgPoint_injective (hS : TwoCoreSetup L K n t) {v w : Fin 2 → K}
    (h : coord φ t (qgPoint v) = coord φ t (qgPoint w)) : v = w :=
  qgPoint_injective (coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem h)

theorem HAct.unique (hS : TwoCoreSetup L K n t) {g : G} {x y d x' y' d' : K}
    (h : HAct φ t g x y d) (h' : HAct φ t g x' y' d') : x = x' ∧ y = y' ∧ d = d' := by
  have e0 := coord_qgPoint_injective hS ((h 0).symm.trans (h' 0))
  have e1 := coord_qgPoint_injective hS ((h ![0, 1]).symm.trans (h' ![0, 1]))
  have a0 := congrFun e0 0
  have a1 := congrFun e0 1
  have b0 := congrFun e1 0
  simp at a0 a1 b0
  exact ⟨a1, a0, by linear_combination b0 - a0⟩

theorem SAct.unique (hS : TwoCoreSetup L K n t) {g : G} {σ σ' : K ≃+* K}
    (h : SAct φ t g σ) (h' : SAct φ t g σ') : σ = σ' := by
  obtain ⟨v₀, M, hM⟩ := h
  obtain ⟨v₀', M', hM'⟩ := h'
  exact (affine_params_unique fun v => coord_qgPoint_injective (φ := φ) hS
    ((hM v).symm.trans (hM' v))).2.2

end Act

section Second

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {t : G}

local notation "𝐁" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
local notation "𝐍" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype

theorem hAct_symm_uElt (hS : TwoCoreSetup L K n t) (a b c d : K) :
    HAct φ t ((φ.symm (uElt a b c d) : L) : G) 0 0 d := by
  intro v
  have hpt : ((φ.symm (uElt a b c d) : L) : G) * t = t * ((φ.symm (uElt a b c d) : L) : G) :=
    (hS.comm (φ.symm _).2).symm
  rw [coord_qgPoint, coord_qgPoint, ← uElt_conj_aElt a b c d v, ← symm_conj_eq φ]
  calc ((φ.symm (uElt a b c d) : L) : G) * (t * ((φ.symm (aElt v 0) : L) : G)) *
        ((φ.symm (uElt a b c d) : L) : G)⁻¹
      = (((φ.symm (uElt a b c d) : L) : G) * t) * ((φ.symm (aElt v 0) : L) : G) *
          ((φ.symm (uElt a b c d) : L) : G)⁻¹ := by group
    _ = _ := by rw [hpt]; group

theorem card_B (hS : TwoCoreSetup L K n t) : Nat.card 𝐁 = 2 * Nat.card K ^ 3 := by
  have hbij : Function.Bijective fun e : QGSpace K => (⟨coord φ t e, coord_mem φ e⟩ : 𝐁) :=
    ⟨fun e e' h => coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem
      (congrArg Subtype.val h), fun b => by
        obtain ⟨e, he⟩ := exists_coord_eq φ hS.t_mul_t (fun _ hx => hS.comm hx) b.2
        exact ⟨e, Subtype.ext he⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]
  ring

theorem exists_sAct [Finite K] (h : SecondHyp L K n φ t) {g : G} (hg : g ∈ 𝐍) :
    ∃ σ, SAct φ t g σ := by
  have hρ := conjRep_mem_qgStab φ h.two h.fus ⟨g, hg⟩
  obtain ⟨v₀, M, σ, hM⟩ := exists_affine_of_mem hρ
  refine ⟨σ, v₀, M, fun v => ?_⟩
  rw [← hM v, qgPoint_qgInduced hρ, coord_toAdd_conjRep]

theorem hAct_of_mem_B (h : SecondHyp L K n φ t) {b : G} (hb : b ∈ 𝐁) : HAct φ t b 0 0 0 := by
  intro v
  rw [B_comm φ h.two hb (coord_mem φ _), mul_inv_cancel_right]
  congr 2
  ext i
  fin_cases i <;> simp

theorem inv_mul_mem_B [Finite K] (h : SecondHyp L K n φ t) {g g' : G} (hg : g ∈ 𝐍)
    (hg' : g' ∈ 𝐍) {x y d : K} (hx : HAct φ t g x y d) (hx' : HAct φ t g' x y d) :
    g'⁻¹ * g ∈ 𝐁 := by
  refine h.mem_B_of_fix (mul_mem (inv_mem hg') hg) fun v => ?_
  calc g'⁻¹ * g * coord φ t (qgPoint v) * (g'⁻¹ * g)⁻¹ =
        g'⁻¹ * (g * coord φ t (qgPoint v) * g⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * coord φ t (qgPoint v) * g'⁻¹) * g' := by rw [hx v, hx' v]
    _ = coord φ t (qgPoint v) := by group

theorem hAct_of_mem_D [Finite G] [Finite K] (h : SecondHyp L K n φ t) {d : G} (hd : d ∈ 𝐃) :
    ∃ x y : K, HAct φ t d x y 0 := by
  obtain ⟨u, hu⟩ := h.D_transl hd
  refine ⟨u 1, u 0, fun v => ?_⟩
  rw [hu v]
  congr 2
  ext i
  fin_cases i <;> simp

theorem exists_D_hAct [Finite G] [Finite K] (h : SecondHyp L K n φ t) (x y : K) :
    ∃ d ∈ 𝐃, HAct φ t d x y 0 := by
  obtain ⟨d, hd, hdu⟩ := h.exists_D_transl ![y, x]
  refine ⟨d, hd, fun v => ?_⟩
  rw [hdu v]
  congr 2
  ext i
  fin_cases i <;> simp

end Second

structure HeisHyp {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] (n : ℕ)
    (φ : L ≃* antiSp K) (TG : Subgroup G) (t : G) : Prop where
  hyp : Hyp L K n φ TG t
  sec : SecondHyp L K n φ t
  normQ : normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) ≤
    normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G) ⊓
      normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
  inf₁ : (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) :
      Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) :
      Set G)).subtype ⊓ (centralizer ({t} : Set G) ⊓
      normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G)) =
    zpowers t ⊔ pull φ (rootA K Axis.one)
  conj₁ : ∀ d ∈ (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
      Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
      Subgroup G) : Set G)).subtype, t⁻¹ * (d⁻¹ * t * d) ∈ pull φ (rootU K Axis.one)
  mul₁ : ∀ d ∈ (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
      Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
      Subgroup G) : Set G)).subtype, ∀ d' ∈ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
      pull φ (rootA K Axis.one) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
      pull φ (rootA K Axis.one) : Subgroup G) : Set G)).subtype,
    t⁻¹ * ((d * d')⁻¹ * t * (d * d')) = t⁻¹ * (d⁻¹ * t * d) * (t⁻¹ * (d'⁻¹ * t * d'))
  surj₁ : ∀ u ∈ pull φ (rootU K Axis.one), ∃ d ∈ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
      pull φ (rootA K Axis.one) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
      pull φ (rootA K Axis.one) : Subgroup G) : Set G)).subtype, t⁻¹ * (d⁻¹ * t * d) = u

namespace HeisHyp

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ TG : Subgroup G)
local notation "𝐔₁" => pull φ (rootU K Axis.one)
local notation "𝐁₁" => (zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G)
local notation "𝐁₂" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
local notation "𝐍₁" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G)
local notation "𝐍₂" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃₁" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem Q_le_N (hh : HeisHyp L K n φ TG t) : 𝐐 ≤ 𝐍₁ ⊓ 𝐍₂ :=
  le_normalizer.trans hh.normQ

theorem comm_Q_U (hh : HeisHyp L K n φ TG t) {q u : G} (hq : q ∈ 𝐐) (hu : u ∈ 𝐔₁) :
    q * u = u * q := by
  obtain ⟨p, hp, c, hc, rfl⟩ := hh.hyp.setup.mem_Q.mp hq
  have hpu : p * u = u * p := Setup.comm_P_ZP hp (pull_mono φ (rootU_le_center Axis.one) hu)
  have hcu : c * u = u * c := (hh.hyp.setup.comm_L_T (pull_le φ _ hu) hc).symm
  calc p * c * u = p * (c * u) := by group
    _ = p * u * c := by rw [hcu]; group
    _ = u * (p * c) := by rw [hpu]; group

theorem D₁_le_N₁ : 𝐃₁ ≤ 𝐍₁ := map_subtype_le _

theorem mem_B₁ (hh : HeisHyp L K n φ TG t) {d : G} (hd : d ∈ 𝐃₁) (hdt : d * t = t * d) :
    d ∈ 𝐁₁ := by
  rw [← hh.inf₁]
  exact ⟨hd, mem_centralizer_singleton_iff.mpr hdt, D₁_le_N₁ hd⟩

theorem conj_mem_Q (hh : HeisHyp L K n φ TG t) {d q : G} (hd : d ∈ 𝐃₁) (hq : q ∈ 𝐐) :
    d * q * d⁻¹ ∈ 𝐐 := by
  have hqN : q ∈ 𝐍₁ := (hh.Q_le_N hq).1
  have hqt : q * t = t * q := mem_centralizer_singleton_iff.mp (hh.hyp.setup.Q_le_C hq)
  have hx : q⁻¹ * d * q ∈ 𝐃₁ := by simpa using conj_mem_pCore_map (inv_mem hqN) hd
  have hqu := hh.comm_Q_U hq (hh.conj₁ d hd)
  have hxt : (q⁻¹ * d * q)⁻¹ * t * (q⁻¹ * d * q) = d⁻¹ * t * d := by
    calc (q⁻¹ * d * q)⁻¹ * t * (q⁻¹ * d * q) = q⁻¹ * d⁻¹ * (q * t) * q⁻¹ * d * q := by group
      _ = q⁻¹ * (t * (t⁻¹ * (d⁻¹ * t * d))) * q := by rw [hqt]; group
      _ = q⁻¹ * t * ((t⁻¹ * (d⁻¹ * t * d)) * q) := by group
      _ = q⁻¹ * (t * q) * (t⁻¹ * (d⁻¹ * t * d)) := by rw [← hqu]; group
      _ = d⁻¹ * t * d := by rw [← hqt]; group
  have hc : q⁻¹ * d * q * d⁻¹ ∈ 𝐐 := by
    refine hh.hyp.B_le_Q Axis.one (hh.mem_B₁ (mul_mem hx (inv_mem hd)) ?_)
    calc q⁻¹ * d * q * d⁻¹ * t = q⁻¹ * d * q * (d⁻¹ * t * d) * d⁻¹ := by group
      _ = q⁻¹ * d * q * ((q⁻¹ * d * q)⁻¹ * t * (q⁻¹ * d * q)) * d⁻¹ := by rw [hxt]
      _ = t * (q⁻¹ * d * q * d⁻¹) := by group
  have e : d * q * d⁻¹ = q * (q⁻¹ * d * q * d⁻¹) := by group
  rw [e]
  exact mul_mem hq hc

theorem D₁_le_N₂ [Finite G] (hh : HeisHyp L K n φ TG t) : 𝐃₁ ≤ 𝐍₂ := fun _ hd =>
  (hh.normQ (mem_normalizer_of_conj_le fun _ hq => hh.conj_mem_Q hd hq)).2

theorem hAct_of_mem_Q (hh : HeisHyp L K n φ TG t) {q : G} (hq : q ∈ 𝐐) :
    ∃ δ : K, HAct φ t q 0 0 δ := by
  obtain ⟨p, hp, c, hc, rfl⟩ := hh.hyp.setup.mem_Q.mp hq
  obtain ⟨a', ⟨a₁, b₁, c₁, d₁, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp
  rw [hh.hyp.T_eq] at hc
  exact ⟨d₁, ((hAct_symm_uElt hh.sec.two a₁ b₁ c₁ d₁).mul
    (hAct_of_mem_B hh.sec (mem_sup_left hc))).congr (by ring) (by ring) (by ring)⟩

theorem shear_mem (hh : HeisHyp L K n φ TG t) (δ : K) :
    ((φ.symm (uElt 0 0 0 δ) : L) : G) ∈ 𝐐 ∧ HAct φ t ((φ.symm (uElt 0 0 0 δ) : L) : G) 0 0 δ :=
  ⟨mem_sup_left (symm_mem_pull.mpr (uElt_mem_antiUnipotent 0 0 0 δ)),
    hAct_symm_uElt hh.sec.two 0 0 0 δ⟩

theorem sq_mem_Q (hh : HeisHyp L K n φ TG t) {d : G} (hd : d ∈ 𝐃₁) : d * d ∈ 𝐐 := by
  refine hh.hyp.B_le_Q Axis.one (hh.mem_B₁ (mul_mem hd hd) ?_)
  obtain ⟨b, hb⟩ := exists_coordG_eq φ Axis.one (hh.conj₁ d hd)
  have h1 : t⁻¹ * ((d * d)⁻¹ * t * (d * d)) = 1 := by
    rw [hh.mul₁ d hd d hd, ← hb, ← coordG_add, CharTwo.add_self_eq_zero, coordG_zero]
  have h2 : (d * d)⁻¹ * t * (d * d) = t := by
    calc (d * d)⁻¹ * t * (d * d) = t * (t⁻¹ * ((d * d)⁻¹ * t * (d * d))) := by group
      _ = t := by rw [h1, mul_one]
  calc d * d * t = (d * d) * ((d * d)⁻¹ * t * (d * d)) := by rw [h2]
    _ = t * (d * d) := by group

theorem exists_torus [Finite G] (hh : HeisHyp L K n φ TG t) {l : K} (hl : l ≠ 0) :
    ∃ j ∈ 𝐍₁ ⊓ 𝐂, (∀ b, j⁻¹ * coordG φ Axis.one b * j = coordG φ Axis.one (l * b)) ∧
      SAct φ t j (RingEquiv.refl K) ∧ SAct φ t j⁻¹ (RingEquiv.refl K) := by
  obtain ⟨δ, hδ, hδm⟩ := exists_diagTorus hl one_ne_zero
  have hjJ : ((φ.symm δ : L) : G) ∈ pull φ (diagTorus K) := symm_mem_pull.mpr hδ
  have hjN := (hh.normQ (hh.hyp.setup.diagTorus_le_normalizer hjJ)).1
  have hjC : ((φ.symm δ : L) : G) ∈ 𝐂 := hh.sec.two.L_le (φ.symm δ).2
  have hjt : ((φ.symm δ : L) : G) * t = t * ((φ.symm δ : L) : G) :=
    mem_centralizer_singleton_iff.mp hjC
  have hjt' : ((φ.symm δ : L) : G)⁻¹ * t * ((φ.symm δ : L) : G) = t := by
    rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  have hΩ : ∀ v : Fin 2 → K, ((φ.symm δ : L) : G)⁻¹ * ((φ.symm (aElt v 0) : L) : G) *
      ((φ.symm δ : L) : G) = ((φ.symm (aElt (l • v) 0) : L) : G) := by
    intro v
    refine Setup.symm_conj ?_
    rw [aElt, aElt, diagTorus_conj hl one_ne_zero hδm]
    congr 1 <;> simp
  have hinv : ∀ v, ((φ.symm δ : L) : G)⁻¹ * coord φ t (qgPoint v) * ((φ.symm δ : L) : G)⁻¹⁻¹ =
      coord φ t (qgPoint (l • v)) := by
    intro v
    rw [inv_inv, coord_qgPoint, coord_qgPoint, ← hΩ v]
    calc ((φ.symm δ : L) : G)⁻¹ * (t * ((φ.symm (aElt v 0) : L) : G)) * ((φ.symm δ : L) : G)
        = (((φ.symm δ : L) : G)⁻¹ * t * ((φ.symm δ : L) : G)) * (((φ.symm δ : L) : G)⁻¹ *
          ((φ.symm (aElt v 0) : L) : G) * ((φ.symm δ : L) : G)) := by group
      _ = _ := by rw [hjt']
  have hfwd : ∀ v, ((φ.symm δ : L) : G) * coord φ t (qgPoint v) * ((φ.symm δ : L) : G)⁻¹ =
      coord φ t (qgPoint (l⁻¹ • v)) := by
    intro v
    have e := hinv (l⁻¹ • v)
    rw [smul_smul, mul_inv_cancel₀ hl, one_smul, inv_inv] at e
    rw [← e]
    group
  refine ⟨_, ⟨hjN, hjC⟩, fun b => Setup.symm_conj ?_, SAct.of_smul (inv_ne_zero hl) hfwd,
    SAct.of_smul hl hinv⟩
  show δ⁻¹ * uElt 0 b 0 0 * δ = uElt 0 (l * b) 0 0
  rw [diagTorus_conj hl one_ne_zero hδm]
  congr 1 <;> ring

theorem sAct_D₁ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {d : G} (hd : d ∈ 𝐃₁) :
    SAct φ t d (RingEquiv.refl K) := by
  have hS := hh.sec.two
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨σ, hσ⟩ := exists_sAct hh.sec (hh.D₁_le_N₂ hd)
  obtain ⟨b, hb⟩ := exists_coordG_eq φ Axis.one (hh.conj₁ d hd)
  have hK2 : 2 < Nat.card K := by
    rw [hS.card_K]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne hK2 (1 : K)
  have hm0 : l + 1 ≠ 0 := fun h => hl1 (by linear_combination -h + h2)
  have hconj : ∀ {m : K}, m ≠ 0 → ∃ d' ∈ 𝐃₁, SAct φ t d' σ ∧
      t⁻¹ * (d'⁻¹ * t * d') = coordG φ Axis.one (m * b) := by
    intro m hm
    obtain ⟨j, ⟨hjN, hjC⟩, hjU, hj, hj'⟩ := hh.exists_torus hm
    refine ⟨j⁻¹ * d * j, by simpa using conj_mem_pCore_map (inv_mem hjN) hd,
      (hj'.mul hσ (τ := σ) fun _ => rfl).mul hj (τ := σ) fun _ => rfl, ?_⟩
    rw [conj_conj_eq (mem_centralizer_singleton_iff.mp hjC), ← hb, hjU]
  obtain ⟨d₁, hd₁, hσ₁, hu₁⟩ := hconj hl0
  obtain ⟨d₂, hd₂, hσ₂, hu₂⟩ := hconj hm0
  have hw : t⁻¹ * ((d₁ * d₂)⁻¹ * t * (d₁ * d₂)) = t⁻¹ * (d⁻¹ * t * d) := by
    rw [hh.mul₁ d₁ hd₁ d₂ hd₂, hu₁, hu₂, ← coordG_add, ← hb]
    congr 1
    linear_combination (l * b) * h2
  have hc : d₁ * d₂ * d⁻¹ ∈ 𝐐 := by
    refine hh.hyp.B_le_Q Axis.one (hh.mem_B₁ (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd)) ?_)
    have e : (d₁ * d₂)⁻¹ * t * (d₁ * d₂) = d⁻¹ * t * d := mul_left_cancel hw
    calc d₁ * d₂ * d⁻¹ * t = d₁ * d₂ * (d⁻¹ * t * d) * d⁻¹ := by group
      _ = d₁ * d₂ * ((d₁ * d₂)⁻¹ * t * (d₁ * d₂)) * d⁻¹ := by rw [e]
      _ = t * (d₁ * d₂ * d⁻¹) := by group
  obtain ⟨δ, hδ⟩ := hh.hAct_of_mem_Q (inv_mem hc)
  have hσ' : SAct φ t d (σ.trans σ) := by
    have e : d = (d₁ * d₂ * d⁻¹)⁻¹ * (d₁ * d₂) := by group
    rw [e]
    exact hδ.sAct.mul (hσ₁.mul hσ₂ (τ := σ.trans σ) fun _ => rfl) fun _ => rfl
  have hσσ := SAct.unique hS hσ hσ'
  have hσr : σ = RingEquiv.refl K := RingEquiv.ext fun x => by
    have e := DFunLike.congr_fun hσσ x
    rw [RingEquiv.trans_apply] at e
    exact (σ.injective e).symm
  rwa [hσr] at hσ

theorem hAct_of_mem_D₁ [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {d : G}
    (hd : d ∈ 𝐃₁) : ∃ y δ : K, HAct φ t d 0 y δ := by
  have hS := hh.sec.two
  obtain ⟨v₀, M, hM⟩ := hh.sAct_D₁ hd
  set m := (M : Matrix (Fin 2) (Fin 2) K)
  have hdet : m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  let g : (Fin 2 → K) → Fin 2 → K := fun v =>
    ![v₀ 0 + (m 0 0 * v 0 + m 0 1 * v 1), v₀ 1 + (m 1 0 * v 0 + m 1 1 * v 1)]
  have hdg : ∀ v, d * coord φ t (qgPoint v) * d⁻¹ = coord φ t (qgPoint (g v)) := by
    intro v
    rw [hM v]
    congr 2
    ext i
    fin_cases i <;> simp [g]
  obtain ⟨hq₁Q, hq₁⟩ := hh.shear_mem 1
  set q₁ := ((φ.symm (uElt 0 0 0 1) : L) : G)
  obtain ⟨δ', hδ'⟩ := hh.hAct_of_mem_Q (hh.conj_mem_Q hd hq₁Q)
  have rel1 : ∀ w, (![(g w) 0 + δ' * (g w) 1 + 0, (g w) 1 + 0] : Fin 2 → K) =
      g ![w 0 + 1 * w 1 + 0, w 1 + 0] := by
    intro w
    apply coord_qgPoint_injective hS
    calc coord φ t (qgPoint ![(g w) 0 + δ' * (g w) 1 + 0, (g w) 1 + 0])
        = (d * q₁ * d⁻¹) * coord φ t (qgPoint (g w)) * (d * q₁ * d⁻¹)⁻¹ := (hδ' (g w)).symm
      _ = (d * q₁ * d⁻¹) * (d * coord φ t (qgPoint w) * d⁻¹) * (d * q₁ * d⁻¹)⁻¹ := by
          rw [hdg w]
      _ = d * (q₁ * coord φ t (qgPoint w) * q₁⁻¹) * d⁻¹ := by group
      _ = d * coord φ t (qgPoint ![w 0 + 1 * w 1 + 0, w 1 + 0]) * d⁻¹ := by rw [hq₁ w]
      _ = coord φ t (qgPoint (g ![w 0 + 1 * w 1 + 0, w 1 + 0])) := hdg _
  have e1 := congrFun (rel1 ![0, 1]) 1
  have e2 := congrFun (rel1 ![0, 1]) 0
  have e3 := congrFun (rel1 0) 0
  simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at e1 e2 e3
  have h10 : m 1 0 = 0 := by linear_combination -e1
  have he2 : δ' * (v₀ 1 + m 1 1) = m 0 0 := by linear_combination e2
  have he3 : δ' * v₀ 1 = 0 := by linear_combination e3
  have hm00 : m 0 0 ≠ 0 := fun h0 => hdet (by rw [h0, h10]; ring)
  have hδ'0 : δ' ≠ 0 := fun h0 => hm00 (by rw [← he2, h0, zero_mul])
  have hv1 : v₀ 1 = 0 := (mul_eq_zero.mp he3).resolve_left hδ'0
  obtain ⟨ε, hε⟩ := hh.hAct_of_mem_Q (hh.sq_mem_Q hd)
  have rel2 : ∀ w, g (g w) = ![w 0 + ε * w 1 + 0, w 1 + 0] := by
    intro w
    apply coord_qgPoint_injective hS
    calc coord φ t (qgPoint (g (g w))) = d * coord φ t (qgPoint (g w)) * d⁻¹ := (hdg _).symm
      _ = d * (d * coord φ t (qgPoint w) * d⁻¹) * d⁻¹ := by rw [hdg w]
      _ = (d * d) * coord φ t (qgPoint w) * (d * d)⁻¹ := by group
      _ = _ := hε w
  have s0 := congrFun (rel2 0) 0
  have s1 := congrFun (rel2 ![1, 0]) 0
  have s2 := congrFun (rel2 ![0, 1]) 1
  simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at s0 s1 s2
  have h00 : m 0 0 * m 0 0 = 1 := by linear_combination s1 - s0 - m 0 1 * h10
  have h11 : m 1 1 * m 1 1 = 1 := by
    linear_combination s2 - (1 + m 1 1) * hv1 - (v₀ 0 + m 0 1) * h10
  have h00' := eq_one_of_mul_self_eq_one h00
  have h11' := eq_one_of_mul_self_eq_one h11
  refine ⟨v₀ 0, m 0 1, fun v => ?_⟩
  rw [hdg v]
  congr 2
  ext i
  fin_cases i
  · simp [g, h00']
    ring
  · simp [g, h11', h10, hv1]

theorem S_le_N₂ [Finite G] (hh : HeisHyp L K n φ TG t) : 𝐒 ≤ 𝐍₂ :=
  sup_le (fun _ hq => (hh.Q_le_N hq).2) (map_subtype_le _)

theorem Q_le_normalizer_D₁ [Finite G] (hh : HeisHyp L K n φ TG t) :
    𝐐 ≤ normalizer ((𝐃₁ : Subgroup G) : Set G) := fun _ hq =>
  le_normalizer_pCore_map (hh.Q_le_N hq).1

theorem Q_le_normalizer_D₂ [Finite G] (hh : HeisHyp L K n φ TG t) :
    𝐐 ≤ normalizer ((𝐃₂ : Subgroup G) : Set G) := fun _ hq =>
  le_normalizer_pCore_map (hh.Q_le_N hq).2

theorem exists_hAct_of_mem_S [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G}
    (hs : s ∈ 𝐒) : ∃ x y d : K, HAct φ t s x y d := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hh.Q_le_normalizer_D₂] at hs
  obtain ⟨q, hq, e, he, rfl⟩ := hs
  obtain ⟨δ, hδ⟩ := hh.hAct_of_mem_Q hq
  obtain ⟨x, y, hxy⟩ := hAct_of_mem_D hh.sec he
  exact ⟨_, _, _, hδ.mul hxy⟩

theorem exists_mem_S_hAct [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) (x y d : K) :
    ∃ s ∈ 𝐒, HAct φ t s x y d := by
  obtain ⟨e, he, hxy⟩ := exists_D_hAct hh.sec x y
  obtain ⟨hqQ, hq⟩ := hh.shear_mem d
  exact ⟨_, mul_mem (mem_sup_right he) (mem_sup_left hqQ),
    (hxy.mul hq).congr (by ring) (by ring) (by ring)⟩

theorem mem_S_of_hAct [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {g : G} (hg : g ∈ 𝐍₂)
    {x y d : K} (hx : HAct φ t g x y d) : g ∈ 𝐒 := by
  obtain ⟨s, hs, hsx⟩ := hh.exists_mem_S_hAct x y d
  have hb := inv_mul_mem_B hh.sec hg (hh.S_le_N₂ hs) hx hsx
  have e : g = s * (s⁻¹ * g) := by group
  rw [e]
  exact mul_mem hs (mem_sup_left (hh.hyp.B_le_Q Axis.two hb))

theorem R_le_S [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) : 𝐐 ⊔ 𝐃₁ ≤ 𝐒 :=
  sup_le le_sup_left fun d hd => by
    obtain ⟨y, δ, h⟩ := hh.hAct_of_mem_D₁ hd
    exact hh.mem_S_of_hAct (hh.D₁_le_N₂ hd) h

theorem mem_D₂_iff [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G} (hs : s ∈ 𝐒)
    {x y d : K} (hx : HAct φ t s x y d) : s ∈ 𝐃₂ ↔ d = 0 := by
  constructor
  · intro hd
    obtain ⟨x', y', h'⟩ := hAct_of_mem_D hh.sec hd
    exact (HAct.unique hh.sec.two hx h').2.2
  · rintro rfl
    obtain ⟨e, he, hxy⟩ := exists_D_hAct hh.sec x y
    have hb := inv_mul_mem_B hh.sec (hh.S_le_N₂ hs) (map_subtype_le _ he) hx hxy
    have e' : s = e * (e⁻¹ * s) := by group
    rw [e']
    exact mul_mem he (hh.sec.B_le_D hb)

theorem mem_Q_iff [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G} (hs : s ∈ 𝐒)
    {x y d : K} (hx : HAct φ t s x y d) : s ∈ 𝐐 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hq
    obtain ⟨δ, hδ⟩ := hh.hAct_of_mem_Q hq
    obtain ⟨h1, h2, -⟩ := HAct.unique hh.sec.two hx hδ
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨hqQ, hq⟩ := hh.shear_mem d
    have hb := inv_mul_mem_B hh.sec (hh.S_le_N₂ hs) (hh.Q_le_N hqQ).2 hx hq
    have e' : s = ((φ.symm (uElt 0 0 0 d) : L) : G) *
        (((φ.symm (uElt 0 0 0 d) : L) : G)⁻¹ * s) := by group
    rw [e']
    exact mul_mem hqQ (hh.hyp.B_le_Q Axis.two hb)

theorem mem_R_iff [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) {s : G} (hs : s ∈ 𝐒)
    {x y d : K} (hx : HAct φ t s x y d) : s ∈ 𝐐 ⊔ 𝐃₁ ↔ x = 0 := by
  constructor
  · intro hr
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hh.Q_le_normalizer_D₁] at hr
    obtain ⟨q, hq, e, he, rfl⟩ := hr
    obtain ⟨δ, hδ⟩ := hh.hAct_of_mem_Q hq
    obtain ⟨y', γ, hγ⟩ := hh.hAct_of_mem_D₁ he
    rw [(HAct.unique hh.sec.two hx (hδ.mul hγ)).1, add_zero]
  · rintro rfl
    obtain ⟨e, he, hey⟩ := hh.surj₁ _ (coordG_mem φ Axis.one y)
    obtain ⟨y', γ, hγ⟩ := hh.hAct_of_mem_D₁ (inv_mem he)
    have hy' : y' = y := by
      have e1 := hγ 0
      rw [inv_inv, qgPoint_zero, coord_qgT] at e1
      have e2 : e⁻¹ * t * e = coord φ t (qgPoint ![y, 0]) := by
        rw [coord_qgPoint]
        calc e⁻¹ * t * e = t * (t⁻¹ * (e⁻¹ * t * e)) := by group
          _ = t * coordG φ Axis.one y := by rw [hey]
      have e3 := congrFun (coord_qgPoint_injective hh.sec.two (e1.symm.trans e2)) 0
      simpa using e3
    subst hy'
    obtain ⟨hqQ, hq⟩ := hh.shear_mem (γ + d)
    have hr : HAct φ t (e⁻¹ * ((φ.symm (uElt 0 0 0 (γ + d)) : L) : G)) 0 y' d :=
      (hγ.mul hq).congr (by ring) (by ring)
        (by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add])
    have hrR : e⁻¹ * ((φ.symm (uElt 0 0 0 (γ + d)) : L) : G) ∈ 𝐐 ⊔ 𝐃₁ :=
      mul_mem (mem_sup_right (inv_mem he)) (mem_sup_left hqQ)
    have hb := inv_mul_mem_B hh.sec (hh.S_le_N₂ hs) (hh.S_le_N₂ (hh.R_le_S hrR)) hx hr
    have e' : s = (e⁻¹ * ((φ.symm (uElt 0 0 0 (γ + d)) : L) : G)) *
        ((e⁻¹ * ((φ.symm (uElt 0 0 0 (γ + d)) : L) : G))⁻¹ * s) := by group
    rw [e']
    exact mul_mem hrR (mem_sup_left (hh.hyp.B_le_Q Axis.two hb))

theorem exists_heisHom [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) :
    ∃ χ : 𝐒 →* unipAll K, (∀ (s : 𝐒) {x y d : K}, HAct φ t s x y d →
      (χ s : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K d x y) ∧
      χ.ker = 𝐁₂.subgroupOf 𝐒 ∧ Function.Surjective χ := by
  have hS := hh.sec.two
  have hex : ∀ s : 𝐒, ∃ p : K × K × K, HAct φ t s p.1 p.2.1 p.2.2 := fun s => by
    obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S s.2
    exact ⟨(x, y, d), h⟩
  choose c hc using hex
  have hcu : ∀ (s : 𝐒) {x y d : K}, HAct φ t s x y d → c s = (x, y, d) := fun s x y d h => by
    obtain ⟨h1, h2, h3⟩ := HAct.unique hS (hc s) h
    exact Prod.ext h1 (Prod.ext h2 h3)
  let χ : 𝐒 →* unipAll K :=
    { toFun := fun s => ⟨unipU K (c s).2.2 (c s).1 (c s).2.1, _, _, _, rfl⟩
      map_one' := by
        apply Subtype.ext
        rw [hcu 1 (hAct_of_mem_B hh.sec (one_mem _))]
        exact unipU_zero
      map_mul' := fun s s' => by
        apply Subtype.ext
        rw [hcu (s * s') ((hc s).mul (hc s'))]
        exact (unipU_mul _ _ _ _ _ _).symm }
  have hχ : ∀ (s : 𝐒) {x y d : K}, HAct φ t s x y d →
      (χ s : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K d x y := fun s x y d h => by
    change unipU K (c s).2.2 (c s).1 (c s).2.1 = _
    rw [hcu s h]
  refine ⟨χ, hχ, ?_, ?_⟩
  · ext s
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have e : unipU K (c s).2.2 (c s).1 (c s).2.1 = unipU K 0 0 0 := by
        rw [unipU_zero]
        exact congrArg Subtype.val h1
      obtain ⟨hd, hx, hy⟩ := unipU_inj' e
      have := inv_mul_mem_B hh.sec (hh.S_le_N₂ s.2) (one_mem _) ((hc s).congr hx hy hd)
        (hAct_of_mem_B hh.sec (one_mem _))
      simpa using this
    · intro hb
      apply Subtype.ext
      change unipU K (c s).2.2 (c s).1 (c s).2.1 = 1
      rw [hcu s (hAct_of_mem_B hh.sec hb), unipU_zero]
  · rintro ⟨g, a, b, c', rfl⟩
    obtain ⟨s, hs, hsx⟩ := hh.exists_mem_S_hAct b c' a
    exact ⟨⟨s, hs⟩, Subtype.ext (hχ ⟨s, hs⟩ hsx)⟩

theorem main [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t) (Q : Subgroup G)
    (hQ : Q = pull φ (antiUnipotent K) ⊔ TG) :
    let B₂ := zpowers t ⊔ pull φ (rootA K Axis.two)
    let N₁ := normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G)
    let N₂ := normalizer (B₂ : Set G)
    let D₁ := (CFSG.pCore 2 N₁).map N₁.subtype
    let D₂ := (CFSG.pCore 2 N₂).map N₂.subtype
    let R := Q ⊔ D₁
    let S := Q ⊔ D₂
    let ω : K → K → G := fun a b => t * ((φ.symm (uElt a b 0 0) : L) : G)
    ((Q : Set G) * D₁ = R ∧ (Q : Set G) * D₂ = S) ∧
      IsPGroup 2 R ∧ IsPGroup 2 S ∧ R < S ∧
      Nat.card R = 2 * (2 ^ n) ^ 5 ∧ Nat.card S = 2 * (2 ^ n) ^ 6 ∧ R.relIndex S = 2 ^ n ∧
      B₂ ≤ S ∧ ∃ _ : (B₂.subgroupOf S).Normal,
      (∀ s ∈ S, ∃! p : K × K × K, ∀ a b : K,
        s * ω a b * s⁻¹ = ω (a + p.1) (b + p.2.2 * a + p.2.1)) ∧
      ∃ θ : (↥S ⧸ B₂.subgroupOf S) ≃* unipAll K,
        (∀ s : S, ∀ x y d : K,
          (∀ a b : K, (s : G) * ω a b * (s : G)⁻¹ = ω (a + x) (b + d * a + y)) →
            (θ s : Matrix.SpecialLinearGroup (Fin 3) K) = unipU K d x y) ∧
        (∀ g, g ∈ (D₂.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ↔
          ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) ∧
        (∀ g, g ∈ (Q.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ↔
          ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
          ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) ∧
        (∀ g, g ∈ (R.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ↔
          ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) ∧
        (∀ E : Subgroup (↥S ⧸ B₂.subgroupOf S),
          Maximal (fun F : Subgroup (↥S ⧸ B₂.subgroupOf S) => IsElementaryAbelian 2 F) E ↔
            E = (R.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ∨
            E = (D₂.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S))) ∧
        (R.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ≠
          (D₂.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ∧
        (∀ g : ↥S ⧸ B₂.subgroupOf S, g ^ 2 = 1 →
          g ∈ (R.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ∨
            g ∈ (D₂.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S))) ∧
        (R.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ⊓
            (D₂.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) =
          center (↥S ⧸ B₂.subgroupOf S) ∧
        Nat.card (center (↥S ⧸ B₂.subgroupOf S)) = 2 ^ n := by
  subst hQ
  intro B₂ N₁ N₂ D₁ D₂ R S ω
  have hS := hh.sec.two
  have hRS : R ≤ S := hh.R_le_S
  have hSN : S ≤ N₂ := hh.S_le_N₂
  have hBQ : B₂ ≤ pull φ (antiUnipotent K) ⊔ TG := hh.hyp.B_le_Q Axis.two
  have hBS : B₂ ≤ S := hBQ.trans le_sup_left
  have hBR : B₂ ≤ R := hBQ.trans le_sup_left
  have hBn : (B₂.subgroupOf S).Normal := ⟨fun b hb s => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (hSN s.2) b).mp (mem_subgroupOf.mp hb))⟩
  obtain ⟨χ, hχ, hker, hsurj⟩ := hh.exists_heisHom
  obtain ⟨θ, hθ⟩ := exists_quotient_mulEquiv χ hker hsurj
  have hex : ∀ s : S, ∃ p : K × K × K, HAct φ t s p.1 p.2.1 p.2.2 := fun s => by
    obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S s.2
    exact ⟨(x, y, d), h⟩
  choose c hc using hex
  have hK : Nat.card K = 2 ^ n := hS.card_K
  have hcardB : Nat.card B₂ = 2 * (2 ^ n) ^ 3 := by rw [card_B hS, hK]
  have hcardS : Nat.card S = 2 * (2 ^ n) ^ 6 := by
    rw [card_eq_card_quotient_mul_card_subgroup (B₂.subgroupOf S), Nat.card_congr θ.toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBS).toEquiv, card_unipAll', hcardB, hK]
    ring
  have hcardR : Nat.card R = 2 * (2 ^ n) ^ 5 := by
    have hkerR : (χ.comp (inclusion hRS)).ker = B₂.subgroupOf R := by
      ext r
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
        mem_subgroupOf, coe_inclusion]
    have hmem : ∀ y d : K,
        (⟨unipU K d 0 y, d, 0, y, rfl⟩ : unipAll K) ∈ (χ.comp (inclusion hRS)).range := by
      intro y d
      obtain ⟨s, hs, hsx⟩ := hh.exists_mem_S_hAct 0 y d
      have hsR : s ∈ R := (hh.mem_R_iff hs hsx).mpr rfl
      refine ⟨⟨s, hsR⟩, Subtype.ext ?_⟩
      rw [MonoidHom.comp_apply]
      exact hχ _ (by rw [coe_inclusion]; exact hsx)
    have hbij : Function.Bijective fun p : K × K =>
        (⟨_, hmem p.1 p.2⟩ : (χ.comp (inclusion hRS)).range) := by
      refine ⟨fun p p' h => ?_, fun g => ?_⟩
      · obtain ⟨h1, -, h3⟩ := unipU_inj' (congrArg (fun z : (χ.comp (inclusion hRS)).range =>
          ((z : unipAll K) : Matrix.SpecialLinearGroup (Fin 3) K)) h)
        exact Prod.ext h3 h1
      · obtain ⟨z, r, rfl⟩ := g
        have hcr := hc (inclusion hRS r)
        rw [coe_inclusion] at hcr
        have hx0 : (c (inclusion hRS r)).1 = 0 := (hh.mem_R_iff (hRS r.2) hcr).mp r.2
        have e1 : ((χ.comp (inclusion hRS) r : unipAll K) : Matrix.SpecialLinearGroup (Fin 3) K) =
            unipU K (c (inclusion hRS r)).2.2 0 (c (inclusion hRS r)).2.1 := by
          rw [MonoidHom.comp_apply, hχ _ (hc (inclusion hRS r)), hx0]
        exact ⟨((c (inclusion hRS r)).2.1, (c (inclusion hRS r)).2.2),
          Subtype.ext (Subtype.ext e1.symm)⟩
    rw [← card_mul_index (χ.comp (inclusion hRS)).ker, index_ker,
      ← Nat.card_eq_of_bijective _ hbij, hkerR, Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv,
      hcardB, Nat.card_prod, hK]
    ring
  have hD' : ∀ g : ↥S ⧸ B₂.subgroupOf S,
      g ∈ (D₂.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ↔
        ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    intro g
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    rw [mem_map_mk_iff hh.sec.B_le_D, hθ, hχ s (hc s), unipU_apply_zero_one]
    exact hh.mem_D₂_iff s.2 (hc s)
  have hQ' : ∀ g : ↥S ⧸ B₂.subgroupOf S,
      g ∈ ((pull φ (antiUnipotent K) ⊔ TG).subgroupOf S).map
        (QuotientGroup.mk' (B₂.subgroupOf S)) ↔
        ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
        ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    intro g
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    rw [mem_map_mk_iff hBQ, hθ, hχ s (hc s), unipU_apply_one_two, unipU_apply_zero_two]
    exact hh.mem_Q_iff s.2 (hc s)
  have hR' : ∀ g : ↥S ⧸ B₂.subgroupOf S,
      g ∈ (R.subgroupOf S).map (QuotientGroup.mk' (B₂.subgroupOf S)) ↔
        ((θ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    intro g
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    rw [mem_map_mk_iff hBR, hθ, hχ s (hc s), unipU_apply_one_two]
    exact hh.mem_R_iff s.2 (hc s)
  obtain ⟨hmax, hne, hsq, hcent, hcardZ⟩ := heis_structure θ _ _ hR' hD'
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by linarith [hS.two_le])
  refine ⟨⟨(coe_mul_of_left_le_normalizer_right _ _ hh.Q_le_normalizer_D₁).symm,
    (coe_mul_of_left_le_normalizer_right _ _ hh.Q_le_normalizer_D₂).symm⟩,
    IsPGroup.of_card (n := 5 * n + 1) (by rw [hcardR]; ring),
    IsPGroup.of_card (n := 6 * n + 1) (by rw [hcardS]; ring),
    lt_of_le_of_ne hRS fun h => ?_, hcardR, hcardS, ?_, hBS, hBn, fun s hs => ?_, θ,
    fun s x y d h => ?_, hD', hQ', hR', hmax, hne, hsq, hcent, hcardZ.trans hK⟩
  · have h1 : Nat.card R = Nat.card S := by rw [h]
    rw [hcardR, hcardS] at h1
    have h2 : (2 ^ n) ^ 5 < (2 ^ n) ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  · have h1 := relIndex_mul_card R S
    rw [inf_of_le_left hRS, hcardR, hcardS] at h1
    exact Nat.eq_of_mul_eq_mul_right (m := 2 * (2 ^ n) ^ 5) (by positivity) (by rw [h1]; ring)
  · obtain ⟨x, y, d, h⟩ := hh.exists_hAct_of_mem_S hs
    refine ⟨(x, y, d), hAct_iff.mp h, fun p hp => ?_⟩
    obtain ⟨e1, e2, e3⟩ := HAct.unique hS (hAct_iff.mpr hp) h
    exact Prod.ext e1 (Prod.ext e2 e3)
  · rw [hθ]
    exact hχ s (hAct_iff.mpr h)

end HeisHyp

end OneAxisHeisenberg

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
