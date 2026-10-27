module

public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.F420L2
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.Prop711

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

section Unpack

variable {V : Type*} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem nat_unpack {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)}
    {U : Subgroup V} {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U ⊥ π) :
    ∃ β : ↥U ≃* Multiplicative (ι → K),
      ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥H) : MulAut V) u, hu⟩ = natAct Γ γ (β u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let e₀ : ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec ≃*
      Multiplicative (ι → K) :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have he₀ : ∀ m : ↥(FFModel.nat Γ).sec,
      e₀ (QuotientGroup.mk m) = (m.1 : Multiplicative (ι → K)) := fun m => rfl
  let f : ↥U →* Multiplicative (ι → K) := e₀.toMonoidHom.comp β
  have hf : ∀ u, f u = e₀ (β u) := fun u => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : β u = 1 := by
      apply e₀.injective
      rw [map_one, ← hf]
      exact hu
    have h2 := (hβk u).mp h1
    rw [Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := fun x => by
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨x, trivial⟩)
    exact ⟨u, by rw [hf, hu, he₀]⟩
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun γ u hu => ?_⟩
  set m : ↥(FFModel.nat Γ).sec := ⟨f u, trivial⟩ with hm
  have hum : β u = QuotientGroup.mk m := by
    apply e₀.injective
    rw [he₀, ← hf]
  have h1 := hβe γ u m hu trivial hum
  have h2 := congrArg e₀ h1
  rw [he₀] at h2
  exact h2

theorem nat_injective {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)}
    {U : Subgroup V} {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U ⊥ π) :
    Function.Injective π := by
  have hHU := h.2.2.2.1
  obtain ⟨β, hβ⟩ := nat_unpack h
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine natAct_faithful Γ γ fun m => ?_
  obtain ⟨u, rfl⟩ := β.surjective m
  have hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
  have h1 := hβ γ u hu
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ : ↥U) = u := by
    apply Subtype.ext
    show ((π γ : ↥H) : MulAut V) (u : V) = u
    rw [hγ]
    rfl
  rw [h2] at h1
  rw [← h1, mul_inv_cancel]

end Unpack

section Aut

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem unit_eq_one_of_card_two [Finite K] (hK : Nat.card K = 2) (u : Kˣ) : u = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card Kˣ = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim u 1

theorem proj_injective_of_card_two (hK : Nat.card K = 2) : Function.Injective (proj n K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ (proj n K).ker := hg
  rw [ker_proj, mem_scalars] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  rw [unit_eq_one_of_card_two hK c, Units.val_one] at hc
  apply Subtype.ext
  rw [hc]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply]

theorem aut_SL_of_card_two (hK : Nat.card K = 2) (hn : 3 ≤ n)
    (τ : MulAut (Matrix.SpecialLinearGroup (Fin n) K)) :
    ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      (∀ g, ((τ g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
            ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∨
      (∀ g, ((τ g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) *
            (((g⁻¹).transpose : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen (descendAut n K τ)
  have hσ : σ = RingEquiv.refl K := F420.ringEquiv_eq_refl_of_card_prime Nat.prime_two hK σ
  have hf : fieldAut n K σ = 1 := by rw [hσ]; exact map_one _
  rw [hf, mul_one] at hαeq
  have hinj := proj_injective_of_card_two (n := n) hK
  refine ⟨A, ?_⟩
  interval_cases ε
  · left
    intro g
    have h1 : proj n K (τ g) = proj n K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A g) := by
      rw [← descendAut_proj, hαeq, pow_zero, mul_one, conjAut_proj]
    rw [hinj h1, coe_slConjugation]
  · right
    intro g
    have h1 : proj n K (τ g) = proj n K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
          (g⁻¹).transpose) := by
      rw [← descendAut_proj, hαeq, pow_one, MulAut.mul_apply, dualAut_proj, conjAut_proj]
    rw [hinj h1, coe_slConjugation]

end Aut

section Rad

open scoped Matrix

variable {n : ℕ} {K : Type} [Field K]

@[expose] def blk (i j : Fin n) : Prop := (i : ℕ) < 2 ∧ 2 ≤ (j : ℕ)

instance (i j : Fin n) : Decidable (blk i j) := inferInstanceAs (Decidable (_ ∧ _))

variable (n K) in
@[expose] def blkMats : AddSubgroup (Matrix (Fin n) (Fin n) K) where
  carrier := {X | ∀ i j, ¬ blk i j → X i j = 0}
  add_mem' {X Y} hX hY i j h := by
    rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]
  zero_mem' i j _ := rfl
  neg_mem' {X} hX i j h := by
    rw [Matrix.neg_apply, hX i j h, neg_zero]

theorem blk_mul_eq_zero {X Y : Matrix (Fin n) (Fin n) K} (hX : X ∈ blkMats n K)
    (hY : Y ∈ blkMats n K) : X * Y = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hij : blk i j
  · have hjk : ¬ blk j k := fun h => by
      have := hij.2
      have := h.1
      omega
    rw [hY j k hjk, mul_zero]
  · rw [hX i j hij, zero_mul]

theorem det_one_add_of_mem_blkMats {X : Matrix (Fin n) (Fin n) K} (hX : X ∈ blkMats n K) :
    (1 + X).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have h0 : X i i = 0 := hX i i fun h => by have := h.1; have := h.2; omega
    rw [Matrix.add_apply, Matrix.one_apply_eq, h0, add_zero]
  · intro i j hij
    have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
    have h0 : X i j = 0 := hX i j fun h => by
      have h1 := h.1
      have h2 := h.2
      have : (j : ℕ) < (i : ℕ) := hij
      omega
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, h0, add_zero]

variable (n K) in
@[expose] def radHom : Multiplicative (blkMats n K) →* Matrix.SpecialLinearGroup (Fin n) K where
  toFun X := ⟨1 + ((Multiplicative.toAdd X : blkMats n K) : Matrix (Fin n) (Fin n) K),
    det_one_add_of_mem_blkMats (Multiplicative.toAdd X).2⟩
  map_one' := by
    apply Subtype.ext
    show 1 + ((0 : blkMats n K) : Matrix (Fin n) (Fin n) K) = 1
    rw [AddSubgroup.coe_zero, add_zero]
  map_mul' X Y := by
    apply Subtype.ext
    show 1 + (((Multiplicative.toAdd X + Multiplicative.toAdd Y : blkMats n K)) :
        Matrix (Fin n) (Fin n) K) =
      (1 + ((Multiplicative.toAdd X : blkMats n K) : Matrix (Fin n) (Fin n) K)) *
        (1 + ((Multiplicative.toAdd Y : blkMats n K) : Matrix (Fin n) (Fin n) K))
    rw [AddSubgroup.coe_add, add_mul, one_mul, mul_add, mul_one,
      blk_mul_eq_zero (Multiplicative.toAdd X).2 (Multiplicative.toAdd Y).2, add_zero]
    abel

theorem coe_radHom (X : Multiplicative (blkMats n K)) :
    ((radHom n K X : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + ((Multiplicative.toAdd X : blkMats n K) : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem radHom_injective : Function.Injective (radHom n K) := by
  intro X Y h
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) K =>
    ((g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
  simp only [coe_radHom, add_right_inj] at h1
  exact Multiplicative.toAdd.injective (Subtype.ext h1)

variable (n K) in
@[expose] def rad : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) := (radHom n K).range

theorem rad_mulVec {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ rad n K)
    {v : Fin n → K} (hv : ∀ j : Fin n, 2 ≤ (j : ℕ) → v j = 0) :
    (g : Matrix (Fin n) (Fin n) K).mulVec v = v := by
  obtain ⟨X, rfl⟩ := hg
  rw [coe_radHom, Matrix.add_mulVec, Matrix.one_mulVec, add_eq_left]
  ext i
  rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hij : blk i j
  · rw [hv j hij.2, mul_zero]
  · rw [(Multiplicative.toAdd X).2 i j hij, zero_mul]

theorem rad_transpose_mulVec {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ rad n K)
    {v : Fin n → K} (hv : ∀ i : Fin n, (i : ℕ) < 2 → v i = 0) :
    (g : Matrix (Fin n) (Fin n) K)ᵀ.mulVec v = v := by
  obtain ⟨X, rfl⟩ := hg
  rw [coe_radHom, Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mulVec,
    Matrix.one_mulVec, add_eq_left]
  ext j
  rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.transpose_apply]
  by_cases hij : blk i j
  · rw [hv i hij.1, mul_zero]
  · rw [(Multiplicative.toAdd X).2 i j hij, zero_mul]

theorem inv_transpose_mulVec {g : Matrix.SpecialLinearGroup (Fin n) K} {v : Fin n → K}
    (h : (g : Matrix (Fin n) (Fin n) K)ᵀ.mulVec v = v) :
    (((g⁻¹).transpose : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).mulVec v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one, Matrix.one_mulVec]

end Rad

section Count

open scoped Matrix

variable {n : ℕ} {K : Type} [Field K]

@[expose] def blkEquiv : blkMats n K ≃ ({p : Fin n × Fin n // blk p.1 p.2} → K) where
  toFun X p := (X : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2
  invFun x := ⟨Matrix.of fun i j => if h : blk i j then x ⟨(i, j), h⟩ else 0,
    fun i j h => by simp [h]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : blk i j
    · simp [h]
    · simp [h, X.2 i j h]
  right_inv x := by
    ext p
    simp [p.2]

theorem card_rad [Finite K] :
    Nat.card (rad n K) = Nat.card K ^ Nat.card {p : Fin n × Fin n // blk p.1 p.2} := by
  rw [← Nat.card_fun]
  refine (Nat.card_congr (MonoidHom.ofInjective radHom_injective).toEquiv).symm.trans ?_
  exact Nat.card_congr (Multiplicative.toAdd.trans blkEquiv)

theorem card_le_low [Finite K] (hn : 2 ≤ n) :
    Nat.card K ^ 2 ≤ Nat.card {v : Fin n → K // ∀ j : Fin n, 2 ≤ (j : ℕ) → v j = 0} := by
  have hc : Nat.card (Fin 2 → K) = Nat.card K ^ 2 := by rw [Nat.card_fun, Nat.card_fin]
  rw [← hc]
  refine Nat.card_le_card_of_injective (fun w => ⟨fun j => if h : (j : ℕ) < 2 then
    w ⟨j, h⟩ else 0, fun j hj => by simp [show ¬ (j : ℕ) < 2 by omega]⟩) ?_
  intro w w' h
  funext k
  have h1 := congrFun (congrArg Subtype.val h) ⟨k, by omega⟩
  simpa [k.2] using h1

theorem card_le_high [Finite K] (hn : 4 ≤ n) :
    Nat.card K ^ 2 ≤ Nat.card {v : Fin n → K // ∀ i : Fin n, (i : ℕ) < 2 → v i = 0} := by
  have hc : Nat.card (Fin 2 → K) = Nat.card K ^ 2 := by rw [Nat.card_fun, Nat.card_fin]
  rw [← hc]
  refine Nat.card_le_card_of_injective (fun w => ⟨fun i => if h : 2 ≤ (i : ℕ) ∧ (i : ℕ) < 4 then
    w ⟨i - 2, by omega⟩ else 0, fun i hi => by
      simp [show ¬ (2 ≤ (i : ℕ) ∧ (i : ℕ) < 4) by omega]⟩) ?_
  intro w w' h
  funext k
  have h1 := congrFun (congrArg Subtype.val h) ⟨k + 2, by omega⟩
  have hk : (2 ≤ (k : ℕ) + 2 ∧ (k : ℕ) + 2 < 4) := ⟨by omega, by omega⟩
  simpa [hk] using h1

theorem card_inf_mul_card_inf_le {V : Type*} [CommGroup V] [Finite V] {U W : Subgroup V}
    (hUW : U ⊓ W = ⊥) (X : Subgroup V) :
    Nat.card ↥(U ⊓ X) * Nat.card ↥(W ⊓ X) ≤ Nat.card X := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => ⟨(p.1 : V) * p.2, X.mul_mem p.1.2.2 p.2.2.2⟩) ?_
  rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩ h
  have h1 : u * w = u' * w' := congrArg Subtype.val h
  have h2 : u'⁻¹ * u = w' * w⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * w) * w⁻¹ := by group
      _ = u'⁻¹ * (u' * w') * w⁻¹ := by rw [h1]
      _ = w' * w⁻¹ := by group
  have h3 : u'⁻¹ * u ∈ U ⊓ W := ⟨U.mul_mem (U.inv_mem hu'.1) hu.1, by
    rw [h2]; exact W.mul_mem hw'.1 (W.inv_mem hw.1)⟩
  rw [hUW, Subgroup.mem_bot] at h3
  have hu1 : u = u' := (inv_mul_eq_one.mp h3).symm
  have hw1 : w = w' := by
    rw [hu1] at h1
    exact mul_left_cancel h1
  subst hu1
  subst hw1
  rfl

theorem card_le_card_mul_card {V : Type*} [CommGroup V] [Finite V] {U W : Subgroup V}
    (hUW : U ⊔ W = ⊤) : Nat.card V ≤ Nat.card U * Nat.card W := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective (fun p : ↥U × ↥W => (p.1 : V) * p.2) ?_
  intro v
  have hv : v ∈ U ⊔ W := by rw [hUW]; exact Subgroup.mem_top v
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hv
  exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩

theorem conj_mulVec_of_mulVec {n : ℕ} {K : Type} [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K)
    {M : Matrix (Fin n) (Fin n) K} {v : Fin n → K} (hv : M *ᵥ v = v) :
    ((A : Matrix (Fin n) (Fin n) K) * M *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = (A : Matrix (Fin n) (Fin n) K) *ᵥ v := by
  have hAA : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (A : Matrix (Fin n) (Fin n) K), hAA,
    Matrix.mul_one, ← Matrix.mulVec_mulVec, hv]

theorem mulVec_injective_GL {n : ℕ} {K : Type} [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    Function.Injective fun v : Fin n → K => (A : Matrix (Fin n) (Fin n) K) *ᵥ v := by
  intro v w h
  have hAA : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 := congrArg (fun x => ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K) *ᵥ x) h
  simpa only [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] using h1

end Count

section Fact

open scoped Matrix

theorem exists_slData {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {n : ℕ} (h : BinaryNaturalSL H U ⊥ n 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ (ρ : Matrix.SpecialLinearGroup (Fin n) K ≃* ↥H) (β : ↥U ≃* Multiplicative (Fin n → K)),
        (∀ (g : Matrix.SpecialLinearGroup (Fin n) K) (u : ↥U),
          ((ρ g : ↥H) : MulAut V) (u : V) ∈ U) ∧
        ∀ (g : Matrix.SpecialLinearGroup (Fin n) K) (u : ↥U)
          (hu : ((ρ g : ↥H) : MulAut V) (u : V) ∈ U),
          β ⟨((ρ g : ↥H) : MulAut V) u, hu⟩ = Multiplicative.ofAdd
            ((g : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd (β u)) := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  obtain ⟨β, hβ⟩ := nat_unpack hπ
  let e := MulEquiv.ofBijective π ⟨nat_injective hπ, hπ.1⟩
  refine ⟨K, inferInstance, inferInstance, by rw [hK, pow_one],
    (specialLinearGroupEquivStatedSL n K).trans e, β,
    fun g u => hπ.2.2.2.1 _ u u.2, fun g u hu => hβ _ u hu⟩

theorem factLnPairFF_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ (H : Subgroup (MulAut V)) (U W : Subgroup V) (n : ℕ), (n = 4 ∨ n = 5) →
        U ⊓ W = ⊥ → U ⊔ W = ⊤ → BinaryNaturalSL H U ⊥ n 1 → BinaryNaturalSL H W ⊥ n 1 →
          IsFFModule H := by
  intro V _ _ hV2 H U W n hn hUW hUW' hU hW
  have hn4 : 4 ≤ n := by omega
  obtain ⟨K, _, _, hK, ρU, βU, hUinv, hβU⟩ := exists_slData hU
  obtain ⟨K', _, _, hK', ρW, βW, hWinv, hβW⟩ := exists_slData hW
  set φ : K' ≃+* K := (QuasithinUnique.Setup.Family.ringEquivZMod2 K' hK').trans
    (QuasithinUnique.Setup.Family.ringEquivZMod2 K hK).symm with hφ
  set Φ : Matrix.SpecialLinearGroup (Fin n) K' ≃* Matrix.SpecialLinearGroup (Fin n) K :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map φ.toRingHom)
      (Matrix.SpecialLinearGroup.map φ.symm.toRingHom)
      (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
      (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    with hΦ
  set τ : MulAut (Matrix.SpecialLinearGroup (Fin n) K) := (ρU.trans ρW.symm).trans Φ with hτ
  obtain ⟨A, hA⟩ := aut_SL_of_card_two hK (by omega) τ
  have h2K : (2 : K) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact_mod_cast h
  set E : Subgroup (MulAut V) := ((rad n K).map ρU.toMonoidHom).map H.subtype with hE
  have hEH : E ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hEmem : ∀ a ∈ E, ∃ g ∈ rad n K, a = ((ρU g : ↥H) : MulAut V) := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  have hgE : ∀ g ∈ rad n K, ((ρU g : ↥H) : MulAut V) ∈ E := fun g hg =>
    ⟨ρU g, ⟨g, hg, rfl⟩, rfl⟩
  have hEcard : Nat.card E = Nat.card (rad n K) := by
    rw [hE, Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective ρU.injective]
  have hfixU : ∀ v : Fin n → K, (∀ j : Fin n, 2 ≤ (j : ℕ) → v j = 0) →
      ((βU.symm (Multiplicative.ofAdd v) : ↥U) : V) ∈ U ⊓ fixV E := by
    intro v hv
    refine ⟨(βU.symm (Multiplicative.ofAdd v)).2, fun a ha => ?_⟩
    obtain ⟨g, hg, rfl⟩ := hEmem a ha
    have h1 := hβU g (βU.symm (Multiplicative.ofAdd v))
      (hUinv g (βU.symm (Multiplicative.ofAdd v)))
    rw [βU.apply_symm_apply, toAdd_ofAdd, rad_mulVec hg hv] at h1
    have h2 := congrArg Subtype.val (βU.injective (h1.trans (βU.apply_symm_apply _).symm))
    exact h2
  have hfixW : ∀ v : Fin n → K, (∀ g ∈ rad n K,
      ((τ g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v) →
      ((βW.symm (Multiplicative.ofAdd (φ.symm ∘ v)) : ↥W) : V) ∈ W ⊓ fixV E := by
    intro v hv
    refine ⟨(βW.symm _).2, fun a ha => ?_⟩
    obtain ⟨g, hg, rfl⟩ := hEmem a ha
    set g' := ρW.symm (ρU g) with hg'
    have hρ : ρW g' = ρU g := ρW.apply_symm_apply _
    have hτg : τ g = Φ g' := rfl
    have h1 := hβW g' (βW.symm (Multiplicative.ofAdd (φ.symm ∘ v)))
      (hWinv g' (βW.symm (Multiplicative.ofAdd (φ.symm ∘ v))))
    rw [βW.apply_symm_apply, toAdd_ofAdd] at h1
    have h3 : (g' : Matrix (Fin n) (Fin n) K') *ᵥ (φ.symm ∘ v) = φ.symm ∘ v := by
      funext i
      apply φ.injective
      have h4 := RingHom.map_mulVec φ.toRingHom (g' : Matrix (Fin n) (Fin n) K') (φ.symm ∘ v) i
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h4
      rw [h4]
      have h5 : φ ∘ (φ.symm ∘ v) = v := by
        funext j
        simp
      rw [h5]
      have h6 : (g' : Matrix (Fin n) (Fin n) K').map φ =
          ((Φ g' : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [hΦ, MonoidHom.toMulEquiv_apply, Matrix.SpecialLinearGroup.map_apply_coe,
          RingHom.mapMatrix_apply]
        rfl
      rw [h6, ← hτg, hv g hg]
      simp
    rw [h3] at h1
    have h7 := βW.injective (h1.trans (βW.apply_symm_apply _).symm)
    rw [← hρ]
    exact congrArg Subtype.val h7
  have hrad1 : ∃ g ∈ rad n K, g ≠ 1 := by
    let X₀ : Matrix (Fin n) (Fin n) K :=
      Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 2 then 1 else 0
    have hX₀ : X₀ ∈ blkMats n K := fun i j h => by
      simp only [X₀, Matrix.of_apply]
      refine ite_eq_right_iff.mpr fun hij => ?_
      exact absurd ⟨by omega, by omega⟩ h
    refine ⟨radHom n K (Multiplicative.ofAdd ⟨X₀, hX₀⟩), ⟨_, rfl⟩, fun h => ?_⟩
    have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨2, by omega⟩) h
    simp [coe_radHom, X₀] at h1
  have hE0 : E ≠ ⊥ := by
    obtain ⟨g, hg, hg1⟩ := hrad1
    intro hbot
    have h1 := hgE g hg
    rw [hbot, Subgroup.mem_bot] at h1
    apply hg1
    apply ρU.injective
    rw [map_one]
    exact Subtype.ext h1
  have hradc : ∀ g ∈ rad n K, ∀ h ∈ rad n K, g * h = h * g := by
    rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hrad2 : ∀ g ∈ rad n K, g * g = 1 := by
    rintro _ ⟨X, rfl⟩
    rw [← map_mul]
    have hX : X * X = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      ext i j
      show ((Multiplicative.toAdd X : blkMats n K) : Matrix (Fin n) (Fin n) K) i j +
        ((Multiplicative.toAdd X : blkMats n K) : Matrix (Fin n) (Fin n) K) i j = 0
      rw [← two_mul, h2K, zero_mul]
    rw [hX, map_one]
  have hEab : IsElemAbelian2 E := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := hEmem a ha
      obtain ⟨h, hh, rfl⟩ := hEmem b hb
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hradc g hg h hh]
    · obtain ⟨g, hg, rfl⟩ := hEmem a ha
      rw [pow_two, ← Subgroup.coe_mul, ← map_mul, hrad2 g hg, map_one, Subgroup.coe_one]
  have hVc := card_le_card_mul_card hUW'
  have hUc : Nat.card U = 2 ^ n := by
    rw [Nat.card_congr βU.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_fin, hK]
  have hWc : Nat.card W = 2 ^ n := by
    rw [Nat.card_congr βW.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_fin, hK']
  have hblk : Nat.card {p : Fin n × Fin n // blk p.1 p.2} = 2 * (n - 2) := by
    rw [Nat.card_eq_fintype_card]
    rcases hn with rfl | rfl <;> decide
  have hEc : Nat.card E = 2 ^ (2 * (n - 2)) := by
    rw [hEcard, card_rad, hK, hblk]
  have hfix := card_inf_mul_card_inf_le hUW (fixV E)
  have hK2 : Nat.card K ^ 2 = 4 := by rw [hK]; norm_num
  have hU4 : 4 ≤ Nat.card ↥(U ⊓ fixV E) := by
    refine (hK2 ▸ card_le_low (K := K) (n := n) (by omega)).trans
      (Nat.card_le_card_of_injective (fun v => ⟨_, hfixU v.1 v.2⟩) ?_)
    intro v w h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (Multiplicative.ofAdd.injective (βU.symm.injective (Subtype.ext h1)))
  have hW4 : 4 ≤ Nat.card ↥(W ⊓ fixV E) := by
    rcases hA with hA1 | hA2
    · refine (hK2 ▸ card_le_low (K := K) (n := n) (by omega)).trans
        (Nat.card_le_card_of_injective (fun v => ⟨_, hfixW ((A : Matrix (Fin n) (Fin n) K) *ᵥ v.1)
          (fun g hg => by rw [hA1 g]; exact conj_mulVec_of_mulVec A (rad_mulVec hg v.2))⟩) ?_)
      intro v w h
      have h' : ((βW.symm (Multiplicative.ofAdd
          (φ.symm ∘ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v.1))) : ↥W) : V) =
          ((βW.symm (Multiplicative.ofAdd
            (φ.symm ∘ ((A : Matrix (Fin n) (Fin n) K) *ᵥ w.1))) : ↥W) : V) :=
        congrArg (fun x : ↥(W ⊓ fixV E) => (x : V)) h
      have h0 := Subtype.ext h'
      have h1 := Multiplicative.ofAdd.injective (βW.symm.injective h0)
      have h2 : (A : Matrix (Fin n) (Fin n) K) *ᵥ v.1 = (A : Matrix (Fin n) (Fin n) K) *ᵥ w.1 := by
        funext i
        have := congrFun h1 i
        simpa using congrArg φ this
      exact Subtype.ext (mulVec_injective_GL A h2)
    · refine (hK2 ▸ card_le_high (K := K) (n := n) hn4).trans
        (Nat.card_le_card_of_injective (fun v => ⟨_, hfixW ((A : Matrix (Fin n) (Fin n) K) *ᵥ v.1)
          (fun g hg => by
            rw [hA2 g]
            exact conj_mulVec_of_mulVec A
              (inv_transpose_mulVec (rad_transpose_mulVec hg v.2)))⟩) ?_)
      intro v w h
      have h' : ((βW.symm (Multiplicative.ofAdd
          (φ.symm ∘ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v.1))) : ↥W) : V) =
          ((βW.symm (Multiplicative.ofAdd
            (φ.symm ∘ ((A : Matrix (Fin n) (Fin n) K) *ᵥ w.1))) : ↥W) : V) :=
        congrArg (fun x : ↥(W ⊓ fixV E) => (x : V)) h
      have h0 := Subtype.ext h'
      have h1 := Multiplicative.ofAdd.injective (βW.symm.injective h0)
      have h2 : (A : Matrix (Fin n) (Fin n) K) *ᵥ v.1 = (A : Matrix (Fin n) (Fin n) K) *ᵥ w.1 := by
        funext i
        have := congrFun h1 i
        simpa using congrArg φ this
      exact Subtype.ext (mulVec_injective_GL A h2)
  refine ⟨E, hEH, hE0, hEab, ?_⟩
  have harith : 2 ^ n * 2 ^ n = 2 ^ (2 * (n - 2)) * (4 * 4) := by
    rcases hn with rfl | rfl <;> norm_num
  calc Nat.card V ≤ Nat.card U * Nat.card W := hVc
    _ = 2 ^ (2 * (n - 2)) * (4 * 4) := by rw [hUc, hWc, harith]
    _ ≤ Nat.card E * (Nat.card ↥(U ⊓ fixV E) * Nat.card ↥(W ⊓ fixV E)) := by
        rw [hEc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hU4 hW4)
    _ ≤ Nat.card E * Nat.card (fixV E) := Nat.mul_le_mul_left _ hfix

end Fact

end CFSG.Quasithin.H13.Prop711
