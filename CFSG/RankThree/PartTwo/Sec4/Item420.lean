module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.LocalRank.HyperplaneDecomposition
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.GroupTheory.FrattiniQuotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec4

section

open Module

section Involutions

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem finrank_ker_sub_one_add_finrank_ker_add_one (h2 : (2 : F) ≠ 0) (σ : V →ₗ[F] V)
    (hσ : σ * σ = 1) :
    finrank F (LinearMap.ker (σ - 1)) + finrank F (LinearMap.ker (σ + 1)) = finrank F V := by
  have hrange : LinearMap.range (σ - 1) = LinearMap.ker (σ + 1) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      have h : (σ + 1) * (σ - 1) = σ * σ - 1 := by noncomm_ring
      have := congrArg (fun T : V →ₗ[F] V => T v) h
      simp only [Module.End.mul_apply, hσ, sub_self, LinearMap.zero_apply] at this
      exact this
    · intro w hw
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hw
      refine ⟨-(2 : F)⁻¹ • w, ?_⟩
      have hσw : σ w = -w := eq_neg_of_add_eq_zero_left hw
      have hm : σ w - w = (-(2 : F)) • w := by
        rw [hσw, neg_smul, two_smul]
        abel
      calc (σ - 1) (-(2 : F)⁻¹ • w) = (-(2 : F)⁻¹) • (σ w - w) := by
            rw [LinearMap.sub_apply, Module.End.one_apply, map_smul, smul_sub]
        _ = (-(2 : F)⁻¹) • ((-(2 : F)) • w) := by rw [hm]
        _ = w := by rw [smul_smul, neg_mul_neg, inv_mul_cancel₀ h2, one_smul]
  rw [← hrange, add_comm, LinearMap.finrank_range_add_finrank_ker]

theorem finrank_le_sum_fixed (h2 : (2 : F) ≠ 0) (a b : V →ₗ[F] V) (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) :
    finrank F V ≤ finrank F (LinearMap.ker (a - 1)) + finrank F (LinearMap.ker (b - 1)) +
      finrank F (LinearMap.ker (a * b - 1)) := by
  set E := LinearMap.ker (a + 1) with hE
  have hbE : ∀ w ∈ E, b w ∈ E := by
    intro w hw
    rw [hE, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hw ⊢
    rw [← Module.End.mul_apply, hab, Module.End.mul_apply, ← map_add, hw, map_zero]
  set b' : E →ₗ[F] E := b.restrict hbE with hb'
  have hb'2 : b' * b' = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change b (b w) = (w : V)
    rw [← Module.End.mul_apply, hb, Module.End.one_apply]
  have h1 := finrank_ker_sub_one_add_finrank_ker_add_one h2 a ha
  have h2' := finrank_ker_sub_one_add_finrank_ker_add_one h2 b' hb'2
  have hle1 : (LinearMap.ker (b' - 1)).map E.subtype ≤ LinearMap.ker (b - 1) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hw
    rw [LinearMap.mem_ker]
    have := congrArg Subtype.val hw
    simpa [hb', LinearMap.sub_apply, sub_eq_zero] using this
  have hle2 : (LinearMap.ker (b' + 1)).map E.subtype ≤ LinearMap.ker (a * b - 1) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hw
    rw [LinearMap.mem_ker]
    have hbw : b (w : V) = -(w : V) := by
      have := congrArg Subtype.val hw
      simp only [hb', LinearMap.add_apply, LinearMap.restrict_apply, Module.End.one_apply,
        Submodule.coe_add, ZeroMemClass.coe_zero] at this
      exact eq_neg_of_add_eq_zero_left this
    have haw : a (w : V) = -(w : V) := by
      have : (a + 1) (w : V) = 0 := w.2
      rw [LinearMap.add_apply, Module.End.one_apply] at this
      exact eq_neg_of_add_eq_zero_left this
    change a (b (w : V)) - (w : V) = 0
    rw [hbw, map_neg, haw, neg_neg, sub_self]
  have e1 := Submodule.finrank_mono hle1
  have e2 := Submodule.finrank_mono hle2
  rw [Submodule.finrank_map_subtype_eq] at e1 e2
  have h1' : finrank F (LinearMap.ker (a - 1)) + finrank F E = finrank F V := h1
  omega

end Involutions

section Hyperplanes

open CFSG.RankThree.LocalRank

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {A : Type*} [CommGroup A] [Finite A]

@[expose] noncomputable def repRestrict (α : Representation F A V) (U : Submodule F V)
    (hU : ∀ a, ∀ u ∈ U, α a u ∈ U) : Representation F A U where
  toFun a := (α a).restrict (hU a)
  map_one' := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change α 1 (u : V) = u
    rw [map_one, Module.End.one_apply]
  map_mul' a b := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change α (a * b) (u : V) = α a (α b u)
    rw [map_mul, Module.End.mul_apply]

omit [FiniteDimensional F V] [Finite A] in
theorem repRestrict_apply (α : Representation F A V) (U : Submodule F V)
    (hU : ∀ a, ∀ u ∈ U, α a u ∈ U) (a : A) (u : U) :
    ((repRestrict α U hU a u : U) : V) = α a u :=
  rfl

open _root_.Classical in
theorem thirteen_le_finrank (h3 : (3 : F) ≠ 0) (hA : ∀ a : A, a ^ 3 = 1)
    (α : Representation F A V) (hα : ∃ a v, α a v ≠ v) (θ : A ≃* A) (β : V ≃ₗ[F] V)
    (hβ : ∀ a v, β (α a v) = α (θ a) (β v))
    (horb : ∀ D : Subgroup A, D.index = 3 → ∀ i j : ℕ, i < 13 → j < 13 →
      D.map ((θ ^ i : A ≃* A) : A →* A) = D.map ((θ ^ j : A ≃* A) : A →* A) → i = j) :
    13 ≤ finrank F V := by
  have h3' : ((3 : ℕ) : F) ≠ 0 := by exact_mod_cast h3
  set S : Set V := {v | ∃ (a : A) (u : V), α a u - u = v} with hS
  set U : Submodule F V := Submodule.span F S with hU
  have hUinv : ∀ a, ∀ u ∈ U, α a u ∈ U := by
    intro a u hu
    have hle : U ≤ U.comap (α a) := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨b, v, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, ← Module.End.mul_apply, ← map_mul]
      have e : α (a * b) v - α a v = (α (a * b) v - v) - (α a v - v) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨a * b, v, rfl⟩)
        (Submodule.subset_span ⟨a, v, rfl⟩)
    exact hle hu
  have hUβ : ∀ u ∈ U, β u ∈ U := by
    intro u hu
    have hle : U ≤ U.comap (β : V →ₗ[F] V) := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨b, v, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, map_sub, hβ]
      exact Submodule.subset_span ⟨θ b, β v, rfl⟩
    exact hle hu
  have hUβ' : ∀ u ∈ U, β.symm u ∈ U := by
    intro u hu
    have hle : U ≤ U.comap (β.symm : V →ₗ[F] V) := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨b, v, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, map_sub]
      have : β.symm (α b v) = α (θ.symm b) (β.symm v) := by
        apply β.injective
        rw [LinearEquiv.apply_symm_apply, hβ, MulEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.subset_span ⟨θ.symm b, β.symm v, rfl⟩
    exact hle hu
  set αU := repRestrict α U hUinv with hαU
  have hspan : Submodule.span F {w : U | ∃ (a : A) (u : U), αU a u - u = w} = ⊤ := by
    set W := Submodule.span F {w : U | ∃ (a : A) (u : U), αU a u - u = w}
    have hav : ∀ v : V, v - averaging α ⊤ v ∈ U := by
      intro v
      let := Fintype.ofFinite (⊤ : Subgroup A)
      have hc := natCast_card_subgroup_ne_zero (K := F) Nat.prime_three hA h3' (⊤ : Subgroup A)
      have e : v - averaging α ⊤ v = -((Nat.card (⊤ : Subgroup A) : F)⁻¹ •
          ∑ b : (⊤ : Subgroup A), (α b v - v)) := by
        rw [averaging_apply_sum, Finset.sum_sub_distrib, smul_sub, Finset.sum_const,
          Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul F, smul_smul,
          inv_mul_cancel₀ hc, one_smul]
        abel
      rw [e]
      exact U.neg_mem (U.smul_mem _ (U.sum_mem fun b _ => Submodule.subset_span ⟨b, v, rfl⟩))
    have hUW : U ≤ W.map U.subtype := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, v, rfl⟩
      set u : U := ⟨v - averaging α ⊤ v, hav v⟩
      refine ⟨αU a u - u, Submodule.subset_span ⟨a, u, rfl⟩, ?_⟩
      have hfix : α a (averaging α ⊤ v) = averaging α ⊤ v := rep_averaging α (Subgroup.mem_top a) v
      simp only [Submodule.subtype_apply, u, hαU, repRestrict_apply, map_sub,
        hfix]
      abel
    rw [eq_top_iff]
    intro w _
    obtain ⟨w', hw', hww'⟩ := hUW w.2
    exact (Subtype.ext hww' : w' = w) ▸ hw'
  obtain ⟨hbij, -, -⟩ := coprime_hyperplane_module_decomposition (α := αU) Nat.prime_three hA h3'
    hspan
  set ι := {D : Subgroup A // D.index = 3}
  have : Finite (Subgroup A) := inferInstance
  let := Fintype.ofFinite ι
  set C : ι → Submodule F U := fun D => Representation.invariants (αU.comp D.1.subtype)
  have hdim : finrank F U = ∑ D : ι, finrank F (C D) := by
    rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_directSum]
  set βU : U →ₗ[F] U := (β : V →ₗ[F] V).restrict hUβ
  set βU' : U →ₗ[F] U := (β.symm : V →ₗ[F] V).restrict hUβ'
  have hθD : ∀ D : ι, (D.1.map ((θ : A ≃* A) : A →* A)).index = 3 := fun D => by
    rw [Subgroup.index_map_equiv]
    exact D.2
  have hstep : ∀ D : ι, finrank F (C D) = finrank F (C ⟨_, hθD D⟩) := by
    intro D
    apply le_antisymm
    ·
      have hmap : ∀ u ∈ C D, βU u ∈ C ⟨_, hθD D⟩ := by
        intro u hu
        rw [Representation.mem_invariants] at hu ⊢
        rintro ⟨d', hd'⟩
        obtain ⟨d, hd, rfl⟩ := hd'
        have := hu ⟨d, hd⟩
        apply Subtype.ext
        change α (θ d) (β u) = β u
        rw [← hβ]
        exact congrArg (fun x : U => β (x : V)) this
      exact LinearMap.finrank_le_finrank_of_injective (f := βU.restrict hmap) (by
        intro x y hxy
        have h1 : (((βU.restrict hmap x : C ⟨_, hθD D⟩) : U) : V) =
            (((βU.restrict hmap y : C ⟨_, hθD D⟩) : U) : V) := by rw [hxy]
        exact Subtype.ext (Subtype.ext (β.injective h1)))
    · have hmap : ∀ u ∈ C ⟨_, hθD D⟩, βU' u ∈ C D := by
        intro u hu
        rw [Representation.mem_invariants] at hu ⊢
        rintro ⟨d, hd⟩
        have := hu ⟨θ d, d, hd, rfl⟩
        apply Subtype.ext
        change α d (β.symm u) = β.symm u
        apply β.injective
        rw [hβ, LinearEquiv.apply_symm_apply]
        exact congrArg (fun x : U => (x : V)) this
      exact LinearMap.finrank_le_finrank_of_injective (f := βU'.restrict hmap) (by
        intro x y hxy
        have h1 : (((βU'.restrict hmap x : C D) : U) : V) =
            (((βU'.restrict hmap y : C D) : U) : V) := by rw [hxy]
        exact Subtype.ext (Subtype.ext (β.symm.injective h1)))
  have hθi : ∀ (D : ι) (i : ℕ), (D.1.map ((θ ^ i : A ≃* A) : A →* A)).index = 3 := fun D i => by
    rw [Subgroup.index_map_equiv]
    exact D.2
  have hiter : ∀ (D : ι) (i : ℕ), finrank F (C ⟨_, hθi D i⟩) = finrank F (C D) := by
    intro D i
    induction i with
    | zero =>
      have e : (⟨_, hθi D 0⟩ : ι) = D := by
        apply Subtype.ext
        ext x
        simp
      rw [e]
    | succ i ih =>
      rw [← ih, hstep ⟨_, hθi D i⟩]
      have e : (⟨_, hθi D (i + 1)⟩ : ι) = ⟨_, hθD ⟨_, hθi D i⟩⟩ := by
        apply Subtype.ext
        change D.1.map ((θ ^ (i + 1) : A ≃* A) : A →* A) =
          (D.1.map ((θ ^ i : A ≃* A) : A →* A)).map ((θ : A ≃* A) : A →* A)
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [pow_succ']
      rw [e]
  have hU0 : 0 < finrank F U := by
    obtain ⟨a, v, hav⟩ := hα
    have hmem : α a v - v ∈ U := Submodule.subset_span ⟨a, v, rfl⟩
    have hne : (⟨α a v - v, hmem⟩ : U) ≠ 0 := fun h => hav (sub_eq_zero.mp
      (congrArg Subtype.val h))
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩
  obtain ⟨D₀, hD₀⟩ : ∃ D : ι, 0 < finrank F (C D) := by
    by_contra hall
    push Not at hall
    have : ∑ D : ι, finrank F (C D) = 0 := Finset.sum_eq_zero fun D _ => by
      have := hall D
      omega
    omega
  set g : ℕ → ι := fun i => ⟨_, hθi D₀ i⟩
  have hginj : Set.InjOn g (Finset.range 13 : Set ℕ) := by
    intro i hi j hj hij
    exact horb D₀.1 D₀.2 i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (congrArg Subtype.val hij)
  have h13 : 13 ≤ ∑ D ∈ (Finset.range 13).image g, finrank F (C D) := by
    rw [Finset.sum_image hginj]
    calc 13 = ∑ i ∈ Finset.range 13, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range 13, finrank F (C (g i)) :=
          Finset.sum_le_sum fun i _ => by
            change 1 ≤ finrank F (C ⟨_, hθi D₀ i⟩)
            rw [hiter D₀ i]
            exact hD₀
  calc 13 ≤ ∑ D ∈ (Finset.range 13).image g, finrank F (C D) := h13
    _ ≤ ∑ D : ι, finrank F (C D) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
    _ = finrank F U := hdim.symm
    _ ≤ finrank F V := Submodule.finrank_le U

end Hyperplanes

end

section

open Matrix CFSG.SectionRank.OddCover

section Orbit

variable {F : Type*} [Field F] [Finite F]

@[expose] def mulMapHom (c : F) : Multiplicative F →* Multiplicative F where
  toFun t := Multiplicative.ofAdd (c * Multiplicative.toAdd t)
  map_one' := by simp
  map_mul' s t := by simp [mul_add]

theorem not_mulStable_of_index_three (hF : Nat.card F = 27) {b : F} (hb1 : b ≠ 1)
    (hb13 : b ^ 13 = 1) {W : Subgroup (Multiplicative F)} (hW : W.index = 3)
    (hbW : ∀ w ∈ W, mulMapHom b w ∈ W) : False := by
  classical
  have := Fintype.ofFinite F
  let M : AddSubgroup F :=
    { carrier := {c | ∀ w ∈ W, mulMapHom c w ∈ W}
      zero_mem' := fun w _ => by
        change Multiplicative.ofAdd (0 * Multiplicative.toAdd w) ∈ W
        rw [zero_mul, ofAdd_zero]
        exact W.one_mem
      add_mem' := fun {c d} hc hd w hw => by
        change Multiplicative.ofAdd ((c + d) * Multiplicative.toAdd w) ∈ W
        rw [add_mul, ofAdd_add]
        exact W.mul_mem (hc w hw) (hd w hw)
      neg_mem' := fun {c} hc w hw => by
        change Multiplicative.ofAdd (-c * Multiplicative.toAdd w) ∈ W
        rw [neg_mul, ofAdd_neg]
        exact W.inv_mem (hc w hw) }
  have hpow : ∀ m : ℕ, b ^ m ∈ M := by
    intro m
    induction m with
    | zero =>
      intro w hw
      change Multiplicative.ofAdd (b ^ 0 * Multiplicative.toAdd w) ∈ W
      rw [pow_zero, one_mul, ofAdd_toAdd]
      exact hw
    | succ m ih =>
      intro w hw
      change Multiplicative.ofAdd (b ^ (m + 1) * Multiplicative.toAdd w) ∈ W
      rw [pow_succ', mul_assoc]
      have := hbW _ (ih w hw)
      exact this
  have hord : orderOf b = 13 := by
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb13
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact orderOf_eq_prime hb13 hb1
  have hcard : 14 ≤ Nat.card M := by
    have hinj : Set.InjOn (fun m : ℕ => b ^ m) (Finset.range 13 : Set ℕ) := by
      intro i hi j hj hij
      have := pow_injOn_Iio_orderOf (x := b) (by rw [hord]; exact Finset.mem_range.mp hi)
        (by rw [hord]; exact Finset.mem_range.mp hj) hij
      exact this
    have hsub : insert (0 : F) ((Finset.range 13).image fun m => b ^ m) ⊆
        (M : Set F).toFinset := by
      intro c hc
      rw [Set.mem_toFinset]
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact M.zero_mem
      · obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hc
        exact hpow m
    have h0 : (0 : F) ∉ (Finset.range 13).image fun m => b ^ m := by
      intro h
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp h
      exact (pow_ne_zero m (fun h0 => hb1 (by rw [h0] at hb13; simp at hb13))) hm
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn hinj, Finset.card_range] at this
    calc 14 ≤ (M : Set F).toFinset.card := this
      _ = Nat.card M := (Nat.card_eq_card_toFinset (M : Set F)).symm
  have hMtop : M = ⊤ := by
    have hdvd := AddSubgroup.card_addSubgroup_dvd_card M
    rw [hF] at hdvd
    have h27 : Nat.card M = 27 := by
      have : Nat.card M ∣ 3 ^ 3 := by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hdvd
      obtain ⟨k, hk, hkM⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
      interval_cases k <;> simp only [Nat.reducePow, pow_zero, pow_one] at hkM <;> omega
    exact AddSubgroup.eq_top_of_card_eq M (by rw [h27, hF])
  by_cases hW1 : ∃ w ∈ W, w ≠ 1
  · obtain ⟨w, hw, hw1⟩ := hW1
    have hw0 : Multiplicative.toAdd w ≠ 0 := fun h => hw1 (by rw [← ofAdd_toAdd w, h, ofAdd_zero])
    have htop : W = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hc : (Multiplicative.toAdd x / Multiplicative.toAdd w) ∈ M :=
        hMtop ▸ AddSubgroup.mem_top _
      have := hc w hw
      change Multiplicative.ofAdd (Multiplicative.toAdd x / Multiplicative.toAdd w *
        Multiplicative.toAdd w) ∈ W at this
      rwa [div_mul_cancel₀ _ hw0, ofAdd_toAdd] at this
    rw [htop, Subgroup.index_top] at hW
    omega
  · push Not at hW1
    have hbot : W = ⊥ := (Subgroup.eq_bot_iff_forall W).mpr hW1
    rw [hbot, Subgroup.index_bot] at hW
    have : Nat.card (Multiplicative F) = 27 := hF
    omega

theorem map_mulMapHom_injOn (hF : Nat.card F = 27) {a : Fˣ} (ha : orderOf a = 26)
    {W : Subgroup (Multiplicative F)} (hW : W.index = 3) {i j : ℕ} (hi : i < 13) (hj : j < 13)
    (hij : W.map (mulMapHom ((a : F) ^ (2 * i))) = W.map (mulMapHom ((a : F) ^ (2 * j)))) :
    i = j := by
  wlog hle : i ≤ j generalizing i j
  · exact (this hj hi hij.symm (by omega)).symm
  by_contra hne
  have hlt : i < j := lt_of_le_of_ne hle hne
  set k := j - i with hk
  set b : F := (a : F) ^ (2 * k)
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have hb1 : b ≠ 1 := by
    intro h
    have h' : a ^ (2 * k) = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
    have := orderOf_dvd_of_pow_eq_one h'
    rw [ha] at this
    omega
  have hb13 : b ^ 13 = 1 := by
    have h26 : (a : F) ^ 26 = 1 := by
      have := pow_orderOf_eq_one a
      rw [ha] at this
      have := congrArg Units.val this
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    calc b ^ 13 = ((a : F) ^ 26) ^ k := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ = 1 := by rw [h26, one_pow]
  apply not_mulStable_of_index_three hF hb1 hb13 hW
  intro w hw
  have hmem : mulMapHom ((a : F) ^ (2 * j)) w ∈ W.map (mulMapHom ((a : F) ^ (2 * i))) := by
    rw [hij]
    exact ⟨w, hw, rfl⟩
  obtain ⟨w', hw', hww'⟩ := hmem
  have : mulMapHom b w = w' := by
    apply Multiplicative.toAdd.injective
    have h1 := congrArg Multiplicative.toAdd hww'
    change (a : F) ^ (2 * i) * Multiplicative.toAdd w' =
      (a : F) ^ (2 * j) * Multiplicative.toAdd w at h1
    change b * Multiplicative.toAdd w = Multiplicative.toAdd w'
    have hj' : 2 * j = 2 * i + 2 * k := by omega
    rw [hj', pow_add, mul_assoc] at h1
    exact (mul_left_cancel₀ (pow_ne_zero _ ha0) h1).symm
  rw [this]
  exact hw'

end Orbit

end

section

open Matrix CFSG.SectionRank.OddCover
open scoped Pointwise commutatorElement IsMulCommutative

section Lifting

variable {G S : Type*} [Group G] [Finite G] [Group S]

theorem exists_mem_normalizer_map_eq {p : ℕ} [Fact p.Prime] (π : G →* S) (P : Sylow p G) {m : G}
    (hm : π m ∈ Subgroup.normalizer (((P : Subgroup G).map π : Subgroup S) : Set S)) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), π n = π m := by
  set L := (P : Subgroup G) ⊔ π.ker with hL
  have hPL : (P : Subgroup G) ≤ L := le_sup_left
  have hconj : ∀ x ∈ (P : Subgroup G), m * x * m⁻¹ ∈ L := by
    intro x hx
    have h := (Subgroup.mem_normalizer_iff.mp hm _).mp (Subgroup.mem_map_of_mem π hx)
    rw [← map_inv, ← map_mul, ← map_mul] at h
    have h2 : m * x * m⁻¹ ∈ ((P : Subgroup G).map π).comap π := h
    rwa [Subgroup.comap_map_eq] at h2
  have hmPL : ((m • P : Sylow p G) : Subgroup G) ≤ L := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hx' : m⁻¹ * x * m ∈ (P : Subgroup G) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hx
    have h := hconj _ hx'
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L ((m • P).subtype hmPL) (P.subtype hPL)
  have hmem : ∀ x ∈ (P : Subgroup G), (l : G) * m * x * ((l : G) * m)⁻¹ ∈ (P : Subgroup G) := by
    intro x hx
    have h1 : m * x * m⁻¹ ∈ ((m • P : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj m) _ hx
    have h2 : (⟨m * x * m⁻¹, hmPL h1⟩ : L) ∈
        (((m • P).subtype hmPL : Sylow p L) : Subgroup L) := by
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      exact h1
    have h3 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj l) _ h2
    rw [← Sylow.coe_subgroup_smul, hl, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h3
    convert h3 using 1
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hlm : (l : G) * m ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype hmem
  obtain ⟨q, hq, o, ho, hqo⟩ := Subgroup.mem_sup_of_normal_right.mp l.2
  refine ⟨o * m, ?_, ?_⟩
  · have h : o * m = q⁻¹ * ((l : G) * m) := by rw [← hqo]; group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ((P : Subgroup G).inv_mem hq)) hlm
  · rw [map_mul, MonoidHom.mem_ker.mp ho, one_mul]

theorem exists_lift_pGroup {p : ℕ} [hp : Fact p.Prime] (π : G →* S) (hπ : Function.Surjective π)
    (hker : p.Coprime (Nat.card π.ker)) (Q : Subgroup S) (hQ : IsPGroup p Q) :
    ∃ R : Subgroup G, R.map π = Q ∧ Function.Injective (π.comp R.subtype) := by
  set P := Q.comap π
  let πP : P →* Q := (π.comp P.subtype).codRestrict Q (fun x => x.2)
  have hπP : Function.Surjective πP := by
    intro y
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨⟨x, by change π x ∈ Q; rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  obtain ⟨T, hT⟩ := CFSG.SignalizerFunctor.Helpers.surjective_pgroup_sylow_lift p hp.out πP hπP hQ
  set R := (T : Subgroup P).map P.subtype
  have hRp : IsPGroup p R := T.isPGroup'.map P.subtype
  refine ⟨R, ?_, CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup p hp.out
    π hker R hRp⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact x.2
  · intro y hy
    have : (⟨y, hy⟩ : Q) ∈ (T : Subgroup P).map πP := by rw [hT]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩

theorem exists_klein_lift (π : G →* S) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) {x y : S} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) :
    ∃ a b : G, π a = x ∧ π b = y ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx' : ∀ z, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
  have hy' : ∀ z, y * (y * z) = z := fun z => by rw [← mul_assoc, hy, one_mul]
  have hyx : ∀ z, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, ← hxy, mul_assoc]
  let T : Subgroup S :=
    { carrier := {1, x, y, x * y}
      one_mem' := by simp
      mul_mem' := by
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp [mul_assoc, hx, hy, hx', hyx, ← hxy]
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl)
        · simp
        · rw [inv_eq_of_mul_eq_one_right hx]
          simp
        · rw [inv_eq_of_mul_eq_one_right hy]
          simp
        · rw [inv_eq_of_mul_eq_one_right (show x * y * (x * y) = 1 by
            rw [mul_assoc, ← mul_assoc y, ← hxy, mul_assoc, hy, mul_one, hx])]
          simp }
  have hT2 : IsPGroup 2 T := by
    rintro ⟨z, hz⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, sq]
    rcases hz with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact hx
    · exact hy
    · rw [mul_assoc, ← mul_assoc y, ← hxy, mul_assoc, hy, mul_one, hx]
  have hcop : Nat.Coprime 2 (Nat.card π.ker) := Nat.coprime_two_left.mpr hker
  obtain ⟨R, hRT, hRinj⟩ := exists_lift_pGroup π hπ hcop T hT2
  have hxT : x ∈ R.map π := by rw [hRT]; exact Or.inr (Or.inl rfl)
  have hyT : y ∈ R.map π := by rw [hRT]; exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨a, ha, rfl⟩ := hxT
  obtain ⟨b, hb, rfl⟩ := hyT
  have key : ∀ (u v : G) (hu : u ∈ R) (hv : v ∈ R), π u = π v → u = v := fun u v hu hv h =>
    congrArg Subtype.val (hRinj (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) h)
  refine ⟨a, b, rfl, rfl, ?_, ?_, ?_⟩
  · exact key _ _ (R.mul_mem ha ha) R.one_mem (by rw [map_mul, hx, map_one])
  · exact key _ _ (R.mul_mem hb hb) R.one_mem (by rw [map_mul, hy, map_one])
  · exact key _ _ (R.mul_mem ha hb) (R.mul_mem hb ha) (by rw [map_mul, map_mul, hxy])

end Lifting

section Critical

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normal_map_subtype_of_characteristic (N : Subgroup G) [N.Normal] (H : Subgroup N)
    [hH : H.Characteristic] : (H.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hx
  have hmap := Subgroup.characteristic_iff_map_eq.mp hH (MulAut.conjNormal g)
  have hk' : MulAut.conjNormal g k ∈ H := by
    rw [← hmap]
    exact ⟨k, hk, rfl⟩
  exact ⟨_, hk', MulAut.conjNormal_apply g k⟩

theorem exists_noncentral_normal_pSubgroup (K : Subgroup G) [K.Normal]
    (hsolv : Group.IsSolvable K) (hK : ¬ K ≤ Subgroup.center G) :
    ∃ p : ℕ, p.Prime ∧ ∃ P : Subgroup G, P.Normal ∧ P ≤ K ∧ IsPGroup p P ∧
      ¬ P ≤ Subgroup.center G := by
  by_contra hcon
  push Not at hcon
  have hcore : ∀ q ∈ (Nat.card K).primeFactors,
      (CFSG.pCore q K).map K.subtype ≤ Subgroup.center G := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqp⟩
    exact hcon q hqp _ (normal_map_subtype_of_characteristic K _)
      (Subgroup.map_subtype_le _) (CFSG.pCore_isPGroup.map K.subtype)
  have hF : (CFSG.fittingSubgroup K).map K.subtype ≤ Subgroup.center G := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    exact iSup_le fun q => hcore q.1.1 q.1.2
  have hC : Subgroup.centralizer (CFSG.fittingSubgroup K : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro k _
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have := hF ⟨f, hf, rfl⟩
    rw [Subgroup.mem_center_iff] at this
    exact Subtype.ext (this k).symm
  have htop := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  rw [hC] at htop
  apply hK
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ CFSG.fittingSubgroup K := htop (Subgroup.mem_top _)
  exact hF ⟨⟨k, hk⟩, this, rfl⟩

omit [Finite G] in
theorem eq_top_of_isPerfect_of_isSolvable_quotient [Group.IsPerfect G] (N : Subgroup G)
    [N.Normal] (hsol : Group.IsSolvable (G ⧸ N)) : N = ⊤ := by
  have hperf : Group.IsPerfect (G ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  by_contra hne
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isSolvable (G ⧸ N) hsol

theorem exists_critical_subgroup [Group.IsPerfect G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} [hPn : P.Normal] (hP : IsPGroup p P) (hPZ : ¬ P ≤ Subgroup.center G) :
    ∃ D : Subgroup G, D.Normal ∧ D ≤ P ∧ (∀ x ∈ D, x ^ p = 1) ∧
      (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧ ¬ D ≤ Subgroup.center G := by
  have hPne : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hPZ
    intro x hx
    have : (⟨x, hx⟩ : P) = 1 := Subsingleton.elim _ _
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1]
    exact Subgroup.one_mem _
  obtain ⟨D₀, hD₀c, -, hD₀comm, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  refine ⟨D₀.map P.subtype, normal_map_subtype_of_characteristic P D₀, Subgroup.map_subtype_le _,
    ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hD₀exp x hx
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, this, Subgroup.coe_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    have h1 : ⁅a, b⁆ ∈ ⁅D₀, (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b)
    have h2 : ⁅a, b⁆ ∈ Subgroup.centralizer (D₀ : Set P) := (hD₀comm h1).2
    rw [Subgroup.mem_centralizer_iff] at h2
    have h3 := h2 c hc
    have := congrArg Subtype.val h3
    simpa [commutatorElement_def] using this.symm
  · intro hDZ
    set χ : G →* MulAut P := MulAut.conjNormal
    have hfix : χ.range ≤ fixingSubgroup (MulAut P) (D₀ : Set P) := by
      rintro _ ⟨g, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      change g * (d : G) * g⁻¹ = d
      have := hDZ ⟨d, hd, rfl⟩
      rw [Subgroup.mem_center_iff] at this
      have h2 : g * (d : G) = (d : G) * g := this g
      rw [h2, mul_inv_cancel_right]
    have hpg : IsPGroup p χ.range := hD₀fix.to_le hfix
    have hsol : Group.IsSolvable (G ⧸ χ.ker) := by
      have : Group.IsSolvable χ.range := by
        have := hpg.isNilpotent
        infer_instance
      exact Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientKerEquivRange χ).symm.toMonoidHom)
        (QuotientGroup.quotientKerEquivRange χ).symm.surjective
    have hker := eq_top_of_isPerfect_of_isSolvable_quotient χ.ker hsol
    apply hPZ
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : χ g = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top g)
    have := congrArg (fun σ : MulAut P => ((σ ⟨x, hx⟩ : P) : G)) hg
    change g * x * g⁻¹ = x at this
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [this]

end Critical

section FrattiniAction

open CFSG.RankThree.PartOne.FixedRank36

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P] {L : Type*} [Group L]

theorem frattiniRep_eq_one_of_coprime [IsElementaryAbelian q (P ⧸ frattini P)]
    (hP : IsPGroup q P) (ρ : L →* MulAut P) (l : L) {r : ℕ} (hr : r.Prime) (hrq : r ≠ q)
    (hl : IsPGroup r (Subgroup.zpowers (ρ l))) (h : frattiniRep q ρ l = 1) : ρ l = 1 := by
  have hker : ρ l ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini P)).ker := by
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h1 := congrArg (fun f : Module.End (ZMod q) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) h
    simp only [frattiniRep_apply, Module.End.one_apply] at h1
    exact congrArg Additive.toMul h1
  have hqker := CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup
    q hP
  obtain ⟨k, hk⟩ := hqker ⟨ρ l, hker⟩
  obtain ⟨m, hm⟩ := hl ⟨ρ l, Subgroup.mem_zpowers _⟩
  have hk' : (ρ l) ^ q ^ k = 1 := congrArg Subtype.val hk
  have hm' : (ρ l) ^ r ^ m = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (q ^ k) (r ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq.out hr).2 (Ne.symm hrq))
  have := pow_gcd_eq_one.2 ⟨hk', hm'⟩
  rwa [hcop, pow_one] at this

end FrattiniAction

section Model

open CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

@[expose] def kleinI : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem det_kleinJ (h3 : (3 : F) = 0) : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [det_fin_two_of]
  linear_combination -h3

@[expose] def kleinJ (h3 : (3 : F) = 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 1, -1], det_kleinJ h3⟩

theorem pslMk_eq_one_iff (A : SpecialLinearGroup (Fin 2) F) :
    pslMk A = 1 ↔
      ∃ r : F, r ^ 2 = 1 ∧ Matrix.scalar (Fin 2) r = (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [pslMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]

theorem pslMk_ne_one_of_entry {A : SpecialLinearGroup (Fin 2) F}
    (h : (A : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0) : pslMk A ≠ 1 := by
  rw [Ne, pslMk_eq_one_iff]
  rintro ⟨r, -, hr⟩
  apply h
  rw [← hr]
  simp

@[expose] def negOneSL : SpecialLinearGroup (Fin 2) F :=
  ⟨-1, by rw [Matrix.det_neg, Fintype.card_fin, det_one]; ring⟩

theorem pslMk_negOneSL : pslMk (negOneSL (F := F)) = 1 := by
  rw [pslMk_eq_one_iff]
  refine ⟨-1, by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negOneSL]

theorem pslMk_eq_of_eq_neg {A B : SpecialLinearGroup (Fin 2) F}
    (hB : (B : Matrix (Fin 2) (Fin 2) F) = -(A : Matrix (Fin 2) (Fin 2) F)) :
    pslMk B = pslMk A := by
  have : B = A * negOneSL := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, hB]
    simp [negOneSL])
  rw [this, map_mul, pslMk_negOneSL, mul_one]

theorem coe_kleinI : ((kleinI : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, 1; -1, 0] :=
  rfl

theorem coe_kleinJ (h3 : (3 : F) = 0) :
    ((kleinJ h3 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, -1] :=
  rfl

theorem psl_klein (h3 : (3 : F) = 0) :
    ∃ x y : ProjectiveSpecialLinearGroup (Fin 2) F, x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧
      x ≠ 1 ∧ y ≠ 1 ∧ x * y ≠ 1 := by
  have hII : ((kleinI * kleinI : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![-1, 0; 0, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_kleinI]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hJJ : ((kleinJ h3 * kleinJ h3 : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![-1, 0; 0, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_kleinJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h3
  have hIJ : ((kleinI * kleinJ h3 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, -1; -1, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_kleinI, coe_kleinJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hJI : ((kleinJ h3 * kleinI : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![-1, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_kleinI, coe_kleinJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hscal : Matrix.scalar (Fin 2) (-1 : F) = !![-1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨pslMk kleinI, pslMk (kleinJ h3), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, pslMk_eq_one_iff]
    exact ⟨-1, by ring, by rw [hII, hscal]⟩
  · rw [← map_mul, pslMk_eq_one_iff]
    exact ⟨-1, by ring, by rw [hJJ, hscal]⟩
  · rw [← map_mul, ← map_mul]
    apply pslMk_eq_of_eq_neg
    rw [hIJ, hJI]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · exact pslMk_ne_one_of_entry (by rw [coe_kleinI]; simp)
  · exact pslMk_ne_one_of_entry (by rw [coe_kleinJ]; simp)
  · rw [← map_mul]
    exact pslMk_ne_one_of_entry (by rw [hIJ]; simp)

end Model

section Unipotent

variable {G : Type*} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem exists_unipotent_lift (hF : Nat.card F = 3 ^ 3)
    (π : G →* ProjectiveSpecialLinearGroup (Fin 2) F) (hπ : Function.Surjective π)
    (hker : Nat.Coprime 3 (Nat.card π.ker)) (a : Fˣ) :
    ∃ φ : Multiplicative F →* G, Function.Injective φ ∧
      ∃ n : G, ∀ t : F, n * φ (Multiplicative.ofAdd t) * n⁻¹ =
        φ (Multiplicative.ofAdd ((a : F) ^ 2 * t)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := Sylow.mapSurjective_surjective hπ 3
    (pslUSylow (K := F) (p := 3) (f := 3) (by norm_num) hF)
  have hRmap : (R : Subgroup G).map π = (pslU (K := F)).range := by
    rw [← coe_pslUSylow (by norm_num : (3 : ℕ) ≠ 2) hF, ← hR, Sylow.coe_mapSurjective]
  have hinj := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup 3
    Nat.prime_three π hker R R.isPGroup'
  let ψ0 : (R : Subgroup G) →* (pslU (K := F)).range :=
    (π.comp (R : Subgroup G).subtype).codRestrict _ (fun r => by
      rw [← hRmap]
      exact ⟨r, r.2, rfl⟩)
  have hψ0 : Function.Bijective ψ0 := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => ?_⟩
    have hy : (y : ProjectiveSpecialLinearGroup (Fin 2) F) ∈ (R : Subgroup G).map π := by
      rw [hRmap]
      exact y.2
    obtain ⟨r, hr, hry⟩ := hy
    exact ⟨⟨r, hr⟩, Subtype.ext hry⟩
  let ψ := MulEquiv.ofBijective ψ0 hψ0
  let eU := MonoidHom.ofInjective (pslU_injective (K := F))
  let φ : Multiplicative F →* G := (R : Subgroup G).subtype.comp (eU.trans ψ.symm).toMonoidHom
  have hφR : ∀ t, φ t ∈ (R : Subgroup G) := fun t => ((eU.trans ψ.symm) t).2
  have hφπ : ∀ t, π (φ t) = pslU t := fun t => by
    have h1 : ψ0 ((eU.trans ψ.symm) t) = eU t := ψ.apply_symm_apply (eU t)
    exact congrArg Subtype.val h1
  refine ⟨φ, fun s t hst => (eU.trans ψ.symm).injective (Subtype.ext hst), ?_⟩
  obtain ⟨m, hm⟩ := hπ (pslMk (slD a))
  have hmN : π m ∈ Subgroup.normalizer (((R : Subgroup G).map π : Subgroup _) : Set _) := by
    rw [hRmap, hm]
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨t, rfl⟩
    refine ⟨Multiplicative.ofAdd ((a : F) ^ 2 * Multiplicative.toAdd t), ?_⟩
    change pslU (Multiplicative.ofAdd ((a : F) ^ 2 * Multiplicative.toAdd t)) = _
    rw [← pslD_conj_pslU, ofAdd_toAdd]
  obtain ⟨n, hn, hnm⟩ := exists_mem_normalizer_map_eq π R hmN
  refine ⟨n, fun t => ?_⟩
  have h1 : n * φ (Multiplicative.ofAdd t) * n⁻¹ ∈ (R : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (hφR _)
  have h2 := hinj (a₁ := ⟨_, h1⟩) (a₂ := ⟨_, hφR (Multiplicative.ofAdd ((a : F) ^ 2 * t))⟩) (by
    change π (n * φ (Multiplicative.ofAdd t) * n⁻¹) =
      π (φ (Multiplicative.ofAdd ((a : F) ^ 2 * t)))
    rw [map_mul, map_mul, map_inv, hnm, hm, hφπ, hφπ, pslD_conj_pslU])
  exact congrArg Subtype.val h2

@[expose] def mulMapEquiv (b : Fˣ) : Multiplicative F ≃* Multiplicative F :=
  { mulMapHom (b : F) with
    invFun := mulMapHom ((b⁻¹ : Fˣ) : F)
    left_inv := fun t => by
      change Multiplicative.ofAdd (((b⁻¹ : Fˣ) : F) * ((b : F) * Multiplicative.toAdd t)) = t
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, ofAdd_toAdd]
    right_inv := fun t => by
      change Multiplicative.ofAdd ((b : F) * (((b⁻¹ : Fˣ) : F) * Multiplicative.toAdd t)) = t
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, ofAdd_toAdd] }

omit [Finite F] in
theorem mulMapEquiv_pow_apply (b : Fˣ) (i : ℕ) (t : Multiplicative F) :
    (mulMapEquiv b ^ i) t = mulMapHom ((b : F) ^ i) t := by
  induction i generalizing t with
  | zero =>
    rw [pow_zero, MulAut.one_apply]
    change t = Multiplicative.ofAdd ((b : F) ^ 0 * Multiplicative.toAdd t)
    rw [pow_zero, one_mul, ofAdd_toAdd]
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    change Multiplicative.ofAdd ((b : F) * Multiplicative.toAdd (Multiplicative.ofAdd
      ((b : F) ^ i * Multiplicative.toAdd t))) =
        Multiplicative.ofAdd ((b : F) ^ (i + 1) * Multiplicative.toAdd t)
    rw [toAdd_ofAdd, ← mul_assoc, ← pow_succ']

omit [Finite F] in
theorem mulMapEquiv_pow (b : Fˣ) (i : ℕ) :
    ((mulMapEquiv b ^ i : Multiplicative F ≃* Multiplicative F) :
      Multiplicative F →* Multiplicative F) = mulMapHom ((b : F) ^ i) :=
  MonoidHom.ext (mulMapEquiv_pow_apply b i)

end Unipotent

section Rank

open CFSG.RankThree.PartOne.FixedRank36

variable {G : Type*} [Group G] [Finite G]

theorem pRank_fixedSub_le_localRank {p : ℕ} (hp : p.Prime) (D : Subgroup G) [D.Normal] {t : G}
    (ht : t ≠ 1) (ht2 : t * t = 1) :
    CFSG.pRank p ↥(fixedSub (MulAut.conjNormal (H := D) t)) ≤
      CFSG.Assembly.RankThreeEven.localRank p G := by
  set C := fixedSub (MulAut.conjNormal (H := D) t)
  set X := Subgroup.normalizer (Subgroup.zpowers t : Set G)
  have hX : CFSG.Assembly.IsTwoLocal X := by
    refine ⟨Subgroup.zpowers t, fun h => ht ?_, ?_, rfl⟩
    · have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      rwa [h, Subgroup.mem_bot] at this
    · rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← _root_.zpow_mul,
        mul_comm, _root_.zpow_mul, zpow_natCast, sq, ht2, _root_.one_zpow]
  have hmem : ∀ c : C, ((c : D) : G) ∈ X := by
    intro c
    have hc : t * ((c : D) : G) * t⁻¹ = ((c : D) : G) := congrArg Subtype.val c.2
    have hcomm : ((c : D) : G) * t * ((c : D) : G)⁻¹ = t := by
      calc ((c : D) : G) * t * ((c : D) : G)⁻¹ =
          (t * ((c : D) : G) * t⁻¹) * t * ((c : D) : G)⁻¹ := by rw [hc]
        _ = t := by group
    apply Subgroup.mem_normalizer_fintype
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := map_zpow (MulAut.conj ((c : D) : G)) t k
    simp only [MulAut.conj_apply] at this
    rw [this, hcomm]
  let f : C →* X :=
    { toFun := fun c => ⟨((c : D) : G), hmem c⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y hxy => by
    have := congrArg (fun z : X => (z : G)) hxy
    exact Subtype.ext (Subtype.ext this)
  calc CFSG.pRank p ↥C ≤ CFSG.pRank p ↥X :=
        CFSG.RankThree.OddKernel.pRank_le_of_injective hp.one_lt f hf
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥X) := CFSG.SectionRank.pRank_eq_open_pRank_top p _
    _ = CFSG.Open.pRank p X :=
        (CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top p hp.one_lt X).symm
    _ ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
        CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt hX

end Rank

open CFSG.RankThree.PartOne.FixedRank36 in
theorem rank3II_4_20 : Item4_20 := by
  intro G _ _ hG hperf hcore ⟨e⟩
  have := hperf
  set F := GaloisField 3 3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card F = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  have h3F : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  set K := CFSG.pPrimeCore 3 G with hKdef
  set e' : G ⧸ K ≃* ProjectiveSpecialLinearGroup (Fin 2) F := e.trans (projSLEquivPSL F)
  set π : G →* ProjectiveSpecialLinearGroup (Fin 2) F :=
    e'.toMonoidHom.comp (QuotientGroup.mk' K) with hπdef
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : π.ker = K := by
    ext g
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e'.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hKodd : Odd (Nat.card K) := by
    rw [hcore]
    exact CFSG.ABGDGroups.odd_card_oddCore G
  have hK3 : Nat.Coprime 3 (Nat.card K) := CFSG.pPrimeCore_coprime_card
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; norm_num)
  suffices hK1 : K = ⊥ by
    have hinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, hker, hK1]
    exact (MulEquiv.ofBijective π ⟨hinj, hπ⟩).isSimpleGroup
  by_contra hK1
  have hKsolv : Group.IsSolvable K := CFSG.Milestones.odd_order_solvable hKodd
  by_cases hKZ : K ≤ Subgroup.center G
  ·
    have := (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel (p := 3) (f := 3)
      (by norm_num) hF π hπ (hker ▸ hKZ) (hker ▸ hKodd)).1 (by norm_num)
    exact hK1 (hker ▸ this)
  obtain ⟨p, hp, P, hPn, hPK, hPp, hPZ⟩ := exists_noncentral_normal_pSubgroup K hKsolv hKZ
  have : Fact p.Prime := ⟨hp⟩
  have hPne : P ≠ ⊥ := fun h => hPZ (by rw [h]; exact bot_le)
  have hpK : p ∣ Nat.card K := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hPne (Subgroup.eq_bot_of_card_eq P hk)
    have : p ∣ Nat.card P := by rw [hk]; exact dvd_pow_self p hk0
    exact this.trans (Subgroup.card_dvd_of_le hPK)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr hpK)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hK3 hpK
  have hp5 : 3 < p := by
    have := hp.two_le
    omega
  obtain ⟨D, hDn, hDP, hDexp, hDclass, hDZ⟩ := exists_critical_subgroup hp2 hPp hPZ
  have := hDn
  have hCK : Subgroup.centralizer (D : Set G) ≤ K := by
    have hCn : (Subgroup.centralizer (D : Set G)).Normal := Subgroup.normal_centralizer
    have hmapn := hCn.map π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.centralizer (D : Set G)).map π) with h | h
    · rw [← hker]
      exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (Subgroup.centralizer (D : Set G))).comp K.subtype) := by
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
        have hg : π g ∈ (Subgroup.centralizer (D : Set G)).map π := by
          rw [h]
          exact Subgroup.mem_top _
        obtain ⟨c, hc, hcg⟩ := hg
        have hk : c⁻¹ * g ∈ K := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
        refine ⟨⟨c⁻¹ * g, hk⟩, ?_⟩
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
          QuotientGroup.mk'_apply, QuotientGroup.eq]
        have : (c⁻¹ * g)⁻¹ * g = g⁻¹ * c * g⁻¹⁻¹ := by group
        rw [this]
        exact hCn.conj_mem c hc g⁻¹
      have hsol : Group.IsSolvable (G ⧸ Subgroup.centralizer (D : Set G)) :=
        Group.isSolvable_of_surjective hsurj
      have htop := eq_top_of_isPerfect_of_isSolvable_quotient _ hsol
      apply hDZ
      intro d hd
      rw [Subgroup.mem_center_iff]
      intro g
      have hgC : g ∈ Subgroup.centralizer (D : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hgC d hd).symm
  have hDp : IsPGroup p D := hPp.to_le hDP
  have hfr := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have : IsElementaryAbelian p (↥D ⧸ frattini ↥D) := hfr.2.2.2.1
  set ρ : G →* MulAut D := MulAut.conjNormal with hρ
  set ρV := frattiniRep p ρ with hρV
  have : FiniteDimensional (ZMod p) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hclass : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hcoe : ((⁅x, y⁆ : D) : G) = ⁅(x : G), (y : G)⁆ := by simp [commutatorElement_def]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
    exact (hDclass x x.2 y y.2 z z.2).symm
  have hpZ : ∀ m : ℕ, m.Prime → m ≠ p → ((m : ℕ) : ZMod p) ≠ 0 := by
    intro m hm hmp h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hmp ((Nat.prime_dvd_prime_iff_eq hp hm).mp h).symm
  obtain ⟨a₀, ha₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have ha₀ord : orderOf a₀ = 26 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha₀, Nat.card_units, hF]
    norm_num
  obtain ⟨φ, hφinj, n, hn⟩ := exists_unipotent_lift hF π hπ (hker ▸ hK3) a₀
  set θ := mulMapEquiv (F := F) (a₀ ^ 2) with hθ
  have hθapply : ∀ t : Multiplicative F,
      θ t = Multiplicative.ofAdd ((a₀ : F) ^ 2 * Multiplicative.toAdd t) := fun t => by
    change Multiplicative.ofAdd (((a₀ ^ 2 : Fˣ) : F) * Multiplicative.toAdd t) = _
    rw [Units.val_pow_eq_pow_val]
  have hnφ : ∀ t : Multiplicative F, n * φ t = φ (θ t) * n := by
    intro t
    have := hn (Multiplicative.toAdd t)
    rw [ofAdd_toAdd] at this
    rw [hθapply, ← this]
    group
  set β : Additive (↥D ⧸ frattini ↥D) ≃ₗ[ZMod p] Additive (↥D ⧸ frattini ↥D) :=
    LinearEquiv.ofLinearMap (ρV n) (ρV n⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl) with hβdef
  have h3p : (3 : ZMod p) ≠ 0 := by exact_mod_cast hpZ 3 Nat.prime_three (Ne.symm hp3)
  have h2p : (2 : ZMod p) ≠ 0 := by exact_mod_cast hpZ 2 Nat.prime_two (Ne.symm hp2)
  have hA3 : ∀ t : Multiplicative F, t ^ 3 = 1 := by
    intro t
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, Nat.cast_ofNat, h3F, zero_mul]
  have hα : ∃ (t : Multiplicative F) (v : Additive (↥D ⧸ frattini ↥D)),
      (ρV.comp φ) t v ≠ v := by
    by_contra hall
    push Not at hall
    have h1 : ∀ t : Multiplicative F, φ t = 1 := by
      intro t
      have hρV1 : ρV (φ t) = 1 := LinearMap.ext fun v => hall t v
      have hl : IsPGroup 3 (Subgroup.zpowers (ρ (φ t))) := by
        rintro ⟨g, hg⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        refine ⟨1, Subtype.ext ?_⟩
        rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← _root_.zpow_mul,
          mul_comm, _root_.zpow_mul, zpow_natCast, ← map_pow, ← map_pow, hA3, map_one, map_one,
          _root_.one_zpow]
      have hρ1 := frattiniRep_eq_one_of_coprime hDp ρ (φ t) Nat.prime_three (Ne.symm hp3) hl hρV1
      have hC : φ t ∈ Subgroup.centralizer (D : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        have := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : G)) hρ1
        change φ t * d * (φ t)⁻¹ = d at this
        calc d * φ t = φ t * d * (φ t)⁻¹ * φ t := by rw [this]
          _ = φ t * d := by group
      have hord3 : orderOf (φ t) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hA3, map_one])
      have hordK : orderOf (φ t) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K (hCK hC)
      have hgcd := Nat.dvd_gcd hord3 hordK
      rw [Nat.Coprime.gcd_eq_one hK3, Nat.dvd_one, orderOf_eq_one_iff] at hgcd
      exact hgcd
    have h10 : Multiplicative.ofAdd (1 : F) ≠ 1 := fun h => by
      have h' := congrArg (Multiplicative.toAdd (α := F)) h
      rw [toAdd_ofAdd, toAdd_one] at h'
      exact one_ne_zero h'
    exact h10 (hφinj (by rw [h1, map_one]))
  have hβ : ∀ (t : Multiplicative F) (v : Additive (↥D ⧸ frattini ↥D)),
      β ((ρV.comp φ) t v) = (ρV.comp φ) (θ t) (β v) := by
    intro t v
    change ρV n (ρV (φ t) v) = ρV (φ (θ t)) (ρV n v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hnφ]
  have horb : ∀ W : Subgroup (Multiplicative F), W.index = 3 → ∀ i j : ℕ, i < 13 → j < 13 →
      W.map ((θ ^ i : Multiplicative F ≃* Multiplicative F) :
          Multiplicative F →* Multiplicative F) =
        W.map ((θ ^ j : Multiplicative F ≃* Multiplicative F) :
          Multiplicative F →* Multiplicative F) → i = j := by
    intro W hW i j hi hj hij
    rw [hθ, mulMapEquiv_pow, mulMapEquiv_pow, Units.val_pow_eq_pow_val, ← pow_mul,
      ← pow_mul] at hij
    exact map_mulMapHom_injOn (by rw [hF]; norm_num) ha₀ord hW hi hj hij
  have h13 := thirteen_le_finrank h3p hA3 (ρV.comp φ) hα θ β hβ horb
  obtain ⟨x, y, hx, hy, hxy, hx1, hy1, hxy1⟩ := psl_klein h3F
  obtain ⟨a, b, hax, hby, ha2, hb2, hab⟩ := exists_klein_lift π hπ (hker ▸ hKodd) hx hy hxy
  have ha1 : a ≠ 1 := fun h => hx1 (by rw [← hax, h, map_one])
  have hb1 : b ≠ 1 := fun h => hy1 (by rw [← hby, h, map_one])
  have hab1 : a * b ≠ 1 := fun h => hxy1 (by rw [← hax, ← hby, ← map_mul, h, map_one])
  have hab2 : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hsum := finrank_le_sum_fixed h2p (ρV a) (ρV b) (by rw [← map_mul, ha2, map_one])
    (by rw [← map_mul, hb2, map_one]) (by rw [← map_mul, ← map_mul, hab])
  have hfix : ∀ t : G, t ≠ 1 → t * t = 1 →
      Module.finrank (ZMod p) (LinearMap.ker (ρV t - 1)) ≤ 2 := by
    intro t ht ht2
    have hl : IsPGroup 2 (Subgroup.zpowers (ρ t)) := by
      rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← _root_.zpow_mul,
        mul_comm, _root_.zpow_mul, zpow_natCast, sq, ← map_mul, ht2, map_one, _root_.one_zpow]
    have hrank : CFSG.pRank p ↥(fixedSub (ρ t)) ≤ 2 := by
      have h1 : CFSG.pRank p ↥(fixedSub (ρ t)) ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
        pRank_fixedSub_le_localRank hp D ht ht2
      have h2 := hG.localRank_lt p hp hp5
      omega
    have := finrank_fixed_le hDp hp2 hexp hclass ρ t hl hrank
    rwa [Module.End.eigenspace_def, one_smul] at this
  have e1 := hfix a ha1 ha2
  have e2 := hfix b hb1 hb2
  have e3 := hfix (a * b) hab1 hab2
  rw [map_mul] at e3
  omega

end

end CFSG.RankThree.PartTwo.Sec4
