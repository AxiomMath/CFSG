module

public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoThree
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear

public section

open Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCSpComm CFSG.ComponentClassification.PresentationLocal
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)
open CFSG.Monster.Existence.Compat (statedScalars_eq_bot statedProjEquivOfBot)
open scoped IsMulCommutative commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

private theorem closure_pair_facts {G : Type*} [Group G] (a b g : G) (hab : a * b = b * a)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hga : g * a * g⁻¹ = b) (hgb : g * b * g⁻¹ = a⁻¹) :
    (∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x) ∧
    (∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 3 = 1) ∧
    (∀ x ∈ Subgroup.closure ({a, b} : Set G), g * x * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G)) ∧
    (∀ x ∈ Subgroup.closure ({a, b} : Set G), g * g * x * (g * g)⁻¹ = x⁻¹) := by
  set E := Subgroup.closure ({a, b} : Set G) with hE
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hgen : ∀ s ∈ ({a, b} : Set G), ∀ t ∈ ({a, b} : Set G), s * t = t * s := by
    rintro s (rfl | rfl) t (rfl | rfl)
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx
    have hgx : ∀ s ∈ ({a, b} : Set G), s * x = x * s := by
      intro s hs
      have hle : E ≤ Subgroup.centralizer {s} := by
        rw [hE, Subgroup.closure_le]
        intro t ht
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact hgen t ht s hs
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
    have hle : E ≤ Subgroup.centralizer {x} := by
      rw [hE, Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hgx t ht
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  refine ⟨hcomm, ?_, ?_, ?_⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ha3
      · exact hb3
    | one => exact one_pow 3
    | mul y z hy hz ihy ihz =>
      rw [(Commute.mul_pow (hcomm y hy z hz) 3), ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [hga]
        exact hbE
      · rw [hgb]
        exact E.inv_mem haE
    | one => simp
    | mul y z hy hz ihy ihz =>
      have h : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [h]
      exact E.mul_mem ihy ihz
    | inv y hy ihy =>
      have h : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [h]
      exact E.inv_mem ihy
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · calc g * g * y * (g * g)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by group
          _ = y⁻¹ := by rw [hga, hgb]
      · calc g * g * y * (g * g)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by group
          _ = g * a⁻¹ * g⁻¹ := by rw [hgb]
          _ = (g * a * g⁻¹)⁻¹ := by group
          _ = y⁻¹ := by rw [hga]
    | one => simp
    | mul y z hy hz ihy ihz =>
      have h : g * g * (y * z) * (g * g)⁻¹ =
          (g * g * y * (g * g)⁻¹) * (g * g * z * (g * g)⁻¹) := by group
      rw [h, ihy, ihz, _root_.mul_inv_rev]
      exact hcomm y⁻¹ (E.inv_mem hy) z⁻¹ (E.inv_mem hz)
    | inv y hy ihy =>
      have h : g * g * y⁻¹ * (g * g)⁻¹ = (g * g * y * (g * g)⁻¹)⁻¹ := (conj_inv).symm
      rw [h, ihy]

theorem four_le_of_order_three_pair {X : Type*} [Group X] (C : Subgroup X) [Finite C]
    (V : Subgroup X) [Finite V] [IsMulCommutative V] {s m : ℕ} (hs : s.Prime) (hs3 : s ≠ 3)
    (hexp : ∀ v ∈ V, v ^ s = 1) (hcard : Nat.card V = s ^ m)
    (hnorm : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hfaith : ∀ c ∈ C, (∀ v ∈ V, c * v * c⁻¹ = v) → c = 1)
    (a b g : C) (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hga : g * a * g⁻¹ = b) (hgb : g * b * g⁻¹ = a⁻¹) : 4 ≤ m := by
  classical
  obtain ⟨hcomm, hE3, hgE, hg2⟩ := closure_pair_facts a b g hab ha3 hb3 hga hgb
  set E : Subgroup C := Subgroup.closure ({a, b} : Set C) with hE
  have hEc : IsMulCommutative E := ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩
  have hnt : E ≠ ⊥ := by
    intro h
    apply ha1
    have haE : a ∈ E := Subgroup.subset_closure (by simp)
    rw [h] at haE
    exact Subgroup.mem_bot.mp haE
  have : Fact s.Prime := ⟨hs⟩
  have hchar : CharP (AlgebraicClosure (ZMod s)) s :=
    charP_of_injective_algebraMap (algebraMap (ZMod s) (AlgebraicClosure (ZMod s))).injective s
  obtain ⟨m', ρ, hcard', hρ1⟩ := exists_rep_of_elementary_abelian C.subtype V hs hexp
    (fun c v hv => hnorm c c.2 v hv) (AlgebraicClosure (ZMod s))
  have hmm : m' = m := by
    have h : s ^ m' = s ^ m := by rw [← hcard', hcard]
    exact Nat.pow_right_injective hs.two_le h
  have hinv : ((Nat.card E : ℕ) : AlgebraicClosure (ZMod s)) ≠ 0 := by
    intro h
    have h1 : s ∣ Nat.card E := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod s)) s _).mp h
    obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := E) s h1
    have he3 : e ^ 3 = 1 := Subtype.ext (hE3 e e.2)
    have h2 : s ∣ 3 := he ▸ orderOf_dvd_of_pow_eq_one he3
    exact hs3 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp h2)
  have hinj : ∀ e ∈ E, ρ e = 1 → e = 1 :=
    fun e _ he => Subtype.ext (hfaith e e.2 (hρ1 e he))
  have hodd : ∀ e ∈ E, e * e = 1 → e = 1 := by
    intro e he hee
    have h1 : e = e ^ 3 * (e * e)⁻¹ := by group
    rw [hE3 e he, hee] at h1
    simpa using h1
  have h4 := four_le_finrank_of_inverting ρ E hEc hinv hinj hodd hnt g hgE hg2
  rw [Module.finrank_fin_fun] at h4
  omega

private def permA : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def permB : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

private def permG : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 3 * (Equiv.swap 1 4 * Equiv.swap 4 2 * Equiv.swap 2 5)

private theorem perm_data :
    permA * permB = permB * permA ∧ permA ^ 3 = 1 ∧ permB ^ 3 = 1 ∧ permA ≠ 1 ∧
      permG * permA * permG⁻¹ = permB ∧ permG * permB * permG⁻¹ = permA⁻¹ := by
  decide +kernel

private theorem exists_order_three_pair_alt :
    ∃ a b g : alternatingGroup (Fin 6), a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a⁻¹ := by
  have hA : permA ∈ alternatingGroup (Fin 6) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hB : permB ∈ alternatingGroup (Fin 6) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hG : permG ∈ alternatingGroup (Fin 6) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := perm_data
  exact ⟨⟨permA, hA⟩, ⟨permB, hB⟩, ⟨permG, hG⟩, Subtype.ext h1, Subtype.ext h2, Subtype.ext h3,
    fun h => h4 (congrArg Subtype.val h), Subtype.ext h5, Subtype.ext h6⟩

private theorem spScalars_eq_bot {k : Type} [Field k] (hk : Nat.card k = 2) :
    spScalars 2 k = ⊥ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  rw [spScalars, statedScalars_eq_bot hk, Subgroup.bot_subgroupOf]

theorem proj_subfieldSpHom_injective {K : Type} [Field K] (k : Subfield K)
    (hk : Nat.card k = 2) : Function.Injective ((proj 2 K).comp (subfieldSpHom 2 k)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := (proj_subfieldSpHom_eq_one_iff k g).mp hg
  rwa [spScalars_eq_bot hk, Subgroup.mem_bot] at h

@[expose] noncomputable def spTwoTwoEquiv {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    StatedSp 2 k ≃* sympFour :=
  (statedProjEquivOfBot (StatedSp 2 k) (statedScalars_eq_bot hk)).symm.trans
    (statedProjEquivSympFour hk)

theorem map_commutator_spTwoTwoEquiv {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    (commutator (StatedSp 2 k)).map (spTwoTwoEquiv hk : StatedSp 2 k →* sympFour) =
      commutator sympFour := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (spTwoTwoEquiv hk).surjective,
    ← commutator_def]

@[expose] noncomputable def commutatorSpTwoEquiv {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) : commutator (StatedSp 2 k) ≃* alternatingGroup (Fin 6) :=
  ((spTwoTwoEquiv hk).subgroupMap (commutator (StatedSp 2 k))).trans
    ((MulEquiv.subgroupCongr (map_commutator_spTwoTwoEquiv hk)).trans commutatorEquivAlternating)

theorem proj_subfieldSpHom_commutator_injective {K : Type} [Field K] (k : Subfield K)
    (hk : Nat.card k = 2) :
    Function.Injective
      ((proj 2 K).comp ((subfieldSpHom 2 k).comp (commutator (StatedSp 2 k)).subtype)) :=
  (proj_subfieldSpHom_injective k hk).comp (Subgroup.subtype_injective _)

@[expose] noncomputable def rangeCommutatorEquiv {K : Type} [Field K] (k : Subfield K)
    (hk : Nat.card k = 2) :
    ((proj 2 K).comp ((subfieldSpHom 2 k).comp (commutator (StatedSp 2 k)).subtype)).range ≃*
      alternatingGroup (Fin 6) :=
  haveI : Finite k := Nat.finite_of_card_ne_zero (by omega)
  (MonoidHom.ofInjective (proj_subfieldSpHom_commutator_injective k hk)).symm.trans
    (commutatorSpTwoEquiv hk)

theorem isSimpleGroup_range_commutator_sp_two_two {K : Type} [Field K] [Finite K]
    (k : Subfield K) (hk : Nat.card k = 2) :
    IsSimpleGroup ((proj 2 K).comp
      ((subfieldSpHom 2 k).comp (commutator (StatedSp 2 k)).subtype)).range :=
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  (rangeCommutatorEquiv k hk).isSimpleGroup

private theorem charP_two_of_card_two {k : Type} [Field k] (hk : Nat.card k = 2) : CharP k 2 := by
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime hk'

theorem spEnd_mem_span_pair {r : ℕ} {K : Type} [Field K] (k : Subfield K) (x : StatedSp r K)
    (hx : ∀ n ∈ commutator (StatedSp r k), x * subfieldSpHom r k n = subfieldSpHom r k n * x)
    (u₀ v₀ : Fin r ⊕ Fin r → k) (huv : spForm r k u₀ v₀ = 1) :
    spEnd x (fun a => (v₀ a : K)) ∈
      Submodule.span K {(fun a => (u₀ a : K) : Fin r ⊕ Fin r → K), fun a => (v₀ a : K)} := by
  set u : Fin r ⊕ Fin r → K := fun a => (u₀ a : K) with hu
  set v : Fin r ⊕ Fin r → K := fun a => (v₀ a : K) with hv
  have huvK : spForm r K u v = 1 := by
    have h := spForm_map k.subtype u₀ v₀
    rw [huv, map_one] at h
    exact h
  have hc : ⁅spTransvection u₀ (1 : k), spTransvection v₀ (1 : k)⁆ ∈ commutator (StatedSp r k) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hj : subfieldSpHom r k ⁅spTransvection u₀ (1 : k), spTransvection v₀ (1 : k)⁆ =
      ⁅spTransvection u (1 : K), spTransvection v (1 : K)⁆ := by
    rw [map_commutatorElement, subfieldSpHom_spTransvection, subfieldSpHom_spTransvection]
    rfl
  have hcomm := hx _ hc
  rw [hj] at hcomm
  have key : spEnd x (spEnd ⁅spTransvection u (1 : K), spTransvection v (1 : K)⁆ u) =
      spEnd ⁅spTransvection u (1 : K), spTransvection v (1 : K)⁆ (spEnd x u) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, ← spEnd_mul, hcomm]
  rw [spEnd_commutator_transvection_left huvK] at key
  have hmov : ⁅spTransvection u (1 : K), spTransvection v (1 : K)⁆ ∈
      spanMoving (Submodule.span K {u, v}) := by
    have h1 : spTransvection u (1 : K) ∈ spanMoving (Submodule.span K {u, v}) :=
      spTransvection_mem_spanMoving (Submodule.subset_span (by simp)) 1
    have h2 : spTransvection v (1 : K) ∈ spanMoving (Submodule.span K {u, v}) :=
      spTransvection_mem_spanMoving (Submodule.subset_span (by simp)) 1
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h1 h2) (inv_mem h1)) (inv_mem h2)
  have h3 := hmov (spEnd x u)
  rw [← key, map_sub, sub_sub_cancel_left] at h3
  exact (Submodule.neg_mem_iff _).mp h3

private def pt4 (a b c d : ZMod 2) : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![a, b] ![c, d]

theorem matrix_scalar_of_pairs {K : Type} [Field K] (κ : ZMod 2 →+* K)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (h : ∀ w₁ w₂ : Fin 2 ⊕ Fin 2 → ZMod 2, spForm 2 (ZMod 2) w₁ w₂ = 1 →
      ∃ α β : K, ∀ i, (M *ᵥ (κ ∘ w₂)) i = α * κ (w₁ i) + β * κ (w₂ i)) :
    ∃ d : K, M = d • 1 := by
  obtain ⟨α₀, β₀, h₀⟩ := h (pt4 0 0 1 0) (pt4 1 0 0 0) (by decide)
  obtain ⟨α₀', β₀', h₀'⟩ := h (pt4 0 1 1 0) (pt4 1 0 0 0) (by decide)
  obtain ⟨α₁, β₁, h₁⟩ := h (pt4 0 0 0 1) (pt4 0 1 0 0) (by decide)
  obtain ⟨α₁', β₁', h₁'⟩ := h (pt4 1 0 0 1) (pt4 0 1 0 0) (by decide)
  obtain ⟨α₂, β₂, h₂⟩ := h (pt4 1 0 0 0) (pt4 0 0 1 0) (by decide)
  obtain ⟨α₂', β₂', h₂'⟩ := h (pt4 1 1 0 0) (pt4 0 0 1 0) (by decide)
  obtain ⟨α₃, β₃, h₃⟩ := h (pt4 0 1 0 0) (pt4 0 0 0 1) (by decide)
  obtain ⟨α₃', β₃', h₃'⟩ := h (pt4 1 1 0 0) (pt4 0 0 0 1) (by decide)
  obtain ⟨α₄, β₄, h₄⟩ := h (pt4 0 0 1 0) (pt4 1 1 0 0) (by decide)
  obtain ⟨α₅, β₅, h₅⟩ := h (pt4 1 0 0 0) (pt4 0 0 1 1) (by decide)
  obtain ⟨α₆, β₆, h₆⟩ := h (pt4 0 1 1 0) (pt4 1 0 1 0) (by decide)
  simp only [Sum.forall, Fin.forall_fin_two] at h₀ h₀' h₁ h₁' h₂ h₂' h₃ h₃' h₄ h₅ h₆
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pt4] at h₀ h₀' h₁ h₁'
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pt4] at h₂ h₂' h₃ h₃'
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pt4] at h₄ h₅ h₆
  refine ⟨M (Sum.inl 0) (Sum.inl 0), ?_⟩
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp <;> grind

theorem eq_one_of_commute_commutator_sp_two_two {K : Type} [Field K]
    (k : Subfield K) (hk : Nat.card k = 2) (x : StatedSp 2 K)
    (hx : ∀ n ∈ commutator (StatedSp 2 k), x * subfieldSpHom 2 k n = subfieldSpHom 2 k n * x) :
    proj 2 K x = 1 := by
  have := charP_two_of_card_two hk
  let ι : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k
  let κ : ZMod 2 →+* K := k.subtype.comp ι
  have hpair : ∀ w₁ w₂ : Fin 2 ⊕ Fin 2 → ZMod 2, spForm 2 (ZMod 2) w₁ w₂ = 1 →
      ∃ α β : K, ∀ i, ((((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (κ ∘ w₂)) i = α * κ (w₁ i) + β * κ (w₂ i)) := by
    intro w₁ w₂ hw
    have h := spEnd_mem_span_pair k x hx (ι ∘ w₁) (ι ∘ w₂)
      (by rw [spForm_map ι w₁ w₂, hw, map_one])
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    exact ⟨a, b, fun i => (congrFun hab i).symm⟩
  obtain ⟨d, hd⟩ := matrix_scalar_of_pairs κ _ hpair
  have hd0 : d ≠ 0 := by
    intro hd0
    have hM0 : ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 0 := by
      rw [hd, hd0, zero_smul]
    have h1 := Units.mul_inv (x : GL (Fin 2 ⊕ Fin 2) K)
    rw [hM0, Matrix.zero_mul] at h1
    have h2 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    simp at h2
  have hmem : x ∈ spScalars 2 K := by
    refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
    change ((Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 d hd0) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hd,
      Matrix.smul_one_eq_diagonal]
    rfl
  rw [← MonoidHom.mem_ker, ker_proj]
  exact hmem

theorem centralizer_commutator_sp_two_two {K : Type} [Field K] [Finite K]
    (k : Subfield K) (hk : Nat.card k = 2) (x : StatedProj (StatedSp 2 K))
    (hx : ∀ n : commutator (StatedSp 2 k),
      x * proj 2 K (subfieldSpHom 2 k n) = proj 2 K (subfieldSpHom 2 k n) * x) : x = 1 := by
  classical
  have hcharK : CharP K 2 :=
    (RingHom.charP_iff k.subtype k.subtype.injective 2).mp (charP_two_of_card_two hk)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hdvd : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 (PNat.ne_zero n)
  have hker : (proj 2 K).ker = ⊥ := by
    rw [ker_proj, ← Subgroup.card_eq_one, card_spScalars_eq_gcd K (by norm_num)]
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h2 : ¬ 2 ∣ Nat.card K - 1 := by omega
    exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
  have hinj : Function.Injective (proj 2 K) := (MonoidHom.ker_eq_bot_iff _).mp hker
  obtain ⟨y, rfl⟩ := proj_surjective (r := 2) (K := K) x
  refine eq_one_of_commute_commutator_sp_two_two k hk y (fun m hm => hinj ?_)
  rw [map_mul, map_mul]
  exact hx ⟨m, hm⟩

theorem alternatingGroup_six_faithful_false {X : Type*} [Group X] (C : Subgroup X) [Finite C]
    (θ : C ≃* alternatingGroup (Fin 6)) (V : Subgroup X) [Finite V] [IsMulCommutative V]
    {s m : ℕ} (hs : s.Prime) (hVexp : ∀ v ∈ V, v ^ s = 1) (hcard : Nat.card V = s ^ m)
    (hnorm : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hfaith : ∀ c ∈ C, (∀ v ∈ V, c * v * c⁻¹ = v) → c = 1) (hm : m ≤ 3) : False := by
  classical
  by_cases h3 : s = 3
  ·
    subst h3
    have hCcard : Nat.card C = 360 := by
      rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hdvd := card_dvd_of_faithful C V hs hVexp hcard hnorm hfaith
    rw [hCcard] at hdvd
    interval_cases m <;> revert hdvd <;> decide
  ·
    obtain ⟨a, b, g, hab, ha3, hb3, ha1, hga, hgb⟩ := exists_order_three_pair_alt
    have h4 := four_le_of_order_three_pair C V hs h3 hVexp hcard hnorm hfaith (θ.symm a)
      (θ.symm b) (θ.symm g)
      (by rw [← map_mul, ← map_mul, hab])
      (by rw [← map_pow, ha3, map_one]) (by rw [← map_pow, hb3, map_one])
      (fun h => ha1 (by simpa using congrArg θ h))
      (by rw [← map_inv, ← map_mul, ← map_mul, hga])
      (by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, hgb])
    omega

theorem sp_two_two_closing {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : Nat.card k = 2) {s m : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (V : Subgroup (StatedProj (StatedSp 2 K))) [Finite V] [IsMulCommutative V]
    (hVexp : ∀ v ∈ V, v ^ s = 1) (hcard : Nat.card V = s ^ m) (hV0 : V ≠ ⊥)
    (hVnorm : ∀ g ∈ commutator (StatedSp 2 k), ∀ v ∈ V,
      proj 2 K (subfieldSpHom 2 k g) * v * (proj 2 K (subfieldSpHom 2 k g))⁻¹ ∈ V)
    (hfaith : ∀ g ∈ commutator (StatedSp 2 k), (∀ v ∈ V, proj 2 K (subfieldSpHom 2 k g) * v *
      (proj 2 K (subfieldSpHom 2 k g))⁻¹ = v) → proj 2 K (subfieldSpHom 2 k g) = 1)
    (hm : m ≤ 3) : False := by
  have _ := hs2
  have _ := hV0
  have : Finite (StatedProj (StatedSp 2 K)) :=
    Finite.of_surjective (proj 2 K) (proj_surjective (r := 2) (K := K))
  refine alternatingGroup_six_faithful_false
    ((proj 2 K).comp ((subfieldSpHom 2 k).comp (commutator (StatedSp 2 k)).subtype)).range
    (rangeCommutatorEquiv k hk) V hs hVexp hcard ?_ ?_ hm
  · rintro _ ⟨n, rfl⟩ v hv
    exact hVnorm n n.2 v hv
  · rintro _ ⟨n, rfl⟩ h
    exact hfaith n n.2 h

end CFSG.SignalizerFunctorTheorem.NonLocal
