module

public import CFSG.LocalAnalysis.StandardType.FS81.RootFusionGen
public import CFSG.LocalAnalysis.UniquenessCase.UCSingerL3
public import CFSG.Assembly.OrderReductions.ElementaryRepresentation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UCK461
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Pointwise

private lemma l3Two_add_add_eq_zero {k : Type*} [Field k] {K V : Type*} [Group K]
    [AddCommGroup V] [Module k V] (ρ : Representation k K V) {x : K} (hx3 : x ^ 3 = 1)
    (hCV : ∀ v, ρ x v = v → v = 0) (w : V) :
    w + ρ x w + ρ (x ^ 2) w = 0 := by
  apply hCV
  have h1 : ρ x (ρ x w) = ρ (x ^ 2) w := by
    rw [← Module.End.mul_apply, ← map_mul, pow_two]
  have h2 : ρ x (ρ (x ^ 2) w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, show x * x ^ 2 = x ^ 3 by rw [← pow_succ'],
      hx3, map_one, Module.End.one_apply]
  rw [map_add, map_add, h1, h2]
  abel

private lemma l3Two_sum_conj_eq {k : Type*} [Field k] {K V : Type*} [Group K]
    [AddCommGroup V] [Module k V] (ρ : Representation k K V) {y : K} {H : Subgroup K}
    [Fintype H] (hyH : ∀ h ∈ H, y * h * y⁻¹ ∈ H)
    (hyCH : ∀ h ∈ H, y * h * y⁻¹ = h → h = 1) (v : V) :
    ∑ h : H, ρ (h⁻¹ * y * h) v = ∑ h : H, ρ h (ρ y v) := by
  classical
  let φ : H → H := fun h => ⟨h⁻¹ * (y * h * y⁻¹), H.mul_mem (H.inv_mem h.2) (hyH h h.2)⟩
  have hφ : Function.Bijective φ := by
    refine Finite.injective_iff_bijective.mp fun a b hab => ?_
    have h : (a : K)⁻¹ * (y * a * y⁻¹) = (b : K)⁻¹ * (y * b * y⁻¹) := congrArg Subtype.val hab
    have h' : y * ((b : K) * (a : K)⁻¹) * y⁻¹ = (b : K) * (a : K)⁻¹ := by
      calc y * ((b : K) * (a : K)⁻¹) * y⁻¹
          = b * ((b : K)⁻¹ * (y * b * y⁻¹)) * (y * (a : K)⁻¹ * y⁻¹) := by group
        _ = b * ((a : K)⁻¹ * (y * a * y⁻¹)) * (y * (a : K)⁻¹ * y⁻¹) := by rw [← h]
        _ = (b : K) * (a : K)⁻¹ := by group
    have h1 := hyCH _ (H.mul_mem b.2 (H.inv_mem a.2)) h'
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  refine Fintype.sum_bijective φ hφ _ _ fun h => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  change (h : K)⁻¹ * y * h = (h : K)⁻¹ * (y * h * y⁻¹) * y
  group

private lemma l3Two_conj_summand {k : Type*} [Field k] {K V : Type*} [Group K]
    [AddCommGroup V] [Module k V] (ρ : Representation k K V) {x : K} (hx3 : x ^ 3 = 1)
    (hCV : ∀ v, ρ x v = v → v = 0) (h : K) (v : V) :
    v + ρ (h⁻¹ * x * h) v + ρ (h⁻¹ * x ^ 2 * h) v = 0 := by
  have hzero := l3Two_add_add_eq_zero ρ hx3 hCV
  have e3 : ∀ (a b c : K) (u : V), ρ a (ρ b (ρ c u)) = ρ (a * b * c) u := fun a b c u => by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc]
  have h1 := congrArg (ρ h⁻¹) (hzero (ρ h v))
  rw [map_add, map_add, map_zero, e3, e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] at h1
  exact h1

private lemma l3Two_conj_pow_two {K : Type*} [Group K] {H : Subgroup K} {x : K}
    (hx3 : x ^ 3 = 1) (hCH : ∀ h ∈ H, x * h * x⁻¹ = h → h = 1) :
    ∀ h ∈ H, x ^ 2 * h * (x ^ 2)⁻¹ = h → h = 1 := by
  intro h hh hc
  have hx2inv : x ^ 2 = x⁻¹ := by
    have h : (x ^ 2)⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hx3])
    simpa using congrArg Inv.inv h
  have h2 : x⁻¹ * h * x = h := by simpa [hx2inv] using hc
  refine hCH h hh ?_
  calc x * h * x⁻¹ = x * (x⁻¹ * h * x) * x⁻¹ := by rw [h2]
    _ = h := by group

private lemma l3Two_sum_eq_nsmul {k : Type*} [Field k] {K V : Type*} [Group K]
    [AddCommGroup V] [Module k V] (ρ : Representation k K V) {x : K} (hx3 : x ^ 3 = 1)
    (hCV : ∀ v, ρ x v = v → v = 0) {H : Subgroup K} [Fintype H]
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hCH : ∀ h ∈ H, x * h * x⁻¹ = h → h = 1) (v : V) :
    ∑ h : H, ρ (h : K) v = Nat.card H • v := by
  classical
  have hx2H : ∀ g ∈ H, x ^ 2 * g * (x ^ 2)⁻¹ ∈ H := fun g hg => by
    have := hxH _ (hxH g hg)
    rwa [show x * (x * g * x⁻¹) * x⁻¹ = x ^ 2 * g * (x ^ 2)⁻¹ by simp only [pow_two]; group]
      at this
  have hsum : ∑ h : H, (v + ρ (h⁻¹ * x * h) v + ρ (h⁻¹ * x ^ 2 * h) v) = 0 :=
    Finset.sum_eq_zero fun h _ => l3Two_conj_summand ρ hx3 hCV h v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    l3Two_sum_conj_eq ρ hxH hCH v,
    l3Two_sum_conj_eq ρ hx2H (l3Two_conj_pow_two hx3 hCH) v,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card] at hsum
  have hneg : ρ x v + ρ (x ^ 2) v = -v := by
    have h := l3Two_add_add_eq_zero ρ hx3 hCV v
    rw [add_assoc] at h
    exact eq_neg_of_add_eq_zero_right h
  rw [add_assoc, ← Finset.sum_add_distrib] at hsum
  simp only [← map_add] at hsum
  rw [hneg] at hsum
  simp only [map_neg, Finset.sum_neg_distrib] at hsum
  rw [add_neg_eq_zero] at hsum
  exact hsum.symm

private theorem l3Two_apply_eq_self {k : Type*} [Field k] {K V : Type*} [Group K]
    [AddCommGroup V] [Module k V] (ρ : Representation k K V) {x : K} (hx3 : x ^ 3 = 1)
    (hCV : ∀ v, ρ x v = v → v = 0) {H : Subgroup K} [Fintype H]
    (hcard : (Nat.card H : k) ≠ 0)
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hCH : ∀ h ∈ H, x * h * x⁻¹ = h → h = 1)
    {f : K} (hf : f ∈ H) (v : V) : ρ f v = v := by
  classical
  have hTv : ∑ h : H, ρ (h : K) v = Nat.card H • v :=
    l3Two_sum_eq_nsmul ρ hx3 hCV hxH hCH v
  have hTfix : ρ f (∑ h : H, ρ (h : K) v) = ∑ h : H, ρ (h : K) v := by
    simp only [map_sum]
    simp only [← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_bijective (fun k : H => (⟨f, hf⟩ : H) * k)
      (Group.mulLeft_bijective _) _ _ fun k => rfl
  have hstep : Nat.card H • (ρ f v) = Nat.card H • v := by
    calc Nat.card H • (ρ f v) = ρ f (Nat.card H • v) := (map_nsmul (ρ f) _ _).symm
      _ = ρ f (∑ h : H, ρ (h : K) v) := by rw [hTv]
      _ = ∑ h : H, ρ (h : K) v := hTfix
      _ = Nat.card H • v := hTv
  have hsmul : Nat.card H • (ρ f v - v) = 0 := by
    rw [smul_sub, hstep, sub_self]
  have hcast : (Nat.card H : k) • (ρ f v - v) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, hsmul]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hcast).resolve_left hcard)

private theorem l3Two_statedClassicalModel {P : Type} [Group P]
    (e : P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel P .PSL 3 2 1 := by
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(e.trans e₂.symm).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

private theorem l3Two_isSimpleGroup {P : Type} [Group P]
    (e : P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : IsSimpleGroup P :=
  CFSG.RankThree.PartTwo.Sec3.isSimpleGroup_of_statedClassicalModel_psl
    (l3Two_statedClassicalModel e)

private abbrev l3TwoSL3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private def l3TwoB0 : l3TwoSL3 := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 1], by decide⟩

private def l3TwoT1 : l3TwoSL3 := ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩

private def l3TwoT2 : l3TwoSL3 := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

private def l3TwoU0 : Subgroup l3TwoSL3 where
  carrier := {x | x = 1 ∨ x = l3TwoT1 ∨ x = l3TwoT2 ∨ x = l3TwoT1 * l3TwoT2}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rcases ha with h1 | h1 | h1 | h1 <;> rw [h1] <;>
      rcases hb with h2 | h2 | h2 | h2 <;> rw [h2] <;> decide
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rcases ha with h1 | h1 | h1 | h1 <;> rw [h1] <;> decide

private instance l3TwoU0_decidableMem : DecidablePred (fun x : l3TwoSL3 => x ∈ l3TwoU0) :=
  fun x => by
    change Decidable (x = 1 ∨ x = l3TwoT1 ∨ x = l3TwoT2 ∨ x = l3TwoT1 * l3TwoT2)
    infer_instance

private theorem l3TwoU0_card : Fintype.card l3TwoU0 = 4 := by
  decide

private theorem l3TwoU0_normal : l3TwoB0 ∈ Subgroup.normalizer (l3TwoU0 : Set l3TwoSL3) := by
  rw [Subgroup.mem_normalizer_iff]
  decide +kernel

private theorem l3TwoU0_fix : ∀ u ∈ l3TwoU0, l3TwoB0 * u * l3TwoB0⁻¹ = u → u = 1 := by
  decide +kernel

private theorem l3Two_conj_class : ∀ b : l3TwoSL3, b ^ 3 = 1 → b ≠ 1 →
    ∃ g : l3TwoSL3, b = g * l3TwoB0 * g⁻¹ := by
  decide +kernel

private theorem l3Two_exists_kleinFour (b : l3TwoSL3) (hb : orderOf b = 3) :
    ∃ U : Subgroup l3TwoSL3, Nat.card U = 4 ∧
      b ∈ Subgroup.normalizer (U : Set l3TwoSL3) ∧
      ∀ u ∈ U, b * u * b⁻¹ = u → u = 1 := by
  have hb3 : b ^ 3 = 1 := by
    have h : orderOf b ∣ 3 := by rw [hb]
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hb1 : b ≠ 1 := by rintro rfl; rw [orderOf_one] at hb; omega
  obtain ⟨g, hg⟩ := l3Two_conj_class b hb3 hb1
  refine ⟨l3TwoU0.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Nat.card_eq_fintype_card]
    exact l3TwoU0_card
  · have hmap := Subgroup.map_equiv_normalizer_eq l3TwoU0 (MulAut.conj g)
    rw [← hmap]
    have hgb : (MulAut.conj g) l3TwoB0 = b := by
      rw [MulAut.conj_apply]
      exact hg.symm
    rw [← hgb]
    exact Subgroup.mem_map_of_mem _ l3TwoU0_normal
  · intro u hu hbu
    rw [Subgroup.mem_map] at hu
    obtain ⟨y, hy, hyu⟩ := hu
    have hyu' : g * y * g⁻¹ = u := hyu
    have hb0 : l3TwoB0 * y * l3TwoB0⁻¹ = y := by
      apply (MulAut.conj g).injective
      rw [MulAut.conj_apply, MulAut.conj_apply]
      calc g * (l3TwoB0 * y * l3TwoB0⁻¹) * g⁻¹
          = (g * l3TwoB0 * g⁻¹) * (g * y * g⁻¹) * (g * l3TwoB0 * g⁻¹)⁻¹ := by group
        _ = b * u * b⁻¹ := by rw [hg, ← hyu']
        _ = u := hbu
        _ = g * y * g⁻¹ := hyu'.symm
    rw [← hyu, l3TwoU0_fix y hy hb0, map_one]

private theorem l3Two_exists_kleinFour_of_mulEquiv {P : Type} [Group P]
    (e : P ≃* l3TwoSL3) {b : P} (hb : orderOf b = 3) :
    ∃ U : Subgroup P, Nat.card U = 4 ∧
      b ∈ Subgroup.normalizer (U : Set P) ∧
      ∀ u ∈ U, b * u * b⁻¹ = u → u = 1 := by
  have hb' : orderOf (e b) = 3 := (MulEquiv.orderOf_eq e b).trans hb
  obtain ⟨U₀, hcard, hnorm, hfix⟩ := l3Two_exists_kleinFour (e b) hb'
  refine ⟨U₀.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]
  · have hmap := Subgroup.map_equiv_normalizer_eq U₀ e.symm
    rw [← hmap]
    have heb : e.symm (e b) = b := e.symm_apply_apply b
    rw [← heb]
    exact Subgroup.mem_map_of_mem _ hnorm
  · intro u hu hbu
    rw [Subgroup.mem_map] at hu
    obtain ⟨y, hy, hyu⟩ := hu
    have hy1 : y = 1 := by
      refine hfix y hy ?_
      have h1 : e (b * u * b⁻¹) = e b * y * (e b)⁻¹ := by
        rw [← hyu]
        simp
      calc e b * y * (e b)⁻¹ = e (b * u * b⁻¹) := h1.symm
        _ = e u := congrArg e hbu
        _ = y := by
          rw [← hyu]
          simpa using MulEquiv.apply_symm_apply e y
    rw [← hyu, hy1, map_one]

private theorem l3Two_normal_action {G : Type*} [Group G] {T T₀ P : Subgroup G}
    (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPT₀ : P ≤ Subgroup.normalizer (T₀ : Set G)) :
    ∃ σ : ↥P →* MulAut ↥T,
      (∀ (g : ↥P) (x : ↥T), (((σ g) x : ↥T) : G) = (g : G) * (x : G) * (g : G)⁻¹) ∧
      ∀ g : ↥P, (T₀.subgroupOf T).map (σ g).toMonoidHom = T₀.subgroupOf T := by
  let σ : ↥P →* MulAut ↥T := T.normalizerMonoidHom.comp (Subgroup.inclusion hPT)
  have hcoe (g : ↥P) (x : ↥T) :
      (((σ g) x : ↥T) : G) = (g : G) * (x : G) * (g : G)⁻¹ := by
    rw [show σ g = T.normalizerMonoidHom (Subgroup.inclusion hPT g) from rfl,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  refine ⟨σ, hcoe, ?_⟩
  intro g
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : G) ∈ T₀ at hy
    change (((σ g) y : ↥T) : G) ∈ T₀
    rw [hcoe g y]
    exact (Subgroup.mem_normalizer_iff.mp (hPT₀ g.2) (y : G)).mp hy
  · intro hx
    change (x : G) ∈ T₀ at hx
    refine ⟨(σ g)⁻¹ x, ?_, (σ g).apply_symm_apply x⟩
    change ((((σ g)⁻¹ x : ↥T)) : G) ∈ T₀
    have hcoe' : ((((σ g)⁻¹ x : ↥T)) : G) = (g : G)⁻¹ * (x : G) * (g : G) := by
      rw [show (σ g)⁻¹ = σ (g⁻¹) from (map_inv σ g).symm]
      rw [hcoe (g⁻¹) x]
      simp
    rw [hcoe']
    simpa using (Subgroup.mem_normalizer_iff.mp (hPT₀ (P.inv_mem g.2)) (x : G)).mp hx

theorem l3Two_quotient_fixedPointFree {G : Type*} [Group G] {T T₀ P : Subgroup G}
    (hPT : P ≤ Subgroup.normalizer (T : Set G)) (hPT₀ : P ≤ Subgroup.normalizer (T₀ : Set G))
    [hN : (T₀.subgroupOf T).Normal] {b : G} (hbP : b ∈ P)
    (hfix : ∀ t ∈ T, b * t * b⁻¹ * t⁻¹ ∈ T₀ → t ∈ T₀) :
    ∃ τ : ↥P →* MulAut (↥T ⧸ T₀.subgroupOf T),
      ∀ x, τ ⟨b, hbP⟩ x = x → x = 1 := by
  classical
  let N : Subgroup ↥T := T₀.subgroupOf T
  haveI hNnormal : N.Normal := hN
  obtain ⟨σ, hcoe, hmap⟩ := l3Two_normal_action hPT hPT₀
  let τ : ↥P →* MulAut (↥T ⧸ N) :=
    { toFun := fun g => QuotientGroup.congr N N (σ g) (by simpa using hmap g)
      map_one' := by
        ext x
        obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N x
        change QuotientGroup.mk' N ((σ 1) t) = QuotientGroup.mk' N t
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext x
        obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N x
        change QuotientGroup.mk' N ((σ (g * h)) t) =
          QuotientGroup.mk' N ((σ g) ((σ h) t))
        rw [map_mul]
        rfl }
  refine ⟨τ, ?_⟩
  intro x hx
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hcongr : τ ⟨b, hbP⟩ (QuotientGroup.mk' N t) =
      QuotientGroup.mk' N (σ ⟨b, hbP⟩ t) := rfl
  rw [hcongr] at hx
  have hmemN : (σ ⟨b, hbP⟩ t)⁻¹ * t ∈ N := (QuotientGroup.eq (s := N)).mp hx
  have hmemT : (b : G) * (t : G)⁻¹ * (b : G)⁻¹ * (t : G) ∈ T₀ := by
    have h := Subgroup.mem_subgroupOf.mp hmemN
    rwa [show (((σ ⟨b, hbP⟩ t)⁻¹ * t : ↥T) : G) =
      (b : G) * (t : G)⁻¹ * (b : G)⁻¹ * (t : G) by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcoe]; group] at h
  have htT₀ : (t : G) ∈ T₀ := by
    have := hfix (t : G)⁻¹ (T.inv_mem t.2) (by simpa using hmemT)
    simpa using T₀.inv_mem this
  change ((t : ↥T) : ↥T ⧸ N) = 1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr htT₀

private theorem l3Two_exists_abelian_characteristic (X : Type) [Group X]
    (hne : ¬ Subsingleton X) (hsol : IsSolvable X) :
    ∃ A : Subgroup X, A.Characteristic ∧ A ≠ ⊥ ∧ ⁅A, A⁆ = ⊥ := by
  classical
  let p : ℕ → Prop := fun k => derivedSeries X k = ⊥
  have hp : ∃ k, p k := hsol.solvable
  let n : ℕ := Nat.find hp
  have hnbot : derivedSeries X n = ⊥ := Nat.find_spec hp
  have hnmin : ∀ m < n, derivedSeries X m ≠ ⊥ := fun m hm => Nat.find_min hp hm
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at hnbot
    exact hne (Subsingleton.intro fun a b => by
      have ha : a ∈ (⊥ : Subgroup X) := hnbot ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup X) := hnbot ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb])
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  refine ⟨derivedSeries X (n - 1), inferInstance, hnmin (n - 1) (Nat.sub_one_lt hn0), ?_⟩
  have h := derivedSeries_succ (G := X) (n - 1)
  rw [Nat.sub_add_cancel hnpos] at h
  rw [← h, hnbot]

private theorem l3Two_exists_prime_order_element {X : Type*} [Group X] [Finite X]
    {A : Subgroup X} (hAne : A ≠ ⊥) :
    ∃ (p : ℕ) (_ : p.Prime) (a : X), a ∈ A ∧ orderOf a = p := by
  have hcard : Nat.card A ≠ 1 := fun h => hAne (Subgroup.eq_bot_of_card_eq A h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpdvd
  exact ⟨p, hp, (a : X), a.2, (Subgroup.orderOf_coe a).trans ha⟩

private theorem l3Two_exists_elementaryAbelian {X : Type*} [Group X]
    {A : Subgroup X} (hAchar : A.Characteristic) (hAab : ⁅A, A⁆ = ⊥) {p : ℕ}
    (hp : p.Prime) {a : X} (haA : a ∈ A) (haord : orderOf a = p) :
    ∃ V : Subgroup X, V.Characteristic ∧ a ∈ V ∧ IsElementaryAbelian p V := by
  classical
  haveI hAcomm : IsMulCommutative A := Subgroup.commutator_self_eq_bot_iff.mp hAab
  letI : CommGroup A := IsMulCommutative.instCommGroup
  let K : Subgroup A := (powMonoidHom p : A →* A).ker
  have hKchar : K.Characteristic := CFSG.Wielandt.powMonoidHom_ker_characteristic p
  let V : Subgroup X := K.map A.subtype
  haveI : A.Characteristic := hAchar
  haveI : K.Characteristic := hKchar
  have hVchar : V.Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
  have haV : a ∈ V := by
    refine Subgroup.mem_map.mpr ⟨⟨a, haA⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact Subtype.ext (by rw [← haord]; exact pow_orderOf_eq_one a)
  have hKelem : IsElementaryAbelian p K := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro y
    exact Subtype.ext (by simpa [powMonoidHom_apply] using MonoidHom.mem_ker.mp y.2)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsElementaryAbelian p K := hKelem
  exact ⟨V, hVchar, haV, IsElementaryAbelian.map_subtype⟩

private theorem l3Two_false_of_trivial_action {k : Type*} [Field k] {P V : Type} [Group P]
    [AddCommGroup V] [Module k V] (ρ : Representation k P V) (hP : IsSimpleGroup P) {b : P}
    (hbNotKer : b ∉ ρ.ker) {H : Subgroup P} [Fintype H] (hH : H ≠ ⊥)
    (hcard : (Nat.card H : k) ≠ 0) (hb3 : b ^ 3 = 1) (hCV : ∀ v, ρ b v = v → v = 0)
    (hxH : ∀ h ∈ H, b * h * b⁻¹ ∈ H)
    (hCH : ∀ h ∈ H, b * h * b⁻¹ = h → h = 1) : False := by
  obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have hfk : ρ (f : P) = 1 := by
    ext v
    exact l3Two_apply_eq_self ρ hb3 hCV hcard hxH hCH f.2 v
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · have : (f : P) ∈ ρ.ker := MonoidHom.mem_ker.mpr hfk
    rw [h] at this
    exact hf1 (Subtype.ext (Subgroup.mem_bot.mp this))
  · exact hbNotKer (h ▸ Subgroup.mem_top b)

private theorem l3Two_false_of_rep {p : ℕ} (hp : p.Prime) {P : Type} {W : Type} [Group P]
    [Finite P] [IsSimpleGroup P] (eP : P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    [AddCommGroup W] [Module (ZMod p) W] (ρ : Representation (ZMod p) P W) {b : P}
    (hb : orderOf b = 3) (hCV : ∀ w : W, ρ b w = w → w = 0)
    (hbNotKer : b ∉ ρ.ker) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hb3 : b ^ 3 = 1 := by
    have h : orderOf b ∣ 3 := by rw [hb]
    exact orderOf_dvd_iff_pow_eq_one.mp h
  by_cases hp7 : p = 7
  · subst hp7
    obtain ⟨U, hUcard, hUnorm, hUfix⟩ :=
      l3Two_exists_kleinFour_of_mulEquiv (b := b) eP hb
    haveI : Fintype U := Fintype.ofFinite U
    have hUne : U ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hUcard
      omega
    have hUcard' : (Nat.card U : ZMod 7) ≠ 0 := by
      intro h
      rw [hUcard, ZMod.natCast_eq_zero_iff] at h
      norm_num at h
    exact l3Two_false_of_trivial_action ρ inferInstance hbNotKer hUne hUcard' hb3 hCV
      (fun h hh => (Subgroup.mem_normalizer_iff.mp hUnorm h).mp hh) hUfix
  · obtain ⟨C, -, hCcard, hCnorm, hCfix⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.l3SingerFact_holds.1 P 2 1
        (l3Two_statedClassicalModel eP) (by decide) b hb
    haveI : Fintype C := Fintype.ofFinite C
    have hCne : C ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hCcard
      omega
    have hCcard' : (Nat.card C : ZMod p) ≠ 0 := by
      intro h
      rw [hCcard, ZMod.natCast_eq_zero_iff] at h
      exact hp7 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h)
    exact l3Two_false_of_trivial_action ρ inferInstance hbNotKer hCne hCcard' hb3 hCV
      (fun h hh => (Subgroup.mem_normalizer_iff.mp hCnorm h).mp hh) hCfix

theorem l3TwoFixedPointFree_holds :
    ∀ (P X : Type) [Group P] [Group X] [Finite X],
      Nonempty (P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∀ (φ : P →* MulAut X) (b : P), orderOf b = 3 → IsSolvable X →
        (∀ x : X, φ b x = x → x = 1) → Subsingleton X := by
  intro P X _ _ _ hP φ b hb hsol hfix
  classical
  obtain ⟨eP⟩ := hP
  haveI : Finite P := Finite.of_injective eP.toMonoidHom eP.injective
  haveI : IsSimpleGroup P := l3Two_isSimpleGroup eP
  by_contra hne
  obtain ⟨A, hAchar, hAne, hAab⟩ := l3Two_exists_abelian_characteristic X hne hsol
  obtain ⟨p, hp, a, haA, haord⟩ := l3Two_exists_prime_order_element hAne
  obtain ⟨V, hVchar, haV, hVexp⟩ := l3Two_exists_elementaryAbelian hAchar hAab hp haA haord
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsElementaryAbelian p V := hVexp
  letI : CommGroup V := IsMulCommutative.instCommGroup
  letI : V.Characteristic := hVchar
  let ψ : P →* MulAut V := (MulAut.characteristic V).comp φ
  let ρ : Representation (ZMod p) P (Additive V) :=
    CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation p ψ
  have hψ : ∀ (g : P) (v : V), ((ψ g v : V) : X) = φ g (v : X) := fun g v => rfl
  have hCV : ∀ v : Additive V, ρ b v = v → v = 0 := by
    intro v hv
    have hv' : ψ b v.toMul = v.toMul := by
      simpa [ρ, CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_apply]
        using congrArg Additive.toMul hv
    have hvX : ((v.toMul : V) : X) = 1 := by
      refine hfix _ ?_
      rw [← hψ b v.toMul]
      exact congrArg Subtype.val hv'
    have : v.toMul = 1 := Subtype.ext hvX
    simpa using congrArg Additive.ofMul this
  have hbNotKer : b ∉ ρ.ker := by
    intro hbk
    have h1 : ρ b = 1 := MonoidHom.mem_ker.mp hbk
    have h2 : ρ b (Additive.ofMul ⟨a, haV⟩) = Additive.ofMul ⟨a, haV⟩ := by
      rw [h1]
      rfl
    have h3 : a = 1 := by simpa using hCV _ h2
    have : orderOf a = 1 := by rw [h3, orderOf_one]
    rw [haord] at this
    exact (Fact.out : p.Prime).ne_one this
  exact l3Two_false_of_rep hp eP ρ hb hCV hbNotKer

theorem le_of_l3TwoFixedPointFree {G : Type} [Group G] [Finite G] {T T₀ P : Subgroup G}
    (hT₀T : T₀ ≤ T) (hT₀ : T ≤ Subgroup.normalizer (T₀ : Set G))
    (hPT : P ≤ Subgroup.normalizer (T : Set G)) (hPT₀ : P ≤ Subgroup.normalizer (T₀ : Set G))
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) {b : G} (hbP : b ∈ P)
    (hb : orderOf b = 3) (hsol : IsSolvable ↥T)
    (hfix : ∀ t ∈ T, b * t * b⁻¹ * t⁻¹ ∈ T₀ → t ∈ T₀) : T ≤ T₀ := by
  classical
  haveI hNnormal : (T₀.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mpr hT₀
  obtain ⟨τ, hfixτ⟩ := l3Two_quotient_fixedPointFree hPT hPT₀ hbP hfix
  let N : Subgroup ↥T := T₀.subgroupOf T
  haveI : N.Normal := hNnormal
  have hquot : IsSolvable (↥T ⧸ N) :=
    @Group.isSolvable_of_surjective ↥T (↥T ⧸ N) _ _ (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) hsol
  have hsub : Subsingleton (↥T ⧸ N) :=
    l3TwoFixedPointFree_holds ↥P (↥T ⧸ N) hP τ ⟨b, hbP⟩
      ((Subgroup.orderOf_mk b hbP).trans hb) hquot hfixτ
  intro t ht
  have h1 : (QuotientGroup.mk' N ⟨t, ht⟩ : ↥T ⧸ N) = 1 := Subsingleton.elim _ _
  change ((⟨t, ht⟩ : ↥T) : ↥T ⧸ N) = 1 at h1
  rw [QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

end CFSG.StandardType.FrameRoute.FS81
