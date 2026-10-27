module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DatumDefs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private noncomputable def ggLieDT_zeta : GGLˣ := ggZeta 3 Nat.prime_three (by norm_num)

private theorem ggLieDT_exists_exp {τ : Tag} {a : Fin τ.rank → GGLˣ}
    (horder : orderOf ggLieDT_zeta = 3) (ha : ∀ i, a i ^ 3 = 1) :
    ∃ k : Fin τ.rank → ℕ, ∀ i, ggLieDT_zeta ^ k i = a i := by
  choose k hk using fun i =>
    (IsPrimitiveRoot.iff_orderOf.2 horder).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity 3 (a i)).2 (ha i))
  exact ⟨k, fun i => (hk i).2⟩

private theorem ggLieDT_rootChar_eq {τ : Tag} (a : Fin τ.rank → GGLˣ) (k : Fin τ.rank → ℕ)
    (hk : ∀ i, ggLieDT_zeta ^ k i = a i) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = ggLieDT_zeta ^ (∑ i, γ i * (k i : ℤ)) := by
  rw [rootChar]
  trans ∏ i, ggLieDT_zeta ^ (γ i * (k i : ℤ))
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hk i, ← zpow_natCast, ← zpow_mul, mul_comm]
  · rw [Finset.prod_zpow_eq_zpow_sum]

private theorem ggLieDT_intCast_sum {τ : Tag} (γ : Fin τ.rank → ℤ) (k : Fin τ.rank → ℕ) :
    ((∑ i, γ i * (k i : ℤ) : ℤ) : ZMod 3) = ggLiePair γ (fun i => (k i : ZMod 3)) := by
  rw [ggLiePair]
  push_cast
  rfl

private theorem ggLieDT_rootChar_one_iff {τ : Tag}
    (a : Fin τ.rank → GGLˣ) (k : Fin τ.rank → ℕ)
    (horder : orderOf ggLieDT_zeta = 3)
    (hk : ∀ i, ggLieDT_zeta ^ k i = a i) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = 1 ↔ ggLiePair γ (fun i => (k i : ZMod 3)) = 0 := by
  rw [ggLieDT_rootChar_eq a k hk γ]
  have hiff : ggLieDT_zeta ^ (∑ i, γ i * (k i : ℤ)) = 1 ↔
      ((∑ i, γ i * (k i : ℤ) : ℤ) : ZMod 3) = 0 := by
    rw [zpow_eq_one_iff_modEq, horder, Int.modEq_zero_iff_dvd]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).symm
  rw [hiff, ggLieDT_intCast_sum γ k]

private theorem ggLieDT_rootChar_pow_two_iff {τ : Tag}
    (a : Fin τ.rank → GGLˣ) (k : Fin τ.rank → ℕ)
    (horder : orderOf ggLieDT_zeta = 3)
    (hk : ∀ i, ggLieDT_zeta ^ k i = a i) (γ γ' : Fin τ.rank → ℤ) :
    rootChar a γ' = rootChar a γ ^ 2 ↔
      ggLiePair γ' (fun i => (k i : ZMod 3)) = 2 * ggLiePair γ (fun i => (k i : ZMod 3)) := by
  rw [ggLieDT_rootChar_eq a k hk γ', ggLieDT_rootChar_eq a k hk γ]
  have h2 : (ggLieDT_zeta ^ (∑ i, γ i * (k i : ℤ))) ^ 2 =
      ggLieDT_zeta ^ (2 * (∑ i, γ i * (k i : ℤ))) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [h2]
  have hiff : ggLieDT_zeta ^ (∑ i, γ' i * (k i : ℤ)) =
      ggLieDT_zeta ^ (2 * (∑ i, γ i * (k i : ℤ))) ↔
      ((∑ i, γ' i * (k i : ℤ) : ℤ) : ZMod 3) =
        ((2 * (∑ i, γ i * (k i : ℤ)) : ℤ) : ZMod 3) := by
    rw [zpow_eq_zpow_iff_modEq, horder]
    exact (ZMod.intCast_eq_intCast_iff _ _ 3).symm
  rw [hiff]
  have h1 : (((∑ i, γ' i * (k i : ℤ)) : ℤ) : ZMod 3) =
      ggLiePair γ' (fun i => (k i : ZMod 3)) := ggLieDT_intCast_sum γ' k
  have h2' : (((2 * (∑ i, γ i * (k i : ℤ)) : ℤ)) : ZMod 3) =
      2 * ggLiePair γ (fun i => (k i : ZMod 3)) := by
    rw [show ((2 * (∑ i, γ i * (k i : ℤ)) : ℤ) : ZMod 3) =
        2 * (((∑ i, γ i * (k i : ℤ)) : ℤ) : ZMod 3) by
      rw [Int.cast_mul, Int.cast_ofNat]]
    rw [ggLieDT_intCast_sum γ k]
  rw [h1, h2']

private noncomputable def ggLieDT_pairHom {τ : Tag}
    (a₁ a₂ : Fin τ.rank → GGLˣ) (ha₁ : a₁ ^ 3 = 1) (ha₂ : a₂ ^ 3 = 1) :
    Multiplicative (ZMod 3 × ZMod 3) →* ModGL τ GGL where
  toFun u := rootDiagUnit τ (a₁ ^ (u.toAdd.1).val * a₂ ^ (u.toAdd.2).val)
  map_one' := by
    have h : Multiplicative.toAdd (1 : Multiplicative (ZMod 3 × ZMod 3)) = 0 :=
      toAdd_ofAdd (0 : ZMod 3 × ZMod 3)
    rw [h]
    show rootDiagUnit τ (a₁ ^ (0 : ZMod 3).val * a₂ ^ (0 : ZMod 3).val) = 1
    rw [ZMod.val_zero, pow_zero, pow_zero, mul_one, rootDiagUnit_one]
  map_mul' u v := by
    have hu : (u * v).toAdd = u.toAdd + v.toAdd := toAdd_mul u v
    rw [hu, Prod.fst_add, Prod.snd_add, ← rootDiagUnit_mul]
    congr 1
    have hmod₁ : (u.toAdd.1 + v.toAdd.1).val ≡ u.toAdd.1.val + v.toAdd.1.val [MOD 3] := by
      rw [ZMod.val_add]
      exact Nat.mod_modEq _ 3
    have hmod₂ : (u.toAdd.2 + v.toAdd.2).val ≡ u.toAdd.2.val + v.toAdd.2.val [MOD 3] := by
      rw [ZMod.val_add]
      exact Nat.mod_modEq _ 3
    rw [pow_eq_pow_of_modEq (x := a₁) hmod₁ ha₁,
      pow_eq_pow_of_modEq (x := a₂) hmod₂ ha₂, pow_add, pow_add]
    ac_rfl

private theorem ggLieDT_coord_eq_one_iff {τ : Tag}
    (a₁ a₂ : Fin τ.rank → GGLˣ) (k₁ k₂ : Fin τ.rank → ℕ)
    (horder : orderOf ggLieDT_zeta = 3)
    (hk₁ : ∀ i, ggLieDT_zeta ^ k₁ i = a₁ i)
    (hk₂ : ∀ i, ggLieDT_zeta ^ k₂ i = a₂ i)
    (i : Fin τ.rank) (s t : ZMod 3) :
    a₁ i ^ s.val * a₂ i ^ t.val = 1 ↔
      s * (k₁ i : ZMod 3) + t * (k₂ i : ZMod 3) = 0 := by
  set A : ℤ := (k₁ i : ℤ) * (s.val : ℤ) + (k₂ i : ℤ) * (t.val : ℤ) with hA
  have h₁' : a₁ i ^ s.val = ggLieDT_zeta ^ ((k₁ i : ℤ) * (s.val : ℤ)) := by
    rw [← hk₁ i, ← zpow_natCast ggLieDT_zeta (k₁ i),
      ← zpow_natCast (ggLieDT_zeta ^ (k₁ i : ℤ)) (s.val)]
    exact (zpow_mul ggLieDT_zeta (k₁ i : ℤ) (s.val : ℤ)).symm
  have h₂' : a₂ i ^ t.val = ggLieDT_zeta ^ ((k₂ i : ℤ) * (t.val : ℤ)) := by
    rw [← hk₂ i, ← zpow_natCast ggLieDT_zeta (k₂ i),
      ← zpow_natCast (ggLieDT_zeta ^ (k₂ i : ℤ)) (t.val)]
    exact (zpow_mul ggLieDT_zeta (k₂ i : ℤ) (t.val : ℤ)).symm
  have hexp : a₁ i ^ s.val * a₂ i ^ t.val = ggLieDT_zeta ^ A := by
    rw [h₁', h₂', ← zpow_add]
  rw [hexp]
  have hiff : ggLieDT_zeta ^ A = 1 ↔ (A : ZMod 3) = 0 := by
    rw [zpow_eq_one_iff_modEq, horder, Int.modEq_zero_iff_dvd]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd A 3).symm
  rw [hiff]
  have hcast : (A : ZMod 3) = s * (k₁ i : ZMod 3) + t * (k₂ i : ZMod 3) := by
    rw [hA]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  rw [hcast]

private theorem ggLieDT_closure_card_iff {τ : Tag}
    (a₁ a₂ : Fin τ.rank → GGLˣ) (k₁ k₂ : Fin τ.rank → ℕ)
    (horder : orderOf ggLieDT_zeta = 3)
    (hk₁ : ∀ i, ggLieDT_zeta ^ k₁ i = a₁ i)
    (hk₂ : ∀ i, ggLieDT_zeta ^ k₂ i = a₂ i)
    (ha₁ : a₁ ^ 3 = 1) (ha₂ : a₂ ^ 3 = 1) :
    Nat.card (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) = 3 ^ 2 ↔
      ∀ s t : ZMod 3,
        s • (fun i => (k₁ i : ZMod 3)) + t • (fun i => (k₂ i : ZMod 3)) = 0 →
          s = 0 ∧ t = 0 := by
  classical
  let c₁ : Fin τ.rank → ZMod 3 := fun i => (k₁ i : ZMod 3)
  let c₂ : Fin τ.rank → ZMod 3 := fun i => (k₂ i : ZMod 3)
  let φ : Multiplicative (ZMod 3 × ZMod 3) →* ModGL τ GGL := ggLieDT_pairHom a₁ a₂ ha₁ ha₂
  have hrange : φ.range = Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} := by
    apply le_antisymm
    · rintro x ⟨u, rfl⟩
      change rootDiagUnit τ (a₁ ^ (u.toAdd.1).val * a₂ ^ (u.toAdd.2).val) ∈
        Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}
      rw [rootDiagUnit_mul]
      exact Subgroup.mul_mem _
        (by rw [← rootDiagUnit_pow]
            exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (by rw [← rootDiagUnit_pow]
            exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · refine ⟨Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)), ?_⟩
        change rootDiagUnit τ
          (a₁ ^ ((Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3))).toAdd.1).val *
            a₂ ^ ((Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3))).toAdd.2).val) =
          rootDiagUnit τ a₁
        rw [toAdd_ofAdd]
        simp [ZMod.val_one, ZMod.val_zero]
      · refine ⟨Multiplicative.ofAdd ((0 : ZMod 3), (1 : ZMod 3)), ?_⟩
        change rootDiagUnit τ
          (a₁ ^ ((Multiplicative.ofAdd ((0 : ZMod 3), (1 : ZMod 3))).toAdd.1).val *
            a₂ ^ ((Multiplicative.ofAdd ((0 : ZMod 3), (1 : ZMod 3))).toAdd.2).val) =
          rootDiagUnit τ a₂
        rw [toAdd_ofAdd]
        simp [ZMod.val_one, ZMod.val_zero]
  have hker : ∀ s t : ZMod 3, φ (Multiplicative.ofAdd (s, t)) = 1 ↔ s • c₁ + t • c₂ = 0 := by
    intro s t
    have hφ : φ (Multiplicative.ofAdd (s, t)) = rootDiagUnit τ (a₁ ^ s.val * a₂ ^ t.val) := by
      change rootDiagUnit τ (a₁ ^ ((Multiplicative.ofAdd (s, t)).toAdd.1).val *
        a₂ ^ ((Multiplicative.ofAdd (s, t)).toAdd.2).val) =
        rootDiagUnit τ (a₁ ^ s.val * a₂ ^ t.val)
      rw [toAdd_ofAdd]
    rw [hφ, show (1 : ModGL τ GGL) = rootDiagUnit τ 1 from rootDiagUnit_one.symm,
      (rootDiagUnit_injective (K := GGL) (τ := τ)).eq_iff]
    rw [show (a₁ ^ s.val * a₂ ^ t.val = 1) ↔ ∀ i, a₁ i ^ s.val * a₂ i ^ t.val = 1 by
      simp [funext_iff, Pi.mul_apply, Pi.pow_apply]]
    rw [show (s • c₁ + t • c₂ = 0) ↔
        ∀ i, s * (k₁ i : ZMod 3) + t * (k₂ i : ZMod 3) = 0 by
      simp only [funext_iff, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, c₁, c₂]]
    exact forall_congr' fun i => ggLieDT_coord_eq_one_iff a₁ a₂ k₁ k₂ horder hk₁ hk₂ i s t
  have hker_all : (∀ u : Multiplicative (ZMod 3 × ZMod 3), φ u = 1 → u = 1) ↔
      ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0 := by
    constructor
    · intro h s t hst
      have h1 : φ (Multiplicative.ofAdd (s, t)) = 1 := (hker s t).2 hst
      have h2 : Multiplicative.ofAdd (s, t) = 1 := h _ h1
      rw [ofAdd_eq_one] at h2
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    · intro h u hu
      have hu' : φ (Multiplicative.ofAdd (u.toAdd.1, u.toAdd.2)) = 1 := hu
      rw [hker] at hu'
      obtain ⟨hs, ht⟩ := h _ _ hu'
      exact (toAdd_eq_zero).1 (Prod.ext hs ht)
  have hcard_dom : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
  have hker_card : Nat.card φ.ker *
      Nat.card (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) = 9 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hcard_dom, hrange] at h
    exact h
  constructor
  · intro hclosure
    have hker_one : Nat.card φ.ker = 1 := by
      have hc : Nat.card (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) = 9 := by
        rw [hclosure]
        norm_num
      rw [hc] at hker_card
      omega
    have hker_bot : φ.ker = ⊥ := (Subgroup.card_eq_one).1 hker_one
    have hall : ∀ u, φ u = 1 → u = 1 :=
      (injective_iff_map_eq_one φ).1 ((MonoidHom.ker_eq_bot_iff φ).1 hker_bot)
    exact hker_all.1 hall
  · intro hindep
    have hall : ∀ u, φ u = 1 → u = 1 := hker_all.2 hindep
    have hker_bot : φ.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff φ).2 ((injective_iff_map_eq_one φ).2 hall)
    have hker_one : Nat.card φ.ker = 1 := (Subgroup.card_eq_one).2 hker_bot
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    rw [hker_one] at hker_card
    omega

theorem ggLie_torus_dictionary
    {τ : Tag} (a₁ a₂ : Fin τ.rank → GGLˣ)
    (h₁ : ∀ i, a₁ i ^ 3 = 1) (h₂ : ∀ i, a₂ i ^ 3 = 1) :
    ∃ c₁ c₂ : Fin τ.rank → ZMod 3,
      (∀ γ, rootChar a₁ γ = 1 ↔ ggLiePair γ c₁ = 0) ∧
      (∀ γ, rootChar a₂ γ = 1 ↔ ggLiePair γ c₂ = 0) ∧
      (∀ γ γ', rootChar a₁ γ' = rootChar a₁ γ ^ 2 ↔ ggLiePair γ' c₁ = 2 * ggLiePair γ c₁) ∧
      (∀ γ γ', rootChar a₂ γ' = rootChar a₂ γ ^ 2 ↔ ggLiePair γ' c₂ = 2 * ggLiePair γ c₂) ∧
      (Nat.card (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) = 3 ^ 2 ↔
        ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0) := by
  classical
  have horder : orderOf ggLieDT_zeta = 3 := by
    show orderOf (ggZeta 3 Nat.prime_three (by norm_num)) = 3
    exact (exists_zeta GGL (p := 3) Nat.prime_three (by norm_num)).choose_spec
  obtain ⟨k₁, hk₁⟩ := ggLieDT_exists_exp (a := a₁) horder h₁
  obtain ⟨k₂, hk₂⟩ := ggLieDT_exists_exp (a := a₂) horder h₂
  have ha₁ : a₁ ^ 3 = 1 := by
    funext i
    simpa [Pi.pow_apply] using h₁ i
  have ha₂ : a₂ ^ 3 = 1 := by
    funext i
    simpa [Pi.pow_apply] using h₂ i
  refine ⟨fun i => (k₁ i : ZMod 3), fun i => (k₂ i : ZMod 3), ?_, ?_, ?_, ?_, ?_⟩
  · intro γ
    exact ggLieDT_rootChar_one_iff a₁ k₁ horder hk₁ γ
  · intro γ
    exact ggLieDT_rootChar_one_iff a₂ k₂ horder hk₂ γ
  · intro γ γ'
    exact ggLieDT_rootChar_pow_two_iff a₁ k₁ horder hk₁ γ γ'
  · intro γ γ'
    exact ggLieDT_rootChar_pow_two_iff a₂ k₂ horder hk₂ γ γ'
  · exact ggLieDT_closure_card_iff a₁ a₂ k₁ k₂ horder hk₁ hk₂ ha₁ ha₂

end CFSG.StandardType.LieCore
