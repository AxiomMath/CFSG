module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionKey
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc TableBExc.Three TableBExcTwo

namespace TableBExcTwoFusion

theorem card_fix_words_le {τ : Tag} {p : ℕ} [Fact p.Prime] {m : ℕ} (ws : Fin m → List (Fin τ.rank))
    {k : ℕ} (R : Fin k → Fin m × Fin τ.rank) (C : Fin k → Fin τ.rank) (hC : Function.Injective C)
    (N : Fin k → Fin k → ZMod p)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (torusWord τ p (ws (R c).1) (Pi.single (C b) 1)
      (R c).2 - if (R c).2 = C b then 1 else 0) = if a = b then 1 else 0) :
    Nat.card {x : Fin τ.rank → ZMod p // ∀ t, torusWord τ p (ws t) x = x} ≤ p ^ (τ.rank - k) := by
  have h := card_fixAll_le_of_leftInverse (fun t => torusWordLin τ p (ws t)) R C hC N
    (by simpa only [torusWordLin_apply] using hN)
  simp only [torusWordLin_apply, ZMod.card] at h
  exact h

theorem list_map_rootReflection_prod_smul {τ : Tag}
    (l : List (Fin τ.rank → ℤ)) (hl : ∀ β ∈ l, IsRoot τ β)
    (v : Fin τ.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr (fun β u => u - corootPair β u • β) v := by
  induction l with
  | nil => simp
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
      rootReflection_smul (hl β List.mem_cons_self), List.foldr_cons]

theorem smul_eq_neg_of_single {τ : Tag} {w : WeylGroup τ}
    (h : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1) (v : Fin τ.rank → ℤ) :
    w • v = -v := by
  have hlin : CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, ← smul_def, h i]
    simp
  rw [smul_def, hlin]
  simp

section E7Checks

local instance tableBExcTwoFusionFactE7 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

local instance tableBExcTwoFusionNeZeroRankE7 : NeZero Tag.E7.rank := ⟨by decide⟩

theorem card_fix_nfWordE7_110_three :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 (nfWordE7 1 1 0) x = x} ≤
      3 ^ (7 - 4) :=
  card_fix_torusWord_le (τ := .E7) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 1, 0], ![2, 2, 1, 1]] (by decide +kernel)

theorem card_fix_nfWordE7_120_three :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 (nfWordE7 1 2 0) x = x} ≤
      3 ^ (7 - 4) :=
  card_fix_torusWord_le (τ := .E7) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 1, 2], ![2, 2, 2, 2]] (by decide +kernel)

theorem card_fix_nfWordE7_112_three :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 (nfWordE7 1 1 2) x = x} ≤
      3 ^ (7 - 4) :=
  card_fix_torusWord_le (τ := .E7) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![0, 0, 1, 2], ![2, 1, 2, 1], ![2, 0, 2, 0], ![1, 1, 1, 0]] (by decide +kernel)

theorem card_fix_gens_E7 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // ∀ t, torusWord .E7 3 (wordE7G t) x = x} ≤
      3 ^ (7 - 5) :=
  card_fix_words_le (τ := .E7) wordE7G ![(0, 0), (0, 2), (1, 4), (1, 5), (2, 0)]
    ![0, 1, 3, 4, 6] (by decide)
    ![![1, 2, 0, 0, 0], ![0, 0, 2, 2, 1], ![2, 2, 0, 0, 0], ![1, 1, 1, 0, 0], ![2, 2, 1, 1, 0]]
    (by decide +kernel)

@[expose] def fixRootE7 : Fin 3 → Fin Tag.E7.rank → ℤ :=
  ![Pi.single 4 1, Pi.single 0 1, Pi.single 4 1]

theorem fixRootE7_isRoot (i : Fin 3) : IsRoot .E7 (fixRootE7 i) := by
  fin_cases i <;> exact IsRoot.basis _

theorem fix_root_E7 : ∀ i : Fin 3,
    torusWord .E7 3 (wordE7G i) (redMod .E7 3 (fixRootE7 i)) = redMod .E7 3 (fixRootE7 i) := by
  decide +kernel

theorem path_roots_E7 :
    (Pi.single 0 1 : Fin Tag.E7.rank → ℤ) ∈ rootFinset .E7 ∧
      (Pi.single 2 1 : Fin Tag.E7.rank → ℤ) ∈ rootFinset .E7 ∧
      (Pi.single 3 1 : Fin Tag.E7.rank → ℤ) ∈ rootFinset .E7 ∧
      (Pi.single 0 1 + Pi.single 2 1 : Fin Tag.E7.rank → ℤ) ∈ rootFinset .E7 ∧
      (Pi.single 2 1 + Pi.single 3 1 : Fin Tag.E7.rank → ℤ) ∈ rootFinset .E7 ∧
      (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 : Fin Tag.E7.rank → ℤ) ∈ rootFinset .E7 := by
  decide +kernel

theorem frameE7_reflections_single : ∀ j : Fin Tag.E7.rank,
    (List.ofFn frameE7Root).foldr (fun β u => u - corootPair β u • β)
      (Pi.single j 1 : Fin Tag.E7.rank → ℤ) = -Pi.single j 1 := by
  decide +kernel

end E7Checks

@[expose] def rootModSet (τ : Tag) : Set (Fin τ.rank → ZMod 3) :=
  {x | ∃ β, IsRoot τ β ∧ redMod τ 3 β = x}

section E7Sylow

local instance tableBExcTwoFusionFactE7' : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem fix_supp_E7_three (v : Multiplicative (Fin 3 → ZMod 3)) (hv : 2 ≤ (supp v).card) :
    fixCard (torusPerm .E7 3) modelHomE7 (SemidirectProduct.inl v) ≤ 3 ^ 3 := by
  rw [eq_ofAdd_vec3 v] at hv ⊢
  obtain ⟨k, e, he⟩ := exists_rep_E7 _ _ _ hv
  refine fixCard_inl_le_of_rot _ _ k ((e : ℕ) + 1) (by omega) ?_
  have hrep : ∀ r ∈ ({.ofAdd ![1, 1, 0], .ofAdd ![1, 2, 0], .ofAdd ![1, 1, 2],
      .ofAdd ![1, 1, 1]} : Finset (Multiplicative (Fin 3 → ZMod 3))),
      fixCard (torusPerm .E7 3) modelHomE7 (SemidirectProduct.inl r) ≤ 3 ^ 3 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 1 0) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_110_three
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 2 0) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_120_three
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 1 2) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_112_three
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 1 1) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_111
  exact hrep _ he

theorem torusPerm_modelHomE7_single (i : Fin 3) (x : Fin Tag.E7.rank → ZMod 3) :
    torusPerm .E7 3 (modelHomE7 (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) x =
      torusWord .E7 3 (wordE7G i) x := by
  rw [torusPerm_apply, torusWord_eq_torusAct cartan_symm_E7, modelHomE7, modelHom_inl,
    modelN_single, ZMod.val_one, pow_one]
  rfl

theorem fix_N_E7_two : Nat.card {x : Fin Tag.E7.rank → ZMod 3 //
    ∀ v, torusPerm .E7 3 (modelHomE7 (SemidirectProduct.inl v)) x = x} ≤ 3 ^ 2 :=
  le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1, fun t => (torusPerm_modelHomE7_single t x.1).symm.trans (x.2 _)⟩ :
      {x : Fin Tag.E7.rank → ZMod 3 // ∀ t, torusWord .E7 3 (wordE7G t) x = x}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) card_fix_gens_E7

theorem shiftAut_vec111_E7 :
    shiftAut piE7 (.ofAdd ![1, 1, 1] : Multiplicative (Fin 3 → ZMod 3)) = .ofAdd ![1, 1, 1] := by
  decide +kernel

theorem fix_centN_E7 : Nat.card {x : Fin Tag.E7.rank → ZMod 3 //
    ∀ w : Multiplicative (Fin 3 → ZMod 3), shiftAut piE7 w = w →
      torusPerm .E7 3 (modelHomE7 (SemidirectProduct.inl w)) x = x} ≤ 3 ^ 3 := by
  have h1 : ∀ x : Fin Tag.E7.rank → ZMod 3,
      torusPerm .E7 3 (modelHomE7 (SemidirectProduct.inl (.ofAdd ![1, 1, 1]))) x = x ↔
        torusWord .E7 3 (nfWordE7 1 1 1) x = x := fun x => by
    rw [torusPerm_apply, modelHomE7_inl, ← torusWord_eq_torusAct cartan_symm_E7]
    rfl
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1, (h1 x.1).mp (x.2 _ shiftAut_vec111_E7)⟩ : {x : Fin Tag.E7.rank → ZMod 3 //
      torusWord .E7 3 (nfWordE7 1 1 1) x = x}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) ?_
  exact card_fix_nfWordE7_111

theorem caseII_E7 (A : Subgroup (Model piE7 piE7_pow_three)) (hI : ∀ y ∈ A, y.right = 1)
    (_hA3 : ∀ y ∈ A, y ^ 3 = 1) (_hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    (hII : ∃ y ∈ A, 2 ≤ (supp y.left).card) :
    Nat.card A * fixAllCard (torusPerm .E7 3) modelHomE7 A < 3 ^ 6 := by
  have := finite_model (π := piE7) (hπ := piE7_pow_three)
  obtain ⟨y, hyA, hy2⟩ := hII
  set Ninl := (SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 3) →*
    Model piE7 piE7_pow_three).range with hNinl
  have hAN : A ≤ Ninl := fun z hz => ⟨z.left, (eq_inl_of_right_eq_one (hI z hz)).symm⟩
  by_cases hfull : A = Ninl
  · have hcard : Nat.card A = 3 ^ 3 := by rw [hfull, card_range_inl]
    have hfix : fixAllCard (torusPerm .E7 3) modelHomE7 A ≤ 3 ^ 2 := by
      refine le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)) fix_N_E7_two
      rw [hfull]
      constructor
      · intro h v
        exact h _ ⟨v, rfl⟩
      · rintro h _ ⟨v, rfl⟩
        exact h v
    calc Nat.card A * fixAllCard (torusPerm .E7 3) modelHomE7 A ≤ 3 ^ 3 * 3 ^ 2 :=
          by rw [hcard]; exact Nat.mul_le_mul_left _ hfix
      _ < 3 ^ 6 := by norm_num
  · have hdvd : Nat.card A ∣ 3 ^ 3 := card_range_inl (π := piE7) (hπ := piE7_pow_three) ▸
      Subgroup.card_dvd_of_le hAN
    have hne : Nat.card A ≠ 3 ^ 3 := fun h => hfull
      (Subgroup.eq_of_le_of_card_ge hAN (by rw [h, card_range_inl]))
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk2 : Nat.card A ≤ 3 ^ 2 := by
      have hkn : k ≤ 2 := by
        by_contra hcon
        exact hne (by rw [hk', show k = 3 by omega])
      rw [hk']
      exact Nat.pow_le_pow_right (by norm_num) hkn
    have hfix : fixAllCard (torusPerm .E7 3) modelHomE7 A ≤ 3 ^ 3 := by
      refine le_trans (fixAllCard_le _ _ hyA) ?_
      rw [eq_inl_of_right_eq_one (hI y hyA)]
      exact fix_supp_E7_three _ hy2
    calc Nat.card A * fixAllCard (torusPerm .E7 3) modelHomE7 A ≤ 3 ^ 2 * 3 ^ 3 :=
          Nat.mul_le_mul hk2 hfix
      _ < 3 ^ 6 := by norm_num

theorem noOffenderRoot_E7 (A : Subgroup (WeylGroup .E7)) (hAS : A ≤ modelHomE7.range)
    (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : Fin Tag.E7.rank → ZMod 3 // ∀ a ∈ A, torusAct .E7 3 a x = x} <
        3 ^ 6 ∨
      (Nat.card A * Nat.card {x : Fin Tag.E7.rank → ZMod 3 // ∀ a ∈ A, torusAct .E7 3 a x = x} ≤
          3 ^ 6 ∧ ∃ x ∈ rootModSet .E7, ∀ a ∈ A, torusAct .E7 3 a x = x) := by
  have hkey := card_mul_card_fix_lt_or_single_of_model (torusPerm .E7 3) modelHomE7
    modelHomE7_injective (T := 3 ^ 6)
    (fun _ h3 hc h1 => card_mul_fixAllCard_lt_or_single (T := 3 ^ 6) (B₁ := 3 ^ 4) (B₅ := 3 ^ 3)
      (m := 1) (torusPerm .E7 3) modelHomE7 fix_caseI_E7 card_fixShift_E7 fix_centN_E7 caseII_E7
      (by norm_num) (by norm_num) h3 hc h1) hAS hA hA1
  simp only [torusPerm_apply] at hkey
  rcases hkey with h | ⟨i, h1, h2, h3⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, redMod .E7 3 (fixRootE7 i), ⟨_, fixRootE7_isRoot i, rfl⟩, ?_⟩
    · have h4 := (h2.trans (fix_single_E7 i))
      calc Nat.card A * Nat.card {x : Fin Tag.E7.rank → ZMod 3 // ∀ a ∈ A, torusAct .E7 3 a x = x}
          ≤ 3 * 3 ^ 5 := Nat.mul_le_mul h1 h4
        _ = 3 ^ 6 := by norm_num
    · refine h3 _ ?_
      rw [← torusPerm_apply, torusPerm_modelHomE7_single]
      exact fix_root_E7 i

end E7Sylow

section E7Assembly

theorem exists_root_mem_E7 (X : AddSubgroup (Fin Tag.E7.rank → ZMod 3)) (hX : 3 ^ 6 ≤ Nat.card X) :
    ∃ x ∈ rootModSet .E7, x ∈ X := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := path_roots_E7
  obtain ⟨δ, hδ, hδX⟩ := exists_isRoot_redMod_mem (mem_rootFinset.1 h1) (mem_rootFinset.1 h2)
    (mem_rootFinset.1 h3) (mem_rootFinset.1 h4) (mem_rootFinset.1 h5) (mem_rootFinset.1 h6)
    (index_le_three_of_card (r := Tag.E7.rank) hX (by decide))
  exact ⟨_, ⟨δ, hδ, rfl⟩, hδX⟩

theorem frameE7_reflections (v : Fin Tag.E7.rank → ℤ) :
    (List.ofFn fun i => rootReflection (frameE7.root i)).prod • v = -v := by
  refine smul_eq_neg_of_single (fun j => ?_) v
  have e : (List.ofFn fun i => rootReflection (frameE7.root i)) =
      (List.ofFn frameE7Root).map rootReflection := by
    rw [List.map_ofFn]
    rfl
  rw [e, list_map_rootReflection_prod_smul _ (fun β hβ => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hβ
      exact frameE7.isRoot i)]
  exact frameE7_reflections_single j


theorem exists_conj_mem_highRootSL2_E7 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .E7 K)} (hA : IsElemAbelian 3 A)
    (h6 : 3 ^ 6 ≤ Nat.card A) :
    ∃ t ∈ A, t ≠ 1 ∧ ∃ g : adjointGroup .E7 K,
      g * t * g⁻¹ ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf
        (adjointGroup .E7 K) := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  have hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E7 (by norm_num)
  have hV := card_torusPow_E7 (K := FiniteField.Extension K 2 2) Nat.prime_three h3
  refine exists_conj_mem_highRootSL2_of_weylX (Or.inl rfl) frameE7 rfl frameE7_reflections
    cartan_symm_E7 hdet hV (not_three_dvd_index_E7 h3) (T := 3 ^ 6) ?_ hK hA h6
  intro ζ hζo hζ E hE hEX hT
  obtain ⟨x, ⟨β, hβ, rfl⟩, hxE⟩ := exists_mem_torusSet_of_le_weylX Nat.prime_three hdet hV
    cartan_symm_E7 hζo hζ (Good := rootModSet .E7) noOffenderRoot_E7 exists_root_mem_E7 hE hEX hT
  exact ⟨β, hβ, hxE⟩

end E7Assembly

end TableBExcTwoFusion

theorem ggE7TwoRootFusionInput_holds :
    TableBExcTwo.GGE7TwoRootFusionInput :=
  fun _ _ _ _ hK _ hA h6 => TableBExcTwoFusion.exists_conj_mem_highRootSL2_E7 hK hA h6

end CFSG.StandardType
