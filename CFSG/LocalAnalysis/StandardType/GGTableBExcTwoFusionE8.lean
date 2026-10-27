module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc TableBExc.Three TableBExcTwo

namespace TableBExcTwoFusion

@[expose] def dotZ3 {n : ℕ} (v lam : Fin n → ZMod 3) : ZMod 3 := ∑ i, v i * lam i

theorem exists_functional_mem_of_card {n : ℕ} (hn : 1 ≤ n) (X : AddSubgroup (Fin n → ZMod 3))
    (hX : Nat.card X = 3 ^ (n - 1)) :
    ∃ lam : Fin n → ZMod 3, lam ≠ 0 ∧ ∀ w, dotZ3 w lam = 0 → w ∈ X := by
  classical
  have := Fact.mk Nat.prime_three
  have hidx : X.index = 3 := by
    have h := X.index_mul_card
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, hX] at h
    have hr : 3 ^ n = 3 * 3 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hr] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  have hQ : Nat.card ((Fin n → ZMod 3) ⧸ X) = 3 := hidx
  set e := addEquivOfPrimeCardEq (p := 3) hQ (Nat.card_zmod 3) with he
  set f : (Fin n → ZMod 3) →+ ZMod 3 := e.toAddMonoidHom.comp (QuotientAddGroup.mk' X) with hf
  have hker : ∀ w, f w = 0 ↔ w ∈ X := fun w => by
    rw [hf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  set lam : Fin n → ZMod 3 := fun i => f (Pi.single i 1) with hlam
  have hexp : ∀ w, f w = dotZ3 w lam := fun w => by
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (Pi.single i (w i) : Fin n → ZMod 3) = (w i).val • Pi.single i 1 := by
      rw [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [e1, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hlam0 : lam ≠ 0 := by
    intro h
    have htop : X = ⊤ := by
      ext w
      refine ⟨fun _ => AddSubgroup.mem_top w, fun _ => (hker w).mp ?_⟩
      rw [hexp, h]
      simp [dotZ3]
    rw [htop, AddSubgroup.index_top] at hidx
    omega
  exact ⟨lam, hlam0, fun w hw => (hker w).mp (by rw [hexp]; exact hw)⟩

section E8Checks

local instance tableBExcTwoFusionFactE8 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

local instance tableBExcTwoFusionNeZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def pairE8 : Fin 5 → (Fin 4 → ZMod 3) × (Fin 4 → ZMod 3) :=
  ![(![0, 0, 1, 0], ![0, 1, 0, 1]), (![0, 0, 1, 2], ![1, 2, 0, 2]),
    (![0, 1, 1, 0], ![1, 0, 1, 2]), (![0, 1, 2, 0], ![1, 0, 2, 0]),
    (![1, 1, 1, 0], ![0, 0, 0, 1])]

@[expose] def nfWordE8v (v : Fin 4 → ZMod 3) : List (Fin Tag.E8.rank) :=
  nfWordE8 (v 0).val (v 1).val (v 2).val (v 3).val

theorem covering_E8 : ∀ lam : Fin 4 → ZMod 3, lam ≠ 0 → ∃ k : Fin 3, ∃ j : Fin 5,
    dotZ3 (fun i => (pairE8 j).1 ((piE8 ^ (k : ℕ)).symm i)) lam = 0 ∧
      dotZ3 (fun i => (pairE8 j).2 ((piE8 ^ (k : ℕ)).symm i)) lam = 0 := by
  decide +kernel

theorem card_fix_pairE8 : ∀ j : Fin 5,
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8v (pairE8 j).1) x = x ∧
      torusWord .E8 3 (nfWordE8v (pairE8 j).2) x = x} ≤ 3 ^ (8 - 5) := by
  intro j
  fin_cases j
  · exact card_fix_two_torusWord_le (τ := .E8) _ _ ![(0, 0), (0, 1), (1, 0), (1, 4), (1, 5)]
      ![1, 3, 4, 6, 7] (by decide)
      ![![1, 0, 0, 2, 2], ![0, 1, 0, 1, 1], ![0, 2, 2, 0, 2], ![0, 1, 0, 2, 2], ![0, 0, 1, 0, 0]]
      (by decide +kernel)
  · exact card_fix_two_torusWord_le (τ := .E8) _ _ ![(0, 0), (0, 1), (0, 4), (0, 7), (1, 0)]
      ![0, 1, 3, 6, 7] (by decide)
      ![![2, 2, 2, 1, 2], ![2, 2, 1, 2, 0], ![0, 2, 0, 1, 0], ![0, 0, 0, 2, 0], ![1, 0, 1, 2, 0]]
      (by decide +kernel)
  · exact card_fix_two_torusWord_le (τ := .E8) _ _ ![(0, 0), (0, 1), (0, 4), (0, 5), (1, 0)]
      ![0, 1, 3, 4, 6] (by decide)
      ![![1, 2, 0, 0, 2], ![1, 0, 2, 2, 0], ![0, 1, 1, 1, 0], ![1, 2, 0, 2, 0], ![0, 1, 2, 2, 0]]
      (by decide +kernel)
  · exact card_fix_two_torusWord_le (τ := .E8) _ _ ![(0, 0), (0, 1), (0, 4), (0, 5), (1, 0)]
      ![0, 1, 3, 4, 6] (by decide)
      ![![1, 2, 1, 1, 2], ![2, 2, 2, 2, 0], ![0, 2, 1, 1, 0], ![1, 1, 0, 2, 0], ![0, 2, 2, 2, 0]]
      (by decide +kernel)
  · exact card_fix_d_u

theorem card_fix_gens_E8 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // ∀ t, torusWord .E8 3 (wordE8G t) x = x} ≤
      3 ^ (8 - 6) :=
  card_fix_words_le (τ := .E8) wordE8G ![(0, 0), (0, 2), (1, 4), (1, 5), (2, 0), (3, 0)]
    ![0, 1, 3, 4, 6, 7] (by decide)
    ![![1, 2, 0, 0, 0, 0], ![0, 0, 2, 2, 1, 0], ![2, 2, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0],
      ![2, 2, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1]]
    (by decide +kernel)

@[expose] def fixRootE8 : Fin 4 → Fin Tag.E8.rank → ℤ :=
  ![Pi.single 6 1, Pi.single 7 1, Pi.single 7 1, Pi.single 1 1]

theorem fixRootE8_isRoot (i : Fin 4) : IsRoot .E8 (fixRootE8 i) := by
  fin_cases i <;> exact IsRoot.basis _

theorem fix_root_E8 : ∀ i : Fin 4,
    torusWord .E8 3 (wordE8G i) (redMod .E8 3 (fixRootE8 i)) = redMod .E8 3 (fixRootE8 i) := by
  decide +kernel

theorem path_roots_E8 :
    (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) ∈ rootFinset .E8 ∧
      (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) ∈ rootFinset .E8 ∧
      (Pi.single 3 1 : Fin Tag.E8.rank → ℤ) ∈ rootFinset .E8 ∧
      (Pi.single 0 1 + Pi.single 2 1 : Fin Tag.E8.rank → ℤ) ∈ rootFinset .E8 ∧
      (Pi.single 2 1 + Pi.single 3 1 : Fin Tag.E8.rank → ℤ) ∈ rootFinset .E8 ∧
      (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 : Fin Tag.E8.rank → ℤ) ∈ rootFinset .E8 := by
  decide +kernel

theorem frameE8_reflections_single : ∀ j : Fin Tag.E8.rank,
    (List.ofFn frameE8Root).foldr (fun β u => u - corootPair β u • β)
      (Pi.single j 1 : Fin Tag.E8.rank → ℤ) = -Pi.single j 1 := by
  decide +kernel

end E8Checks

section E8Sylow

local instance tableBExcTwoFusionFactE8' : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem torusPerm_modelHomE8_single (i : Fin 4) (x : Fin Tag.E8.rank → ZMod 3) :
    torusPerm .E8 3 (modelHomE8 (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) x =
      torusWord .E8 3 (wordE8G i) x := by
  rw [torusPerm_apply, torusWord_eq_torusAct cartan_symm_E8, modelHomE8, modelHom_inl,
    modelN_single, ZMod.val_one, pow_one]
  rfl

theorem torusPerm_modelHomE8_inl (v : Fin 4 → ZMod 3) (x : Fin Tag.E8.rank → ZMod 3) :
    torusPerm .E8 3 (modelHomE8 (SemidirectProduct.inl (.ofAdd v))) x =
      torusWord .E8 3 (nfWordE8v v) x := by
  rw [torusPerm_apply, modelHomE8_inl, ← torusWord_eq_torusAct cartan_symm_E8]
  rfl

theorem fix_N_E8_two : Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
    ∀ v, torusPerm .E8 3 (modelHomE8 (SemidirectProduct.inl v)) x = x} ≤ 3 ^ 2 :=
  le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1, fun t => (torusPerm_modelHomE8_single t x.1).symm.trans (x.2 _)⟩ :
      {x : Fin Tag.E8.rank → ZMod 3 // ∀ t, torusWord .E8 3 (wordE8G t) x = x}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) card_fix_gens_E8

theorem shiftAut_vec1110_E8 :
    shiftAut piE8 (.ofAdd ![1, 1, 1, 0] : Multiplicative (Fin 4 → ZMod 3)) = .ofAdd ![1, 1, 1, 0] := by
  decide +kernel

theorem shiftAut_vec0001_E8 :
    shiftAut piE8 (.ofAdd ![0, 0, 0, 1] : Multiplicative (Fin 4 → ZMod 3)) = .ofAdd ![0, 0, 0, 1] := by
  decide +kernel

theorem fix_centN_E8 : Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
    ∀ w : Multiplicative (Fin 4 → ZMod 3), shiftAut piE8 w = w →
      torusPerm .E8 3 (modelHomE8 (SemidirectProduct.inl w)) x = x} ≤ 3 ^ 3 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1, (torusPerm_modelHomE8_inl ![1, 1, 1, 0] x.1).symm.trans
        (x.2 _ shiftAut_vec1110_E8), (torusPerm_modelHomE8_inl ![0, 0, 0, 1] x.1).symm.trans
        (x.2 _ shiftAut_vec0001_E8)⟩ : {x : Fin Tag.E8.rank → ZMod 3 //
      torusWord .E8 3 (nfWordE8v ![1, 1, 1, 0]) x = x ∧
        torusWord .E8 3 (nfWordE8v ![0, 0, 0, 1]) x = x}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) ?_
  exact card_fix_d_u

section Conj

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {hπ : π ^ 3 = 1} {M : Type*} [Group M] {V : Type*}
  (ρ : M →* Equiv.Perm V) (F : Model π hπ →* M)

theorem card_fix_two_conj (z u v : Model π hπ) :
    Nat.card {x : V // ρ (F (z * u * z⁻¹)) x = x ∧ ρ (F (z * v * z⁻¹)) x = x} =
      Nat.card {x : V // ρ (F u) x = x ∧ ρ (F v) x = x} := by
  have key : ∀ (x : V) (y : Model π hπ), ρ (F (z * y * z⁻¹)) x = x ↔
      ρ (F y) ((ρ (F z))⁻¹ x) = (ρ (F z))⁻¹ x := fun x y => by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, perm_conj_apply_eq_iff]
  exact Nat.card_congr
    { toFun := fun x => ⟨(ρ (F z))⁻¹ x.1, (key x.1 u).mp x.2.1, (key x.1 v).mp x.2.2⟩
      invFun := fun x => ⟨ρ (F z) x.1, (key _ u).mpr (by simpa using x.2.1),
        (key _ v).mpr (by simpa using x.2.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

end Conj

theorem fix_hyperplane_E8 (A : Subgroup (Model piE8 piE8_pow_three)) (hI : ∀ y ∈ A, y.right = 1)
    (h27 : Nat.card A = 27) : fixAllCard (torusPerm .E8 3) modelHomE8 A ≤ 3 ^ 3 := by
  classical
  let A' : AddSubgroup (Fin 4 → ZMod 3) :=
    { carrier := {w | (SemidirectProduct.inl (.ofAdd w) : Model piE8 piE8_pow_three) ∈ A}
      add_mem' := fun {a b} ha hb => by
        show SemidirectProduct.inl (Multiplicative.ofAdd (a + b)) ∈ A
        rw [ofAdd_add, map_mul]
        exact mul_mem ha hb
      zero_mem' := by
        show SemidirectProduct.inl (Multiplicative.ofAdd 0) ∈ A
        rw [ofAdd_zero, map_one]
        exact one_mem A
      neg_mem' := fun {a} ha => by
        show SemidirectProduct.inl (Multiplicative.ofAdd (-a)) ∈ A
        have h := inv_mem (show SemidirectProduct.inl (Multiplicative.ofAdd a) ∈ A from ha)
        rw [← map_inv] at h
        exact h }
  have hcard' : Nat.card A' = 3 ^ (4 - 1) := by
    rw [show (3 : ℕ) ^ (4 - 1) = 27 by norm_num, ← h27]
    refine Nat.card_congr (Equiv.ofBijective (fun w => (⟨_, w.2⟩ : A)) ⟨fun a b hab => ?_,
      fun y => ?_⟩)
    · have h := congrArg (fun y : A => (y : Model piE8 piE8_pow_three).left) hab
      exact Subtype.ext (Multiplicative.ofAdd.injective h)
    · refine ⟨⟨Multiplicative.toAdd (y : Model piE8 piE8_pow_three).left, ?_⟩, ?_⟩
      · show SemidirectProduct.inl (Multiplicative.ofAdd _) ∈ A
        rw [ofAdd_toAdd, ← eq_inl_of_right_eq_one (hI _ y.2)]
        exact y.2
      · exact Subtype.ext (by
          show SemidirectProduct.inl (Multiplicative.ofAdd _) = _
          rw [ofAdd_toAdd, ← eq_inl_of_right_eq_one (hI _ y.2)])
  obtain ⟨lam, hlam0, hmem⟩ := exists_functional_mem_of_card (by norm_num) A' hcard'
  obtain ⟨k, j, hx, hy⟩ := covering_E8 lam hlam0
  have hrot : ∀ w : Fin 4 → ZMod 3, (SemidirectProduct.inl (.ofAdd fun i => w ((piE8 ^ (k : ℕ)).symm i)) :
      Model piE8 piE8_pow_three) = SemidirectProduct.inr (.ofAdd ((k : ℕ) : ZMod 3)) *
        SemidirectProduct.inl (.ofAdd w) * (SemidirectProduct.inr (.ofAdd ((k : ℕ) : ZMod 3)))⁻¹ := by
    intro w
    rw [inr_conj_inl]
    congr 1
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_shiftAut_pow]
    rfl
  have hxA := hmem _ hx
  have hyA := hmem _ hy
  change SemidirectProduct.inl _ ∈ A at hxA hyA
  rw [hrot] at hxA hyA
  set z := (SemidirectProduct.inr (.ofAdd ((k : ℕ) : ZMod 3)) : Model piE8 piE8_pow_three)
  calc fixAllCard (torusPerm .E8 3) modelHomE8 A
      ≤ Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
          torusPerm .E8 3 (modelHomE8 (z * SemidirectProduct.inl (.ofAdd (pairE8 j).1) * z⁻¹)) x =
            x ∧
          torusPerm .E8 3 (modelHomE8 (z * SemidirectProduct.inl (.ofAdd (pairE8 j).2) * z⁻¹)) x =
            x} :=
        Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2 _ hxA, x.2 _ hyA⟩)
          fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
    _ = Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
          torusWord .E8 3 (nfWordE8v (pairE8 j).1) x = x ∧
            torusWord .E8 3 (nfWordE8v (pairE8 j).2) x = x} := by
        rw [card_fix_two_conj]
        refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
        rw [torusPerm_modelHomE8_inl, torusPerm_modelHomE8_inl]
    _ ≤ 3 ^ 3 := card_fix_pairE8 j

theorem caseII_E8 (A : Subgroup (Model piE8 piE8_pow_three)) (hI : ∀ y ∈ A, y.right = 1)
    (_hA3 : ∀ y ∈ A, y ^ 3 = 1) (_hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    (hII : ∃ y ∈ A, 2 ≤ (supp y.left).card) :
    Nat.card A * fixAllCard (torusPerm .E8 3) modelHomE8 A < 3 ^ 7 := by
  have := finite_model (π := piE8) (hπ := piE8_pow_three)
  obtain ⟨y, hyA, hy2⟩ := hII
  set Ninl := (SemidirectProduct.inl : Multiplicative (Fin 4 → ZMod 3) →*
    Model piE8 piE8_pow_three).range with hNinl
  have hAN : A ≤ Ninl := fun z hz => ⟨z.left, (eq_inl_of_right_eq_one (hI z hz)).symm⟩
  have hdvd : Nat.card A ∣ 3 ^ 4 := card_range_inl (π := piE8) (hπ := piE8_pow_three) ▸
    Subgroup.card_dvd_of_le hAN
  have hfix4 : fixAllCard (torusPerm .E8 3) modelHomE8 A ≤ 3 ^ 4 := by
    refine le_trans (fixAllCard_le _ _ hyA) ?_
    rw [eq_inl_of_right_eq_one (hI y hyA)]
    exact fix_supp_E8 _ hy2
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  ·
    exfalso
    have h1 : A = ⊥ := (Subgroup.card_eq_one).mp (by rw [hk']; rfl)
    have hy1 : y = 1 := by
      have : y ∈ (⊥ : Subgroup (Model piE8 piE8_pow_three)) := h1 ▸ hyA
      exact Subgroup.mem_bot.mp this
    rw [hy1] at hy2
    simp [supp] at hy2
  · rw [hk']
    calc 3 ^ 1 * fixAllCard (torusPerm .E8 3) modelHomE8 A ≤ 3 ^ 1 * 3 ^ 4 :=
          Nat.mul_le_mul_left _ hfix4
      _ < 3 ^ 7 := by norm_num
  · rw [hk']
    calc 3 ^ 2 * fixAllCard (torusPerm .E8 3) modelHomE8 A ≤ 3 ^ 2 * 3 ^ 4 :=
          Nat.mul_le_mul_left _ hfix4
      _ < 3 ^ 7 := by norm_num
  · rw [hk']
    calc 3 ^ 3 * fixAllCard (torusPerm .E8 3) modelHomE8 A ≤ 3 ^ 3 * 3 ^ 3 :=
          Nat.mul_le_mul_left _ (fix_hyperplane_E8 A hI hk')
      _ < 3 ^ 7 := by norm_num
  · have hfull : A = Ninl := Subgroup.eq_of_le_of_card_ge hAN (by rw [hk', card_range_inl])
    have hfix : fixAllCard (torusPerm .E8 3) modelHomE8 A ≤ 3 ^ 2 := by
      refine le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)) fix_N_E8_two
      rw [hfull]
      constructor
      · intro h v
        exact h _ ⟨v, rfl⟩
      · rintro h _ ⟨v, rfl⟩
        exact h v
    rw [hk']
    calc 3 ^ 4 * fixAllCard (torusPerm .E8 3) modelHomE8 A ≤ 3 ^ 4 * 3 ^ 2 :=
          Nat.mul_le_mul_left _ hfix
      _ < 3 ^ 7 := by norm_num

theorem noOffenderRoot_E8 (A : Subgroup (WeylGroup .E8)) (hAS : A ≤ modelHomE8.range)
    (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : Fin Tag.E8.rank → ZMod 3 // ∀ a ∈ A, torusAct .E8 3 a x = x} <
        3 ^ 7 ∨
      (Nat.card A * Nat.card {x : Fin Tag.E8.rank → ZMod 3 // ∀ a ∈ A, torusAct .E8 3 a x = x} ≤
          3 ^ 7 ∧ ∃ x ∈ rootModSet .E8, ∀ a ∈ A, torusAct .E8 3 a x = x) := by
  have hkey := card_mul_card_fix_lt_or_single_of_model (torusPerm .E8 3) modelHomE8
    modelHomE8_injective (T := 3 ^ 7)
    (fun _ h3 hc h1 => card_mul_fixAllCard_lt_or_single (T := 3 ^ 7) (B₁ := 3 ^ 4) (B₅ := 3 ^ 3)
      (m := 2) (torusPerm .E8 3) modelHomE8 fix_caseI_E8 card_fixShift_E8 fix_centN_E8 caseII_E8
      (by norm_num) (by norm_num) h3 hc h1) hAS hA hA1
  simp only [torusPerm_apply] at hkey
  rcases hkey with h | ⟨i, h1, h2, h3⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, redMod .E8 3 (fixRootE8 i), ⟨_, fixRootE8_isRoot i, rfl⟩, ?_⟩
    · have h4 := (h2.trans (fix_single_E8 i))
      calc Nat.card A * Nat.card {x : Fin Tag.E8.rank → ZMod 3 // ∀ a ∈ A, torusAct .E8 3 a x = x}
          ≤ 3 * 3 ^ 6 := Nat.mul_le_mul h1 h4
        _ = 3 ^ 7 := by norm_num
    · refine h3 _ ?_
      rw [← torusPerm_apply, torusPerm_modelHomE8_single]
      exact fix_root_E8 i

end E8Sylow

section E8Assembly

theorem exists_root_mem_E8 (X : AddSubgroup (Fin Tag.E8.rank → ZMod 3)) (hX : 3 ^ 7 ≤ Nat.card X) :
    ∃ x ∈ rootModSet .E8, x ∈ X := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := path_roots_E8
  obtain ⟨δ, hδ, hδX⟩ := exists_isRoot_redMod_mem (mem_rootFinset.1 h1) (mem_rootFinset.1 h2)
    (mem_rootFinset.1 h3) (mem_rootFinset.1 h4) (mem_rootFinset.1 h5) (mem_rootFinset.1 h6)
    (index_le_three_of_card (r := Tag.E8.rank) hX (by decide))
  exact ⟨_, ⟨δ, hδ, rfl⟩, hδX⟩

theorem frameE8_reflections (v : Fin Tag.E8.rank → ℤ) :
    (List.ofFn fun i => rootReflection (frameE8.root i)).prod • v = -v := by
  refine smul_eq_neg_of_single (fun j => ?_) v
  have e : (List.ofFn fun i => rootReflection (frameE8.root i)) =
      (List.ofFn frameE8Root).map rootReflection := by
    rw [List.map_ofFn]
    rfl
  rw [e, list_map_rootReflection_prod_smul _ (fun β hβ => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hβ
      exact frameE8.isRoot i)]
  exact frameE8_reflections_single j


theorem exists_conj_mem_highRootSL2_E8 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .E8 K)} (hA : IsElemAbelian 3 A)
    (h7 : 3 ^ 7 ≤ Nat.card A) :
    ∃ t ∈ A, t ≠ 1 ∧ ∃ g : adjointGroup .E8 K,
      g * t * g⁻¹ ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E8 K).subgroupOf
        (adjointGroup .E8 K) := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  have hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E8 (by norm_num)
  have hV := card_torusPow_E8 (K := FiniteField.Extension K 2 2) Nat.prime_three h3
  refine exists_conj_mem_highRootSL2_of_weylX (Or.inr rfl) frameE8 rfl frameE8_reflections
    cartan_symm_E8 hdet hV (not_three_dvd_index_E8 h3) (T := 3 ^ 7) ?_ hK hA h7
  intro ζ hζo hζ E hE hEX hT
  obtain ⟨x, ⟨β, hβ, rfl⟩, hxE⟩ := exists_mem_torusSet_of_le_weylX Nat.prime_three hdet hV
    cartan_symm_E8 hζo hζ (Good := rootModSet .E8) noOffenderRoot_E8 exists_root_mem_E8 hE hEX hT
  exact ⟨β, hβ, hxE⟩

end E8Assembly

end TableBExcTwoFusion

theorem ggE8TwoRootFusionInput_holds :
    TableBExcTwo.GGE8TwoRootFusionInput :=
  fun _ _ _ _ hK _ hA h7 => TableBExcTwoFusion.exists_conj_mem_highRootSL2_E8 hK hA h7

end CFSG.StandardType
