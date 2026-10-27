module

public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal

public section

namespace CFSG.Quasithin.H13.KGInspOdd

open scoped MatrixGroups commutatorElement
open CFSG.Open (pCoreOf IsElemAbelian)

variable {F : Type} [Field F]

@[expose] noncomputable def projSL2 : SL(2, F) →* PSL(2, F) :=
  QuotientGroup.mk' (Subgroup.center SL(2, F))

theorem ker_projSL2 : (projSL2 (F := F)).ker = Subgroup.center SL(2, F) :=
  QuotientGroup.ker_mk' _

theorem projSL2_surjective : Function.Surjective (projSL2 (F := F)) :=
  QuotientGroup.mk'_surjective _

theorem center_le_zpowers : Subgroup.center SL(2, F) ≤ Subgroup.zpowers (-1 : SL(2, F)) := by
  intro A hA
  rcases CFSG.GH74.KGroups.L3Eps.sl2c_center_eq hA with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

theorem neg_one_mem_center : (-1 : SL(2, F)) ∈ Subgroup.center SL(2, F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [neg_one_mul, mul_neg_one]

theorem zpowers_le_center : Subgroup.zpowers (-1 : SL(2, F)) ≤ Subgroup.center SL(2, F) :=
  (Subgroup.zpowers_le).mpr neg_one_mem_center

theorem neg_one_sq : (-1 : SL(2, F)) ^ 2 = 1 := by
  rw [sq, neg_one_mul, neg_neg]

theorem center_sl2_two {F' : Type} [Field F'] [CharP F' 2] : Subgroup.center SL(2, F') = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F') = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linear_combination this - h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

@[expose] def upperSL (a : F) : SL(2, F) :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem upperSL_mul (a b : F) : upperSL a * upperSL b = upperSL (a + b) := by
  refine Subtype.ext ?_
  change (!![1, a; 0, 1] * !![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, a + b; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem upperSL_zero : upperSL (0 : F) = 1 := by
  refine Subtype.ext ?_
  change (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1
  exact (Matrix.one_fin_two).symm

@[expose] def upperHom : Multiplicative F →* SL(2, F) where
  toFun a := upperSL (Multiplicative.toAdd a)
  map_one' := upperSL_zero
  map_mul' _ _ := (upperSL_mul _ _).symm

theorem upperHom_injective : Function.Injective (upperHom (F := F)) := by
  intro a b h
  have h' : upperSL (Multiplicative.toAdd a) = upperSL (Multiplicative.toAdd b) := h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h'
  exact Multiplicative.toAdd.injective (by simpa [upperSL] using this)

theorem upper_elem {F' : Type} [Field F'] [Finite F'] [CharP F' 2] :
    IsElemAbelian 2 (upperHom (F := F')).range ∧
      Nat.card (upperHom (F := F')).range = Nat.card F' := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨x, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, sq]
    have : x * x = 1 := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_one]
      have h2 : (2 : F') = 0 := CharTwo.two_eq_zero
      linear_combination (Multiplicative.toAdd x) * h2
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective (upperHom_injective (F := F'))).toEquiv.symm]
    exact Nat.card_congr Multiplicative.toAdd

section Perfect

variable [Finite F] {K : Subgroup SL(2, F)}

theorem neg_one_mem (hF : ringChar F ≠ 2) (h2 : 2 ∣ Nat.card K) : (-1 : SL(2, F)) ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2
  have hk2 : (k : SL(2, F)) * k = 1 := by
    have := pow_orderOf_eq_one k
    rw [hk, sq] at this
    exact congrArg Subtype.val this
  rcases CFSG.GH74.KGroups.L3Eps.sl2c_sq_eq_one hF hk2 with h | h
  · exfalso
    have : k = 1 := Subtype.ext h
    rw [this, orderOf_one] at hk
    omega
  · rw [← h]
    exact k.2

omit [Finite F] in
theorem not_isSolvable_map (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    ¬ Group.IsSolvable (K.map (projSL2 (F := F))) := by
  intro hs
  have hperf : Group.IsPerfect (K.map (projSL2 (F := F))) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hK]
  have hbot : K.map (projSL2 (F := F)) = ⊥ := by
    by_contra hne
    have : Nontrivial (K.map (projSL2 (F := F))) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hs
  apply hK1
  have hKZ : K ≤ Subgroup.center SL(2, F) := by
    rw [← ker_projSL2, ← Subgroup.map_eq_bot_iff]
    exact hbot
  rw [← hK, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.mp (hKZ hb) a

theorem pCoreOf_le_zpowers (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    pCoreOf 2 K ≤ Subgroup.zpowers (-1 : SL(2, F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (pCoreOf 2 K).map (projSL2 (F := F)) with hT
  have hTs : Group.IsSolvable T := by
    have h2 : IsPGroup 2 ↥T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).map _
    have : Group.IsNilpotent T := h2.isNilpotent
    infer_instance
  have hle : K.map (projSL2 (F := F)) ≤ Subgroup.normalizer (T : Set PSL(2, F)) :=
    (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)).trans
      (Subgroup.le_normalizer_map _)
  by_cases hTb : T = ⊥
  · have : pCoreOf 2 K ≤ (projSL2 (F := F)).ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact hTb
    rw [ker_projSL2] at this
    exact this.trans center_le_zpowers
  · exact absurd hle
      (CFSG.SignalizerFunctorTheorem.CatalogBridge.nonLocalized_of_not_isSolvable_psl2 _
        (not_isSolvable_map hK hK1) T hTb hTs)

variable {F' : Type} [Field F']

theorem ker_chi_eq (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥)
    [CharP F' 2] (χ : ↥K →* SL(2, F'))
    (hχ : Function.Surjective χ) (hχk : IsPGroup 2 ↥χ.ker) :
    χ.ker = (Subgroup.zpowers (-1 : SL(2, F))).subgroupOf K := by
  refine le_antisymm ?_ ?_
  · intro k hk
    rw [Subgroup.mem_subgroupOf]
    refine pCoreOf_le_zpowers hK hK1 ?_
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (N := χ.ker.map K.subtype)
      (Subgroup.map_subtype_le _) ?_ (hχk.map _) ⟨k, hk, rfl⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      exact (χ.normal_ker).conj_mem _ hy' _
    · rintro ⟨y', hy', hyy⟩
      have hyK : y ∈ K := by
        have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [e, ← hyy]
        exact K.mul_mem (K.mul_mem (K.inv_mem hg) y'.2) hg
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      have h1 : (⟨y, hyK⟩ : ↥K) = ⟨g, hg⟩⁻¹ * y' * ⟨g, hg⟩⁻¹⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [show (y' : SL(2, F)) = g * y * g⁻¹ from hyy]
        group
      rw [h1]
      exact (χ.normal_ker).conj_mem _ hy' _
  · intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    have hc : χ k ∈ Subgroup.center SL(2, F') := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := hχ y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_center_iff.mp (zpowers_le_center hk) l)
    rw [center_sl2_two, Subgroup.mem_bot] at hc
    exact hc

theorem n_eq_two (hodd : CFSG.GorensteinWalter.IsOddPrimePower
      (Nat.card F)) (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) {n : ℕ}
    [Fintype F'] (hF' : Fintype.card F' = 2 ^ n) [CharP F' 2] (χ : ↥K →* SL(2, F'))
    (hχ : Function.Surjective χ) (hχk : IsPGroup 2 ↥χ.ker) : n ≤ 2 := by
  have hker := ker_chi_eq hK hK1 χ hχ hχk
  set ψ : ↥K →* PSL(2, F) := (projSL2 (F := F)).comp K.subtype with hψ
  have hle : χ.ker ≤ ψ.ker := by
    intro k hk
    rw [hker, Subgroup.mem_subgroupOf] at hk
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_projSL2]
    exact zpowers_le_center hk
  set θ : SL(2, F') →* PSL(2, F) := χ.liftOfSurjective hχ ⟨ψ, hle⟩ with hθ
  have hθχ : ∀ k, θ (χ k) = ψ k := fun k => χ.liftOfRightInverse_comp_apply _ _ ⟨ψ, hle⟩ k
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := hχ y
    rw [MonoidHom.mem_ker, hθχ, hψ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      ker_projSL2] at hy
    have hk : k ∈ χ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact center_le_zpowers hy
    rw [Subgroup.mem_bot]
    exact hk
  obtain ⟨hE, hEc⟩ := upper_elem (F' := F')
  have hEc' : Nat.card ((upperHom (F := F')).range.map θ) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective hθinj, hEc, Nat.card_eq_fintype_card, hF']
  have h1 := CFSG.SectionRank.le_pRank (by norm_num) le_top
    (CFSG.SectionRank.isElemAbelian_map hE θ) hEc'
  have h2 := CFSG.GH74.SmallRanks.twoRank_psl2_le_two F hodd
  exact h1.trans h2

omit [Finite F] in
theorem eq_top_of_normal (h4 : 4 ≤ Nat.card F) (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥)
    (hneg : (-1 : SL(2, F)) ∈ K) (hN : K.Normal) : K = ⊤ := by
  have hS := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hCn : (K.map (projSL2 (F := F))).Normal := hN.map _ projSL2_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (projSL2 (F := F))) with h | h
  · exfalso
    apply hK1
    have hKZ : K ≤ Subgroup.center SL(2, F) := by
      rw [← ker_projSL2, ← Subgroup.map_eq_bot_iff]
      exact h
    rw [← hK, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hKZ hb) a
  · rw [eq_top_iff]
    intro g _
    have hg : projSL2 g ∈ K.map (projSL2 (F := F)) := by rw [h]; trivial
    obtain ⟨k, hk, hkg⟩ := hg
    have hz : k⁻¹ * g ∈ Subgroup.center SL(2, F) := by
      rw [← ker_projSL2, MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    have hzK : k⁻¹ * g ∈ K := (Subgroup.zpowers_le.mpr hneg) (center_le_zpowers hz)
    have e : g = k * (k⁻¹ * g) := by group
    rw [e]
    exact K.mul_mem hk hzK

end Perfect

end CFSG.Quasithin.H13.KGInspOdd
