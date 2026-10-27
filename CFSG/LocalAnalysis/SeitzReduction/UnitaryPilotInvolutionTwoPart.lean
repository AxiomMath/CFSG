module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartGroup
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUniquePair

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

section Involution

variable {s : unitarySU 2 f K n}

theorem stdHermForm_mulVec_mulVec_unitarySU (x y : Fin n → K) :
    stdHermForm h n (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y :=
  ((mem_unitarySU_iff_isometry h).mp s.2).2 x y

variable (hss : s * s = 1)
include hss

theorem mulVec_mulVec_eq_self_of_mul_self (v : Fin n → K) :
    ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, hss, OneMemClass.coe_one,
    Units.val_one, one_mulVec]

theorem stdHermForm_sub_left_of_mul_self (x y : Fin n → K) :
    stdHermForm h n (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x) y =
      stdHermForm h n x (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y - y) := by
  have h1 : stdHermForm h n (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) y =
      stdHermForm h n x (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) := by
    conv_lhs => rw [← mulVec_mulVec_eq_self_of_mul_self hss y]
    exact stdHermForm_mulVec_mulVec_unitarySU h x _
  rw [LinearMap.map_sub₂, map_sub, h1]

theorem stdHermForm_sub_sub_eq_zero_of_mul_self [CharP K 2] (x y : Fin n → K) :
    stdHermForm h n (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x)
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y - y) = 0 := by
  rw [stdHermForm_sub_left_of_mul_self h hss, mulVec_sub, mulVec_mulVec_eq_self_of_mul_self hss]
  have hadd : ∀ u : Fin n → K, u + u = 0 := fun u => funext fun i => by
    rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
  have : y - ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y -
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y - y) = 0 := by
    rw [show y - ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y -
      (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y - y) =
        (y + y) - (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y +
          ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) by abel, hadd, hadd, sub_zero]
  rw [this, map_zero]

theorem mulVec_eq_self_of_forall_stdHermForm_eq_zero {x : Fin n → K}
    (hx : ∀ v, stdHermForm h n (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - v) x = 0) :
    ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = x := by
  refine sub_eq_zero.mp (stdHermForm_separatingLeft h n _ fun v => ?_)
  rw [← (stdHermForm_isSymm h n).eq v, ← stdHermForm_sub_left_of_mul_self h hss, hx, map_zero]

end Involution

section Witt

theorem form_eq_zero_of_mem_span_range {V : Type*} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} {ι κ : Type*} {u : ι → V} {v : κ → V}
    (huv : ∀ i j, B (u i) (v j) = 0) {x y : V} (hx : x ∈ Submodule.span K (Set.range u))
    (hy : y ∈ Submodule.span K (Set.range v)) : B x y = 0 := by
  have h1 : ∀ i, Submodule.span K (Set.range v) ≤ LinearMap.ker (B (u i)) := fun i =>
    Submodule.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact huv i j)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact LinearMap.mem_ker.mp (h1 i hy)
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x x' _ _ hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', add_zero]
  | smul c x _ hx => rw [map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem form_eq_zero_of_mem_aSpanTop {V : Type*} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} {r ε : ℕ} {w : HypIndex r ε → V}
    (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y) {x y : V} (hx : x ∈ aSpanTop K w)
    (hy : y ∈ aSpanTop K w ⊔ zSpan K w) : B x y = 0 := by
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, form_eq_zero_of_mem_span_range h (fun i j => by rw [hw, hypGram_inl_inl]) hx hy₁,
    form_eq_zero_of_mem_span_range h (fun i l => by rw [hw, hypGram_inl_inr_inl]) hx hy₂, add_zero]

theorem exists_wittBasis_le_aSpanTop (W : Submodule K (Fin n → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, stdHermForm h n x y = 0) :
    ∃ w : Module.Basis (HypIndex (n / 2) (n % 2)) K (Fin n → K),
      (∀ x y, stdHermForm h n (w x) (w y) = hypGram (n / 2) (n % 2) K x y) ∧
        W ≤ aSpanTop K ⇑w := by
  obtain ⟨C, hC, hCW⟩ := exists_isotropicChain_eq W hW
  obtain ⟨-, w, hw, hspan⟩ := exists_hypBasis_of_isotropicChain h _ (stdHermForm_isSymm h n)
    (stdHermForm_separatingLeft h n) (r := n / 2) (ε := n % 2) (by omega)
    (by rw [Module.finrank_fin_fun]; omega) C hC
  refine ⟨w, hw, ?_⟩
  rw [← hCW, hspan _ le_rfl]
  exact Submodule.span_mono (Set.image_subset_range _ _)

end Witt

include h in
theorem exists_isPGroup_le_centralizer_of_mul_self (s : unitarySU 2 f K n) (hss : s * s = 1) :
    ∃ R : Subgroup (unitarySU 2 f K n), IsPGroup 2 R ∧ R ≤ Subgroup.centralizer {s} ∧
      2 ^ (f * (n / 2 * (n / 2 + 2 * (n % 2)))) ≤ Nat.card R := by
  have : CharP K 2 := h.charP
  set S := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hS
  set W : Submodule K (Fin n → K) := LinearMap.range (S.mulVecLin - LinearMap.id) with hW
  have hmemW : ∀ v, S *ᵥ v - v ∈ W := fun v => ⟨v, rfl⟩
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, stdHermForm h n x y = 0 := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact stdHermForm_sub_sub_eq_zero_of_mul_self h hss a b
  obtain ⟨w, hw, hWM⟩ := exists_wittBasis_le_aSpanTop h W hWiso
  refine ⟨pairRadical 2 f (aSpanTop K ⇑w) (aSpanTop K ⇑w ⊔ zSpan K ⇑w),
    isPGroup_pairRadical 2 f _ _, fun g hg => ?_, card_pairRadical_ge h w hw⟩
  refine mem_centralizer_of_mem_pairRadical (fun v => hWM (hmemW v)) (fun v hv => ?_) hg
  exact mulVec_eq_self_of_forall_stdHermForm_eq_zero h hss fun u =>
    form_eq_zero_of_mem_aSpanTop h hw (hWM (hmemW u)) hv

theorem odd_card_unitaryScalars (hn : 1 ≤ n) : Odd (Nat.card (unitaryScalars h n)) := by
  rw [card_unitaryScalars h hn]
  refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right _ _)
  have : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩
  exact this.add_one

theorem exists_mk_eq_mul_self_eq_one (hn : 1 ≤ n) (y : unitaryPSU h n) (hy : y ^ 2 = 1) :
    ∃ s : unitarySU 2 f K n, s * s = 1 ∧ (QuotientGroup.mk s : unitaryPSU h n) = y := by
  obtain ⟨s₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := odd_card_unitaryScalars h hn
  have hZ : s₀ ^ 2 ∈ unitaryScalars h n := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hy
  refine ⟨s₀ ^ Nat.card (unitaryScalars h n), ?_, ?_⟩
  · rw [← pow_add, ← two_mul, pow_mul]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨s₀ ^ 2, hZ⟩ : unitaryScalars h n)))
  · rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, hy, one_pow, one_mul]

theorem unitaryInnerInvolutionTwoPart_holds (h : UnitaryFieldData 2 f K) (n : ℕ) :
    UnitaryInnerInvolutionTwoPart h n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro y _
    simp
  refine unitaryInnerInvolutionTwoPart_of_twoSubgroup h fun y hy => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hss, rfl⟩ := exists_mk_eq_mul_self_eq_one h hn y (by
    have := pow_orderOf_eq_one y
    rwa [hy] at this)
  obtain ⟨R, hR2, hRC, hRcard⟩ := exists_isPGroup_le_centralizer_of_mul_self h s hss
  set π : unitarySU 2 f K n →* unitaryPSU h n := QuotientGroup.mk' (unitaryScalars h n) with hπ
  have hodd := odd_card_unitaryScalars h hn
  have hinj : Function.Injective (π.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : (g : unitarySU 2 f K n) ∈ unitaryScalars h n := (QuotientGroup.eq_one_iff _).mp hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) g
    have hdvd : orderOf g ∣ Nat.card (unitaryScalars h n) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk _ hgZ]
      exact orderOf_dvd_natCard _
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at hk
    · rw [hk] at hdvd
      have h1 := Nat.odd_iff.mp hodd
      have h2 := Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_pow_self 2 k.succ_ne_zero) hdvd)
      omega
  refine ⟨(π.comp R.subtype).range,
    hR2.of_surjective _ (π.comp R.subtype).rangeRestrict_surjective, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.mp (hRC g.2)
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hπ,
      QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hRcard

end CFSG.SeitzReduction.UnitaryPilot
