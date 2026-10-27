module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerKernel
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

structure SpPlaneSetup (ℓ f p r : ℕ) (K : Type) [Field K] (Ahat : Subgroup (StatedSp r K)) :
    Prop where
  prime_ell : ℓ.Prime
  one_le_f : 1 ≤ f
  card_K : Nat.card K = ℓ ^ f
  prime_p : p.Prime
  three_lt_p : 3 < p
  ne_char : p ≠ ℓ
  two_le_r : 2 ≤ r
  not_exceptional : ¬ (r = 2 ∧ ℓ ^ f = 2)
  elem : IsElementaryAbelian p Ahat
  card_plane : Nat.card Ahat = p ^ 2

variable {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

theorem SpPlaneSetup.finite (S : SpPlaneSetup ℓ f p r K Ahat) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [S.card_K]; exact pow_ne_zero f S.prime_ell.ne_zero)

theorem SpPlaneSetup.charP (S : SpPlaneSetup ℓ f p r K Ahat) : CharP K ℓ := by
  have := S.finite
  have := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨S.prime_ell⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, S.card_K])

theorem SpPlaneSetup.p_ne_two (S : SpPlaneSetup ℓ f p r K Ahat) : p ≠ 2 := by
  have := S.three_lt_p
  omega

theorem SpPlaneSetup.neZero (S : SpPlaneSetup ℓ f p r K Ahat) : NeZero r :=
  ⟨by have := S.two_le_r; omega⟩

theorem SpPlaneSetup.p_cast_ne_zero (S : SpPlaneSetup ℓ f p r K Ahat) : (p : K) ≠ 0 := by
  have := S.charP
  intro h
  rw [CharP.cast_eq_zero_iff K ℓ] at h
  exact S.ne_char ((Nat.prime_dvd_prime_iff_eq S.prime_ell S.prime_p).mp h).symm

theorem SpPlaneSetup.conj_injective (S : SpPlaneSetup ℓ f p r K Ahat) :
    Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))) :=
  spConj_injective S.prime_ell S.one_le_f S.card_K S.two_le_r S.not_exceptional

theorem SpPlaneSetup.pow_eq_one (S : SpPlaneSetup ℓ f p r K Ahat) {x : StatedSp r K}
    (hx : x ∈ Ahat) : x ^ p = 1 := by
  have := S.elem
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem SpPlaneSetup.orderOf_eq (S : SpPlaneSetup ℓ f p r K Ahat) {x : StatedSp r K}
    (hx : x ∈ Ahat) (hx1 : x ≠ 1) : orderOf x = p :=
  have : Fact p.Prime := ⟨S.prime_p⟩
  orderOf_eq_prime (S.pow_eq_one hx) hx1

theorem four_le_lcm_of_small {q : ℕ} (hq : q = 2 ∨ q = 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    4 ≤ Nat.lcm (orderOf (q : ZMod p)) 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    rcases hq with rfl | rfl <;> (have := Nat.le_of_dvd (by norm_num) h; omega)
  have hpos : 0 < orderOf (q : ZMod p) := by
    apply orderOf_pos_iff.mpr
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by have := hp.one_lt; omega,
      ZMod.pow_card_sub_one_eq_one hq0⟩
  have hge : 3 ≤ orderOf (q : ZMod p) := by
    by_contra hlt
    have hle : orderOf (q : ZMod p) ≤ 2 := by omega
    have hdvd : orderOf (q : ZMod p) ∣ 2 := by
      interval_cases h : orderOf (q : ZMod p)
      · exact one_dvd _
      · exact dvd_refl _
    have hsq : (q : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hdp : p ∣ q ^ 2 - 1 := by
      have h1 : ((q ^ 2 - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by rcases hq with rfl | rfl <;> norm_num)),
          Nat.cast_pow, hsq, Nat.cast_one, sub_self]
      exact (ZMod.natCast_eq_zero_iff _ _).mp h1
    rcases hq with rfl | rfl
    · have : p ∣ 3 := by simpa using hdp
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have : p ∣ 8 := by simpa using hdp
      have h8 : p ∣ 2 ^ 3 := by simpa using this
      have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h8)
      omega
  have h2 : 2 ∣ Nat.lcm (orderOf (q : ZMod p)) 2 := Nat.dvd_lcm_right _ _
  have h3 : orderOf (q : ZMod p) ≤ Nat.lcm (orderOf (q : ZMod p)) 2 :=
    Nat.le_of_dvd (Nat.lcm_pos hpos (by norm_num)) (Nat.dvd_lcm_left _ _)
  omega


open _root_.Classical in
structure SpPlaneDecomp (p : ℕ) (Ahat : Subgroup (StatedSp r K)) : Prop where
  internal : DirectSum.IsInternal (spInnerSummand p Ahat)
  orth : ∀ i j, i ≠ j → ∀ u ∈ spInnerSummand p Ahat i, ∀ v ∈ spInnerSummand p Ahat j,
    spForm r K u v = 0
  nondeg : ∀ i, ((spForm r K).restrict (spInnerSummand p Ahat i)).Nondegenerate
  ker_eq : ∀ M : Subgroup ↥Ahat, Nat.card M = p → ∀ a ∈ M, a ≠ 1 →
    LinearMap.ker (spEnd (a : StatedSp r K) - 1) = spLineFix M ∧
      spLineFix M = spPlaneFix Ahat ⊔ spLineSpace M
  two_active : ∃ M₁ M₂ : Subgroup ↥Ahat, Nat.card M₁ = p ∧ Nat.card M₂ = p ∧ M₁ ≠ M₂ ∧
    spLineSpace M₁ ≠ ⊥ ∧ spLineSpace M₂ ≠ ⊥
  dim_dvd : ∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ →
    0 < Module.finrank K (spLineSpace M) ∧
      Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ∣ Module.finrank K (spLineSpace M)
  lcm_le : Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≤ r

open _root_.Classical in
theorem SpPlaneSetup.decomp (S : SpPlaneSetup ℓ f p r K Ahat) : SpPlaneDecomp p Ahat := by
  have := S.finite
  have := S.charP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := symplectic_plane_kernel_line_decomposition
    S.prime_ell S.prime_p S.p_ne_two S.ne_char S.elem S.card_plane
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem nondegenerate_sup_of_orthogonal {V : Type*} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {V₁ V₂ : Submodule K V}
    (h1 : (B.restrict V₁).Nondegenerate) (h2 : (B.restrict V₂).Nondegenerate)
    (horth : ∀ u ∈ V₁, ∀ v ∈ V₂, B u v = 0) (horth' : ∀ v ∈ V₂, ∀ u ∈ V₁, B v u = 0) :
    (B.restrict (V₁ ⊔ V₂)).Nondegenerate := by
  constructor
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp y.2
    have e1 : y₁ = 0 := by
      have := h1.1 ⟨y₁, hy₁⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_left z.2⟩
        change B (y : V) (z : V) = 0 at h
        change B y₁ (z : V) = 0
        rw [← hsum, map_add, LinearMap.add_apply, horth' y₂ hy₂ z z.2, add_zero] at h
        exact h)
      exact congrArg Subtype.val this
    have e2 : y₂ = 0 := by
      have := h2.1 ⟨y₂, hy₂⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_right z.2⟩
        change B (y : V) (z : V) = 0 at h
        change B y₂ (z : V) = 0
        rw [← hsum, map_add, LinearMap.add_apply, horth y₁ hy₁ z z.2, zero_add] at h
        exact h)
      exact congrArg Subtype.val this
    exact Subtype.ext (by rw [← hsum, e1, e2, add_zero]; rfl)
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp y.2
    have e1 : y₁ = 0 := by
      have := h1.2 ⟨y₁, hy₁⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_left z.2⟩
        change B (z : V) (y : V) = 0 at h
        change B (z : V) y₁ = 0
        rw [← hsum, map_add, horth z z.2 y₂ hy₂, add_zero] at h
        exact h)
      exact congrArg Subtype.val this
    have e2 : y₂ = 0 := by
      have := h2.2 ⟨y₂, hy₂⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_right z.2⟩
        change B (z : V) (y : V) = 0 at h
        change B (z : V) y₂ = 0
        rw [← hsum, map_add, horth' z z.2 y₁ hy₁, zero_add] at h
        exact h)
      exact congrArg Subtype.val this
    exact Subtype.ext (by rw [← hsum, e1, e2, add_zero]; rfl)


theorem SpPlaneDecomp.ker_eq_sup (D : SpPlaneDecomp p Ahat) {M : Subgroup ↥Ahat}
    (hM : Nat.card M = p) {x : StatedSp r K} (hxA : x ∈ Ahat)
    (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) :
    LinearMap.ker (spEnd x - 1) = spPlaneFix Ahat ⊔ spLineSpace M := by
  have h := D.ker_eq M hM ⟨x, hxA⟩ hxM (fun h' => hx1 (congrArg Subtype.val h'))
  exact h.1.trans h.2

open _root_.Classical in
theorem SpPlaneDecomp.nondegenerate_ker (D : SpPlaneDecomp p Ahat) {M : Subgroup ↥Ahat}
    (hM : Nat.card M = p) {x : StatedSp r K} (hxA : x ∈ Ahat)
    (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) :
    ((spForm r K).restrict (LinearMap.ker (spEnd x - 1))).Nondegenerate := by
  rw [D.ker_eq_sup hM hxA hxM hx1]
  refine nondegenerate_sup_of_orthogonal (D.nondeg none) (D.nondeg (some ⟨M, hM⟩)) ?_ ?_
  · intro u hu v hv
    exact D.orth none (some ⟨M, hM⟩) (by simp) u hu v hv
  · intro v hv u hu
    exact D.orth (some ⟨M, hM⟩) none (by simp) v hv u hu

theorem SpPlaneDecomp.lcm_le_finrank_ker (D : SpPlaneDecomp p Ahat) {M : Subgroup ↥Ahat}
    (hM : Nat.card M = p) (hVM : spLineSpace M ≠ ⊥) {x : StatedSp r K} (hxA : x ∈ Ahat)
    (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) :
    2 ≤ Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ∧
      Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≤
        Module.finrank K (LinearMap.ker (spEnd x - 1)) := by
  obtain ⟨hpos, hdvd⟩ := D.dim_dvd M hM hVM
  have h1 := Nat.le_of_dvd hpos hdvd
  have h2 : Module.finrank K (spLineSpace M) ≤ Module.finrank K (LinearMap.ker (spEnd x - 1)) := by
    rw [D.ker_eq_sup hM hxA hxM hx1]
    exact Submodule.finrank_mono le_sup_right
  have h3 : 0 < Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 := Nat.pos_of_dvd_of_pos hdvd hpos
  exact ⟨Nat.le_of_dvd h3 (Nat.dvd_lcm_right _ _), by omega⟩

theorem spFixedDim_eq_finrank_ker (x : StatedSp r K) :
    spFixedDim x = Module.finrank K (LinearMap.ker (spEnd x - 1)) := by
  unfold spFixedDim
  rw [show (X - 1 : K[X]) = X - C 1 by rw [map_one], KCUnitary.primaryComponent_X_sub_C_one]

theorem ker_proj_eq_bot_of_even [Finite K] (hr : 1 ≤ r) (hK : 2 ∣ Nat.card K) :
    (proj r K).ker = ⊥ := by
  rw [SymplecticHigher.ker_proj, ← Subgroup.card_eq_one, card_spScalars_eq_gcd K hr]
  have : 1 < Nat.card K := Finite.one_lt_card
  have h2 : ¬ 2 ∣ Nat.card K - 1 := by omega
  exact (Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))

theorem SpPlaneSetup.spFixedListed (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) (hVM : spLineSpace M ≠ ⊥) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) :
    SpFixedListed x ∧ 2 ≤ spFixedDim x ∧ (Nat.card K = 2 ∨ Nat.card K = 3 → 4 ≤ spFixedDim x) := by
  obtain ⟨h2, hle⟩ := D.lcm_le_finrank_ker hM hVM hxA hxM hx1
  rw [← spFixedDim_eq_finrank_ker] at hle
  have h4 : Nat.card K = 2 ∨ Nat.card K = 3 → 4 ≤ spFixedDim x := fun hq =>
    (four_le_lcm_of_small hq S.prime_p S.three_lt_p).trans hle
  refine ⟨⟨by omega, ?_⟩, by omega, h4⟩
  rintro ⟨hdim, hq⟩
  have := h4 hq
  omega

@[expose] def CentralizesListed (α : MulAut (StatedProj (StatedSp r K))) (x : StatedSp r K) :
    Prop :=
  (SpFixedListed x → ∀ t ∈ spFixedLayerImage x, α * MulAut.conj t = MulAut.conj t * α) ∧
  ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → 2 ≤ primaryMultiplicity (spEnd x) h →
    ∀ t ∈ spBlockImage x h, α * MulAut.conj t = MulAut.conj t * α

theorem SpPlaneSetup.orderOf_proj (S : SpPlaneSetup ℓ f p r K Ahat) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hx1 : x ≠ 1) : orderOf (proj r K x) = p := by
  have := S.finite
  have : Fact p.Prime := ⟨S.prime_p⟩
  have hxp := S.pow_eq_one hxA
  have hr : 1 ≤ r := by have := S.two_le_r; omega
  have h1 : proj r K x ≠ 1 := by
    intro h
    exact hx1 (eq_of_map_eq_of_pow_eq_one_of_coprime (proj r K) ker_proj_le_center
      (coprime_card_ker_proj hr S.prime_p S.p_ne_two) (a := 1) (b := 1)
      (by rwa [pow_one]) (by simp) (by rw [h, map_one]))
  refine orderOf_eq_prime ?_ h1
  rw [← map_pow, hxp, map_one]

theorem SpPlaneSetup.blocks (S : SpPlaneSetup ℓ f p r K Ahat) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hx1 : x ≠ 1) : SpPrimaryBlocks ℓ f p x (proj r K x) := by
  have hr : 1 ≤ r := by have := S.two_le_r; omega
  exact (symplectic_cross_prime_primary_centralizer_blocks S.prime_ell S.one_le_f S.card_K
    S.prime_p S.p_ne_two S.ne_char hr (proj r K x) (S.orderOf_proj hxA hx1)).2 x rfl
    (S.orderOf_eq hxA hx1)

theorem isPerfect_spFixedFactor {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x))
    (h2 : 2 ≤ Module.finrank K (primaryComponent (spEnd x) (X - 1)))
    (hK : 4 ≤ Nat.card K ∨
      (Nat.card K = 3 ∧ 4 ≤ Module.finrank K (primaryComponent (spEnd x) (X - 1)))) :
    Group.IsPerfect (spFixedFactor x) := by
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hBalt : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun z => (spForm_isAlt (r := r) (K := K)).self_eq_zero (z : Fin r ⊕ Fin r → K)
  have hQS := KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hBalt blocks.fixed_nondegenerate
    h2 (by rcases hK with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  exact @KCUnitary.isPerfect_of_surjective _ _ _ _ φ.symm.toMonoidHom φ.symm.surjective hQS.1


theorem SpPlaneSetup.line_scalar [NeZero r] (S : SpPlaneSetup ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat)
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) (hVM : spLineSpace M ≠ ⊥) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) (A : gsp r K) (σ : K ≃+* K)
    {α : MulAut (StatedProj (StatedSp r K))} (hα : α = conjAut r K A * fieldAut r K σ)
    (hcent : CentralizesListed α x) :
    σ = RingEquiv.refl K ∧ ∃ l : K,
      (∀ u ∈ LinearMap.ker (spEnd x - 1), semilinMap A σ u = l • u) ∧
        l * l = (multiplier r K A : K) := by
  have := S.finite
  have hr : 1 ≤ r := by have := S.two_le_r; omega
  have hnd := D.nondegenerate_ker hM hxA hxM hx1
  obtain ⟨hlisted, h2dim, h4dim⟩ := S.spFixedListed D hM hVM hxA hxM hx1
  have hdim : spFixedDim x = Module.finrank K (LinearMap.ker (spEnd x - 1)) :=
    spFixedDim_eq_finrank_ker x
  have hne : LinearMap.ker (spEnd x - 1) ≠ ⊥ := by
    intro h
    have h0 : Module.finrank K (LinearMap.ker (spEnd x - 1)) = 0 := by
      rw [h]
      exact finrank_bot K _
    omega
  have hinj := S.conj_injective
  by_cases h42 : spFixedDim x = 4 ∧ Nat.card K = 2
  ·
    have himg : spFixedLayerImage x = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K) := by
      simp [spFixedLayerImage, hlisted, h42.1, h42.2]
    have hcomm : ∀ g ∈ ⁅spFixedFactor x, spFixedFactor x⁆,
        α * MulAut.conj (proj r K g) = MulAut.conj (proj r K g) * α := fun g hg =>
      hcent.1 hlisted _ (himg ▸ Subgroup.mem_map_of_mem _ hg)
    have hker0 : (proj r K).ker = ⊥ := ker_proj_eq_bot_of_even hr (by rw [h42.2])
    have hfix := semiConj_eq_of_commute hinj A σ (Or.inr hker0) (hα ▸ hcomm)
    exact line_scalar_of_derived h42.2 A σ hfix hnd (by omega)
  · have himg : spFixedLayerImage x = (spFixedFactor x).map (proj r K) := by
      simp [spFixedLayerImage, hlisted, h42]
    have hcomm : ∀ g ∈ spFixedFactor x,
        α * MulAut.conj (proj r K g) = MulAut.conj (proj r K g) * α := fun g hg =>
      hcent.1 hlisted _ (himg ▸ Subgroup.mem_map_of_mem _ hg)
    have hG : Group.IsPerfect (spFixedFactor x) ∨ (proj r K).ker = ⊥ := by
      by_cases hev : 2 ∣ Nat.card K
      · exact Or.inr (ker_proj_eq_bot_of_even hr hev)
      · left
        have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
          obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
          have hev1 : (spEnd x).HasEigenvalue 1 :=
            Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (by
              rw [one_smul]; exact mem_ker_sub_one_iff.mp hu), hu0⟩
          have := KCUnitaryScalar.X_sub_C_mem_primaryFactors hev1
          rwa [map_one] at this
        have hq3 : 1 < Nat.card K := Finite.one_lt_card
        have hfd : Module.finrank K (primaryComponent (spEnd x) (X - 1)) = spFixedDim x := rfl
        refine isPerfect_spFixedFactor (S.blocks hxA hx1) hmem (by rw [hfd]; exact h2dim) ?_
        rw [hfd]
        by_cases h3 : Nat.card K = 3
        · exact Or.inr ⟨h3, h4dim (Or.inr h3)⟩
        · exact Or.inl (by omega)
    have hfix := semiConj_eq_of_commute hinj A σ hG (hα ▸ hcomm)
    exact line_scalar_of_fixedFactor A σ hfix hnd hne

end CFSG.RankThree.PartOne.KCSpFull
