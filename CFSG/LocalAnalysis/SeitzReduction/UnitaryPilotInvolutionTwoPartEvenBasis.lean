module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPart

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {N : ℕ}

section ASpan

variable {V : Type*} [AddCommGroup V] [Module K V] {r ε : ℕ}

theorem aSpan_mono (w : HypIndex r ε → V) {i j : ℕ} (hij : i ≤ j) :
    (aSpan w i : Submodule K V) ≤ aSpan w j :=
  Submodule.span_mono (Set.image_mono fun x (hx : (x : ℕ) < i) => lt_of_lt_of_le hx hij)

theorem aSpan_self_eq (w : HypIndex r ε → V) : (aSpan w r : Submodule K V) = aSpanTop K w := by
  rw [aSpan, aSpanTop]
  congr 1
  ext v
  simp

end ASpan

theorem exists_wittBasis_eq_aSpan {r ε : ℕ} (hε : ε ≤ 1) (hN : N = 2 * r + ε)
    (W : Submodule K (Fin N → K)) (hW : ∀ x ∈ W, ∀ y ∈ W, stdHermForm h N x y = 0) :
    Module.finrank K W ≤ r ∧ ∃ w : Module.Basis (HypIndex r ε) K (Fin N → K),
      (∀ x y, stdHermForm h N (w x) (w y) = hypGram r ε K x y) ∧
        W = aSpan ⇑w (Module.finrank K W) := by
  obtain ⟨C, hC, hCW⟩ := exists_isotropicChain_eq W hW
  obtain ⟨hk, w, hw, hspan⟩ := exists_hypBasis_of_isotropicChain h _ (stdHermForm_isSymm h N)
    (stdHermForm_separatingLeft h N) hε (by rw [Module.finrank_fin_fun]; exact hN) C hC
  exact ⟨hk, w, hw, hCW.symm.trans (hspan _ le_rfl)⟩

section Rebase

variable {V : Type*} [AddCommGroup V] [Module K V] {m : ℕ}

@[expose] noncomputable def rebaseFamily (θ : K) (w : HypIndex (m + 1) 0 → V) :
    HypIndex m 2 → V
  | .inl i => w (.inl i.castSucc)
  | .inr (.inl l) => w (.inl (Fin.last m)) + (![θ, h.bar θ] l) • w (.inr (.inr (Fin.last m)))
  | .inr (.inr j) => w (.inr (.inr j.castSucc))

theorem rebaseFamily_gram [CharP K 2] {θ : K} (hθ : θ + h.bar θ = 1)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} {w : HypIndex (m + 1) 0 → V}
    (hw : ∀ x y, B (w x) (w y) = hypGram (m + 1) 0 K x y) (x y : HypIndex m 2) :
    B (rebaseFamily h θ w x) (rebaseFamily h θ w y) = hypGram m 2 K x y := by
  rcases x with i | l | i <;> rcases y with j | t | j <;>
    simp only [rebaseFamily, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hw, hypGram_inl_inl, hypGram_inl_inr_inl,
      hypGram_inl_inr_inr, hypGram_inr_inl_inl, hypGram_inr_inl_inr_inl, hypGram_inr_inl_inr_inr,
      hypGram_inr_inr_inl, hypGram_inr_inr_inr_inl, hypGram_inr_inr_inr_inr, Fin.castSucc_inj,
      Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, ite_false, mul_zero, add_zero,
      zero_add]
  fin_cases l <;> fin_cases t <;>
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.mk_one, h.bar_bar, ite_true, one_ne_zero, zero_ne_one,
      ite_false, RingHom.id_apply, mul_one] <;>
    first
      | exact hθ
      | exact CharTwo.add_self_eq_zero _
      | (rw [add_comm]; exact hθ)

theorem exists_rebase [CharP K 2] [FiniteDimensional K V] (hV : Module.finrank K V = 2 * m + 2)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} {w : HypIndex (m + 1) 0 → V}
    (hw : ∀ x y, B (w x) (w y) = hypGram (m + 1) 0 K x y) :
    ∃ w' : Module.Basis (HypIndex m 2) K V, (∀ x y, B (w' x) (w' y) = hypGram m 2 K x y) ∧
      (aSpan w m : Submodule K V) ≤ aSpanTop K ⇑w' := by
  obtain ⟨θ, hθ⟩ := exists_add_bar_eq_one h
  have hv := rebaseFamily_gram h hθ hw
  refine ⟨basisOfHypGram _ hv hV, fun x y => by rw [coe_basisOfHypGram, hv], ?_⟩
  rw [coe_basisOfHypGram, aSpan, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj' : (j : ℕ) < m := hj
  exact inl_mem_aSpanTop (rebaseFamily h θ w) ⟨j, hj'⟩

end Rebase

section Adapted

variable {n : ℕ}

theorem exists_adapted_wittBasis (s : unitarySU 2 f K (2 * n)) (hss : s * s = 1)
    {w₀ : Module.Basis (HypIndex n 0) K (Fin (2 * n) → K)}
    (hw₀ : ∀ x y, stdHermForm h (2 * n) (w₀ x) (w₀ y) = hypGram n 0 K x y)
    (hW : LinearMap.range (((s : GL (Fin (2 * n)) K) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K).mulVecLin - LinearMap.id) = aSpanTop K ⇑w₀) :
    ∃ w : Module.Basis (HypIndex n 0) K (Fin (2 * n) → K),
      (∀ x y, stdHermForm h (2 * n) (w x) (w y) = hypGram n 0 K x y) ∧
      (∀ i, ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ w (.inl i) =
        w (.inl i)) ∧
      ∀ i, ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ
        w (.inr (.inr i)) = w (.inr (.inr i)) + w (.inl i) := by
  have : CharP K 2 := h.charP
  set S := ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hS
  set F : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) := S.mulVecLin - LinearMap.id with hF
  set U : Submodule K (Fin (2 * n) → K) :=
    Submodule.span K (Set.range fun j : Fin n => w₀ (.inr (.inr j))) with hU
  have hFv : ∀ v, F v = S *ᵥ v - v := fun v => rfl
  have hadj : ∀ x y, stdHermForm h (2 * n) (F x) y = stdHermForm h (2 * n) x (F y) :=
    fun x y => stdHermForm_sub_left_of_mul_self h hss x y
  have hFM : ∀ v, F v ∈ aSpanTop K ⇑w₀ := fun v => by
    rw [← hW]
    exact LinearMap.mem_range_self F v
  have hMM : ∀ x ∈ aSpanTop K ⇑w₀, ∀ y ∈ aSpanTop K ⇑w₀, stdHermForm h (2 * n) x y = 0 :=
    fun x hx y hy => form_eq_zero_of_mem_aSpanTop h hw₀ hx (Submodule.mem_sup_left hy)
  have hUU : ∀ x ∈ U, ∀ y ∈ U, stdHermForm h (2 * n) x y = 0 := fun x hx y hy =>
    form_eq_zero_of_mem_span_range h (fun i j => by rw [hw₀, hypGram_inr_inr_inr_inr]) hx hy
  have hadd : ∀ u : Fin (2 * n) → K, u + u = 0 := fun u => funext fun i => by
    rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
  have hFF : ∀ v, F (F v) = 0 := fun v => by
    rw [hFv, hFv, mulVec_sub, mulVec_mulVec_eq_self_of_mul_self hss,
      show v - S *ᵥ v - (S *ᵥ v - v) = (v + v) - (S *ᵥ v + S *ᵥ v) by abel, hadd, hadd, sub_zero]
  have hzero : ∀ z, (∀ x, stdHermForm h (2 * n) z (w₀ x) = 0) → z = 0 := fun z hz =>
    stdHermForm_separatingLeft h _ z fun y => by
      rw [show stdHermForm h (2 * n) z = 0 from w₀.ext fun x => by rw [hz, LinearMap.zero_apply],
        LinearMap.zero_apply]
  have hMdim : Module.finrank K (aSpanTop K ⇑w₀) = n := by
    have := finrank_span_eq_card (R := K) (b := fun i : Fin n => w₀ (.inl i))
      (w₀.linearIndependent.comp _ Sum.inl_injective)
    rw [aSpanTop, this, Fintype.card_fin]
  have hker : LinearMap.ker F = aSpanTop K ⇑w₀ := by
    have hle : aSpanTop K ⇑w₀ ≤ LinearMap.ker F := by
      rw [← hW]
      rintro _ ⟨v, rfl⟩
      exact hFF v
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    have := LinearMap.finrank_range_add_finrank_ker F
    rw [hW, hMdim, Module.finrank_fin_fun] at this
    rw [hMdim]
    omega
  set H₀ : (Fin (2 * n) → K) →ₛₗ[h.bar] (Fin (2 * n) → K) →ₗ[K] K :=
    (stdHermForm h (2 * n)).compl₂ F with hH₀
  have hH₀s : H₀.IsSymm := ⟨fun x y => by
    rw [hH₀, LinearMap.compl₂_apply, LinearMap.compl₂_apply, (stdHermForm_isSymm h _).eq x (F y)]
    exact hadj y x⟩
  set H := H₀.domRestrict₁₂ U U with hH
  have hHapp : ∀ x y : U, H x y = stdHermForm h (2 * n) x (F y) := fun x y => by
    rw [hH, LinearMap.domRestrict₁₂_apply, hH₀, LinearMap.compl₂_apply]
  have hHl : H.SeparatingLeft := by
    intro x hx
    have hFx : F x = 0 := hzero _ fun y => by
      rcases y with i | l | j
      · exact hMM _ (hFM x) _ (inl_mem_aSpanTop _ i)
      · exact l.elim0
      · rw [hadj, ← hHapp x ⟨_, Submodule.subset_span ⟨j, rfl⟩⟩]
        exact hx _
    have hxM : (x : Fin (2 * n) → K) ∈ aSpanTop K ⇑w₀ := hker ▸ LinearMap.mem_ker.mpr hFx
    exact Subtype.ext (hzero _ fun y => by
      rcases y with i | l | j
      · exact hMM _ hxM _ (inl_mem_aSpanTop _ i)
      · exact l.elim0
      · exact hUU _ x.2 _ (Submodule.subset_span ⟨j, rfl⟩))
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hH₀s.domRestrict U) hHl
  have hUdim : Module.finrank K U = n := by
    have := finrank_span_eq_card (R := K) (b := fun i : Fin n => w₀ (.inr (.inr i)))
      (w₀.linearIndependent.comp _ (Sum.inr_injective.comp Sum.inr_injective))
    rw [hU, this, Fintype.card_fin]
  let b : Fin n → Fin (2 * n) → K := fun i => (e (Fin.cast hUdim.symm i) : Fin (2 * n) → K)
  have hbU : ∀ i, b i ∈ U := fun i => (e _).2
  have hb : ∀ i j, stdHermForm h (2 * n) (b i) (F (b j)) = if i = j then 1 else 0 := fun i j => by
    have := he (Fin.cast hUdim.symm i) (Fin.cast hUdim.symm j)
    rw [hHapp] at this
    simp only [(Fin.cast_injective _).eq_iff] at this
    exact this
  let v : HypIndex n 0 → Fin (2 * n) → K
    | .inl i => F (b i)
    | .inr (.inl l) => l.elim0
    | .inr (.inr i) => b i
  have hv : ∀ x y, stdHermForm h (2 * n) (v x) (v y) = hypGram n 0 K x y := by
    rintro (i | l | i) (j | t | j)
    · exact (hMM _ (hFM _) _ (hFM _)).trans (hypGram_inl_inl i j).symm
    · exact t.elim0
    · change stdHermForm h (2 * n) (F (b i)) (b j) = _
      rw [hadj, hb, hypGram_inl_inr_inr]
    · exact l.elim0
    · exact l.elim0
    · exact l.elim0
    · change stdHermForm h (2 * n) (b i) (F (b j)) = _
      rw [hb, hypGram_inr_inr_inl]
    · exact t.elim0
    · exact (hUU _ (hbU i) _ (hbU j)).trans (hypGram_inr_inr_inr_inr i j).symm
  refine ⟨basisOfHypGram v hv (by rw [Module.finrank_fin_fun]; omega),
    fun x y => by rw [coe_basisOfHypGram, hv], fun i => ?_, fun i => ?_⟩
  · rw [coe_basisOfHypGram]
    change S *ᵥ F (b i) = F (b i)
    have := hFF (b i)
    rw [hFv (F (b i))] at this
    exact sub_eq_zero.mp this
  · rw [coe_basisOfHypGram]
    change S *ᵥ b i = b i + F (b i)
    rw [hFv]
    abel

end Adapted

end CFSG.SeitzReduction.UnitaryPilot
