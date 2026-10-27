module

public import CFSG.Quasithin.Background.HSL3Pair

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def slAct (g : ↥(StatedSL 3 K)) (v : Fin 3 → K) : Fin 3 → K :=
  ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v

theorem slAct_one (v : Fin 3 → K) : slAct (1 : ↥(StatedSL 3 K)) v = v := by
  simp [slAct]

theorem slAct_mul (g h : ↥(StatedSL 3 K)) (v : Fin 3 → K) :
    slAct (g * h) v = slAct g (slAct h v) := by
  simp [slAct, Matrix.mulVec_mulVec]

theorem slAct_inv_slAct (g : ↥(StatedSL 3 K)) (v : Fin 3 → K) : slAct g⁻¹ (slAct g v) = v := by
  rw [← slAct_mul, inv_mul_cancel, slAct_one]

theorem slAct_slAct_inv (g : ↥(StatedSL 3 K)) (v : Fin 3 → K) : slAct g (slAct g⁻¹ v) = v := by
  rw [← slAct_mul, mul_inv_cancel, slAct_one]

theorem slAct_add (g : ↥(StatedSL 3 K)) (v w : Fin 3 → K) :
    slAct g (v + w) = slAct g v + slAct g w := Matrix.mulVec_add _ _ _

theorem slAct_sub (g : ↥(StatedSL 3 K)) (v w : Fin 3 → K) :
    slAct g (v - w) = slAct g v - slAct g w := Matrix.mulVec_sub _ _ _

theorem slAct_smul (g : ↥(StatedSL 3 K)) (c : K) (v : Fin 3 → K) :
    slAct g (c • v) = c • slAct g v := Matrix.mulVec_smul _ _ _

theorem slAct_zero (g : ↥(StatedSL 3 K)) : slAct g 0 = 0 := Matrix.mulVec_zero _

@[expose] def slLin (g : ↥(StatedSL 3 K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
  Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem slLin_apply (g : ↥(StatedSL 3 K)) (v : Fin 3 → K) : slLin g v = slAct g v := rfl

theorem slAct_injective (g : ↥(StatedSL 3 K)) : Function.Injective (slAct g) := fun v w h => by
  rw [← slAct_inv_slAct g v, h, slAct_inv_slAct]

theorem ext_slAct {g h : ↥(StatedSL 3 K)} (hgh : ∀ v, slAct g v = slAct h v) : g = h := by
  apply Subtype.ext
  apply Units.ext
  exact Matrix.ext_iff_mulVec.mpr hgh

@[expose] def axisSub (W : Submodule K (Fin 3 → K)) : Subgroup ↥(StatedSL 3 K) where
  carrier := {g | (∀ w ∈ W, slAct g w = w) ∧ ∀ v, slAct g v - v ∈ W}
  one_mem' := ⟨fun w _ => slAct_one w, fun v => by simp [slAct_one]⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w hw => by rw [slAct_mul, hh1 w hw, hg1 w hw], fun v => ?_⟩
    have : slAct (g * h) v - v = (slAct g (slAct h v) - slAct h v) + (slAct h v - v) := by
      rw [slAct_mul]; abel
    rw [this]
    exact W.add_mem (hg2 _) (hh2 v)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · have := slAct_inv_slAct g w
      rwa [hg1 w hw] at this
    · have h1 := hg2 (slAct g⁻¹ v)
      rw [slAct_slAct_inv] at h1
      have : slAct g⁻¹ v - v = -(v - slAct g⁻¹ v) := by abel
      rw [this]
      exact W.neg_mem h1

theorem axisSub_act {W : Submodule K (Fin 3 → K)} {g h : ↥(StatedSL 3 K)} (hg : g ∈ axisSub W)
    (hh : h ∈ axisSub W) (v : Fin 3 → K) :
    slAct (g * h) v = v + (slAct g v - v) + (slAct h v - v) := by
  rw [slAct_mul]
  have h1 : slAct g (slAct h v - v) = slAct h v - v := hg.1 _ (hh.2 v)
  rw [slAct_sub] at h1
  have : slAct g (slAct h v) = slAct h v - v + slAct g v := by
    rw [← h1]; abel
  rw [this]; abel

theorem axisSub_comm {W : Submodule K (Fin 3 → K)} {g h : ↥(StatedSL 3 K)} (hg : g ∈ axisSub W)
    (hh : h ∈ axisSub W) : g * h = h * g := by
  apply ext_slAct
  intro v
  rw [axisSub_act hg hh, axisSub_act hh hg]
  abel

theorem axisSub_mul_self [CharP K 2] {W : Submodule K (Fin 3 → K)} {g : ↥(StatedSL 3 K)}
    (hg : g ∈ axisSub W) : g * g = 1 := by
  apply ext_slAct
  intro v
  rw [axisSub_act hg hg, slAct_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]

@[expose] def fixK (D : Subgroup ↥(StatedSL 3 K)) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ g ∈ D, slAct g v = v}
  add_mem' := fun ha hb g hg => by rw [slAct_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => slAct_zero g
  smul_mem' := fun c v hv g hg => by rw [slAct_smul, hv g hg]

theorem mem_fixK {D : Subgroup ↥(StatedSL 3 K)} {v : Fin 3 → K} :
    v ∈ fixK D ↔ ∀ g ∈ D, slAct g v = v := Iff.rfl

theorem fixK_anti {D E : Subgroup ↥(StatedSL 3 K)} (h : D ≤ E) : fixK E ≤ fixK D :=
  fun _ hv g hg => hv g (h hg)

theorem fixK_ne_top {D : Subgroup ↥(StatedSL 3 K)} (hD : D ≠ ⊥) : fixK D ≠ ⊤ := by
  intro htop
  apply hD
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply ext_slAct
  intro v
  rw [slAct_one]
  exact (htop ▸ Submodule.mem_top : v ∈ fixK D) g hg

theorem le_fixK_axisSub (W : Submodule K (Fin 3 → K)) : W ≤ fixK (axisSub W) :=
  fun w hw _ hg => hg.1 w hw

theorem fixK_eq_of_le_axisSub {W : Submodule K (Fin 3 → K)} (hW : Module.finrank K W = 2)
    {B : Subgroup ↥(StatedSL 3 K)} (hB : B ≤ axisSub W) (hne : B ≠ ⊥) : fixK B = W := by
  have h1 : W ≤ fixK B := (le_fixK_axisSub W).trans (fixK_anti hB)
  have h2 : fixK B ≠ ⊤ := fixK_ne_top hne
  have h3 : Module.finrank K (fixK B) ≤ 2 := by
    by_contra hlt
    push Not at hlt
    apply h2
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (fixK B)
    rw [Module.finrank_fin_fun] at this ⊢
    omega
  exact (Submodule.eq_of_le_of_finrank_le h1 (by rw [hW]; exact h3)).symm

theorem le_axisSub_fixK [CharP K 2] {D : Subgroup ↥(StatedSL 3 K)}
    (hsq : ∀ g ∈ D, g * g = 1) (h2 : Module.finrank K (fixK D) = 2) : D ≤ axisSub (fixK D) := by
  intro g hg
  refine ⟨fun w hw => hw g hg, fun v => ?_⟩
  by_cases hg1 : g = 1
  · subst hg1; rw [slAct_one, sub_self]; exact (fixK D).zero_mem
  set N : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := slLin g - LinearMap.id with hN
  have hNapp : ∀ x, N x = slAct g x - x := fun x => rfl
  have hker : fixK D ≤ LinearMap.ker N := fun x hx => by
    rw [LinearMap.mem_ker, hNapp, hx g hg, sub_self]
  have hker' : LinearMap.ker N ≠ ⊤ := by
    intro htop
    apply hg1
    apply ext_slAct
    intro x
    have : x ∈ LinearMap.ker N := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hNapp, sub_eq_zero] at this
    rw [this, slAct_one]
  have hkerdim : Module.finrank K (LinearMap.ker N) ≤ 2 := by
    by_contra hlt
    push Not at hlt
    apply hker'
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (LinearMap.ker N)
    rw [Module.finrank_fin_fun] at this ⊢
    omega
  have heq : fixK D = LinearMap.ker N :=
    Submodule.eq_of_le_of_finrank_le hker (by rw [h2]; exact hkerdim)
  have hgg : slAct g (slAct g v) = v := by
    rw [← slAct_mul, hsq g hg, slAct_one]
  have hNN : N (N v) = 0 := by
    rw [hNapp, hNapp, slAct_sub, hgg]
    have : v - slAct g v - (slAct g v - v) = (v - slAct g v) + (v - slAct g v) := by abel
    rw [this, CharTwo.add_self_eq_zero]
  rw [heq]
  show N v ∈ LinearMap.ker N
  rw [LinearMap.mem_ker]
  exact hNN

theorem card_le_sq [CharP K 2] [Finite K] {D : Subgroup ↥(StatedSL 3 K)}
    (hsq : ∀ g ∈ D, g * g = 1) (hcomm : ∀ g ∈ D, ∀ h ∈ D, g * h = h * g) :
    Nat.card D ≤ Nat.card K ^ 2 := by
  have h := H.card_le_of_elemAbelian_GL3 (D.map (StatedSL 3 K).subtype)
    (by
      rintro _ ⟨g, hg, rfl⟩
      have := congrArg Subtype.val (hsq g hg)
      simpa using this)
    (by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
      have := congrArg Subtype.val (hcomm g hg h hh)
      simpa using this)
  rwa [Subgroup.card_map_of_injective (StatedSL 3 K).subtype_injective] at h

theorem card_axisSub_le [CharP K 2] [Finite K] (W : Submodule K (Fin 3 → K)) :
    Nat.card (axisSub W) ≤ Nat.card K ^ 2 :=
  card_le_sq (fun _ hg => axisSub_mul_self hg) (fun _ hg _ hh => axisSub_comm hg hh)

theorem eq_axisSub_fixK [CharP K 2] [Finite K] {D : Subgroup ↥(StatedSL 3 K)}
    (hsq : ∀ g ∈ D, g * g = 1) (h2 : Module.finrank K (fixK D) = 2)
    (hcard : Nat.card K ^ 2 ≤ Nat.card D) : D = axisSub (fixK D) :=
  Subgroup.eq_of_le_of_card_ge (le_axisSub_fixK hsq h2)
    ((card_axisSub_le _).trans hcard)

@[expose] noncomputable def transv (u φ : Fin 3 → K) (h : φ ⬝ᵥ u = 0) : ↥(StatedSL 3 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + vecMulVec u φ) (by
      rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, h, add_zero]
      exact one_ne_zero),
    H.SL3Pair.mem_statedSL_iff.2 (by
      show (1 + vecMulVec u φ).det = 1
      rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, h,
        add_zero])⟩

theorem slAct_transv (u φ : Fin 3 → K) (h : φ ⬝ᵥ u = 0) (v : Fin 3 → K) :
    slAct (transv u φ h) v = v + (φ ⬝ᵥ v) • u := by
  show (1 + vecMulVec u φ) *ᵥ v = v + (φ ⬝ᵥ v) • u
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem card_axisSub [CharP K 2] [Finite K] {W : Submodule K (Fin 3 → K)}
    (hW : Module.finrank K W = 2) : Nat.card (axisSub W) = Nat.card K ^ 2 := by
  classical
  refine le_antisymm (card_axisSub_le W) ?_
  have hWtop : W ≠ ⊤ := by
    intro htop
    have := congrArg (fun S : Submodule K (Fin 3 → K) => Module.finrank K S) htop
    simp only [finrank_top, Module.finrank_fin_fun] at this
    omega
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ W := by
    by_contra hall
    push Not at hall
    exact hWtop (eq_top_iff.2 fun v _ => hall v)
  obtain ⟨f, hfv, hWf⟩ := Submodule.exists_le_ker_of_notMem hv₀
  set φ : Fin 3 → K := fun i => f (Pi.single i 1) with hφ
  have hφf : ∀ x, φ ⬝ᵥ x = f x := by
    intro x
    conv_rhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, hφ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 1
    congr 1
    ext j
    simp [Pi.single_apply, eq_comm]
  have hφW : ∀ w ∈ W, φ ⬝ᵥ w = 0 := fun w hw => by rw [hφf]; exact hWf hw
  let F : ↥W → ↥(axisSub W) := fun w => ⟨transv (w : Fin 3 → K) φ (hφW w w.2), by
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · rw [slAct_transv, hφW x hx, zero_smul, add_zero]
    · rw [slAct_transv, add_sub_cancel_left]
      exact W.smul_mem _ w.2⟩
  have hF : Function.Injective F := by
    intro w w' hww'
    have h1 := congrArg (fun g : ↥(axisSub W) => slAct (g : ↥(StatedSL 3 K)) v₀) hww'
    simp only [F, slAct_transv] at h1
    have h2 : φ ⬝ᵥ v₀ ≠ 0 := by rw [hφf]; exact hfv
    apply Subtype.ext
    have := add_left_cancel h1
    exact smul_right_injective _ h2 this
  have hcardW : Nat.card ↥W = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hW]
  rw [← hcardW]
  exact Nat.card_le_card_of_injective F hF

@[expose] noncomputable def slMap (g : ↥(StatedSL 3 K)) (W : Submodule K (Fin 3 → K)) :
    Submodule K (Fin 3 → K) :=
  W.map (slLin g)

theorem mem_slMap {g : ↥(StatedSL 3 K)} {W : Submodule K (Fin 3 → K)} {v : Fin 3 → K} :
    v ∈ slMap g W ↔ slAct g⁻¹ v ∈ W := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [slLin_apply, slAct_inv_slAct]
    exact hw
  · intro hv
    exact ⟨_, hv, by rw [slLin_apply, slAct_slAct_inv]⟩

theorem finrank_slMap (g : ↥(StatedSL 3 K)) (W : Submodule K (Fin 3 → K)) :
    Module.finrank K (slMap g W) = Module.finrank K W :=
  LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (slLin g) (slAct_injective g) W).symm

theorem conj_mem_axisSub {W : Submodule K (Fin 3 → K)} {g h : ↥(StatedSL 3 K)}
    (hh : h ∈ axisSub W) : g * h * g⁻¹ ∈ axisSub (slMap g W) := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · rw [mem_slMap] at hw
    rw [slAct_mul, slAct_mul, hh.1 _ hw, slAct_slAct_inv]
  · rw [mem_slMap, slAct_mul, slAct_mul, slAct_sub, slAct_inv_slAct]
    exact hh.2 _

theorem map_conj_axisSub (g : ↥(StatedSL 3 K)) (W : Submodule K (Fin 3 → K)) :
    (axisSub W).map (MulAut.conj g).toMonoidHom = axisSub (slMap g W) := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact conj_mem_axisSub hh
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := conj_mem_axisSub (g := g⁻¹) hx
    rw [inv_inv] at this
    have hW : slMap g⁻¹ (slMap g W) = W := by
      ext v
      rw [mem_slMap, mem_slMap, inv_inv, slAct_inv_slAct]
    rwa [hW] at this

theorem finrank_le_two_of_ne_top {S : Submodule K (Fin 3 → K)} (hS : S ≠ ⊤) :
    Module.finrank K S ≤ 2 := by
  by_contra hlt
  push Not at hlt
  apply hS
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le S
  rw [Module.finrank_fin_fun] at this ⊢
  omega

theorem exists_slMap_eq {W W' : Submodule K (Fin 3 → K)} (hW : Module.finrank K W = 2)
    (hW' : Module.finrank K W' = 2) : ∃ g : ↥(StatedSL 3 K), slMap g W = W' := by
  classical
  by_cases heq : W = W'
  · exact ⟨1, by
      ext v
      rw [mem_slMap, inv_one, slAct_one, heq]⟩
  have hex : ∀ {X Y : Submodule K (Fin 3 → K)}, Module.finrank K X = 2 →
      Module.finrank K Y = 2 → X ≠ Y → ∃ x ∈ X, x ∉ Y := by
    intro X Y hX hY hXY
    by_contra hall
    push Not at hall
    exact hXY (Submodule.eq_of_le_of_finrank_le (fun x hx => hall x hx) (by rw [hX, hY]))
  obtain ⟨w, hwW, hwW'⟩ := hex hW hW' heq
  obtain ⟨w', hw'W', hw'W⟩ := hex hW' hW (Ne.symm heq)
  set ℓ := W ⊓ W' with hℓ
  have hsup : W ⊔ W' = ⊤ := by
    by_contra hne
    have h1 := finrank_le_two_of_ne_top hne
    have h2 : W = W ⊔ W' := Submodule.eq_of_le_of_finrank_le le_sup_left (by rw [hW]; exact h1)
    exact hw'W (h2 ▸ Submodule.mem_sup_right hw'W')
  have hℓdim : Module.finrank K ℓ = 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W W'
    have h2 : Module.finrank K ↥(W ⊔ W') = 3 := by
      rw [hsup, finrank_top, Module.finrank_fin_fun]
    rw [h2, hW, hW'] at h1
    have h3 : Module.finrank K ↥(W ⊓ W') = 1 := by omega
    exact h3
  set c := w' - w with hc
  set H := ℓ ⊔ Submodule.span K {c} with hH
  have hwH : w ∉ H := by
    intro hw
    obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.1 hw
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 hy
    by_cases hμ : μ = 0
    · rw [hμ, zero_smul, add_zero] at hly
      exact hwW' (hly ▸ hl.2)
    · have h2 : μ • c = w - l := by rw [← hly]; abel
      have h3 : c = μ⁻¹ • (w - l) := by rw [← h2, smul_smul, inv_mul_cancel₀ hμ, one_smul]
      have hcW : c ∈ W := h3 ▸ W.smul_mem _ (W.sub_mem hwW hl.1)
      apply hw'W
      have : w' = c + w := by rw [hc]; abel
      rw [this]
      exact W.add_mem hcW hwW
  obtain ⟨f, hfw, hHf⟩ := Submodule.exists_le_ker_of_notMem hwH
  set φ : Fin 3 → K := fun i => (f w)⁻¹ * f (Pi.single i 1) with hφ
  have hφf : ∀ x, φ ⬝ᵥ x = (f w)⁻¹ * f x := by
    intro x
    conv_rhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, hφ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (fun j => if i = j then (1 : K) else 0) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply, eq_comm]
    rw [this]
    ring
  have hφH : ∀ x ∈ H, φ ⬝ᵥ x = 0 := fun x hx => by
    rw [hφf, LinearMap.mem_ker.1 (hHf hx), mul_zero]
  have hφc : φ ⬝ᵥ c = 0 := hφH c (Submodule.mem_sup_right (Submodule.mem_span_singleton_self c))
  have hφw : φ ⬝ᵥ w = 1 := by rw [hφf, inv_mul_cancel₀ hfw]
  set ker := LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Fin 1) j => φ j)) with hker
  have hmemker : ∀ x, x ∈ ker ↔ φ ⬝ᵥ x = 0 := by
    intro x
    rw [hker, LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · intro h0
      have := congrFun h0 0
      simpa [Matrix.mulVec, dotProduct] using this
    · intro h0
      funext i
      fin_cases i
      simpa [Matrix.mulVec, dotProduct] using h0
  have hWker : W ⊓ ker = ℓ := by
    have hle : ℓ ≤ W ⊓ ker := fun x hx => ⟨hx.1, (hmemker x).2 (hφH x (Submodule.mem_sup_left hx))⟩
    have hne : W ⊓ ker ≠ W := by
      intro h
      have : w ∈ W ⊓ ker := by rw [h]; exact hwW
      rw [(hmemker w).1 this.2] at hφw
      exact zero_ne_one hφw
    have hlt : W ⊓ ker < W := lt_of_le_of_ne inf_le_left hne
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hW] at h1
    exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hℓdim]; omega)).symm
  set t := transv c φ hφc with ht
  refine ⟨t, ?_⟩
  have hle : slMap t W ≤ W' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [slLin_apply, ht, slAct_transv]
    set y := x - (φ ⬝ᵥ x) • w with hy
    have hyW : y ∈ W := W.sub_mem hx (W.smul_mem _ hwW)
    have hyk : y ∈ ker := by
      rw [hmemker, hy, dotProduct_sub, dotProduct_smul, hφw, smul_eq_mul, mul_one, sub_self]
    have hyℓ : y ∈ ℓ := hWker ▸ ⟨hyW, hyk⟩
    have : x + (φ ⬝ᵥ x) • c = y + (φ ⬝ᵥ x) • w' := by
      rw [hy, hc, smul_sub]; abel
    rw [this]
    exact W'.add_mem hyℓ.2 (W'.smul_mem _ hw'W')
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_slMap, hW, hW'])

@[expose] def coordHyp (i : Fin 3) : Submodule K (Fin 3 → K) :=
  LinearMap.ker (LinearMap.proj i : (Fin 3 → K) →ₗ[K] K)

theorem mem_coordHyp {i : Fin 3} {v : Fin 3 → K} : v ∈ coordHyp i ↔ v i = 0 := Iff.rfl

theorem finrank_coordHyp (i : Fin 3) : Module.finrank K (coordHyp (K := K) i) = 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj i : (Fin 3 → K) →ₗ[K] K)
  have h2 : LinearMap.range (LinearMap.proj i : (Fin 3 → K) →ₗ[K] K) = ⊤ :=
    LinearMap.range_eq_top.2 fun c => ⟨Pi.single i c, by simp⟩
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  show Module.finrank K (LinearMap.ker (LinearMap.proj i : (Fin 3 → K) →ₗ[K] K)) = 2
  omega

theorem mem_axisSub_coordHyp {i j : Fin 3} (hij : j ≠ i) {g : ↥(StatedSL 3 K)}
    (hg : ∀ v, slAct g v = v + Pi.single j (v i)) : g ∈ axisSub (coordHyp i) := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · rw [hg, mem_coordHyp.1 hw, Pi.single_zero, add_zero]
  · rw [hg, add_sub_cancel_left, mem_coordHyp, Pi.single_apply]
    exact ite_eq_right_iff.2 fun h => absurd h.symm hij

end B5

end CFSG.Quasithin
