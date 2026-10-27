module

public import CFSG.Timmesfeld.Bridge.RootStructR2OneTorus

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped Matrix commutatorElement

namespace RootOne

variable {G : Type} [Group G] {D : Set G}

theorem biadd_eq_zero {K Q : Type*} [Field K] [AddCommGroup Q]
    (b : (Fin 2 → K) → (Fin 2 → K) → Q)
    (hadd₁ : ∀ v v' w, b (v + v') w = b v w + b v' w)
    (hadd₂ : ∀ v w w', b v (w + w') = b v w + b v w')
    {c : K} (hc1 : c ≠ 1)
    (hinv : ∀ r s r' s' : K, b ![c * r, s] ![c * r', s'] = b ![r, s] ![r', s'])
    (h11 : ∀ r r' : K, b ![r, 0] ![r', 0] = 0) (h22 : ∀ s s' : K, b ![0, s] ![0, s'] = 0)
    (v w : Fin 2 → K) : b v w = 0 := by
  have hc : c - 1 ≠ 0 := sub_ne_zero.2 hc1
  have hsplit : ∀ r : K, (![c * (r / (c - 1)), 0] : Fin 2 → K) = ![r / (c - 1), 0] + ![r, 0] := by
    intro r
    rw [Higman.vec_add, add_zero]
    congr 2
    field_simp
    ring
  have h12 : ∀ r s : K, b ![r, 0] ![0, s] = 0 := by
    intro r s
    have h1 := hinv (r / (c - 1)) 0 0 s
    rw [mul_zero, hsplit, hadd₁] at h1
    exact add_eq_left.mp h1
  have h21 : ∀ s r : K, b ![0, s] ![r, 0] = 0 := by
    intro s r
    have h1 := hinv 0 s (r / (c - 1)) 0
    rw [mul_zero, hsplit, hadd₂] at h1
    exact add_eq_left.mp h1
  rw [Higman.eq_vec v, Higman.eq_vec w, Higman.vec_eq_add (v 0), Higman.vec_eq_add (w 0), hadd₁,
    hadd₂, hadd₂, h11, h12, h21, h22]
  simp

namespace LineConf

variable {a d x y : G} (C : LineConf D a d x y)
include C

theorem commutator_mem_T {n : G} (hn : n ∈ lineN D a d) {m : G} (hm : m ∈ lineN₀ D a d) :
    n * m * n⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
  have hR := nCoreCommutatorInRoot_of_hyp C.setting.hyp C.setting.closure
  obtain ⟨na, hna, nd, hnd, rfl⟩ := C.exists_mul_eq hn
  have h1 : na * m * na⁻¹ * m⁻¹ ∈ rootGroup D a :=
    hR a C.ha na (Subgroup.mem_inf.1 hna).1 m (Subgroup.mem_inf.1 hm).1
  have h2 : nd * m * nd⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d :=
    Subgroup.mem_sup_right (hR d C.hd nd (Subgroup.mem_inf.1 hnd).1 m (Subgroup.mem_inf.1 hm).2)
  have e : na * nd * m * (na * nd)⁻¹ * m⁻¹ =
      na * (nd * m * nd⁻¹ * m⁻¹) * na⁻¹ * (na * m * na⁻¹ * m⁻¹) := by group
  rw [e, (C.commute_of_mem_Na hna h2).eq, mul_inv_cancel_right]
  exact Subgroup.mul_mem _ h2 (Subgroup.mem_sup_left h1)

theorem commute_of_mem_lineN₀ {m m' : G} (hm : m ∈ lineN₀ D a d) (hm' : m' ∈ lineN₀ D a d) :
    Commute m m' := by
  have hR := nCoreCommutatorInRoot_of_hyp C.setting.hyp C.setting.closure
  have h1 := hR a C.ha m (Subgroup.mem_inf.1 hm).1 m' (Subgroup.mem_inf.1 hm').1
  have h2 := hR d C.hd m (Subgroup.mem_inf.1 hm).2 m' (Subgroup.mem_inf.1 hm').2
  have hne : rootSet D a ≠ rootSet D d := fun h => C.hdT (h ▸ mem_rootSet_self C.hd)
  have h3 : m * m' * m⁻¹ * m'⁻¹ ∈ rootGroup D a ⊓ rootGroup D d := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [rootGroup_inf_eq_bot_of_rootClosure C.root C.setting.closure C.ha C.hd hne,
    Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact h3)

theorem conj_mem_lineN₀_of_commute {g : G} (hgX : ∀ u ∈ rootGroup D x ⊔ rootGroup D y, Commute g u)
    (hgT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, g * t * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d)
    {m : G} (hm : m ∈ lineN₀ D a d) : g * m * g⁻¹ ∈ lineN₀ D a d := by
  have hclass := C.isClass
  have hD := C.root
  have hconj : ∀ {p u : G}, p ∈ D → p ∈ rootGroup D a ⊔ rootGroup D d → Commute p u →
      Commute g u → Commute (g * p * g⁻¹) u := by
    intro p u _ _ hpu hgu
    have := (Commute.conj_iff g).2 hpu
    rwa [hgu.eq, mul_inv_cancel_right] at this
  have ha' : g * a * g⁻¹ ∈ rootSet D a := by
    refine mem_rootSet_of_mem_rootGroup_of_ne_one hD C.setting.closure C.ha
      (C.mem_rootGroup_a_of_commute (hgT a (left_mem_line C.ha))
        (hconj C.ha (left_mem_line C.ha) C.hax (hgX x C.x_mem_X))) ?_
    intro h1
    exact hD.ne_one C.ha (by simpa [mul_assoc] using congrArg (fun w => g⁻¹ * w * g) h1)
  have hd' : g * d * g⁻¹ ∈ rootSet D d := by
    refine mem_rootSet_of_mem_rootGroup_of_ne_one hD C.setting.closure C.hd
      (C.mem_rootGroup_d_of_commute (hgT d (right_mem_line C.hd))
        (hconj C.hd (right_mem_line C.hd) C.hdy (hgX y C.y_mem_X))) ?_
    intro h1
    exact hD.ne_one C.hd (by simpa [mul_assoc] using congrArg (fun w => g⁻¹ * w * g) h1)
  have h1 := conj_mem_nCore_conj hclass (Subgroup.mem_inf.1 hm).1 g
  have h2 := conj_mem_nCore_conj hclass (Subgroup.mem_inf.1 hm).2 g
  rw [C.setting.nCore_eq_of_mem_rootSet C.ha ha'] at h1
  rw [C.setting.nCore_eq_of_mem_rootSet C.hd hd'] at h2
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

end LineConf

namespace ModConf

variable {a d x y : G} {C : LineConf D a d x y} {K : Type*} [Field K]
  {φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K}
  {θ₀ θ₁ : (Fin 2 → K) → G} (M : ModConf C φ θ₀ θ₁)
include M

theorem conj_mul_inv_mem_T {g : G} (hg : g ∈ rootGroup D x ⊔ rootGroup D y) {m : G}
    (hm : m ∈ lineN₀ D a d) : g * m * g⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
  have hR := nCoreCommutatorInRoot_of_hyp C.setting.hyp C.setting.closure
  have hxM : rootGroup D x ≤ nCore D a :=
    le_sup_right.trans (C.setting.sup_rootGroup_le_nCore C.ha C.hx C.hax)
  have hyM : rootGroup D y ≤ nCore D d :=
    le_sup_right.trans (C.setting.sup_rootGroup_le_nCore C.hd C.hy C.hdy)
  have hX : rootGroup D x ⊔ rootGroup D y = Subgroup.closure (rootSet D x ∪ rootSet D y) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hX] at hg
  induction hg using Subgroup.closure_induction generalizing m with
  | mem e he =>
    rcases he with he | he
    · exact Subgroup.mem_sup_left
        (hR a C.ha e (hxM (rootSet_subset_rootGroup D x he)) m (Subgroup.mem_inf.1 hm).1)
    · exact Subgroup.mem_sup_right
        (hR d C.hd e (hyM (rootSet_subset_rootGroup D y he)) m (Subgroup.mem_inf.1 hm).2)
  | one => simp
  | mul g₁ g₂ hg₁ _ ih₁ ih₂ =>
    have e : g₁ * g₂ * m * (g₁ * g₂)⁻¹ * m⁻¹ =
        g₁ * (g₂ * m * g₂⁻¹ * m⁻¹) * g₁⁻¹ * (g₁ * m * g₁⁻¹ * m⁻¹) := by group
    rw [e]
    rw [← hX] at hg₁
    exact Subgroup.mul_mem _ (C.conj_mem_T hg₁ (ih₂ hm)) (ih₁ hm)
  | inv g hg ih =>
    rw [← hX] at hg
    have hm' : g⁻¹ * m * g⁻¹⁻¹ ∈ lineN₀ D a d := M.conj_N₀ _ (Subgroup.inv_mem _ hg) m hm
    have h1 := ih hm'
    have e : g⁻¹ * m * g⁻¹⁻¹ * m⁻¹ = (g * (g⁻¹ * m * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * m * g⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    rw [e]
    exact Subgroup.inv_mem _ h1

theorem comm_mem_T [CharP K 2] {h : G} (hhN : ∀ n ∈ lineN D a d, h * n * h⁻¹ ∈ lineN D a d)
    (hhN₀ : ∀ m ∈ lineN₀ D a d, h * m * h⁻¹ ∈ lineN₀ D a d)
    (htriv : ∀ m ∈ lineN₀ D a d, h * m * h⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d)
    {μ : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (hμ : ∀ v, (θ₁ (μ • v))⁻¹ * (h * θ₁ v * h⁻¹) ∈ lineN₀ D a d)
    {n n' : G} (hn : n ∈ lineN D a d) (hn' : n' ∈ lineN D a d) :
    ⁅n, n'⁆ ∈ rootGroup D a ⊔ rootGroup D d := by
  classical
  have := C.finite
  have hR := nCoreCommutatorInRoot_of_hyp C.setting.hyp C.setting.closure
  have hTN₀ := C.T_le_lineN₀
  have hN₀N : lineN₀ D a d ≤ lineN D a d := lineN₀_le_lineN D a d
  have hθ₁N : ∀ v, θ₁ v ∈ lineN D a d := M.nat₁.mem
  have hcommN : ∀ {n n' : G}, n ∈ lineN D a d → n' ∈ lineN D a d → ⁅n, n'⁆ ∈ lineN₀ D a d :=
    fun hn hn' => by rw [commutatorElement_def]; exact M.comm _ hn _ hn'
  let instN₀ : CommGroup ↥(lineN₀ D a d) :=
    { (inferInstance : Group ↥(lineN₀ D a d)) with
      mul_comm := fun m m' => Subtype.ext (C.commute_of_mem_lineN₀ m.2 m'.2).eq }
  let T' : Subgroup ↥(lineN₀ D a d) := (rootGroup D a ⊔ rootGroup D d).subgroupOf (lineN₀ D a d)
  let mk : G → Additive (↥(lineN₀ D a d) ⧸ T') := fun g =>
    if hg : g ∈ lineN₀ D a d then Additive.ofMul (QuotientGroup.mk ⟨g, hg⟩) else 0
  have hmk : ∀ {g : G} (hg : g ∈ lineN₀ D a d),
      mk g = Additive.ofMul (QuotientGroup.mk ⟨g, hg⟩ : ↥(lineN₀ D a d) ⧸ T') :=
    fun hg => by simp [mk, hg]
  have hmk_mul : ∀ {g g' : G}, g ∈ lineN₀ D a d → g' ∈ lineN₀ D a d →
      mk (g * g') = mk g + mk g' := by
    intro g g' hg hg'
    rw [hmk (Subgroup.mul_mem _ hg hg'), hmk hg, hmk hg']
    rfl
  have hmk_inv : ∀ {g : G}, g ∈ lineN₀ D a d → mk g⁻¹ = -mk g := by
    intro g hg
    rw [hmk (Subgroup.inv_mem _ hg), hmk hg]
    rfl
  have hmk_zero : ∀ {g : G} (hg : g ∈ lineN₀ D a d),
      mk g = 0 ↔ g ∈ rootGroup D a ⊔ rootGroup D d := by
    intro g hg
    rw [hmk hg]
    change (QuotientGroup.mk ⟨g, hg⟩ : ↥(lineN₀ D a d) ⧸ T') = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmk_T : ∀ {g : G}, g ∈ rootGroup D a ⊔ rootGroup D d → mk g = 0 :=
    fun hg => (hmk_zero (hTN₀ hg)).2 hg
  have hc1 : ∀ {n m n' : G}, n ∈ lineN D a d → m ∈ lineN₀ D a d → n' ∈ lineN D a d →
      mk ⁅n * m, n'⁆ = mk ⁅n, n'⁆ := by
    intro n m n' hn hm hn'
    have ht : ⁅m, n'⁆ ∈ rootGroup D a ⊔ rootGroup D d := by
      have := Subgroup.inv_mem _ (C.commutator_mem_T hn' hm)
      rwa [show (n' * m * n'⁻¹ * m⁻¹)⁻¹ = ⁅m, n'⁆ by rw [commutatorElement_def]; group] at this
    have e : ⁅n * m, n'⁆ = (n * ⁅m, n'⁆ * n⁻¹) * ⁅n, n'⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, (C.commute_of_mem_lineN hn ht).eq, mul_inv_cancel_right,
      hmk_mul (hTN₀ ht) (hcommN hn hn'), hmk_T ht, zero_add]
  have hc2 : ∀ {n₁ n₂ n' : G}, n₁ ∈ lineN D a d → n₂ ∈ lineN D a d → n' ∈ lineN D a d →
      mk ⁅n₁ * n₂, n'⁆ = mk ⁅n₁, n'⁆ + mk ⁅n₂, n'⁆ := by
    intro n₁ n₂ n' hn₁ hn₂ hn'
    have hc := hcommN hn₂ hn'
    have ht := C.commutator_mem_T hn₁ hc
    have e : ⁅n₁ * n₂, n'⁆ = (n₁ * ⁅n₂, n'⁆ * n₁⁻¹ * ⁅n₂, n'⁆⁻¹) * ⁅n₂, n'⁆ * ⁅n₁, n'⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hmk_mul (Subgroup.mul_mem _ (hTN₀ ht) hc) (hcommN hn₁ hn'),
      hmk_mul (hTN₀ ht) hc, hmk_T ht, zero_add, add_comm]
  have hc3 : ∀ {n n' : G}, n ∈ lineN D a d → n' ∈ lineN D a d → mk ⁅n', n⁆ = -mk ⁅n, n'⁆ := by
    intro n n' hn hn'
    rw [show ⁅n', n⁆ = ⁅n, n'⁆⁻¹ by simp only [commutatorElement_def]; group,
      hmk_inv (hcommN hn hn')]
  have hc1' : ∀ {n n' m : G}, n ∈ lineN D a d → n' ∈ lineN D a d → m ∈ lineN₀ D a d →
      mk ⁅n, n' * m⁆ = mk ⁅n, n'⁆ := by
    intro n n' m hn hn' hm
    rw [hc3 (Subgroup.mul_mem _ hn' (hN₀N hm)) hn, hc1 hn' hm hn, ← hc3 hn' hn]
  set b : (Fin 2 → K) → (Fin 2 → K) → Additive (↥(lineN₀ D a d) ⧸ T') :=
    fun v w => mk ⁅θ₁ v, θ₁ w⁆ with hb
  have hsplit : ∀ v v', θ₁ (v + v') = θ₁ v * θ₁ v' * ((θ₁ v * θ₁ v')⁻¹ * θ₁ (v + v')) :=
    fun v v' => by group
  have hadd₁ : ∀ v v' w, b (v + v') w = b v w + b v' w := by
    intro v v' w
    simp only [hb]
    rw [hsplit, hc1 (Subgroup.mul_mem _ (hθ₁N v) (hθ₁N v')) (M.nat₁.map_add v v') (hθ₁N w),
      hc2 (hθ₁N v) (hθ₁N v') (hθ₁N w)]
  have hadd₂ : ∀ v w w', b v (w + w') = b v w + b v w' := by
    intro v w w'
    simp only [hb]
    rw [hc3 (hθ₁N (w + w')) (hθ₁N v), hc3 (hθ₁N w) (hθ₁N v), hc3 (hθ₁N w') (hθ₁N v), hsplit,
      hc1 (Subgroup.mul_mem _ (hθ₁N w) (hθ₁N w')) (M.nat₁.map_add w w') (hθ₁N v),
      hc2 (hθ₁N w) (hθ₁N w') (hθ₁N v), neg_add]
  set tS : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![μ, 0; 0, μ⁻¹], by rw [Matrix.det_fin_two_of]; field_simp; ring⟩ with htS
  set t := φ.symm tS with ht
  have htX : (t : G) ∈ rootGroup D x ⊔ rootGroup D y := t.2
  have hφt : φ t = tS := by rw [ht, MulEquiv.apply_symm_apply]
  have hgθ : ∀ r s : K, ∃ m ∈ lineN₀ D a d,
      θ₁ ![μ ^ 2 * r, s] = h * (t : G) * θ₁ ![r, s] * (h * (t : G))⁻¹ * m := by
    intro r s
    have h1 := M.nat₁.map_mulVec t ![r, s]
    rw [hφt] at h1
    have hvec : (tS : Matrix (Fin 2) (Fin 2) K) *ᵥ ![r, s] = ![μ * r, μ⁻¹ * s] := by
      rw [htS]
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hvec] at h1
    have h2 := hμ ![μ * r, μ⁻¹ * s]
    have hvec2 : μ • (![μ * r, μ⁻¹ * s] : Fin 2 → K) = ![μ ^ 2 * r, s] := by
      ext i
      fin_cases i <;> simp [pow_two, mul_assoc, hμ0]
    rw [hvec2] at h2
    refine ⟨(h * ((θ₁ ![μ * r, μ⁻¹ * s])⁻¹ * ((t : G) * θ₁ ![r, s] * (t : G)⁻¹)) * h⁻¹)⁻¹ *
      ((θ₁ ![μ ^ 2 * r, s])⁻¹ * (h * θ₁ ![μ * r, μ⁻¹ * s] * h⁻¹))⁻¹,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hhN₀ _ h1)) (Subgroup.inv_mem _ h2), ?_⟩
    group
  have hgtriv : ∀ {m : G}, m ∈ lineN₀ D a d →
      mk (h * (t : G) * m * (h * (t : G))⁻¹) = mk m := by
    intro m hm
    have h1 := M.conj_mul_inv_mem_T htX hm
    have h2 := htriv _ (M.conj_N₀ _ htX m hm)
    have e : h * (t : G) * m * (h * (t : G))⁻¹ =
        (h * ((t : G) * m * (t : G)⁻¹) * h⁻¹ * ((t : G) * m * (t : G)⁻¹)⁻¹) *
          ((t : G) * m * (t : G)⁻¹ * m⁻¹) * m := by group
    rw [e, hmk_mul (Subgroup.mul_mem _ (hTN₀ h2) (hTN₀ h1)) hm,
      hmk_mul (hTN₀ h2) (hTN₀ h1), hmk_T h1, hmk_T h2, zero_add, zero_add]
  have hgN : ∀ v, h * (t : G) * θ₁ v * (h * (t : G))⁻¹ ∈ lineN D a d := by
    intro v
    have h1 := hhN _ (M.conj_N _ htX _ (hθ₁N v))
    rwa [show h * ((t : G) * θ₁ v * (t : G)⁻¹) * h⁻¹ = h * (t : G) * θ₁ v * (h * (t : G))⁻¹ by
      group] at h1
  have hinv : ∀ r s r' s' : K, b ![μ ^ 2 * r, s] ![μ ^ 2 * r', s'] = b ![r, s] ![r', s'] := by
    intro r s r' s'
    simp only [hb]
    obtain ⟨m, hm, hm1⟩ := hgθ r s
    obtain ⟨m', hm', hm2⟩ := hgθ r' s'
    rw [hm1, hm2, hc1 (hgN _) hm (Subgroup.mul_mem _ (hgN _) (hN₀N hm')),
      hc1' (hgN _) (hgN _) hm',
      show ⁅h * (t : G) * θ₁ ![r, s] * (h * (t : G))⁻¹, h * (t : G) * θ₁ ![r', s'] *
        (h * (t : G))⁻¹⁆ = h * (t : G) * ⁅θ₁ ![r, s], θ₁ ![r', s']⁆ * (h * (t : G))⁻¹ by
        simp only [commutatorElement_def]; group,
      hgtriv (hcommN (hθ₁N _) (hθ₁N _))]
  have hμ2 : μ ^ 2 ≠ 1 := fun h2 => hμ1 (eq_one_of_sq_eq_one h2)
  have h11 : ∀ r r' : K, b ![r, 0] ![r', 0] = 0 := by
    intro r r'
    simp only [hb]
    refine hmk_T (Subgroup.mem_sup_left ?_)
    rw [commutatorElement_def]
    exact hR a C.ha _ (Subgroup.mem_inf.1 (M.θ₁_a r)).1 _ (Subgroup.mem_inf.1 (M.θ₁_a r')).1
  have h22 : ∀ s s' : K, b ![0, s] ![0, s'] = 0 := by
    intro s s'
    simp only [hb]
    refine hmk_T (Subgroup.mem_sup_right ?_)
    rw [commutatorElement_def]
    exact hR d C.hd _ (Subgroup.mem_inf.1 (M.θ₁_d s)).1 _ (Subgroup.mem_inf.1 (M.θ₁_d s')).1
  have hb0 := biadd_eq_zero b hadd₁ hadd₂ hμ2 hinv h11 h22
  obtain ⟨v, hv⟩ := M.nat₁.exists_eq n hn
  obtain ⟨w, hw⟩ := M.nat₁.exists_eq n' hn'
  have e1 : n = θ₁ v * ((θ₁ v)⁻¹ * n) := by group
  have e2 : n' = θ₁ w * ((θ₁ w)⁻¹ * n') := by group
  refine (hmk_zero (hcommN hn hn')).1 ?_
  rw [e1, e2, hc1 (hθ₁N v) hv (Subgroup.mul_mem _ (hθ₁N w) (hN₀N hw)), hc1' (hθ₁N v) (hθ₁N w) hw]
  exact hb0 v w

theorem false_of_trivial_mod_T [Finite K] [CharP K 2] (hK2 : 2 < Nat.card K) {h : G}
    (hhX : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute h g)
    (hhN : ∀ n ∈ lineN D a d, h * n * h⁻¹ ∈ lineN D a d)
    (hhN₀ : ∀ m ∈ lineN₀ D a d, h * m * h⁻¹ ∈ lineN₀ D a d)
    (htriv : ∀ m ∈ lineN₀ D a d, h * m * h⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d)
    {μ : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (hμ : ∀ v, (θ₁ (μ • v))⁻¹ * (h * θ₁ v * h⁻¹) ∈ lineN₀ D a d) : False := by
  classical
  have := C.finite
  have hD := C.root
  have hTN₀ := C.T_le_lineN₀
  have hN₀N : lineN₀ D a d ≤ lineN D a d := lineN₀_le_lineN D a d
  have hθ₁N : ∀ v, θ₁ v ∈ lineN D a d := M.nat₁.mem
  have hNT : ∀ {n t : G}, n ∈ lineN D a d → t ∈ rootGroup D a ⊔ rootGroup D d → Commute n t :=
    fun hn ht => C.commute_of_mem_lineN hn ht
  have hcomm : ∀ {n n' : G}, n ∈ lineN D a d → n' ∈ lineN D a d →
      ⁅n, n'⁆ ∈ rootGroup D a ⊔ rootGroup D d := fun hn hn' =>
    M.comm_mem_T hhN hhN₀ htriv hμ0 hμ1 hμ hn hn'
  set f : G → G := fun n => h * n * h⁻¹ * n⁻¹ with hf
  have hfN : ∀ {n : G}, n ∈ lineN D a d → f n ∈ lineN D a d := fun hn =>
    Subgroup.mul_mem _ (hhN _ hn) (Subgroup.inv_mem _ hn)
  have hfmul : ∀ {n n' : G}, n ∈ lineN D a d → n' ∈ lineN D a d →
      (f n * f n')⁻¹ * f (n * n') ∈ rootGroup D a ⊔ rootGroup D d := by
    intro n n' hn hn'
    have hp : h * n' * h⁻¹ ∈ lineN D a d := hhN _ hn'
    have h1 := hcomm (Subgroup.inv_mem _ hp) hn
    have h2 := hcomm hn' hn
    have e : (f n * f n')⁻¹ * f (n * n') =
        n' * ⁅(h * n' * h⁻¹)⁻¹, n⁆ * n'⁻¹ * ⁅n', n⁆ := by
      simp only [hf, commutatorElement_def]; group
    rw [e, (hNT hn' h1).eq, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ h1 h2
  have hfN₀ : ∀ {m : G}, m ∈ lineN₀ D a d → f m ∈ rootGroup D a ⊔ rootGroup D d :=
    fun hm => htriv _ hm
  have hfmulN₀ : ∀ {n m : G}, n ∈ lineN D a d → m ∈ lineN₀ D a d →
      (f n)⁻¹ * f (n * m) ∈ rootGroup D a ⊔ rootGroup D d := by
    intro n m hn hm
    have h1 := hfmul hn (hN₀N hm)
    have h2 := hfN₀ hm
    have e : (f n)⁻¹ * f (n * m) = f m * ((f n * f m)⁻¹ * f (n * m)) := by
      rw [show f m * ((f n * f m)⁻¹ * f (n * m)) = f m * (f m)⁻¹ * (f n)⁻¹ * f (n * m) by group,
        mul_inv_cancel, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ h2 h1
  have hμ1' : μ - 1 ≠ 0 := sub_ne_zero.2 hμ1
  set θ' : (Fin 2 → K) → G := fun v => f (θ₁ ((μ - 1)⁻¹ • v)) with hθ'
  have hθ'def : ∀ v, θ' v = f (θ₁ ((μ - 1)⁻¹ • v)) := fun v => rfl
  have hθ'N : ∀ v, θ' v ∈ lineN D a d := fun v => hfN (hθ₁N _)
  have hfθ : ∀ u, (θ₁ ((μ - 1) • u))⁻¹ * f (θ₁ u) ∈ lineN₀ D a d := by
    intro u
    have h1 := hμ u
    have h2 := M.nat₁.map_add ((μ - 1) • u) u
    rw [show (μ - 1) • u + u = μ • u by rw [sub_smul, one_smul, sub_add_cancel]] at h2
    have e : (θ₁ ((μ - 1) • u))⁻¹ * f (θ₁ u) =
        θ₁ u * (((θ₁ ((μ - 1) • u) * θ₁ u)⁻¹ * θ₁ (μ • u)) *
          ((θ₁ (μ • u))⁻¹ * (h * θ₁ u * h⁻¹))) * (θ₁ u)⁻¹ := by
      simp only [hf]; group
    rw [e]
    exact M.normal _ (hθ₁N u) _ (Subgroup.mul_mem _ h2 h1)
  have hθ'cls : ∀ v, (θ₁ v)⁻¹ * θ' v ∈ lineN₀ D a d := by
    intro v
    have := hfθ ((μ - 1)⁻¹ • v)
    rwa [smul_smul, mul_inv_cancel₀ hμ1', one_smul] at this
  have hθ'add : ∀ v w, (θ' v * θ' w)⁻¹ * θ' (v + w) ∈ rootGroup D a ⊔ rootGroup D d := by
    intro v w
    have huv : (μ - 1)⁻¹ • (v + w) = (μ - 1)⁻¹ • v + (μ - 1)⁻¹ • w := smul_add _ _ _
    have hm := M.nat₁.map_add ((μ - 1)⁻¹ • v) ((μ - 1)⁻¹ • w)
    have h1 := hfmulN₀ (Subgroup.mul_mem _ (hθ₁N ((μ - 1)⁻¹ • v)) (hθ₁N ((μ - 1)⁻¹ • w))) hm
    rw [mul_inv_cancel_left] at h1
    have h2 := hfmul (hθ₁N ((μ - 1)⁻¹ • v)) (hθ₁N ((μ - 1)⁻¹ • w))
    rw [hθ'def, hθ'def, hθ'def, huv]
    have e : (f (θ₁ ((μ - 1)⁻¹ • v)) * f (θ₁ ((μ - 1)⁻¹ • w)))⁻¹ *
        f (θ₁ ((μ - 1)⁻¹ • v + (μ - 1)⁻¹ • w)) =
        ((f (θ₁ ((μ - 1)⁻¹ • v)) * f (θ₁ ((μ - 1)⁻¹ • w)))⁻¹ *
          f (θ₁ ((μ - 1)⁻¹ • v) * θ₁ ((μ - 1)⁻¹ • w))) *
        ((f (θ₁ ((μ - 1)⁻¹ • v) * θ₁ ((μ - 1)⁻¹ • w)))⁻¹ *
          f (θ₁ ((μ - 1)⁻¹ • v + (μ - 1)⁻¹ • w))) := by group
    rw [e]
    exact Subgroup.mul_mem _ h2 h1
  have hθ'conj : ∀ (g : ↥(rootGroup D x ⊔ rootGroup D y)) v,
      (θ' ((φ g : Matrix (Fin 2) (Fin 2) K) *ᵥ v))⁻¹ * ((g : G) * θ' v * (g : G)⁻¹) ∈
        rootGroup D a ⊔ rootGroup D d := by
    intro g v
    set u := (μ - 1)⁻¹ • v
    have hgu : (μ - 1)⁻¹ • ((φ g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        (φ g : Matrix (Fin 2) (Fin 2) K) *ᵥ u := by rw [Matrix.mulVec_smul]
    have hm := M.nat₁.map_mulVec g u
    have hcg := hhX g g.2
    have e1 : (g : G) * θ' v * (g : G)⁻¹ = f ((g : G) * θ₁ u * (g : G)⁻¹) := by
      simp only [hθ', hf]
      calc (g : G) * (h * θ₁ u * h⁻¹ * (θ₁ u)⁻¹) * (g : G)⁻¹ =
          ((g : G) * h) * θ₁ u * (h⁻¹ * (g : G)⁻¹) * ((g : G) * (θ₁ u)⁻¹ * (g : G)⁻¹) := by
            group
        _ = (h * (g : G)) * θ₁ u * ((g : G)⁻¹ * h⁻¹) *
            ((g : G) * (θ₁ u)⁻¹ * (g : G)⁻¹) := by
          rw [hcg.eq, ← mul_inv_rev, ← mul_inv_rev, hcg.eq]
        _ = _ := by group
    have e2 : (g : G) * θ₁ u * (g : G)⁻¹ = θ₁ ((φ g : Matrix (Fin 2) (Fin 2) K) *ᵥ u) *
        ((θ₁ ((φ g : Matrix (Fin 2) (Fin 2) K) *ᵥ u))⁻¹ * ((g : G) * θ₁ u * (g : G)⁻¹)) := by
      group
    rw [e1, e2, hθ'def, hgu]
    exact hfmulN₀ (hθ₁N _) hm
  set W := Subgroup.closure (((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) ∪
    Set.range θ') with hW
  have hθ'0 : θ' 0 ∈ rootGroup D a ⊔ rootGroup D d := by
    have h0 : θ₁ ((μ - 1)⁻¹ • (0 : Fin 2 → K)) ∈ lineN₀ D a d := by
      rw [smul_zero]
      have := M.nat₁.map_add 0 0
      rw [add_zero, show (θ₁ 0 * θ₁ 0)⁻¹ * θ₁ 0 = (θ₁ 0)⁻¹ by group] at this
      exact inv_mem_iff.1 this
    exact hfN₀ h0
  have hWN : W ≤ lineN D a d := by
    rw [hW, Subgroup.closure_le]
    rintro w (hw | ⟨v, rfl⟩)
    · exact hN₀N (hTN₀ hw)
    · exact hθ'N v
  have hWcls : ∀ w ∈ W, ∃ v, (θ' v)⁻¹ * w ∈ rootGroup D a ⊔ rootGroup D d := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hw | ⟨v, rfl⟩
      · exact ⟨0, Subgroup.mul_mem _ (Subgroup.inv_mem _ hθ'0) hw⟩
      · exact ⟨v, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
    | one => exact ⟨0, by rw [mul_one]; exact Subgroup.inv_mem _ hθ'0⟩
    | mul w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
      obtain ⟨v₁, hv₁⟩ := ih₁
      obtain ⟨v₂, hv₂⟩ := ih₂
      refine ⟨v₁ + v₂, ?_⟩
      have h1 := hθ'add v₁ v₂
      have e : (θ' (v₁ + v₂))⁻¹ * (w₁ * w₂) = ((θ' v₁ * θ' v₂)⁻¹ * θ' (v₁ + v₂))⁻¹ *
          ((θ' v₂)⁻¹ * ((θ' v₁)⁻¹ * w₁) * θ' v₂) * ((θ' v₂)⁻¹ * w₂) := by group
      rw [e]
      have h3 : (θ' v₂)⁻¹ * ((θ' v₁)⁻¹ * w₁) * θ' v₂ ∈ rootGroup D a ⊔ rootGroup D d := by
        rw [(hNT (Subgroup.inv_mem _ (hθ'N v₂)) hv₁).eq, inv_mul_cancel_right]
        exact hv₁
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h3) hv₂
    | inv w hw ih =>
      obtain ⟨v, hv⟩ := ih
      refine ⟨-v, ?_⟩
      have h1 := hθ'add v (-v)
      rw [add_neg_cancel] at h1
      have h2 : θ' v * θ' (-v) ∈ rootGroup D a ⊔ rootGroup D d := by
        have := Subgroup.mul_mem _ hθ'0 (Subgroup.inv_mem _ h1)
        rwa [show θ' 0 * ((θ' v * θ' (-v))⁻¹ * θ' 0)⁻¹ = θ' v * θ' (-v) by group] at this
      have hwN : w ∈ lineN D a d := hWN hw
      have e : (θ' (-v))⁻¹ * w⁻¹ = (θ' v * θ' (-v))⁻¹ * (θ' v * ((θ' v)⁻¹ * w)⁻¹ * (θ' v)⁻¹) := by
        group
      rw [e, (hNT (hθ'N v) (Subgroup.inv_mem _ hv)).eq, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) (Subgroup.inv_mem _ hv)
  have hWconj : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hw | ⟨v, rfl⟩
      · exact Subgroup.subset_closure (Or.inl (C.conj_mem_T hg hw))
      · have h1 := hθ'conj ⟨g, hg⟩ v
        have e : g * θ' v * g⁻¹ = θ' ((φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) *
            ((θ' ((φ ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ v))⁻¹ * (g * θ' v * g⁻¹)) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))
          (Subgroup.subset_closure (Or.inl h1))
    | one => simp
    | mul w₁ w₂ _ _ ih₁ ih₂ =>
      rw [show g * (w₁ * w₂) * g⁻¹ = g * w₁ * g⁻¹ * (g * w₂ * g⁻¹) by group]
      exact Subgroup.mul_mem _ ih₁ ih₂
    | inv w _ ih =>
      rw [show g * w⁻¹ * g⁻¹ = (g * w * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ih
  have hext : Higman.IsNaturalExtension φ W (rootGroup D a ⊔ rootGroup D d) θ₀ θ' :=
    { le := fun t ht => Subgroup.subset_closure (Or.inl ht)
      normal := fun w hw t ht => by
        rw [(hNT (hWN hw) ht).eq, mul_inv_cancel_right]
        exact ht
      conj_mem := hWconj
      natural := M.nat₀
      range := M.range₀
      quotient :=
        { mem := fun v => Subgroup.subset_closure (Or.inr ⟨v, rfl⟩)
          map_add := hθ'add
          eq_zero_of_mem := fun v hv => by
            refine M.nat₁.eq_zero_of_mem v ?_
            have := Subgroup.mul_mem _ (hθ'cls v) (Subgroup.inv_mem _ (hTN₀ hv))
            rwa [show (θ₁ v)⁻¹ * θ' v * (θ' v)⁻¹ = (θ₁ v)⁻¹ by group, inv_mem_iff] at this
          exists_eq := hWcls
          map_mulVec := hθ'conj } }
  have hxX := C.x_mem_X
  set w := θ' ![0, 1] with hw
  have hwW : w ∈ W := Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  have hc : x * w * x⁻¹ * w⁻¹ ∈ W :=
    Subgroup.mul_mem _ (hWconj x hxX w hwW) (Subgroup.inv_mem _ hwW)
  have hc2 := hext.mul_self_eq_one hK2 hc
  have hx'D : w * x * w⁻¹ ∈ D := conj_mem_of_isClass C.isClass w C.hx
  have hcomm' : Commute x (w * x * w⁻¹) := by
    rw [commute_iff_mul_sq_eq_one (hD.mul_self_eq_one C.hx) (hD.mul_self_eq_one hx'D),
      show x * (w * x * w⁻¹) = x * w * x⁻¹ * w⁻¹ by rw [hD.inv_eq C.hx]; group, sq]
    exact hc2
  have hwNa := C.mem_Na_of_commute (hWN hwW) hcomm'
  have hθNa : θ₁ ![0, 1] ∈ nCore D a ⊓ Subgroup.centralizer {d} := by
    have h1 := lineN₀_le_Na (hθ'cls ![0, 1])
    have := Subgroup.mul_mem _ hwNa (Subgroup.inv_mem _ h1)
    rwa [show w * ((θ₁ ![0, 1])⁻¹ * θ' ![0, 1])⁻¹ = θ₁ ![0, 1] by rw [hw]; group] at this
  have h0 := M.nat₁.eq_zero_of_mem _ (mem_lineN₀_of_mem hθNa (M.θ₁_d 1))
  have := congrFun h0 1
  simp at this

end ModConf

end RootOne

end CFSG.Timmesfeld.Bridge
