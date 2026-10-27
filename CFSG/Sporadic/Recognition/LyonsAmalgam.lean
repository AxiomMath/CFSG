module

public import CFSG.Sporadic.Recognition.LyonsAmalgamStage3
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelTau
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtWord

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore

section ModelY

open Ly1080

noncomputable def stage2ModelY0 (h : YOK) (hcard : Nat.card Y0 ≤ 349920) :
    Stage2Model ↥Y0 where
  κ := kappa0 h
  T := Txy0.subgroupOf Y0
  center_eq_bot := center_Y0 h
  card_aut_le := card_mulAut_Y0 h hcard
  κ_mul_κ := by
    refine MulEquiv.ext fun y => ?_
    apply Subtype.ext
    have hs : sigma0 * sigma0 = 1 := sigma_mul_self h
    have hs' : sigma0⁻¹ = sigma0 := sigma_inv h
    show sigma0 * (sigma0 * (y : Perm (Fin deg)) * sigma0⁻¹) * sigma0⁻¹ = y
    rw [hs']
    calc sigma0 * (sigma0 * (y : Perm (Fin deg)) * sigma0) * sigma0
        = (sigma0 * sigma0) * y * (sigma0 * sigma0) := by group
      _ = y := by rw [hs]; group
  κ_mem := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact sigma_conj_Txy0 h _ ht
  normalizer_le := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    refine normalizer_Txy0 h hcard (n : Perm (Fin deg)) n.2 fun t ht => ?_
    have := hn ⟨t, Txy0_le_Y0 h ht⟩ (Subgroup.mem_subgroupOf.2 ht)
    exact Subgroup.mem_subgroupOf.1 this
  not_inner := by
    intro t ht hEq
    refine not_inner_Txy0 h (t : Perm (Fin deg)) (Subgroup.mem_subgroupOf.1 ht) fun i hi => ?_
    have := congrArg (fun α : MulAut ↥Y0 => ((α ⟨ug i, ug_mem h hi⟩ : ↥Y0) : Perm (Fin deg))) hEq
    simpa [MulAut.conj_apply, kappa0_coe] using this

end ModelY

section Words

variable {G X : Type*} [Group G] [Group X]

@[expose] def wordLetter (u : ℕ → X) (l : ℤ) : X :=
  if 0 < l then u (l.toNat - 1) else (u ((-l).toNat - 1))⁻¹

theorem wordLetter_hom (H : Subgroup G) (φ : H →* X) (u : ℕ → G) (u' : ℕ → X) {n : ℕ}
    (hu : ∀ i, i < n → ∃ h : u i ∈ H, φ ⟨u i, h⟩ = u' i) {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ n) :
    ∃ h : wordLetter u l ∈ H, φ ⟨wordLetter u l, h⟩ = wordLetter u' l := by
  obtain ⟨hl0, hln⟩ := hl
  unfold wordLetter
  split_ifs with hpos
  · exact hu _ (by omega)
  · obtain ⟨h, hφ⟩ := hu ((-l).toNat - 1) (by omega)
    refine ⟨H.inv_mem h, ?_⟩
    have : (⟨(u ((-l).toNat - 1))⁻¹, H.inv_mem h⟩ : H) = (⟨u ((-l).toNat - 1), h⟩ : H)⁻¹ := rfl
    rw [this, map_inv, hφ]

theorem wordG_hom (H : Subgroup G) (φ : H →* X) (f : ℤ → G) (f' : ℤ → X) (w : List ℤ)
    (hf : ∀ l ∈ w, ∃ h : f l ∈ H, φ ⟨f l, h⟩ = f' l) :
    ∃ h : wordG f w ∈ H, φ ⟨wordG f w, h⟩ = wordG f' w := by
  induction w with
  | nil => exact ⟨H.one_mem, map_one φ⟩
  | cons l w ih =>
    obtain ⟨hl, hφl⟩ := hf l (List.mem_cons_self ..)
    obtain ⟨hw, hφw⟩ := ih fun l' hl' => hf l' (List.mem_cons_of_mem _ hl')
    refine ⟨H.mul_mem hl hw, ?_⟩
    have : (⟨wordG f (l :: w), H.mul_mem hl hw⟩ : H) = ⟨f l, hl⟩ * ⟨wordG f w, hw⟩ := rfl
    rw [this, map_mul, hφl, hφw]
    rfl

end Words

structure SmallModelIso {G : Type} [Group G] (x₁ x₂ x₃ : G) where
  φY : ↥(NN x₁ x₂) ≃* ↥Ly1080.Y0
  φT : ↥(TxN x₁ x₂ x₃) ≃* ↥Ly243.Tx0
  K_iff : ∀ y : ↥(NN x₁ x₂), (y : G) ∈ KN x₁ x₂ x₃ ↔
    (φY y : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0
  agree : ∀ (j : ℕ) (g : G) (hN : g ∈ NN x₁ x₂) (hX : g ∈ TxN x₁ x₂ x₃), j < 5 →
    (φY ⟨g, hN⟩ : Perm (Fin Ly1080.deg)) = Ly1080.txyG j →
      (φT ⟨g, hX⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG j

structure IsSwapY0 {G : Type} [Group G] (a b c : G) (φY : ↥(NN a b) ≃* ↥Ly1080.Y0) (k : G) :
    Prop where
  mem_EN : k ∈ EN a b
  act : ∀ (y : G) (hy : y ∈ NN a b), ∃ hy' : k * y * k⁻¹ ∈ NN a b,
    (φY ⟨k * y * k⁻¹, hy'⟩ : Perm (Fin Ly1080.deg)) =
      Ly1080.sigma0 * (φY ⟨y, hy⟩ : Perm (Fin Ly1080.deg)) * Ly1080.sigma0⁻¹
  mul_self : k * k = 1
  not_mem_NN : k ∉ NN a b
  conj_a : k * a * k⁻¹ ∈ zpowers b
  conj_b : k * b * k⁻¹ ∈ zpowers a
  conj_c : k * c * k⁻¹ ∈ zpowers c
  mem_TrN : k ∈ TrN a b c
  conj_KN : ∀ g ∈ KN a b c, k * g * k⁻¹ ∈ KN a b c

section TauCalculus

variable {G : Type} [Group G] [Finite G] {x₁ x₂ x₃ : G}

theorem Txy0_induction (hY : Ly1080.YOK)
    {P : (t : Perm (Fin Ly1080.deg)) → t ∈ Ly1080.Txy0 → Prop}
    (gen : ∀ (j : ℕ) (hj : j < 5), P (Ly1080.txyG j) (Ly1080.txyG_mem_Txy0 hY hj))
    (one : P 1 (one_mem _))
    (mul : ∀ (x y : Perm (Fin Ly1080.deg)) (hx : x ∈ Ly1080.Txy0) (hy : y ∈ Ly1080.Txy0),
      P x hx → P y hy → P (x * y) (mul_mem hx hy))
    (inv : ∀ (x : Perm (Fin Ly1080.deg)) (hx : x ∈ Ly1080.Txy0), P x hx → P x⁻¹ (inv_mem hx))
    (t : Perm (Fin Ly1080.deg)) (ht : t ∈ Ly1080.Txy0) : P t ht := by
  have key : ∀ (j : ℕ) (hj : j < 5) (s : Perm (Fin Ly1080.deg)) (_ : s = Ly1080.txyG j)
      (h : s ∈ Ly1080.Txy0), P s h := by
    intro j hj s hs
    subst hs
    intro h
    exact gen j hj
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    have hT' : T ∈ Ly1080.txyTabs := by simpa using hT
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
    have hsz := (Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).2
    have e : tp Ly1080.deg Ly1080.txyTabs[j] = Ly1080.txyG j := by
      have := Ly1080.tp_txyTab hY (j := j) (by omega)
      rwa [getElem!_pos Ly1080.txyTabs j hj] at this
    exact key j (by omega) _ e _
  | one => exact one
  | mul x y hx hy ihx ihy => exact mul x y hx hy ihx ihy
  | inv x hx ihx => exact inv x hx ihx

theorem sigmaTxyWords_get_mem (hY : Ly1080.YOK) {j : ℕ} (hj : j < 5) :
    Ly1080.sigmaTxyWords[j]! ∈ Ly1080.sigmaTxyWords := by
  have hs := (Ly1080.yCheck_parts hY).2.2.2.2
  simp only [Ly1080.sigmaTxyOK, Bool.and_eq_true, beq_iff_eq] at hs
  rw [getElem!_pos Ly1080.sigmaTxyWords j (by omega)]
  exact List.getElem_mem _

theorem iota_wordG (hY : Ly1080.YOK) (ι : ↥Ly1080.Txy0 ≃* ↥Ly243.Txy0)
    (hι : ∀ (j : ℕ) (hj : j < 5),
      (ι ⟨Ly1080.txyG j, Ly1080.txyG_mem_Txy0 hY hj⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG j)
    {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) :
    (ι ⟨wordG Ly1080.txyLetG w, Ly1080.wordG_mem_Txy0 hY hw⟩ : Perm (Fin Ly243.deg)) =
      wordG Ly243.txyLetG w := by
  let φ : ↥Ly1080.Txy0 →* Perm (Fin Ly243.deg) := Ly243.Txy0.subtype.comp ι.toMonoidHom
  have hu : ∀ i, i < 5 → ∃ h : Ly1080.txyG i ∈ Ly1080.Txy0,
      φ ⟨Ly1080.txyG i, h⟩ = Ly243.txyG i := fun i hi => ⟨Ly1080.txyG_mem_Txy0 hY hi, hι i hi⟩
  obtain ⟨h, hφ⟩ := wordG_hom Ly1080.Txy0 φ Ly1080.txyLetG Ly243.txyLetG w fun l hl =>
    wordLetter_hom Ly1080.Txy0 φ Ly1080.txyG Ly243.txyG hu (hw l hl)
  exact hφ

theorem iota_conj_sigma (hY : Ly1080.YOK) (hT : Ly243.trCheck = true)
    (ι : ↥Ly1080.Txy0 ≃* ↥Ly243.Txy0)
    (hι : ∀ (j : ℕ) (hj : j < 5),
      (ι ⟨Ly1080.txyG j, Ly1080.txyG_mem_Txy0 hY hj⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG j)
    (t : Perm (Fin Ly1080.deg)) (ht : t ∈ Ly1080.Txy0) :
    (ι ⟨Ly1080.sigma0 * t * Ly1080.sigma0⁻¹, Ly1080.sigma_conj_Txy0 hY t ht⟩ :
        Perm (Fin Ly243.deg)) =
      Ly243.k0 * (ι ⟨t, ht⟩ : Perm (Fin Ly243.deg)) * Ly243.k0⁻¹ := by
  refine Txy0_induction hY (P := fun t ht =>
    (ι ⟨Ly1080.sigma0 * t * Ly1080.sigma0⁻¹, Ly1080.sigma_conj_Txy0 hY t ht⟩ :
        Perm (Fin Ly243.deg)) =
      Ly243.k0 * (ι ⟨t, ht⟩ : Perm (Fin Ly243.deg)) * Ly243.k0⁻¹) ?_ ?_ ?_ ?_ t ht
  · intro j hj
    have hw : ∀ l ∈ Ly1080.sigmaTxyWords[j]!, l ≠ 0 ∧ l.natAbs ≤ 5 := fun l hl =>
      Ly1080.words_range₅ hY _ (sigmaTxyWords_get_mem hY hj) l hl
    have e1 : (⟨Ly1080.sigma0 * Ly1080.txyG j * Ly1080.sigma0⁻¹,
        Ly1080.sigma_conj_Txy0 hY _ (Ly1080.txyG_mem_Txy0 hY hj)⟩ : ↥Ly1080.Txy0) =
        ⟨wordG Ly1080.txyLetG Ly1080.sigmaTxyWords[j]!, Ly1080.wordG_mem_Txy0 hY hw⟩ :=
      Subtype.ext (Ly1080.sigma_conj_txyG hY hj)
    rw [e1, iota_wordG hY ι hι hw, hι j hj, Ly243.k0_conj_txyG hT hj]
  · have e1 : ∀ h, (⟨Ly1080.sigma0 * 1 * Ly1080.sigma0⁻¹, h⟩ : ↥Ly1080.Txy0) = 1 :=
      fun h => Subtype.ext (by simp)
    have e2 : (⟨(1 : Perm (Fin Ly1080.deg)), one_mem _⟩ : ↥Ly1080.Txy0) = 1 := rfl
    rw [e1, e2, map_one]
    simp
  · intro x y hx hy ihx ihy
    beta_reduce at ihx ihy ⊢
    have e1 : ∀ h, (⟨Ly1080.sigma0 * (x * y) * Ly1080.sigma0⁻¹, h⟩ : ↥Ly1080.Txy0) =
        ⟨Ly1080.sigma0 * x * Ly1080.sigma0⁻¹, Ly1080.sigma_conj_Txy0 hY x hx⟩ *
          ⟨Ly1080.sigma0 * y * Ly1080.sigma0⁻¹, Ly1080.sigma_conj_Txy0 hY y hy⟩ := fun h =>
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    have e2 : ∀ h, (⟨x * y, h⟩ : ↥Ly1080.Txy0) = ⟨x, hx⟩ * ⟨y, hy⟩ := fun h => rfl
    rw [e1, e2, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ihx, ihy]
    group
  · intro x hx ihx
    beta_reduce at ihx ⊢
    have e1 : ∀ h, (⟨Ly1080.sigma0 * x⁻¹ * Ly1080.sigma0⁻¹, h⟩ : ↥Ly1080.Txy0) =
        (⟨Ly1080.sigma0 * x * Ly1080.sigma0⁻¹, Ly1080.sigma_conj_Txy0 hY x hx⟩ :
          ↥Ly1080.Txy0)⁻¹ := fun h => Subtype.ext (by simp only [Subgroup.coe_inv]; group)
    have e2 : ∀ h, (⟨x⁻¹, h⟩ : ↥Ly1080.Txy0) = (⟨x, hx⟩ : ↥Ly1080.Txy0)⁻¹ := fun h => rfl
    rw [e1, e2, map_inv, map_inv, Subgroup.coe_inv, Subgroup.coe_inv, ihx]
    group

omit [Finite G] in
theorem SmallModelIso.exists_K (I : SmallModelIso x₁ x₂ x₃) (hY : Ly1080.YOK)
    {t : Perm (Fin Ly1080.deg)} (ht : t ∈ Ly1080.Txy0) :
    ∃ y : ↥(NN x₁ x₂), (y : G) ∈ KN x₁ x₂ x₃ ∧ (I.φY y : Perm (Fin Ly1080.deg)) = t := by
  refine ⟨I.φY.symm ⟨t, Ly1080.Txy0_le_Y0 hY ht⟩, ?_, by rw [MulEquiv.apply_symm_apply]⟩
  exact (I.K_iff _).2 (by rw [MulEquiv.apply_symm_apply]; exact ht)

theorem SmallModelIso.φT_eq_iota (I : SmallModelIso x₁ x₂ x₃) (hY : Ly1080.YOK)
    (ι : ↥Ly1080.Txy0 ≃* ↥Ly243.Txy0)
    (hι : ∀ (j : ℕ) (hj : j < 5),
      (ι ⟨Ly1080.txyG j, Ly1080.txyG_mem_Txy0 hY hj⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG j)
    {t : Perm (Fin Ly1080.deg)} (ht : t ∈ Ly1080.Txy0) (g : G) (hN : g ∈ NN x₁ x₂)
    (hX : g ∈ TxN x₁ x₂ x₃) (hg : (I.φY ⟨g, hN⟩ : Perm (Fin Ly1080.deg)) = t) :
    (I.φT ⟨g, hX⟩ : Perm (Fin Ly243.deg)) = (ι ⟨t, ht⟩ : Perm (Fin Ly243.deg)) := by
  revert g hN hX hg
  refine Txy0_induction hY (P := fun t ht => ∀ (g : G) (hN : g ∈ NN x₁ x₂)
    (hX : g ∈ TxN x₁ x₂ x₃), (I.φY ⟨g, hN⟩ : Perm (Fin Ly1080.deg)) = t →
      (I.φT ⟨g, hX⟩ : Perm (Fin Ly243.deg)) = (ι ⟨t, ht⟩ : Perm (Fin Ly243.deg))) ?_ ?_ ?_ ?_ t ht
  · intro j hj g hN hX hg
    rw [hι j hj]
    exact I.agree j g hN hX hj hg
  · intro g hN hX hg
    have h1 : (⟨g, hN⟩ : ↥(NN x₁ x₂)) = 1 :=
      I.φY.injective ((Subtype.ext hg).trans (map_one I.φY).symm)
    have hg1 : g = 1 := congrArg Subtype.val h1
    have h2 : (⟨g, hX⟩ : ↥(TxN x₁ x₂ x₃)) = 1 := Subtype.ext hg1
    have h3 : (⟨(1 : Perm (Fin Ly1080.deg)), one_mem _⟩ : ↥Ly1080.Txy0) = 1 := rfl
    rw [h2, h3, map_one, map_one]
    simp
  · intro x y hx hy ihx ihy g hN hX hg
    obtain ⟨y₁, hK₁, hφ₁⟩ := I.exists_K hY hx
    obtain ⟨y₂, hK₂, hφ₂⟩ := I.exists_K hY hy
    have hX₁ := KN_le_TxN _ _ _ hK₁
    have hX₂ := KN_le_TxN _ _ _ hK₂
    have e₁ := ihx (y₁ : G) y₁.2 hX₁ hφ₁
    have e₂ := ihy (y₂ : G) y₂.2 hX₂ hφ₂
    have hprod : (⟨g, hN⟩ : ↥(NN x₁ x₂)) = y₁ * y₂ := by
      apply I.φY.injective
      rw [map_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, hg, hφ₁, hφ₂]
    have hg' : g = (y₁ : G) * (y₂ : G) := congrArg Subtype.val hprod
    have hprodT : (⟨g, hX⟩ : ↥(TxN x₁ x₂ x₃)) = ⟨(y₁ : G), hX₁⟩ * ⟨(y₂ : G), hX₂⟩ :=
      Subtype.ext hg'
    have e3 : (⟨x * y, mul_mem hx hy⟩ : ↥Ly1080.Txy0) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [hprodT, map_mul, Subgroup.coe_mul, e₁, e₂, e3, map_mul, Subgroup.coe_mul]
  · intro x hx ihx g hN hX hg
    obtain ⟨y₁, hK₁, hφ₁⟩ := I.exists_K hY hx
    have hX₁ := KN_le_TxN _ _ _ hK₁
    have e₁ := ihx (y₁ : G) y₁.2 hX₁ hφ₁
    have hprod : (⟨g, hN⟩ : ↥(NN x₁ x₂)) = y₁⁻¹ := by
      apply I.φY.injective
      rw [map_inv]
      apply Subtype.ext
      rw [Subgroup.coe_inv, hg, hφ₁]
    have hg' : g = ((y₁ : G))⁻¹ := congrArg Subtype.val hprod
    have hprodT : (⟨g, hX⟩ : ↥(TxN x₁ x₂ x₃)) = (⟨(y₁ : G), hX₁⟩ : ↥(TxN x₁ x₂ x₃))⁻¹ :=
      Subtype.ext hg'
    have e3 : (⟨x⁻¹, inv_mem hx⟩ : ↥Ly1080.Txy0) = (⟨x, hx⟩ : ↥Ly1080.Txy0)⁻¹ := rfl
    rw [hprodT, map_inv, Subgroup.coe_inv, e₁, e3, map_inv, Subgroup.coe_inv]

theorem SmallModelIso.exists_K_of_T (I : SmallModelIso x₁ x₂ x₃) (hY : Ly1080.YOK)
    (ι : ↥Ly1080.Txy0 ≃* ↥Ly243.Txy0)
    (hι : ∀ (j : ℕ) (hj : j < 5),
      (ι ⟨Ly1080.txyG j, Ly1080.txyG_mem_Txy0 hY hj⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG j)
    {z : Perm (Fin Ly243.deg)} (hz : z ∈ Ly243.Txy0) :
    ∃ (g : G) (hX : g ∈ TxN x₁ x₂ x₃), g ∈ KN x₁ x₂ x₃ ∧
      (I.φT ⟨g, hX⟩ : Perm (Fin Ly243.deg)) = z := by
  obtain ⟨y, hK, hφ⟩ := I.exists_K hY (ι.symm ⟨z, hz⟩ : ↥Ly1080.Txy0).2
  have hX := KN_le_TxN _ _ _ hK
  refine ⟨(y : G), hX, hK, ?_⟩
  have := I.φT_eq_iota hY ι hι (ι.symm ⟨z, hz⟩ : ↥Ly1080.Txy0).2 (y : G) y.2 hX hφ
  rw [this]
  simp

theorem SmallModelIso.φT_mem_Txy0 (I : SmallModelIso x₁ x₂ x₃) (hY : Ly1080.YOK)
    (ι : ↥Ly1080.Txy0 ≃* ↥Ly243.Txy0)
    (hι : ∀ (j : ℕ) (hj : j < 5),
      (ι ⟨Ly1080.txyG j, Ly1080.txyG_mem_Txy0 hY hj⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG j)
    (g : G) (hX : g ∈ TxN x₁ x₂ x₃) (hK : g ∈ KN x₁ x₂ x₃) :
    (I.φT ⟨g, hX⟩ : Perm (Fin Ly243.deg)) ∈ Ly243.Txy0 := by
  have hN : g ∈ NN x₁ x₂ := KN_le_NN _ _ _ hK
  rw [I.φT_eq_iota hY ι hι ((I.K_iff ⟨g, hN⟩).1 hK) g hN hX rfl]
  exact (ι _).2

end TauCalculus

section Stage2Model

variable {G : Type} [Group G]

theorem IsSwapElement.toY0 {hY : Ly1080.YOK} {hcard : Nat.card ↥Ly1080.Y0 ≤ 349920}
    {a b c : G} {φY : ↥(NN a b) ≃* ↥Ly1080.Y0} {k : G}
    (hk : IsSwapElement a b c (stage2ModelY0 hY hcard) φY k) : IsSwapY0 a b c φY k where
  mem_EN := hk.mem_EN
  act y hy := by
    obtain ⟨hy', h⟩ := hk.act y hy
    refine ⟨hy', ?_⟩
    rw [h]
    exact Ly1080.kappa0_coe hY _
  mul_self := hk.mul_self
  not_mem_NN := hk.not_mem_NN
  conj_a := hk.conj_a
  conj_b := hk.conj_b
  conj_c := hk.conj_c
  mem_TrN := hk.mem_TrN
  conj_KN := hk.conj_KN

end Stage2Model

section Stage2

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem LyData.card_Y0_le (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (I : SmallModelIso (x₁ : G) (x₂ : G) (x₃ : G)) : Nat.card ↥Ly1080.Y0 ≤ 349920 := by
  rw [← Nat.card_congr I.φY.toEquiv, D.card_NN' S]

theorem LyData.exists_swapY0 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (I : SmallModelIso (x₁ : G) (x₂ : G) (x₃ : G)) :
    ∃ k : G, IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) I.φY k := by
  obtain ⟨k, hk⟩ := D.exists_swapElement S (stage2ModelY0 hY (D.card_Y0_le S I)) I.φY
    (fun y => (I.K_iff y).trans Subgroup.mem_subgroupOf.symm) (D.card_normalizer_EE' S)
  exact ⟨k, hk.toY0⟩

theorem LyData.exists_mulEquiv_mulAut_Y0 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (I : SmallModelIso (x₁ : G) (x₂ : G) (x₃ : G)) :
    ∃ Φ : ↥(EN (x₁ : G) (x₂ : G)) ≃* MulAut ↥(NN (x₁ : G) (x₂ : G)),
      ∀ (e : ↥(EN (x₁ : G) (x₂ : G))) (y : ↥(NN (x₁ : G) (x₂ : G))),
        ((Φ e y : ↥(NN (x₁ : G) (x₂ : G))) : G) = (e : G) * (y : G) * (e : G)⁻¹ :=
  D.exists_mulEquiv_mulAut S (stage2ModelY0 hY (D.card_Y0_le S I)) I.φY
    (D.card_normalizer_EE' S)

end Stage2

section ERelators

variable {G : Type} [Group G]

theorem erelWords_get_mem (hY : Ly1080.YOK) {i : ℕ} (hi : i < 4) :
    Ly1080.erelWords[i]! ∈ Ly1080.erelWords := by
  have herel := (Ly1080.yCheck_parts hY).2.1
  simp only [Ly1080.erelOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    List.mem_range] at herel
  rw [getElem!_pos Ly1080.erelWords i (by omega)]
  exact List.getElem_mem _

theorem IsSwapY0.erelators {a b c : G} {φY : ↥(NN a b) ≃* ↥Ly1080.Y0} {k : G}
    (hk : IsSwapY0 a b c φY k) (hY : Ly1080.YOK) (u : ℕ → G)
    (hu : ∀ i, i < 4 → ∃ h : u i ∈ NN a b, (φY ⟨u i, h⟩ : Perm (Fin Ly1080.deg)) = Ly1080.ug i)
    {i : ℕ} (hi : i < 4) : k * u i * k⁻¹ = wordG (wordLetter u) Ly1080.erelWords[i]! := by
  obtain ⟨h, hφ⟩ := hu i hi
  obtain ⟨hy', hact⟩ := hk.act (u i) h
  let φ : ↥(NN a b) →* Perm (Fin Ly1080.deg) := Ly1080.Y0.subtype.comp φY.toMonoidHom
  have hu' : ∀ i, i < 4 → ∃ h : u i ∈ NN a b, φ ⟨u i, h⟩ = Ly1080.ug i := hu
  have hr : ∀ l ∈ Ly1080.erelWords[i]!, l ≠ 0 ∧ l.natAbs ≤ 4 := fun l hl =>
    Ly1080.words_range₄ hY _ (List.mem_append_left _ (erelWords_get_mem hY hi)) l hl
  obtain ⟨hR, hφR⟩ := wordG_hom (NN a b) φ (wordLetter u) (wordLetter Ly1080.ug)
    Ly1080.erelWords[i]! fun l hl =>
      wordLetter_hom (NN a b) φ u Ly1080.ug hu' (hr l hl)
  have h1 : (φY ⟨k * u i * k⁻¹, hy'⟩ : Perm (Fin Ly1080.deg)) =
      wordG (wordLetter Ly1080.ug) Ly1080.erelWords[i]! := by
    rw [hact, hφ]
    exact Ly1080.sigma_conj_ug hY hi
  have h2 : (⟨k * u i * k⁻¹, hy'⟩ : ↥(NN a b)) =
      ⟨wordG (wordLetter u) Ly1080.erelWords[i]!, hR⟩ := by
    apply φY.injective
    apply Subtype.ext
    exact h1.trans hφR.symm
  exact congrArg Subtype.val h2

end ERelators

section Stage3

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem LyData.exists_mulEquiv_Tr0 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (I : SmallModelIso (x₁ : G) (x₂ : G) (x₃ : G)) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) I.φY k) :
    ∃ ψ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) ≃* ↥Ly243.Tr0,
      (∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
        (ψ ⟨(x : G), x.2.1⟩ : Perm (Fin Ly243.deg)) = (I.φT x : Perm (Fin Ly243.deg))) ∧
      (ψ ⟨k, hk.mem_TrN⟩ : Perm (Fin Ly243.deg)) = Ly243.k0 := by
  obtain ⟨ι, hι⟩ := Tau.tau_exists hY hT hτ
  let φT' : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)) →* ↥Ly243.Tr0 :=
    (Subgroup.inclusion Ly243.Tx0_le_Tr0).comp I.φT.toMonoidHom
  have hinj : Function.Injective φT' :=
    (Subgroup.inclusion_injective Ly243.Tx0_le_Tr0).comp I.φT.injective
  have hcoe : ∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
      (φT' x : Perm (Fin Ly243.deg)) = (I.φT x : Perm (Fin Ly243.deg)) := fun x => rfl
  have hker : ∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
      φT' x ∈ (Ly243.trHom hT).ker ↔ (x : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := by
    intro x
    rw [MonoidHom.mem_ker, Ly243.ker_trHom hT, hcoe]
    constructor
    · intro hx
      obtain ⟨g, hX, hK, hφ⟩ := I.exists_K_of_T hY ι hι hx
      have : I.φT ⟨g, hX⟩ = I.φT x := Subtype.ext hφ
      have hgx : (⟨g, hX⟩ : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G))) = x := I.φT.injective this
      rw [← hgx]
      exact hK
    · intro hK
      exact I.φT_mem_Txy0 hY ι hι (x : G) x.2 hK
  have honto : ∀ y ∈ (Ly243.trHom hT).ker, ∃ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
      (x : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) ∧ φT' x = y := by
    intro y hy
    have hy' : (y : Perm (Fin Ly243.deg)) ∈ Ly243.Txy0 :=
      (Ly243.ker_trHom hT y).1 (MonoidHom.mem_ker.1 hy)
    obtain ⟨g, hX, hK, hφ⟩ := I.exists_K_of_T hY ι hι hy'
    exact ⟨⟨g, hX⟩, hK, Subtype.ext hφ⟩
  have hfix : ∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
      Ly243.trHom hT (φT' x) 0 = 0 := fun x =>
    Ly243.trHom_fix_zero hT (φT' x) (I.φT x).2
  have hcompat : ∀ (g : G) (hg : g ∈ KN (x₁ : G) (x₂ : G) (x₃ : G)),
      (⟨Ly243.k0, Ly243.k0_mem hT⟩ : ↥Ly243.Tr0) * φT' ⟨g, KN_le_TxN _ _ _ hg⟩ *
        (⟨Ly243.k0, Ly243.k0_mem hT⟩ : ↥Ly243.Tr0)⁻¹ =
        φT' ⟨k * g * k⁻¹, KN_le_TxN _ _ _ (hk.conj_KN g hg)⟩ := by
    intro g hg
    apply Subtype.ext
    have hgN : g ∈ NN (x₁ : G) (x₂ : G) := KN_le_NN _ _ _ hg
    obtain ⟨hy', hact⟩ := hk.act g hgN
    have hKg : k * g * k⁻¹ ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := hk.conj_KN g hg
    have ht1 := (I.K_iff ⟨g, hgN⟩).1 hg
    have ht2 := (I.K_iff ⟨k * g * k⁻¹, hy'⟩).1 hKg
    have e1 := I.φT_eq_iota hY ι hι ht1 g hgN (KN_le_TxN _ _ _ hg) rfl
    have e2 := I.φT_eq_iota hY ι hι ht2 (k * g * k⁻¹) hy' (KN_le_TxN _ _ _ hKg) rfl
    have e3 : (⟨(I.φY ⟨k * g * k⁻¹, hy'⟩ : Perm (Fin Ly1080.deg)), ht2⟩ : ↥Ly1080.Txy0) =
        ⟨Ly1080.sigma0 * (I.φY ⟨g, hgN⟩ : Perm (Fin Ly1080.deg)) * Ly1080.sigma0⁻¹,
          Ly1080.sigma_conj_Txy0 hY _ ht1⟩ := Subtype.ext hact
    show Ly243.k0 * (I.φT ⟨g, KN_le_TxN _ _ _ hg⟩ : Perm (Fin Ly243.deg)) * Ly243.k0⁻¹ =
      (I.φT ⟨k * g * k⁻¹, KN_le_TxN _ _ _ hKg⟩ : Perm (Fin Ly243.deg))
    rw [e1, e2, e3, iota_conj_sigma hY hT ι hι _ ht1]
  obtain ⟨ψ, hψ1, hψ2⟩ := D.exists_mulEquiv_Tr S (Ly243.trHom hT) (Ly243.center_ker_trHom hT)
    φT' hinj hker honto hfix hk.mem_TrN hk.conj_a hk.conj_b hk.conj_c hk.conj_KN
    ⟨Ly243.k0, Ly243.k0_mem hT⟩ (Ly243.trHom_k0 hT) hcompat
  refine ⟨ψ, fun x => ?_, ?_⟩
  · rw [hψ1 x]
    rfl
  · rw [hψ2]

theorem LyData.lift_eq_one_of_tr (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (I : SmallModelIso (x₁ : G) (x₂ : G) (x₃ : G)) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) I.φY k) (g : Fin 5 → G)
    (hg : ∀ i : Fin 5, i.val < 4 → ∃ h : g i ∈ TxN (x₁ : G) (x₂ : G) (x₃ : G),
      (I.φT ⟨g i, h⟩ : Perm (Fin Ly243.deg)) = Ly243.gg i.val)
    (hk5 : g 4 = k) (r : FreeGroup (Fin 5))
    (hr : FreeGroup.lift (fun i : Fin 5 => Ly243.gg i.val) r = 1) :
    FreeGroup.lift g r = 1 := by
  obtain ⟨ψ, hψ1, hψ2⟩ := D.exists_mulEquiv_Tr0 S hY hT hτ I hk
  have hTr : ∀ i : Fin 5, g i ∈ TrN (x₁ : G) (x₂ : G) (x₃ : G) := by
    intro i
    by_cases hi : i.val < 4
    · obtain ⟨h, -⟩ := hg i hi
      exact h.1
    · have hi4 : i = 4 := Fin.ext (by omega)
      rw [hi4, hk5]
      exact hk.mem_TrN
  let g' : Fin 5 → ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) := fun i => ⟨g i, hTr i⟩
  have hψg : ∀ i : Fin 5, (ψ (g' i) : Perm (Fin Ly243.deg)) = Ly243.gg i.val := by
    intro i
    by_cases hi : i.val < 4
    · obtain ⟨h, hφ⟩ := hg i hi
      exact (hψ1 ⟨g i, h⟩).trans hφ
    · have hi4 : i = 4 := Fin.ext (by omega)
      have e : g' i = ⟨k, hk.mem_TrN⟩ := Subtype.ext (by rw [hi4]; exact hk5)
      rw [e, hψ2, hi4]
      rfl
  have h1 := lift_subgroup_eq_one_iff (TrN (x₁ : G) (x₂ : G) (x₃ : G)) g' r
  have h2 := lift_eq_one_iff_lift_comp_eq_one ψ g' r
  have h3 := lift_subgroup_eq_one_iff Ly243.Tr0 (⇑ψ ∘ g') r
  have e : (fun i => (((⇑ψ ∘ g') i : ↥Ly243.Tr0) : Perm (Fin Ly243.deg))) =
      fun i : Fin 5 => Ly243.gg i.val := funext hψg
  rw [e] at h3
  exact h1.1 (h2.2 (h3.2 hr))

theorem LyData.wordG_eq_one_of_tr (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (I : SmallModelIso (x₁ : G) (x₂ : G) (x₃ : G)) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) I.φY k) (g : ℕ → G)
    (hg : ∀ i, i < 4 → ∃ h : g i ∈ TxN (x₁ : G) (x₂ : G) (x₃ : G),
      (I.φT ⟨g i, h⟩ : Perm (Fin Ly243.deg)) = Ly243.gg i)
    (hk4 : g 4 = k) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5)
    (hmodel : wordG Ly243.trLetG w = 1) : wordG (wordLetter g) w = 1 := by
  obtain ⟨ψ, hψ1, hψ2⟩ := D.exists_mulEquiv_Tr0 S hY hT hτ I hk
  let φ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) →* Perm (Fin Ly243.deg) :=
    Ly243.Tr0.subtype.comp ψ.toMonoidHom
  have hu : ∀ i, i < 5 → ∃ h : g i ∈ TrN (x₁ : G) (x₂ : G) (x₃ : G),
      φ ⟨g i, h⟩ = Ly243.gg i := by
    intro i hi
    by_cases hi4 : i < 4
    · obtain ⟨h, hφ⟩ := hg i hi4
      exact ⟨h.1, (hψ1 ⟨g i, h⟩).trans hφ⟩
    · have hi' : i = 4 := by omega
      subst hi'
      refine ⟨hk4 ▸ hk.mem_TrN, ?_⟩
      have e : (⟨g 4, hk4 ▸ hk.mem_TrN⟩ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) =
          ⟨k, hk.mem_TrN⟩ := Subtype.ext hk4
      show (ψ ⟨g 4, hk4 ▸ hk.mem_TrN⟩ : Perm (Fin Ly243.deg)) = Ly243.gg 4
      rw [e, hψ2]
      rfl
  obtain ⟨h, hφ⟩ := wordG_hom (TrN (x₁ : G) (x₂ : G) (x₃ : G)) φ (wordLetter g)
    (wordLetter Ly243.gg) w fun l hl => wordLetter_hom _ φ g Ly243.gg hu (hw l hl)
  have h1 : ψ ⟨wordG (wordLetter g) w, h⟩ = 1 :=
    Subtype.ext (hφ.trans hmodel)
  have h2 : (⟨wordG (wordLetter g) w, h⟩ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) = 1 :=
    ψ.injective (h1.trans (map_one ψ).symm)
  exact congrArg Subtype.val h2

end Stage3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
theorem Ly243.wordG_trLetG_eq_one_of_powFixW (h : Ly243.trCheck = true) {w : List ℤ}
    (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5)
    (hp : powFixW Ly243.deg (w.map Ly243.trLet) 1 = true) : wordG Ly243.trLetG w = 1 := by
  have hF : List.Forall₂ (Rep Ly243.deg) (w.map Ly243.trLet) (w.map Ly243.trLetG) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun l hl => Ly243.rep_trLet h (hw l hl)
  have := (powFixW_iff perm_faithful hF 1).1 hp
  simpa [wordG] using this

section Stage23

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem LyData.exists_swap_and_mulEquiv_Tr0 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (I : SmallModelIso (x₁ : G) (x₂ : G) (x₃ : G)) :
    ∃ k : G, ∃ hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) I.φY k,
      ∃ ψ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) ≃* ↥Ly243.Tr0,
        (∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
          (ψ ⟨(x : G), x.2.1⟩ : Perm (Fin Ly243.deg)) = (I.φT x : Perm (Fin Ly243.deg))) ∧
        (ψ ⟨k, hk.mem_TrN⟩ : Perm (Fin Ly243.deg)) = Ly243.k0 := by
  obtain ⟨k, hk⟩ := D.exists_swapY0 S hY I
  exact ⟨k, hk, D.exists_mulEquiv_Tr0 S hY hT hτ I hk⟩

end Stage23

end CFSG.Sporadic.Recognition.LyonsSims
