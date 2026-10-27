module

public import CFSG.Quasithin.Background.HL3WrA3

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open Matrix
open scoped Matrix

theorem relIndex_stabilizer_le_two {W : Type*} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {D e : W} (hAD : ∀ y ∈ A, y D = D ∨ y D = D * e) :
    (A ⊓ MulAction.stabilizer (MulAut W) D).relIndex A ≤ 2 := by
  have h1 : (A ⊓ MulAction.stabilizer (MulAut W) D).subgroupOf A =
      MulAction.stabilizer ↥A D := by
    ext c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
  rw [Subgroup.relIndex, h1, MulAction.index_stabilizer]
  calc (MulAction.orbit ↥A D).ncard ≤ ({D, D * e} : Set W).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨c, rfl⟩
        rcases hAD c c.2 with h | h
        · exact Or.inl h
        · exact Or.inr h
    _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]

theorem not_mem_aSet_two_of_orbit {W : Type*} [CommGroup W] [Finite W]
    {Y A : Subgroup (MulAut W)} (hA2 : IsPGroup 2 A) {D e : W}
    (hAD : ∀ y ∈ A, y D = D ∨ y D = D * e) {a : MulAut W} (ha : a ∈ A) (haD : a D ≠ D) :
    A ∉ E3.aSet 2 Y := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  rintro ⟨-, -, -, hfix⟩
  have hidx := relIndex_stabilizer_le_two hAD
  have hm : E3.mQuot A (A ⊓ MulAction.stabilizer (MulAut W) D) < 2 :=
    lt_of_le_of_lt (mQuot_le_of_relIndex_le hA2 (k := 1) (hidx.trans (by norm_num)))
      (by norm_num)
  have h := hfix _ inf_le_left hm
  have hDB : D ∈ fixV (A ⊓ MulAction.stabilizer (MulAut W) D) := fun y hy => hy.2
  rw [h] at hDB
  exact haD (hDB a ha)

theorem uMat_E11 (x y w x' y' w' : ZMod 2) :
    uMat x y w * Matrix.single 1 1 1 * (uMat x' y' w')ᵀ =
      Matrix.single 1 1 1 + Matrix.single 0 1 x + Matrix.single 1 0 x' +
        Matrix.single 0 0 (x * x') := by
  revert x y w x' y' w'
  decide

theorem zmod_two_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

theorem uMat_eq_of_fix_eSym {u v : ↥SL32} {a b c a' b' c' : ZMod 2} (ha : mat u = uMat a b c)
    (hb : mat v = uMat a' b' c') (hs : rho (u, v) eSym = eSym) : a' = a := by
  have e2 : Matrix.single 1 0 1 + Matrix.single 0 1 1 + Matrix.single 0 0 (a + a') =
      (Matrix.single 1 0 1 + Matrix.single 0 1 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have h := congrArg Multiplicative.toAdd hs
    change mat u * (Matrix.single 1 0 1 + Matrix.single 0 1 1) * (mat v)ᵀ = _ at h
    rw [ha, hb, uMat_sym] at h
    exact h
  have ha0 : a + a' = 0 := by
    have h := congrFun (congrFun e2 0) 0
    simpa using h
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases a' with rfl | rfl <;>
    first | rfl | exact absurd ha0 (by decide)

theorem rho_E11 {u v : ↥SL32} (hu : u ∈ U3) (hv : v ∈ U3) (hs : rho (u, v) eSym = eSym) :
    rho (u, v) (eW 1 1) = eW 1 1 ∨ rho (u, v) (eW 1 1) = eW 1 1 * (eW 0 0 * eSym) := by
  obtain ⟨a, b, c, ha⟩ := exists_uMat hu
  obtain ⟨a', b', c', hb⟩ := exists_uMat hv
  have ea := uMat_eq_of_fix_eSym ha hb hs
  have e : Multiplicative.toAdd (rho (u, v) (eW 1 1)) =
      Matrix.single 1 1 1 + Matrix.single 0 1 a + Matrix.single 1 0 a' +
        Matrix.single 0 0 (a * a') := by
    change mat u * Matrix.single 1 1 1 * (mat v)ᵀ = _
    rw [ha, hb, uMat_E11]
  rw [ea] at e
  rcases zmod_two_cases a with rfl | rfl
  · left
    apply Multiplicative.toAdd.injective
    rw [e]
    exact (by decide : (Matrix.single 1 1 1 + Matrix.single 0 1 0 + Matrix.single 1 0 0 +
      Matrix.single 0 0 (0 * 0) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = Matrix.single 1 1 1)
  · right
    apply Multiplicative.toAdd.injective
    rw [e]
    exact (by decide : (Matrix.single 1 1 1 + Matrix.single 0 1 1 + Matrix.single 1 0 1 +
      Matrix.single 0 0 (1 * 1) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        Matrix.single 1 1 1 + (Matrix.single 0 0 1 + (Matrix.single 1 0 1 + Matrix.single 0 1 1)))

theorem uMat_zero_of_fix {u v : ↥SL32} (hu : u ∈ U3) (hv : v ∈ U3)
    (hs : rho (u, v) eSym = eSym) (h11 : rho (u, v) (eW 1 1) = eW 1 1) :
    ∃ y w y' w' : ZMod 2, mat u = uMat 0 y w ∧ mat v = uMat 0 y' w' := by
  obtain ⟨a, b, c, ha⟩ := exists_uMat hu
  obtain ⟨a', b', c', hb⟩ := exists_uMat hv
  have ea := uMat_eq_of_fix_eSym ha hb hs
  have e : Matrix.single 1 1 1 + Matrix.single 0 1 a + Matrix.single 1 0 a' +
      Matrix.single 0 0 (a * a') = (Matrix.single 1 1 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have h := congrArg Multiplicative.toAdd h11
    change mat u * Matrix.single 1 1 1 * (mat v)ᵀ = _ at h
    rw [ha, hb, uMat_E11] at h
    exact h
  have ha0 : a = 0 := by
    have h := congrFun (congrFun e 0) 1
    simpa using h
  refine ⟨b, c, b', c', ?_, ?_⟩
  · rw [ha, ha0]
  · rw [hb, ea, ha0]

theorem tau_eSym : tau eSym = eSym := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau]
  exact (by decide : (Matrix.single 1 0 1 + Matrix.single 0 1 1 :
    Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = Matrix.single 1 0 1 + Matrix.single 0 1 1)

theorem tau_E11 : tau (eW 1 1) = eW 1 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau]
  exact Matrix.transpose_single 1 1 (1 : ZMod 2)

theorem tau_E01 : tau (eW 0 1) = eW 1 0 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau]
  exact Matrix.transpose_single 0 1 (1 : ZMod 2)

theorem T0_E11 {x : MulAut WMod} (hx : x ∈ T0) (hs : x eSym = eSym) :
    x (eW 1 1) = eW 1 1 ∨ x (eW 1 1) = eW 1 1 * (eW 0 0 * eSym) := by
  rcases mem_T0_cases hx with ⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩
  · exact rho_E11 hu hv hs
  · have hs' : rho (u, v) eSym = eSym := by
      have h := hs
      change rho (u, v) (tau eSym) = eSym at h
      rwa [tau_eSym] at h
    change rho (u, v) (tau (eW 1 1)) = _ ∨ rho (u, v) (tau (eW 1 1)) = _
    rw [tau_E11]
    exact rho_E11 hu hv hs'

theorem T0_E01 {x : MulAut WMod} (hx : x ∈ T0) (hs : x eSym = eSym)
    (h11 : x (eW 1 1) = eW 1 1) :
    (x (eW 0 1) = eW 0 1 ∨ x (eW 0 1) = eW 0 1 * eSym) ∧
      (x (eW 0 1) = eW 0 1 → x ∈ (R1.prod R1).map rho) := by
  rcases mem_T0_cases hx with ⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩
  · obtain ⟨y, w, y', w', hu', hv'⟩ := uMat_zero_of_fix hu hv hs h11
    refine ⟨Or.inl ?_, fun _ => ⟨(u, v), ⟨⟨y, w, hu'⟩, ⟨y', w', hv'⟩⟩, rfl⟩⟩
    apply Multiplicative.toAdd.injective
    change mat u * Matrix.single 0 1 1 * (mat v)ᵀ = Matrix.single 0 1 1
    rw [hu', hv', uMat_E01, Matrix.single_zero, add_zero]
  · have hs' : rho (u, v) eSym = eSym := by
      have h := hs
      change rho (u, v) (tau eSym) = eSym at h
      rwa [tau_eSym] at h
    have h11' : rho (u, v) (eW 1 1) = eW 1 1 := by
      have h := h11
      change rho (u, v) (tau (eW 1 1)) = eW 1 1 at h
      rwa [tau_E11] at h
    obtain ⟨y, w, y', w', hu', hv'⟩ := uMat_zero_of_fix hu hv hs' h11'
    have e : Multiplicative.toAdd ((rho (u, v) * tau) (eW 0 1)) = Matrix.single 1 0 1 := by
      change Multiplicative.toAdd (rho (u, v) (tau (eW 0 1))) = _
      rw [tau_E01]
      change mat u * Matrix.single 1 0 1 * (mat v)ᵀ = Matrix.single 1 0 1
      rw [hu', hv', uMat_E10, Matrix.single_zero, add_zero]
    refine ⟨Or.inr ?_, fun h => ?_⟩
    · apply Multiplicative.toAdd.injective
      rw [e]
      exact (by decide : (Matrix.single 1 0 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        Matrix.single 0 1 1 + (Matrix.single 1 0 1 + Matrix.single 0 1 1))
    · have h' := congrArg Multiplicative.toAdd h
      rw [e] at h'
      exact absurd h' (by decide)

theorem le_R1R1_of_mem_aSet_two {A : Subgroup (MulAut WMod)} (hA : A ∈ E3.aSet 2 T0) :
    A ≤ (R1.prod R1).map rho := by
  obtain ⟨hAT, -, hA2, -⟩ := id hA
  have hAp : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by rw [pow_one]; exact hA2.2 _ a.2)⟩
  have hs : ∀ a ∈ A, a eSym = eSym := by
    by_contra h
    push Not at h
    obtain ⟨a, ha, haD⟩ := h
    exact not_mem_aSet_two_of_orbit hAp (fun y hy => T0_eSym (hAT hy)) ha haD hA
  have h11 : ∀ a ∈ A, a (eW 1 1) = eW 1 1 := by
    by_contra h
    push Not at h
    obtain ⟨a, ha, haD⟩ := h
    exact not_mem_aSet_two_of_orbit hAp (fun y hy => T0_E11 (hAT hy) (hs y hy)) ha haD hA
  have h01 : ∀ a ∈ A, a (eW 0 1) = eW 0 1 := by
    by_contra h
    push Not at h
    obtain ⟨a, ha, haD⟩ := h
    exact not_mem_aSet_two_of_orbit hAp (fun y hy => (T0_E01 (hAT hy) (hs y hy) (h11 y hy)).1)
      ha haD hA
  exact fun a ha => (T0_E01 (hAT ha) (hs a ha) (h11 a ha)).2 (h01 a ha)

theorem R1R1_le_A1_sup_A2 : (R1.prod R1).map rho ≤ A1 ⊔ A2 := by
  rintro _ ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
  have e : ((g, h) : ↥SL32 × ↥SL32) = (g, 1) * (1, h) := by simp
  rw [e, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨(g, 1), ⟨hg, Subgroup.one_mem _⟩, rfl⟩)
    (Subgroup.mem_sup_right ⟨(1, h), ⟨Subgroup.one_mem _, hh⟩, rfl⟩)

theorem iSup_aSet_two_eq {Y : Subgroup (MulAut WMod)} (hYn : Y ≤ norm) (hY2 : IsPGroup 2 Y)
    (hUY : (U3.prod U3).map rho ≤ Y) :
    ⨆ A ∈ E3.aSet 2 Y, A = (R1.prod R1).map rho := by
  have hYT := le_T0_of_isPGroup hYn hY2 hUY
  refine le_antisymm (iSup₂_le fun A hA => le_R1R1_of_mem_aSet_two ⟨hA.1.trans hYT, hA.2⟩) ?_
  refine R1R1_le_A1_sup_A2.trans (sup_le ?_ ?_)
  · exact le_iSup₂_of_le (f := fun A (_ : A ∈ E3.aSet 2 Y) => A) A1 (A1_mem_aSet hUY) le_rfl
  · exact le_iSup₂_of_le (f := fun A (_ : A ∈ E3.aSet 2 Y) => A) A2 (A2_mem_aSet hUY) le_rfl

theorem axMat_single : ∀ (y w y' w' : ZMod 2) (i j : Fin 3), i ≠ 2 → j ≠ 2 →
    axMat y w * Matrix.single i j 1 * (axMat y' w')ᵀ = Matrix.single i j 1 := by
  decide

theorem eW_mem_fixV_R1R1 {i j : Fin 3} (hi : i ≠ 2) (hj : j ≠ 2) :
    eW i j ∈ fixV ((R1.prod R1).map rho) := by
  rintro _ ⟨⟨g, h⟩, ⟨⟨y, w, hg⟩, ⟨y', w', hh⟩⟩, rfl⟩
  apply Multiplicative.toAdd.injective
  change mat g * Matrix.single i j 1 * (mat h)ᵀ = Matrix.single i j 1
  rw [hg, hh]
  exact axMat_single y w y' w' i j hi hj

@[expose] def cBm : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 1, 0; 0, 0, 1]

theorem det_cBm : cBm.det ≠ 0 := by decide

@[expose] noncomputable def cB : ↥SL32 := slOfMat cBm det_cBm

theorem mat_cB : mat cB = cBm := rfl

theorem cB_pow_three : cB ^ 3 = 1 :=
  eq_of_mat_eq (by rw [mat_pow, mat_cB, mat_one]; decide)

theorem cB_ne_one : cB ≠ 1 := fun h => by
  have h1 := congrArg mat h
  rw [mat_cB, mat_one] at h1
  exact absurd h1 (by decide)

theorem orderOf_cB : orderOf cB = 3 := orderOf_eq_prime cB_pow_three cB_ne_one

theorem mat_cB_inv : mat cB⁻¹ = cBm * cBm := by
  have h : cB⁻¹ = cB ^ 2 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, cB_pow_three]
  rw [h, mat_pow, mat_cB, sq]

theorem cBm_conj_axMat : ∀ x y : ZMod 2, ∃ x' y' : ZMod 2,
    cBm * axMat x y * (cBm * cBm) = axMat x' y' := by
  decide

theorem cB_mem_normalizer_R1 : cB ∈ Subgroup.normalizer (R1 : Set ↥SL32) := by
  have key : ∀ g ∈ R1, cB * g * cB⁻¹ ∈ R1 := by
    rintro g ⟨x, y, hg⟩
    obtain ⟨x', y', h⟩ := cBm_conj_axMat x y
    exact ⟨x', y', by rw [mat_mul, mat_mul, hg, mat_cB, mat_cB_inv, h]⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key g, fun h => ?_⟩
  have e : g = cB * (cB * (cB * g * cB⁻¹) * cB⁻¹) * cB⁻¹ := by
    have h33 : cB * cB * cB = 1 := by
      have := cB_pow_three
      rwa [pow_succ, pow_two] at this
    have h3 : cB * (cB * (cB * g * cB⁻¹) * cB⁻¹) * cB⁻¹ =
        (cB * cB * cB) * g * (cB * cB * cB)⁻¹ := by group
    rw [h3, h33, one_mul, inv_one, mul_one]
  rw [e]
  exact key _ (key _ h)

@[expose] noncomputable def PB : Subgroup (MulAut WMod) :=
  ((Subgroup.zpowers cB).prod (Subgroup.zpowers cB)).map rho

theorem PB_le_normalizer : PB ≤ Subgroup.normalizer (((R1.prod R1).map rho : Subgroup _) :
    Set (MulAut WMod)) := by
  have hz : Subgroup.zpowers cB ≤ Subgroup.normalizer (R1 : Set ↥SL32) :=
    Subgroup.zpowers_le.mpr cB_mem_normalizer_R1
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ (a b : ↥SL32), a ∈ Subgroup.normalizer (R1 : Set ↥SL32) →
      b ∈ Subgroup.normalizer (R1 : Set ↥SL32) → ∀ x ∈ (R1.prod R1).map rho,
        rho (a, b) * x * (rho (a, b))⁻¹ ∈ (R1.prod R1).map rho := by
    rintro a b ha hb _ ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
    refine ⟨(a * g * a⁻¹, b * h * b⁻¹), ⟨(Subgroup.mem_normalizer_iff.mp ha g).mp hg,
      (Subgroup.mem_normalizer_iff.mp hb h).mp hh⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  intro x
  refine ⟨key a b (hz ha) (hz hb) x, fun hx => ?_⟩
  have h1 := key a⁻¹ b⁻¹ ((Subgroup.normalizer _).inv_mem (hz ha))
    ((Subgroup.normalizer _).inv_mem (hz hb)) _ hx
  have e : rho (a⁻¹, b⁻¹) * (rho (a, b) * x * (rho (a, b))⁻¹) * (rho (a⁻¹, b⁻¹))⁻¹ = x := by
    have : rho (a⁻¹, b⁻¹) = (rho (a, b))⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    group
  rwa [e] at h1

theorem cBm_pow_fix : ∀ m n : Fin 3, (∀ k l : Fin 3, k ≠ 2 → l ≠ 2 →
    cBm ^ (m : ℕ) * Matrix.single k l 1 * (cBm ^ (n : ℕ))ᵀ = Matrix.single k l 1) →
      m = 0 ∧ n = 0 := by
  decide

theorem eq_one_of_mem_PB_of_fix {x : MulAut WMod} (hx : x ∈ PB)
    (h : ∀ X ∈ fixV ((R1.prod R1).map rho), x X = X) : x = 1 := by
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hm : ∀ k : ℤ, cB ^ k = cB ^ ((k % 3).toNat) := by
    intro k
    have h1 : cB ^ k = cB ^ (k % 3) := by
      have := zpow_mod_orderOf cB k
      rw [orderOf_cB] at this
      exact this.symm
    rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  have hi3 : (i % 3).toNat < 3 := by omega
  have hj3 : (j % 3).toNat < 3 := by omega
  rw [hm i, hm j] at h ⊢
  have key := cBm_pow_fix ⟨_, hi3⟩ ⟨_, hj3⟩ (by
    intro k l hk hl
    have h1 := congrArg Multiplicative.toAdd (h _ (eW_mem_fixV_R1R1 hk hl))
    change mat (cB ^ (i % 3).toNat) * Matrix.single k l 1 *
      (mat (cB ^ (j % 3).toNat))ᵀ = Matrix.single k l 1 at h1
    rw [mat_pow, mat_pow, mat_cB] at h1
    exact h1)
  have hi0 : (i % 3).toNat = 0 := congrArg Fin.val key.1
  have hj0 : (j % 3).toNat = 0 := congrArg Fin.val key.2
  rw [hi0, hj0, pow_zero]
  exact map_one rho

theorem PB_le_img : PB ≤ img := Subgroup.map_le_range _ _

theorem card_PB : Nat.card ↥PB = 3 ^ 2 := by
  rw [PB, Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, Nat.card_zpowers,
    orderOf_cB]
  norm_num

theorem isElemAbelian_PB : IsElemAbelian 3 PB := by
  have hcomm : ∀ a ∈ PB, ∀ b ∈ PB, a * b = b * a := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ _ ⟨⟨a', b'⟩, ⟨ha', hb'⟩, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    obtain ⟨j', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext ((Commute.zpow_zpow_self cB i i').eq) ((Commute.zpow_zpow_self cB j j').eq)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← map_pow]
  have e : ((cB ^ i, cB ^ j) : ↥SL32 × ↥SL32) ^ 3 = 1 := by
    refine Prod.ext ?_ ?_
    · change (cB ^ i) ^ 3 = 1
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, cB_pow_three,
        _root_.one_zpow]
    · change (cB ^ j) ^ 3 = 1
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, cB_pow_three,
        _root_.one_zpow]
  rw [e, map_one]

theorem apply_mem_fixV_of_mem_normalizer {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) {w : W}
    (hw : w ∈ fixV X) : y w ∈ fixV X :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hy hw

end L3Wr

end H

end CFSG.Quasithin
