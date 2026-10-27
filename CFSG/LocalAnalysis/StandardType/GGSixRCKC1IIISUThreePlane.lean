module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISULevi
public import CFSG.GroupTheory.InvolutionPair

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCKK1IIISU CFSG.StandardType.SUTransvection

variable {k : ℕ}

private noncomputable def suZHom (hk : 4 ≤ k) :
    Multiplicative (Fin 4 → ZMod 2) →* SUG k :=
  MonoidHom.mk' (fun v => suZ hk v.toAdd) (fun v w => (suZ_add hk v.toAdd w.toAdd).symm)

private theorem suZHom_apply (hk : 4 ≤ k) (v : Multiplicative (Fin 4 → ZMod 2)) :
    suZHom hk v = suZ hk v.toAdd := rfl

private theorem suZHom_injective (hk : 4 ≤ k) : Function.Injective (suZHom hk) := by
  intro v w h
  exact Multiplicative.toAdd.injective (suZ_injective hk h)

theorem rank_fin_two_le_one_of_det_eq_zero {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 0) : A.rank ≤ 1 := by
  have hdet : LinearMap.det (Matrix.toLin' A) = 0 := by
    rw [LinearMap.det_toLin', hA]
  have hker : LinearMap.ker (Matrix.toLin' A) ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  have hposne : Module.finrank K (LinearMap.ker (Matrix.toLin' A)) ≠ 0 := by
    intro h0
    exact hker ((Submodule.finrank_eq_zero).mp h0)
  have hpos : 0 < Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := Nat.pos_of_ne_zero hposne
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have hdom : Module.finrank K (Fin 2 → K) = 2 := Module.finrank_fin_fun K
  rw [hdom] at hsum
  have hle : Module.finrank K (LinearMap.range (Matrix.toLin' A)) ≤ 1 := by omega
  rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun K (Fin 2)) (Pi.basisFun K (Fin 2)),
    Matrix.toLin_eq_toLin']
  exact hle

private noncomputable def rckSUc_E (hk : 4 ≤ k) : Matrix (Fin k) (Fin 2) SUF :=
  fun i a => if rckSUc_e hk a = i then 1 else 0

private noncomputable def rckSUc_F (hk : 4 ≤ k) : Matrix (Fin 2) (Fin k) SUF :=
  fun a j => if rckSUc_e' hk a = j then 1 else 0

private theorem rckSUc_M_eq_mul_block (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    rckSUc_M hk v = rckSUc_E hk * rckSUc_A v * rckSUc_F hk := by
  ext i j
  by_cases hi0 : rckSUc_e hk 0 = i <;> by_cases hi1 : rckSUc_e hk 1 = i <;>
    by_cases hj0 : rckSUc_e' hk 0 = j <;> by_cases hj1 : rckSUc_e' hk 1 = j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, rckSUc_E, rckSUc_F, rckSUc_M,
      Matrix.add_apply, hi0, hi1, hj0, hj1, rckSUc_A_apply_00, rckSUc_A_apply_01,
      rckSUc_A_apply_10, rckSUc_A_apply_11]; ring

private theorem rank_suZ_sub_one_le_one (hk : 4 ≤ k) {v : Fin 4 → ZMod 2}
    (hq : s5q v = 0) : (mat SUσ k (suZ hk v) - 1).rank ≤ 1 := by
  have hmat : mat SUσ k (suZ hk v) - 1 = rckSUc_M hk v := by
    rw [mat_apply, suZ_val, rckSUc_M_eq_suCorner]
    abel
  rw [hmat, rckSUc_M_eq_mul_block]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
  refine rank_fin_two_le_one_of_det_eq_zero _ ?_
  rw [rckSUc_det_A, hq, rckSUc_alpha, map_zero]


private def s5G1 : Fin 4 → ZMod 2 := ![0, 0, 1, 0]

private def s5G2 : Fin 4 → ZMod 2 := ![1, 0, 1, 0]

private def s5G3 : Fin 4 → ZMod 2 := ![0, 1, 1, 1]

private theorem s5h1_G1 :
    (s5h1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec ![0, 0, 1, 0] = s5G2 := by
  decide +kernel

private theorem s5h2_G2 : (s5h2 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5G2 = s5G3 := by
  decide +kernel

private theorem s5q_six (A : Fin 4 → ZMod 2)
    (hA0 : A ≠ 0) (hAR : A ≠ s5R) (hq : s5q A = 1) (hqR : s5q (A + s5R) = 1) :
    A = s5G1 ∨ A = s5G1 + s5R ∨ A = s5G2 ∨ A = s5G2 + s5R ∨
      A = s5G3 ∨ A = s5G3 + s5R := by
  revert A hA0 hAR hq hqR
  decide +kernel

private theorem closure_pair_mul_right {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    Subgroup.closure ({x, y * x} : Set G) = Subgroup.closure ({x, y} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · rw [h]
      exact Subgroup.subset_closure (by simp)
    · rw [h]
      have h1 : y ∈ Subgroup.closure ({x, y} : Set G) :=
        Subgroup.subset_closure (by simp)
      have h2 : x ∈ Subgroup.closure ({x, y} : Set G) :=
        Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem _ h1 h2
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · rw [h]
      exact Subgroup.subset_closure (by simp)
    · rw [h]
      have hy : (y * x) * x = y := by rw [mul_assoc, hx, mul_one]
      have h1 : y * x ∈ Subgroup.closure ({x, y * x} : Set G) :=
        Subgroup.subset_closure (by simp)
      have h2 : x ∈ Subgroup.closure ({x, y * x} : Set G) :=
        Subgroup.subset_closure (by simp)
      have h3 : (y * x) * x ∈ Subgroup.closure ({x, y * x} : Set G) :=
        Subgroup.mul_mem _ h1 h2
      rwa [hy] at h3

private theorem closure_suR_suZ_add_R (hk : 4 ≤ k) (w : Fin 4 → ZMod 2) :
    Subgroup.closure ({suR hk, suZ hk (w + s5R)} : Set (SUG k)) =
      Subgroup.closure ({suR hk, suZ hk w} : Set (SUG k)) := by
  have hy : suZ hk (w + s5R) = suZ hk w * suR hk := by
    rw [← suZ_add]
    rfl
  rw [hy]
  exact closure_pair_mul_right (by simpa [pow_two] using rckSU_suR_sq hk)

theorem rckSU_exists_conj_suV_of_fourAt
    {k : ℕ} (hk : 4 ≤ k) {V : Subgroup (SUG k)}
    (hFour : FourAt (⊤ : Subgroup (SUG k)) V (suR hk))
    (hCore : CoreCommAt (⊤ : Subgroup (SUG k)) V (suR hk)) :
    ∃ c ∈ Subgroup.centralizer ({suR hk} : Set (SUG k)),
      V = (suV hk).map (MulAut.conj c).toMonoidHom := by
  classical
  have hVZ : V ≤ suZ0 hk := by
    refine rckSU_elemAbelian_le_suZ0 hk V hFour.1 hFour.2.2.1 ?_
    intro v hv y hy
    exact hCore v hv y (by simpa only [top_inf_eq] using hy)
  have hVrange : V ≤ (suZHom hk).range := hVZ
  let W : Subgroup (Multiplicative (Fin 4 → ZMod 2)) := V.comap (suZHom hk)
  have hWmap : W.map (suZHom hk) = V := Subgroup.map_comap_eq_self hVrange
  have hWcard : Nat.card W = 4 := by
    rw [← Subgroup.card_map_of_injective (K := W) (suZHom_injective hk), hWmap,
      hFour.2.2.2.1]
  have hRmem : Multiplicative.ofAdd s5R ∈ W := hFour.1
  have hq : ∀ w ∈ W, w ≠ 1 → s5q w.toAdd = 1 := by
    intro w hw hw1
    have hmem : suZ hk w.toAdd ∈ V := hw
    have hne : suZ hk w.toAdd ≠ 1 := by
      intro h
      have h0 : w.toAdd = 0 := suZ_injective hk (by rw [h, suZ_zero])
      apply hw1
      exact Multiplicative.toAdd.injective (by simpa using h0)
    obtain ⟨j, -, hj⟩ := hFour.2.2.2.2.2 (suZ hk w.toAdd) hmem hne
    have hrank2 : (mat SUσ k (suZ hk w.toAdd) - 1).rank = 2 := by
      rw [hj, rank_mat_conj_sub_one, rckSU_rank_suR_sub_one hk]
    by_contra hq0
    have hq00 : s5q w.toAdd = 0 :=
      (by decide : ∀ a : ZMod 2, a ≠ 1 → a = 0) _ hq0
    have hle := rank_suZ_sub_one_le_one hk hq00
    omega
  have hR2 : Multiplicative.ofAdd s5R * Multiplicative.ofAdd s5R = 1 := by
    apply Multiplicative.toAdd.injective
    change s5R + s5R = (0 : Fin 4 → ZMod 2)
    funext i
    exact (by decide : ∀ a : ZMod 2, a + a = 0) (s5R i)
  have hR1 : Multiplicative.ofAdd s5R ≠ 1 := fun h =>
    (by decide +kernel : s5R ≠ 0) (congrArg Multiplicative.toAdd h)
  have hex : ∃ A ∈ W, A ≠ 1 ∧ A ≠ Multiplicative.ofAdd s5R := by
    by_contra hcon
    push Not at hcon
    have hz : W ≤ Subgroup.zpowers (Multiplicative.ofAdd s5R) := by
      intro A hA
      by_cases h1 : A = 1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hcon A hA h1]; exact Subgroup.mem_zpowers _
    have hle := Subgroup.card_le_of_le hz
    have hRpow : Multiplicative.ofAdd s5R ^ 2 = 1 := by
      rw [pow_two]; exact hR2
    rw [hWcard, Nat.card_zpowers, orderOf_eq_prime hRpow hR1] at hle
    omega
  obtain ⟨A, hAW, hA1, hAR⟩ := hex
  have hAsq : A * A = 1 := by
    apply Multiplicative.toAdd.injective
    change A.toAdd + A.toAdd = (0 : Fin 4 → ZMod 2)
    funext i
    exact (by decide : ∀ a : ZMod 2, a + a = 0) (A.toAdd i)
  have hA0 : A.toAdd ≠ 0 := fun h0 =>
    hA1 (Multiplicative.toAdd.injective (by simpa using h0))
  have hAR' : A.toAdd ≠ s5R := fun h => hAR (Multiplicative.toAdd.injective h)
  have hAq : s5q A.toAdd = 1 := hq A hAW hA1
  have hARmem : A * Multiplicative.ofAdd s5R ∈ W := W.mul_mem hAW hRmem
  have hARne1 : A * Multiplicative.ofAdd s5R ≠ 1 := by
    intro h
    apply hAR
    calc A = A * Multiplicative.ofAdd s5R * Multiplicative.ofAdd s5R := by
            rw [mul_assoc, hR2, mul_one]
      _ = 1 * Multiplicative.ofAdd s5R := by rw [h]
      _ = Multiplicative.ofAdd s5R := one_mul _
  have hqAR : s5q (A.toAdd + s5R) = 1 := by
    have := hq (A * Multiplicative.ofAdd s5R) hARmem hARne1
    simpa using this
  have hAsix := s5q_six A.toAdd hA0 hAR' hAq hqAR
  have hWclosure : Subgroup.closure ({A, Multiplicative.ofAdd s5R} : Set _) = W := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact hAW
      · exact hRmem
    · rw [hWcard,
        CFSG.GroupTheory.card_closure_pair_eq_four hAsq hR2 (mul_comm _ _) hA1 hR1 hAR]
  have hVeq : V = Subgroup.closure ({suR hk, suZ hk A.toAdd} : Set (SUG k)) := by
    rw [← hWmap, ← hWclosure, MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, suZHom_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact ⟨Multiplicative.ofAdd s5R, Or.inr rfl, rfl⟩
      · exact ⟨A, Or.inl rfl, rfl⟩
  obtain ⟨c1, c2, hc1r, hc2r, hc1act, hc2act⟩ := rckSU_levi hk
  have hc1conj : c1 * suR hk * c1⁻¹ = suR hk := by
    rw [hc1r, mul_assoc, mul_inv_cancel, mul_one]
  have hc2conj : c2 * suR hk * c2⁻¹ = suR hk := by
    rw [hc2r, mul_assoc, mul_inv_cancel, mul_one]
  have hc1_suR : (MulAut.conj c1) (suR hk) = suR hk := by
    rw [MulAut.conj_apply]; exact hc1conj
  have hmap1 : (suV hk).map (MulAut.conj (1 : SUG k)).toMonoidHom =
      Subgroup.closure ({suR hk, suZ hk s5G1} : Set (SUG k)) := by
    rw [show (MulAut.conj (1 : SUG k)).toMonoidHom = MonoidHom.id (SUG k) from by
      ext x; simp]
    rw [Subgroup.map_id]
    rfl
  have hmapc1 : (suV hk).map (MulAut.conj c1).toMonoidHom =
      Subgroup.closure ({suR hk, suZ hk s5G2} : Set (SUG k)) := by
    have h1 : (MulAut.conj c1).toMonoidHom (suZ hk ![0, 1, 0, 0]) = suR hk := hc1_suR
    have h2 : (MulAut.conj c1).toMonoidHom (suZ hk ![0, 0, 1, 0]) = suZ hk s5G2 := by
      change (MulAut.conj c1) (suZ hk ![0, 0, 1, 0]) = suZ hk s5G2
      rw [MulAut.conj_apply, hc1act, s5h1_G1]
    rw [suV, MonoidHom.map_closure, Set.image_pair, h1, h2]
  have hmapc21 : (suV hk).map (MulAut.conj (c2 * c1)).toMonoidHom =
      Subgroup.closure ({suR hk, suZ hk s5G3} : Set (SUG k)) := by
    have h1 : (MulAut.conj (c2 * c1)).toMonoidHom (suZ hk ![0, 1, 0, 0]) = suR hk := by
      change (MulAut.conj (c2 * c1)) (suZ hk ![0, 1, 0, 0]) = suR hk
      rw [MulAut.conj_apply]
      calc (c2 * c1) * suR hk * (c2 * c1)⁻¹
          = c2 * (c1 * suR hk * c1⁻¹) * c2⁻¹ := by group
        _ = c2 * suR hk * c2⁻¹ := by rw [hc1conj]
        _ = suR hk := hc2conj
    have h2 : (MulAut.conj (c2 * c1)).toMonoidHom (suZ hk ![0, 0, 1, 0]) = suZ hk s5G3 := by
      change (MulAut.conj (c2 * c1)) (suZ hk ![0, 0, 1, 0]) = suZ hk s5G3
      rw [MulAut.conj_apply]
      calc (c2 * c1) * suZ hk ![0, 0, 1, 0] * (c2 * c1)⁻¹
          = c2 * (c1 * suZ hk ![0, 0, 1, 0] * c1⁻¹) * c2⁻¹ := by group
        _ = c2 * suZ hk s5G2 * c2⁻¹ := by rw [hc1act, s5h1_G1]
        _ = suZ hk s5G3 := by rw [hc2act, s5h2_G2]
    rw [suV, MonoidHom.map_closure, Set.image_pair, h1, h2]
  have hc21r : (c2 * c1) * suR hk = suR hk * (c2 * c1) := by
    calc (c2 * c1) * suR hk = c2 * (c1 * suR hk) := by rw [mul_assoc]
      _ = c2 * (suR hk * c1) := by rw [hc1r]
      _ = (c2 * suR hk) * c1 := by rw [mul_assoc]
      _ = (suR hk * c2) * c1 := by rw [hc2r]
      _ = suR hk * (c2 * c1) := by rw [mul_assoc]
  rcases hAsix with hA | hA | hA | hA | hA | hA
  · refine ⟨1, by simp, ?_⟩
    rw [hVeq, hA, hmap1]
  · refine ⟨1, by simp, ?_⟩
    rw [hVeq, hA, closure_suR_suZ_add_R hk s5G1, hmap1]
  · refine ⟨c1, Subgroup.mem_centralizer_singleton_iff.mpr hc1r, ?_⟩
    rw [hVeq, hA, hmapc1]
  · refine ⟨c1, Subgroup.mem_centralizer_singleton_iff.mpr hc1r, ?_⟩
    rw [hVeq, hA, closure_suR_suZ_add_R hk s5G2, hmapc1]
  · refine ⟨c2 * c1, Subgroup.mem_centralizer_singleton_iff.mpr hc21r, ?_⟩
    rw [hVeq, hA, hmapc21]
  · refine ⟨c2 * c1, Subgroup.mem_centralizer_singleton_iff.mpr hc21r, ?_⟩
    rw [hVeq, hA, closure_suR_suZ_add_R hk s5G3, hmapc21]

theorem rckSU_exists_conj_suV_of_rank_two
    {k : ℕ} (hk : 4 ≤ k) {V : Subgroup (SUG k)} {r : SUG k}
    (hFour : FourAt (⊤ : Subgroup (SUG k)) V r)
    (hCore : CoreCommAt (⊤ : Subgroup (SUG k)) V r)
    (hRank : (mat SUσ k r - 1).rank = 2) :
    ∃ g : SUG k, r = g * suR hk * g⁻¹ ∧ V = (suV hk).map (MulAut.conj g).toMonoidHom := by
  have hr : orderOf r = 2 :=
    orderOf_eq_prime (hFour.2.2.1.2 r hFour.1) hFour.2.2.2.2.1
  have hs : orderOf (suR hk) = 2 := orderOf_eq_prime (rckSU_suR_sq hk) (suR_ne_one hk)
  obtain ⟨g₀, hg₀⟩ := rckSU_exists_conj_of_rank_eq hr hs
    (hRank.trans (rckSU_rank_suR_sub_one hk).symm)
  let e : (⊤ : Subgroup (SUG k)) ≃* SUG k := Subgroup.topEquiv.trans (MulAut.conj g₀⁻¹)
  let V' : Subgroup (SUG k) := (V.subgroupOf ⊤).map e.toMonoidHom
  have her : e ⟨r, Subgroup.mem_top _⟩ = suR hk := by
    change g₀⁻¹ * r * (g₀⁻¹)⁻¹ = suR hk
    rw [hg₀]
    group
  have hFour' : FourAt (⊤ : Subgroup (SUG k)) V' (suR hk) := by
    rw [← her]
    exact fourAt_map_mulEquiv e (Subgroup.mem_top _) hFour
  have hCore' : CoreCommAt (⊤ : Subgroup (SUG k)) V' (suR hk) := by
    rw [← her]
    exact coreCommAt_map_mulEquiv e (Subgroup.mem_top _) hCore
  obtain ⟨c, hc, hVc⟩ := rckSU_exists_conj_suV_of_fourAt hk hFour' hCore'
  have hc_conj : c * suR hk * c⁻¹ = suR hk := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_assoc, mul_inv_cancel, mul_one]
  have hV' : V' = V.map (MulAut.conj g₀⁻¹).toMonoidHom := by
    have hcomp : V' = (V.subgroupOf ⊤).map
        ((MulAut.conj g₀⁻¹).toMonoidHom.comp (Subgroup.subtype ⊤)) := rfl
    rw [hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le (le_top : V ≤ (⊤ : Subgroup (SUG k)))]
  have hVmap : V = V'.map (MulAut.conj g₀).toMonoidHom := by
    rw [hV', Subgroup.map_map]
    rw [show (MulAut.conj g₀).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom =
        MonoidHom.id (SUG k) from by
      ext x : 1
      show (MulAut.conj g₀) ((MulAut.conj g₀⁻¹) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group,
      Subgroup.map_id]
  have hgcomp : (MulAut.conj (g₀ * c)).toMonoidHom =
      (MulAut.conj g₀).toMonoidHom.comp (MulAut.conj c).toMonoidHom := by
    ext x : 1
    show (MulAut.conj (g₀ * c)) x = (MulAut.conj g₀) ((MulAut.conj c) x)
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  refine ⟨g₀ * c, ?_, ?_⟩
  · calc r = g₀ * suR hk * g₀⁻¹ := hg₀
      _ = g₀ * (c * suR hk * c⁻¹) * g₀⁻¹ := by rw [hc_conj]
      _ = (g₀ * c) * suR hk * (g₀ * c)⁻¹ := by group
  · calc V = V'.map (MulAut.conj g₀).toMonoidHom := hVmap
      _ = ((suV hk).map (MulAut.conj c).toMonoidHom).map
            (MulAut.conj g₀).toMonoidHom := by rw [hVc]
      _ = (suV hk).map (MulAut.conj (g₀ * c)).toMonoidHom := by
            rw [hgcomp, Subgroup.map_map]

end CFSG.StandardType.RCKC1
