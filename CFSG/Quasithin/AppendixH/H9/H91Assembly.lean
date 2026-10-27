module

public import CFSG.Quasithin.AppendixH.H9.ClauseTransport
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer
public import CFSG.Quasithin.AppendixH.H9.PairStabilizer

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem map_V1n_of_mem_Lg {n : ℕ} {l : MulAut (PairN n)} (hl : l ∈ Lg n) :
    (V1n n).map (l : MulAut (PairN n)).toMonoidHom = V1n n := by
  have hs := Lg_le_stabSub_V1n hl
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_stabSub.mp hs y).2 hy
  · intro hx
    have h2 : l (l⁻¹ x) = x := MulEquiv.apply_symm_apply l x
    refine ⟨l⁻¹ x, ?_, h2⟩
    have hx' : l (l⁻¹ x) ∈ V1n n := by rw [h2]; exact hx
    exact (mem_stabSub.mp hs (l⁻¹ x)).1 hx'

theorem map_V2n_of_mem_Lg {n : ℕ} {l : MulAut (PairN n)} (hl : l ∈ Lg n) :
    (V2n n).map (l : MulAut (PairN n)).toMonoidHom = V2n n := by
  have hs := Lg_le_stabSub_V2n hl
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_stabSub.mp hs y).2 hy
  · intro hx
    have h2 : l (l⁻¹ x) = x := MulEquiv.apply_symm_apply l x
    refine ⟨l⁻¹ x, ?_, h2⟩
    have hx' : l (l⁻¹ x) ∈ V2n n := by rw [h2]; exact hx
    exact (mem_stabSub.mp hs (l⁻¹ x)).1 hx'

theorem eq_of_zpowers_eq_of_sq_eq_one {G : Type*} [Group G] {v x : G}
    (h : Subgroup.zpowers v = Subgroup.zpowers x) (hx : x ^ 2 = 1) (hx1 : x ≠ 1) : v = x := by
  have hv : v ∈ Subgroup.zpowers x := h ▸ Subgroup.mem_zpowers v
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · exfalso
    have h1 : x ^ (2 * j) = 1 := by rw [zpow_mul]; simp [hx]
    have h2 : Subgroup.zpowers (x ^ (2 * j)) = ⊥ := by rw [h1]; exact Subgroup.zpowers_one_eq_bot
    rw [h2] at h
    have hxm : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [← h] at hxm
    exact hx1 (Subgroup.mem_bot.mp hxm)
  · rw [zpow_add_one, zpow_mul]
    simp [hx]

section Generic

variable {V : Type*} [CommGroup V]

theorem conjAut_stabSub_of_map_eq {g : MulAut V} {U : Subgroup V}
    (h : U.map (g : MulAut V).toMonoidHom = U) : conjAut g (stabSub U) = stabSub U := by
  rw [conjAut_stabSub, h]

theorem fixV_conjAut_inf_stabSub_inf {g : MulAut V} {U : Subgroup V}
    (h : U.map (g : MulAut V).toMonoidHom = U) (T : Subgroup (MulAut V)) :
    fixV (conjAut g T ⊓ stabSub U) ⊓ U =
      (fixV (T ⊓ stabSub U) ⊓ U).map (g : MulAut V).toMonoidHom := by
  have h1 : conjAut g T ⊓ stabSub U = conjAut g (T ⊓ stabSub U) := by
    rw [conjAut_inf, conjAut_stabSub_of_map_eq h]
  rw [h1, conjAut_eq_map, fixV_map_conj_eq, map_inf_subgroup, h]

theorem commOn_twoResidual_centSub_map {g : MulAut V} {L : Subgroup (MulAut V)}
    (hL : conjAut g L = L) {W : Subgroup V} (hW : W.map (g : MulAut V).toMonoidHom = W) (v : V) :
    commOn W (twoResidual (L ⊓ centSub (Subgroup.zpowers (g v)))) =
      (commOn W (twoResidual (L ⊓ centSub (Subgroup.zpowers v)))).map
        (g : MulAut V).toMonoidHom := by
  have h1 : L ⊓ centSub (Subgroup.zpowers (g v)) =
      conjAut g (L ⊓ centSub (Subgroup.zpowers v)) := by
    rw [conjAut_inf, hL, conjAut_centSub, map_zpowers]
  have h2 := commOn_conjAut g W (twoResidual (L ⊓ centSub (Subgroup.zpowers v)))
  rw [hW, ← twoResidual_conjAut, ← h1] at h2
  exact h2

end Generic

private theorem H91Clause4_congr {n : ℕ} {T T' : Subgroup (MulAut (PairN n))} {v₁ v₁' v₂ v₂' : PairN n}
    (hT : T = T') (h₁ : v₁ = v₁') (h₂ : v₂ = v₂') (h : H91Clause4 n T v₁ v₂) :
    H91Clause4 n T' v₁' v₂' := by
  subst hT h₁ h₂
  exact h

private theorem mem_perpN_zpowers_iff {n : ℕ} {x y : PairN n} :
    x ∈ perpN n (Subgroup.zpowers y) ↔ polarN n x y = 0 := by
  refine ⟨fun h => mem_perpN.mp h y (Subgroup.mem_zpowers y), fun h => ?_⟩
  rw [mem_perpN]
  intro s hs
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  rw [zpow_eq_zpow_emod' k (pairN_sq y)]
  rcases Int.emod_two_eq_zero_or_one k with h2 | h2
  · simp [h2, polarN_comm x 1, polarN_one_left]
  · simpa [h2] using h

private theorem polarN_pairVec_ez {m : ℕ} (b : Fin (m + 1) → ZMod 2) :
    polarN (m + 1) (pairVec 0 b) (pairVec (ez m) 0) = b 0 := by
  rw [polarN_pairVec]
  simp [ez, dotProduct, Pi.single_apply]

theorem exists_normalize_pair (m : ℕ) {T : Subgroup (MulAut (PairN (m + 1)))}
    (hT : IsSylowIn 2 T (Mg (m + 1))) {v₁ : PairN (m + 1)}
    (hfix : fixV (T ⊓ stabSub (V1n (m + 1))) ⊓ V1n (m + 1) = Subgroup.zpowers v₁) :
    ∃ l ∈ Lg (m + 1), T = conjAut l (T0 (m + 1)) ∧ v₁ = l (pairVec (ez m) 0) := by
  obtain ⟨l, hl, hTl⟩ := exists_Lg_conj_T0 (n := m + 1) (Nat.succ_pos m) hT
  refine ⟨l, hl, hTl, ?_⟩
  subst hTl
  have h2 := fixV_conjAut_inf_stabSub_inf (map_V1n_of_mem_Lg hl) (T0 (m + 1))
  have h3 := map_zpowers l (pairVec (ez m) 0)
  have h4 : Subgroup.zpowers v₁ = Subgroup.zpowers (l (pairVec (ez m) 0)) :=
    hfix.symm.trans (h2.trans ((congrArg (Subgroup.map (l : MulAut (PairN (m + 1))).toMonoidHom)
      (fixV_T0_inf_stabSub_inf_V1n m)).trans h3))
  have hx2 : (l (pairVec (ez m) 0)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, ← pow_two, pairN_sq, map_one]
  have hx1 : l (pairVec (ez m) 0) ≠ 1 := by
    intro h
    have h3 : pairVec (ez m) 0 = 1 := (map_eq_one_iff l (EquivLike.injective l)).mp h
    rw [pairVec_one, pairVec_inj] at h3
    have h4 := congrFun h3.1 0
    simp [ez] at h4
  exact eq_of_zpowers_eq_of_sq_eq_one h4 hx2 hx1

theorem h91_clause3 (n : ℕ) (hn : n = 4 ∨ n = 5) (T : Subgroup (MulAut (PairN n)))
    (hT : IsSylowIn 2 T (Mg n)) (v₁ : PairN n)
    (hfix : fixV (T ⊓ stabSub (V1n n)) ⊓ V1n n = Subgroup.zpowers v₁) : H91Clause3 n T v₁ := by
  obtain ⟨m, rfl, hm⟩ : ∃ m, n = m + 1 ∧ 3 ≤ m := by
    rcases hn with rfl | rfl
    · exact ⟨3, rfl, le_rfl⟩
    · exact ⟨4, rfl, by norm_num⟩
  obtain ⟨l, hl, rfl, rfl⟩ := exists_normalize_pair m hT hfix
  exact (H91Clause3_conj (m + 1) hl _ _).1 (clause3_normal m hm)

theorem h91_clause4 (n : ℕ) (hn : n = 4 ∨ n = 5) (T : Subgroup (MulAut (PairN n)))
    (hT : IsSylowIn 2 T (Mg n)) (v₁ : PairN n)
    (hfix : fixV (T ⊓ stabSub (V1n n)) ⊓ V1n n = Subgroup.zpowers v₁) (v₂ : PairN n)
    (hv₂ : v₂ ∈ V2n n)
    (hv₂' : v₂ ∉ commOn (V2n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁)))) :
    H91Clause4 n T v₁ v₂ := by
  obtain ⟨m, rfl, hm⟩ : ∃ m, n = m + 1 ∧ 3 ≤ m := by
    rcases hn with rfl | rfl
    · exact ⟨3, rfl, le_rfl⟩
    · exact ⟨4, rfl, by norm_num⟩
  obtain ⟨l, hl, rfl, rfl⟩ := exists_normalize_pair m hT hfix
  have hcomm := commOn_twoResidual_centSub_map (conjAut_eq_self_of_mem hl)
    (map_V2n_of_mem_Lg hl) (pairVec (ez m) 0)
  have hmem2 : l⁻¹ v₂ ∈ V2n (m + 1) :=
    (mem_stabSub.mp (Lg_le_stabSub_V2n ((Lg (m + 1)).inv_mem hl)) v₂).mpr hv₂
  have hnot : l⁻¹ v₂ ∉ commOn (V2n (m + 1))
      (twoResidual (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)))) := by
    intro hmem
    apply hv₂'
    have h5 : v₂ ∈ (commOn (V2n (m + 1))
        (twoResidual (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0))))).map
          (l : MulAut (PairN (m + 1))).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨l⁻¹ v₂, hmem, MulEquiv.apply_symm_apply l v₂⟩
    exact (SetLike.ext_iff.mp hcomm v₂).mpr h5
  obtain ⟨a, b, hab⟩ := pairVec_surj (l⁻¹ v₂)
  have ha : a = 0 := by
    have h := mem_V2n.mp hmem2
    rw [hab] at h
    simpa [pairVec] using h
  subst ha
  have hb : b 0 = 1 := by
    by_contra hb1
    have hb0 : b 0 = 0 := by
      have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      exact (h01 (b 0)).resolve_right hb1
    apply hnot
    obtain ⟨_, _, _, h4, _⟩ := clause3_normal m hm
    rw [h4]
    refine Subgroup.mem_inf.mpr ⟨hmem2, ?_⟩
    rw [mem_perpN_zpowers_iff, hab, polarN_pairVec_ez, hb0]
  obtain ⟨u, hu, hue, huv⟩ := exists_T0_inf_Lg_apply_V2 m (b := ez m) (b' := b) (by simp [ez]) hb
  have h4 : H91Clause4 (m + 1) (T0 (m + 1)) (pairVec (ez m) 0) (pairVec 0 b) := by
    have h5 := (H91Clause4_conj (m + 1) hu.2 (T0 (m + 1)) (pairVec (ez m) 0)
      (pairVec 0 (ez m))).1 (clause4_normal m hm)
    exact H91Clause4_congr (conjAut_eq_self_of_mem hu.1) hue huv h5
  have h6 := (H91Clause4_conj (m + 1) hl (T0 (m + 1)) (pairVec (ez m) 0) (pairVec 0 b)).1 h4
  have hv : l (pairVec 0 b) = v₂ := by
    rw [← hab]
    exact MulEquiv.apply_symm_apply l v₂
  exact H91Clause4_congr rfl rfl hv h6

end CFSG.ASVolI.ChH
