module

public import CFSG.Timmesfeld.Bridge.Asc72WreathDefs
import CFSG.GroupTheory.SwapCommute
import CFSG.Timmesfeld.Bridge.Asc72WreathL2
import CFSG.Timmesfeld.Bridge.Asc72WreathStruct
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Bridge.Asc72Lift
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Bridge.Asc72

theorem commute_pow_three_of_conj {G : Type*} [Group G] {c s a b : G}
    (h1 : c * s * c⁻¹ = a) (h2 : c * a * c⁻¹ = b) (h3 : c * b * c⁻¹ = s) :
    Commute (c ^ 3) s := by
  have h3eq : c ^ 3 = c * (c * c) := by
    rw [pow_succ, pow_succ, pow_one]
    group
  have h3inv : (c ^ 3)⁻¹ = c⁻¹ * (c⁻¹ * c⁻¹) := by
    rw [h3eq, mul_inv_rev, mul_inv_rev]
    group
  have hconj : c ^ 3 * s * (c ^ 3)⁻¹ = s := by
    rw [h3inv, h3eq]
    calc c * (c * c) * s * (c⁻¹ * (c⁻¹ * c⁻¹))
        = c * (c * (c * s * c⁻¹) * c⁻¹) * c⁻¹ := by group
      _ = c * (c * a * c⁻¹) * c⁻¹ := by rw [h1]
      _ = c * b * c⁻¹ := by rw [h2]
      _ = s := h3
  rw [Commute]
  calc c ^ 3 * s = (c ^ 3 * s * (c ^ 3)⁻¹) * c ^ 3 := by
        rw [h3inv, h3eq]
        group
    _ = s * c ^ 3 := by rw [hconj]

section Wreath

variable {X : Type} [Group X] {D : Set X} {M : Subgroup X}

theorem commute_of_mem_swap (W : WreathData X D M) {u : X} (hu : u ∈ D) {i j : Fin W.r}
    (hπ : W.π u = Equiv.swap i j) {k : Fin W.r} (hki : k ≠ i) (hkj : k ≠ j) {s : X}
    (hs : s ∈ W.S k) : Commute u s := by
  obtain ⟨a, b, hab, hπab, hcent⟩ := W.swap u hu
  have hswap : Equiv.swap a b = Equiv.swap i j := hπab.symm.trans hπ
  have hka : k ≠ a := by
    intro hka
    have h1 : b = k := by
      calc b = Equiv.swap a b a := (Equiv.swap_apply_left a b).symm
        _ = Equiv.swap a b k := by rw [hka]
        _ = Equiv.swap i j k := by rw [hswap]
        _ = k := Equiv.swap_apply_of_ne_of_ne hki hkj
    exact hab (h1.trans hka).symm
  have hkb : k ≠ b := by
    intro hkb
    have h1 : a = k := by
      calc a = Equiv.swap a b b := (Equiv.swap_apply_right a b).symm
        _ = Equiv.swap a b k := by rw [hkb]
        _ = Equiv.swap i j k := by rw [hswap]
        _ = k := Equiv.swap_apply_of_ne_of_ne hki hkj
    exact hab (h1.trans hkb)
  exact hcent k hka hkb s hs

theorem commute_pow_three_of_mem_factor_i (W : WreathData X D M) {x y : X} {i j k : Fin W.r}
    (hx : x ∈ D) (hy : y ∈ D) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hπx : W.π x = Equiv.swap i j)
    (hπy : W.π y = Equiv.swap j k) {s : X} (hs : s ∈ W.S i) :
    Commute ((x * y) ^ 3) s := by
  set c : X := x * y with hc
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hxk : ∀ t ∈ W.S k, Commute x t :=
    fun t ht => commute_of_mem_swap W hx hπx hik.symm hjk.symm ht
  have hyi : ∀ t ∈ W.S i, Commute y t :=
    fun t ht => commute_of_mem_swap W hy hπy hij hik ht
  set r : X := x * s * x⁻¹ with hr
  have hrj : r ∈ W.S j := by
    have h := W.conj_mem x hs
    rwa [hπx, Equiv.swap_apply_left] at h
  have hyr : y * r * y⁻¹ ∈ W.S k := by
    have h := W.conj_mem y hrj
    rwa [hπy, Equiv.swap_apply_left] at h
  have h1 : c * s * c⁻¹ = r := by
    have hyfix : y * s * y⁻¹ = s := Commute.mul_inv_cancel (hyi s hs)
    calc c * s * c⁻¹ = x * (y * s * y⁻¹) * x⁻¹ := by
          rw [hc, mul_inv_rev]
          group
      _ = r := by rw [hyfix, hr]
  have h2 : c * r * c⁻¹ = y * r * y⁻¹ := by
    have hxfix : x * (y * r * y⁻¹) * x⁻¹ = y * r * y⁻¹ :=
      Commute.mul_inv_cancel (hxk _ hyr)
    calc c * r * c⁻¹ = x * (y * r * y⁻¹) * x⁻¹ := by
          rw [hc, mul_inv_rev]
          group
      _ = y * r * y⁻¹ := hxfix
  have h3 : c * (y * r * y⁻¹) * c⁻¹ = s := by
    rw [hc, hr, mul_inv_rev, hyinv, hxinv]
    calc (x * y) * (y * (x * s * x) * y) * (y * x)
        = x * (y * y) * (x * s * x) * (y * y) * x := by group
      _ = x * (x * s * x) * x := by rw [hy2]; group
      _ = (x * x) * s * (x * x) := by group
      _ = s := by rw [hx2]; group
  exact commute_pow_three_of_conj h1 h2 h3

theorem commute_pow_three_of_mem_factor_j (W : WreathData X D M) {x y : X} {i j k : Fin W.r}
    (hx : x ∈ D) (hy : y ∈ D) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hπx : W.π x = Equiv.swap i j)
    (hπy : W.π y = Equiv.swap j k) {t : X} (ht : t ∈ W.S j) :
    Commute ((x * y) ^ 3) t := by
  set c : X := x * y with hc
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : ∀ s ∈ W.S i, Commute y s :=
    fun s hs => commute_of_mem_swap W hy hπy hij hik hs
  have hs : x * t * x⁻¹ ∈ W.S i := by
    have h := W.conj_mem x ht
    rwa [hπx, Equiv.swap_apply_right] at h
  have hcomm : Commute (c ^ 3) (x * t * x⁻¹) := by
    simpa [hc] using
      commute_pow_three_of_mem_factor_i W hx hy hx2 hy2 hij hjk hik hπx hπy hs
  have hconj : c * (x * t * x⁻¹) * c⁻¹ = t := by
    have hyfix : y * (x * t * x⁻¹) * y⁻¹ = x * t * x⁻¹ :=
      Commute.mul_inv_cancel (hyi _ hs)
    calc c * (x * t * x⁻¹) * c⁻¹ = x * (y * (x * t * x⁻¹) * y⁻¹) * x⁻¹ := by
          rw [hc, mul_inv_rev]
          group
      _ = x * (x * t * x⁻¹) * x⁻¹ := by rw [hyfix]
      _ = t := by
          rw [hxinv]
          calc x * (x * t * x) * x = (x * x) * t * (x * x) := by group
            _ = t := by rw [hx2]; group
  have hcc3 : Commute c (c ^ 3) := (Commute.refl c).pow_right 3
  have hc3 : c * c ^ 3 * c⁻¹ = c ^ 3 := hcc3.mul_inv_cancel
  have hfinal := hcomm.conj c
  rwa [hc3, hconj] at hfinal

theorem commute_pow_three_of_mem_factor_k (W : WreathData X D M) {x y : X} {i j k : Fin W.r}
    (hx : x ∈ D) (hy : y ∈ D) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hπx : W.π x = Equiv.swap i j)
    (hπy : W.π y = Equiv.swap j k) {t : X} (ht : t ∈ W.S k) :
    Commute ((x * y) ^ 3) t := by
  set c : X := x * y with hc
  have hπc : W.π c = Equiv.swap i j * Equiv.swap j k := by
    rw [hc, map_mul, hπx, hπy]
  have hck : W.π c k = i := by
    rw [hπc, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
  have hs : c * t * c⁻¹ ∈ W.S i := by
    have h := W.conj_mem c ht
    rwa [hck] at h
  have hcomm : Commute (c ^ 3) (c * t * c⁻¹) := by
    simpa [hc] using
      commute_pow_three_of_mem_factor_i W hx hy hx2 hy2 hij hjk hik hπx hπy hs
  have hcc3 : Commute c⁻¹ (c ^ 3) := ((Commute.refl c).pow_right 3).inv_left
  have hc3 : c⁻¹ * c ^ 3 * c = c ^ 3 := by
    simpa using hcc3.mul_inv_cancel
  have hconj : c⁻¹ * (c * t * c⁻¹) * c = t := by group
  have hfinal := hcomm.conj c⁻¹
  rw [inv_inv] at hfinal
  rwa [hc3, hconj] at hfinal

theorem commute_pow_three_of_mem_factor_other (W : WreathData X D M) {x y : X}
    {i j k l : Fin W.r} (hx : x ∈ D) (hy : y ∈ D) (hπx : W.π x = Equiv.swap i j)
    (hπy : W.π y = Equiv.swap j k) (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) {s : X}
    (hs : s ∈ W.S l) : Commute ((x * y) ^ 3) s := by
  have hxl : Commute x s := commute_of_mem_swap W hx hπx hli hlj hs
  have hyl : Commute y s := commute_of_mem_swap W hy hπy hlj hlk hs
  exact (hxl.mul_left hyl).pow_left 3

theorem commute_pow_three_of_mem_factor (W : WreathData X D M) {x y : X} {i j k : Fin W.r}
    (hx : x ∈ D) (hy : y ∈ D) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hπx : W.π x = Equiv.swap i j)
    (hπy : W.π y = Equiv.swap j k) (l : Fin W.r) {s : X} (hs : s ∈ W.S l) :
    Commute ((x * y) ^ 3) s := by
  by_cases hli : l = i
  · subst hli
    exact commute_pow_three_of_mem_factor_i W hx hy hx2 hy2 hij hjk hik hπx hπy hs
  by_cases hlj : l = j
  · subst hlj
    exact commute_pow_three_of_mem_factor_j W hx hy hx2 hy2 hij hjk hik hπx hπy hs
  by_cases hlk : l = k
  · subst hlk
    exact commute_pow_three_of_mem_factor_k W hx hy hx2 hy2 hij hjk hik hπx hπy hs
  · exact commute_pow_three_of_mem_factor_other W hx hy hπx hπy hli hlj hlk hs

theorem orderOf_mul_eq_three_of_wreathData (W : WreathData X D M)
    (hC : Subgroup.centralizer (M : Set X) = ⊥) {x y : X}
    (hx : x ∈ D) (hy : y ∈ D) (hx2 : x * x = 1) (hy2 : y * y = 1) {i j k : Fin W.r}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hπx : W.π x = Equiv.swap i j)
    (hπy : W.π y = Equiv.swap j k) : orderOf (x * y) = 3 := by
  set c : X := x * y with hc
  have hcent : ∀ (l : Fin W.r) (s : X), s ∈ W.S l → Commute (c ^ 3) s := by
    intro l s hs
    simpa [hc] using
      commute_pow_three_of_mem_factor W hx hy hx2 hy2 hij hjk hik hπx hπy l hs
  have hH : ∀ l, W.S l ≤ Subgroup.centralizer ({c ^ 3} : Set X) := by
    intro l s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcent l s hs).eq.symm
  have hMle : M ≤ Subgroup.centralizer ({c ^ 3} : Set X) :=
    WreathStruct.le_of_forall_factor_le (e := W.e) W.e_single hH
  have hmem : c ^ 3 ∈ Subgroup.centralizer (M : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hMle hm)
  have hc3 : c ^ 3 = 1 := by
    simpa [hC] using hmem
  have hπc : W.π c = Equiv.swap i j * Equiv.swap j k := by
    rw [hc, map_mul, hπx, hπy]
  have hne : c ≠ 1 := by
    intro h1
    have h2 : (Equiv.swap i j * Equiv.swap j k) i = i := by
      rw [← hπc, h1, map_one]
      rfl
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik,
      Equiv.swap_apply_left] at h2
    exact hij h2.symm
  exact orderOf_eq_prime hc3 hne

theorem false_of_commute_of_closure_eq_top (W : WreathData X D M) (hr : 2 < W.r)
    {u w v : X} {i j : Fin W.r} (hij : i ≠ j) (hπu : W.π u = Equiv.swap i j)
    (hv : v ∈ D) (huv : Commute u v) (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤)
    (hcomm : Commute (W.π u) (W.π w)) : False := by
  let H : Subgroup X :=
    (Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin W.r)))).comap W.π
  have hcomm' : Commute (Equiv.swap i j) (W.π w) := by
    rwa [hπu] at hcomm
  obtain ⟨_, _, _, hπv, -⟩ := W.swap v hv
  have hcommv : Commute (Equiv.swap i j) (W.π v) := by
    have h := huv.map W.π
    rw [hπu] at h
    simpa [hπv] using h
  have huH : u ∈ H := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    simp [hπu]
  have hwH : w ∈ H := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm'.symm
  have hvH : v ∈ H := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact hcommv.symm
  have htop : H = ⊤ := by
    have hle : Subgroup.closure ({u, w, v} : Set X) ≤ H := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact huH
      · exact hwH
      · exact hvH
    exact top_le_iff.mp (by rwa [hgen] at hle)
  have hex : ∃ k : Fin W.r, k ≠ i ∧ k ≠ j := by
    have hlt : ({i, j} : Finset (Fin W.r)).card < (Finset.univ : Finset (Fin W.r)).card := by
      rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩
  obtain ⟨k, hki, hkj⟩ := hex
  obtain ⟨g, hg⟩ := W.transitive i k
  have hgH : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
  have hgcomm : Commute (W.π g) (Equiv.swap i j) := by
    have h := Subgroup.mem_comap.1 hgH
    rwa [Subgroup.mem_centralizer_singleton_iff] at h
  have hk := CFSG.GroupTheory.apply_mem_pair_of_commute hij hgcomm
  rw [hg] at hk
  rcases hk with h | h
  · exact hki h
  · exact hkj h

theorem exists_swap_swap_of_closure_eq_top (W : WreathData X D M) (hr : 2 < W.r) {u w v : X}
    (hu : u ∈ D) (hw : w ∈ D) (hv : v ∈ D) (huv : Commute u v)
    (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) :
    ∃ i j k : Fin W.r, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ W.π u = Equiv.swap i j ∧
      W.π w = Equiv.swap j k := by
  obtain ⟨i, j, hij, hπu, -⟩ := W.swap u hu
  obtain ⟨a, b, hab, hπw, -⟩ := W.swap w hw
  by_cases hcomm : Commute (W.π u) (W.π w)
  · exact (false_of_commute_of_closure_eq_top W hr hij hπu hv huv hgen hcomm).elim
  · obtain ⟨i', j', k', hij', hjk', hik', hπu', hπw'⟩ :=
      CFSG.GroupTheory.exists_swap_swap_of_not_commute hij hab (by rwa [hπu, hπw] at hcomm)
    exact ⟨i', j', k', hij', hjk', hik', hπu.trans hπu', hπw.trans hπw'⟩

end Wreath

end CFSG.OddTranspositions.PartThree.EightSix
