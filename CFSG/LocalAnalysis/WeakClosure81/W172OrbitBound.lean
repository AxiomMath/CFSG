module

public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitCount
public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitInv
public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitSurj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

theorem w172_relIndex_le_relIndex_map {K Γ : Type*} [Group K] [Group Γ] [Finite K]
    (f : K →* Γ) {S C : Subgroup K} {Y : Subgroup Γ} (h : ∀ s ∈ S, f s ∈ Y → s ∈ C) :
    C.relIndex S ≤ Y.relIndex (S.map f) := by
  rw [← Subgroup.relIndex_comap Y f S]
  have hle : Y.comap f ⊓ S ≤ C ⊓ S := fun s hs => ⟨h s hs.2 hs.1, hs.2⟩
  calc C.relIndex S = (C ⊓ S).relIndex S := (Subgroup.inf_relIndex_right C S).symm
    _ ≤ (Y.comap f ⊓ S).relIndex S :=
        Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
    _ = (Y.comap f).relIndex S := Subgroup.inf_relIndex_right _ _

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_two_pow_le_relIndex_normalizer (h162 : W3Thm162Gt2 G) (hL : W172Lem26 D V₀ V)
    (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W}
    (hge : M.img V = Subgroup.zpowers e) (he : e * e = 1) (he1 : e ≠ 1) {y : LGL 2 M.W}
    (hy : y ∈ M.img H) (hodd : Odd (orderOf y)) (hinv : e * y * e⁻¹ = y⁻¹) (hy1 : y ≠ 1) :
    2 ^ (rk ↥V₀ * (mBar D.M V₀ V c.hyp.setting.isElemAbelian - 1)) ≤
      (Subgroup.normalizer (Subgroup.zpowers y : Set (LGL 2 M.W))).relIndex
        (M.img (w172R D V₀ V)) := by
  classical
  obtain ⟨x, -, rfl⟩ := M.mem_img.1 hy
  have hx64 := c.w172_hyp64_of_inverted h162 hL M hge he he1 hodd hinv hy1
  have hV : IsElemAbelian 2 V := c.hyp.setting.isElemAbelian
  have hNV : NOf D.M V (x : G) ≤ V := inf_le_left.trans inf_le_left
  have hNbot : NOf D.M V (x : G) ⊓ V₀ = ⊥ := NOf_inf_eq_bot hx64
  have hV₀V : V₀ ≤ V := hx64.le
  have hV₀ab : IsElemAbelian 2 V₀ := hV.mono hV₀V
  have hNab : IsElemAbelian 2 (NOf D.M V (x : G)) := hV.mono hNV
  have hrank := hx64.w172_mBar_sub_one_le_rk_nOf
  have hMle : D.M ≤ Subgroup.normalizer (V : Set G) := c.hyp.setting.normalizer_eq.symm.le
  have hcomm : ∀ t ∈ w172R D V₀ V, ∀ n ∈ NOf D.M V (x : G), ⁅n, t⁆ ∈ V₀ := by
    intro t ht n hn
    obtain ⟨-, hs, hact⟩ :=
      (mem_cTilde_iff hV hMle).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 ht).1).2
    have h1 : t * (n : G) * t⁻¹ * (n : G)⁻¹ ∈ V₀ :=
      (actTil_eq_one_iff V₀ V hV ⟨t, hs⟩).1 hact (n : G) (hNV hn)
    rw [← commutatorElement_inv t (n : G)]
    exact V₀.inv_mem h1
  have hcent : ∀ t ∈ w172R D V₀ V, ∀ v ∈ V₀, t * v = v * t := fun t ht v hv =>
    ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ht).2) v hv).symm
  have hNV₀ : ∀ n ∈ NOf D.M V (x : G), ∀ v ∈ V₀, n * v = v * n := fun n hn v hv =>
    hV.comm (hNV hn) (hV₀V hv)
  have hsurj : ∀ f : ↥(NOf D.M V (x : G)) →* ↥V₀,
      ∃ t ∈ w172R D V₀ V, ∀ n : ↥(NOf D.M V (x : G)), ⁅(n : G), t⁆ = (f n : G) := fun f =>
    w172_exists_comm_eq_R c.hyp.setting c.hyp.ne_bot hx64 hNV hNbot f
  have h1 := w172_two_pow_le_relIndex_centralizer hV₀ab hNab hNV₀ hcomm hcent hsurj
  have h2 : 2 ^ (rk ↥V₀ * (mBar D.M V₀ V c.hyp.setting.isElemAbelian - 1)) ≤
      2 ^ (rk ↥V₀ * rk ↥(NOf D.M V (x : G))) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hrank)
  have hRH : w172R D V₀ V ≤ H := (w172R_le_T D V₀ V).trans c.hyp.hyp171.2.1
  have h3 := w172_relIndex_le_relIndex_map M.ρ
    (S := (w172R D V₀ V).subgroupOf H)
    (C := (Subgroup.centralizer (NOf D.M V (x : G) : Set G)).subgroupOf H)
    (Y := Subgroup.normalizer (Subgroup.zpowers (M.ρ x) : Set (LGL 2 M.W)))
    (fun s hs hsY => c.w172_comm_of_normalizes h162 hL M hge he he1 hodd hinv hy1 hs hsY)
  rw [Subgroup.relIndex_subgroupOf hRH] at h3
  exact h2.trans (h1.trans h3)

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
