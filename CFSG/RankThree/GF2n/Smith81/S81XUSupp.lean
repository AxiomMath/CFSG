module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Frame
public import CFSG.RankThree.GF2n.Smith81.S81NBasis
public import CFSG.RankThree.GF2n.Smith81.S81WGeomGen

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K] [CharP K 2]

theorem a5supp_S024_val : S024.val = ({0, 2, 4} : Finset (Fin 6)) := rfl

theorem a5supp_card_fin : ∀ (J : Finset (Fin 6)), J.card = 3 → ∀ (a : Fin 6), a ∈ J →
    a.val % 2 = 0 → ∀ (b : Fin 6), b ∉ J → b.val % 2 = 1 → J ≠ ({0, 2, 4} : Finset (Fin 6)) →
    2 ≤ ((insert b (J.erase a)).filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
  decide

theorem a5supp_card_set {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val % 2 = 1)
    (J : Set.powersetCard (Fin 6) 3) (haJ : a ∈ J.val) (hbJ : b ∉ J.val) (hJ : J ≠ S024) :
    2 ≤ ((replSet J b a haJ hbJ).val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
  have hJ' : J.val ≠ ({0, 2, 4} : Finset (Fin 6)) :=
    fun h => hJ (Subtype.ext (h.trans a5supp_S024_val.symm))
  exact a5supp_card_fin J.val J.prop a haJ ha b hbJ hb hJ'

theorem a5supp_coord_rho_sub {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val % 2 = 1)
    (hne : a ≠ b) (c : K) {ξ : Cube K}
    (h : ∀ I : Set.powersetCard (Fin 6) 3,
      2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card → coord K ξ I = 0)
    (J : Set.powersetCard (Fin 6) 3) (hJ : J ≠ S024) :
    coord K (rho K (transvGL K a b hne c) ξ - ξ) J = 0 := by
  rw [coord_sub, coord_rho_transvGL_gen a b hne c ξ J]
  by_cases hJc : a ∈ J.val ∧ b ∉ J.val
  · have h0 : coord K ξ (replSet J b a hJc.1 hJc.2) = 0 :=
      h (replSet J b a hJc.1 hJc.2) (a5supp_card_set ha hb J hJc.1 hJc.2 hJ)
    rw [dif_pos hJc, h0]
    ring
  · rw [dif_neg hJc]
    ring

theorem a5supp_eq_smul_p0 {y : Cube K}
    (hy : ∀ J : Set.powersetCard (Fin 6) 3, J ≠ S024 → coord K y J = 0) :
    y = coord K y S024 • p0 K := by
  rw [← sub_eq_zero]
  apply eq_zero_of_coord_eq_zero
  intro J
  rw [coord_sub, coord_smul]
  by_cases hJ : J = S024
  · subst hJ
    rw [p0, coord_cubeBasis, if_pos rfl]
    ring
  · rw [hy J hJ, p0, coord_cubeBasis, if_neg (Ne.symm hJ)]
    ring

theorem a5supp_mem_span {y : Cube K}
    (hy : ∀ J : Set.powersetCard (Fin 6) 3, J ≠ S024 → coord K y J = 0) :
    y ∈ Submodule.span K {p0 K} := by
  rw [a5supp_eq_smul_p0 hy]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem a5supp_rho_sub_mem {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val % 2 = 1)
    (hne : a ≠ b) (c : K) {ξ : Cube K}
    (h : ∀ I : Set.powersetCard (Fin 6) 3,
      2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card → coord K ξ I = 0) :
    rho K (transvGL K a b hne c) ξ - ξ ∈ Submodule.span K {p0 K} :=
  a5supp_mem_span fun J hJ => a5supp_coord_rho_sub ha hb hne c h J hJ

theorem a5_mem_W0_of_support {ξ : Cube K}
    (h : ∀ I : Set.powersetCard (Fin 6) 3,
      2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card → coord K ξ I = 0) :
    ξ ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  have hfix : ∀ s ∈ rootSet K, s (p0 K) = p0 K :=
    fun s hs => U0_fix (K := K) s (Subgroup.subset_closure hs)
  have hv : ∀ s ∈ rootSet K, s ξ - ξ ∈ Submodule.span K {p0 K} := by
    rintro s ⟨a, b, hab, c, rfl⟩
    rw [rhoEquiv_apply]
    exact a5supp_rho_sub_mem hab.1 hab.2 (rootSet_ne hab) c h
  exact (mem_Wsp_closure_iff hfix).mpr hv

end CFSG.RankThree.GF2n.Smith81.A5Cube
