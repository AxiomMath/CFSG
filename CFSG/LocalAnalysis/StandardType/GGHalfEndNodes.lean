module

public import CFSG.LocalAnalysis.StandardType.GGHalfEndCentral
public import CFSG.LocalAnalysis.StandardType.GGHalfAlpha
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnGen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

private theorem map_conj_map' {N : ℕ} {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin N) F2 →* G) (s : SpecialLinearGroup (Fin N) F2)
    (H : Subgroup (SpecialLinearGroup (Fin N) F2)) :
    (H.map (MulAut.conj s).toMonoidHom).map φ =
      (H.map φ).map (MulAut.conj (φ s)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]

include h

private theorem endT_involutions :
    endT₁ φ₂ * endT₁ φ₂ = 1 ∧ endT₂ φ₂ * endT₂ φ₂ = 1 := by
  constructor
  · rw [endT₁, ← map_mul,
      weylRep_mul_self (F := F2) (m := m + 1 + 1) gf2_two (⟨m, by omega⟩), map_one]
  · rw [endT₂, ← map_mul,
      weylRep_mul_self (F := F2) (m := m + 1 + 1) gf2_two (⟨m + 1, by omega⟩), map_one]

private theorem endT₁_mul_endT₂_cube : (endT₁ φ₂ * endT₂ φ₂) ^ 3 = 1 := by
  rw [endT₁, endT₂, ← map_mul, ← map_pow,
    weylRep_cube (m + 1 + 1) (⟨m, by omega⟩) (⟨m + 1, by omega⟩) (by simp), map_one]

private theorem endT₁_cube_weylRep_last :
    (endT₁ φ₂ * φ₁ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩)) ^ 3 = 1 := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hlow : slLower2Hom m (weylRep m F2 ⟨m - 1, by omega⟩) =
      weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ := by
    rw [slLower2Hom_weylRep]
    congr 1
    exact Fin.ext (by simp only [Fin.val_succ, Fin.val_mk]; omega)
  have hup : slUpper2Hom m (weylRep m F2 ⟨m - 1, by omega⟩) =
      weylRep (m + 1 + 1) F2 ⟨m - 1, by omega⟩ := by
    rw [slUpper2Hom_weylRep]
  have hagree := DFunLike.congr_fun h.coords.agree (weylRep m F2 ⟨m - 1, by omega⟩)
  have hphi : φ₁ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩) =
      φ₂ (weylRep (m + 1 + 1) F2 ⟨m - 1, by omega⟩) := by
    rw [← hlow, ← hup]
    simpa only [MonoidHom.comp_apply] using hagree
  rw [hphi, endT₁, ← map_mul, ← map_pow]
  have hcube : (weylRep (m + 1 + 1) F2 ⟨m - 1, by omega⟩ *
      weylRep (m + 1 + 1) F2 ⟨m, by omega⟩) ^ 3 = 1 :=
    weylRep_cube (m + 1 + 1) (⟨m - 1, by omega⟩) (⟨m, by omega⟩)
      (by simp only [Fin.val_mk]; omega)
  have hc := typeASpecial₂_cube_of_cube_swap (a := weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)
    (b := weylRep (m + 1 + 1) F2 ⟨m - 1, by omega⟩) hcube
  rw [hc, map_one]

private theorem endT₂_centralize_φ₁ : ∀ g, endT₂ φ₂ * φ₁ g = φ₁ g * endT₂ φ₂ := by
  intro g
  exact h.endT₂_central (φ₁ g) (by
    rw [← h.coords.range₁]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩)

private theorem K_le_sup_conj :
    K ≤ L ⊔ L.map (MulAut.conj (endT₁ φ₂)).toMonoidHom ⊔
      L.map (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hsup := top_eq_sup_conj m hm
  have hs₁ : φ₂ (weylRep (m + 1 + 1) F2 ⟨m, by omega⟩) = endT₁ φ₂ := rfl
  have hs₂ : φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩) = endT₂ φ₂ := rfl
  have hs : φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
      weylRep (m + 1 + 1) F2 ⟨m, by omega⟩) = endT₂ φ₂ * endT₁ φ₂ := by
    rw [map_mul, hs₁, hs₂]
  have hJL : J ≤ L := by
    calc J = (φ₁.comp (slLower2Hom m)).range := h.coords.rangeJ.symm
      _ = (slLower2Hom m).range.map φ₁ := MonoidHom.range_comp φ₁ (slLower2Hom m)
      _ ≤ (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)).map φ₁ :=
            Subgroup.map_mono le_top
      _ = φ₁.range := (MonoidHom.range_eq_map φ₁).symm
      _ = L := h.coords.range₁
  have hJ : (slUpper2Hom m).range.map φ₂ = J := by
    rw [← MonoidHom.range_comp, ← h.coords.agree, h.coords.rangeJ]
  calc K = φ₂.range := h.coords.range₂.symm
    _ = (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)).map φ₂ := by
          rw [MonoidHom.range_eq_map]
    _ = ((slUpper2Hom m).range ⊔
          ((slUpper2Hom m).range.map (MulAut.conj
            (weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)).toMonoidHom) ⊔
          ((slUpper2Hom m).range.map (MulAut.conj
            (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
              weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)).toMonoidHom)).map φ₂ := by
          rw [hsup]
    _ = ((slUpper2Hom m).range.map φ₂) ⊔
          (((slUpper2Hom m).range.map φ₂).map (MulAut.conj
            (φ₂ (weylRep (m + 1 + 1) F2 ⟨m, by omega⟩))).toMonoidHom) ⊔
          (((slUpper2Hom m).range.map φ₂).map (MulAut.conj
            (φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
              weylRep (m + 1 + 1) F2 ⟨m, by omega⟩))).toMonoidHom) := by
          rw [Subgroup.map_sup, Subgroup.map_sup, map_conj_map', map_conj_map']
    _ = ((slUpper2Hom m).range.map φ₂) ⊔
          (((slUpper2Hom m).range.map φ₂).map (MulAut.conj (endT₁ φ₂)).toMonoidHom) ⊔
          (((slUpper2Hom m).range.map φ₂).map
            (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom) := by
          rw [hs₁, hs]
    _ = J ⊔ J.map (MulAut.conj (endT₁ φ₂)).toMonoidHom ⊔
          J.map (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom := by
          rw [hJ]
    _ ≤ L ⊔ L.map (MulAut.conj (endT₁ φ₂)).toMonoidHom ⊔
          L.map (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom :=
          sup_le_sup (sup_le_sup hJL (Subgroup.map_mono hJL)) (Subgroup.map_mono hJL)

private theorem endT₁_centralize_slOn_lt (hK1 : GGHalfNormSL014 φ₁ φ₂) :
    ∀ y ∈ slOn (m + 1 + 1 + 1) {i | i.val < m + 2},
      endT₁ φ₂ * φ₁ y = φ₁ y * endT₁ φ₂ := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hD : slOn (m + 1 + 1 + 1) {i | i.val < m + 2} ≤
      (Subgroup.centralizer ({endT₁ φ₂} : Set G)).comap φ₁ := by
    rw [slOn_lt_eq_sup m hm]
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      have hset : {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val < m + 2} =
          (fun j : Fin (m + 1) => j.succ.succ) '' {j : Fin (m + 1) | j.val < m} := by
        ext i; constructor
        · rintro ⟨h2, hlt⟩
          exact ⟨⟨i.val - 2, by omega⟩, by simp only [Set.mem_setOf_eq]; omega,
            Fin.ext (by simp only [Fin.val_succ, Fin.val_mk]; omega)⟩
        · rintro ⟨j, hj, rfl⟩
          simp only [Set.mem_setOf_eq, Fin.val_succ] at hj ⊢
          omega
      rw [hset, ← slLower2Hom_map_slOn m (S := {j : Fin (m + 1) | j.val < m})] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      have hagree : φ₁ (slLower2Hom m y') = φ₂ (slUpper2Hom m y') := by
        have := DFunLike.congr_fun h.coords.agree y'
        simpa only [MonoidHom.comp_apply] using this
      have hset2 : {i : Fin (m + 1 + 1 + 1) | i.val < m} =
          (fun j : Fin (m + 1) => j.castSucc.castSucc) '' {j : Fin (m + 1) | j.val < m} := by
        ext i; constructor
        · intro hi
          simp only [Set.mem_setOf_eq] at hi
          exact ⟨⟨i.val, by omega⟩, hi,
            Fin.ext (by simp only [Fin.val_castSucc, Fin.val_mk])⟩
        · rintro ⟨j, hj, rfl⟩
          simp only [Set.mem_setOf_eq, Fin.val_castSucc] at hj ⊢
          omega
      have hmem : slUpper2Hom m y' ∈ slOn (m + 1 + 1 + 1) {i | i.val < m} := by
        rw [hset2, ← slUpper2Hom_map_slOn m (S := {j : Fin (m + 1) | j.val < m})]
        exact ⟨y', hy', rfl⟩
      have hfix : ∀ i ∈ ({i : Fin (m + 1 + 1 + 1) | i.val < m} : Set (Fin (m + 1 + 1 + 1))),
          (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨m + 1, by omega⟩) i = i := by
        intro i hi
        simp only [Set.mem_setOf_eq] at hi
        exact Equiv.swap_apply_of_ne_of_ne
          (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
          (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
      have hcomm := commute_slPerm_slOn (N := m + 1 + 1 + 1)
        (π := Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨m + 1, by omega⟩)
        (S := {i | i.val < m}) hfix hmem
      rw [hagree, endT₁, weylRep_eq_slPerm]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [← map_mul, ← map_mul, ← hcomm]
    · intro y hy
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      have hτm_apply : tauPerm m (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) = ⟨m, by omega⟩ := by
        rw [tauPerm, Equiv.Perm.mul_apply]
        rw [show (Equiv.swap (Fin.last (m + 1 + 1)) 1) (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) =
            ⟨m, by omega⟩ from Equiv.swap_apply_of_ne_of_ne
              (by intro h; have := congrArg Fin.val h
                  simp only [Fin.val_mk, Fin.val_last] at this; omega)
              (by intro h; have := congrArg Fin.val h
                  simp only [Fin.val_mk, Fin.val_one] at this; omega)]
        rw [show (Equiv.swap (Fin.last (m + 1)).castSucc 0) (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) =
            ⟨m, by omega⟩ from Equiv.swap_apply_of_ne_of_ne
              (by intro h; have := congrArg Fin.val h
                  simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc] at this; omega)
              (by intro h; have := congrArg Fin.val h
                  simp only [Fin.val_mk, Fin.val_zero] at this; omega)]
      have hτm1_apply : tauPerm m (⟨0, by omega⟩ : Fin (m + 1 + 1 + 1)) = ⟨m + 1, by omega⟩ := by
        rw [tauPerm, Equiv.Perm.mul_apply]
        rw [show (Equiv.swap (Fin.last (m + 1 + 1)) 1) (⟨0, by omega⟩ : Fin (m + 1 + 1 + 1)) =
            ⟨0, by omega⟩ from Equiv.swap_apply_of_ne_of_ne
              (by intro h; have := congrArg Fin.val h
                  simp only [Fin.val_mk, Fin.val_last] at this; omega)
              (by intro h; have := congrArg Fin.val h
                  simp only [Fin.val_mk, Fin.val_one] at this; omega)]
        change (Equiv.swap (Fin.last (m + 1)).castSucc 0)
            (0 : Fin (m + 1 + 1 + 1)) = ⟨m + 1, by omega⟩
        rw [show (Equiv.swap (Fin.last (m + 1)).castSucc 0) (0 : Fin (m + 1 + 1 + 1)) =
            (Fin.last (m + 1)).castSucc from
              Equiv.swap_apply_right (Fin.last (m + 1)).castSucc (0 : Fin (m + 1 + 1 + 1))]
        exact Fin.ext (by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_mk])
      have hτm : (tauPerm m)⁻¹ (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) = ⟨m, by omega⟩ :=
        (Equiv.symm_apply_eq (tauPerm m)).mpr hτm_apply.symm
      have hτm1 : (tauPerm m)⁻¹ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) = ⟨0, by omega⟩ :=
        (Equiv.symm_apply_eq (tauPerm m)).mpr hτm1_apply.symm
      have hperm : (tauPerm m)⁻¹ *
            Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨m + 1, by omega⟩ * tauPerm m =
          Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨0, by omega⟩ := by
        have h := Equiv.swap_apply_apply (tauPerm m)⁻¹
          (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨m + 1, by omega⟩
        rw [hτm, hτm1, inv_inv] at h
        exact h.symm
      have hconj : (hElt φ₂)⁻¹ * endT₁ φ₂ * hElt φ₂ =
          φ₂ (slPerm gf2_two (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨0, by omega⟩)) := by
        rw [hElt, endT₁, weylRep_eq_slPerm]
        simp only [← map_inv, ← map_mul, Fin.castSucc_mk, Fin.succ_mk]
        rw [hperm]
      set P : G := φ₁ (slPerm gf2_two
        (Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨2, by omega⟩)) with hP
      have hswap : φ₂ (slPerm gf2_two
          (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨0, by omega⟩)) = P := by
        rw [hP]
        have hupper : slUpper2Hom m (slPerm gf2_two
              (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1)) ⟨0, by omega⟩)) =
            slPerm gf2_two (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨0, by omega⟩) := by
          rw [slUpper2Hom, MonoidHom.comp_apply, slUpperBlockHom_slPerm_swap,
            slUpperBlockHom_slPerm_swap]
          simp only [Fin.castSucc_mk]
        have hlower : slLower2Hom m (slPerm gf2_two
              (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1)) ⟨0, by omega⟩)) =
            slPerm gf2_two (Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨2, by omega⟩) := by
          rw [slLower2Hom, MonoidHom.comp_apply, slLowerBlockHom_slPerm_swap,
            slLowerBlockHom_slPerm_swap]
          simp only [Fin.succ_mk]
        have hagree := DFunLike.congr_fun h.coords.agree
          (slPerm gf2_two (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1)) ⟨0, by omega⟩))
        simp only [MonoidHom.comp_apply] at hagree
        rw [hupper, hlower] at hagree
        exact hagree.symm
      have hmem' : φ₁ y ∈ ((slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁).map
          (MulAut.conj (hElt φ₂)).toMonoidHom := by
        rw [hK1]
        exact ⟨y, hy, rfl⟩
      obtain ⟨a, haA, haeq⟩ := hmem'
      obtain ⟨y'', hy'', hy''eq⟩ := haA
      have hconja : hElt φ₂ * a * (hElt φ₂)⁻¹ = φ₁ y := by
        simpa only [← hy''eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using haeq
      have hfix2 : ∀ i ∈ ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1))),
          (Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨2, by omega⟩) i = i := by
        have h0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
        have h1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
        have h2 : (2 : Fin (m + 1 + 1 + 1)).val = 2 := by
          change 2 % (m + 1 + 1 + 1) = 2
          exact Nat.mod_eq_of_lt (by omega)
        have h4 : (4 : Fin (m + 1 + 1 + 1)).val = 4 := by
          change 4 % (m + 1 + 1 + 1) = 4
          exact Nat.mod_eq_of_lt (by omega)
        intro i hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact Equiv.swap_apply_of_ne_of_ne
            (Fin.ne_of_val_ne (by rw [h0, Fin.val_mk]; omega))
            (Fin.ne_of_val_ne (by rw [h0, Fin.val_mk]; omega))
        · exact Equiv.swap_apply_of_ne_of_ne
            (Fin.ne_of_val_ne (by rw [h1, Fin.val_mk]; omega))
            (Fin.ne_of_val_ne (by rw [h1, Fin.val_mk]; omega))
        · exact Equiv.swap_apply_of_ne_of_ne
            (Fin.ne_of_val_ne (by rw [h4, Fin.val_mk]; omega))
            (Fin.ne_of_val_ne (by rw [h4, Fin.val_mk]; omega))
      have hcP := commute_slPerm_slOn (N := m + 1 + 1 + 1)
        (π := Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) ⟨2, by omega⟩)
        (S := {0, 1, 4}) hfix2 hy''
      have haP : P * a = a * P := by
        rw [hP, ← hy''eq, ← map_mul, ← map_mul, hcP]
      have hgoal : endT₁ φ₂ * φ₁ y * (endT₁ φ₂)⁻¹ = φ₁ y := by
        have hT : endT₁ φ₂ =
            hElt φ₂ * ((hElt φ₂)⁻¹ * endT₁ φ₂ * hElt φ₂) * (hElt φ₂)⁻¹ := by group
        rw [hT, hconj, hswap, ← hconja]
        calc (hElt φ₂ * P * (hElt φ₂)⁻¹) * (hElt φ₂ * a * (hElt φ₂)⁻¹) *
              (hElt φ₂ * P * (hElt φ₂)⁻¹)⁻¹
            = hElt φ₂ * (P * a * P⁻¹) * (hElt φ₂)⁻¹ := by group
          _ = hElt φ₂ * a * (hElt φ₂)⁻¹ := by
                rw [show P * a * P⁻¹ = a from by rw [haP]; group]
      have hcommy : endT₁ φ₂ * φ₁ y = φ₁ y * endT₁ φ₂ := by
        rw [← mul_inv_eq_iff_eq_mul]
        exact hgoal
      exact hcommy.symm
  intro y hy
  have hyC : φ₁ y ∈ Subgroup.centralizer ({endT₁ φ₂} : Set G) := hD hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC
  exact hyC.symm

theorem twoEndNodes (hK1 : GGHalfNormSL014 φ₁ φ₂) :
    GGTypeATwoEndNodes φ₁ (endT₁ φ₂) (endT₂ φ₂) ∧
      K ≤ L ⊔ L.map (MulAut.conj (endT₁ φ₂)).toMonoidHom ⊔
        L.map (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom ⊔
          L.map (MulAut.conj (endT₁ φ₂ * endT₂ φ₂ * endT₁ φ₂)).toMonoidHom := by
  have hKle : K ≤ L ⊔ L.map (MulAut.conj (endT₁ φ₂)).toMonoidHom ⊔
      L.map (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom :=
    K_le_sup_conj (h := h)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact endT_involutions (h := h).1
      · intro j hj
        have hj' : j = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) := Fin.ext (by simp; omega)
        rw [hj']
        exact endT₁_cube_weylRep_last (h := h)
      · intro a b hab ha hb c
        exact endT₁_centralize_slOn_lt (h := h) hK1 (SpecialLinearGroup.transvection hab c)
          (transvection_mem_slOn hab c (by simp [ha]) (by simp [hb]))
    · exact endT_involutions (h := h).2
    · exact endT₁_mul_endT₂_cube (h := h)
    · exact endT₂_centralize_φ₁ (h := h)
  · exact hKle.trans (le_sup_of_le_left le_rfl)

end GGHalfCtx

theorem ggHalf_endNodes_of_coord (hH : GGTypeAHalfCoordInput) :
    GGHalfEndNodesOn (fun n => 6 ≤ n) := by
  intro G _ _ p B Bs x L D J n y K hn hcfg hOp hInn hNoTr hN hAut
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  obtain ⟨φ₁, φ₂, hco⟩ := hH G p B Bs x L D J m y K hcfg hInn hN
  have hctx : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂ := ⟨hcfg, hInn, hNoTr, hN, hco⟩
  obtain ⟨hT, hKle⟩ :=
    hctx.twoEndNodes
      (hctx.normSL014_of_alphaInner (by omega) (hctx.alphaInner_of_six_le (by omega)))
  have hmem : ∀ s, φ₂ s ∈ L ⊔ K := fun s =>
    Subgroup.mem_sup_right (hco.range₂ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩)
  refine ⟨φ₁, hco.range₁, ?_, endT₁ φ₂, endT₂ φ₂, hmem _, hmem _, hT, hKle⟩
  rw [(MonoidHom.ker_eq_bot_iff φ₁).mpr hco.inj₁]
  exact bot_le

theorem ggTypeAHalfJoinEndNodes_of_coord_five (hH : GGTypeAHalfCoordInput)
    (h5 : GGHalfEndNodesOn (fun n => n = 5)) : GGTypeAHalfJoinEndNodesInput :=
  GGHalfEndNodesOn.of_cases h5 (ggHalf_endNodes_of_coord hH)

end CFSG.StandardType

end
