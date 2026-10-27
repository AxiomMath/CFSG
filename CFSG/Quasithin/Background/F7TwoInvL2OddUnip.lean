module

public import CFSG.Quasithin.Background.F7TwoInvL2OddUnipGen
public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GorensteinWalter CFSG.PSL2Table Matrix
open scoped MatrixGroups

theorem invAutGen_of_unip_invariant {K : Type} [Field K] [Finite K]
    (φ : MulAut (PSL2 K)) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) (h2 : (2 : K) ≠ 0)
    (hq : 5 ≤ Nat.card K) (hU : ∀ x ∈ unipotent K, φ x ∈ unipotent K)
    (hw : φ (splitWeyl K) = splitWeyl K) : InvAutGen (PSL2 K) φ := by
  have hs : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hodd₁ : Odd (Nat.card (unipotent K)) := odd_natCard_unipotent h2
  have hinj : Function.Injective (MulAut.conj (splitWeyl K)).toMonoidHom :=
    fun a b h => (MulAut.conj (splitWeyl K)).injective h
  refine invAutGen_of_odd_sup (U₁ := unipotent K)
    (U₂ := (unipotent K).map (MulAut.conj (splitWeyl K)).toMonoidHom) hs psl2_nonabelian hφ2 hφ1
    hodd₁ ?_ hU ?_ (unipotent_sup_conj_weyl_eq_top K)
  · rw [Subgroup.card_map_of_injective hinj]
    exact hodd₁
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨φ u, hU u hu, ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv, hw]

theorem odd_of_isOddPrimePower {q : ℕ} (hq : IsOddPrimePower q) : Odd q := by
  obtain ⟨p, n, -, hp, -, h⟩ := hq
  rw [h]
  exact hp.pow

theorem five_le_of_odd_of_three_lt {n : ℕ} (h : Odd n) (hn : 3 < n) : 5 ≤ n := by
  obtain ⟨m, hm⟩ := h
  omega

theorem two_ne_zero_of_odd_natCard {K : Type} [Field K] [Finite K] (h : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  have := Fintype.ofFinite K
  apply Ring.two_ne_zero
  intro hc
  have h1 := (FiniteField.even_card_iff_char_two (F := K)).mp hc
  rw [← Nat.card_eq_fintype_card] at h1
  have h2 := Nat.odd_iff.mp h
  omega

section Split

variable {K : Type} [Field K]

@[expose] noncomputable def pgl2S0GL (K : Type) [Field K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp [Matrix.det_fin_two])

@[expose] noncomputable def pgl2S0 (K : Type) [Field K] : PGL2 K :=
  Matrix.ProjGenLinGroup.mk (pgl2S0GL K)

theorem coe_pgl2S0GL : (pgl2S0GL K : Matrix (Fin 2) (Fin 2) K) = !![-1, 0; 0, 1] := rfl

theorem val_det_pgl2S0GL : ((pgl2S0GL K).det : K) = -1 := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_pgl2S0GL, Matrix.det_fin_two]

theorem pgl2S0GL_mul_self : pgl2S0GL K * pgl2S0GL K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_pgl2S0GL, Matrix.mul_apply, Fin.sum_univ_two]

theorem pgl2S0_mul_self : pgl2S0 K * pgl2S0 K = 1 := by
  rw [pgl2S0, ← map_mul, pgl2S0GL_mul_self, map_one]

theorem pgl2S0_ne_one (h2 : (2 : K) ≠ 0) : pgl2S0 K ≠ 1 := by
  intro h
  rw [pgl2S0, Matrix.ProjGenLinGroup.mk_eq_one] at h
  have hc := Subgroup.mem_center_iff.mp h (SpecialLinearGroup.toGL (unip (1 : K)))
  have h01 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hc
  simp [coe_pgl2S0GL, Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact h2 (by linear_combination h01)

theorem pgl2S0GL_mul_toGL_unip (t : K) :
    pgl2S0GL K * SpecialLinearGroup.toGL (unip t) =
      SpecialLinearGroup.toGL (unip (-t)) * pgl2S0GL K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_pgl2S0GL, Matrix.mul_apply, Fin.sum_univ_two]

theorem toGL_weyl_mul_pgl2S0GL :
    SpecialLinearGroup.toGL (weyl : SL(2, K)) * pgl2S0GL K *
        GeneralLinearGroup.scalar (Fin 2) (-1) =
      pgl2S0GL K * SpecialLinearGroup.toGL weyl := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_pgl2S0GL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar]

end Split

section Action

variable {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
  (hcard : 3 < Nat.card K)

theorem pgl2InnerAutPSL2_S0_unip (t : K) :
    pgl2InnerAutPSL2 K hK hcard (pgl2S0 K) (mk (unip t)) = mk (unip (-t)) := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply]
  show pgl2S0 K * Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip t)) * (pgl2S0 K)⁻¹ =
    Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL (unip (-t)))
  rw [mul_inv_eq_iff_eq_mul, pgl2S0, ← map_mul, ← map_mul, pgl2S0GL_mul_toGL_unip]

theorem pgl2InnerAutPSL2_S0_weyl :
    pgl2InnerAutPSL2 K hK hcard (pgl2S0 K) (splitWeyl K) = splitWeyl K := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply]
  show pgl2S0 K * Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL weyl) * (pgl2S0 K)⁻¹ =
    Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL weyl)
  rw [mul_inv_eq_iff_eq_mul, pgl2S0, ← map_mul, ← map_mul]
  exact (Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨-1, toGL_weyl_mul_pgl2S0GL⟩).symm

theorem invAutGen_pgl2_split_involution :
    InvAutGen (PSL2 K) (pgl2InnerAutPSL2 K hK hcard (pgl2S0 K)) := by
  have hodd := odd_of_isOddPrimePower hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  refine invAutGen_of_unip_invariant _ ?_ ?_ h2 (five_le_of_odd_of_three_lt hodd hcard) ?_ ?_
  · rw [← map_mul, pgl2S0_mul_self, map_one]
  · intro h1
    have h := DFunLike.congr_fun h1 (mk (unip (1 : K)))
    rw [pgl2InnerAutPSL2_S0_unip hK hcard, MulAut.one_apply, mk_eq_mk_iff] at h
    rcases h with h | h
    · have h01 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp at h01
      exact h2 (by linear_combination h01)
    · have h00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
      simp [neg_apply_SL] at h00
      exact h2 (by linear_combination h00)
  · intro x hx
    obtain ⟨t, rfl⟩ := mem_unipotent_iff_exists_unip.mp hx
    rw [pgl2InnerAutPSL2_S0_unip hK hcard]
    exact mk_unip_mem_unipotent _
  · exact pgl2InnerAutPSL2_S0_weyl hK hcard

end Action

section FieldAut

variable {K : Type} [Field K]

theorem psl2FieldAut_mk_unip (σ : K ≃+* K) (t : K) :
    psl2FieldAut K σ (mk (unip t)) = mk (unip (σ t)) := by
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center SL(2, K)) (unip t)) = _
  rw [psl2RingEquiv_mk]
  change QuotientGroup.mk' (Subgroup.center SL(2, K)) (SpecialLinearGroup.map σ.toRingHom (unip t))
    = QuotientGroup.mk' (Subgroup.center SL(2, K)) (unip (σ t))
  congr 1
  apply SL_ext <;> simp

theorem psl2FieldAut_splitWeyl (σ : K ≃+* K) : psl2FieldAut K σ (splitWeyl K) = splitWeyl K := by
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center SL(2, K)) weyl) = _
  rw [psl2RingEquiv_mk]
  change QuotientGroup.mk' (Subgroup.center SL(2, K)) (SpecialLinearGroup.map σ.toRingHom weyl)
    = QuotientGroup.mk' (Subgroup.center SL(2, K)) weyl
  congr 1
  apply SL_ext <;> simp

theorem invAutGen_psl2FieldAut [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) :
    InvAutGen (PSL2 K) (psl2FieldAut K σ) := by
  have hodd := odd_of_isOddPrimePower hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  refine invAutGen_of_unip_invariant _ ?_ ?_ h2 (five_le_of_odd_of_three_lt hodd hcard) ?_ ?_
  · rw [← map_mul, hσ2, map_one]
  · intro h1
    exact hσ1 (psl2FieldAut_injective K (h1.trans (map_one (psl2FieldAut K)).symm))
  · intro x hx
    obtain ⟨t, rfl⟩ := mem_unipotent_iff_exists_unip.mp hx
    rw [psl2FieldAut_mk_unip]
    exact mk_unip_mem_unipotent _
  · exact psl2FieldAut_splitWeyl σ

end FieldAut

end CFSG.Quasithin.F7Two
