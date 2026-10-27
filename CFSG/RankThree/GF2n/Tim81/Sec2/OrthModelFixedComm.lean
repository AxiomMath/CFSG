module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelConj
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelOrder3

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.CGT.Timmesfeld75

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W}

private theorem fixedSub_inf_commSub_eq_bot_model {A A' : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Nat.card F)
    (hA'2 : ∀ a ∈ A', a * a = 1) (hA' : Nat.card A' = Nat.card F) (hne : A ≠ A') :
    fixedSub (hermRep l hF) A ⊓ commSub (hermRep l hF) A' = ⊥ := by
  obtain ⟨c, hc⟩ := eq_conj_rootGroup A hA2 hA
  obtain ⟨d, hd⟩ := eq_conj_rootGroup A' hA'2 hA'
  have hAc : A = conjSubgroup c upperSylow := eq_map_conj_upperSylow_of_forall_mem_iff hc
  have hA'c : A' = conjSubgroup d upperSylow := eq_map_conj_upperSylow_of_forall_mem_iff hd
  rw [Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
  rw [hAc, conjSubgroup, fixedSub_map_conj] at hy1
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy1
  rw [hA'c, conjSubgroup, commSub_map_conj] at hy2
  obtain ⟨b, hb, hb_eq⟩ := Submodule.mem_map.mp hy2
  have ha' : a ∈ herm1101 l F := by
    rw [fixedSub_upperSylow] at ha
    simpa using ha
  have haeq : a = hermDiag l hF ((a : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) a) :=
    eq_hermDiag_of_mem_herm1101 (hF := hF) a ha'
  have hb' : hermRep l hF (d⁻¹ * c) a ∈ commSub (hermRep l hF) upperSylow := by
    have hb'' : b = hermRep l hF (d⁻¹ * c) a := by
      calc b = hermRep l hF d⁻¹ (hermRep l hF d b) := by
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply]
        _ = hermRep l hF d⁻¹ (hermRep l hF c a) := by rw [hb_eq]
        _ = hermRep l hF (d⁻¹ * c) a := by rw [map_mul, Module.End.mul_apply]
    rw [← hb'']
    exact hb
  have hz11 : ((hermRep l hF (d⁻¹ * c)
      (hermDiag l hF ((a : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) a)) :
        ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      ((a : Matrix (Fin 2) (Fin 2) F) 0 0) *
        (((d⁻¹ * c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 *
          (((d⁻¹ * c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 ^ l) := by
    have hD : ((hermDiag l hF ((a : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) a) :
        ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) = !![(a : Matrix (Fin 2) (Fin 2) F) 0 0,
          0; 0, 0] := hermDiag_coe (hF := hF) _ _
    rw [hermRep_apply, hermAct_coe, triple_apply, hD]
    simp [CFSG.Quasithin.frobPow]
    ring_nf
  have hzero : ((a : Matrix (Fin 2) (Fin 2) F) 0 0) *
      (((d⁻¹ * c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 *
        (((d⁻¹ * c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 ^ l) = 0 := by
    have h11 : ((hermRep l hF (d⁻¹ * c)
        (hermDiag l hF ((a : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) a)) :
          ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have hmem : hermRep l hF (d⁻¹ * c)
          (hermDiag l hF ((a : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) a)) ∈
          AddSubgroup.toZModSubmodule (n := 2) (herm11 l F) := by
        rw [← commSub_upperSylow, ← haeq]
        exact hb'
      simpa [herm11] using hmem
    rwa [hz11] at h11
  rcases mul_eq_zero.mp hzero with ha0 | hr
  · have hazero : a = 0 := by
      rw [haeq]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hermDiag, ha0]
    rw [hazero]
    simp
  · have hr0 : ((d⁻¹ * c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · by_contra hne'
        exact (pow_ne_zero _ hne') h
    have hEq : upperSylow (F := F) = utri F := upperSylow_eq_utri
    have hmem : d⁻¹ * c ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))) := by
      have hborel : d⁻¹ * c ∈ borel F := mem_borel_iff.mpr hr0
      rw [hEq, normalizer_utri]
      exact hborel
    exfalso
    exact hne (by
      rw [hAc, hA'c]
      exact ((conjSubgroup_eq_conjSubgroup_iff (a := d) (b := c)
        (T := upperSylow)).mpr hmem).symm)

theorem IsOrthModule.fixedSub_inf_commSub_eq_bot (horth : IsOrthModule hF ρ)
    {A A' : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l))
    (hA2' : ∀ a ∈ A', a * a = 1) (hA' : Nat.card A' = 2 ^ (2 * l)) (hAA' : A ≠ A') :
    fixedSub ρ A ⊓ commSub ρ A' = ⊥ := by
  have horth0 := horth
  obtain ⟨j, β, hβ⟩ := horth
  set B : Subgroup SL(2, F) := A.map (fieldAut F j) with hB
  set B' : Subgroup SL(2, F) := A'.map (fieldAut F j) with hB'
  have hs := fieldAut_image_sylow A hA2 hA j
  have hs' := fieldAut_image_sylow A' hA2' hA' j
  have hB2 : ∀ b ∈ B, b * b = 1 := by rw [hB]; exact hs.1
  have hBcard : Nat.card B = 2 ^ (2 * l) := by rw [hB]; exact hs.2
  have hB2' : ∀ b ∈ B', b * b = 1 := by rw [hB']; exact hs'.1
  have hBcard' : Nat.card B' = 2 ^ (2 * l) := by rw [hB']; exact hs'.2
  have hFcard : Nat.card B = Nat.card F := by
    rw [hBcard, Nat.card_eq_fintype_card, hF]
  have hFcard' : Nat.card B' = Nat.card F := by
    rw [hBcard', Nat.card_eq_fintype_card, hF]
  have hcomp : ((fieldAutEquiv (F := F) j).symm.toMonoidHom.comp (fieldAut F j)) =
      MonoidHom.id (SL(2, F)) := by
    refine MonoidHom.ext fun a => ?_
    exact (fieldAutEquiv (F := F) j).symm_apply_apply a
  have hne : B ≠ B' := by
    intro h
    apply hAA'
    have h1 : B.map ((fieldAutEquiv (F := F) j).symm).toMonoidHom = A := by
      rw [hB, Subgroup.map_map, hcomp, Subgroup.map_id]
    have h2 : B'.map ((fieldAutEquiv (F := F) j).symm).toMonoidHom = A' := by
      rw [hB', Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [← h1, ← h2, h]
  have hmodel := fixedSub_inf_commSub_eq_bot_model (hF := hF) hB2 hFcard hB2' hFcard' hne
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hx1' : β x ∈ fixedSub (hermRep l hF) B := by
    rw [hB]
    exact (fixedSub_fieldAut_mem (hF := hF) (j := j) hβ A x).mp hx1
  have hx2' : β x ∈ commSub (hermRep l hF) B' := by
    rw [hB']
    exact (commSub_fieldAut_mem (hF := hF) hβ A' x).mp hx2
  rw [Submodule.eq_bot_iff] at hmodel
  have hzero : β x = 0 := hmodel (β x) (Submodule.mem_inf.mpr ⟨hx1', hx2'⟩)
  exact β.injective (by simpa using hzero)

end CFSG.RankThree.GF2n.Tim81.Sec2

end
