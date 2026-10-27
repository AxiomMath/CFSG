module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinInv
public import CFSG.CGT.Timmesfeld75.ListWCLinSylow
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

private theorem mark_sl_conj (m : ℕ) (hm : 3 ≤ m + 1)
    (S : Subgroup (SL(m + 1, ZMod 2))) (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (SL(m + 1, ZMod 2)), IsPGroup 2 T → S ≤ T → T = S)
    (t : SL(m + 1, ZMod 2)) (htS : t ∈ S) (ht : orderOf t = 2)
    (hc : ∀ s ∈ S, s * t = t * s) :
    IsConj (ggInvSL (m + 1) 1 (ZMod 2)) t := by
  obtain ⟨P, hSP⟩ := hS.exists_le_sylow
  have hPS : (P : Subgroup (SL(m + 1, ZMod 2))) = S := hmax _ P.isPGroup' hSP
  obtain ⟨P₀, hP₀⟩ :=
    exists_sylow_unitriangular (K := ZMod 2) 2 (n := m + 1) (by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(m + 1, ZMod 2)) P₀ P
  have hmem : ∀ x : SL(m + 1, ZMod 2), x ∈ (P : Subgroup (SL(m + 1, ZMod 2))) ↔
      g⁻¹ * x * g ∈ unitriangular (m + 1) (ZMod 2) := by
    intro x
    rw [← hP₀, ← hg]
    exact mem_smul_sylow_iff_inv_mul_mul_mem
  set u : SL(m + 1, ZMod 2) := g⁻¹ * t * g with hu
  have htP : t ∈ (P : Subgroup (SL(m + 1, ZMod 2))) := by rw [hPS]; exact htS
  have huU : u ∈ unitriangular (m + 1) (ZMod 2) := by
    rw [hu]
    exact (hmem t).1 htP
  have hu_comm : ∀ v ∈ unitriangular (m + 1) (ZMod 2), u * v = v * u := by
    intro v hv
    have hgv : g * v * g⁻¹ ∈ S := by
      rw [← hPS]
      rw [hmem]
      have h1 : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      rw [h1]
      exact hv
    have h := hc (g * v * g⁻¹) hgv
    rw [hu]
    calc g⁻¹ * t * g * v = g⁻¹ * (t * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * t) * g := by rw [h]
      _ = v * (g⁻¹ * t * g) := by group
  obtain ⟨b, hb⟩ :=
    eq_one_add_single_of_commute_unitri (K := ZMod 2) (m := m + 1) (by omega) huU hu_comm
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hu1 : u ≠ 1 := by
    intro h
    apply ht1
    calc t = g * u * g⁻¹ := by rw [hu]; group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  have hij : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have hb0 : b ≠ 0 := by
    intro h0
    apply hu1
    have hmat : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = 1 := by
      rw [hb, h0]
      simp
    exact Subtype.ext hmat
  have hu_tv : u = Matrix.SpecialLinearGroup.transvection hij b := by
    apply Subtype.ext
    rw [hb, Matrix.SpecialLinearGroup.transvection_coe]
    rfl
  obtain ⟨g', hg'⟩ :=
    exists_conj_transvection_eq (F := ZMod 2) (m := m) (by omega)
      (i := (0 : Fin (m + 1))) (j := Fin.last m) hij (c := b) hb0
  have huG : IsConj u (ggInvSL (m + 1) 1 (ZMod 2)) := by
    rw [isConj_iff]
    exact ⟨g', by rw [hu_tv]; exact hg'⟩
  have hut : IsConj u t := by
    rw [isConj_iff]
    exact ⟨g, by rw [hu]; group⟩
  exact huG.symm.trans hut

theorem isConj_jN_one_of_central_in_sylow (N : ℕ) (hN : 3 ≤ N)
    (S : Subgroup (GL (Fin N) (ZMod 2))) (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (GL (Fin N) (ZMod 2)), IsPGroup 2 T → S ≤ T → T = S)
    (t : GL (Fin N) (ZMod 2)) (htS : t ∈ S) (ht : orderOf t = 2)
    (hc : ∀ s ∈ S, s * t = t * s) : IsConj (jN N 1) t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  let e : SL(m + 1, ZMod 2) ≃* GL (Fin (m + 1)) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL (toGL_bijective (m + 1))
  let S' : Subgroup (SL(m + 1, ZMod 2)) := S.comap e.toMonoidHom
  let t' : SL(m + 1, ZMod 2) := e.symm t
  have hS' : IsPGroup 2 S' := hS.comap_of_injective e.toMonoidHom e.injective
  have het' : e t' = t := e.apply_symm_apply t
  have ht'S : t' ∈ S' := by
    show e t' ∈ S
    rw [het']
    exact htS
  have ht' : orderOf t' = 2 := by
    have h := orderOf_injective e.toMonoidHom e.injective t'
    have het2 : e.toMonoidHom t' = t := het'
    rw [het2, ht] at h
    exact h.symm
  have hmax' : ∀ T : Subgroup (SL(m + 1, ZMod 2)), IsPGroup 2 T → S' ≤ T → T = S' := by
    intro T hT hST
    have hmap : T.map e.toMonoidHom = S := by
      apply hmax
      · exact hT.map e.toMonoidHom
      · have h1 : S'.map e.toMonoidHom ≤ T.map e.toMonoidHom := Subgroup.map_mono hST
        have h2 : S'.map e.toMonoidHom = S :=
          Subgroup.map_comap_eq_self_of_surjective e.surjective S
        rwa [h2] at h1
    calc T = (T.map e.toMonoidHom).comap e.toMonoidHom :=
          (Subgroup.comap_map_eq_self_of_injective e.injective T).symm
      _ = S.comap e.toMonoidHom := by rw [hmap]
  have hc' : ∀ s ∈ S', s * t' = t' * s := by
    intro s hs
    apply e.injective
    simpa only [map_mul, het'] using hc (e s) hs
  have hconj := mark_sl_conj m (by omega) S' hS' hmax' t' ht'S ht' hc'
  have hmap := MonoidHom.map_isConj e.toMonoidHom hconj
  have h1 : e.toMonoidHom (ggInvSL (m + 1) 1 (ZMod 2)) = jN (m + 1) 1 := rfl
  have het2 : e.toMonoidHom t' = t := het'
  rw [h1, het2] at hmap
  exact hmap

end CFSG.StandardType.FF81.RootFusionLin

end
