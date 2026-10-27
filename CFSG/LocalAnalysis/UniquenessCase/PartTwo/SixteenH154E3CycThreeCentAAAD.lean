module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Conjugation

variable {W : Type*} [CommGroup W]

private lemma s16h_e3_CycThreeCentAAAD_stabSub_map_conj (g : MulAut W) (U : Subgroup W) :
    (stabSub U).map (MulAut.conj g).toMonoidHom = stabSub (U.map g.toMonoidHom) := by
  have hginj : Function.Injective g.toMonoidHom := fun a b h => g.injective h
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_stabSub] at hy ⊢
    intro v
    have hkey : ((MulAut.conj g) y) v = g (y (g⁻¹ v)) := by simp [MulAut.mul_apply]
    have hA : ((MulAut.conj g) y) v ∈ U.map g.toMonoidHom ↔ y (g⁻¹ v) ∈ U := by
      rw [hkey]
      exact Subgroup.mem_map_iff_mem hginj
    have hB : v ∈ U.map g.toMonoidHom ↔ g⁻¹ v ∈ U := by
      simpa using (Subgroup.mem_map_iff_mem hginj (x := g⁻¹ v))
    exact hA.trans ((hy (g⁻¹ v)).trans hB.symm)
  · intro hx
    rw [mem_stabSub] at hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_stabSub]
      intro u
      have hkey : (g⁻¹ * x * g) u = g⁻¹ (x (g u)) := by simp [MulAut.mul_apply]
      have hA : (g⁻¹ * x * g) u ∈ U ↔ x (g u) ∈ U.map g.toMonoidHom := by
        rw [hkey]
        simpa using (Subgroup.mem_map_iff_mem hginj (x := g⁻¹ (x (g u)))).symm
      have hB : g u ∈ U.map g.toMonoidHom ↔ u ∈ U :=
        Subgroup.mem_map_iff_mem hginj
      exact hA.trans ((hx (g u)).trans hB)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private lemma s16h_e3_CycThreeCentAAAD_centSub_map_conj (g : MulAut W) (U : Subgroup W) :
    (centSub U).map (MulAut.conj g).toMonoidHom = centSub (U.map g.toMonoidHom) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_centSub] at hy ⊢
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.inv_apply_self]
    rw [hy u hu]
  · intro hx
    rw [mem_centSub] at hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_centSub]
      intro u hu
      have hgu : g u ∈ U.map g.toMonoidHom := Subgroup.mem_map_of_mem g.toMonoidHom hu
      change g⁻¹ (x (g u)) = u
      rw [hx (g u) hgu]
      simp
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private lemma s16h_e3_CycThreeCentAAAD_map_inv_map (g : MulAut W) (U : Subgroup W) :
    (U.map g.toMonoidHom).map g⁻¹.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : g⁻¹.toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
    ext x
    simp [MulAut.inv_apply_self]
  rw [h, Subgroup.map_id]

end Conjugation

theorem s16h_e3_cyc_rank_one_conj
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p) (hp3 : p ≠ 3)
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6))
    {g : MulAut (Vtil V₀ V hV)} (hg : g ∈ Mbar D.M V₀ V hV)
    {B : Subgroup (MulAut (Vtil V₀ V hV))} (hBM : B ≤ Mbar D.M V₀ V hV)
    (hB : IsElemAbelian 3 B) (hBg : B ≤ stabSub ((wTil V₀ V hV L).map g.toMonoidHom)) :
    Nat.card ↥B ≤ 3 * Nat.card ↥(B ⊓ centSub ((wTil V₀ V hV L).map g.toMonoidHom)) := by
  let f : MulAut (Vtil V₀ V hV) →* MulAut (Vtil V₀ V hV) := (MulAut.conj g⁻¹).toMonoidHom
  have hfinj : Function.Injective f := fun _ _ hab => (MulAut.conj g⁻¹).injective hab
  have hMconj : (Mbar D.M V₀ V hV).map f = Mbar D.M V₀ V hV := by
    have hmem : g⁻¹ ∈ Subgroup.normalizer (Mbar D.M V₀ V hV : Set _) :=
      (Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hg)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
  have hB'm : B.map f ≤ Mbar D.M V₀ V hV := by
    rw [← hMconj]
    exact Subgroup.map_mono hBM
  have hB'ab : IsElemAbelian 3 (B.map f) := CFSG.Open.IsElemAbelian.map hB f
  have hstab : (stabSub ((wTil V₀ V hV L).map g.toMonoidHom)).map f
      = stabSub (wTil V₀ V hV L) := by
    rw [s16h_e3_CycThreeCentAAAD_stabSub_map_conj g⁻¹ ((wTil V₀ V hV L).map g.toMonoidHom),
      s16h_e3_CycThreeCentAAAD_map_inv_map g (wTil V₀ V hV L)]
  have hB'stab : B.map f ≤ stabSub (wTil V₀ V hV L) := by
    rw [← hstab]
    exact Subgroup.map_mono hBg
  have hbase := s16h_e3_cyc_rank_one_wTil D hV h hc hp hLp hp3 hn76 hB'm hB'ab hB'stab
  have hcent : (centSub ((wTil V₀ V hV L).map g.toMonoidHom)).map f
      = centSub (wTil V₀ V hV L) := by
    rw [s16h_e3_CycThreeCentAAAD_centSub_map_conj g⁻¹ ((wTil V₀ V hV L).map g.toMonoidHom),
      s16h_e3_CycThreeCentAAAD_map_inv_map g (wTil V₀ V hV L)]
  have hmapinf : (B ⊓ centSub ((wTil V₀ V hV L).map g.toMonoidHom)).map f
      = B.map f ⊓ centSub (wTil V₀ V hV L) := by
    rw [Subgroup.map_inf B (centSub ((wTil V₀ V hV L).map g.toMonoidHom)) f hfinj, hcent]
  have hcardB : Nat.card ↥(B.map f) = Nat.card ↥B := Subgroup.card_map_of_injective hfinj
  have hcardC : Nat.card ↥(B ⊓ centSub ((wTil V₀ V hV L).map g.toMonoidHom))
      = Nat.card ↥(B.map f ⊓ centSub (wTil V₀ V hV L)) := by
    rw [← hmapinf, Subgroup.card_map_of_injective hfinj]
  calc Nat.card ↥B = Nat.card ↥(B.map f) := hcardB.symm
    _ ≤ 3 * Nat.card ↥(B.map f ⊓ centSub (wTil V₀ V hV L)) := hbase
    _ = 3 * Nat.card ↥(B ⊓ centSub ((wTil V₀ V hV L).map g.toMonoidHom)) := by
        rw [hcardC]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
