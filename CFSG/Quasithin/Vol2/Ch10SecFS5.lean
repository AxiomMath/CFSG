module

public import CFSG.Quasithin.Vol2.Ch10SecFS4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

theorem eFour_fix_four : ∀ σ ∈ SecE.eFour, σ 4 = 4 := by decide +kernel

theorem vFour_fix_four : ∀ σ ∈ SecE.vFour, σ 4 = 4 := by decide +kernel

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : SecE.Case2Data hyp t)

theorem fix_vOneW_of_mem_K₁ {g : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hg : g ∈ D.K₁) (h4 : D.θ₁ ⟨g, hg⟩ 4 = 4) : g (vOneW D).1 = (vOneW D).1 := by
  have h1 := coord₁_apply D ⟨g, hg⟩ (vOneW D)
  rw [coord₁_vOneW, pact_wFour_of_fix _ h4, ← coord₁_vOneW D] at h1
  exact congrArg Subtype.val (coord₁_injective D h1)

theorem fix_vOneW_of_mem_thompsonJ
    {p : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hp : p ∈ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T)) :
    p (vOneW D).1 = (vOneW D).1 := by
  have hle : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) ≤
      MulAction.stabilizer _ (vOneW D).1 := by
    rw [D.thompsonJ_eq]
    refine sup_le (fun q hq => ?_) (fun q hq => D.triv₂ hq.1 (vOneW D).2)
    exact fix_vOneW_of_mem_K₁ D hq.1 (eFour_fix_four _ ((D.memP₁ q hq.1).mp hq))
  exact hle hp

theorem fix_vOneW_of_mem_inf_L
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (h2 : Ch10.Case10_1_1Two T L I)
    {p : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hp : p ∈ autI (SecA.isElemAbelian_fsuVM hyp) (T ⊓ L)) :
    p (vOneW D).1 = (vOneW D).1 := by
  have hpK : p ∈ D.K₁ := oTwoUpper_le _ (D.autI_inf_L_le hp)
  exact fix_vOneW_of_mem_K₁ D hpK
    (vFour_fix_four _ ((D.mem_autI_inf_L_iff h37 h38 h322 h2 p hpK).mp hp))

theorem conj_vOne_of_fix (g : Subgroup.normalizer (fsuVM T L I : Set G))
    (hg : convI (SecA.isElemAbelian_fsuVM hyp) g (vOneW D).1 = (vOneW D).1) :
    (g : G) * vOne D * (g : G)⁻¹ = vOne D :=
  (SecE.convI_fix_iff _ g _).mp hg

theorem eq_vOne_of_fix
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (h2 : Ch10.Case10_1_1Two T L I) {y : G}
    (hyU : y ∈ fsuUL T L I) (hJ : ∀ j ∈ thompsonJ T, j * y * j⁻¹ = y)
    (hTL : ∀ s ∈ T ⊓ L, s * y * s⁻¹ = y) : y = 1 ∨ y = vOne D := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hyV : y ∈ fsuVM T L I := SecA.fsuUL_le_fsuVM T L I hyU
  have hw1 : IntMod.mk hV ⟨y, hyV⟩ ∈ commV D.K₁ := by
    have := SecE.mk_mem_commV_of_mem_commutator hV hLN hyU hyV
    rw [← D.oTwo₁] at this
    refine Subgroup.closure_mono (fun w hw => ?_) this
    obtain ⟨g, hg, v, hv⟩ := hw
    exact ⟨g, oTwoUpper_le _ hg, v, hv⟩
  set u : ↥(commV D.K₁) := ⟨IntMod.mk hV ⟨y, hyV⟩, hw1⟩ with hu
  have hfixJ : ∀ p ∈ D.K₁ ⊓ autI hV (thompsonJ T), p u.1 = u.1 := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := (mem_autI _).mp hp.2
    apply IntMod.val_injective
    rw [convI_apply_val]
    exact hJ j hj
  have hA := pact_eq_of_fix D u hfixJ (σ := SecE.sA) (by decide +kernel)
  have hB := pact_eq_of_fix D u hfixJ (σ := SecE.sB) (by decide +kernel)
  have hR : pact SecE.rA (coord₁ D u) = coord₁ D u := by
    rw [← coord₁_symm_apply]
    congr 1
    apply Subtype.ext
    have hmem : (D.θ₁.symm SecE.rA).1 ∈ autI hV (T ⊓ L) :=
      (D.mem_autI_inf_L_iff h37 h38 h322 h2 _ (D.θ₁.symm SecE.rA).2).mpr
        (by simpa using SecE.rA_mem_vFour)
    obtain ⟨s, hs, hseq⟩ := (mem_autI _).mp hmem
    show (D.θ₁.symm SecE.rA).1 u.1 = u.1
    rw [← hseq]
    apply IntMod.val_injective
    rw [convI_apply_val]
    exact hTL s hs
  have hval : ∀ z : ↥(commV D.K₁), u = z → y = IntMod.val z.1 := by
    rintro z rfl
    rfl
  rcases eq_of_fix_rA _ (coord₁_isEven D u) hA hB hR with h | h
  · left
    have h1 : u = 1 := coord₁_injective D (by rw [h]; simp [coord₁])
    rw [hval 1 h1]
    rfl
  · right
    exact hval _ (coord₁_injective D (by rw [h, coord₁_vOneW]))

theorem T1_le_centralizer_vOne (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two)
    (h2 : Ch10.Case10_1_1Two T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    Ch10.T1 T L ≤ Subgroup.centralizer ({vOne D} : Set G) := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  intro x hx
  have hxT : x ∈ T := hx.1
  have hxN : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hx.2
  have hT1N : Ch10.T1 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I))
      inf_le_right
  have hU : x * vOne D * x⁻¹ ∈ fsuUL T L I :=
    (Subgroup.mem_normalizer_iff.mp (hT1N hx) _).mp (vOne_mem_fsuUL D h37 h38 h2 ht htn)
  have hconj : ∀ g : G, g * (x * vOne D * x⁻¹) * g⁻¹ =
      x * ((x⁻¹ * g * x) * vOne D * (x⁻¹ * g * x)⁻¹) * x⁻¹ := fun g => by group
  have hTJ : x⁻¹ ∈ Subgroup.normalizer (thompsonJ T : Set G) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)) (T.inv_mem hxT)
  have hJ : ∀ j ∈ thompsonJ T, j * (x * vOne D * x⁻¹) * j⁻¹ = x * vOne D * x⁻¹ := by
    intro j hj
    have hj' : x⁻¹ * j * x ∈ thompsonJ T := by
      have := (Subgroup.mem_normalizer_iff.mp hTJ j).mp hj
      simpa using this
    have hjN : x⁻¹ * j * x ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.le_normalizer_fsuVM T L I ((iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T) hj')
    rw [hconj, conj_vOne_of_fix D ⟨_, hjN⟩
      (fix_vOneW_of_mem_thompsonJ D (convI_mem_autI hV hj' hjN))]
  have hTL : ∀ s ∈ T ⊓ L, s * (x * vOne D * x⁻¹) * s⁻¹ = x * vOne D * x⁻¹ := by
    intro s hs
    have hs' : x⁻¹ * s * x ∈ T ⊓ L := by
      refine ⟨T.mul_mem (T.mul_mem (T.inv_mem hxT) hs.1) hxT, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp hxN s).mp hs.2
      simpa using this
    have hsN : x⁻¹ * s * x ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.le_normalizer_fsuVM T L I hs'.1
    rw [hconj, conj_vOne_of_fix D ⟨_, hsN⟩
      (fix_vOneW_of_mem_inf_L D h37 h38 h322 h2 (convI_mem_autI hV hs' hsN))]
  rcases eq_vOne_of_fix D h37 h38 h322 h2 hU hJ hTL with h | h
  · exfalso
    apply vOne_ne_one D
    calc vOne D = x⁻¹ * (x * vOne D * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    calc vOne D * x = (x * vOne D * x⁻¹) * x := by rw [h]
      _ = x * vOne D := by group

theorem T1_le_centralizer_vTwo (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two)
    (h2 : Ch10.Case10_1_1Two T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    Ch10.T1 T L ≤ Subgroup.centralizer ({t⁻¹ * vOne D * t} : Set G) := by
  intro x hx
  have hx' : t * x * t⁻¹ ∈ Ch10.T1 T L :=
    (Subgroup.mem_normalizer_iff.mp (SecE.le_normalizer_T1 h37 h38 hyp ht) x).mp hx
  have h1 := Subgroup.mem_centralizer_iff.mp
    (T1_le_centralizer_vOne D h37 h38 h322 h2 ht htn hx') (vOne D) rfl
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  calc t⁻¹ * vOne D * t * x = t⁻¹ * (vOne D * (t * x * t⁻¹)) * t := by group
    _ = t⁻¹ * ((t * x * t⁻¹) * vOne D) * t := by rw [h1]
    _ = x * (t⁻¹ * vOne D * t) := by group

end CFSG.Quasithin.Vol2.Ch10.SecF
