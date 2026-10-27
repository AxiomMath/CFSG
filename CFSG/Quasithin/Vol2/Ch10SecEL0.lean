module

public import CFSG.Quasithin.Vol2.Ch10SecEIdent
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem twoResidual_eq_oTwoUpper (X : Subgroup G) : twoResidual X = oTwoUpper X := by
  unfold twoResidual
  exact le_antisymm (iInf₂_le _ ⟨oTwoUpper_le X, le_normalizer_oTwoUpper X,
    fun _ hx => exists_pow_mem_oTwoUpper X hx⟩)
    (le_iInf₂ fun _ hN => oTwoUpper_le_of_pow_mem hN.2.2)

theorem fsuL0_perfect (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅fsuL0 T L, fsuL0 T L⁆ = fsuL0 T L := by
  have hL := SecA.perfect_L hyp.fsu.maximal.1
  have hLt : ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ = CFSG.conjugate L t := by
    rw [SecA.conjugate_eq_map, ← Subgroup.map_commutator, hL]
  rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · calc L ⊔ CFSG.conjugate L t = ⁅L, L⁆ ⊔ ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ := by
          rw [hL, hLt]
      _ ≤ _ := sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem oTwoUpper_fsuL0_sup (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : oTwoUpper (fsuL0 T L ⊔ T) = fsuL0 T L := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  exact oTwoUpper_sup_eq_of_normal (eq_oTwoUpper_of_perfect (fsuL0_perfect h37 h38 hyp ht htn))
    hyp.fsu.sylow.1 (SecA.le_fsuM T L)

theorem twoResidual_fsuL0_sup (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : twoResidual (fsuL0 T L ⊔ T) = fsuL0 T L := by
  rw [twoResidual_eq_oTwoUpper, oTwoUpper_fsuL0_sup h37 h38 hyp]

omit [Finite G] in
theorem fsuL0_sup_le_normalizer (T L I : Subgroup G) :
    fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
  sup_le (SecA.fsuL0_le_normalizer_fsuVM T L I) (SecA.le_normalizer_fsuVM T L I)

theorem autI_commute (h37 : Vol2Native.A37ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∀ a ∈ autI (SecA.isElemAbelian_fsuVM hyp) L,
      ∀ b ∈ autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t), a * b = b * a := by
  intro a ha b hb
  obtain ⟨l, hl, rfl⟩ := (mem_autI _).mp ha
  obtain ⟨m, hm, rfl⟩ := (mem_autI _).mp hb
  have hc : ((l * m * l⁻¹ * m⁻¹ : Subgroup.normalizer (fsuVM T L I : Set G)) : G) ∈
      Subgroup.centralizer (fsuVM T L I : Set G) := by
    have h1 := SecA.commutator_conjugate_le h37 hyp ht htn
      (Subgroup.commutator_mem_commutator hl hm)
    rw [commutatorElement_def] at h1
    exact SecA.pCoreOf_le_centralizer_fsuVM h322 hyp h1.1
  have h1 := (convI_eq_one_iff (SecA.isElemAbelian_fsuVM hyp) _).mpr hc
  rw [← map_mul, ← map_mul]
  have e : l * m = (l * m * l⁻¹ * m⁻¹) * (m * l) := by group
  rw [e, map_mul, h1, one_mul]

theorem isSimpleGroup_autI_conjugate (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I)
    {t : G} (ht : t ∈ T) :
    IsSimpleGroup ↥(autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t)) ∧
      ∃ a ∈ autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t),
        ∃ a' ∈ autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t), a * a' ≠ a' * a := by
  obtain ⟨hs, x, y, hxy⟩ := SecA.isSimpleGroup_autOn h37 h38 h322 hyp
  have htN : t ∈ Subgroup.normalizer (fsuVM T L I : Set G) := SecA.le_normalizer_fsuVM T L I ht
  set f := (MulAut.conj (conjAct (fsuVM T L I) ⟨t, htN⟩)⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj _).injective
  have heq : autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t) =
      (autOn L (fsuVM T L I)).map f := SecA.autOn_conjugate htN
  rw [heq]
  refine ⟨(Subgroup.equivMapOfInjective _ f hf).symm.isSimpleGroup, f x, ⟨x, x.2, rfl⟩, f y,
    ⟨y, y.2, rfl⟩, fun h => hxy (Subtype.ext (hf (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]; exact h)))⟩

theorem autI_fsuL0 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L) =
      autI (SecA.isElemAbelian_fsuVM hyp) L ⊔
        autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t) := by
  rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
  exact SecA.autOn_sup_eq
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))

theorem ident_L0T
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G))
    {I' : Finset (Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))))}
    (hKJ : twoResidual (fsuL0 T L ⊔ T) ≤ thompsonJ (fsuL0 T L ⊔ T))
    (hcard : I'.card = 1 ∨ I'.card = 2)
    (hJeq : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = ⨆ K ∈ I', K)
    (hcomm : ∀ K ∈ I', ∀ K' ∈ I', K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hind : ∀ K ∈ I', K ⊓ ⨆ K' ∈ I', ⨆ (_ : K' ≠ K), K' = ⊥)
    (htrans : ∀ K ∈ I', ∀ K' ∈ I',
      ∃ s ∈ autI (SecA.isElemAbelian_fsuVM hyp) T, B1.conjAut s K = K') :
    (∃ K ∈ I', (∀ K' ∈ I', K' = K) ∧
        autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = K ∧
        oTwoUpper K = autI (SecA.isElemAbelian_fsuVM hyp) L ⊔
          autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t)) ∨
      ∃ K₁ ∈ I', ∃ K₂ ∈ I', (∀ K ∈ I', K = K₁ ∨ K = K₂) ∧ K₁ ≠ K₂ ∧
        autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = K₁ ⊔ K₂ ∧
        oTwoUpper K₁ = autI (SecA.isElemAbelian_fsuVM hyp) L ∧
        oTwoUpper K₂ = autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t) ∧
        (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧ K₁ ⊓ K₂ = ⊥ := by
  obtain ⟨hAs, a, b, hab⟩ := SecA.isSimpleGroup_autOn h37 h38 h322 hyp
  obtain ⟨hBs, hBn⟩ := isSimpleGroup_autI_conjugate h37 h38 h322 hyp ht
  refine eq_oTwoUpper_of_e23 (SecA.isElemAbelian_fsuVM hyp) (fsuL0_sup_le_normalizer T L I)
    hAs hBs ⟨a.1, a.2, b.1, b.2, fun h => hab (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h))⟩ hBn
    (autI_commute h37 h322 hyp ht htn) ?_ ?_ hcard hJeq hcomm hind htrans
  · rw [oTwoUpper_fsuL0_sup h37 h38 hyp]
    exact autI_fsuL0 h37 h38 hyp ht htn
  · rw [← twoResidual_eq_oTwoUpper]
    exact hKJ

end CFSG.Quasithin.Vol2.Ch10.SecE
