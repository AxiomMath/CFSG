module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpUnitaryMarkAux
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIUnitaryTwo
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSU StatedSL)
open CFSG.StandardType.ClassicalBlocks


theorem kgfniSp_unitaryBlock_negMarking_congr {X H : Type} [Group X] [Group H] {F C : Subgroup H}
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2)
    (e : ↥F ≃* ↥(GUFull m Q E)) (hC : IsComponentOf C F)
    (θ : X ≃* ↥C) (fX : MulAut X) (fC : MulAut ↥C) (hθ : ∀ x : X, θ (fX x) = fC (θ x))
    (B : GL (Fin m) E) (hB : B ∈ GUFull m Q E) (τ : E ≃+* E) (hτ : τ ≠ 1)
    (hτodd : Odd (orderOf τ))
    (hsq : ∀ c : ↥C,
      ((e ⟨fC c, hC.1 (fC c).2⟩ : GUFull m Q E) : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom
          ((e ⟨c, hC.1 c.2⟩ : GUFull m Q E) : GL (Fin m) E) * B⁻¹) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ' => kgInducedAut θ' fX ∉ I := by
  classical
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  have hp2 : ringChar E = 2 := CharP.eq E hUF.charP ‹CharP E 2›
  have hQ : Q = 2 ^ f := by rw [hQf, hp2]
  have hK : Nat.card E = (2 ^ f) ^ 2 := by rw [hE, hQ]
  clear hQf
  subst Q
  let C₀ : Subgroup ↥(GUFull m (2 ^ f) E) := (C.subgroupOf F).map e.toMonoidHom
  have hCsub : IsComponentOf (C.subgroupOf F) ⊤ :=
    ⟨le_top,
      Assembly.IsSubnormal.of_mathlib (Assembly.IsSubnormal.subgroupOf hC.2.1),
      Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (G := H) hC.1) hC.2.2⟩
  have hC0 : IsComponentOf C₀ ⊤ := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := e.toMonoidHom) e.injective).mpr hCsub
    simpa [C₀] using h
  let Cgl : Subgroup (GL (Fin m) E) := C₀.map (GUFull m (2 ^ f) E).subtype
  have hCgl : IsComponentOf Cgl (GUFull m (2 ^ f) E) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := (GUFull m (2 ^ f) E).subtype) (GUFull m (2 ^ f) E).subtype_injective).mpr hC0
    simpa [Cgl, Subgroup.map_top, Subgroup.range_subtype] using h
  have hCgl_eq : Cgl = StatedSU m (2 ^ f) E :=
    eq_statedSU_of_isComponentOf_unitaryFull hE hCgl
  let eC : ↥C ≃* ↥(StatedSU m (2 ^ f) E) :=
    (Subgroup.subgroupOfEquivOfLe hC.1).symm.trans
      ((Subgroup.equivMapOfInjective (C.subgroupOf F) e.toMonoidHom
          (by simpa using e.injective)).trans
        ((Subgroup.equivMapOfInjective C₀ (GUFull m (2 ^ f) E).subtype
          (GUFull m (2 ^ f) E).subtype_injective).trans
          (MulEquiv.subgroupCongr hCgl_eq)))
  have eC_coe : ∀ c : ↥C, ((eC c : ↥(StatedSU m (2 ^ f) E)) : GL (Fin m) E) =
      ((e ⟨c, hC.1 c.2⟩ : GUFull m (2 ^ f) E) : GL (Fin m) E) := fun c => rfl
  let g : MulAut ↥(StatedSU m (2 ^ f) E) := eC.symm.trans (fC.trans eC)
  have hg : ∀ x : ↥(StatedSU m (2 ^ f) E),
      ((g x : ↥(StatedSU m (2 ^ f) E)) : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom
          ((x : ↥(StatedSU m (2 ^ f) E)) : GL (Fin m) E) * B⁻¹ := by
    intro x
    set c : ↥C := eC.symm x with hc
    have hx : eC c = x := eC.apply_symm_apply x
    have h1 : ((g x : ↥(StatedSU m (2 ^ f) E)) : GL (Fin m) E) =
        ((e ⟨fC c, hC.1 (fC c).2⟩ : GUFull m (2 ^ f) E) : GL (Fin m) E) := by
      rw [← hx]
      simp only [g, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact eC_coe (fC c)
    have h2 : ((x : ↥(StatedSU m (2 ^ f) E)) : GL (Fin m) E) =
        ((e ⟨c, hC.1 c.2⟩ : GUFull m (2 ^ f) E) : GL (Fin m) E) := by
      rw [← hx]
      exact eC_coe c
    rw [h1, h2]
    exact hsq c
  have hqs : Assembly.IsQuasisimple ↥(StatedSU m (2 ^ f) E) := hCgl_eq ▸ hCgl.2.2
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m ≤ 1 := by omega
    haveI : Subsingleton ↥(StatedSL m E) :=
      CFSG.LieType.SemisimpleCentralizers.Held.hct_subsingleton_statedSL_of_le_one hm1
    haveI : Subsingleton ↥(StatedSU m (2 ^ f) E) := by
      refine ⟨fun x y => ?_⟩
      have hx : (⟨x.1, CFSG.Open.StatedAPI.statedSU_le_statedSL m (2 ^ f) E x.2⟩ :
          ↥(StatedSL m E)) =
          ⟨y.1, CFSG.Open.StatedAPI.statedSU_le_statedSL m (2 ^ f) E y.2⟩ :=
        Subsingleton.elim _ _
      exact Subtype.ext (show (x : GL (Fin m) E) = (y : GL (Fin m) E) from
        congrArg (fun z : ↥(StatedSL m E) => (z : GL (Fin m) E)) hx)
    haveI : Nontrivial (↥(StatedSU m (2 ^ f) E) ⧸
        Subgroup.center ↥(StatedSU m (2 ^ f) E)) := hqs.2.toNontrivial
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (↥(StatedSU m (2 ^ f) E) ⧸
      Subgroup.center ↥(StatedSU m (2 ^ f) E))).exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  have hmark : LargeEvenMarking ↥(StatedSU m (2 ^ f) E)
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun j k => k = g j) φ) := by
    by_cases hm2eq : m = 2
    · subst m
      have hf : 2 ≤ f := by
        rcases Nat.lt_or_ge f 2 with hlt | hge
        · rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl
          · rw [pow_zero] at hK
            have := Finite.one_lt_card (α := E)
            omega
          · rw [pow_one] at hK
            have hsolv : Group.IsSolvable ↥(StatedSU 2 2 E) :=
              isSolvable_statedSU_two_two hK
            exact (ResU3Three.not_isSolvable_of_isQuasisimple (hCgl_eq ▸ hCgl.2.2) hsolv).elim
        · exact hge
      have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E := by
        refine ⟨Nat.prime_two, ?_, ?_⟩
        · rcases Nat.eq_zero_or_pos f with h0 | hpos
          · rw [h0, pow_zero, one_pow] at hK
            have := Finite.one_lt_card (α := E)
            omega
          · exact hpos
        · rw [hK, pow_two, ← pow_add]; ring
      obtain ⟨z, hz⟩ := kgfniSpUMark_fixedSubfield_restricts hK τ hτ hτodd
      let eSU : ↥(LargeEvenSUGroup (Fin 2) E (2 ^ f)) ≃* ↥(StatedSU 2 (2 ^ f) E) :=
        MulEquiv.subgroupCongr (largeEvenSUGroup_eq_statedSU 2 (2 ^ f))
      let f' : MulAut ↥(LargeEvenSUGroup (Fin 2) E (2 ^ f)) :=
        eSU.trans (g.trans eSU.symm)
      have hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin 2) E (2 ^ f)),
          (f' c : GL (Fin 2) E) =
            B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
              (c : GL (Fin 2) E) * B⁻¹ := by
        intro c
        have hcoe : ((eSU c : ↥(StatedSU 2 (2 ^ f) E)) : GL (Fin 2) E) = (c : GL (Fin 2) E) := rfl
        have hf'_coe : (f' c : GL (Fin 2) E) =
            ((g (eSU c) : ↥(StatedSU 2 (2 ^ f) E)) : GL (Fin 2) E) := rfl
        rw [hf'_coe, hg (eSU c), hcoe]
        congr 2
      have hB_gu : B ∈ LargeEvenGUSet (Fin 2) E (2 ^ f) := by
        have hbar : ∀ x : E, hUF.bar x = x ^ (2 ^ f) := fun x => hUF.bar_apply x
        have h_eq : GUFull 2 (2 ^ f) E =
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
              hUF (CFSG.RankThree.PartOne.KCUnitaryModel.idGram E 2) :=
          ggJS2_GUFull_eq_primeFormUnitary hUF hbar
        have hB_prime : B ∈
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
              hUF (CFSG.RankThree.PartOne.KCUnitaryModel.idGram E 2) := by
          rw [← h_eq]
          exact hB
        exact CFSG.StandardType.TableBUD.mem_guSet_of_mem_primeFormUnitary hUF hB_prime
      have hmark_LE : LargeEvenMarking ↥(LargeEvenSUGroup (Fin 2) E (2 ^ f))
          (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
            LargeEvenInduces θ (fun j k => k = f' j) φ) :=
        unitaryTwo_fieldAction_oneMarking_no_hf hUF f' hB_gu hpoint z hz
      refine largeEvenMarking_congr eSU ?_ hmark_LE
      intro lab R _ I F θ hθ
      rintro ⟨φ, hφ, hind⟩
      have hrel : ∀ x x' : ↥(LargeEvenSUGroup (Fin 2) E (2 ^ f)),
          (x' = f' x) ↔ (eSU x' = g (eSU x)) := by
        intro x x'
        have hf' : eSU (f' x) = g (eSU x) := by
          simp only [f', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        rw [← hf']
        exact (eSU.injective.eq_iff).symm
      exact hθ ⟨φ, hφ,
        (largeEvenInduces_congr_equiv eSU θ
          (fun j k => k = f' j)
          (fun j k => k = g j) hrel φ).1 hind⟩
    · have hm3 : 3 ≤ m := by omega
      have h32 : (m, 2 ^ f) ≠ (3, 2) := by
        intro h
        have hm3' : m = 3 := congrArg Prod.fst h
        have h2 : 2 ^ f = 2 := congrArg Prod.snd h
        subst m
        have hK2 : Nat.card E = 2 ^ 2 := by rw [hK, h2]
        have hCgl_eq' : Cgl = StatedSU 3 2 E := by rw [hCgl_eq, h2]
        have hsolv : Group.IsSolvable ↥(StatedSU 3 2 E) := isSolvable_statedSU_three_two hK2
        exact (ResU3Three.not_isSolvable_of_isQuasisimple (hCgl_eq' ▸ hCgl.2.2) hsolv).elim
      exact kgfniSpUMark_marking_high hK hm3 h32 B hB τ hτ hτodd g hg
  have hfg : ∀ x : X, (θ.trans eC) (fX x) = g ((θ.trans eC) x) := by
    intro x
    simp only [MulEquiv.trans_apply]
    rw [hθ x]
    change eC (fC (θ x)) = g (eC (θ x))
    refine Subtype.ext ?_
    simp only [g, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, eC_coe]
  exact kgFieldRestriction_of_oneMarking_congr (θ.trans eC) fX g hfg hmark

end CFSG.StandardType
