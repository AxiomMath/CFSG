module

public import CFSG.Quasithin.Background.E6EighteenE
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentJ4Three

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

theorem noA7Fix_m11 : NoA7Fix ↥NativeSporadic.M11 :=
  noA7Fix_of_not_dvd (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num)

theorem noA7Fix_m12 : NoA7Fix ↥NativeSporadic.M12 :=
  noA7Fix_of_not_dvd (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)

theorem noA7Fix_m22 :
    NoA7Fix ↥NativeSporadic.M22 := by
  refine noA7Fix_of_fixed_card fun α hα hα1 => ?_
  rcases CFSG.GH74.Generic.S45.m22_fixed_card α hα hα1 with h | h | h <;> rw [h] <;> norm_num

theorem noA7Fix_m23 :
    NoA7Fix ↥NativeSporadic.M23 := by
  refine noA7Fix_of_fixed_card fun α hα hα1 => ?_
  rw [CFSG.GH74.Generic.S45.LAlt.m23_fixed_card α hα hα1]
  norm_num

theorem noA7Fix_m24 :
    NoA7Fix ↥NativeSporadic.M24 := by
  refine noA7Fix_of_fixed_card fun α hα hα1 => ?_
  rcases CFSG.GH74.Generic.S45.LAlt.m24_fixed_card α hα hα1 with h | h <;> rw [h] <;> norm_num

section J

open CFSG.Sporadic.Schreier

theorem noA7Fix_j2 :
    NoA7Fix NativeSporadic.J2 := by
  refine NoA7Fix.of_mulEquiv CFSG.ComponentClassification.J2Cover.nativeEquivP.symm ?_
  refine noA7Fix_of_fixed_card fun α hα hα1 => ?_
  have hc : Nat.card {x : ↥CFSG.ComponentClassification.J2Cover.P // α x = x} =
      Nat.card ↥(fixSub α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixSub.symm)
  rw [hc]
  rcases Id2519.Tab.j2_fixSub_card α hα hα1 with h | h | h <;> rw [h] <;> norm_num

theorem forall_not_isComponent_of_isConj {X : Type*} [Group X] {a b : X} (h : IsConj a b)
    (hb : ∀ B : Subgroup ↥(Subgroup.centralizer ({b} : Set X)), ¬ CFSG.IsComponent B) :
    ∀ B : Subgroup ↥(Subgroup.centralizer ({a} : Set X)), ¬ CFSG.IsComponent B := by
  intro B hB
  obtain ⟨x, hx⟩ := isConj_iff.1 h
  obtain ⟨B', hB'⟩ := Id2519.exists_isComponent_centralizer_of_mulEquiv (MulAut.conj x) a hB
  have hxa : (MulAut.conj x) a = b := by
    rw [MulAut.conj_apply]
    exact hx
  subst hxa
  exact hb B' hB'

theorem exists_noncomm_of_isSimpleGroup {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup S := { (inferInstance : Group S) with mul_comm := fun a b => hcon a b }
  exact h (IsSimpleGroup.prime_card (α := S))

theorem j4_involution_centralizer_component_free
    {r : ↥CFSG.Sporadic.J4.J} (hsq : r * r = 1) (hne : r ≠ 1) :
    ∀ B : Subgroup ↥(Subgroup.centralizer ({r} : Set ↥CFSG.Sporadic.J4.J)),
      ¬ CFSG.IsComponent B := by
  have hcore : ∀ c, Id2519.J4Row.CentralizerCore c →
      ∀ B : Subgroup ↥(Subgroup.centralizer
        ({CFSG.Sporadic.J4.QT.eta CFSG.Sporadic.J4.QT.uJ 11 c} : Set ↥CFSG.Sporadic.J4.J)),
        ¬ CFSG.IsComponent B := fun c h B hB => by
    obtain ⟨N, hNK, hn, hp, hc⟩ := h
    exact Id2519.J4Row.noComponent_of_normal_pgroup hNK hn hp hc B hB
  rcases CFSG.Sporadic.J4.QT.inv_conj_root CFSG.Sporadic.J4.j4Facts hsq hne with hc | hc
  · exact forall_not_isComponent_of_isConj hc.symm (hcore 1 Id2519.J4Row.centralizerCore_one)
  · exact forall_not_isComponent_of_isConj hc.symm (hcore 3 Id2519.J4Row.centralizerCore_three)

theorem forall_not_isComponent_of_equiv_sub {X M : Type*} [Group X] [Group M] (H : Subgroup M)
    (e : X ≃* H) (hfree : ∀ r : H, r * r = 1 → r ≠ 1 →
      ∀ B : Subgroup ↥(Subgroup.centralizer ({r} : Set ↥H)), ¬ CFSG.IsComponent B)
    (y : X) (hy : orderOf y = 2) (B : Subgroup ↥(Subgroup.centralizer ({y} : Set X))) :
    ¬ CFSG.IsComponent B := by
  intro hB
  obtain ⟨B', hB'⟩ := Id2519.exists_isComponent_centralizer_of_mulEquiv e y hB
  have hyy : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by norm_num)
  refine hfree (e y) ?_ ?_ B' hB'
  · rw [← map_mul, hyy, map_one]
  · intro h
    exact hy1 (e.injective (by rw [h, map_one]))

theorem noA7Fix_j4 :
    NoA7Fix (NativeSporadic.Carrier .J4) := by
  have hsimple : IsSimpleGroup (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.isSimpleGroup_J4
  have : Finite (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.fam_j4_simplicity.1
  have hnc : ∃ a b : NativeSporadic.Carrier .J4, a * b ≠ b * a := by
    refine exists_noncomm_of_isSimpleGroup ?_
    change ¬ (Nat.card NativeSporadic.J4).Prime
    rw [CFSG.Sporadic.J4.card_J4]
    norm_num
  have hZ : Subgroup.center (NativeSporadic.Carrier .J4) = ⊥ :=
    Id2519.J4Row.center_eq_bot_of_simple hnc
  obtain ⟨e⟩ : Nonempty (NativeSporadic.Carrier .J4 ≃* ↥CFSG.Sporadic.J4.J) :=
    ⟨CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat⟩
  intro α hα2 hα1
  have hα2' : ∀ x, α (α x) = x := fun x => by
    have := congrArg (fun f : MulAut (NativeSporadic.Carrier .J4) => f x) hα2
    simpa using this
  obtain ⟨l, hl⟩ := Ch1.isInnerAut_of_outer_odd (MulEquiv.refl (NativeSporadic.Carrier .J4))
    (Setup.X1.j4OuterOdd : Ch1.J4OutOdd) α hα2'
  have hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (NativeSporadic.Carrier .J4) :=
    ⟨l⁻¹, MulEquiv.ext fun x => by rw [MulAut.conj_apply, inv_inv, hl]⟩
  exact not_hasA7Component_fix_of_inner hZ
    (forall_not_isComponent_of_equiv_sub CFSG.Sporadic.J4.J e
      fun r hsq hne => j4_involution_centralizer_component_free hsq hne) hα2 hα1 hin

end J

section HSRu

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem noA7Fix_hsP :
    NoA7Fix ↥hsP := by
  intro α hα2 hα1 hA
  obtain ⟨r, hr, g, hg, x, -, -, hFmap⟩ := Id2519.SporHS.fix_data α hα2 hα1
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨-, -, -, -, hrcard, -⟩ := hrows r hr
  have hFcard : Nat.card ↥(Id2519.fixSubgroup α) = r.centOrder := by
    rw [← Subgroup.card_map_of_injective hsP.subtype_injective, hFmap,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hrcard]
  rcases Id2519.SporHS.hsRows_cases hr with h0 | ⟨-, -, hord, -⟩ | ⟨hrep, -⟩ | h3
  · exact not_hasA7Component_of_not_dvd (by rw [hFcard, h0]; norm_num) hA
  · exact not_hasA7Component_of_not_dvd (by rw [hFcard, hord]; norm_num) hA
  · have hA' := hA.of_mulEquiv (Id2519.SporHS.fixEquiv hFmap)
    rw [hrep] at hA'
    have : IsSimpleGroup ↥(commutator ↥Id2519.HSAut.outerC) := Id2519.HSAut.commutator_simple'
    exact not_hasA7Component_of_commutator_simple (Q := ↥Id2519.HSAut.outerC)
      (by rw [Id2519.HSAut.card_commutator']; norm_num) hA'
  · exact not_hasA7Component_of_not_dvd (by rw [hFcard, h3]; norm_num) hA

theorem noA7Fix_hs :
    NoA7Fix NativeSporadic.HS :=
  NoA7Fix.of_mulEquiv hsPermEquiv.symm noA7Fix_hsP

theorem noA7Fix_ru :
    NoA7Fix (NativeSporadic.Carrier .Ru) := by
  refine NoA7Fix.of_mulEquiv Id2519.MathNoLayer.ruEquivCar.symm ?_
  intro α hα2 hα1 hA
  obtain ⟨g, hg⟩ := CFSG.Sporadic.RuSchreier.mulAut_inner α
  obtain ⟨y, hy, ⟨e⟩⟩ := Id2519.MathNoLayer.fix_of_inner CFSG.Sporadic.RuSchreier.ruP
    CFSG.Sporadic.RuSchreier.center_ruP α ⟨g, hg.symm⟩ hα2 hα1
  refine not_hasA7Component_of_not_dvd ?_ (hA.of_mulEquiv e)
  rw [centralizerIn]
  rcases Id2519.MathNoLayer.ru_centralizer_card y.2 hy with h | h <;> rw [h] <;> norm_num

end HSRu

end E6

end CFSG.Quasithin
