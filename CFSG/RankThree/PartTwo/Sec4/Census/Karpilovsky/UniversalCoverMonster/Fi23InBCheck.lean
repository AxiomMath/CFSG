module

public import Certificates.Certificate291200
public import CFSG.Sporadic.Bridge.Fi23Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
  CFSG.Sporadic.GLQ CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.Fi23GPL.Native

section Inst


abbrev SM : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2)) :=
  NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2

abbrev mA : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1

abbrev mB : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2

theorem fi23InB_check : mA * mA = 1 ∧ mB * mB * mB = 1 ∧
    ∀ x y : NativeSporadic.B, ((x : SM) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = mA →
      ((y : SM) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = mB →
      Fi23ImgFacts (runProg (initRegs x y) slp 1) (runProg (initRegs x y) slp 2) :=
  Certificates.certificate291200

theorem mA_sq : mA ^ 2 = 1 := by
  rw [pow_two]
  exact fi23InB_check.1

theorem mB_cube : mB ^ 3 = 1 := by
  rw [pow_three']
  exact fi23InB_check.2.1

theorem mA_mem : mA ∈ SM := Submonoid.subset_closure (Set.mem_insert _ _)

theorem mB_mem : mB ∈ SM := Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def gA : SMˣ := unitOf SM mA_mem two_ne_zero mA_sq

@[expose] noncomputable def gB : SMˣ := unitOf SM mB_mem three_ne_zero mB_cube

theorem gA_sq : gA ^ 2 = 1 := unitOf_pow SM _ _ _

theorem gB_cube : gB ^ 3 = 1 := unitOf_pow SM _ _ _

theorem φ_gA : valHom SM gA = mA := valHom_unitOf SM _ _ _

theorem φ_gB : valHom SM gB = mB := valHom_unitOf SM _ _ _

theorem φ_gA_inv : valHom SM gA⁻¹ = mA := by
  rw [valHom_inv_of_pow SM two_ne_zero gA_sq, φ_gA]
  simp

theorem φ_gB_inv : valHom SM gB⁻¹ = mB ^ 2 := by
  rw [valHom_inv_of_pow SM three_ne_zero gB_cube, φ_gB]

theorem rep_gA : Rep (spec2fr 4370) (valHom SM) gA
    ((ops2fr 4370).decode NativeSporadic.BSeed1, (ops2fr 4370).decode NativeSporadic.BSeed1) :=
  rep_of ((spec2fr 4370).decode_wf _) ((spec2fr 4370).decode_wf _)
    (by rw [(spec2fr 4370).toMat_decode, φ_gA]) (by rw [(spec2fr 4370).toMat_decode, φ_gA_inv])

theorem rep_gB : Rep (spec2fr 4370) (valHom SM) gB
    ((ops2fr 4370).decode NativeSporadic.BSeed2,
      (ops2fr 4370).pow ((ops2fr 4370).decode NativeSporadic.BSeed2) 2) :=
  rep_of ((spec2fr 4370).decode_wf _) ((spec2fr 4370).pow_spec ((spec2fr 4370).decode_wf _) 2).1
    (by rw [(spec2fr 4370).toMat_decode, φ_gB])
    (by rw [((spec2fr 4370).pow_spec ((spec2fr 4370).decode_wf _) 2).2,
      (spec2fr 4370).toMat_decode, φ_gB_inv])

@[expose] noncomputable def Rg : ℕ → SMˣ := runProg (initRegs gA gB) slp

theorem regsRep : RegsRep (spec2fr 4370) (valHom SM) nreg Rg regsN :=
  regsRep_runProg slp (by decide) (regsRep_initRegs rep_gA rep_gB)

@[expose] noncomputable def img (k : ℕ) : SMˣ := signedWord (Rg 1) (Rg 2) imgWords[k]!

theorem imgN_spec (k : ℕ) :
    (spec2fr 4370).WF (imgN k) ∧ (spec2fr 4370).toMat (imgN k) = valHom SM (img k) :=
  rep_signedWord (regsRep.2 1 (by decide)) (regsRep.2 2 (by decide)) imgWords[k]!

theorem imgsN_getElem {k : ℕ} (hk : k < 10) : imgsN[k]! = imgN k := by
  unfold imgsN
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem img_facts : Fi23ImgFacts (Rg 1) (Rg 2) := fi23InB_check.2.2 gA gB φ_gA φ_gB

theorem img_sq {k : ℕ} (hk : k < 10) : img k ^ 2 = 1 := img_facts.1 k hk

theorem img_inv {k : ℕ} (hk : k < 10) : (img k)⁻¹ = img k :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact img_sq hk)

theorem wordN_spec : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 10) →
    (spec2fr 4370).WF (wordN imgsN w) ∧
      (spec2fr 4370).toMat (wordN imgsN w) = valHom SM (wordProd img w)
  | [], _ => ⟨(spec2fr 4370).one_wf, by
      rw [wordN, List.foldr_nil, (spec2fr 4370).toMat_one]
      simp [wordProd]⟩
  | l :: w, h => by
    have hl : l.1 < 10 := h l List.mem_cons_self
    obtain ⟨hw, hw'⟩ := wordN_spec w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hi := imgN_spec l.1
    have e : wordN imgsN (l :: w) = (ops2fr 4370).mul imgsN[l.1]! (wordN imgsN w) := by
      simp only [wordN, List.foldr_cons]
    rw [e, imgsN_getElem hl]
    refine ⟨(spec2fr 4370).mul_wf hi.1 hw, ?_⟩
    rw [(spec2fr 4370).toMat_mul hi.1 hw, hi.2, hw']
    have : wordProd img (l :: w) = img l.1 * wordProd img w := by
      simp only [wordProd, List.map_cons, List.prod_cons]
      cases l.2 <;> simp [img_inv hl]
    rw [this, map_mul]

theorem relators_eval : ∀ v ∈ rels, wordProd img v = 1 := img_facts.2.1

theorem img_zero_ne_one : img 0 ≠ 1 := img_facts.2.2

theorem relators_eval' :
    ∀ v ∈ TauCeti.SporadicName.Fi23.presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  have hv' : v ∈ TauCeti.Sporadic.fi23Presentation.relatorLetters := hv
  rw [Fi23.relatorLetters_eq] at hv'
  exact relators_eval v hv'

@[expose] noncomputable def toB :
    TauCeti.SporadicName.Fi23.presentation.Group →* SMˣ :=
  presHom TauCeti.SporadicName.Fi23.presentation img relators_eval'

theorem exists_injective_of_simple {G H K : Type} [Group G] [Group H] [Group K] [IsSimpleGroup G]
    (e : G ≃* H) (φ : H →* K) (x : H) (hx : φ x ≠ 1) : ∃ f : G →* K, Function.Injective f := by
  refine ⟨φ.comp e.toMonoidHom, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.comp e.toMonoidHom).ker with
    h | h
  · exact h
  · exfalso
    have : e.symm x ∈ (φ.comp e.toMonoidHom).ker := by rw [h]; trivial
    simp at this
    exact hx this

theorem exists_injective_fi23_carrier_B :
    ∃ f : NativeSporadic.Carrier .Fi23 →* NativeSporadic.Carrier .B, Function.Injective f := by
  obtain ⟨e⟩ := Fi23.nonempty_mulEquiv
  have : IsSimpleGroup (NativeSporadic.Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  have hx : toB (presGen TauCeti.SporadicName.Fi23.presentation 0) ≠ 1 := by
    rw [toB, presHom_presGen _ _ _ (by rw [show TauCeti.SporadicName.Fi23.presentation =
      TauCeti.Sporadic.fi23Presentation from rfl, Fi23.generatorCount_eq]; omega)]
    exact img_zero_ne_one
  exact exists_injective_of_simple (G := NativeSporadic.Carrier .Fi23) (K := NativeSporadic.Carrier .B) e toB _ hx

end Inst

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB
