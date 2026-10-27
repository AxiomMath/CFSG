module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L3Facts
import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.GroupTheory.WeirSylow.UnitaryBridge
import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUModel
import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.GH74.GLS.IVK.L2.Fixed

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.Open
open CFSG.GH74.GLS.IVK.Proofs2 (uniU₀)
open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open CFSG.ClassicalInvolution.Models (rootSU2 rootInvSU suMat isClassicalSL2_rootSU2)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.RankThree.CentralCover (oddDiag₃ statedProjMk)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (suEquivUnitarySU coe_suEquivUnitarySU
  isPerfect_and_center_unitarySU)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (psu3_std suMat_rootInvSU_three)

variable {F : Type} [Field F] [Finite F] {q : ℕ}

section FieldPart

variable {p f : ℕ} {h : UnitaryFieldData p f F}

omit [Finite F] in
private theorem eq_of_psuConj_mul_psuField_eq (A B : unitaryIsom3 h) (σ τ : RingAut F)
    (heq : psuConj h A * psuField h σ = psuConj h B * psuField h τ) : σ = τ := by
  have h2 : (psuConj h B)⁻¹ * (psuConj h A * psuField h σ) * (psuField h τ)⁻¹ = 1 := by
    rw [heq]
    group
  have h3 : psuConj h (B⁻¹ * A) * psuField h (σ * τ⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv]
    simpa only [mul_assoc] using h2
  have h4 : σ * τ⁻¹ = 1 := (eq_one_of_psuConj_mul_psuField_eq_one (B⁻¹ * A) (σ * τ⁻¹) h3).1
  exact mul_inv_eq_one.mp h4

private noncomputable def psuDecomp (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3)) :
    unitaryIsom3 h × RingAut F :=
  ⟨Classical.choose (exists_psuConj_mul_psuField hq α),
    Classical.choose (Classical.choose_spec (exists_psuConj_mul_psuField hq α))⟩

omit [Finite F] in
private theorem psuDecomp_spec (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3)) :
    α = psuConj h (psuDecomp hq α).1 * psuField h (psuDecomp hq α).2 :=
  Classical.choose_spec (Classical.choose_spec (exists_psuConj_mul_psuField hq α))

private noncomputable def psuFieldPart (hq : 2 < p ^ f) :
    MulAut (unitaryPSU h 3) →* RingAut F where
  toFun α := (psuDecomp hq α).2
  map_one' := by
    have h1 : psuConj h (psuDecomp hq 1).1 * psuField h (psuDecomp hq 1).2 = 1 :=
      (psuDecomp_spec hq 1).symm
    exact (eq_one_of_psuConj_mul_psuField_eq_one _ _ h1).1
  map_mul' α β := by
    have hα := psuDecomp_spec hq α
    have hβ := psuDecomp_spec hq β
    have hαβ := psuDecomp_spec hq (α * β)
    have h1 : α * β = psuConj h ((psuDecomp hq α).1 *
        ⟨glAut (psuDecomp hq α).2 (psuDecomp hq β).1,
          glAut_mem_unitaryIsom3 _ (psuDecomp hq β).1.2⟩) *
          psuField h ((psuDecomp hq α).2 * (psuDecomp hq β).2) := by
      conv_lhs => rw [hα, hβ]
      rw [psuConj_mul_psuField_mul]
    exact eq_of_psuConj_mul_psuField_eq _ _ _ _ (hαβ.symm.trans h1)

omit [Finite F] in
private theorem psuFieldPart_eq_one_of (hq : 2 < p ^ f) {α : MulAut (unitaryPSU h 3)}
    {A : unitaryIsom3 h} (hα : α = psuConj h A) : psuFieldPart (h := h) hq α = 1 := by
  have hspec := psuDecomp_spec hq α
  have heq : psuConj h (psuDecomp hq α).1 * psuField h (psuDecomp hq α).2 =
      psuConj h A * psuField h 1 := by
    rw [← hspec, hα, map_one, mul_one]
  exact eq_of_psuConj_mul_psuField_eq _ _ _ _ heq

omit [Finite F] in
private theorem psuFieldPart_psuConj (hq : 2 < p ^ f) (A : unitaryIsom3 h) :
    psuFieldPart (h := h) hq (psuConj h A) = 1 :=
  psuFieldPart_eq_one_of hq rfl

omit [Finite F] in
private theorem psuFieldPart_eq_one_iff (hq : 2 < p ^ f) {α : MulAut (unitaryPSU h 3)} :
    psuFieldPart (h := h) hq α = 1 ↔ α ∈ (psuConj h).range := by
  constructor
  · intro hα
    have hα' : (psuDecomp hq α).2 = 1 := hα
    refine ⟨(psuDecomp hq α).1, ?_⟩
    conv_rhs => rw [psuDecomp_spec hq α]
    rw [hα', map_one, mul_one]
  · rintro ⟨A, rfl⟩
    exact psuFieldPart_psuConj hq A

private theorem exists_inner_of_four (hq : 2 < p ^ f) (B : Subgroup (MulAut (unitaryPSU h 3)))
    (hB : Nat.card B = 4) (hB2 : ∀ β ∈ B, β * β = 1) :
    ∃ β ∈ B, β ≠ 1 ∧ β ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  classical
  have : IsCyclic (RingAut F) := (card_ringAut_and_isCyclic h.prime F h.card).2
  let g : B →* RingAut F := (psuFieldPart (h := h) hq).comp B.subtype
  have hsq : ∀ x : B, g x * g x = 1 := by
    intro x
    have hx' : x * x = 1 := Subtype.ext (by simpa [Subgroup.coe_mul] using hB2 x x.2)
    calc g x * g x = g (x * x) := (map_mul g x x).symm
      _ = 1 := by rw [hx', map_one]
  have hrange : Nat.card g.range ≤ 2 := by
    obtain ⟨σ, hσ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top g.range).mp
      (Subgroup.isCyclic g.range)
    have hσ2 : σ * σ = 1 := by
      have hmem : σ ∈ g.range := by rw [← hσ]; exact Subgroup.mem_zpowers σ
      obtain ⟨x, rfl⟩ := hmem
      exact hsq x
    have hord : orderOf σ ≤ 2 := by
      have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
      exact Nat.le_of_dvd (by norm_num) hdvd
    rw [← hσ, Nat.card_zpowers]
    exact hord
  have hker : 2 ≤ Nat.card g.ker := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hB] at h
    have hpos : 0 < Nat.card g.range := Nat.card_pos
    nlinarith
  have : Fintype ↥g.ker := Fintype.ofFinite _
  have hker2 : 1 < Fintype.card ↥g.ker := by rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨x, hx1⟩ := Fintype.exists_ne_of_one_lt_card hker2 (1 : ↥g.ker)
  have hxmem : ((x : B) : MulAut (unitaryPSU h 3)) ∈ B := (x : B).2
  have hx2 : ((x : B) : MulAut (unitaryPSU h 3)) * (x : B) = 1 :=
    hB2 (x : B) (x : B).2
  have hfp : psuFieldPart (h := h) hq ((x : B) : MulAut (unitaryPSU h 3)) = 1 := x.2
  refine ⟨((x : B) : MulAut (unitaryPSU h 3)), hxmem, ?_, ?_⟩
  · intro hxone
    exact hx1 (Subtype.ext (Subtype.ext hxone))
  · have hrange' : ((x : B) : MulAut (unitaryPSU h 3)) ∈ (psuConj h).range :=
      (psuFieldPart_eq_one_iff (h := h) hq).mp hfp
    have hcube := cube_mem_range_conj_of_mem_psuConj_range hrange'
    simpa only [pow_three, hx2, one_mul, mul_one] using hcube

end FieldPart

theorem psu3_inner (hq : Odd q) (hq3 : 3 < q) (hF : Nat.card F = q ^ 2)
    (B : Subgroup (MulAut (StatedProj (StatedSU 3 q F)))) (hB : Nat.card B = 4)
    (hB2 : ∀ β ∈ B, β * β = 1) :
    ∃ β ∈ B, β ≠ 1 ∧ β ∈ (MulAut.conj :
      StatedProj (StatedSU 3 q F) →* MulAut (StatedProj (StatedSU 3 q F))).range := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hqf, h⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData F (q := q)
    (by rwa [← Nat.card_eq_fintype_card])
  subst hqf
  have hq2 : 2 < ringChar F ^ f := by linarith
  let e := unitaryPSUEquiv h (by norm_num : 1 ≤ 3)
  set B' : Subgroup (MulAut (unitaryPSU h 3)) :=
    B.comap (MulAut.congr e).toMonoidHom with hB'def
  have hB'card : Nat.card B' = 4 := by
    have hmap : B'.map (MulAut.congr e).toMonoidHom = B := by
      rw [hB'def, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr (MulAut.congr e).surjective, top_inf_eq]
    have h1 : Nat.card (B'.map (MulAut.congr e).toMonoidHom) = Nat.card B' :=
      Subgroup.card_map_of_injective (MulAut.congr e).injective
    rw [← h1, hmap, hB]
  have hB'2 : ∀ β ∈ B', β * β = 1 := by
    intro β hβ
    have hβ' : MulAut.congr e β ∈ B := hβ
    have h2 : MulAut.congr e (β * β) = MulAut.congr e 1 := by
      rw [map_mul, hB2 _ hβ', map_one]
    exact (MulAut.congr e).injective h2
  obtain ⟨β, hβB, hβ1, hβinner⟩ := exists_inner_of_four (h := h) hq2 B' hB'card hB'2
  refine ⟨MulAut.congr e β, hβB, ?_, ?_⟩
  · intro h
    apply hβ1
    have h' : MulAut.congr e β = MulAut.congr e 1 := by rw [h, map_one]
    exact (MulAut.congr e).injective h'
  · obtain ⟨x, rfl⟩ := hβinner
    rw [congr_mulAutConj]
    exact ⟨e x, rfl⟩

theorem psu3_cent (hq : Odd q) (hq5 : 5 ≤ q) (hF : Nat.card F = q ^ 2)
    (β : MulAut (StatedProj (StatedSU 3 q F))) (h2 : β * β = 1) (ht : β (uniU₀ F hq) = uniU₀ F hq)
    (hK : ∀ k ∈ derivedCent (uniU₀ F hq), β k = k) : β = 1 ∨ β = MulAut.conj (uniU₀ F hq) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hqf, h⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData F (q := q)
    (by rwa [← Nat.card_eq_fintype_card])
  subst hqf
  have : Fact (ringChar F).Prime := ⟨h.prime⟩
  have : CharP F (ringChar F) := h.charP
  have hq2 : 2 < ringChar F ^ f := by linarith
  have hp2 : ringChar F ≠ 2 := by
    intro hp
    have hq' : Odd (2 ^ f) := by simpa [hp] using hq
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, (Nat.sub_add_cancel h.one_le).symm⟩
    have heven : Even (2 ^ (g + 1)) := by
      rw [pow_succ]
      exact ⟨2 ^ g, by ring⟩
    obtain ⟨k, hk⟩ := hq'
    obtain ⟨j, hj⟩ := heven
    omega
  have hKcard : Nat.card F = (ringChar F ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  have hSU := isPerfect_and_center_unitarySU h hq5 (d := 3) (by norm_num)
  have : Group.IsPerfect ↥(unitarySU (ringChar F) f F 3) := hSU.1
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ := by
    have hZeq : unitaryScalars h 3 = Subgroup.center (unitarySU (ringChar F) f F 3) := hSU.2.symm
    let ee : unitaryPSU h 3 ≃*
        (unitarySU (ringChar F) f F 3 ⧸ Subgroup.center (unitarySU (ringChar F) f F 3)) :=
      QuotientGroup.quotientMulEquivOfEq hZeq
    have h1 := Group.IsPerfect.center_quotient_center_eq_bot (unitarySU (ringChar F) f F 3)
    have h2 : (Subgroup.center (unitaryPSU h 3)).map ee.toMonoidHom ≤ ⊥ := by
      rw [← h1]
      exact Subgroup.map_center_le_center ee.surjective
    have h3 : (Subgroup.center (unitaryPSU h 3)).map ee.toMonoidHom = ⊥ :=
      le_antisymm h2 bot_le
    rw [Subgroup.map_eq_bot_iff] at h3
    have hker : ee.toMonoidHom.ker = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have hz1 : ee z = 1 := MonoidHom.mem_ker.mp hz
      exact ee.injective (by rw [hz1, map_one])
    rw [hker] at h3
    rwa [eq_bot_iff]
  let e := unitaryPSUEquiv h (by norm_num : 1 ≤ 3)
  let β' : MulAut (unitaryPSU h 3) := (MulAut.congr e).symm β
  have hβ : MulAut.congr e β' = β := (MulAut.congr e).apply_symm_apply β
  have hcongr : ∀ (γ : MulAut (unitaryPSU h 3)) (x : unitaryPSU h 3),
      MulAut.congr e γ (e x) = e (γ x) := by
    intro γ x
    simp [MulAut.congr_apply]
  have hmulconj : ∀ (α : MulAut (unitaryPSU h 3)) (y : unitaryPSU h 3),
      α * MulAut.conj y = MulAut.conj (α y) * α := by
    intro α y
    rw [← mul_mulAutConj_mul_inv α y]
    group
  have hmulconj' : ∀ (α : MulAut (unitaryPSU h 3)) (y : unitaryPSU h 3),
      MulAut.conj (α y) = α * MulAut.conj y * α⁻¹ := fun α y =>
    (mul_mulAutConj_mul_inv α y).symm
  have h2' : β' * β' = 1 := by
    apply (MulAut.congr e).injective
    rw [map_mul, hβ, h2, map_one]
  let x₀ : Su F (ringChar F) f 3 := rootInvSU F (ringChar F) f (show 2 ≤ 3 by norm_num)
  let tS : unitarySU (ringChar F) f F 3 := suEquivUnitarySU F (ringChar F) f hKcard 3 x₀
  let t : unitaryPSU h 3 := unitaryProj h 3 tS
  have htS_coe : ((tS : unitarySU (ringChar F) f F 3) : GL (Fin 3) F) = oddDiag₃ F := by
    change ((suEquivUnitarySU F (ringChar F) f hKcard 3 x₀ :
      unitarySU (ringChar F) f F 3) : GL (Fin 3) F) = oddDiag₃ F
    rw [coe_suEquivUnitarySU]
    apply Units.ext
    rw [show ((x₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] from suMat_rootInvSU_three]
    rfl
  have ht_eq : e t = uniU₀ F hq := by
    have h1 := unitaryPSUEquiv_unitaryProj h (by norm_num : 1 ≤ 3) tS
    rw [show e t = (QuotientGroup.mk tS : StatedProj _) from h1]
    unfold uniU₀ statedProjMk
    congr 1
    exact Subtype.ext htS_coe
  have ht' : β' t = t := by
    apply e.injective
    calc e (β' t) = MulAut.congr e β' (e t) := (hcongr β' t).symm
      _ = β (e t) := by rw [hβ]
      _ = β (uniU₀ F hq) := by rw [ht_eq]
      _ = uniU₀ F hq := ht
      _ = e t := ht_eq.symm
  have hmap_le : (derivedCent t).map e.toMonoidHom ≤ derivedCent (uniU₀ F hq) := by
    rw [← ht_eq]
    have hcen_le : (Subgroup.centralizer ({t} : Set (unitaryPSU h 3))).map e.toMonoidHom ≤
        Subgroup.centralizer ({e t} : Set _) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      show e x * e t = e t * e x
      rw [← map_mul, ← map_mul, hx']
    calc (derivedCent t).map e.toMonoidHom
        = ⁅(Subgroup.centralizer ({t} : Set (unitaryPSU h 3))).map e.toMonoidHom,
            (Subgroup.centralizer ({t} : Set (unitaryPSU h 3))).map e.toMonoidHom⁆ := by
          rw [derivedCent, Subgroup.map_commutator]
      _ ≤ ⁅Subgroup.centralizer ({e t} : Set _), Subgroup.centralizer ({e t} : Set _)⁆ :=
          Subgroup.commutator_mono hcen_le hcen_le
      _ = derivedCent (e t) := rfl
  have hK' : ∀ k ∈ derivedCent t, β' k = k := by
    intro k hk
    have hk' : e k ∈ derivedCent (uniU₀ F hq) := hmap_le ⟨k, hk, rfl⟩
    have hfix := hK (e k) hk'
    have h1 : e (β' k) = e k := by
      rw [← hcongr β' k, hβ]
      exact hfix
    exact e.injective h1
  have hcl := isClassicalSL2_rootSU2 (K := F) (p := ringChar F) (f := f) hKcard hp2
    (show 2 ≤ 3 by norm_num)
  have h4F : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield F (ringChar F) f) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hKcard]
    omega
  have hperf_root : Group.IsPerfect ↥(rootSU2 F (ringChar F) f (show 2 ≤ 3 by norm_num)) :=
    hcl.isPerfect h4F
  let θS : Su F (ringChar F) f 3 →* unitaryPSU h 3 :=
    (unitaryProj h 3).comp (suEquivUnitarySU F (ringChar F) f hKcard 3).toMonoidHom
  have htS_def : θS (rootInvSU F (ringChar F) f (show 2 ≤ 3 by norm_num)) = t := rfl
  have hroot_le : (rootSU2 F (ringChar F) f (show 2 ≤ 3 by norm_num)).map θS ≤
      derivedCent t := by
    have hle_cent : rootSU2 F (ringChar F) f (show 2 ≤ 3 by norm_num) ≤
        Subgroup.centralizer ({rootInvSU F (ringChar F) f (show 2 ≤ 3 by norm_num)} :
          Set (Su F (ringChar F) f 3)) :=
      hcl.le_centralizer
    have hperf_img : Group.IsPerfect
        ↥((rootSU2 F (ringChar F) f (show 2 ≤ 3 by norm_num)).map θS) :=
      Group.IsPerfect.map θS
    have hle : (rootSU2 F (ringChar F) f (show 2 ≤ 3 by norm_num)).map θS ≤
        Subgroup.centralizer ({t} : Set (unitaryPSU h 3)) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : r * rootInvSU F (ringChar F) f (show 2 ≤ 3 by norm_num) =
          rootInvSU F (ringChar F) f (show 2 ≤ 3 by norm_num) * r :=
        Subgroup.mem_centralizer_singleton_iff.mp (hle_cent hr)
      show θS r * t = t * θS r
      rw [← htS_def, ← map_mul, ← map_mul, hcomm]
    have hcomm := Subgroup.commutator_mono hle hle
    rwa [Subgroup.commutator_eq_self] at hcomm
  let θ : Su F (ringChar F) f 3 →* MulAut (unitaryPSU h 3) := MulAut.conj.comp θS
  have hθrange : θ.range = (MulAut.conj :
      unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
    have hsurj : Function.Surjective θS :=
      (unitaryProj_surjective h 3).comp (suEquivUnitarySU F (ringChar F) f hKcard 3).surjective
    show (MulAut.conj.comp θS).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top]
  have hker : θ.ker ≤ Subgroup.center (Su F (ringChar F) f 3) := by
    intro s hs
    have hconj : MulAut.conj
        (unitaryProj h 3 (suEquivUnitarySU F (ringChar F) f hKcard 3 s)) = 1 := hs
    have hx1 : unitaryProj h 3 (suEquivUnitarySU F (ringChar F) f hKcard 3 s) = 1 :=
      CFSG.mulAutConj_injective_of_center_eq_bot hZ (by simpa using hconj)
    have hmem : suEquivUnitarySU F (ringChar F) f hKcard 3 s ∈
        Subgroup.center (unitarySU (ringChar F) f F 3) := by
      rw [hSU.2, ← ker_unitaryProj h 3, MonoidHom.mem_ker]
      exact hx1
    rw [Subgroup.mem_center_iff] at hmem ⊢
    intro y
    apply (suEquivUnitarySU F (ringChar F) f hKcard 3).injective
    rw [map_mul, map_mul]
    exact hmem _
  have hw : β' ∈ Subgroup.normalizer (θ.range : Set (MulAut (unitaryPSU h 3))) := by
    rw [hθrange, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨β' y, hmulconj' β' y⟩
    · rintro ⟨y, hy⟩
      refine ⟨β'⁻¹ y, ?_⟩
      calc MulAut.conj (β'⁻¹ y) = β'⁻¹ * MulAut.conj y * β' := hmulconj' β'⁻¹ y
        _ = β'⁻¹ * (β' * x * β'⁻¹) * β' := by rw [hy]
        _ = x := by group
  have hwR : ∀ r ∈ rootSU2 F (ringChar F) f (show 2 ≤ 3 by norm_num), β' * θ r = θ r * β' := by
    intro r hr
    have hxmem : θS r ∈ derivedCent t := hroot_le ⟨r, hr, rfl⟩
    have hfix : β' (θS r) = θS r := hK' _ hxmem
    show β' * MulAut.conj (θS r) = MulAut.conj (θS r) * β'
    rw [hmulconj, hfix]
  have hstd := psu3_std hKcard hp2 hq5 θ hker hw h2' hwR
  have hθroot : θ (rootInvSU F (ringChar F) f (show 2 ≤ 3 by norm_num)) = MulAut.conj t := rfl
  have ht2 : t * t = 1 := by
    have hx2 : x₀ * x₀ = 1 := by
      have h2 : x₀ ^ 2 = 1 := by
        rw [← hcl.orderOf_eq_two]
        exact pow_orderOf_eq_one x₀
      rwa [pow_two] at h2
    have htS2 : tS * tS = 1 := by
      rw [show tS = suEquivUnitarySU F (ringChar F) f hKcard 3 x₀ from rfl, ← map_mul, hx2, map_one]
    rw [show t = unitaryProj h 3 tS from rfl, ← map_mul, htS2, map_one]
  have hcen_eq_one : ∀ γ : MulAut (unitaryPSU h 3),
      (∀ y ∈ θ.range, γ * y = y * γ) → γ = 1 := by
    intro γ hγ
    ext x
    have hcx : MulAut.conj x ∈ θ.range := by
      rw [hθrange]
      exact ⟨x, rfl⟩
    have h1 := hγ _ hcx
    have h2 : MulAut.conj (γ x) = MulAut.conj x := by
      rw [hmulconj' γ x]
      calc γ * MulAut.conj x * γ⁻¹ = (MulAut.conj x * γ) * γ⁻¹ := by rw [h1]
        _ = MulAut.conj x := by rw [mul_assoc, mul_inv_cancel, mul_one]
    exact CFSG.mulAutConj_injective_of_center_eq_bot hZ h2
  rcases hstd with hcen | hcen
  · left
    have hβ'1 : β' = 1 := hcen_eq_one β' hcen
    rw [show β = MulAut.congr e β' from hβ.symm, hβ'1, map_one]
  · right
    have hc2 : MulAut.conj t * MulAut.conj t = 1 := by
      rw [← map_mul, ht2, map_one]
    have hγ1 : β' * MulAut.conj t = 1 := by
      refine hcen_eq_one (β' * MulAut.conj t) ?_
      simpa [hθroot] using hcen
    have hβ'conj : β' = MulAut.conj t := by
      calc β' = β' * (MulAut.conj t * MulAut.conj t) := by rw [hc2, mul_one]
        _ = (β' * MulAut.conj t) * MulAut.conj t := by group
        _ = MulAut.conj t := by rw [hγ1, one_mul]
    rw [show β = MulAut.congr e β' from hβ.symm, hβ'conj, congr_mulAutConj e t, ht_eq]


end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
