module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryField
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaith
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen (mapAut mem_mapAut)

section Core

variable {p f : ℕ} {K : Type} [Field K]

theorem closure_fix_eq_top_of_not_inner_unitary
    (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) {e : ℕ} (hfe : f = 3 * e)
    (hq2 : 2 < p ^ e) (B : Subgroup (MulAut (unitaryPSU h 3)))
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hB27 : Nat.card B = 27) {c : MulAut (unitaryPSU h 3)} (hcB : c ∈ B)
    (hc : ¬ IsInnerAut c) :
    ∃ F₀ : Subgroup (MulAut (unitaryPSU h 3)), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) = ⊤ := by
  classical
  have hQ2 : 2 < p ^ f := by
    rw [hfe, pow_mul']
    exact lt_of_lt_of_le hq2 (Nat.le_self_pow (by norm_num) _)
  have hcD : c ∉ (psuConj h).range :=
    not_mem_psuConj_range_of_E27 hQ hQ2 B hBab hB3 hB27 hcB hc
  obtain ⟨σ, hσ, H, hcH⟩ := unitary_order_three_field_descent hQ2 c (hB3 c hcB) hcD
  set cH : MulAut (unitaryPSU h 3) := psuConj h H with hcHdef
  set θ : MulAut (MulAut (unitaryPSU h 3)) := MulAut.conj cH⁻¹ with hθ
  set B' : Subgroup (MulAut (unitaryPSU h 3)) := B.map θ.toMonoidHom with hB'
  have hθinj : Function.Injective θ.toMonoidHom := θ.injective
  have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBab x hx y hy]
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB3 x hx, map_one]
  have hB'27 : Nat.card B' = 27 := by rw [hB', Subgroup.card_map_of_injective hθinj, hB27]
  have hσB' : psuField h σ ∈ B' := by
    refine ⟨c, hcB, ?_⟩
    change cH⁻¹ * c * cH⁻¹⁻¹ = psuField h σ
    rw [hcH, inv_inv]
    group
  obtain ⟨F₀', hF₀'B', hF₀'9, hgen⟩ := closure_fix_eq_top_field_unitary h hQ hfe hq2 hσ B'
    hB'ab hB'3 hB'27 hσB'
  set F₀ : Subgroup (MulAut (unitaryPSU h 3)) := F₀'.map θ.symm.toMonoidHom with hF₀
  have hF₀B : F₀ ≤ B := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨β, hβ, rfl⟩ := hF₀'B' hφ'
    change θ.symm (θ β) ∈ B
    rw [MulEquiv.symm_apply_apply]
    exact hβ
  have hF₀9 : Nat.card F₀ = 9 := by
    rw [hF₀, Subgroup.card_map_of_injective θ.symm.injective, hF₀'9]
  refine ⟨F₀, hF₀B, hF₀9, ?_⟩
  have himage : (cH : unitaryPSU h 3 →* unitaryPSU h 3) ''
      ({x | psuField h σ x = x} ∪ {x | ∀ φ ∈ F₀', φ x = x}) ⊆
      {x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x} := by
    rintro _ ⟨y, hy | hy, rfl⟩
    · left
      change c (cH y) = cH y
      rw [hcH]
      simp only [MulAut.mul_apply]
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      exact congrArg cH hy
    · right
      rintro _ ⟨φ', hφ', rfl⟩
      change (θ.symm φ') (cH y) = cH y
      rw [hθ, MulAut.conj_symm_apply, inv_inv]
      simp only [MulAut.mul_apply]
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      exact congrArg cH (hy φ' hφ')
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective (cH : unitaryPSU h 3 →* unitaryPSU h 3)
    cH.surjective, ← hgen, MonoidHom.map_closure]
  exact Subgroup.closure_mono himage

end Core

section Transport

variable {Y : Type*} [Group Y] {p f : ℕ} {K : Type} [Field K]

theorem closure_fix_eq_top_of_mulEquiv_unitary
    (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) {e : ℕ} (hfe : f = 3 * e)
    (hq2 : 2 < p ^ e) (ψ : Y ≃* unitaryPSU h 3) (B : Subgroup (MulAut Y))
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hB27 : Nat.card B = 27) {c : MulAut Y} (hcB : c ∈ B) (hc : ¬ IsInnerAut c) :
    ∃ F₀ : Subgroup (MulAut Y), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) = ⊤ := by
  set B' := mapAut ψ B with hB'
  have hinj : Function.Injective (MulAut.congr ψ).toMonoidHom := (MulAut.congr ψ).injective
  have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBab x hx y hy]
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB3 x hx, map_one]
  have hB'27 : Nat.card B' = 27 := by
    rw [hB', mapAut, Subgroup.card_map_of_injective hinj, hB27]
  have hcB' : MulAut.congr ψ c ∈ B' := ⟨c, hcB, rfl⟩
  have hc' : ¬ IsInnerAut (MulAut.congr ψ c) := fun hin => hc ((isInnerAut_congr ψ c).mp hin)
  obtain ⟨F₀', hF₀'B', hF₀'9, hgen⟩ := closure_fix_eq_top_of_not_inner_unitary h hQ hfe hq2 B'
    hB'ab hB'3 hB'27 hcB' hc'
  set F₀ : Subgroup (MulAut Y) := F₀'.map (MulAut.congr ψ.symm).toMonoidHom with hF₀
  have hF₀B : F₀ ≤ B := by
    rintro _ ⟨φ', hφ', rfl⟩
    exact mem_mapAut.1 (hF₀'B' hφ')
  have hF₀9 : Nat.card F₀ = 9 := by
    rw [hF₀, Subgroup.card_map_of_injective (MulAut.congr ψ.symm).injective, hF₀'9]
  refine ⟨F₀, hF₀B, hF₀9, ?_⟩
  have himage : (ψ.symm : unitaryPSU h 3 →* Y) ''
      ({x | MulAut.congr ψ c x = x} ∪ {x | ∀ φ ∈ F₀', φ x = x}) ⊆
      {x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x} := by
    rintro _ ⟨y, hy | hy, rfl⟩
    · left
      change c (ψ.symm y) = ψ.symm y
      rw [Set.mem_ofPred_eq, CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.congr_apply'] at hy
      have h1 := congrArg ψ.symm hy
      rwa [MulEquiv.symm_apply_apply] at h1
    · right
      rintro _ ⟨φ', hφ', rfl⟩
      change MulAut.congr ψ.symm φ' (ψ.symm y) = ψ.symm y
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.congr_apply', MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply, hy φ' hφ']
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective (ψ.symm : unitaryPSU h 3 →* Y)
    ψ.symm.surjective, ← hgen, MonoidHom.map_closure]
  exact Subgroup.closure_mono himage

end Transport

end Item19Res6Proof

open Item19Res4Proof Item19Res5Proof Item19Res6Proof CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts in
theorem ks1917XGenFaithfulUnitary_holds :
    KS1917XGenFaithfulUnitary := by
  intro G _ _ X E c hXp hXq hEX hEab hE27 hcE hfaith htype
  obtain ⟨p, e, hpF, he, hq2, hQ, ⟨ι⟩, hind⟩ := htype
  classical
  have hp : p.Prime := hpF.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := GaloisField p (2 * (3 * e)) with hKdef
  have h : UnitaryFieldData p (3 * e) K := ⟨hp, by omega, GaloisField.card p _ (by omega)⟩
  obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  set ψ : (X ⧸ CFSG.pCore 2 X) ≃* unitaryPSU h 3 := ι.trans φ.symm with hψ
  set ρ := Step1910Proof.quotAct hEX with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := (quotAct_eq_one_iff hEX a).mp ha
    have h2 := hfaith a a.2 (fun x hx => (commutator_mem_pCoreOf_iff hx).mpr (h1 x hx))
    exact Subtype.ext h2
  have hR := isElemAbelian_range_quotAct hEX hEab
  have hRab : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hR27 : Nat.card ρ.range = 27 := by
    rw [← hE27]
    exact Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
  have hout : Sec4.InducesOuterTheta c X :=
    KFacts.InducesStdKind.inducesOuterTheta X hind (by decide)
  have hcout := quotAct_not_mem_range_conj hEX hcE hout
  obtain ⟨F₀, hF₀R, hF₀9, hgen⟩ := closure_fix_eq_top_of_mulEquiv_unitary h hQ rfl hq2 ψ ρ.range
    hRab hR.2 hR27 (c := ρ ⟨c, hcE⟩) ⟨_, rfl⟩ hcout
  set FE : Subgroup E := F₀.comap ρ with hFE
  set F : Subgroup G := FE.map E.subtype with hF
  have hFEle : F ≤ E := Subgroup.map_subtype_le FE
  have hFE9 : Nat.card FE = 9 := by
    have h1 : FE.map ρ = F₀ := by
      rw [hFE, Subgroup.map_comap_eq, inf_eq_right.2 hF₀R]
    rw [← hF₀9, ← h1, Subgroup.card_map_of_injective hρinj]
  have hF9 : Nat.card F = 9 := by
    rw [hF, Subgroup.card_map_of_injective E.subtype_injective, hFE9]
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  have hgen' : Subgroup.closure ({y | ρ ⟨c, hcE⟩ y = y} ∪
      {y | ∀ b : E, (b : G) ∈ F → ρ b y = y}) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_mono ?_
    rintro y (hy | hy)
    · exact Or.inl hy
    · refine Or.inr fun b hb => ?_
      obtain ⟨b', hb', hbb'⟩ := hb
      have : b' = b := Subtype.ext hbb'
      subst this
      exact hy _ hb'
  have hle := le_sup_of_closure_fix_eq_top hEX hE3 hcE hFEle hgen'
  refine hle.trans (sup_le_sup_right (sup_le_sup_left ?_ _) _)
  exact le_iSup_of_le (⟨F, hFEle, hF9⟩ : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9}) le_rfl

end CFSG.RankThree.PartTwo.Sec19
