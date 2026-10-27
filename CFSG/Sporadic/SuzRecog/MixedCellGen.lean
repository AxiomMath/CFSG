module

public import CFSG.Sporadic.SuzRecog.MixedCellModel
public import CFSG.Sporadic.SuzRecog.GluingProof2
public import CFSG.Sporadic.SuzRecog.LevelTwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Monster.Code.Weights
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.Sporadic.SuzRecog.MixedCell

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.CosetEnumeration CFSG.Sporadic.SuzRecog.MixedCellData
  CFSG.Sporadic.SuzRecog.MixedCellCheck

local notation "Pm" => Equiv.Perm (Fin 1782)

theorem evalWord_mem_of {H : Type*} [Group H] (S : Subgroup H) (g : ℕ → H) {w : List ℕ}
    (h : ∀ c ∈ w, g c ∈ S) : evalWord g w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons c w ih =>
    rw [evalWord_cons]
    exact S.mul_mem (h c List.mem_cons_self) (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem evalWord_chart {G : Type*} [Group G] {H : Subgroup Pm} (f : ↥H →* G) (gen : ℕ → G)
    {w : List ℕ} (hgen : ∀ c ∈ w, ∃ h : genM c ∈ H, gen c = f ⟨genM c, h⟩)
    (h : evalWord genM w ∈ H) : evalWord gen w = f ⟨evalWord genM w, h⟩ := by
  induction w with
  | nil =>
    rw [evalWord_nil]
    exact (map_one f).symm
  | cons c w ih =>
    obtain ⟨hc, e⟩ := hgen c List.mem_cons_self
    have hw : evalWord genM w ∈ H :=
      evalWord_mem_of H genM fun c' hc' => (hgen c' (List.mem_cons_of_mem _ hc')).1
    rw [evalWord_cons, e, ih (fun c' hc' => hgen c' (List.mem_cons_of_mem _ hc')) hw, ← map_mul]
    congr 1

section Letters

theorem sP_mem_centM : sP ∈ centM wP := by
  have hX : LevelTwo.sX ∈ LevelTwo.Xe := (LevelTwo.mem_Xe _).2 (Or.inr LevelTwo.sX_spec)
  have := LevelTwo.mem_centM_of_mem_Xe hX
  rwa [coe_sX] at this

variable {G : Type} [Group G] {M : Subgroup G}

@[expose] noncomputable def sig (σ : M ≃* invE 1) : ↥(invE 1) →* G :=
  M.subtype.comp σ.symm.toMonoidHom

theorem sig_apply (σ : M ≃* invE 1) (c : ↥(invE 1)) : sig σ c = (σ.symm c : G) := rfl

@[expose] noncomputable def gLet (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) : ℕ → G
  | 0 => sig σ ⟨h1, h1_mem.1⟩
  | 1 => sig σ ⟨h2, h2_mem.1⟩
  | 2 => ψ ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩
  | 3 => ψ ⟨ja, ja_mem.2⟩
  | 4 => ψ ⟨jb, jb_mem.2⟩
  | 5 => ζ ⟨sP, sP_mem_centM⟩
  | _ => 1

@[expose] noncomputable def gGen (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G)
    (c : ℕ) : G :=
  if c % 2 = 0 then gLet σ ψ ζ (c / 2) else (gLet σ ψ ζ (c / 2))⁻¹

theorem gGen_inv (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) :
    ∀ i < 6, gGen σ ψ ζ (2 * i + 1) = (gGen σ ψ ζ (2 * i))⁻¹ := by
  intro i _
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  have h3 : (2 * i) % 2 = 0 := by omega
  have h4 : (2 * i) / 2 = i := by omega
  simp only [gGen, h1, h2, h3, h4]
  rfl

theorem gGen_even (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) (i : ℕ) :
    gGen σ ψ ζ (2 * i) = gLet σ ψ ζ i := by
  simp [gGen]

theorem gGen_odd (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) (i : ℕ) :
    gGen σ ψ ζ (2 * i + 1) = (gLet σ ψ ζ i)⁻¹ := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [gGen, h1, h2]

theorem gGen_sig {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} (ζ : centM wP →* G) (hB : B0Agree σ ψ)
    {c : ℕ} (hc : c < 6) : ∃ h : genM c ∈ invE 1, gGen σ ψ ζ c = sig σ ⟨genM c, h⟩ := by
  refine ⟨genM_mem_invE c (Or.inl hc), ?_⟩
  have hρ : ψ ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩ = sig σ ⟨Model.rho1, C1Model.rho1_mem_invE⟩ :=
    hB _ C1Model.rho1_mem_invE ModelGroups.rho1_mem_NR0
  obtain ⟨i, rfl | rfl⟩ : ∃ i, c = 2 * i ∨ c = 2 * i + 1 := ⟨c / 2, by omega⟩
  · rw [gGen_even]
    have hi : i < 3 := by omega
    interval_cases i
    · rfl
    · rfl
    · exact hρ
  · rw [gGen_odd]
    have hi : i < 3 := by omega
    interval_cases i
    · show (sig σ ⟨h1, h1_mem.1⟩)⁻¹ = _
      rw [← map_inv]; rfl
    · show (sig σ ⟨h2, h2_mem.1⟩)⁻¹ = _
      rw [← map_inv]; rfl
    · show (ψ ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩)⁻¹ = _
      rw [hρ, ← map_inv]; rfl

theorem gGen_psi (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) {c : ℕ}
    (hc : 4 ≤ c ∧ c < 10) : ∃ h : genM c ∈ Model.NR0, gGen σ ψ ζ c = ψ ⟨genM c, h⟩ := by
  refine ⟨genM_mem_NR0 c hc.1 hc.2, ?_⟩
  obtain ⟨i, rfl | rfl⟩ : ∃ i, c = 2 * i ∨ c = 2 * i + 1 := ⟨c / 2, by omega⟩
  · rw [gGen_even]
    have hi : 2 ≤ i ∧ i < 5 := by omega
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i
    · rfl
    · rfl
    · rfl
  · rw [gGen_odd]
    have hi : 2 ≤ i ∧ i < 5 := by omega
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i
    · show (ψ ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩)⁻¹ = _
      rw [← map_inv]; rfl
    · show (ψ ⟨ja, ja_mem.2⟩)⁻¹ = _
      rw [← map_inv]; rfl
    · show (ψ ⟨jb, jb_mem.2⟩)⁻¹ = _
      rw [← map_inv]; rfl

theorem gGen_ten (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) :
    gGen σ ψ ζ 10 = ζ ⟨sP, sP_mem_centM⟩ := by
  rw [show (10 : ℕ) = 2 * 5 by rfl, gGen_even]
  rfl

theorem gGen_eleven (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) :
    gGen σ ψ ζ 11 = (ζ ⟨sP, sP_mem_centM⟩)⁻¹ := by
  rw [show (11 : ℕ) = 2 * 5 + 1 by rfl, gGen_odd]
  rfl

end Letters

section Words

variable {G : Type} [Group G] {M : Subgroup G}

theorem sigWord_mem {w : List ℕ} (hw : ∀ c ∈ w, c < 6) : evalWord genM w ∈ invE 1 :=
  evalWord_mem_of _ _ fun c hc => genM_mem_invE c (Or.inl (hw c hc))

theorem psiWord_mem {w : List ℕ} (hw : ∀ c ∈ w, 4 ≤ c ∧ c < 10) : evalWord genM w ∈ Model.NR0 :=
  evalWord_mem_of _ _ fun c hc => genM_mem_NR0 c (hw c hc).1 (hw c hc).2

theorem evalWord_sig {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} (ζ : centM wP →* G)
    (hB : B0Agree σ ψ) {w : List ℕ} (hw : ∀ c ∈ w, c < 6) (h : evalWord genM w ∈ invE 1) :
    evalWord (gGen σ ψ ζ) w = sig σ ⟨evalWord genM w, h⟩ :=
  evalWord_chart (sig σ) _ (fun c hc => gGen_sig ζ hB (hw c hc)) h

theorem evalWord_psi (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM wP →* G) {w : List ℕ}
    (hw : ∀ c ∈ w, 4 ≤ c ∧ c < 10) (h : evalWord genM w ∈ Model.NR0) :
    evalWord (gGen σ ψ ζ) w = ψ ⟨evalWord genM w, h⟩ :=
  evalWord_chart ψ _ (fun c hc => gGen_psi σ ψ ζ (hw c hc)) h

theorem invE_le_suzM' {x : Pm} (hx : x ∈ invE 1) : x ∈ suzM :=
  (mem_inf.1 (invE_le_centM (by norm_num : 1 < 4) hx)).2

theorem comm_t1' {x : Pm} (hx : x ∈ invE 1) : x * suzInv 1 = suzInv 1 * x :=
  mem_centralizer_singleton_iff.1 (mem_inf.1 (invE_le_centM (by norm_num : 1 < 4) hx)).1

theorem mem_centM_wP {x : Pm} (hx : x ∈ invE 1) (hp : Commute x p1P) : x ∈ centM wP := by
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, invE_le_suzM' hx⟩
  have h1 := comm_t1' hx
  simp only [wP, p1P] at hp ⊢
  calc x * (suzInv 1 * LevelTwo.aP LevelTwo.p1) = suzInv 1 * (x * LevelTwo.aP LevelTwo.p1) := by
        rw [← mul_assoc, h1, mul_assoc]
    _ = suzInv 1 * LevelTwo.aP LevelTwo.p1 * x := by rw [hp.eq, mul_assoc]

theorem baseRels_val {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} {ζ : centM wP →* G}
    (hB : B0Agree σ ψ) (hζ : ChartAgree σ ζ) : ∀ r ∈ baseRels, evalWord (gGen σ ψ ζ) r = 1 := by
  have hinv := gGen_inv σ ψ ζ
  have hsP := sP_mem_centM
  intro r hr
  simp only [baseRels, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with (((hr | hr) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | rfl
  · rw [evalWord_sig ζ hB (relsH1_codes r hr) (sigWord_mem (relsH1_codes r hr))]
    have e : (⟨evalWord genM r, sigWord_mem (relsH1_codes r hr)⟩ : ↥(invE 1)) = 1 :=
      Subtype.ext (relsH1_val r hr)
    rw [e, map_one]
  · rw [evalWord_psi σ ψ ζ (relsH2_codes r hr) (psiWord_mem (relsH2_codes r hr))]
    have e : (⟨evalWord genM r, psiWord_mem (relsH2_codes r hr)⟩ : ↥Model.NR0) = 1 :=
      Subtype.ext (relsH2_val r hr)
    rw [e, map_one]
  · obtain ⟨h1, h2⟩ := relsA_codes p hp
    rw [evalWord_append, evalWord_winv hinv (fun c hc => by have := (h2 c hc).2; omega),
      evalWord_sig ζ hB h1 (sigWord_mem h1), evalWord_psi σ ψ ζ h2 (psiWord_mem h2),
      mul_inv_eq_one]
    have hv : evalWord genM p.2 ∈ invE 1 := relsA_val p hp ▸ sigWord_mem h1
    rw [hB _ hv (psiWord_mem h2)]
    exact congrArg (fun c => sig σ c) (Subtype.ext (relsA_val p hp))
  · obtain ⟨h1, h2⟩ := edge_codes p hp
    obtain ⟨hc, he⟩ := edge_val p hp
    have hu := sigWord_mem h1
    have hu' := sigWord_mem h2
    have huw : evalWord genM p.1 ∈ centM wP := mem_centM_wP hu hc
    have hu'w : evalWord genM p.2 ∈ centM wP := by
      rw [he]
      exact mul_mem (mul_mem hsP huw) (inv_mem hsP)
    rw [evalWord_append, evalWord_append, evalWord_append, evalWord_winv hinv
      (fun c hc => by have := h2 c hc; omega), evalWord_sig ζ hB h1 hu, evalWord_sig ζ hB h2 hu']
    simp only [evalWord_cons, evalWord_nil, mul_one]
    rw [gGen_ten, gGen_eleven, sig_apply, sig_apply, ← hζ _ hu huw, ← hζ _ hu' hu'w, ← map_inv,
      ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    convert map_one ζ
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Subgroup.coe_one]
    rw [he]
    group
  · have hsq := sigWord_mem sq_codes
    have hsqw : evalWord genM sq ∈ centM wP := by
      rw [sq_val]
      exact mul_mem hsP hsP
    rw [evalWord_append, evalWord_winv hinv (fun c hc => by have := sq_codes c hc; omega),
      evalWord_sig ζ hB sq_codes hsq]
    simp only [evalWord_cons, evalWord_nil, mul_one]
    rw [gGen_ten, sig_apply, ← hζ _ hsq hsqw, ← map_mul, mul_inv_eq_one]
    refine congrArg ζ (Subtype.ext ?_)
    show sP * sP = evalWord genM sq
    rw [sq_val]

end Words

section Disc

variable {G : Type} [Group G] {M : Subgroup G}

@[expose] noncomputable def eP (j : Fin 2) : Pm := (cP j)⁻¹ * sP * cP' j

theorem cP_mem (j : Fin 2) : cP j ∈ invE 1 := by
  rw [← cW_val j]
  exact sigWord_mem (cell_codes j).1

theorem cP'_mem (j : Fin 2) : cP' j ∈ invE 1 := by
  rw [← cpW_val j]
  exact sigWord_mem (cell_codes j).2.1

theorem eP_mem (j : Fin 2) : eP j ∈ Model.NR0 := by
  rw [eP, ← eW_val j]
  exact psiWord_mem (cell_codes j).2.2

@[expose] noncomputable def candP (j : Fin 2) (n : ℕ) : Pm :=
  evalWord genM ((deltaW (2 * j.val)).getD n [])

theorem candP_mem (j : Fin 2) (n : ℕ) : candP j n ∈ invE 1 :=
  evalWord_mem_of _ _ fun c hc => genM_mem_invE c (Or.inl (by have := delta_codes j n c hc; omega))

@[expose] noncomputable def cellG (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (j : Fin 2) : G :=
  sig σ ⟨cP j, cP_mem j⟩ * ψ ⟨eP j, eP_mem j⟩ * (sig σ ⟨cP' j, cP'_mem j⟩)⁻¹

theorem cellRel_val {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} {ζ : centM wP →* G}
    (hB : B0Agree σ ψ) (j : Fin 2) (n : ℕ)
    (h : cellG σ ψ j = ζ ⟨sP, sP_mem_centM⟩ * sig σ ⟨candP j n, candP_mem j n⟩) :
    evalWord (gGen σ ψ ζ) (cellRel (2 * j.val) n) = 1 := by
  have hinv := gGen_inv σ ψ ζ
  obtain ⟨h1, h2, h3⟩ := cell_codes j
  have hd : ∀ c ∈ (deltaW (2 * j.val)).getD n [], c < 6 := fun c hc => by
    have := delta_codes j n c hc; omega
  rw [cellRel, evalWord_append, evalWord_append, evalWord_append, evalWord_append,
    evalWord_winv hinv (fun c hc => by have := h2 c hc; omega),
    evalWord_winv hinv (fun c hc => by have := hd c hc; omega),
    evalWord_sig ζ hB h1 (sigWord_mem h1), evalWord_psi σ ψ ζ h3 (psiWord_mem h3),
    evalWord_sig ζ hB h2 (sigWord_mem h2), evalWord_sig ζ hB hd (sigWord_mem hd)]
  simp only [evalWord_cons, evalWord_nil, mul_one]
  rw [gGen_eleven]
  have e1 : (⟨evalWord genM (cW (2 * j.val)), sigWord_mem h1⟩ : ↥(invE 1)) = ⟨cP j, cP_mem j⟩ :=
    Subtype.ext (cW_val j)
  have e2 : (⟨evalWord genM (eW (2 * j.val)), psiWord_mem h3⟩ : ↥Model.NR0) = ⟨eP j, eP_mem j⟩ :=
    Subtype.ext (eW_val j)
  have e3 : (⟨evalWord genM (cpW (2 * j.val)), sigWord_mem h2⟩ : ↥(invE 1)) =
      ⟨cP' j, cP'_mem j⟩ := Subtype.ext (cpW_val j)
  have e4 : (⟨evalWord genM ((deltaW (2 * j.val)).getD n []), sigWord_mem hd⟩ : ↥(invE 1)) =
      ⟨candP j n, candP_mem j n⟩ := rfl
  rw [e1, e2, e3, e4]
  have h' := h
  rw [cellG] at h'
  rw [h']
  group

end Disc

theorem hom_mul_eq {G : Type*} [Group G] {H : Subgroup Pm} (f : ↥H →* G) {a b c d : Pm}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H) (h : a * b = c * d) :
    f ⟨a, ha⟩ * f ⟨b, hb⟩ = f ⟨c, hc⟩ * f ⟨d, hd⟩ := by
  rw [← map_mul, ← map_mul]
  exact congrArg f (Subtype.ext h)

section Bound

variable {G : Type} [Group G] {M : Subgroup G}

theorem disc_comm {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} {ζ : centM wP →* G} (hB : B0Agree σ ψ)
    (hζ : ChartAgree σ ζ) (j : Fin 2) {m : Pm} (hm : m ∈ invE 1) (hp : Commute m p1P)
    (hN : (cP' j)⁻¹ * m * cP' j ∈ normalizer (Model.R0 : Set Pm))
    (h2 : Commute (eP j * ((cP' j)⁻¹ * m * cP' j) * (eP j)⁻¹) (suzInv 1))
    (h3 : Commute (sP * m * sP⁻¹) (suzInv 1)) :
    (ζ ⟨sP, sP_mem_centM⟩)⁻¹ * cellG σ ψ j * sig σ ⟨m, hm⟩ =
      sig σ ⟨m, hm⟩ * ((ζ ⟨sP, sP_mem_centM⟩)⁻¹ * cellG σ ψ j) := by
  have hsP := sP_mem_centM
  have hC := cP_mem j
  have hC' := cP'_mem j
  have hE := eP_mem j
  have hB' : ∀ x (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = sig σ ⟨x, hx⟩ := hB
  have hm1 : (cP' j)⁻¹ * m * cP' j ∈ invE 1 := mul_mem (mul_mem (inv_mem hC') hm) hC'
  have hm1N : (cP' j)⁻¹ * m * cP' j ∈ Model.NR0 := mem_inf.2 ⟨invE_le_suzM' hm1, hN⟩
  have hm2N : eP j * ((cP' j)⁻¹ * m * cP' j) * (eP j)⁻¹ ∈ Model.NR0 :=
    mul_mem (mul_mem hE hm1N) (inv_mem hE)
  have hm2 : eP j * ((cP' j)⁻¹ * m * cP' j) * (eP j)⁻¹ ∈ invE 1 :=
    ModelGroups.mem_invE_one_iff.2 ⟨h2.eq, (mem_inf.1 hm2N).1⟩
  have hmw := mem_centM_wP hm hp
  have hm3w : sP * m * sP⁻¹ ∈ centM wP := mul_mem (mul_mem hsP hmw) (inv_mem hsP)
  have hm3 : sP * m * sP⁻¹ ∈ invE 1 := ModelGroups.mem_invE_one_iff.2 ⟨h3.eq, (mem_inf.1 hm3w).2⟩
  have ha : cellG σ ψ j * sig σ ⟨m, hm⟩ = sig σ ⟨sP * m * sP⁻¹, hm3⟩ * cellG σ ψ j := by
    have e1 : (sig σ ⟨cP' j, hC'⟩)⁻¹ * sig σ ⟨m, hm⟩ =
        sig σ ⟨(cP' j)⁻¹ * m * cP' j, hm1⟩ * (sig σ ⟨cP' j, hC'⟩)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
      exact hom_mul_eq (sig σ) hm hC' hC' hm1 (by group)
    have e2 : ψ ⟨eP j, hE⟩ * ψ ⟨(cP' j)⁻¹ * m * cP' j, hm1N⟩ =
        ψ ⟨eP j * ((cP' j)⁻¹ * m * cP' j) * (eP j)⁻¹, hm2N⟩ * ψ ⟨eP j, hE⟩ :=
      hom_mul_eq ψ hE hm1N hm2N hE (by group)
    have e3 : sig σ ⟨cP j, hC⟩ * sig σ ⟨eP j * ((cP' j)⁻¹ * m * cP' j) * (eP j)⁻¹, hm2⟩ =
        sig σ ⟨sP * m * sP⁻¹, hm3⟩ * sig σ ⟨cP j, hC⟩ :=
      hom_mul_eq (sig σ) hC hm2 hm3 hC (by simp only [eP]; group)
    rw [cellG, mul_assoc, e1, ← mul_assoc, mul_assoc (sig σ ⟨cP j, hC⟩), ← hB' _ hm1 hm1N, e2,
      hB' _ hm2 hm2N, ← mul_assoc, e3]
    group
  have hb : ζ ⟨sP, hsP⟩ * sig σ ⟨m, hm⟩ = sig σ ⟨sP * m * sP⁻¹, hm3⟩ * ζ ⟨sP, hsP⟩ := by
    rw [sig_apply, sig_apply, ← hζ _ hm hmw, ← hζ _ hm3 hm3w]
    exact hom_mul_eq ζ hsP hmw hm3w hsP (by group)
  calc (ζ ⟨sP, hsP⟩)⁻¹ * cellG σ ψ j * sig σ ⟨m, hm⟩ =
        (ζ ⟨sP, hsP⟩)⁻¹ * (sig σ ⟨sP * m * sP⁻¹, hm3⟩ * cellG σ ψ j) := by rw [mul_assoc, ha]
    _ = (ζ ⟨sP, hsP⟩)⁻¹ * (ζ ⟨sP, hsP⟩ * sig σ ⟨m, hm⟩ * (ζ ⟨sP, hsP⟩)⁻¹ * cellG σ ψ j) := by
        rw [hb, mul_inv_cancel_right]
    _ = sig σ ⟨m, hm⟩ * ((ζ ⟨sP, hsP⟩)⁻¹ * cellG σ ψ j) := by group

theorem t1_mem_C1 : suzInv 1 ∈ invE 1 :=
  ModelGroups.mem_invE_one_iff.2 ⟨rfl, ModelGroups.t1_mem_suzM⟩

end Bound

end CFSG.Sporadic.SuzRecog.MixedCell
