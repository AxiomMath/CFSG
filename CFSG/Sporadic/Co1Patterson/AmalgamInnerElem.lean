module

public import CFSG.Sporadic.Co1Patterson.AmalgamInnerCore
public import CFSG.Sporadic.Co1Patterson.AmalgamInnerInputs
public import CFSG.Sporadic.Co1Patterson.TwistNativeCore
public import Certificates.Certificate21159
public import Certificates.Certificate21235
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2AData
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.NotConj
public import CFSG.Open.QuasithinDefs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.InnerNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
  CFSG.Sporadic.Co1Patterson.TwistNative CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

local macro "CA" : term => `(centralizer ({aNC} : Set NativeSporadic.Co1))

theorem inner_elem_check : innerElemOK = true :=
  Certificates.certificate21159.1

theorem inner_gen_check : innerGenOK = true :=
  Certificates.certificate21159.2.1

theorem inner_loop_check : innerLoopOK = true :=
  Certificates.certificate21159.2.2

theorem inner_bfs_check : innerBfsOK = true :=
  Certificates.certificate21235.1

theorem inner_orb_check : innerOrbOK = true :=
  Certificates.certificate21235.2

theorem innerElemOK_parts :
    (∀ j < 2, CFSG.Sporadic.Co1.InvNative.validRows (kRow j) = true ∧
      CFSG.Sporadic.Co1.InvNative.validRows (kRowI j) = true ∧
      Native.mul (kRow j) (kRowI j) = Native.one) ∧
    Native.pow (kRow 1) 15 = Native.one ∧ Native.mul rxRow rxRow = iotaARows ∧
    Native.mul ryRow ryRow = yRow 0 ∧
    ∀ w ∈ stabWords, stabR (kWordR w) rxRow = true ∧ stabR (kWordR w) ryRow = true := by
  have h := inner_elem_check
  simp only [innerElemOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨fun j hj => ⟨(h1 j hj).1.1, (h1 j hj).1.2, (h1 j hj).2⟩, h2, h3, h4,
    fun w hw => h5 w hw⟩

section Words


theorem rep_kH {j : ℕ} (hj : j < 2) : MRep (kRow j) (centEmb (kH j)) := by
  rw [kH, centEmb_twH (elemsOK_parts.2.1 j hj).2.1]
  exact rep_twG _

theorem rep_kH_inv {j : ℕ} (hj : j < 2) :
    MRep (kRowI j) (centEmb (kH j)⁻¹) := by
  rw [map_inv]
  exact (rep_kH hj).inv (innerElemOK_parts.1 j hj).2.2

@[expose] noncomputable def kW (w : List ℕ) : CA := w.foldl (fun acc j => acc * kH j) 1

theorem foldl_kH (w : List ℕ) (x : CA) :
    w.foldl (fun acc j => acc * kH j) x = x * kW w := by
  induction w generalizing x with
  | nil => simp [kW]
  | cons j w ih =>
    simp only [List.foldl_cons, kW]
    rw [ih, ih (1 * kH j), one_mul, mul_assoc]

theorem kW_nil : kW [] = 1 := rfl

theorem kW_append (w w' : List ℕ) : kW (w ++ w') = kW w * kW w' := by
  rw [kW, List.foldl_append, ← kW, foldl_kH]

theorem kW_cons (j : ℕ) (w : List ℕ) : kW (j :: w) = kH j * kW w := by
  rw [show j :: w = [j] ++ w from rfl, kW_append]
  simp [kW]

theorem kW_inv (w : List ℕ) : (kW w)⁻¹ = w.foldl (fun acc j => (kH j)⁻¹ * acc) 1 := by
  have key : ∀ x : CA, (w.foldl (fun acc j => acc * kH j) x)⁻¹ =
      w.foldl (fun acc j => (kH j)⁻¹ * acc) x⁻¹ := by
    induction w with
    | nil => exact fun _ => rfl
    | cons j w ih =>
      intro x
      simp only [List.foldl_cons]
      rw [ih, mul_inv_rev]
  rw [kW, key, inv_one]

theorem rep_kW {w : List ℕ} (hw : ∀ j ∈ w, j < 2) : MRep (kWordR w) (centEmb (kW w)) := by
  have key : ∀ (X : Native.Rows) (x : CA), MRep X (centEmb x) →
      MRep (w.foldl (fun acc j => Native.mul acc (kRow j)) X)
        (centEmb (w.foldl (fun acc j => acc * kH j) x)) := by
    induction w with
    | nil => exact fun _ _ h => h
    | cons j w ih =>
      intro X x h
      simp only [List.foldl_cons]
      refine ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _ _ ?_
      rw [map_mul]
      exact h.mul (rep_kH (hw j List.mem_cons_self))
  rw [kWordR, kW]
  exact key _ _ (by rw [map_one]; exact MRep.one)

theorem rep_kW_inv {w : List ℕ} (hw : ∀ j ∈ w, j < 2) :
    MRep (kWordIR w) (centEmb (kW w)⁻¹) := by
  have key : ∀ (X : Native.Rows) (x : CA), MRep X (centEmb x) →
      MRep (w.foldl (fun acc j => Native.mul (kRowI j) acc) X)
        (centEmb (w.foldl (fun acc j => (kH j)⁻¹ * acc) x)) := by
    induction w with
    | nil => exact fun _ _ h => h
    | cons j w ih =>
      intro X x h
      simp only [List.foldl_cons]
      refine ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _ _ ?_
      rw [map_mul]
      exact (rep_kH_inv (hw j List.mem_cons_self)).mul h
  rw [kWordIR, kW_inv]
  exact key _ _ (by rw [map_one]; exact MRep.one)

end Words

section Members


theorem kW_mem_K₀ {w : List ℕ} (hw : ∀ j ∈ w, j < 2) : kW w ∈ K₀ := by
  have key : ∀ x : CA, x ∈ K₀ → w.foldl (fun acc j => acc * kH j) x ∈ K₀ := by
    induction w with
    | nil => exact fun _ h => h
    | cons j w ih =>
      intro x hx
      simp only [List.foldl_cons]
      exact ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _
        (mul_mem hx (kH_mem_K₀ (hw j List.mem_cons_self)))
  exact key 1 (one_mem _)

theorem mem_R₀_of_phi {q : CA} (hq : typeSystemC.φ q = 1) (hk : q ∈ K₀) : q ∈ R₀ := by
  refine ⟨hk, fun x hx => ?_⟩
  rw [actV, hq, OneMemClass.coe_one, LinearEquiv.coe_one, id, clean_of_mem hx]

theorem z_mem_K₀ : typeSystemC.z ∈ K₀ := mem_K₀.2 (typeSystemC.z_comm (yH 0)).symm

theorem yH_zero_mem_K₀ : yH 0 ∈ K₀ := mem_K₀.2 rfl

theorem z_mem_R₀ : typeSystemC.z ∈ R₀ := mem_R₀_of_phi typeSystemC.φ_z z_mem_K₀

theorem yH_zero_mem_R₀ : yH 0 ∈ R₀ := mem_R₀_of_phi phi_yH_zero yH_zero_mem_K₀

theorem hcH_zero : hcH 0 = 1 := by
  simp [hcH]

@[expose] noncomputable def rx : CA := aElt (34, 0)

@[expose] noncomputable def ry : CA := hcH 55 * aElt (108, 0)

theorem rx_mem_R₀ : rx ∈ R₀ := by
  have h := hcH_mul_aElt_mem (c := 0) (by norm_num) (p := (34, 0)) (by decide)
  rwa [hcH_zero, one_mul] at h

theorem ry_mem_R₀ : ry ∈ R₀ := hcH_mul_aElt_mem (by norm_num) (by decide)

theorem conjWords_lt (i : ℕ) : ∀ j ∈ conjWords.getD i [], j < 2 := by
  by_cases hi : i < 6
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [conjWords]; omega)]
    simp

@[expose] noncomputable def tE (j : ℕ) : CA :=
  kW (conjWords.getD (j % 6) []) * (if j < 6 then rx else ry) *
    (kW (conjWords.getD (j % 6) []))⁻¹

theorem tE_mem_R₀ (j : ℕ) : tE j ∈ R₀ := by
  refine conj_mem_R₀ (kW_mem_K₀ (conjWords_lt _)) ?_
  split_ifs
  · exact rx_mem_R₀
  · exact ry_mem_R₀

end Members

section Rows


theorem rep_rx : MRep rxRow (centEmb rx) := rep_aElt _

theorem rep_ry : MRep ryRow (centEmb ry) := by
  rw [ry, map_mul]
  exact (rep_hcH 55).mul (rep_aElt _)

theorem valid_rxRow : CFSG.Sporadic.Co1.InvNative.validRows rxRow = true :=
  valid_aRowOf (by norm_num)

theorem valid_ryRow : CFSG.Sporadic.Co1.InvNative.validRows ryRow = true :=
  valid_mul (valid_hprodRow 55) (valid_aRowOf (by norm_num))

theorem rep_tE (j : ℕ) : MRep (tRow j) (centEmb (tE j)) := by
  rw [tE, tRow, map_mul, map_mul]
  refine ((rep_kW (conjWords_lt _)).mul ?_).mul (rep_kW_inv (conjWords_lt _))
  split_ifs
  · exact rep_rx
  · exact rep_ry

theorem valid_kWordR {w : List ℕ} (hw : ∀ j ∈ w, j < 2) :
    CFSG.Sporadic.Co1.InvNative.validRows (kWordR w) = true := by
  have key : ∀ X : Native.Rows, CFSG.Sporadic.Co1.InvNative.validRows X = true →
      CFSG.Sporadic.Co1.InvNative.validRows
        (w.foldl (fun acc j => Native.mul acc (kRow j)) X) = true := by
    induction w with
    | nil => exact fun _ h => h
    | cons j w ih =>
      intro X h
      simp only [List.foldl_cons]
      exact ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _
        (valid_mul h (innerElemOK_parts.1 j (hw j List.mem_cons_self)).1)
  exact key _ validRows_one

theorem valid_kWordIR {w : List ℕ} (hw : ∀ j ∈ w, j < 2) :
    CFSG.Sporadic.Co1.InvNative.validRows (kWordIR w) = true := by
  have key : ∀ X : Native.Rows, CFSG.Sporadic.Co1.InvNative.validRows X = true →
      CFSG.Sporadic.Co1.InvNative.validRows
        (w.foldl (fun acc j => Native.mul (kRowI j) acc) X) = true := by
    induction w with
    | nil => exact fun _ h => h
    | cons j w ih =>
      intro X h
      simp only [List.foldl_cons]
      exact ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _
        (valid_mul (innerElemOK_parts.1 j (hw j List.mem_cons_self)).2.1 h)
  exact key _ validRows_one

theorem valid_tRow (j : ℕ) : CFSG.Sporadic.Co1.InvNative.validRows (tRow j) = true := by
  rw [tRow]
  refine valid_mul (valid_mul (valid_kWordR (conjWords_lt _)) ?_)
    (valid_kWordIR (conjWords_lt _))
  split_ifs
  · exact valid_rxRow
  · exact valid_ryRow

end Rows

section Four


theorem yH_zero_mul_self : yH 0 * yH 0 = 1 := by
  rw [typeSystemC.mul_self_eq_one_iff _ phi_yH_zero, vec_yH_zero, q₀_bv]
  rfl

theorem z_mul_yH_zero : typeSystemC.z * yH 0 = yH 0 * typeSystemC.z :=
  (typeSystemC.z_comm _).symm

@[expose] noncomputable def vSub : Subgroup CA :=
  fourGroup typeSystemC.z_mul_self yH_zero_mul_self z_mul_yH_zero

theorem mem_vSub {x : CA} :
    x ∈ vSub ↔ x = 1 ∨ x = typeSystemC.z ∨ x = yH 0 ∨ x = yH 0 * typeSystemC.z :=
  Iff.rfl

theorem vSub_le_R₀ : vSub ≤ R₀ := by
  intro x hx
  rcases mem_vSub.1 hx with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact z_mem_R₀
  · exact yH_zero_mem_R₀
  · exact mul_mem yH_zero_mem_R₀ z_mem_R₀

theorem vSub_central : ∀ v ∈ vSub, ∀ g ∈ K₀, v * g = g * v := by
  intro v hv g hg
  rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact (typeSystemC.z_comm g).symm
  · exact (mem_K₀.1 hg).symm
  · rw [mul_assoc, ← typeSystemC.z_comm g, ← mul_assoc, ← mem_K₀.1 hg, mul_assoc]

theorem vSub_mul_self : ∀ v ∈ vSub, v * v = 1 := by
  intro v hv
  rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact typeSystemC.z_mul_self
  · exact yH_zero_mul_self
  · calc yH 0 * typeSystemC.z * (yH 0 * typeSystemC.z) =
        yH 0 * (typeSystemC.z * yH 0) * typeSystemC.z := by group
      _ = yH 0 * (yH 0 * typeSystemC.z) * typeSystemC.z := by rw [z_mul_yH_zero]
      _ = 1 := by rw [← mul_assoc, yH_zero_mul_self, one_mul, typeSystemC.z_mul_self]

end Four

section FourRows


theorem rep_one' : MRep Native.one (centEmb (1 : CA)) := by
  rw [map_one]
  exact MRep.one

theorem rep_z' : MRep iotaARows (centEmb typeSystemC.z) := by
  rw [show centEmb typeSystemC.z = aG from centEmb_zM]
  exact rep_iotaA

theorem rep_w' : MRep (yRow 0) (centEmb (yH 0)) := by
  rw [centEmb_yH]
  exact rep_yG 0

theorem rep_wz' : MRep (Native.mul (yRow 0) iotaARows) (centEmb (yH 0 * typeSystemC.z)) := by
  rw [map_mul]
  exact rep_w'.mul rep_z'

theorem exists_of_any {X Y : Native.Rows} {x y : CA} (hX : MRep X (centEmb x))
    (hY : MRep Y (centEmb y)) (h : (vRows.any fun v => X == Native.mul v Y) = true) :
    ∃ v ∈ vSub, x = v * y := by
  simp only [vRows, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  have key : ∀ (W : Native.Rows) (v : CA), MRep W (centEmb v) → v ∈ vSub →
      X = Native.mul W Y → ∃ v ∈ vSub, x = v * y := fun W v hW hv e => by
    have h' : MRep (Native.mul W Y) (centEmb x) := e ▸ hX
    exact ⟨v, hv, centEmb_injective (by rw [map_mul]; exact h'.eq (hW.mul hY))⟩
  rcases h with h | h | h | h
  · exact key _ _ rep_one' (mem_vSub.2 (Or.inl rfl)) h
  · exact key _ _ rep_z' (mem_vSub.2 (Or.inr (Or.inl rfl))) h
  · exact key _ _ rep_w' (mem_vSub.2 (Or.inr (Or.inr (Or.inl rfl)))) h
  · exact key _ _ rep_wz' (mem_vSub.2 (Or.inr (Or.inr (Or.inr rfl)))) h

theorem any_of_exists {X Y : Native.Rows} {x y : CA} (hX : MRep X (centEmb x))
    (hY : MRep Y (centEmb y)) (vX : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (vY : CFSG.Sporadic.Co1.InvNative.validRows Y = true) (h : ∃ v ∈ vSub, x = v * y) :
    (vRows.any fun v => X == Native.mul v Y) = true := by
  obtain ⟨v, hv, rfl⟩ := h
  simp only [vRows, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
  have key : ∀ W : Native.Rows, MRep W (centEmb v) →
      CFSG.Sporadic.Co1.InvNative.validRows W = true → (X == Native.mul W Y) = true :=
    fun W hW vW => (rows_beq_iff hX (hW.mul hY) vX (valid_mul vW vY)).2 (by rw [map_mul])
  rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
  · exact Or.inl (key _ rep_one' validRows_one)
  · exact Or.inr (Or.inl (key _ rep_z' dagOK_parts.2.1))
  · exact Or.inr (Or.inr (Or.inl (key _ rep_w' (dagOK_parts.2.2.1 0 (by norm_num)))))
  · exact Or.inr (Or.inr (Or.inr (key _ rep_wz'
      (valid_mul (dagOK_parts.2.2.1 0 (by norm_num)) dagOK_parts.2.1))))

theorem stab_of_stabR {G X : Native.Rows} {g x : CA} (hG : MRep G (centEmb g))
    (hX : MRep X (centEmb x)) (h : stabR G X = true) : ∃ v ∈ vSub, g * x = v * (x * g) := by
  have hGX : MRep (Native.mul G X) (centEmb (g * x)) := by rw [map_mul]; exact hG.mul hX
  have hXG : MRep (Native.mul X G) (centEmb (x * g)) := by rw [map_mul]; exact hX.mul hG
  exact exists_of_any hGX hXG h

theorem stabR_of_stab {G X : Native.Rows} {g x : CA} (hG : MRep G (centEmb g))
    (hX : MRep X (centEmb x)) (vG : CFSG.Sporadic.Co1.InvNative.validRows G = true)
    (vX : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (h : ∃ v ∈ vSub, g * x = v * (x * g)) : stabR G X = true := by
  have hGX : MRep (Native.mul G X) (centEmb (g * x)) := by rw [map_mul]; exact hG.mul hX
  have hXG : MRep (Native.mul X G) (centEmb (x * g)) := by rw [map_mul]; exact hX.mul hG
  exact any_of_exists hGX hXG (valid_mul vG vX) (valid_mul vX vG) h

end FourRows

end CFSG.Sporadic.Co1Patterson.InnerNative
