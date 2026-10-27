
module

public import CFSG.Monster.Existence.TwoA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Monster.Existence.TwoPoint.Fi23Check
public import CFSG.Sporadic.Bridge.Common

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

@[expose] noncomputable def fiMkW (w : List Native.Gen) : MGriess :=
  ⟨wordLin w, Gmat_le_AutO (wordLin_mem_Gmat w)⟩

theorem fiMkW_append (w₁ w₂ : List Native.Gen) : fiMkW (w₁ ++ w₂) = fiMkW w₂ * fiMkW w₁ :=
  Subtype.ext (wordLin_append w₁ w₂)

theorem fiMkW_nil : fiMkW [] = 1 := Subtype.ext wordLin_nil

theorem fiMkW_eq_one_iff {w : List Native.Gen} : fiMkW w = 1 ↔ wordLin w = 1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem wordLin_fiRhoT : wordLin fiRhoT = tStar := by
  have h1 : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ)) = 191 := by decide
  have h2 := Rep4371.pauliQ_minus (i := 0) (j := 1) (by decide)
  rw [h1] at h2
  show wordLin [Native.Gen.rho (false, 0, 191)] = tStar
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho]
  unfold tStar
  rw [rStar_eq_rMinus, ← h2]

theorem fiMkW_fiRhoT : fiMkW fiRhoT = tGriess := Subtype.ext wordLin_fiRhoT

@[expose] noncomputable def fiAlpha : MGriess := fiMkW fiWAlpha

@[expose] noncomputable def fiBeta : MGriess := fiMkW fiWBeta

theorem fiAlpha_mul_fiBeta : fiAlpha * fiBeta = fiMkW fiWAB :=
  (fiMkW_append fiWBeta fiWAlpha).symm

theorem fi_isConj_of_dihedral {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h3 : (a * b) ^ 3 = 1) : IsConj a b := by
  refine isConj_iff.2 ⟨a * b, ?_⟩
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h6 : a * b * a * b * a * b = 1 := by simpa [pow_succ, mul_assoc] using h3
  have h5 : a * b * a * b * a = b := by
    have : a * b * a * b * a * b = 1 := h6
    rw [mul_eq_one_iff_eq_inv, hb'] at this
    exact this
  calc a * b * a * (a * b)⁻¹ = a * b * a * b * a := by
        rw [mul_inv_rev, hb', ha']
        simp only [mul_assoc]
    _ = b := h5

theorem fiMkW_mem_cent_xGriess {w : List Native.Gen} (hw : w.all fiNotTau = true) :
    fiMkW w ∈ cent xGriess := by
  have h := wordLin_mem_Gvis w fun g hg => fiNotTau_spec (List.all_eq_true.1 hw g hg)
  rw [← map_cent_xGriess] at h
  obtain ⟨u, hu, hu'⟩ := h
  have e : u = fiMkW w := Subtype.ext hu'
  rw [← e]
  exact hu

theorem notTau_fiWAlpha : fiWAlpha.all fiNotTau = true := by decide

theorem notTau_fiWBeta : fiWBeta.all fiNotTau = true := by decide

theorem xGriess_mem_cent2 : xGriess ∈ cent2 fiAlpha fiBeta := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (fiMkW_mem_cent_xGriess notTau_fiWAlpha)).symm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (fiMkW_mem_cent_xGriess notTau_fiWBeta)).symm

@[expose] noncomputable def fiE (i : ℕ) : MGriess := fiMkW fiWU[i]!

theorem wordProd_fiE {R : List (ℕ × Bool)} (hR : ∀ l ∈ R, l.1 < 10) (hp : ∀ l ∈ R, l.2 = true) :
    wordProd fiE R = fiMkW (fiRelW R) := by
  induction R with
  | nil => simp [wordProd, fiRelW, fiMkW_nil]
  | cons l R ih =>
    have hR' : ∀ l' ∈ R, l'.1 < 10 := fun l' hl' => hR l' (List.mem_cons_of_mem _ hl')
    have hp' : ∀ l' ∈ R, l'.2 = true := fun l' hl' => hp l' (List.mem_cons_of_mem _ hl')
    have hpl : l.2 = true := hp l List.mem_cons_self
    have e : fiRelW (l :: R) = fiRelW R ++ fiWU[l.1]! := by
      simp [fiRelW]
    rw [e, fiMkW_append, ← ih hR' hp']
    simp only [wordProd, List.map_cons, List.prod_cons, hpl, ↓reduceIte]
    rfl

theorem fiRels_length : rels.length = 57 := rfl

end CFSG.Monster.Existence
