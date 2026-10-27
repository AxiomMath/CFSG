module

public import CFSG.LocalAnalysis.WeakClosure81.W18Center
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Gt2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem comm_centralizer_le_conj (h162 : W3Thm162Gt2 G) (hm : MBarGT D.M V₀ V 2)
    (h : Hyp183 D V₀ V H i) {g : G} {A B : Subgroup G} (hAV : A ≤ conjSubgroup V g)
    (hAH : A ≤ H) (hBA : B ≤ A)
    (hlt : E3.mQuot A B + E3.mQuot (conjSubgroup V g) A <
      mBar D.M V₀ V h.setting.isElemAbelian) :
    ⁅eOmegaZ H D.T ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤
      eOmegaZ H D.T ⊓ conjSubgroup V₀ g := by
  have hs := h.setting
  have hVg := E3.isElemAbelian_conjSubgroup hs.isElemAbelian g
  have hMnormg : normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, hs.normalizer_eq]
  have hM₀g : conjSubgroup D.M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    refine (E3.conjSubgroup_mono_left g hs.pair.le_normalizer₀).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hmb : 2 < mBar D.M V₀ V hs.isElemAbelian := (hs.pair.mBarGT_iff_lt_mBar 2).1 hm
  have hr0 : ((mBar D.M V₀ V hs.isElemAbelian : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_trans (by exact_mod_cast Nat.le_add_right _ _) (h162 D V₀ V hs h.ne_bot (by omega))
  have hsum : ((E3.mQuot A B : ℕ) : ℕ∞) + ((E3.mQuot (conjSubgroup V g) A : ℕ) : ℕ∞) <
      ((mBar D.M V₀ V hs.isElemAbelian : ℕ) : ℕ∞) := by exact_mod_cast hlt
  have hlt' : (E3.mQuot A B : ℕ∞) + ((E3.mQuot (conjSubgroup V g) A : ℕ) : ℕ∞) <
      Min.min (rMV (conjSubgroup D.M g) (conjSubgroup V g))
        (mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg : ℕ∞) := by
    rw [rMV_conj hs.normalizer_eq g, mBar_conj D.M V₀ V hs.isElemAbelian hs.pair.le
      hs.pair.le_normalizer hs.pair.le_normalizer₀ g]
    exact lt_min (lt_of_lt_of_le hsum hr0) hsum
  exact commutator_le_inf_of_mQuot_add_lt (M := conjSubgroup D.M g) (V₀ := conjSubgroup V₀ g)
    (V := conjSubgroup V g) (A := A) (B := B) (E := eOmegaZ H D.T) hVg
    (E3.conjSubgroup_mono_left g hs.pair.le) hMnormg.ge hM₀g hAV rfl hBA
    (hAH.trans (Hyp183.normalizer_eOmegaZ H D.T)) h.isElemAbelian_eOmegaZ.isPGroup hlt'

theorem quadratic_of_lt (h162 : W3Thm162Gt2 G) (hm : MBarGT D.M V₀ V 2)
    (h : Hyp183 D V₀ V H i) {g : G} {A : Subgroup G} (hAV : A ≤ conjSubgroup V g)
    (hAH : A ≤ H)
    (hlt : E3.mQuot A (A ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) +
      E3.mQuot (conjSubgroup V g) A < mBar D.M V₀ V h.setting.isElemAbelian) :
    ⁅⁅eOmegaZ H D.T, A⁆, A⁆ = ⊥ := by
  have hb := h.comm_centralizer_le_conj h162 hm hAV hAH
    (inf_le_left : A ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ A) hlt
  have hEC : eOmegaZ H D.T ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) : Subgroup G) : Set G) =
      eOmegaZ H D.T := by
    refine inf_eq_left.2 fun e he => Subgroup.mem_centralizer_iff.2 fun b hb' => ?_
    exact (Subgroup.mem_centralizer_iff.mp hb'.2 e he).symm
  rw [hEC] at hb
  have hVg := E3.isElemAbelian_conjSubgroup h.setting.isElemAbelian g
  rw [eq_bot_iff]
  refine (Subgroup.commutator_mono hb le_rfl).trans ?_
  refine Subgroup.commutator_le.2 fun x hx a ha => ?_
  have hxV : x ∈ conjSubgroup V g := E3.conjSubgroup_mono_left g h.setting.pair.le hx.2
  have hcomm : x * a = a * x := hVg.comm hxV (hAV ha)
  rw [commutatorElement_def, hcomm]
  simp

end Hyp183

end CFSG.LocalAnalysis.WeakClosure81

end
