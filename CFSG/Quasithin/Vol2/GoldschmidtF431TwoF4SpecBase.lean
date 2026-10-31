
module

public import Certificates.Data.TwoF4LieCheck
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsAction
public import Mathlib.Logic.Relation
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuArr
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
public import CFSG.Quasithin.Recognition.RuTypeJ47Cert

@[expose] public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

open scoped Pointwise

set_option linter.unusedSectionVars false

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

def gInv : Array (Array ℕ) := invArrs 1755 titsGenArrs

theorem invsOK_gInv : invsOK 1755 titsGenArrs gInv = true := by
  simp only [invsOK, gInv, invArrs, Array.size_map, beq_self_eq_true, Bool.true_and]
  refine allLt_iff.2 fun i hi => ?_
  rw [getElem!_pos (titsGenArrs.map (invCand 1755)) i (by simpa using hi), Array.getElem_map,
    ← getElem!_pos titsGenArrs i hi]
  exact titsGen_inv (by rwa [titsGenArrs_size] at hi)

noncomputable def wEl (s : String) : ↥TA := wordElt (decodeWord s)

theorem decodeWord_lt {s : String} (h : wordOK s = true) : ∀ l ∈ decodeWord s, l.1 < 4 := by
  simpa [wordOK, List.all_eq_true] using h

theorem rep_wEl {s : String} (hs : wordOK s = true) (hG : invsOK 1755 titsGenArrs gInv = true) :
    Rep 1755 (wArr titsGenArrs gInv s) (wEl s).1 :=
  rep_evalArr rfl hG (decodeWord s) (decodeWord_lt hs)

theorem fix_point_of_inH {a : Array ℕ} {g : ↥TA} (ha : Rep 1755 a g.1)
    (h : fixesH titsLinePtArr a = true) : g.1 0 = 0 := by
  have h1 := (actOK_iff ha (by norm_num : 0 < 4680) (by norm_num : 0 < 4680)).1 h
  rw [ofCode_inl (by norm_num), smul_inl] at h1
  exact congrArg Fin.val (Sum.inl.inj h1) |> fun e => Fin.ext e

theorem fix_line_of_inN {a : Array ℕ} {g : ↥TA} (ha : Rep 1755 a g.1)
    (h : fixesN titsLinePtArr a = true) : g.1 • titsLine 0 = titsLine 0 := by
  have h1 := (actOK_iff ha (by norm_num : 1755 < 4680) (by norm_num : 1755 < 4680)).1 h
  rw [ofCode_inr (by norm_num) (by norm_num), smul_inr] at h1
  exact (lineHom_eq_iff g _ _).1 (Sum.inr.inj h1)

theorem mem_twoF4H_of_inH {a : Array ℕ} {g : ↥TA} (ha : Rep 1755 a g.1)
    (h : fixesH titsLinePtArr a = true) : g.1 ∈ twoF4H :=
  (mem_twoF4H_iff g.2).2 (fix_point_of_inH ha h)

theorem mem_twoF4N_of_inN {a : Array ℕ} {g : ↥TA} (ha : Rep 1755 a g.1)
    (h : fixesN titsLinePtArr a = true) : g.1 ∈ twoF4N :=
  (mem_twoF4N_iff g.2).2 (fix_line_of_inN ha h)

theorem mem_twoF4S_of_inS {a : Array ℕ} {g : ↥TA} (ha : Rep 1755 a g.1)
    (h : fixesS titsLinePtArr a = true) : g.1 ∈ twoF4S := by
  rw [fixesS, Bool.and_eq_true] at h
  exact (mem_twoF4S_iff g.2).2 ⟨fix_point_of_inH ha h.1, fix_line_of_inN ha h.2⟩

theorem wordOK_tWord : wordOK tWord = true := by decide

theorem wordOK_cWord : wordOK cWord = true := by decide

noncomputable def tEl : ↥TA := wEl tWord

theorem rep_tEl : Rep 1755 (tArr titsGenArrs gInv) tEl.1 :=
  rep_wEl wordOK_tWord invsOK_gInv

noncomputable def cEl : ↥TA := wEl cWord

theorem rep_cEl : Rep 1755 (cArr titsGenArrs gInv) cEl.1 :=
  rep_wEl wordOK_cWord invsOK_gInv

theorem card_twoF4S : Nat.card twoF4S = 4096 := by
  have h := Subgroup.card_mul_index (titsS.subgroupOf twoF4S)
  have h2 : (titsS.subgroupOf twoF4S).index = 2 :=
    relIndex_extSub (fun hq => tπ_not_mem_D (titsS_le_titsD hq))
  have hle : titsS ≤ twoF4S := le_extSub
  rw [h2, card_subgroupOf_eq hle, (titsQS_facts).2.2.2] at h
  omega

end CFSG.Quasithin.H13.F431.TwoF4
