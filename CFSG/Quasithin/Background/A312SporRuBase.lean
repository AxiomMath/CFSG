
module

public import CFSG.Quasithin.Background.A312SporAlt5
public import CFSG.Quasithin.Background.A312SporE8
public import CFSG.Quasithin.Background.A312SporRuInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.ZMod.Basic
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat.Ru CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.Sporadic.SmallF2 CFSG.Quasithin.A312S.Ru
open CFSG.Sporadic.Ru.Native (ruData)
open Matrix

section Ru

theorem ru_row1 :
    MemStmt (ruCtx.Y 1) ⟨245760, 2048, 2⟩ := by
  obtain ⟨m, hm, hmS⟩ := ru_row 1 (by norm_num)
  have hc : Nat.card (ruCtx.Y 1) = 245760 := by
    rw [ru_member_card 1 (by norm_num)]
    rfl
  have h1 := hmS.1
  rw [hc] at h1
  simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hmS
    | exact absurd h1 (by decide)

theorem ru_index31 :
    ((ruCtx.Y 3).subgroupOf (ruCtx.Y 1)).index = 5 := by
  have hle : ruCtx.Y 3 ≤ ruCtx.Y 1 :=
    (ru_Y_le_iff (j := 3) (jj := 1) (by norm_num) (by norm_num)).mpr (by decide)
  have h1 := Subgroup.card_mul_index ((ruCtx.Y 3).subgroupOf (ruCtx.Y 1))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ru_member_card 3 (by norm_num),
    ru_member_card 1 (by norm_num)] at h1
  have h3 : (#[1, 15, 21, 3, 3] : Array ℕ)[3]! = 3 := rfl
  have h15 : (#[1, 15, 21, 3, 3] : Array ℕ)[1]! = 15 := rfl
  rw [h3, h15] at h1
  omega

theorem ru_case1
    {B : Subgroup (J ruData)}
    (hB : B ∈ lFamily ruCtx.S) (hY : B ⊔ ruCtx.S = ruCtx.Y 1) : A312Case B ⊤ := by
  have hZs : Group.IsSolvable ↥(ruCtx.Y 3) :=
    isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 14) (b := 1)
      (by rw [ru_member_card 3 (by norm_num)]; rfl)
  have hrow := ru_row1
  have hcard : Nat.card ↥(ruCtx.Y 1) = 120 * 2 ^ 11 := by
    rw [hrow.1]
    decide
  have hO2 : Nat.card (CFSG.Open.pCoreOf 2 (ruCtx.Y 1)) ≤ 2 ^ 11 := by
    rw [hrow.2.1]
    decide
  obtain ⟨hA5, hO2B⟩ := lFamily_alt5_of_index_five hB hY ru_index31 hZs hcard hO2 hrow.2.2
  iterate 18 right
  exact ⟨Or.inl hA5, hO2B, ⟨Subgroup.topEquiv.trans (seedEquiv ru_facts.toBaseFacts).symm⟩⟩

theorem ru_quotL2 :
    ruCtx.D.sTabs ++ ruCtx.D.mt[2]! = ruQuotL2 :=
  ru_letters2

noncomputable def ruE2 :
    List (J ruData) := ruCtx.sg ++ ruCtx.gens 2

theorem ruE2_tabs :
    genTabs ruData.n ruE2 = ruQuotL2 := by
  rw [ruE2, ruCtx.Y_letters (by rw [ru_J]; norm_num), ru_quotL2]

theorem ruE2_size :
    ruE2.toArray.size = 4 := by
  rw [List.size_toArray, ← genTabs_length (n := ruData.n), ruE2_tabs]
  rfl

theorem ruQuotL2_size : ruQuotL2.toArray.size = 4 := rfl

theorem ruE2_hel :
    ∀ l < ruE2.toArray.size,
      ruQuotL2.toArray.getD l #[] = (tab ruData.n (ruE2.toArray.getD l 1)).toArray := by
  rw [← ruE2_tabs]
  exact genTabs_hel ruE2

noncomputable def ruLetter
    (l : ℕ) : J ruData := ruE2.toArray.getD l 1

noncomputable def ruV
    (i : Fin 3) : J ruData :=
  evalElt ruE2.toArray (ruVWords.getD i [])

@[expose] def ruMat : ℕ → Matrix (Fin 3) (Fin 3) (ZMod 2)
  | 0 => !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  | 1 => !![1, 1, 1; 0, 0, 1; 0, 1, 0]
  | 2 => !![1, 0, 1; 0, 1, 0; 0, 0, 1]
  | 3 => !![1, 0, 0; 0, 0, 1; 1, 1, 1]
  | _ => 1

theorem ruMat_det (l : ℕ) : (ruMat l).det = 1 := by
  rcases l with _ | _ | _ | _ | l
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Matrix.det_one

@[expose] def ruSL (l : ℕ) : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨ruMat l, ruMat_det l⟩

theorem ru_hM : ∀ l < ruQuotL2.toArray.size, ∀ i : Fin 3,
    e8Col (ruVMats.getD l []) i = e8Vec fun r => ruMat l r i := by
  rw [ruQuotL2_size]
  decide +kernel

theorem ru_hv
    (i : Fin 3) :
    (tab ruData.n (ruV i)).toArray = ruVTabs.getD i #[] := by
  have hw : ∀ i : Fin 3, ∀ l ∈ ruVWords.getD i [], l < ruE2.toArray.size := by
    rw [ruE2_size]
    decide
  have h1 : ruVTabs.getD i #[] = wordTabA ruQuotL2.toArray ruData.n (ruVWords.getD i []) := by
    have key : ∀ (l : List (List ℕ)) (f : List ℕ → Array ℕ) (j : ℕ), j < l.length →
        (l.map f).toArray.getD j #[] = f (l.getD j []) := by
      intro l f j hj
      simp [Array.getD, hj, List.getD_eq_getElem _ _ hj]
    rw [ruVTabs]
    exact key _ _ _ (by simpa [ruVWords] using i.2)
  rw [h1, wordTabA_eq ruE2.toArray ruQuotL2.toArray ruE2_hel _ (hw i)]
  rfl

theorem ruLetter_mem
    {l : ℕ} (hl : l < 4) : ruLetter l ∈ ruCtx.Y 2 := by
  have h1 := evalElt_getD_mem_closure ruE2.toArray (l := l) (by rw [ruE2_size]; exact hl)
  rw [LatCtx.toList_toArray_set] at h1
  exact h1

theorem famRu_of {Γ : Type} [Group Γ] [Finite Γ]
    (eΓ : CFSG.Blueprint.NativeSporadic.Carrier .Ru ≃* Γ)
    (h : CFSG.IsQuasisimple Γ → A312For Γ) : FamRu := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  exact A312For.of_mulEquiv (e.trans eΓ)
    (h (CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.trans eΓ) hq))

end Ru

end CFSG.Quasithin.A312S
