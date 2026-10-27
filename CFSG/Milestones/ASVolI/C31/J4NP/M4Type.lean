module

public import CFSG.Milestones.ASVolI.C31.J4NP.M4TypeK
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictCol
public import Certificates.Certificate7953

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.J4Tree.Native CFSG.J4Tree.Native.Node CFSG.J4Tree.M4

section Conj


theorem burnsideJ4NP_m4_conj_parts :
    burnsideJ4NP_ConjW539 (burnsideJ4NP_Wv 486) ∧ burnsideJ4NP_ConjW539 (burnsideJ4NP_Wv 542) ∧
      burnsideJ4NP_ConjW539 burnsideJ4NP_m4Y136 ∧ burnsideJ4NP_ConjW539 burnsideJ4NP_m4Y266 :=
  Certificates.certificate7953

theorem burnsideJ4NP_m4_W486 :
    ∃ m : J, burnsideJ4NP_Wv 486 = (burnsideJ4NP_Wv 539).map (MulAut.conj m).toMonoidHom :=
  burnsideJ4NP_m4_conj_parts.1

theorem burnsideJ4NP_m4_W542 :
    ∃ m : J, burnsideJ4NP_Wv 542 = (burnsideJ4NP_Wv 539).map (MulAut.conj m).toMonoidHom :=
  burnsideJ4NP_m4_conj_parts.2.1

theorem burnsideJ4NP_m4_Y136_eq :
    ∃ m : J, burnsideJ4NP_m4Y136 = (burnsideJ4NP_Wv 539).map (MulAut.conj m).toMonoidHom :=
  burnsideJ4NP_m4_conj_parts.2.2.1

theorem burnsideJ4NP_m4_Y266_eq :
    ∃ m : J, burnsideJ4NP_m4Y266 = (burnsideJ4NP_Wv 539).map (MulAut.conj m).toMonoidHom :=
  burnsideJ4NP_m4_conj_parts.2.2.2

end Conj

section Verdicts


theorem burnsideJ4NP_verdictW_m4_486
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv 486) := by
  obtain ⟨m, hm⟩ := burnsideJ4NP_m4_W486
  rw [hm]
  exact burnsideJ4NP_verdictW_map_conj (burnsideJ4NP_verdictW_m4_539 h539) _

theorem burnsideJ4NP_verdictW_m4_542
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv 542) := by
  obtain ⟨m, hm⟩ := burnsideJ4NP_m4_W542
  rw [hm]
  exact burnsideJ4NP_verdictW_map_conj (burnsideJ4NP_verdictW_m4_539 h539) _

theorem burnsideJ4NP_verdictW_m4_of_Y0
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539)
    {W₀ Y₀ : Subgroup J} {m : J}
    (hY : Y₀ = (burnsideJ4NP_Wv 539).map (MulAut.conj m).toMonoidHom)
    (hNY : Subgroup.normalizer (W₀ : Set J) ≤ Subgroup.normalizer (Y₀ : Set J)) {h : J}
    (hhY : h ∈ Subgroup.centralizer (Y₀ : Set J))
    (hhW : h ∉ Subgroup.centralizer (W₀ : Set J)) : burnsideJ4NP_VerdictW W₀ := by
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (Y₀ : Set J)) := by
    rw [hY, burnsideJ4NP_centralizer_map_conj, burnsideJ4NP_m4_centralizer_W539 h539]
    exact burnsideJ4NP_m4_isPGroup_K.map _
  exact burnsideJ4NP_verdictW_of_core hNY hC2 hhY hhW

theorem burnsideJ4NP_verdictW_m4_136_of_normalizer
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539)
    (hNY : Subgroup.normalizer (burnsideJ4NP_Wv 136 : Set J) ≤
      Subgroup.normalizer (burnsideJ4NP_m4Y136 : Set J)) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv 136) := by
  obtain ⟨hy, -, hh, hw, -, hOK1, -⟩ := burnsideJ4NP_m4_h_parts
  have hhce : h136 ∈ [h136, h266] := by simp
  have hH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK hh _ hhce)
  unfold hOK at hOK1
  rw [Bool.and_eq_true, ← burnsideJ4NP_m4_encJ_treeElt hh hhce] at hOK1
  obtain ⟨m, hm⟩ := burnsideJ4NP_m4_Y136_eq
  exact burnsideJ4NP_verdictW_m4_of_Y0 h539 hm hNY
    (burnsideJ4NP_m4_mem_centralizer_coordSub hy hH hOK1.1)
    (burnsideJ4NP_m4_not_mem_centralizer_coordSub hw hH hOK1.2)

theorem burnsideJ4NP_verdictW_m4_266_of_normalizer
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539)
    (hNY : Subgroup.normalizer (burnsideJ4NP_Wv 266 : Set J) ≤
      Subgroup.normalizer (burnsideJ4NP_m4Y266 : Set J)) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv 266) := by
  obtain ⟨-, hy, hh, -, hw, -, hOK2⟩ := burnsideJ4NP_m4_h_parts
  have hhce : h266 ∈ [h136, h266] := by simp
  have hH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK hh _ hhce)
  unfold hOK at hOK2
  rw [Bool.and_eq_true, ← burnsideJ4NP_m4_encJ_treeElt hh hhce] at hOK2
  obtain ⟨m, hm⟩ := burnsideJ4NP_m4_Y266_eq
  exact burnsideJ4NP_verdictW_m4_of_Y0 h539 hm hNY
    (burnsideJ4NP_m4_mem_centralizer_coordSub hy hH hOK2.1)
    (burnsideJ4NP_m4_not_mem_centralizer_coordSub hw hH hOK2.2)

end Verdicts

theorem burnsideJ4NP_m4_eta_colBasis (k o : ℕ) :
    eta (burnsideJ4NP_colBasis k) (treeWv k).length o = burnsideJ4NP_maskElt (treeWv k) o := by
  unfold eta burnsideJ4NP_colBasis burnsideJ4NP_maskElt
  rfl

section Y0


theorem burnsideJ4NP_m4_encJ_maskElt {L : List (ℕ × ℕ)} (hL : coordsOK L = true) (m : ℕ) :
    burnsideJ4NP_maskElt L m ∈ Hj ∧
      burnsideJ4NP_encJ (burnsideJ4NP_maskElt L m) = maskCodeL L m := by
  unfold burnsideJ4NP_maskElt maskCodeL
  suffices h : ∀ (S : List ℕ), (∀ l ∈ S, l < L.length) → ∀ (a : J) (c : Code), a ∈ Hj →
      burnsideJ4NP_encJ a = c →
      S.foldl (fun acc l => if m.testBit l then acc * burnsideJ4NP_treeElt (L.getD l (0, 0))
        else acc) a ∈ Hj ∧
      burnsideJ4NP_encJ (S.foldl (fun acc l => if m.testBit l then
        acc * burnsideJ4NP_treeElt (L.getD l (0, 0)) else acc) a) =
        S.foldl (fun acc l => if m.testBit l then acc * cc (L.getD l (0, 0)) else acc) c from
    h _ (fun l hl => List.mem_range.1 hl) 1 1 Hj.one_mem burnsideJ4NP_encJ_one
  intro S
  induction S with
  | nil => intro _ a c ha hc; exact ⟨ha, hc⟩
  | cons l S ih =>
    intro hS a c ha hc
    have hl : l < L.length := hS l List.mem_cons_self
    have hlH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK hL _ (burnsideJ4NP_getD_mem hl))
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hb : m.testBit l
    · simp only [hb, if_true]
      refine ih (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl')) _ _ (Hj.mul_mem ha hlH) ?_
      rw [burnsideJ4NP_encJ_mul ha hlH, hc,
        burnsideJ4NP_encJ_treeElt (burnsideJ4NP_m4_coordsOK hL _ (burnsideJ4NP_getD_mem hl))]
    · simp only [hb]
      exact ih (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl')) _ _ ha hc

theorem burnsideJ4NP_m4_coordSub_eq_of_yOK {y w : List (ℕ × ℕ)} {yin os : List ℕ}
    (hy : coordsOK y = true) (hw : coordsOK w = true) (h : yOK y w yin os = true) :
    burnsideJ4NP_coordSub y =
      Subgroup.closure ((fun o => burnsideJ4NP_maskElt w o) '' {o | o ∈ os}) := by
  unfold yOK yCore at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hsub, -⟩, hyi⟩, hos⟩ := h
  apply le_antisymm
  · rw [burnsideJ4NP_coordSub, Subgroup.closure_le]
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    obtain ⟨h1, h2⟩ := hyi i hi
    have hpH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK hy _ (List.getElem_mem hi))
    have e : burnsideJ4NP_treeElt y[i] = burnsideJ4NP_maskElt w (yin.getD i 0) := by
      refine burnsideJ4NP_encJ_inj hpH (burnsideJ4NP_m4_encJ_maskElt hw _).1 ?_
      rw [(burnsideJ4NP_m4_encJ_maskElt hw _).2,
        burnsideJ4NP_encJ_treeElt (burnsideJ4NP_m4_coordsOK hy _ (List.getElem_mem hi)),
        ← List.getD_eq_getElem y (0, 0) hi]
      exact h1
    rw [SetLike.mem_coe, e]
    exact Subgroup.subset_closure ⟨_, List.contains_iff_mem.mp h2, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨o, ho, rfl⟩
    rw [SetLike.mem_coe, burnsideJ4NP_m4_mem_coordSub_iff hy hsub
      (burnsideJ4NP_m4_encJ_maskElt hw o).1, (burnsideJ4NP_m4_encJ_maskElt hw o).2]
    exact hos o ho


theorem burnsideJ4NP_m4_Y136_eq_col :
    burnsideJ4NP_m4Y136 = Subgroup.closure
      ((fun o => eta (burnsideJ4NP_colBasis 136) (treeWv 136).length o) ''
        {o | o ∈ [2, 8, 10, 16, 18, 24, 26, 128, 130, 136, 138, 144, 146, 152, 154]}) := by
  obtain ⟨-, -, -, -, -, hy, -, -, hw, -, -, -, -, h, -⟩ := burnsideJ4NP_m4_codeChecks_parts
  simp only [burnsideJ4NP_m4_eta_colBasis]
  exact burnsideJ4NP_m4_coordSub_eq_of_yOK hy hw h

theorem burnsideJ4NP_m4_Y266_eq_col :
    burnsideJ4NP_m4Y266 = Subgroup.closure
      ((fun o => eta (burnsideJ4NP_colBasis 266) (treeWv 266).length o) ''
        {o | o ∈ [31, 36, 59, 76, 83, 104, 119, 139, 148, 175, 176, 199, 216, 227, 252]}) := by
  obtain ⟨-, -, -, -, -, -, hy, -, -, hw, -, -, -, -, h⟩ := burnsideJ4NP_m4_codeChecks_parts
  simp only [burnsideJ4NP_m4_eta_colBasis]
  exact burnsideJ4NP_m4_coordSub_eq_of_yOK hy hw h

end Y0

@[expose] def burnsideJ4NP_m4Ids : List ℕ := [136, 266, 486, 539, 542]

section Verdicts2


theorem burnsideJ4NP_verdictW_m4_136
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv 136) :=
  burnsideJ4NP_verdictW_m4_136_of_normalizer h539
    (by rw [burnsideJ4NP_m4_Y136_eq_col]; exact burnsideJ4NP_normalizer_le_union136)

theorem burnsideJ4NP_verdictW_m4_266
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv 266) :=
  burnsideJ4NP_verdictW_m4_266_of_normalizer h539
    (by rw [burnsideJ4NP_m4_Y266_eq_col]; exact burnsideJ4NP_normalizer_le_union266)

theorem burnsideJ4NP_verdictW_m4Ids
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    ∀ k ∈ burnsideJ4NP_m4Ids, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv k) := by
  intro k hk
  simp only [burnsideJ4NP_m4Ids, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact burnsideJ4NP_verdictW_m4_136 h539
  · exact burnsideJ4NP_verdictW_m4_266 h539
  · exact burnsideJ4NP_verdictW_m4_486 h539
  · exact burnsideJ4NP_verdictW_m4_539 h539
  · exact burnsideJ4NP_verdictW_m4_542 h539

theorem burnsideJ4NP_verdictWH_m4Ids
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    ∀ k ∈ burnsideJ4NP_m4Ids, burnsideJ4NP_VerdictWH (burnsideJ4NP_Wv k) := fun k hk =>
  burnsideJ4NP_verdictWH_of_verdictW (burnsideJ4NP_verdictW_m4Ids h539 k hk)

end Verdicts2

end CFSG.ASVolI
