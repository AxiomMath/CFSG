
module

public import Certificates.Kernel.Co1ThreeK.QModelSound
public import Certificates.Kernel.Co1ThreeK.LettersEq
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KS.SporSch.M24
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (lG wG lG_mem)

section Letters

theorem lRows_repK : List.Forall₂ MRep (Co1T.Native.lRows ()) lG := by
  have hflag : (Co1T.Native.sDag ()).2.2 = true := by rw [sDag_eq]
  unfold Co1T.Native.lRows lG
  refine List.rel_append (List.rel_append ?_ ?_) ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun i _ => W_rep _
  · exact List.Forall₂.cons (g_rep 0) (List.Forall₂.cons (g_rep 1)
      (List.Forall₂.cons (g_rep 2) List.Forall₂.nil))
  · exact dag_rep (List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil)) _ hflag

theorem lRows_listRepK : ListRep (Co1T.Native.lRows ()) (Co1T.Native.lInvs ()) lG := by
  refine ⟨lRows_repK, ?_⟩
  have hinv : ∀ x ∈ Co1T.Native.lRows (), Native.mul x (Native.inv x) = Native.one () := by
    intro x hx
    rw [lRows_eq, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨hm, hi'⟩ := invOKW_sound (invL (List.mem_range.1 hi))
    rw [hi', hm]
  unfold Co1T.Native.lInvs
  have key : ∀ (rs : List Native.Rows) (gs : List GL24), List.Forall₂ MRep rs gs →
      (∀ x ∈ rs, Native.mul x (Native.inv x) = Native.one ()) →
      List.Forall₂ (fun I g => MRep I g⁻¹) (rs.map Native.inv) gs := by
    intro rs gs h
    induction h with
    | nil => intro _; exact List.Forall₂.nil
    | cons hab _ ih =>
      intro hall
      exact List.Forall₂.cons (hab.inv (hall _ List.mem_cons_self))
        (ih fun x hx => hall x (List.mem_cons_of_mem _ hx))
  exact key _ _ lRows_repK hinv

theorem wordL_repK (w : List ℕ) : MRep (Co1T.Native.wordL w) (wG w : GL24) :=
  MRep.word lRows_listRepK _

theorem matK_wordWK {w : List Nat} (h : lettersK 75 w = true) :
    matK (wordWK L.M L.MI w) = ((wG w : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  rw [← mRep_iff, unpackR_eq_unpack, ← wordL_eq h]
  exact wordL_repK w

theorem matK_RM {j : Nat} (hj : j < 3) :
    matK (R.M j) = ((Co1T.root j : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  obtain ⟨h1, h2, -⟩ := rootK hj
  rw [← Nat.eq_of_beq_eq_true h2, matK_wordWK h1]
  rfl

theorem matK_LM {k : Nat} (hk : k < 75) :
    matK (L.M k) = ((lG.getD k 1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have h := getD_rep lRows_repK MRep.one k
  rw [lRows_eq, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range] at h
  rw [← mRep_iff, unpackR_eq_unpack]
  exact h

end Letters

@[expose] noncomputable def ιK : ↥GA →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))).comp GA.subtype

theorem ιK_injective : Function.Injective ιK := fun _ _ h => Subtype.ext (Units.ext h)

@[expose] noncomputable def aK (i : Nat) (hi : i < 6) : ↥GA :=
  ⟨a ⟨i, hi⟩, A_le_GA (Subgroup.subset_closure (Set.mem_union_left _ (a_mem_E _)))⟩

theorem lG_getD_a {i : Nat} (hi : i < 6) : lG.getD i 1 = a ⟨i, hi⟩ := by
  interval_cases i <;> rfl

section Nodes

theorem seedsK : (Nat.beq CS.T.length 39 && allN 9 (fun k => Nat.beq (TS k) (L.M k)) &&
    lettersK 75 (Co1T.Data.qGenWords.getD 6 []) && lettersK 75 (Co1T.Data.qGenWords.getD 7 []) &&
    Nat.beq (TS 9) (wordWK L.M L.MI (Co1T.Data.qGenWords.getD 6 [])) &&
    Nat.beq (TS 10) (wordWK L.M L.MI (Co1T.Data.qGenWords.getD 7 [])) &&
    Nat.beq (TS 11) oneK && Nat.beq oneK idM && canAllK TS 12) = true := kSeeds

theorem TS_LM {k : Nat} (hk : k < 9) : TS k = L.M k := by
  have h := seedsK
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true (MatL.allN_iff.1 h.1.1.1.1.1.1.1.2 k hk)

theorem nodeK_ex : ∀ k < 39, ∃ g : ↥GA, matK (TS k) = ιK g := by
  have h := seedsK
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h6⟩, h7⟩, h9⟩, h10⟩, h11⟩, -⟩, -⟩ := h
  have hseed : ∀ k < 12, ∃ g : ↥GA, matK (TS k) = ιK g := by
    intro k hk
    rcases (by omega : k < 9 ∨ k = 9 ∨ k = 10 ∨ k = 11) with hk9 | rfl | rfl | rfl
    · refine ⟨⟨lG.getD k 1, getD_mem_of_forall lG_mem k⟩, ?_⟩
      rw [TS_LM hk9, matK_LM (by omega)]
      rfl
    · refine ⟨wG (Co1T.Data.qGenWords.getD 6 []), ?_⟩
      rw [Nat.eq_of_beq_eq_true h9, matK_wordWK h6]
      rfl
    · refine ⟨wG (Co1T.Data.qGenWords.getD 7 []), ?_⟩
      rw [Nat.eq_of_beq_eq_true h10, matK_wordWK h7]
      rfl
    · refine ⟨1, ?_⟩
      rw [Nat.eq_of_beq_eq_true h11, matK_oneK, map_one]
  have hT := kQTab
  simp only [Bool.and_eq_true] at hT
  have hP := kProg
  simp only [Bool.and_eq_true] at hP
  have hlen : CS.W.length = 27 := Nat.eq_of_beq_eq_true hP.1
  have hcos : ∀ l < 27, ∃ g : ↥GA, matK (TS (12 + l)) = ιK g := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro hl
      rcases (tabQK_spec hT.2 (k := 0) (by norm_num) hl).2 with ⟨rfl, -⟩ | ⟨-, h0, h3, hi, hj, -⟩
      · exact hseed 11 (by norm_num) |>.imp fun g hg => by
          rw [Nat.eq_of_beq_eq_true hT.1]
          rw [Nat.eq_of_beq_eq_true h11] at hg
          exact hg
      · have hr := runK_sound hP.2 l (by omega)
        rw [← CFSG.KC.Co1Cl.getL_eq] at hr
        have e := recK_mul hr h0
        have hS : ([9, 10, 11] : List Nat).length = 3 := rfl
        rw [hS] at e
        have e1 : refK [9, 10, 11] 3 12 (Nat.land (Nat.shiftRight (getL 0 CS.W l) 1) 1048575) =
            12 + (Nat.land (Nat.shiftRight (getL 0 CS.W l) 1) 1048575 - 3) := by
          unfold refK
          rw [nrec_eq, if_neg (by rw [Nat.blt_eq]; omega)]
          rfl
        have e2 : refK [9, 10, 11] 3 12 (Nat.shiftRight (getL 0 CS.W l) 21) =
            9 + Nat.shiftRight (getL 0 CS.W l) 21 := by
          unfold refK
          rw [nrec_eq, if_pos (by rw [Nat.blt_eq]; omega)]
          generalize Nat.shiftRight (getL 0 CS.W l) 21 = j at hj ⊢
          interval_cases j <;> rfl
        rw [e1, e2] at e
        obtain ⟨g, hg⟩ := ih _ hi (by omega)
        obtain ⟨g', hg'⟩ := hseed (9 + Nat.shiftRight (getL 0 CS.W l) 21) (by omega)
        exact ⟨g * g', by rw [e, matK_mulWK, hg, hg', map_mul]⟩
  intro k hk
  rcases Nat.lt_or_ge k 12 with h12 | h12
  · exact hseed k h12
  · have := hcos (k - 12) (by omega)
    rwa [Nat.add_sub_cancel' h12] at this

@[expose] noncomputable def nodeK (k : Nat) : ↥GA :=
  if h : k < 39 then (nodeK_ex k h).choose else 1

theorem matK_nodeK {k : Nat} (h : k < 39) : matK (TS k) = ιK (nodeK k) := by
  unfold nodeK
  rw [dif_pos h]
  exact (nodeK_ex k h).choose_spec

theorem nodeK_eq {k : Nat} (hk : k < 39) (g : ↥GA)
    (h : matK (TS k) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) : nodeK k = g :=
  ιK_injective ((matK_nodeK hk).symm.trans h)

theorem nodeK_a {i : Nat} (hi : i < 6) : nodeK i = aK i hi := by
  refine nodeK_eq (by omega) _ ?_
  rw [TS_LM (by omega), matK_LM (by omega), lG_getD_a hi]
  rfl

theorem nodeK_q {j : Nat} (hj : j < 2) :
    nodeK (9 + j) = wG (Co1T.Data.qGenWords.getD (6 + j) []) := by
  have h := seedsK
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h6⟩, h7⟩, h9⟩, h10⟩, -⟩, -⟩, -⟩ := h
  refine nodeK_eq (by omega) _ ?_
  interval_cases j
  · rw [Nat.eq_of_beq_eq_true h9, matK_wordWK h6]
  · rw [Nat.eq_of_beq_eq_true h10, matK_wordWK h7]

theorem qHypK : QHyp ιK nodeK where
  inj := ιK_injective
  mat := fun k hk => matK_nodeK hk
  comm := by
    intro x hx y hy
    have hx6 : x < 6 := by simp at hx; omega
    have hy6 : y < 6 := by simp at hy; omega
    rw [nodeK_a hx6, nodeK_a hy6]
    exact Subtype.ext (a_comm ⟨x, hx6⟩ ⟨y, hy6⟩)
  cube := by
    intro x hx
    have hx6 : x < 6 := by simp at hx; omega
    rw [nodeK_a hx6]
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact a_pow_three ⟨x, hx6⟩

end Nodes

end CertificateChecks.KernelCo1ThreeK

end
