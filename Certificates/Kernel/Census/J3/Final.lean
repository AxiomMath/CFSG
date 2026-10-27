module

public import Certificates.Kernel.Census.J3.Bind
public import Certificates.Kernel.Census.J3.T
public import Certificates.Kernel.Census.J3.U
public import Certificates.Kernel.Census.J3.W0
public import Certificates.Kernel.Census.J3.W1
public import Certificates.Kernel.Census.J3.W2
public import Certificates.Kernel.Census.J3.W3
public import Certificates.Kernel.Census.J3.W4
public import Certificates.Kernel.Census.J3.E0
public import Certificates.Kernel.Census.J3.E1
public import Certificates.Kernel.Census.J3.E2
public import Certificates.Kernel.Census.J3.E3
public import Certificates.Kernel.Census.J3.N0
public import Certificates.Kernel.Census.J3.N1
public import Certificates.Kernel.Census.J3.N2
public import Certificates.Kernel.Census.J3.N3
public import Certificates.Kernel.Census.J3.N4
public import Certificates.Kernel.Census.J3.N5
public import Certificates.Kernel.Census.J3.N6
public import CFSG.Certificates.Kernel.Census.ConjFNodeSound
public import CFSG.Certificates.Kernel.Census.ConjSound
public import CFSG.Certificates.Kernel.Census.ExcSound
public import CFSG.Certificates.Kernel.Census.PidProof
public import CFSG.Certificates.Kernel.Census.XsProof
public import CFSG.Certificates.Kernel.Common.ForallChunks
import all Certificates.Kernel.Census.J3.Data
import all Certificates.Kernel.Census.J3.Words
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3W
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3Tests
import all CFSG.Sporadic.Schreier.PairJ3CertInputs
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedConjF
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Census.ConjFSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel

public section

namespace CertificateChecks.KernelCensus.J3

open CFSG.KC.Census CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.J3
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CertificateChecks.KernelCensus
open CFSG.RankThree.Native

set_option maxRecDepth 1000000

#kc_forall_chunks words_c (fun k => (List.range' (30 * k) 30).all wordF = true) 10
  CertificateChecks.KernelCensus.J3.kW 30

#kc_forall_chunks eb_c (fun c => ((j3EB.drop (0 + c * 2)).take 2).all ebF = true) 31
  CertificateChecks.KernelCensus.J3.kE 2

#kc_forall_chunks nodes_c (fun c => (List.range' (0 + c * 4) 4).all nodeF = true) 52
  CertificateChecks.KernelCensus.J3.kN 4

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem getElem!_mem {α : Type} [Inhabited α] {a : Array α} {k : Nat} (hk : k < a.size) :
    a[k]! ∈ a.toList := by
  rw [getElem!_pos a k hk]
  exact Array.getElem_mem_toList hk

theorem us_ok : (j3Us.toList.zip j3Im).all
    (fun ua => Nat.beq (ppcA 6156 13 j3Xs ua.2) ua.1) = true :=
  zip_all_of_chunks (L := 5) (C := 12) (Nat.le_of_ble_eq_true (by quickRfl)) fun c hc => by
    interval_cases c
    exacts [kU0, kU1, kU2, kU3, kU4, kU5, kU6, kU7, kU8, kU9, kU10, kU11]

theorem us_valid {x : Nat} (hx : x ∈ j3Us.toList) :
    canon1 6156 13 x = true ∧ pvalid 6156 13 x = true := by
  have h := List.all_eq_true.1 kUsV x hx
  simpa only [Bool.and_eq_true] using h

theorem basis_valid {i : Nat} (hi : i < j3Bases.size) : ∀ k < j3Bases[i]!.size,
    canon1 6156 13 (j3Bases[i]!)[k]! = true ∧ pvalid 6156 13 (j3Bases[i]!)[k]! = true := by
  intro k hk
  have hb := List.all_eq_true.1 kBM _ (getElem!_mem hi)
  have hx := List.all_eq_true.1 hb _ (getElem!_mem hk)
  obtain ⟨y, hy, he⟩ := List.any_eq_true.1 hx
  rw [Nat.eq_of_beq_eq_true he]
  exact us_valid hy

theorem words_ok : pxsOK 6156 13 lettersP j3XE j3XW = true := by
  have h : ∀ k < j3XE.size, wordF k = true := by
    intro k hk
    rw [Nat.eq_of_beq_eq_true kXES] at hk
    have hk' : k / 30 < 10 := by omega
    exact List.all_eq_true.1 (words_c (k / 30) hk') k (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  unfold pxsOK
  exact List.all_eq_true.2 fun k hk => h k (List.mem_range.1 hk)

theorem letter_valid {i : Nat} (hi : i < lettersP.size) :
    canon1 6156 13 lettersP[i]! = true ∧ pvalid 6156 13 lettersP[i]! = true := by
  have h := List.all_eq_true.1 kL _ (getElem!_mem hi)
  simpa only [Bool.and_eq_true] using h

theorem x_valid (P : Nat) (h : inXP P = true) :
    canon1 6156 13 P = true ∧ pvalid 6156 13 P = true := by
  unfold inXP pinXL at h
  obtain ⟨x, hx, he⟩ := List.any_eq_true.1 h
  rw [Nat.eq_of_beq_eq_true he]
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk' : k < j3XE.size := by simpa using hk
  have hw := List.all_eq_true.1 words_ok k (List.mem_range.2 hk')
  simp only [Bool.and_eq_true, List.all_eq_true] at hw
  rw [Array.getElem_toList, ← getElem!_pos j3XE k hk', Nat.eq_of_beq_eq_true hw.2]
  refine pvalid_pprod_proved (by norm_num) (by norm_num) (by norm_num) fun y hy => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  exact letter_valid (by simpa using hw.1 i hi)

theorem eb_ok : j3EB.all ebF = true := by
  have hl : j3EB.length = 62 := Nat.eq_of_beq_eq_true kEBL
  have h := all_blocks (B := 2) (C := 31) (a := 0) (l := j3EB) (f := ebF) eb_c (by omega)
  simpa using h

theorem ents_ok {i : Nat} (hi : j3EL.any (fun t => t.1 == i) = true) :
    pentsOK 6156 13 j3Bases cNL j3Us j3Cs j3Cs j3Ents[i]! i = true := by
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.1 hi
  rw [beq_iff_eq] at hti
  subst hti
  have hk := List.all_eq_true.1 kEL t ht
  simp only [Bool.and_eq_true] at hk
  refine pentsOK_of_blocks (L := t.2.1) (C := t.2.2) hk.1 (Nat.le_of_ble_eq_true hk.2)
    fun c hc => ?_
  have hm : (t.1, c * t.2.1, t.2.1) ∈ j3EB :=
    List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩⟩
  exact List.all_eq_true.1 eb_ok _ hm

theorem kNS' : j3Conj.nodes.size = 208 ∧ j3Bases.size = 208 ∧ j3Aux.size = 208 := by
  have h := kNS
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.1, Nat.eq_of_beq_eq_true h.1.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

theorem bases_eq : j3Conj.nodes.map NodeP.basis = j3Bases := by decide +kernel

theorem cNL_eq : cNL = j3Bases.map (pmaskCert 6156 13) := by
  apply Array.ext'
  simp [cNL]

theorem cN_eq : pcN 6156 13 j3Conj.nodes = cNL := by
  unfold pcN
  rw [show (fun nd : NodeP => pmaskCert 6156 13 nd.basis) = pmaskCert 6156 13 ∘ NodeP.basis
    from rfl, ← Array.map_map, bases_eq, cNL_eq]

theorem nodes_F : ∀ i < 208, nodeF i = true :=
  allRange_blocks (a := 0) (L := 4) (C := 52) (allRange_zero _) nodes_c

theorem nodes_ok : ∀ i < j3Conj.nodes.size, pnodeOKC 6156 13 j3PS inXP (fun _ => true)
    (fun _ => false) false false false j3Conj (pcN 6156 13 j3Conj.nodes) #[] i = true := by
  obtain ⟨hns, hbs, has⟩ := kNS'
  rw [cN_eq, hns]
  intro i hi
  have hF := nodes_F i hi
  have hps : psL = j3PS := rfl
  unfold nodeF at hF
  rw [hps] at hF
  simp only [Bool.and_eq_true] at hF
  have hb := basis_valid (i := i) (by omega)
  have hbi : j3Conj.nodes[i]!.basis = j3Bases[i]! := by
    rw [← getElem!_map_lt j3Conj.nodes NodeP.basis (by omega), bases_eq]
  have hci : cNL[i]! = pmaskCert 6156 13 j3Bases[i]! := by
    rw [cNL_eq, getElem!_map_lt _ _ (by omega)]
  have ha : canon1 6156 13 j3Aux[i]!.1 = true ∧ canon1 6156 13 j3Aux[i]!.2 = true := by
    have := List.all_eq_true.1 kAux _ (getElem!_mem (a := j3Aux) (k := i) (by omega))
    simpa only [Bool.and_eq_true] using this
  have hE := penumF_sound (by norm_num) (by norm_num) (by norm_num) hb hF.1
  have hW := pwitF_sound (by norm_num) (by norm_num) (by norm_num) x_valid hb ha hF.2
  refine pnodeOKC_of_q ?_ fun hm => ?_
  · rw [hbi, hci]
    rw [hci] at hW
    cases hmono : j3Conj.nodes[i]!.wit.isMono <;>
      simp only [hE, hW, Bool.true_and, cond_true, cond_false, Bool.true_or]
  · have he := List.all_eq_true.1 kMono i (List.mem_range.2 hi)
    rw [hm, Bool.false_or] at he
    rw [bases_eq]
    exact ents_ok he

theorem letters_eq : j3Letters j3Si = lettersP.map (unpackP 6156 13) := by
  unfold j3Letters lettersP
  rw [Array.map_append]
  congr 1
  apply Array.ext (by simp [j3StrongArrs])
  intro k h1 h2
  have hk : k < 5 := by simpa [j3StrongArrs] using h1
  rw [← getElem!_pos j3StrongArrs k h1, strong_eq hk, Array.getElem_map]
  interval_cases k <;> rfl

theorem si_size : j3Si.size = 5 := Nat.eq_of_beq_eq_true kSiS

theorem si_canon {k : Nat} (hk : k < 5) : canon1 6156 13 j3Si[k]! = true := by
  have hm : j3Si[k]! ∈ lettersP.toList := by
    rw [lettersP, Array.toList_append]
    exact List.mem_append_right _ (getElem!_mem (by rw [si_size]; exact hk))
  have h := List.all_eq_true.1 kL _ hm
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem xs_canon : j3Xs.all (canon1 6156 13) = true := by
  have h := kCanon
  simp only [canonC, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

theorem hU : j3UArr = unpackP 6156 13 (J3UT.F 0) := j3UArr_eq

theorem kU' : canon1 6156 13 (J3UT.F 0) = true ∧ pvalid 6156 13 (J3UT.F 0) = true := by
  simpa only [Bool.and_eq_true] using kU

theorem c_u : isInvA 6156 j3UArr (invCand 6156 j3UArr) = true := by
  rw [hU]
  exact validA_unpackP_proved (by norm_num) (by norm_num) kU'.1 kU'.2

theorem c_si : (allLt 5 fun k =>
    eqA 6156 (compA 6156 (j3Si.map (unpackP 6156 13))[k]! j3StrongArrs[k]!) (idA 6156)) = true := by
  have hid := unpackP_pid_proved (n := 6156) (w := 13) (by norm_num) (by norm_num)
  rw [allLt_iff]
  intro k hk
  rw [getElem!_map_lt _ _ (by rw [si_size]; exact hk), strong_eq hk,
    ← unpackP_pc (by norm_num) (by norm_num) (si_canon hk), ← hid.1,
    eqA_unpackP (by norm_num) (by norm_num) (canon1_pc (by norm_num) (by norm_num)) hid.2]
  exact List.all_eq_true.1 kSi k (List.mem_range.2 hk)

theorem c_val : (allLt (j3Letters j3Si).size fun k => validA 6156 (j3Letters j3Si)[k]!) = true := by
  rw [letters_eq, allLt_iff]
  intro k hk
  rw [getElem!_map_lt _ _ (by simpa using hk)]
  have h := letter_valid (i := k) (by simpa using hk)
  exact validA_unpackP_proved (by norm_num) (by norm_num) h.1 h.2

theorem c_xs : xsOK 6156 (j3Letters j3Si) (j3XE.map (unpackP 6156 13)) j3XW = true := by
  rw [letters_eq]
  refine xsOK_of_pxsOK_proved (by norm_num) (by norm_num) (by norm_num)
    (List.all_eq_true.2 fun x hx => ?_) kXE words_ok
  have h := List.all_eq_true.1 kL x hx
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem c_inv : pinvOK 6156 13 j3Xs j3Us j3Im j3Wt = true := by
  have hl := kInvL
  simp only [Bool.and_eq_true] at hl
  unfold pinvOK
  rw [kWalk, hl.1, hl.2, us_ok]
  rfl

theorem c_pc : ppcOK 6156 13 j3Xs j3Rs j3Cjs j3Bs = true :=
  ppcOK_of_heads _ _ _ _ fun k hk => by
    have h8 : j3Xs.length = 8 := Nat.eq_of_beq_eq_true kXsL
    rw [h8] at hk
    interval_cases k
    exacts [kH0, kH1, kH2, kH3, kH4, kH5, kH6, kH7, kH8]

theorem c_roots : (j3Conj.us.toList.zip j3Conj.roots).all (fun ur => prootOKC 6156 13
    (j3Conj.nodes.map NodeP.basis) (pcN 6156 13 j3Conj.nodes) j3Conj.cs j3Conj.ci ur.1 ur.2) =
      true := by
  rw [bases_eq, cN_eq]
  exact kRoots

theorem c_census : conjCensusOKW 6156 j3PS (inXL 6156 (j3XE.map (unpackP 6156 13)))
    (fun _ => true) (fun _ => false) false false false (j3Conj.toMain 6156 13) #[] = true := by
  have hc := pconjCensus_sound_proved (ps := j3PS) (allowPW := false) (allowInX := false)
    (allowU := false) (d := j3Conj) (e0 := #[]) (inX := inXL 6156 (j3XE.map (unpackP 6156 13)))
    (outX := fun _ => true) (inW := fun _ => false) (by norm_num) (by norm_num) (by norm_num)
    kCanon rfl (fun P hP _ => pinXL_eq hP kXE) (fun _ _ _ => rfl) (fun _ _ _ => rfl) c_pc c_inv
    kTab kRL c_roots nodes_ok
  rw [Array.map_empty] at hc
  exact hc

theorem inX_eq {x : Nat} (hxc : canon1 6156 13 x = true) :
    inXL 6156 (j3XE.map (unpackP 6156 13)) (unpackP 6156 13 x) = inXP x :=
  (pinXL_eq hxc kXE).symm

theorem u_comp {x : Nat} :
    compA 6156 j3UArr (unpackP 6156 13 x) = unpackP 6156 13 (pc 6156 13 (J3UT.F 0) x) := by
  rw [hU, unpackP_pc (by norm_num) (by norm_num) kU'.1]

theorem gen_of {xs : List Nat} (hc : xs.all (canon1 6156 13) = true)
    (h : xs.all (fun x => inXP x || inXP (pc 6156 13 (J3UT.F 0) x)) = true) :
    (xs.map (unpackP 6156 13)).all (fun a =>
      inXL 6156 (j3XE.map (unpackP 6156 13)) a ||
        inXL 6156 (j3XE.map (unpackP 6156 13)) (compA 6156 j3UArr a)) = true := by
  refine List.all_eq_true.2 fun a ha => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  have hxc := List.all_eq_true.1 hc x hx
  have h1 := List.all_eq_true.1 h x hx
  rw [inX_eq hxc, u_comp, inX_eq (canon1_pc (by norm_num) (by norm_num))]
  exact h1

theorem toMain_xs : (j3Conj.toMain 6156 13).xs = j3Xs.map (unpackP 6156 13) := rfl

theorem c_gen : (j3Conj.toMain 6156 13).xs.all (fun a =>
    inXL 6156 (j3XE.map (unpackP 6156 13)) a ||
      inXL 6156 (j3XE.map (unpackP 6156 13)) (compA 6156 j3UArr a)) = true := by
  rw [toMain_xs]
  exact gen_of xs_canon kXs

theorem c_len : (j3Conj.toMain 6156 13).xs.length = 8 := by
  rw [toMain_xs, List.length_map]
  exact Nat.eq_of_beq_eq_true kXsL

theorem j3_ok : ∃ (si xe : Array ℕ) (ws : List (List ℕ)) (d : ConjDataP),
    j3CheckW si xe ws d = true := by
  refine ⟨j3Si, j3XE, j3XW, j3Conj, ?_⟩
  unfold j3CheckW
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨c_u, si_size⟩, c_si⟩, c_val⟩, c_xs⟩, c_census⟩, c_gen⟩, c_len⟩

end CertificateChecks.KernelCensus.J3

end
