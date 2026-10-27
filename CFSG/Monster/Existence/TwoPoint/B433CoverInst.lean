module

public import CFSG.YGroups.DCE.B433Check
public import CFSG.Monster.Existence.TwoPoint.B433Cover
public import CFSG.Monster.Existence.TwoPoint.B433CoverNodes
public import CFSG.Monster.Existence.TwoPoint.B433CoverLinkInputs

public section

namespace CFSG.Monster.Existence.B433Cover

open CFSG.YGroups CFSG.YGroups.DCE CFSG.YGroups.DCE.B433 CFSG.YGroups.DCE.B433Native
  CFSG.Monster.B.Co2
open CFSG.Certificates.CosetEnumeration (evalWord)

theorem exists_cover_of_finalOK
    {C : B.CtxB} {X0 : Array ℕ} (hG : Good X0) (hC : CtxGood C)
    (pt : ℕ → Pts X0) (hpt0 : pt 0 = basePt X0) (hact : ActSpec C pt) (hnodes : NodesOK C)
    (hactAll : ∀ (σ : ByteArray) (e : YGroup 4 3 2), RepB 31671 σ (rho432F e) → ∀ p < C.N,
      B.u32get (C.actAll σ) p < C.N ∧ pt (B.u32get (C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Pts X0, ∃ p < C.N, pt p = ω) (bound : ℕ) (prog : Array B.Ins)
    (fins : Array (ℕ × B.NodeFin))
    (h : (env hG hC pt hpt0 hact hnodes).finalOK prog fins 4089470473293004800 bound = true)
    (g : B433) :
    ∃ l < fins.size, ∃ a ∈ psi.range, ∃ b ∈ psi.range,
      g = a * xNode hG pt C.nodes fins[l]!.1 * b :=
  exists_doubleCoset_of_finalOK (env hG hC pt hpt0 hact hnodes) (setup hG) (n := 31671) hC.n_eq
    rho432F pt (xNode hG pt C.nodes)
    (fun j a hW => hW)
    (fun i p k a hV => ⟨hV.1, by obtain ⟨e, -, he⟩ := hV.2; exact ⟨e, he⟩⟩)
    hactAll hpt (by rw [xNode_zero]; exact Subgroup.one_mem _)
    4089470473293004800 bound closure_psi_t prog fins h g

theorem exists_cover_of_checked
    {L : Array ByteArray} {O : BigOmega} {cert : B.Cert}
    (S : Checked L O cert) {bound : ℕ} (h : S.finalCheck 4089470473293004800 bound = true)
    (g : B433) :
    ∃ l < cert.fins.size, ∃ a ∈ psi.range, ∃ b ∈ psi.range,
      g = a * xNode S.good S.pt (nodesOf O L cert.words) cert.fins[l]!.1 * b :=
  exists_cover_of_finalOK S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK S.actAllSpec
    S.ptSurj bound cert.prog cert.fins h g

@[expose] noncomputable def xB : ℕ → B433 := nodeProd (fun l => psi (yGen 4 3 2 l)) tB

theorem xB_zero : xB 0 = 1 := nodeProd_zero _ _

theorem xB_one : xB 1 = tB := nodeProd_one _ _

theorem xB_eq {j : ℕ} (hj : 0 < j) (hj' : j < 23) :
    xB j = xB (nodeParent j) *
      (psi (evalWord (yGen 4 3 2) (nodeWord j)) * tB *
        (psi (evalWord (yGen 4 3 2) (nodeWord j)))⁻¹) := by
  rw [xB, nodeProd_eq _ _ hj hj', ← map_evalWord psi (yGen 4 3 2)]

theorem nodeArr_getElem? {j : ℕ} (hj : j < 23) :
    nodeArr[j]? = some (nodeParent j, (nodeWord j).toArray) := by
  have hj' : j < nodeData.length := by rw [nodeData_length]; exact hj
  simp [nodeArr, nodeParent, nodeWord, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']

theorem xNode_eq_xB
    {L : Array ByteArray} {O : BigOmega} {cert : B.Cert} (S : Checked L O cert)
    (hw : cert.words = nodeArr) {j : ℕ} (hj : j < 23) :
    xNode S.good S.pt (nodesOf O L cert.words) j = xB j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [xNode_zero, xB_zero]
    · have hpar : nodeParent j < j := nodeParent_lt j hj hj0
      have hn : (nodesOf O L cert.words)[j]? =
          some (nodeParent j, O.act (wordB L (nodeWord j).toArray) 0) := by
        rw [hw, nodesOf, Array.getElem?_map, nodeArr_getElem? hj]
        rfl
      have hN : 0 < O.N := by rw [S.N_eq]; norm_num
      have hrep := wordB_rep (fun l hl => S.letters_rep hl) (nodeWord j).toArray
        (fun l hl => nodeWord_lt j hj l (by simpa using hl))
      obtain ⟨-, hpt⟩ := S.act_pt hrep hN
      rw [S.pt_zero] at hpt
      rw [xNode_eq S.good S.pt _ hj0 hn hpar, xB_eq hj0 hj, ih _ hpar (hpar.trans hj),
        (setup S.good).T_eq_of_smul (evalWord (yGen 4 3 2) (nodeWord j)) _ hpt.symm]
      rfl

theorem exists_cover_of_checked_explicit
    {L : Array ByteArray} {O : BigOmega} {cert : B.Cert}
    (S : Checked L O cert) (hw : cert.words = nodeArr) (hs : cert.fins.size = 23)
    (hf : ∀ l < 23, cert.fins[l]!.1 = l) {bound : ℕ}
    (h : S.finalCheck 4089470473293004800 bound = true) (g : B433) :
    ∃ l < 23, ∃ a ∈ psi.range, ∃ b ∈ psi.range, g = a * xB l * b := by
  obtain ⟨l, hl, a, ha, b, hb, hg⟩ := exists_cover_of_checked S h g
  rw [hs] at hl
  refine ⟨l, hl, a, ha, b, hb, ?_⟩
  rw [hg, hf l hl, xNode_eq_xB S hw hl]

end CFSG.Monster.Existence.B433Cover
