module

public import Certificates.Kernel.Co2Smith.Root
public import Certificates.Kernel.Co2Smith.F0
public import Certificates.Kernel.Co2Smith.Cent
public import Certificates.Kernel.Co2Smith.U62K
public import Certificates.Kernel.Co2Smith.ChainL1J
public import Certificates.Kernel.Co2Smith.ChainL1K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem distL_pairwise : ∀ l : List Nat, distL l = true → l.Pairwise (· ≠ ·)
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    simp only [distL, Bool.and_eq_true, List.all_eq_true] at h
    refine List.Pairwise.cons (fun b hb e => ?_) (distL_pairwise l h.2)
    have := h.1 b hb
    rw [e, Nat.beq_refl] at this
    exact Bool.noConfusion this

theorem not_beq_of_ne {a b : Nat} (h : a ≠ b) : (!Nat.beq a b) = true := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem dist_of {α : Type} {n : Nat} {A : Array α} {f : α → Nat} (hs : A.size = n)
    (h : distL (A.toList.map fun a => cK (f a)) = true) :
    u62DistOK n (A.map fun a => unpackR 22 (f a)) = true := by
  have hp := List.pairwise_iff_getElem.1 (distL_pairwise _ h)
  have hget : ∀ i (hi : i < A.size), (A.map fun a => unpackR 22 (f a)).getD i #[] =
      unpackR 22 (f A[i]) := fun i hi => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi]
    rfl
  unfold u62DistOK
  simp only [Bool.and_eq_true]
  rw [Array.all_eq_true]
  simp only [beq_iff_eq, Array.size_map, List.all_eq_true, List.mem_range]
  refine ⟨⟨hs, fun i hi => ?_⟩, fun i hi k hk => ?_⟩
  · rw [Array.getElem_map]
    exact validM_unpack _
  · rw [hget i (by omega), hget k (by omega), bne_unpack, eqK]
    refine not_beq_of_ne ?_
    have := hp k i (by simp; omega) (by simp; omega) hk
    simpa using this.symm

theorem invK_spec {ws : List (List Nat)} (h : invK ws = true) :
    (∀ w ∈ ws, ∀ k ∈ w, k < 22) ∧ u62InvOK ws = true := by
  simp only [invK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun w hw => (h w hw).1.1, ?_⟩
  unfold u62InvOK
  simp only [List.all_eq_true, Bool.and_eq_true]
  intro w hw
  obtain ⟨⟨hl, he⟩, hm⟩ := h w hw
  rw [glR_eq hl, mulRows_unpack, idRows_eq, beq_unpack,
    glMaps_unpack _ (by decide) (by decide)]
  exact ⟨he, hm⟩

theorem getD_glR {ws : List (List Nat)} (hw : ∀ w ∈ ws, ∀ k ∈ w, k < 22) (j : Nat) :
    (ws.toArray.map glR).getD j (idRows 22) = unpackR 22 ((ws.map (wK LP)).getD j IDP) := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_toArray, List.getElem?_map]
  cases h : ws[j]? with
  | none => exact idRows_eq
  | some w => exact glR_eq (hw w (List.mem_of_getElem? h))

theorem foldl_unpack {G : Array (Array Nat)} {GK : List Nat}
    (hG : ∀ j, G.getD j (idRows 22) = unpackR 22 (GK.getD j IDP)) :
    ∀ (w : List Nat) (a : Nat),
      w.foldl (fun A j => mulRows 22 A (G.getD j (idRows 22))) (unpackR 22 a) =
        unpackR 22 (w.foldl (fun A j => mulV A (GK.getD j IDP)) a)
  | [], _ => rfl
  | j :: w, a => by
    simp only [List.foldl_cons]
    rw [hG, mulRows_unpack]
    exact foldl_unpack hG w _

theorem wr_unpack {G : Array (Array Nat)} {GK : List Nat}
    (hG : ∀ j, G.getD j (idRows 22) = unpackR 22 (GK.getD j IDP)) (w : List Nat) :
    u62WR G w = unpackR 22 (wrK GK w) := by
  unfold u62WR wrK
  rw [idRows_eq]
  exact foldl_unpack hG w IDP

theorem q_ok : u62QOK = true := by
  have h := q_k
  unfold u62QOK
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h ⊢
  intro j hj
  have hg : glRows.getD (j + 1) #[] = unpackR 22 (LP (j + 1)) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [glRows_size]; omega),
      Option.getD_some, ← getElem!_pos glRows (j + 1) (by rw [glRows_size]; omega),
      glRows_get (by omega)]
  have hq : ∀ c, u62QNFR c = unpackR 22 (qnfK c) := by
    intro c
    unfold u62QNFR qnfK
    have hz : (if c.1 == 1 then glZ else idRows 22) =
        unpackR 22 (if c.1 == 1 then zK else IDP) := by
      split_ifs
      · exact glZ_eq
      · exact idRows_eq
    rw [hz, glRootRows_eq, glRootRows_eq, glRootRows_eq, glRootRows_eq, mulRows_unpack,
      mulRows_unpack, mulRows_unpack, mulRows_unpack]
  rw [hg, hq, eq_unpack_iff]
  exact Nat.eq_of_beq_eq_true (h j hj)

theorem comm_ok : u62CommOK = true := by
  obtain ⟨h61, -⟩ := el_eqs
  unfold u62CommOK
  rw [glZ_eq, h61, mulRows_unpack, mulRows_unpack, validM_unpack, validM_unpack, commRows_unpack]
  exact comm_k

theorem orb_ok : u62OrbOK = true := by
  have h := orb_k
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hi, hs⟩, hd⟩ := h
  obtain ⟨hw, hinv⟩ := invK_spec hi
  have hG : u62G1R = u62G1Words.toArray.map glR := by unfold u62G1R; rfl
  have hf : (fun w => mulRows 22 (mulRows 22 (u62WR u62G1R w) glZ) (u62WR u62G1R w.reverse)) =
      fun w => unpackR 22 (orbK w) := by
    funext w
    rw [hG, wr_unpack (getD_glR hw), wr_unpack (getD_glR hw), glZ_eq, mulRows_unpack,
      mulRows_unpack]
    unfold orbK g1K zK
    rfl
  have hR : u62OrbR = u62Orb.map fun w => unpackR 22 (orbK w) := by
    unfold u62OrbR
    exact congrArg (fun f => u62Orb.map f) hf
  unfold u62OrbOK
  rw [hinv, Bool.true_and, hR]
  exact dist_of hs hd

theorem c1_ok : u62C1OK = true := by
  have h := c1_k
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hi, hc⟩, hs⟩, hd⟩, hl⟩, h6⟩, h7⟩, hf⟩ := h
  obtain ⟨hw, hinv⟩ := invK_spec hi
  have hG : u62C1R = u62C1Words.toArray.map glR := by unfold u62C1R; rfl
  have hwr : u62WR u62C1R = fun w => unpackR 22 (wrK c1K w) := by
    funext w
    rw [hG]
    exact wr_unpack (getD_glR hw) w
  have hE : u62C1E = u62C1.map fun w => unpackR 22 (wrK c1K w) := by
    unfold u62C1E
    exact congrArg (fun f => u62C1.map f) hwr
  have hfr : ((List.range 6).all fun j => glR (u62C1Words.getD j []) ==
      glLongRows (u62C1Frame.getD j 0)) = true := by
    simp only [List.all_eq_true, List.mem_range] at hf ⊢
    intro j hj
    have hm : u62C1Words.getD j [] ∈ u62C1Words := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega)]
      exact List.getElem_mem _
    rw [glR_eq (hw _ hm), glLongRows_eq, beq_unpack]
    exact hf j hj
  have hD : u62DistOK 1296 u62C1E = true := by
    rw [hE]
    exact dist_of hs hd
  unfold u62C1OK
  rw [hinv, hc, hD, hfr]
  simp only [hl, h6, h7, beq_self_eq_true, Bool.and_self]

theorem l1w_ok : (u62L1Words.all (fun w => glMaps (glR w) 80 80 && commRows (glR w) glZ) &&
    u62L1Words.length == 22 && u62L1Words.getD 21 [] == glD0hWord &&
    (List.range 21).all fun i => glR (u62L1Words.getD i []) ==
      glRootRows (u62L1Ids.getD i (0, 0)).1 (u62L1Ids.getD i (0, 0)).2) = true := by
  have h := l1w_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h ⊢
  obtain ⟨⟨⟨hw, hl⟩, h21⟩, hr⟩ := h
  refine ⟨⟨⟨fun w hm => ?_, hl⟩, h21⟩, fun i hi => ?_⟩
  · obtain ⟨⟨hlt, hmp⟩, hc⟩ := hw w hm
    rw [glR_eq hlt, glMaps_unpack _ (by decide) (by decide), glZ_eq, commRows_unpack]
    exact ⟨hmp, hc⟩
  · have hm : u62L1Words.getD i [] ∈ u62L1Words := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega)]
      exact List.getElem_mem _
    rw [glR_eq (hw _ hm).1.1, glRootRows_eq, eq_unpack_iff]
    exact Nat.eq_of_beq_eq_true (hr i hi)

theorem chainL1_ok :
    glChainOK u62L1Words u62L1Base u62L1W 26542080 = true := by
  have hB := chL1Bind_k
  have hO := chL1O_k
  have hC := l1Cent_k
  have hl : u62L1Words.length = 22 := by decide
  have hget : ∀ i < u62L1Words.length, u62L1Words[i]! = u62L1Words.getD i [] := fun i hi => by
    rw [getElem!_pos u62L1Words i hi, List.getD_eq_getElem _ _ hi]
  have hK : ∀ i < u62L1Words.length, permK (CL1.S i) ∈ centX ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 2300)) (0 : Fin 2300) := by
    intro i hi
    have h := allN_spec hC i (by omega)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, hs⟩, hc⟩, h0⟩ := h
    refine Subgroup.mem_inf.2 ⟨mem_centX hp hs hc, ?_⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    apply Fin.ext
    rw [← prep_of_permOK hp 0]
    exact Nat.eq_of_beq_eq_true h0
  have h0 : ∀ g ∈ centX ⊓ MulAction.stabilizer (Equiv.Perm (Fin 2300)) (0 : Fin 2300),
      g 0 = 0 := fun g hg => MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hg).2
  refine chainOK_of_card (D := chL1D) (G := L1GP) (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) CL1.head
    CL1.ho (by norm_num) hK (card_cent0_le inf_le_left h0) (by decide +kernel)
  · have h := allN_spec hB i (by omega)
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rw [hget i hi]
    exact h.1
  · have h := allN_spec hB i (by omega)
    simp only [Bool.and_eq_true] at h
    rw [hget i hi]
    exact h.2
  · exact Nat.eq_of_beq_eq_true (allN_spec hO i (by omega))

theorem u62_ok :
    u62OK = true := by
  have hw := l1w_ok
  simp only [Bool.and_eq_true] at hw
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
  unfold u62OK u62L1OK
  rw [q_ok, comm_ok, chainL1_ok, orb_ok, c1_ok, h1, h2, h3, h4]
  rfl

end CertificateChecks.KernelCo2Smith
