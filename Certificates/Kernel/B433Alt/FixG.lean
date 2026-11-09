module

public import Certificates.Kernel.B433Alt.FixOK
public import Certificates.Data.Kernel.B433Alt.FixF
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
import Certificates.Kernel.B433Alt.KVal

set_option maxRecDepth 100000

public section

namespace CFSG.KD.B4AX

open CFSG.KC.B4A CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def relAF (i : Nat) : Bool :=
  Nat.beq (apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (wList (CFSG.KD.B4A.RW (RS.getD i (0, [])).1)) RP)
    (permPlanes RP (RS.getD i (0, [])).2)

@[expose] noncomputable def relBF (i : Nat) : Bool :=
  Nat.beq (apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (wList (CFSG.KD.B4A.RW (RS.getD i (0, [])).1))
      (ptPlanes RA)) (permPlanes (ptPlanes RA) (RS.getD i (0, [])).2)

theorem relChk_eq_F (i : Nat) : relChk i = andB (relAF i) (relBF i) := by
  unfold relChk relAF relBF
  rw [apP_eq_F]

@[expose] noncomputable def wOf (i : Nat) : List Nat := wList (CFSG.KD.B4A.RW (RS.getD i (0, [])).1)

@[expose] noncomputable def pLen (K i : Nat) : Nat := (wOf i).length / K + 1

@[expose] noncomputable def segS (K i k : Nat) : List Nat :=
  List.take (pLen K i) (List.drop (k * pLen K i) (wOf i))

@[expose] noncomputable def pcS (K i : Nat) (S : List Nat) (k : Nat) : Bool :=
  Nat.beq (apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (segS K i k) (S.getD k 0)) (S.getD (k + 1) 0)

theorem pLen_ok (K i : Nat) (hK : 0 < K) : (wOf i).length ≤ K * pLen K i := by
  unfold pLen
  generalize (wOf i).length = n
  have h1 := Nat.div_add_mod n K
  have h2 := Nat.mod_lt n hK
  rw [Nat.mul_add, Nat.mul_one]
  generalize K * (n / K) = q at h1 ⊢
  generalize n % K = r at h1 h2
  omega

theorem relAF_of (i K : Nat) (S : List Nat) (hK0 : 0 < K) (h0 : S.getD 0 0 = RP)
    (hK : S.getD K 0 = permPlanes RP (RS.getD i (0, [])).2) (h : ∀ k < K, pcS K i S k = true) :
    relAF i = true := by
  unfold relAF
  exact apPF_beq_chain CFSG.KD.YMY432F.Nf (nat_lit 12) (wOf i) (pLen K i) K S RP
    (permPlanes RP (RS.getD i (0, [])).2) h0 hK (pLen_ok K i hK0) h

theorem relBF_of (i K : Nat) (S : List Nat) (hK0 : 0 < K) (h0 : S.getD 0 0 = ptPlanes RA)
    (hK : S.getD K 0 = permPlanes (ptPlanes RA) (RS.getD i (0, [])).2)
    (h : ∀ k < K, pcS K i S k = true) :
    relBF i = true := by
  unfold relBF
  exact apPF_beq_chain CFSG.KD.YMY432F.Nf (nat_lit 12) (wOf i) (pLen K i) K S (ptPlanes RA)
    (permPlanes (ptPlanes RA) (RS.getD i (0, [])).2) h0 hK (pLen_ok K i hK0) h

#b4_kval A1s1 := apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (segS (nat_lit 3) (nat_lit 1) (nat_lit 0)) RP
#b4_kval A1s2 := apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (segS (nat_lit 3) (nat_lit 1) (nat_lit 1)) A1s1
#b4_kval B1s1 := apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (segS (nat_lit 3) (nat_lit 1) (nat_lit 0))
  (ptPlanes RA)
#b4_kval B1s2 := apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (segS (nat_lit 3) (nat_lit 1) (nat_lit 1)) B1s1
#b4_kval A2s1 := apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (segS (nat_lit 2) (nat_lit 2) (nat_lit 0)) RP
#b4_kval B2s1 := apPF CFSG.KD.YMY432F.Nf (nat_lit 12) (segS (nat_lit 2) (nat_lit 2) (nat_lit 0))
  (ptPlanes RA)

@[expose] noncomputable def SA1 : List Nat :=
  [RP, A1s1, A1s2, permPlanes RP (RS.getD (nat_lit 1) (0, [])).2]
@[expose] noncomputable def SB1 : List Nat :=
  [ptPlanes RA, B1s1, B1s2, permPlanes (ptPlanes RA) (RS.getD (nat_lit 1) (0, [])).2]
@[expose] noncomputable def SA2 : List Nat :=
  [RP, A2s1, permPlanes RP (RS.getD (nat_lit 2) (0, [])).2]
@[expose] noncomputable def SB2 : List Nat :=
  [ptPlanes RA, B2s1, permPlanes (ptPlanes RA) (RS.getD (nat_lit 2) (0, [])).2]

end CFSG.KD.B4AX

#bm_range CFSG.KD.B4AX relA 0 1 relAF
#bm_range CFSG.KD.B4AX relB 0 1 relBF
#bm_range CFSG.KD.B4AX pA1_ 0 3 (pcS 3 1 SA1)
#bm_range CFSG.KD.B4AX pB1_ 0 3 (pcS 3 1 SB1)
#bm_range CFSG.KD.B4AX pA2_ 0 2 (pcS 2 2 SA2)
#bm_range CFSG.KD.B4AX pB2_ 0 2 (pcS 2 2 SB2)

namespace CFSG.KD.B4AX

theorem relA1 : relAF (nat_lit 1) = true :=
  relAF_of (nat_lit 1) (nat_lit 3) SA1 (by decide) rfl rfl
    (CFSG.KC.B4A.allLt3 (p := fun k => pcS (nat_lit 3) (nat_lit 1) SA1 k = true)
    pA1_0 pA1_1 pA1_2)
theorem relB1 : relBF (nat_lit 1) = true :=
  relBF_of (nat_lit 1) (nat_lit 3) SB1 (by decide) rfl rfl
    (CFSG.KC.B4A.allLt3 (p := fun k => pcS (nat_lit 3) (nat_lit 1) SB1 k = true)
    pB1_0 pB1_1 pB1_2)
theorem relA2 : relAF (nat_lit 2) = true :=
  relAF_of (nat_lit 2) (nat_lit 2) SA2 (by decide) rfl rfl
    (CFSG.KC.B4A.allLt2 (p := fun k => pcS (nat_lit 2) (nat_lit 2) SA2 k = true)
    pA2_0 pA2_1)
theorem relB2 : relBF (nat_lit 2) = true :=
  relBF_of (nat_lit 2) (nat_lit 2) SB2 (by decide) rfl rfl
    (CFSG.KC.B4A.allLt2 (p := fun k => pcS (nat_lit 2) (nat_lit 2) SB2 k = true)
    pB2_0 pB2_1)

theorem rel0 : relChk (nat_lit 0) = true := by rw [relChk_eq_F, relA0, relB0]; rfl
theorem rel1 : relChk (nat_lit 1) = true := by rw [relChk_eq_F, relA1, relB1]; rfl
theorem rel2 : relChk (nat_lit 2) = true := by rw [relChk_eq_F, relA2, relB2]; rfl

end CFSG.KD.B4AX

#bm_range CFSG.KD.B4AX wit 0 12 witChk
#bm_range CFSG.KD.B4AX lt 0 9 cChkI
#bm_range CFSG.KD.B4AX gl 0 4 glChk

end
