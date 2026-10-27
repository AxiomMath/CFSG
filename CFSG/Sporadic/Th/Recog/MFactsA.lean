module

public import Certificates.Certificate687003
public import CFSG.Sporadic.Th.Recog.ConjE8
public import CFSG.GroupTheory.SuzukiTwoGroupsBasic

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.InvRep
open CFSG.Certificates Certificates CFSG.Sporadic.Th.Recog.MFactsData
open Equiv Equiv.Perm
open scoped commutatorElement

section Cert

private theorem cert_inv : eqRows (mulRows (sqrtRowsGInv ()) (sqrtRowsG ())) idRows = true :=
  Certificates.certificate687003.1

private theorem cert_sq : eqRows (mulRows (sqrtRowsM ()) (sqrtRowsM ())) rowsZ = true :=
  Certificates.certificate687003.2.1

private theorem cert_comm :
    eqRows (mulRows (sqrtRowsM ()) (rowsQ 0)) (mulRows (rowsQ 0) (sqrtRowsM ())) = true :=
  Certificates.certificate687003.2.2.1

private theorem cert_cent : centPairCard () = 2 ^ 8 := Certificates.certificate687003.2.2.2.1

private theorem cert_invCount : invPairCard () = 143 :=
  Certificates.certificate687003.2.2.2.2.1

private theorem cert_invQCount : invQCard () = 270 :=
  Certificates.certificate687003.2.2.2.2.2.1

private theorem cert_q0NeOne : eqRows (rowsQ 0) idRows = false :=
  Certificates.certificate687003.2.2.2.2.2.2.1

private theorem cert_q0NeZ : eqRows (rowsQ 0) rowsZ = false :=
  Certificates.certificate687003.2.2.2.2.2.2.2

end Cert

section Basic

theorem cycleType_kap_ne_of_mul_self {n : ↥M} (hsq : n * n = 1) :
    (kap n : Equiv.Perm (Fin 9)).cycleType ≠ {2, 2} := by
  intro hct
  have hsqP : (kap n : Equiv.Perm (Fin 9)) * (kap n) = 1 := by
    have h : kap n * kap n = 1 := by rw [← map_mul, hsq, map_one]
    exact congrArg Subtype.val h
  have hsupp : ((kap n : Equiv.Perm (Fin 9))).support.card + 2 ≤ 9 := by
    have hsum : ((kap n : Equiv.Perm (Fin 9))).support.card = 4 := by
      rw [← Equiv.Perm.sum_cycleType ((kap n : Equiv.Perm (Fin 9))), hct]
      norm_num
    omega
  have hconjS : IsConj ((kap n : Equiv.Perm (Fin 9))) altRep2 :=
    Equiv.Perm.isConj_iff_cycleType_eq.2 (hct.trans cycleType_altRep2.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconjS
  have hg' : ∃ g : Equiv.Perm (Fin 9), g ∈ alternatingGroup (Fin 9) ∧
      g * (kap n : Equiv.Perm (Fin 9)) * g⁻¹ = altRep2 := by
    by_cases hg1 : Equiv.Perm.sign g = 1
    · exact ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg1, hg⟩
    · refine ⟨swap 0 1 * g, ?_, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_swap (by decide)]
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
        · exact absurd h hg1
        · rw [h]; decide
      · have hinv : (swap (0 : Fin 9) 1)⁻¹ = swap 0 1 :=
          swap_inv 0 1
        calc swap 0 1 * g * (kap n : Equiv.Perm (Fin 9)) *
              (swap 0 1 * g)⁻¹ =
              swap 0 1 * (g * (kap n : Equiv.Perm (Fin 9)) * g⁻¹) *
                (swap 0 1)⁻¹ := by group
          _ = swap 0 1 * altRep2 * swap 0 1 := by
              rw [hg, hinv]
          _ = altRep2 := by
              rw [swap_mul_altRep2, mul_assoc, swap_mul_self, mul_one]
  obtain ⟨g, hgA, hg⟩ := hg'
  obtain ⟨t, ht⟩ := kap_surjective ⟨g, hgA⟩
  let n' : ↥M := t * n * t⁻¹
  have hsq' : n' * n' = 1 := by
    calc n' * n' = t * (n * n) * t⁻¹ := by simp [n']
      _ = 1 := by rw [hsq]; group
  have hkap : (kap n' : Equiv.Perm (Fin 9)) = altRep2 := by
    have h1 : kap n' = (⟨g, hgA⟩ : alternatingGroup (Fin 9)) * kap n *
        (⟨g, hgA⟩ : alternatingGroup (Fin 9))⁻¹ := by
      simp only [n', map_mul, map_inv, ht]
    have h2 : (↑(kap n') : Equiv.Perm (Fin 9)) = g * (kap n : Equiv.Perm (Fin 9)) * g⁻¹ := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val h1
    rw [h2, hg]
  exact not_kap_altRep2 hsq' hkap

theorem exists_sqrt_z_comm_q0 :
    ∃ m : ↥M, (m : J) * q 0 = q 0 * (m : J) ∧ (m : J) ^ 2 = z ∧
      (kap m : Equiv.Perm (Fin 9)).cycleType = {2, 2} := by
  let g : ↥M := wordM sqrtWordInv
  let d : ↥M := wordM dWord
  let d' : ↥M := g * d * g⁻¹
  have hnQ : nfAt 84 ∈ Q := AltQuot.nfAt_mem_Q 84
  let n : ↥M := ⟨nfAt 84, Q_le_M hnQ⟩
  let m : ↥M := d' * n
  have hg : IsRows (sqrtRowsGInv ()) (g : J) :=
    IsRows.word isRows_x isRows_y sqrtWordInv
  have hw : IsRows (sqrtRowsG ()) (wordM sqrtWord : J) :=
    IsRows.word isRows_x isRows_y sqrtWord
  have hd : IsRows (sqrtRowsD ()) (d : J) :=
    IsRows.word isRows_x isRows_y dWord
  have hprod : (g : J) * (wordM sqrtWord : J) = 1 :=
    (hg.mul hw).eq_of_eqRows IsRows.one cert_inv
  have hginv : (g : J)⁻¹ = (wordM sqrtWord : J) :=
    inv_eq_of_mul_eq_one_right hprod
  have hwinv : IsRows (sqrtRowsG ()) ((g : J)⁻¹) := by
    rw [hginv]
    exact hw
  have hd' : IsRows (sqrtRowsD' ()) (d' : J) := by
    change IsRows (mulRows (mulRows (sqrtRowsGInv ()) (sqrtRowsD ())) (sqrtRowsG ()))
      (((g : J) * (d : J)) * (g : J)⁻¹)
    exact (hg.mul hd).mul hwinv
  have hn : IsRows (rowsNfAt 84) (n : J) := isRows_nfAt 84
  have hm : IsRows (sqrtRowsM ()) (m : J) := by
    change IsRows (mulRows (sqrtRowsD' ()) (rowsNfAt 84)) ((d' : J) * (n : J))
    exact hd'.mul hn
  refine ⟨m, ?_, ?_, ?_⟩
  · exact (hm.mul (isRows_q 0)).eq_of_eqRows ((isRows_q 0).mul hm)
      cert_comm
  · have h := (hm.mul hm).eq_of_eqRows isRows_z cert_sq
    simpa [sq] using h
  · have hkapn : kap n = 1 := InvRep.kap_eq_one_iff.2 (AltQuot.nfAt_mem_Q 84)
    have hkap : kap m = kap g * kap d * (kap g)⁻¹ := by
      simp only [m, d', map_mul, map_inv, hkapn, mul_one]
    have hdK : (kap d : Equiv.Perm (Fin 9)) = altRep2 := by
      change (InvRep.kap (InvRep.wordM InvRep.dWord) : Equiv.Perm (Fin 9)) = altRep2
      exact InvRep.kap_wordM_dWord
    have hval : (kap m : Equiv.Perm (Fin 9)) =
        (kap g : Equiv.Perm (Fin 9)) * altRep2 * (kap g : Equiv.Perm (Fin 9))⁻¹ := by
      have h := congrArg Subtype.val hkap
      simpa [hdK] using h
    rw [hval, Equiv.Perm.cycleType_conj, cycleType_altRep2]

theorem exists_conj_q0_eq_mul_z : ∃ c ∈ Q, c * q 0 * c⁻¹ = q 0 * z := by
  refine ⟨q 1, q_mem_Q 1, ?_⟩
  have h := q_mul_q 1 0
  rw [show (c 1 0).val = 1 by decide, pow_one] at h
  calc q 1 * q 0 * (q 1)⁻¹ = (q 0 * q 1 * z) * (q 1)⁻¹ := by rw [h]
    _ = q 0 * z := by
      have hq1 : (q 1)⁻¹ = q 1 := inv_eq_of_mul_eq_one_right (q_mul_self 1)
      rw [hq1]
      have hzq : q 1 * z = z * q 1 := (commute_z_of_mem_M (q_mem_M 1)).symm.eq
      have hq1sq : q 1 * q 1 = 1 := q_mul_self 1
      calc q 0 * q 1 * z * q 1 = q 0 * (q 1 * z) * q 1 := by group
        _ = q 0 * (z * q 1) * q 1 := by rw [hzq]
        _ = q 0 * z * (q 1 * q 1) := by group
        _ = q 0 * z := by rw [hq1sq, mul_one]

def q0Vec : Fin 8 → ZMod 2 := Pi.single 0 1

abbrev centVec (v : Fin 8 → ZMod 2) : Prop :=
  ExtraspecialNF.bil c v q0Vec = 0

instance instDecidableCentVec (v : Fin 8 → ZMod 2) : Decidable (centVec v) := by
  change Decidable (ExtraspecialNF.bil c v q0Vec = 0)
  infer_instance

noncomputable def nfPair (p : ZMod 2 × (Fin 8 → ZMod 2)) : J := nf p.1 p.2

theorem nf_comm_q0_iff (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    nf s v * q 0 = q 0 * nf s v ↔ centVec v := by
  have hq0 : q 0 = nf 0 q0Vec := (ExtraspecialNF.nf_single z q 0).symm
  have hdiag : ∀ i, c i i = 0 := by decide
  have hswap := ExtraspecialNF.nf_mul_comm (n := 8) (z := z) (q := q) (c := c)
    symplectic_rel (fun i j => c_symm j i) hdiag 0 s q0Vec v
  have hsym : ExtraspecialNF.bil c q0Vec v = ExtraspecialNF.bil c v q0Vec := by
    simp only [ExtraspecialNF.bil]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [c_symm i j]
    ring
  constructor
  · intro h
    rw [hq0] at h
    have h' : ExtraspecialNF.nf z q s v * ExtraspecialNF.nf z q 0 q0Vec =
        ExtraspecialNF.nf z q 0 q0Vec * ExtraspecialNF.nf z q s v := by
      simpa [nf_eq_generic] using h
    rw [h'] at hswap
    have hz : z ^ (ExtraspecialNF.bil c q0Vec v).val = 1 := by
      have := congrArg (fun t => (nf s v * nf 0 q0Vec)⁻¹ * t) hswap
      simpa [mul_assoc] using this
    rw [hsym] at hz
    rcases ExtraspecialNF.zmod_two_cases (ExtraspecialNF.bil c v q0Vec) with hb | hb
    · exact hb
    · rw [hb, ExtraspecialNF.val_one_two, pow_one] at hz
      exact absurd hz z_ne_one
  · intro hb
    rw [hq0]
    change ExtraspecialNF.nf z q s v * ExtraspecialNF.nf z q 0 q0Vec =
      ExtraspecialNF.nf z q 0 q0Vec * ExtraspecialNF.nf z q s v
    change ExtraspecialNF.bil c v q0Vec = 0 at hb
    rw [← hsym] at hb
    rw [hb, ZMod.val_zero, pow_zero, mul_one] at hswap
    exact hswap.symm

theorem nf_sq_one_iff (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    nf s v ^ 2 = 1 ↔ ExtraspecialNF.qf c v = 0 := by
  rw [nf_eq_generic]
  exact ExtraspecialNF.nf_sq_eq_one_iff symplectic_rel nf_injective_generic s v

theorem card_centVec :
    (Finset.univ.filter fun p : ZMod 2 × (Fin 8 → ZMod 2) => centVec p.2).card = 2 ^ 8 := by
  change ((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter fun p =>
    ExtraspecialNF.bil c p.2 centE0 = 0).card = 2 ^ 8
  exact cert_cent

theorem card_invVec :
    (Finset.univ.filter fun p : ZMod 2 × (Fin 8 → ZMod 2) =>
      centVec p.2 ∧ ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0).card = 143 := by
  change ((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter fun p =>
    ExtraspecialNF.bil c p.2 centE0 = 0 ∧
      ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0).card = 143
  exact cert_invCount

theorem card_centralizer_q0 :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({q 0} : Set J)) = 2 ^ 8 := by
  let S : Set (ZMod 2 × (Fin 8 → ZMod 2)) :=
    ↑(Finset.univ.filter fun p : ZMod 2 × (Fin 8 → ZMod 2) => centVec p.2)
  have hS : S.ncard = 2 ^ 8 := by
    rw [Set.ncard_coe_finset]
    exact card_centVec
  have himage : (Q ⊓ Subgroup.centralizer ({q 0} : Set J) : Set J) = nfPair '' S := by
    ext g
    constructor
    · intro hg
      obtain ⟨s, v, hsv⟩ := mem_Q_iff.1 hg.1
      have hcomm_g : g * q 0 = q 0 * g := by
        have h' := (Subgroup.mem_centralizer_iff (s := ({q 0} : Set J)) (g := g)).1 hg.2
        have hq0 : q 0 ∈ ({q 0} : Set J) := by rw [Set.mem_singleton_iff]
        have h1 : q 0 * g = g * q 0 := h' (q 0) hq0
        exact h1.symm
      have hcomm : nf s v * q 0 = q 0 * nf s v := by
        simpa [← hsv] using hcomm_g
      have hv : centVec v := (nf_comm_q0_iff s v).1 hcomm
      refine ⟨(s, v), ?_, hsv⟩
      change (s, v) ∈ (Finset.univ.filter fun p : ZMod 2 × (Fin 8 → ZMod 2) => centVec p.2)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    · rintro ⟨p, hp, rfl⟩
      have hp' : centVec p.2 := (Finset.mem_filter.mp hp).2
      refine ⟨nf_mem_Q p.1 p.2, ?_⟩
      change nfPair p ∈ Subgroup.centralizer ({q 0} : Set J)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      exact ((nf_comm_q0_iff p.1 p.2).2 hp').symm
  rw [show Nat.card ↥(Q ⊓ Subgroup.centralizer ({q 0} : Set J)) =
      (Q ⊓ Subgroup.centralizer ({q 0} : Set J) : Set J).ncard from Nat.card_coe_set_eq _]
  rw [himage, Set.ncard_image_of_injective _ (show Function.Injective nfPair from nf_injective)]
  exact hS

theorem ncard_involutions_centralizer_q0 :
    {w : J | w ∈ Q ∧ w * q 0 = q 0 * w ∧ w * w = 1 ∧ w ≠ 1}.ncard = 143 := by
  let S : Set (ZMod 2 × (Fin 8 → ZMod 2)) :=
    ↑(Finset.univ.filter fun p : ZMod 2 × (Fin 8 → ZMod 2) =>
      centVec p.2 ∧ ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0)
  have hS : S.ncard = 143 := by
    rw [Set.ncard_coe_finset]
    exact card_invVec
  have himage : {w : J | w ∈ Q ∧ w * q 0 = q 0 * w ∧ w * w = 1 ∧ w ≠ 1} = nfPair '' S := by
    ext w
    constructor
    · rintro ⟨hwQ, hcomm, hw2, hwne⟩
      obtain ⟨s, v, hsv⟩ := mem_Q_iff.1 hwQ
      have hv1 : centVec v := (nf_comm_q0_iff s v).1 (by simpa [← hsv] using hcomm)
      have hv2 : ExtraspecialNF.qf c v = 0 := by
        apply (nf_sq_one_iff s v).1
        simpa [← hsv, sq] using hw2
      have hv3 : (s, v) ≠ 0 := by
        intro hp
        apply hwne
        rw [← hsv]
        rw [Prod.ext_iff] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ExtraspecialNF.nf_zero_zero z q
      refine ⟨(s, v), ?_, hsv⟩
      change (s, v) ∈ (Finset.univ.filter fun p : ZMod 2 × (Fin 8 → ZMod 2) =>
        centVec p.2 ∧ ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv1, hv2, hv3⟩
    · rintro ⟨p, hp, rfl⟩
      have hp' : centVec p.2 ∧ ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0 :=
        (Finset.mem_filter.mp hp).2
      have hcomm := (nf_comm_q0_iff p.1 p.2).2 hp'.1
      have hsq : nfPair p * nfPair p = 1 := by
        simpa [nfPair, sq] using (nf_sq_one_iff p.1 p.2).2 hp'.2.1
      refine ⟨nf_mem_Q p.1 p.2, hcomm, hsq, ?_⟩
      intro h
      apply hp'.2.2
      have h' : nf p.1 p.2 = 1 := by simpa [nfPair] using h
      have h0 : nf p.1 p.2 = nf 0 (0 : Fin 8 → ZMod 2) := by
        rw [h']
        exact (ExtraspecialNF.nf_zero_zero z q).symm
      exact nf_injective h0
  rw [himage, Set.ncard_image_of_injective _ (show Function.Injective nfPair from nf_injective)]
  exact hS

def qInvSet : Set J := {w | w ∈ Q ∧ w * w = 1 ∧ w ≠ 1 ∧ w ≠ z}

theorem ncard_noncentral_involutions_Q :
    qInvSet.ncard = 270 := by
  classical
  have himage : qInvSet = nfPair '' ((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter
      fun p => ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0 ∧
        p ≠ ((1, 0) : ZMod 2 × (Fin 8 → ZMod 2))) := by
    ext w
    constructor
    · rintro ⟨hwQ, hwsq, hw1, hwz⟩
      obtain ⟨s, v, hsv⟩ := mem_Q_iff.1 hwQ
      refine ⟨(s, v), ?_, hsv⟩
      have hsq : nf s v * nf s v = 1 := by simpa [← hsv] using hwsq
      have hqf : ExtraspecialNF.qf c v = 0 := (nf_sq_one_iff s v).1 (by simpa [sq] using hsq)
      have hp0 : (s, v) ≠ 0 := by
        intro hp
        apply hw1
        rw [← hsv]
        rw [Prod.ext_iff] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ExtraspecialNF.nf_zero_zero z q
      have hp1 : (s, v) ≠ ((1, 0) : ZMod 2 × (Fin 8 → ZMod 2)) := by
        intro hp
        apply hwz
        rw [← hsv]
        rw [Prod.ext_iff] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have hz1 : nf 1 (0 : Fin 8 → ZMod 2) = z := ExtraspecialNF.nf_one_zero z q
        simpa using hz1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqf, hp0, hp1⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hqf, hp0, hp1⟩ := (Finset.mem_filter.mp hp).2
      refine ⟨nf_mem_Q p.1 p.2, by simpa [nfPair, sq] using (nf_sq_one_iff p.1 p.2).2 hqf, ?_, ?_⟩
      · intro h1
        apply hp0
        have h1' : nf p.1 p.2 = 1 := by simpa [nfPair] using h1
        have h0 : nf p.1 p.2 = nf 0 (0 : Fin 8 → ZMod 2) := by
          rw [h1']
          exact (ExtraspecialNF.nf_zero_zero z q).symm
        exact nf_injective h0
      · intro hz
        apply hp1
        have hz' : nf p.1 p.2 = z := by simpa [nfPair] using hz
        have h0 : nf p.1 p.2 = nf 1 (0 : Fin 8 → ZMod 2) := by
          rw [hz']
          exact (ExtraspecialNF.nf_one_zero z q).symm
        exact nf_injective h0
  rw [himage]
  let S : Set (ZMod 2 × (Fin 8 → ZMod 2)) :=
    ↑((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter fun p =>
      ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0 ∧
        p ≠ ((1, 0) : ZMod 2 × (Fin 8 → ZMod 2)))
  change (nfPair '' S).ncard = 270
  rw [show (nfPair '' S).ncard = S.ncard from Set.ncard_image_of_injective _ nf_injective]
  change ((↑((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter fun p =>
    ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0 ∧
      p ≠ ((1, 0) : ZMod 2 × (Fin 8 → ZMod 2))) : Set (ZMod 2 × (Fin 8 → ZMod 2))).ncard) = 270
  rw [Set.ncard_coe_finset]
  exact cert_invQCount

noncomputable abbrev q0M : ↥M := ⟨q 0, q_mem_M 0⟩

theorem q0M_sq : q0M * q0M = 1 := Subtype.ext (q_mul_self 0)

theorem q0M_ne_one : q0M ≠ 1 := by
  intro h
  have hq : (q 0 : J) ≠ 1 :=
    (isRows_q 0).ne_of_eqRows IsRows.one cert_q0NeOne
  exact hq (by simpa using congrArg Subtype.val h)

theorem q0M_ne_z : q0M ≠ ⟨z, z_mem_M⟩ := by
  intro h
  have hq : (q 0 : J) ≠ z :=
    (isRows_q 0).ne_of_eqRows isRows_z cert_q0NeZ
  exact hq (by simpa using congrArg Subtype.val h)

theorem image_conjClass_q0M :
    Subtype.val '' (conjugatesOf q0M) = qInvSet := by
  ext w
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hm
    have hQsub : q0M ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr (q_mem_Q 0)
    have hmQsub : m ∈ Q.subgroupOf M := by
      rw [← hc]
      exact (Max3.normal_Q_subgroupOf_M.conj_mem q0M hQsub c)
    refine ⟨Subgroup.mem_subgroupOf.mp hmQsub, ?_, ?_, ?_⟩
    · have hsqM : m * m = 1 := by
        rw [← hc]
        calc (c * q0M * c⁻¹) * (c * q0M * c⁻¹) = c * (q0M * q0M) * c⁻¹ := by group
          _ = 1 := by rw [q0M_sq]; group
      have h' : ((m * m : ↥M) : J) = ((1 : ↥M) : J) := congrArg Subtype.val hsqM
      simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h' 
    · intro h1
      apply q0M_ne_one
      have hm1 : m = 1 := Subtype.ext h1
      calc q0M = c⁻¹ * (c * q0M * c⁻¹) * c := by group
        _ = 1 := by rw [hc, hm1]; group
    · intro hz
      apply q0M_ne_z
      have hzM : m = (⟨z, z_mem_M⟩ : ↥M) := Subtype.ext hz
      calc q0M = c⁻¹ * (c * q0M * c⁻¹) * c := by group
        _ = c⁻¹ * (⟨z, z_mem_M⟩ : ↥M) * c := by rw [hc, hzM]
        _ = ⟨z, z_mem_M⟩ := by
          have hcz : c * (⟨z, z_mem_M⟩ : ↥M) =
              (⟨z, z_mem_M⟩ : ↥M) * c :=
            (Subgroup.mem_center_iff.mp Max3.z_mem_center_M) c
          calc c⁻¹ * (⟨z, z_mem_M⟩ : ↥M) * c
              = c⁻¹ * ((⟨z, z_mem_M⟩ : ↥M) * c) := by group
            _ = c⁻¹ * (c * (⟨z, z_mem_M⟩ : ↥M)) := by rw [← hcz]
            _ = ⟨z, z_mem_M⟩ := by group
  · rintro ⟨hwQ, hwsq, hw1, hwz⟩
    let wM : ↥M := ⟨w, Q_le_M hwQ⟩
    have hwMsq : wM * wM = 1 := by
      apply Subtype.ext
      exact hwsq
    have hwM1 : wM ≠ 1 := by
      intro h
      apply hw1
      exact congrArg Subtype.val h
    obtain ⟨c, hcM, hc⟩ := InvRep.exists_conj_of_mem_Q hwQ hwsq hw1
    let cM : ↥M := ⟨c, hcM⟩
    have hconj : IsConj q0M wM := by
      rcases hc with hz | hq
      · exfalso
        apply hwz
        calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
          _ = c⁻¹ * z * c := by rw [hz]
          _ = z := by
            have hcz : c * z = z * c := (commute_z_of_mem_M hcM).symm.eq
            calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
              _ = c⁻¹ * (c * z) := by rw [← hcz]
              _ = z := by group
      · refine isConj_iff.mpr ⟨cM⁻¹, ?_⟩
        apply Subtype.ext
        change ((cM⁻¹ : ↥M) : J) * (q0M : J) * (((cM⁻¹ : ↥M) : J)⁻¹) = (wM : J)
        have hcJ : ((cM⁻¹ : ↥M) : J) = c⁻¹ := rfl
        rw [hcJ]
        have hq' : c * w * c⁻¹ = (q0M : J) := by
          change c * w * c⁻¹ = (q 0 : J)
          simpa [wM] using hq
        calc c⁻¹ * (q0M : J) * (c⁻¹)⁻¹ = c⁻¹ * (q0M : J) * c := by rw [inv_inv]
          _ = c⁻¹ * (c * w * c⁻¹) * c := by rw [hq']
          _ = w := by group
    refine ⟨wM, hconj, rfl⟩

theorem ncard_conjugates_q0M : (conjugatesOf q0M).ncard = 270 := by
  calc (conjugatesOf q0M).ncard = (Subtype.val '' (conjugatesOf q0M)).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = qInvSet.ncard := by rw [image_conjClass_q0M]
    _ = 270 := ncard_noncentral_involutions_Q

theorem card_centralizer_q0M :
    Nat.card (Subgroup.centralizer ({q0M} : Set ↥M)) = 2 ^ 14 * 21 := by
  have hidx : (Subgroup.centralizer ({q0M} : Set ↥M)).index = 270 := by
    rw [Subgroup.index_centralizer_eq_ncard, ncard_conjugates_q0M]
  have hcard := Subgroup.card_mul_index (Subgroup.centralizer ({q0M} : Set ↥M))
  rw [hidx, Max3.card_M] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 270) (hcard.trans (by norm_num))

theorem exists_swap_z_q0 :
    ∃ g : J, g * z * g⁻¹ = q 0 ∧ g * q 0 * g⁻¹ = z := by
  classical
  have hCM : Subgroup.centralizer ({a} : Set J) = M :=
    CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M CFSG.Sporadic.Th.th_kernel_facts
  have hq0Jsq : (q 0 : J) * (q 0 : J) = 1 := q_mul_self 0
  have hq0Jne : (q 0 : J) ≠ 1 :=
    (isRows_q 0).ne_of_eqRows IsRows.one cert_q0NeOne
  have hq0ord : orderOf (q 0 : J) = 2 :=
    CFSG.GroupTheory.SuzukiTwoGroup.orderOf_eq_two_iff_sq_eq_one.2
      ⟨by simpa [sq] using hq0Jsq, hq0Jne⟩
  have hyconj : IsConj (q 0 : J) a :=
    (Max3.all_involutions_conjugate (q 0) hq0ord).symm
  obtain ⟨y, hy⟩ := isConj_iff.mp hyconj
  have hyz : y * (q 0 : J) * y⁻¹ = z := by simpa [z_eq_a] using hy
  have hq0eq : y⁻¹ * z * y = q 0 := by
    have h := congrArg (fun t => y⁻¹ * t * y) hyz
    simpa [mul_assoc] using h.symm
  let k : J := y * z * y⁻¹
  have hk2 : k * k = 1 := by
    calc k * k = y * (z * z) * y⁻¹ := by simp [k]
      _ = 1 := by rw [z_mul_self]; group
  have hkcommz : k * z = z * k := by
    have hconj : k * z * k⁻¹ = z := by
      calc k * z * k⁻¹ = y * z * (y⁻¹ * z * y) * z⁻¹ * y⁻¹ := by simp [k]; group
        _ = y * z * q 0 * z⁻¹ * y⁻¹ := by rw [hq0eq]
        _ = y * q 0 * y⁻¹ := by
          have hq0z : z * q 0 = q 0 * z := (commute_z_of_mem_M (q_mem_M 0)).eq
          rw [show y * z * q 0 * z⁻¹ * y⁻¹ = y * (z * q 0) * z⁻¹ * y⁻¹ by group]
          rw [hq0z]
          group
        _ = z := hyz
    calc k * z = (k * z * k⁻¹) * k := by group
      _ = z * k := by rw [hconj]
  have hkM : k ∈ M := by
    have hka : k * a = a * k := by simpa [z_eq_a] using hkcommz
    have hc : k ∈ Subgroup.centralizer ({a} : Set J) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hka
    simpa [hCM] using hc
  let kM : ↥M := ⟨k, hkM⟩
  have hkM2 : kM * kM = 1 := Subtype.ext hk2
  have hkMz : kM ≠ (⟨z, z_mem_M⟩ : ↥M) := by
    intro h
    have hkz : k = z := by
      injection h with hkz
    have hyz' : y * z * y⁻¹ = z := by simpa [k] using hkz
    have hycomm : y * z = z * y := by
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz']
    have hyM : y ∈ M := by
      have hyC : y ∈ Subgroup.centralizer ({a} : Set J) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [z_eq_a] using hycomm)
      rwa [hCM] at hyC
    have hq0z : (q 0 : J) = z := by
      calc (q 0 : J) = y⁻¹ * z * y := hq0eq.symm
        _ = z := by
          have hcomm' : z * y = y * z := hycomm.symm
          calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
            _ = y⁻¹ * (y * z) := by rw [hcomm']
            _ = z := by group
    exact ((isRows_q 0).ne_of_eqRows isRows_z cert_q0NeZ) hq0z
  let C0 : Subgroup ↥M := Subgroup.centralizer ({q0M} : Set ↥M)
  let Ck : Subgroup ↥M := Subgroup.centralizer ({kM} : Set ↥M)
  have hmap1 : C0.map M.subtype =
      M ⊓ Subgroup.centralizer ({q 0} : Set J) := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ Subgroup.centralizer ({q0M} : Set ↥M) at hx
      refine ⟨x.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := Subgroup.mem_centralizer_singleton_iff.mp hx
        simpa [q0M] using congrArg Subtype.val this)
    · rintro ⟨huM, huC⟩
      refine ⟨⟨u, huM⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        apply Subtype.ext
        simpa [q0M] using
          (Subgroup.mem_centralizer_singleton_iff (g := (q 0 : J)) (k := u)).mp huC)
  have hmap2 : (C0.map M.subtype).map (MulAut.conj y).toMonoidHom =
      Ck.map M.subtype := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hmap1] at hv
      rcases hv with ⟨hvM, hvC⟩
      have hvq0 : v * q 0 = q 0 * v :=
        (Subgroup.mem_centralizer_singleton_iff (g := (q 0 : J)) (k := v)).mp hvC
      have hvz : v * z = z * v := by
        have hvM' : v ∈ Subgroup.centralizer ({a} : Set J) := by
          simpa [hCM] using hvM
        simpa [z_eq_a] using Subgroup.mem_centralizer_singleton_iff.mp hvM'
      have huM : y * v * y⁻¹ ∈ M := by
        have hcomm : (y * v * y⁻¹) * z = z * (y * v * y⁻¹) := by
          calc (y * v * y⁻¹) * z = y * v * (y⁻¹ * z * y) * y⁻¹ := by group
            _ = y * v * (q 0) * y⁻¹ := by rw [hq0eq]
            _ = y * (v * q 0) * y⁻¹ := by group
            _ = y * (q 0 * v) * y⁻¹ := by rw [hvq0]
            _ = (y * q 0 * y⁻¹) * (y * v * y⁻¹) := by group
            _ = z * (y * v * y⁻¹) := by rw [hyz]
        have hc : y * v * y⁻¹ ∈ Subgroup.centralizer ({a} : Set J) :=
          Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [z_eq_a] using hcomm)
        simpa [hCM] using hc
      have huk : (y * v * y⁻¹) * k = k * (y * v * y⁻¹) := by
        calc (y * v * y⁻¹) * (y * z * y⁻¹) = y * (v * z) * y⁻¹ := by group
          _ = y * (z * v) * y⁻¹ := by rw [hvz]
          _ = (y * z * y⁻¹) * (y * v * y⁻¹) := by group
      refine ⟨⟨y * v * y⁻¹, huM⟩, ?_, rfl⟩
      change (⟨y * v * y⁻¹, huM⟩ : ↥M) ∈ Subgroup.centralizer ({kM} : Set ↥M)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext huk
    · rintro ⟨x, hx, rfl⟩
      have hxM : (x : J) ∈ M := x.2
      change x ∈ Subgroup.centralizer ({kM} : Set ↥M) at hx
      have hxkM : (x : ↥M) * kM = kM * (x : ↥M) :=
        (Subgroup.mem_centralizer_singleton_iff (g := kM) (k := (x : ↥M))).mp hx
      have hxk : (x : J) * k = k * (x : J) := by
        have := congrArg Subtype.val hxkM
        simpa [kM] using this
      have hxz : (x : J) * z = z * (x : J) := by
        have hxM' : (x : J) ∈ Subgroup.centralizer ({a} : Set J) := by
          simpa [hCM] using hxM
        simpa [z_eq_a] using Subgroup.mem_centralizer_singleton_iff.mp hxM'
      let v : J := y⁻¹ * (x : J) * y
      have hvM : v ∈ M := by
        have hconj : v * z * v⁻¹ = z := by
          calc v * z * v⁻¹ = y⁻¹ * (x : J) * k * (x : J)⁻¹ * y := by
                simp [v, k]; group
            _ = y⁻¹ * ((x : J) * k * (x : J)⁻¹) * y := by group
            _ = y⁻¹ * k * y := by rw [hxk]; group
            _ = z := by simp [k]; group
        have hcomm : v * z = z * v := by
          calc v * z = (v * z * v⁻¹) * v := by group
            _ = z * v := by rw [hconj]
        have hc : v ∈ Subgroup.centralizer ({a} : Set J) :=
          Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [z_eq_a] using hcomm)
        rw [← hCM]
        exact hc
      have hvq0 : v * q 0 = q 0 * v := by
        calc v * q 0 = (y⁻¹ * (x : J) * y) * (y⁻¹ * z * y) := by rw [hq0eq]
          _ = y⁻¹ * ((x : J) * z) * y := by group
          _ = y⁻¹ * (z * (x : J)) * y := by rw [hxz]
          _ = (y⁻¹ * z * y) * (y⁻¹ * (x : J) * y) := by group
          _ = q 0 * v := by rw [hq0eq]
      have hvmem : v ∈ M ⊓ Subgroup.centralizer ({q 0} : Set J) :=
        ⟨hvM, Subgroup.mem_centralizer_singleton_iff.mpr hvq0⟩
      refine ⟨v, ?_, ?_⟩
      · rw [hmap1]
        exact hvmem
      · change y * (y⁻¹ * (x : J) * y) * y⁻¹ = (x : J)
        group
  have hinj_conj : Function.Injective (MulAut.conj y) := by
    intro a b h
    have h' := congrArg (fun t => y⁻¹ * t * y) h
    simpa [MulAut.conj_apply, mul_assoc] using h'
  have hcard : Nat.card C0 = Nat.card Ck := by
    calc Nat.card C0 = Nat.card (C0.map M.subtype) :=
          (Subgroup.card_map_of_injective (K := C0) (f := M.subtype) M.subtype_injective).symm
      _ = Nat.card ((C0.map M.subtype).map (MulAut.conj y).toMonoidHom) :=
          (Subgroup.card_map_of_injective (K := C0.map M.subtype)
            (f := (MulAut.conj y).toMonoidHom) hinj_conj).symm
      _ = Nat.card (Ck.map M.subtype) := by rw [hmap2]
      _ = Nat.card Ck :=
          Subgroup.card_map_of_injective (K := Ck) (f := M.subtype) M.subtype_injective
  have hCk : Nat.card Ck = 2 ^ 14 * 21 := by
    rw [← hcard]
    exact card_centralizer_q0M
  have hkQ : k ∈ Q :=
    mem_Q_of_card_centralizer (k := kM) hkM2 (by simpa [Ck] using hCk)
  have hk1 : k ≠ 1 := by
    intro h
    apply z_ne_one
    calc z = y⁻¹ * k * y := by simp [k]; group
      _ = 1 := by rw [h]; group
  obtain ⟨n, hnM, hn⟩ := InvRep.exists_conj_of_mem_Q hkQ hk2 hk1
  have hnq : n * k * n⁻¹ = q 0 := by
    rcases hn with hz | hq
    · exfalso
      apply hkMz
      apply Subtype.ext
      calc k = n⁻¹ * (n * k * n⁻¹) * n := by group
        _ = n⁻¹ * z * n := by rw [hz]
        _ = z := by
          have hnz : n * z = z * n := (commute_z_of_mem_M hnM).symm.eq
          calc n⁻¹ * z * n = n⁻¹ * (z * n) := by group
            _ = n⁻¹ * (n * z) := by rw [← hnz]
            _ = z := by group
    · exact hq
  refine ⟨n * y, ?_, ?_⟩
  · calc (n * y) * z * (n * y)⁻¹ = n * (y * z * y⁻¹) * n⁻¹ := by group
      _ = n * k * n⁻¹ := rfl
      _ = q 0 := hnq
  · calc (n * y) * q 0 * (n * y)⁻¹ = n * (y * q 0 * y⁻¹) * n⁻¹ := by group
      _ = n * z * n⁻¹ := by rw [hyz]
      _ = z := by
        have hnz : n * z = z * n := (commute_z_of_mem_M hnM).symm.eq
        calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [hnz]
          _ = z := by group

theorem exists_not_commute_centralizer_q0 :
    ∃ u ∈ Q, ∃ v ∈ Q, u * q 0 = q 0 * u ∧ v * q 0 = q 0 * v ∧ u * v ≠ v * u := by
  refine ⟨q 3, q_mem_Q 3, q 4, q_mem_Q 4, ?_, ?_, ?_⟩
  · have h := q_mul_q 3 0
    rw [show (c 3 0).val = 0 by decide, pow_zero, mul_one] at h
    exact h
  · have h := q_mul_q 4 0
    rw [show (c 4 0).val = 0 by decide, pow_zero, mul_one] at h
    exact h
  · intro h
    have h34 := q_mul_q 3 4
    rw [show (c 3 4).val = 1 by decide, pow_one] at h34
    rw [h] at h34
    generalize hA : q 4 * q 3 = a at h34
    have hz1 : (1 : J) = z := by
      have := congrArg (fun t => a⁻¹ * t) h34
      simpa [mul_assoc] using this
    exact z_ne_one hz1.symm

end Basic

end CFSG.Sporadic.Th.Recog
