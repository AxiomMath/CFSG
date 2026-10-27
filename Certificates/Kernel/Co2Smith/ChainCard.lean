module

public import Certificates.Kernel.Co2Smith.Chain
public import Certificates.Kernel.SporSch.Co2M.Chains2049
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Co2Cert.OrderCheck
public import CFSG.Sporadic.Co2Schreier.OrbitZCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier
open CertificateChecks.KernelSporSch.Co2M
open scoped Pointwise

@[expose] noncomputable def permK (P : Nat) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (unpack 2300 12 P)

theorem prep_of_permOK {P Q : Nat} (h : permOK 2300 12 (mask 12) (2300 * 12) P Q = true) :
    PRep 2300 12 P (permK P) :=
  prep_of_rep (rep_permOfArr (isInvA_unpack h)).1

theorem prep_unique {P : Nat} {g h : Equiv.Perm (Fin 2300)} (hg : PRep 2300 12 P g)
    (hh : PRep 2300 12 P h) : g = h :=
  (rep_unpack hg).unique (rep_unpack hh)

theorem range_of_prep {P : Nat} {g : Equiv.Perm (Fin 2300)} (hg : PRep 2300 12 P g) :
    allN 2300 (fun i => Nat.blt (pg 12 (mask 12) P i) 2300) = true :=
  allN_of_forall fun i hi => by
    rw [Nat.blt_eq, hg ⟨i, hi⟩]
    exact (g ⟨i, hi⟩).isLt

theorem comm_of_pcomp {P X : Nat} {g x : Equiv.Perm (Fin 2300)} (hg : PRep 2300 12 P g)
    (hx : PRep 2300 12 X x)
    (h : Nat.beq (pcomp 2300 12 (mask 12) P X) (pcomp 2300 12 (mask 12) X P) = true) :
    g * x = x * g := by
  have h1 := prep_pcomp (by norm_num) hg hx
  have h2 := prep_pcomp (by norm_num) hx hg
  rw [Nat.eq_of_beq_eq_true h] at h1
  exact prep_unique h1 h2

theorem mem_P_of_sift {P : Nat}
    {g : Equiv.Perm (Fin 2300)} (hg : PRep 2300 12 P g)
    (hs : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) KernelSpor.Co2A.LR
      KernelSpor.Co2A.TRI KernelSpor.Co2A.BP 6 0 P = true) : g ∈ co2P := by
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
    (rep_unpack hg)).1 (siftK_sound KernelSpor.Co2A.binds KernelSpor.Co2A.perm KernelSpor.Co2A.hl
      rfl (range_of_prep hg) hs)

theorem fix_iff {x w z : Equiv.Perm (Fin 2300)} (hc : x * w = w * z) (p : Fin 2300) :
    x (w p) = w p ↔ z p = p := by
  have e : x (w p) = w (z p) := by
    rw [← Equiv.Perm.mul_apply, hc, Equiv.Perm.mul_apply]
  rw [e]
  exact w.injective.eq_iff

theorem fixSet_eq {x w z : Equiv.Perm (Fin 2300)} (hc : x * w = w * z) :
    {p : Fin 2300 | x p = p} = w • {p : Fin 2300 | z p = p} := by
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def, Set.mem_setOf_eq,
    Set.mem_setOf_eq]
  have h := fix_iff hc (w⁻¹ p)
  have e : w (w⁻¹ p) = p := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [e] at h
  exact h

theorem translates_eq {G : Subgroup (Equiv.Perm (Fin 2300))} {x w z : Equiv.Perm (Fin 2300)}
    (hw : w ∈ G) (hc : x * w = w * z) :
    (Set.range fun g : G => g • {p : Fin 2300 | x p = p}) =
      Set.range fun g : G => g • {p : Fin 2300 | z p = p} := by
  rw [fixSet_eq hc]
  obtain ⟨w', hw'w⟩ : ∃ w' : G, (w' : Equiv.Perm (Fin 2300)) = w := ⟨⟨w, hw⟩, rfl⟩
  have hw' : ∀ (g : G) (S : Set (Fin 2300)), g • w • S = (g * w') • S := fun g S => by
    rw [mul_smul, ← hw'w]
    rfl
  ext S
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * w', (hw' g _).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨g * w'⁻¹, ?_⟩
    simp only [hw', inv_mul_cancel_right]

theorem card_mul_le_of_fix
    {x w : Equiv.Perm (Fin 2300)}
    (hx : x ∈ co2P) (hw : w ∈ co2P) (hc : x * w = w * locZ)
    {H : Subgroup (Equiv.Perm (Fin 2300))} (hH : H ≤ co2P ⊓ Subgroup.centralizer {x}) :
    Nat.card H * 56925 ≤ 42305421312000 := by
  refine card_mul_leK hx hH ?_
  rw [translates_eq hw hc]
  exact le_ncard_orbitK repK_z orbitZ_check

theorem card_mul_le_of_orbit
    {x w : Equiv.Perm (Fin 2300)}
    (hx : x ∈ co2P) (hw : w ∈ co2P) (hc : x * w = w * locZ)
    {m : Nat} {t : Fin m → Equiv.Perm (Fin 2300)}
    (ht : ∀ k, t k ∈ co2P ⊓ Subgroup.centralizer {x}) (hinj : Function.Injective fun k => t k 0)
    {K : Subgroup (Equiv.Perm (Fin 2300))} (hK : K ≤ co2P ⊓ Subgroup.centralizer {x})
    (h0 : ∀ g ∈ K, g 0 = 0) :
    Nat.card K * m * 56925 ≤ 42305421312000 := by
  have hC := card_mul_le_of_fix hx hw hc (le_refl _)
  obtain ⟨C, hCd⟩ : ∃ C, C = co2P ⊓ Subgroup.centralizer {x} := ⟨_, rfl⟩
  rw [← hCd] at hC hK ht
  have hidx : (MulAction.stabilizer C (0 : Fin 2300)).index =
      (MulAction.orbit C (0 : Fin 2300)).ncard := MulAction.index_stabilizer _ _
  have hm := (MulAction.stabilizer C (0 : Fin 2300)).card_mul_index
  have horb : m ≤ (MulAction.orbit C (0 : Fin 2300)).ncard := by
    have hmaps : ∀ k : Fin m, t k 0 ∈ MulAction.orbit C (0 : Fin 2300) :=
      fun k => ⟨⟨t k, ht k⟩, rfl⟩
    have := Set.ncard_le_ncard_of_injOn (fun k => t k 0) (s := (Set.univ : Set (Fin m)))
      (fun k _ => hmaps k) (fun a _ b _ hab => hinj hab)
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using this
  have hKs : K.subgroupOf C ≤ MulAction.stabilizer C (0 : Fin 2300) := by
    intro g hg
    exact h0 _ (Subgroup.mem_subgroupOf.1 hg)
  have hKc : Nat.card K = Nat.card (K.subgroupOf C) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv).symm
  have h1 : Nat.card K ≤ Nat.card (MulAction.stabilizer C (0 : Fin 2300)) := by
    rw [hKc]
    exact Subgroup.card_le_of_le hKs
  calc Nat.card K * m * 56925
      ≤ Nat.card (MulAction.stabilizer C (0 : Fin 2300)) *
          (MulAction.stabilizer C (0 : Fin 2300)).index * 56925 := by
        rw [hidx]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 horb)
    _ = Nat.card C * 56925 := by rw [hm]
    _ ≤ 42305421312000 := hC

theorem chainOK_of_card {ws : List (List Nat)} {base : List Nat} {W : Array (List Int)}
    {ord kS nb BP NS CH : Nat} {PS PSI LR G : Nat → Nat} {D : List (List Int)}
    {K : Subgroup (Equiv.Perm (Fin 2300))}
    (hw : ∀ i < ws.length, ∀ k ∈ ws[i]!, k < 22)
    (hG : ∀ i < ws.length,
      bindVK (KernelSporSch.Co2M.PV 0) (G i) (trK 22 (wK LP ws[i]!)) = true)
    (hO : ∀ i < ws.length,
      pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (G i)) CIK = PS i)
    (hD : W.toList.drop ws.length = D)
    (hW : W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr ws.length kS D)
    (hbs : base.toArray.size = nb) (hbt : ∀ t < nb, base.toArray[t]! = pg 12 (mask 12) BP t)
    (hh : headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) PS PSI kS ws.length D nb BP = true)
    (ho : OrbsOK 2300 12 PS PSI LR kS nb BP NS CH) (hN : 2300 ≤ NS * CH)
    (hK : ∀ i < ws.length, permK (PS i) ∈ K) (hKc : Nat.card K ≤ ord)
    (hord : ((List.range nb).map fun i => rcnt (LR i)).prod = ord) :
    glChainOK ws base W ord = true := by
  have hR : ∀ i < ws.length, glR ws[i]! = unpackR 22 (wK LP ws[i]!) := fun i hi => glR_eq (hw i hi)
  obtain ⟨hb, hpsi⟩ := chainBinds_of hw hG hO hD hbs hbt hh
  have hhd := Orb.rawHeadOK_of hb hh
  have hp : allN kS (fun j => permOK 2300 12 (mask 12) (2300 * 12) (PS j) (PSI j)) = true := by
    have h := hh
    unfold headK at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
    exact h.2.2.2.2.1
  have hkS : ∀ i < ws.length, i < kS := fun i hi => by
    have := hhd.1
    rw [hb.2.2.2.1] at this
    omega
  have hcl : Subgroup.closure (Set.range fun j : Fin ws.length =>
      permOfArr 2300 (glExtend (glOrig ws) W)[j.val]!) ≤ K := by
    rw [Subgroup.closure_le, Set.range_subset_iff]
    intro j
    have e := hb.2.2.2.2.1 j.val (hkS j.val j.isLt)
    change permOfArr 2300 (glExtend (glOrig ws) W)[j.val]! ∈ K
    rw [e]
    exact hK j.val j.isLt
  unfold glChainOK
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨fun w hw' => ?_, hhd.1⟩, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw'
    rw [← getElem!_pos ws i hi, hR i hi]
    exact permOK_of (hG i hi)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [hpsi i hi, hb.2.2.2.2.1 i (hkS i hi)]
    exact eqA_self _
  · have h := rawChainK_of_card_orb 1 hb hh ho hN (by
      rw [rawOrbitSizesK_orb hb hp ho hN, hord]
      exact (Subgroup.card_le_of_le hcl).trans hKc)
    rw [← hW] at h
    exact h
  · rw [rawOrbitSizesK_orb hb hp ho hN, hord]

end CertificateChecks.KernelCo2Smith
