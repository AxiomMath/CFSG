
module

public import Certificates.Kernel.CU43Aut.Cls
public import Certificates.Kernel.CU43Aut.Swap
public import Certificates.Kernel.CU43Aut.WitC
public import Certificates.Kernel.Multipliers.U43BFacts
public import CFSG.Certificates.Kernel.Spor.CentBoundSound
public import CFSG.Certificates.Kernel.J2Enum.Group
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CoverBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CountBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut.CentG

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
open CertificateChecks.KernelU43B

abbrev PR (p : Nat) (g : Equiv.Perm (Fin 820)) : Prop := Raw.Orb.PRep 820 10 p g

theorem pr_pc {p q : Nat} {g h : Equiv.Perm (Fin 820)} (hp : PR p g) (hq : PR q h) :
    PR (pc p q) (g * h) :=
  Raw.Orb.prep_pcomp (by norm_num) hp hq

theorem pr_eq {p q : Nat} {g h : Equiv.Perm (Fin 820)} (hp : PR p g) (hq : PR q h) (e : p = q) :
    g = h := by
  subst e
  exact Equiv.ext fun x => Fin.ext ((hp x).symm.trans (hq x))

theorem pr_of_bind {p : Nat} {A : Array Nat} {g : Equiv.Perm (Fin 820)}
    (hb : bindListK 820 10 p A.toList = true) (hA : Rep 820 A g) : PR p g :=
  Raw.Orb.prep_of_rep (by rw [← eq_unpack_of_bindListK hb]; exact hA)

theorem pr_inv {p q : Nat} {g : Equiv.Perm (Fin 820)} (hp : PR p g)
    (h : invEqK 820 10 (mask 10) (820 * 10) p q = true) : PR q g⁻¹ := by
  obtain ⟨-, h2⟩ := invEqK_sound h
  exact Raw.Orb.prep_of_rep (rep_inv_of_isInvA (Raw.Orb.rep_unpack hp) h2)

theorem inP_unpack {X : Nat} (hc : cK X = true) (h : inPK X = true) :
    inP (unpack 820 10 X) = true := by
  unfold inP CFSG.EvenSporadicStandard.M24Std.CU43.levels baseArr
  rw [KernelU43B.base_eq]
  exact siftK_sound KernelU43B.binds KernelU43B.perm C.hl rfl (range_of_canonK hc) h

section P

theorem mem_P {X : Nat} (hc : cK X = true) (h : inPK X = true) : ∃ γ, PR X γ ∧ γ ∈ P := by
  obtain ⟨γ, -, hγ⟩ := ((CFSG.KC.J2Enum.GrpPf.group3 KernelU43B.binds C.head C.hl
    (by norm_num) C.hs).2.2.1 X hc).1 h
  exact ⟨γ, hγ, (inP_iff (Raw.Orb.rep_unpack hγ)).1 (inP_unpack hc h)⟩

theorem P_eq_Gen : P = Raw.Orb.Gen 820 chainS 2 := by
  have F := chainCheckFacts CFSG.LieType.Multipliers.U43.chain_check
  have e0 : permOfArr 820 chainS[0]! = psi xElt :=
    (rep_permOfArr (F.strong_inv 0 (by decide))).1.unique rep_tabA
  have e1 : permOfArr 820 chainS[1]! = psi yElt :=
    (rep_permOfArr (F.strong_inv 1 (by decide))).1.unique rep_tabB
  rw [P_eq_closure, Raw.Orb.Gen]
  congr 1
  ext g
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, e0⟩
    · exact ⟨1, e1⟩
  · rintro ⟨⟨_ | _ | j, hj⟩, rfl⟩
    · exact Or.inl e0
    · exact Or.inr e1
    · exact absurd hj (by omega)

theorem pr_S0 : PR (C.S 0) (psi xElt) := by
  have e : chainS[0]! = unpack 820 10 (C.S 0) := KernelU43B.binds.2.2.2.2.1 0 (by norm_num)
  have h : Rep 820 chainS[0]! (psi xElt) := rep_tabA
  rw [e] at h
  exact Raw.Orb.prep_of_rep h

theorem psi_x_mem : psi xElt ∈ P := by
  rw [P_eq_closure]
  exact subset_closure (Set.mem_insert _ _)

theorem card_of_bounds {r : Nat} {ρ : Equiv.Perm (Fin 820)} (hr : PR r ρ) {O G L : Nat → Nat}
    {nh nl c : Nat} (hu : ubOK r O c = true) (hl : lbOK r G L nh nl c = true) :
    Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) = c := by
  unfold ubOK at hu
  obtain ⟨hu1, hu2⟩ := (bAnd_iff _ _).1 hu
  have hup := ubProdK_sound (NS := 13) (CH := 64) KernelU43B.binds C.head C.hl (by norm_num) C.hs
    P_eq_Gen hr hu1
  rw [Nat.eq_of_beq_eq_true hu2] at hup
  unfold lbOK at hl
  obtain ⟨hg, hl2⟩ := (bAnd_iff _ _).1 hl
  obtain ⟨ht, hc⟩ := (bAnd_iff _ _).1 hl2
  have hex : ∀ l, ∃ γ : Equiv.Perm (Fin 820), l < nh →
      PR (G l) γ ∧ γ ∈ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    intro l
    by_cases hlt : l < nh
    · have hx := allN_spec hg l hlt
      simp only [bAnd_iff] at hx
      obtain ⟨h1, h2, h3⟩ := hx
      obtain ⟨γ, hγ, hγP⟩ := mem_P h1 h2
      refine ⟨γ, fun _ => ⟨hγ, mem_inf.2 ⟨hγP, mem_centralizer_singleton_iff.2 ?_⟩⟩⟩
      exact pr_eq (pr_pc hγ hr) (pr_pc hr hγ) (Nat.eq_of_beq_eq_true h3)
    · exact ⟨1, fun h => absurd h hlt⟩
  choose h hh using hex
  have hlow := towerProdK_sound (h := h) (fun l hl => (hh l hl).1) ht
  rw [Nat.eq_of_beq_eq_true hc] at hlow
  have hle : closure (h '' {l | l < nh}) ≤ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact (hh l hl).2
  exact le_antisymm hup (hlow.trans (Subgroup.card_le_of_le hle))

end P

section D

theorem pr_rP {j : Nat} (hj : j < 9) : PR (CU43T (j + 2)) (rP j) := by
  have hb := kBind
  have hr := rep_rP hj
  interval_cases j
  · exact pr_of_bind hb.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.2.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.2.2.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.2.2.2.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.2.2.2.2.2.2.1 hr
  · exact pr_of_bind hb.2.2.2.2.2.2.2.2.2.2 hr

theorem pr_dP : PR (CU43T 0) dP := pr_of_bind kBind.1 rep_dP

theorem card_cent_conj_norm {u : Equiv.Perm (Fin 820)}
    (hu : u ∈ normalizer (P : Set (Equiv.Perm (Fin 820)))) (r : Equiv.Perm (Fin 820)) :
    Nat.card ↥(P ⊓ centralizer ({u * r * u⁻¹} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card ↥(P ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 820)))) := by
  have hN := mem_normalizer_iff.1 hu
  have hN' := mem_normalizer_iff.1 (inv_mem hu)
  refine Nat.card_congr
    { toFun := fun x => ⟨u⁻¹ * x * u, mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩⟩
      invFun := fun y => ⟨u * y * u⁻¹, mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        change u * (u⁻¹ * x.1 * u) * u⁻¹ = x.1
        group
      right_inv := fun y => by
        apply Subtype.ext
        change u⁻¹ * (u * y.1 * u⁻¹) * u = y.1
        group }
  · have := (hN' x.1).1 (mem_inf.1 x.2).1
    simpa using this
  · have h := mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2
    calc u⁻¹ * x.1 * u * r = u⁻¹ * (x.1 * (u * r * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * r * u⁻¹) * x.1) * u := by rw [h]
      _ = r * (u⁻¹ * x.1 * u) := by group
  · exact (hN y.1).1 (mem_inf.1 y.2).1
  · have h := mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2
    calc u * y.1 * u⁻¹ * (u * r * u⁻¹) = u * (y.1 * r) * u⁻¹ := by group
      _ = u * (r * y.1) * u⁻¹ := by rw [h]
      _ = u * r * u⁻¹ * (u * y.1 * u⁻¹) := by group

theorem card_swap {s j j' : Nat} (hj : j < 9) (hj' : j' < 9) (hs : s < 3)
    (h : swOK (SWP s) j j' = true) :
    Nat.card ↥(P ⊓ centralizer ({rP j'} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card ↥(P ⊓ centralizer ({rP j} : Set (Equiv.Perm (Fin 820)))) := by
  unfold swOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hk := kWC
  simp only [bAnd_iff] at hk
  have hc := allN_spec hk.2 s hs
  obtain ⟨γ, hγ, hγP⟩ := mem_P hc h1
  have e := pr_eq (pr_pc (pr_pc hγ pr_dP) (pr_rP hj)) (pr_rP hj' |> fun h => pr_pc h (pr_pc hγ pr_dP))
    (Nat.eq_of_beq_eq_true h2)
  have e2 : rP j' = γ * (dP * rP j * dP⁻¹) * γ⁻¹ := by
    calc rP j' = rP j' * (γ * dP) * (γ * dP)⁻¹ := by group
      _ = γ * dP * rP j * (γ * dP)⁻¹ := by rw [← e]
      _ = γ * (dP * rP j * dP⁻¹) * γ⁻¹ := by group
  rw [e2, card_inf_centralizer_conj hγP, card_cent_conj_norm dP_mem_normalizer]

theorem pr_R3 : PR (R3P 0) (psi xElt * rP 3 * (psi xElt)⁻¹) := by
  have h := (bAnd_iff (cK (R3P 0)) (Nat.beq (pc (C.S 0) (CU43T 5)) (pc (R3P 0) (C.S 0)))).1 kR3
  have he : pc (C.S 0) (CU43T 5) = pc (R3P 0) (C.S 0) := Nat.eq_of_beq_eq_true h.2
  have e5 : PR (CU43T 5) (rP 3) := pr_rP (j := 3) (by norm_num)
  intro y
  have h2 := pr_pc pr_S0 e5 ((psi xElt)⁻¹ y)
  have h1 : pg 10 (mask 10) (pc (R3P 0) (C.S 0)) ((psi xElt)⁻¹ y) =
      pg 10 (mask 10) (R3P 0) (pg 10 (mask 10) (C.S 0) ((psi xElt)⁻¹ y)) :=
    PF.pg_pcomp (by norm_num) ((psi xElt)⁻¹ y).2
  rw [he, h1, pr_S0 ((psi xElt)⁻¹ y)] at h2
  have e : psi xElt ((psi xElt)⁻¹ y) = y := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [e] at h2
  rw [h2, Equiv.Perm.mul_apply (psi xElt * rP 3)]

theorem card3 : Nat.card ↥(P ⊓ centralizer ({rP 3} : Set (Equiv.Perm (Fin 820)))) =
    repCent.getD 3 0 := by
  rw [← card_inf_centralizer_conj psi_x_mem]
  exact card_of_bounds pr_R3 kU3 kL3

theorem card_cent {j : Nat} (hj : j < 9) :
    Nat.card ↥(P ⊓ centralizer ({rP j} : Set (Equiv.Perm (Fin 820)))) = repCent.getD j 0 := by
  have h0 : Nat.card ↥(P ⊓ centralizer ({rP 0} : Set (Equiv.Perm (Fin 820)))) = repCent.getD 0 0 :=
    card_of_bounds (pr_rP (j := 0) (by norm_num)) kU0 kL0
  have h4 : Nat.card ↥(P ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820)))) = repCent.getD 4 0 :=
    card_of_bounds (pr_rP (j := 4) (by norm_num)) kU4 kL4
  have h7 : Nat.card ↥(P ⊓ centralizer ({rP 7} : Set (Equiv.Perm (Fin 820)))) = repCent.getD 7 0 :=
    card_of_bounds (pr_rP (j := 7) (by norm_num)) kU7 kL7
  obtain ⟨s0, s1, s2⟩ : swOK (SWP 0) 0 1 = true ∧ swOK (SWP 1) 4 5 = true ∧
      swOK (SWP 2) 7 6 = true := by
    have h := kSwap
    simp only [bAnd_iff] at h
    exact h
  interval_cases j
  · exact h0
  · rw [card_swap (by norm_num) (by norm_num) (by norm_num) s0, h0]
    rfl
  · exact card_of_bounds (pr_rP (j := 2) (by norm_num)) kU2 kL2
  · exact card3
  · exact h4
  · rw [card_swap (by norm_num) (by norm_num) (by norm_num) s1, h4]
    rfl
  · rw [card_swap (by norm_num) (by norm_num) (by norm_num) s2, h7]
    rfl
  · exact h7
  · exact card_of_bounds (pr_rP (j := 8) (by norm_num)) kU8 kL8

theorem centCounts_true : centCounts = true := by
  simp only [centCounts, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro j hj
  rw [← card_eq_countW_P (f := commW (idA 820) [reps[j]!]) (Pr := fun g => g * rP j = rP j * g)
    (fun w g hw _ => by
      have hH : RepW 820 (idA 820 :: w) (g * 1) := RepW.cons rep_idA hw
      rw [mul_one] at hH
      simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
      exact allLt_comm_iff hH (rep_rP hj))]
  have e : repCent[j]! = repCent.getD j 0 := by
    rw [List.getElem!_eq_getElem?_getD]
    rfl
  rw [e, ← card_cent hj]
  exact Nat.card_congr
    { toFun := fun y => ⟨y.1.1, mem_inf.2 ⟨y.1.2, mem_centralizer_singleton_iff.2 y.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2⟩
      left_inv := fun y => rfl
      right_inv := fun x => rfl }

end D

end CertificateChecks.KernelCU43Aut.CentG

end
