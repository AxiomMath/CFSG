
module

public import CFSG.Sporadic.HNOddCore.InvRow4Base
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem card_of_split
    {C : Subgroup RH} {K : Subgroup JH}
    (h : ∀ r : RH, r ∈ C ↔ (∃ g ∈ K, r = jR g) ∨ ∃ g ∈ K, r = jR g * cR) :
    Nat.card C = 2 * Nat.card K := by
  classical
  have hmemK : ∀ r ∈ C, jPart r ∈ K := by
    intro r hr
    rcases (h r).1 hr with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · rwa [jPart_jR]
    · rwa [jPart_jR_mul_cR]
  have e : C ≃ K ⊕ K :=
    { toFun := fun r => if IsOuter r then Sum.inr ⟨jPart r, hmemK r r.2⟩
        else Sum.inl ⟨jPart r, hmemK r r.2⟩
      invFun := fun s => match s with
        | Sum.inl g => ⟨jR g, (h _).2 (Or.inl ⟨g, g.2, rfl⟩)⟩
        | Sum.inr g => ⟨jR g * cR, (h _).2 (Or.inr ⟨g, g.2, rfl⟩)⟩
      left_inv := by
        rintro ⟨r, hr⟩
        rcases (h r).1 hr with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
        · simp only [not_isOuter_jR, ite_false, jPart_jR]
        · simp only [isOuter_jR_mul_cR, ite_true, jPart_jR_mul_cR]
      right_inv := by
        rintro (⟨g, hg⟩ | ⟨g, hg⟩)
        · simp only [not_isOuter_jR, ite_false, jPart_jR]
        · simp only [isOuter_jR_mul_cR, ite_true, jPart_jR_mul_cR] }
  rw [Nat.card_congr e, Nat.card_sum]
  ring

theorem orbit4_parts :
    orbitOK InvData.f4Arr.size s4J (bfsList InvData.f4Arr.size s4J 0) = true ∧
    (bfsList InvData.f4Arr.size s4J 0).size = 800 := by
  have h := orbits_cert
  unfold orbitChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, h5⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨h4, beq_iff_eq.1 h5⟩

theorem x0_fix_t4 :
    jR t4J • x0 = x0 := by
  rw [jR_smul]
  exact (mem_HJ_iff_fix _).1 t4J_mem_HJ

theorem PtList.range_eq_univ {m : ℕ} {L : Array ℕ} (hL : PtList m L) (hs : L.size = m) :
    Set.range hL.pt = Set.univ :=
  Set.range_eq_univ.2 ((Fintype.bijective_iff_injective_and_card hL.pt).2
    ⟨hL.pt_injective, by rw [Fintype.card_fin, Fintype.card_fin, hs]⟩).2

theorem thetaJ_comm_t4
    {h : JH} (hh : h ∈ HJ) (hc : h * t4J = t4J * h) :
    (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * sig4 = sig4 * (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) := by
  have e1 := thetaJ_mul h t4J hh t4J_mem_HJ
  have e2 := thetaJ_mul t4J h t4J_mem_HJ hh
  have e3 : (⟨h * t4J, mul_mem hh t4J_mem_HJ⟩ : HJ) = ⟨t4J * h, mul_mem t4J_mem_HJ hh⟩ :=
    Subtype.ext hc
  have e4 : (thetaJ ⟨t4J, t4J_mem_HJ⟩ : Perm (Fin 12)) = sig4 := thetaJ_t4H
  rw [← e4, ← e1, ← e2, e3]

abbrev Z4 : Subgroup (Perm (Fin 12)) := Subgroup.centralizer {sig4} ⊓ alternatingGroup (Fin 12)

theorem card_CH_t4_le :
    Nat.card (Subgroup.centralizer {t4J} ⊓ HJ : Subgroup JH) ≤ 4608 := by
  rw [← card_altCentralizer_sig4]
  refine card_le_of_thetaJ (K := Subgroup.centralizer {t4J} ⊓ HJ) (Z := Z4) inf_le_right ?_
  intro g hg
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_centralizer_singleton_iff (g := sig4)).2 ?_,
    (thetaJ _).2⟩
  exact thetaJ_comm_t4 _ ((Subgroup.mem_centralizer_singleton_iff (g := t4J) (k := g)).1
    (Subgroup.mem_inf.1 hg).1)

abbrev K4 : Subgroup JH := Subgroup.closure (Set.range fun s : Fin InvData.c4Nat.size => c4G s)

theorem K4_le_HJ : K4 ≤ HJ := closure_le_HJ fun s => c4G_mem_HJ s

theorem cR_comm_t4 :
    jR t4J * cR = cR * jR t4J :=
  jR_comm_cR t4J_mem_HJ (commute_of_prep prep_tau nat_t4 natComm_parts.2.2.2).symm

theorem mem_centralizer_t4_iff
    (r : RH) : r ∈ Subgroup.centralizer {jR t4J} ↔
    (∃ g ∈ Subgroup.centralizer {t4J}, r = jR g) ∨
      ∃ g ∈ Subgroup.centralizer {t4J}, r = jR g * cR := by
  have key : ∀ g : JH, jR g * jR t4J = jR t4J * jR g ↔ g * t4J = t4J * g := fun g => by
    rw [← map_mul, ← map_mul]
    exact jR_injective.eq_iff
  constructor
  · intro hr
    have hr0 := (Subgroup.mem_centralizer_singleton_iff (g := jR t4J) (k := r)).1 hr
    rcases exists_jR_or r with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact Or.inl ⟨g, (Subgroup.mem_centralizer_singleton_iff (g := t4J) (k := g)).2
        ((key g).1 hr0), rfl⟩
    · refine Or.inr ⟨g, (Subgroup.mem_centralizer_singleton_iff (g := t4J) (k := g)).2
        ((key g).1 ?_), rfl⟩
      have e : jR g * cR * jR t4J = jR g * jR t4J * cR := by
        rw [mul_assoc, ← cR_comm_t4, ← mul_assoc]
      rw [e] at hr0
      exact mul_right_cancel (hr0.trans (mul_assoc _ _ _).symm)
  · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
    · exact (Subgroup.mem_centralizer_singleton_iff (g := jR t4J) (k := jR g)).2
        ((key g).2 ((Subgroup.mem_centralizer_singleton_iff (g := t4J) (k := g)).1 hg))
    · refine (Subgroup.mem_centralizer_singleton_iff (g := jR t4J) (k := jR g * cR)).2 ?_
      have h1 := (key g).2 ((Subgroup.mem_centralizer_singleton_iff (g := t4J) (k := g)).1 hg)
      rw [mul_assoc, ← cR_comm_t4, ← mul_assoc, h1, mul_assoc]

theorem CR_t4_eq :
    Subgroup.centralizer {jR t4J} = (Subgroup.centralizer {t4J}).map jR ⊔ Subgroup.zpowers cR := by
  apply le_antisymm
  · intro r hr
    rcases (mem_centralizer_t4_iff r).1 hr with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · exact Subgroup.mem_sup_left ⟨g, hg, rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, hg, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers cR))
  · rw [sup_le_iff, Subgroup.zpowers_le]
    refine ⟨?_, (Subgroup.mem_centralizer_singleton_iff (g := jR t4J) (k := cR)).2
      cR_comm_t4.symm⟩
    rintro _ ⟨g, hg, rfl⟩
    exact (mem_centralizer_t4_iff _).2 (Or.inl ⟨g, hg, rfl⟩)

end CFSG.Sporadic.HNOddCore
