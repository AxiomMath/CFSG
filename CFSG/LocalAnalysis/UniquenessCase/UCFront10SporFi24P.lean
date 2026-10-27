module

public import Certificates.Certificate10511
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatSeq
public import CFSG.Sporadic.FischerOddCore.Fi24R2Order
import CFSG.Certificates.NativeValidSchreier
import CFSG.Certificates.SchreierBaseImageDecoding
import CFSG.Certificates.Kernel.SporLatDc2Sound
import CFSG.Certificates.Kernel.SporLatOmegaSound
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1K
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Kernel.SporSch.J4S.NoCP
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSpin
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSylow
import CFSG.LocalAnalysis.RankThreeUC.Asc1930
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1Rep
import CFSG.Quasithin.Background.A1bGroups
import CFSG.Quasithin.Background.B3Basic
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24P

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KD.Fi24PDc2 (L C D shapeOK letOK wOK sbOK)
open CFSG.Sporadic.FischerOddCore

section Order


@[expose] noncomputable def ga : ↥fi24P :=
  ⟨fi24Pa, by rw [fi24P_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def gb : ↥fi24P :=
  ⟨fi24Pb, by rw [fi24P_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem sep0 : ∀ g : ↥fi24P, (∀ p ∈ [0, 1, 2, 5], act 378 g p = p) → g = 1 := by
  intro g hg
  have hmem : (g : Equiv.Perm (Fin 378)) ∈ fi24P := g.2
  have hQ : CFSG.Certificates.ValidSchreier fi24PChain :=
    (CFSG.Certificates.validSchreier_of_chainOK fi24PChain_arrays (by norm_num)
      fi24PChain_facts.2.1).1
  let v : Fin fi24PChain.baseCount → Fin 378 := fun i => fi24PChain.base.get i
  have huniq := (fi24PChain.schreier_base_image_decoding hQ v).2.1
  have hbase_mem : ∀ j < 4, fi24PBase[j]! ∈ [0, 1, 2, 5] := by
    intro j hj
    interval_cases j <;> decide
  have hfix : ∀ i, (g : Equiv.Perm (Fin 378)) (fi24PChain.base.get i) = v i := by
    intro i
    have hb := fi24PChain_arrays.base_val i
    have hbc : fi24PChain.baseCount = 4 := by
      rw [← fi24PChain_arrays.base_size]
      rfl
    have hi : (i : Nat) < 4 := hbc ▸ i.2
    have hmem' : ((fi24PChain.base.get i : Fin 378) : Nat) ∈ [0, 1, 2, 5] := by
      rw [hb]
      exact hbase_mem (i : Nat) hi
    have e := hg ((fi24PChain.base.get i : Fin 378) : Nat) hmem'
    rw [act_eq, Subgroup.smul_def, Equiv.Perm.smul_def] at e
    exact Fin.ext e
  have hgdec : fi24PChain.decodePrefix v fi24PChain.baseCount =
      some (g : Equiv.Perm (Fin 378)) :=
    (huniq _).2 ⟨hmem, hfix⟩
  have h1dec : fi24PChain.decodePrefix v fi24PChain.baseCount =
      some (1 : Equiv.Perm (Fin 378)) :=
    (huniq _).2 ⟨Subgroup.one_mem _, fun i => rfl⟩
  exact Subtype.ext (Option.some.inj (hgdec.symm.trans h1dec))

theorem hN : Nat.card ↥fi24P = C.N1 * C.N2 * 2 ^ C.k := by
  change Nat.card ↥fi24P = 567 * 135 * 2 ^ 8
  rw [card_fi24P]
  norm_num

end Order

section Elements


@[expose] noncomputable def E0 : Array ↥fi24P := #[1, 1, 1, 1, 1, 1, ga, gb]

@[expose] noncomputable def hh (i : Nat) : ↥fi24P := evalElt E0 (CFSG.KD.Fi24PDc2.LT.hw.getD i [])

@[expose] noncomputable def E1 : Array ↥fi24P := #[1, 1, 1, 1, hh 0, hh 1, 1, 1]

@[expose] noncomputable def sg (i : Nat) : ↥fi24P := evalElt E1 (CFSG.KD.Fi24PDc2.LT.sgw.getD i [])

@[expose] noncomputable def els : List ↥fi24P :=
  [sg 0, sg 1, sg 2, sg 3, hh 0, hh 1, ga, gb]

end Elements

section Facts


theorem facts :
    CFSG.KC.SLD2.dc2Check C D = true ∧
    (∀ l < 2, ∀ p < 378, (fi24PStrong[l]!)[p]! = L (Nat.add 6 l) p) ∧
    shapeOK = true ∧ letOK = true ∧ D.sep = [0, 1, 2, 5] ∧ sbOK = true ∧
    CFSG.KD.Fi24PDc2.SB.C.flatten.length = 256 :=
  Certificates.certificate10511

theorem shape_parts :
    (∀ i < 2, ∀ l ∈ CFSG.KD.Fi24PDc2.LT.hw.getD i [], l = 6 ∨ l = 7) ∧
    ∀ i < 4, ∀ l ∈ CFSG.KD.Fi24PDc2.LT.sgw.getD i [], l = 4 ∨ l = 5 := by
  have h := facts.2.2.1
  unfold shapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := Nat.eq_of_beq_eq_true h1
  have e3 := Nat.eq_of_beq_eq_true h3
  refine ⟨fun i hi l hl => ?_, fun i hi l hl => ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega)] at hl
    rcases h2 _ (List.getElem_mem _) l hl with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · exact Or.inr (Nat.eq_of_beq_eq_true e)
  · rw [List.getD_eq_getElem _ _ (by omega)] at hl
    rcases h4 _ (List.getElem_mem _) l hl with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · exact Or.inr (Nat.eq_of_beq_eq_true e)

theorem let_parts :
    (∀ p < 378, L 4 p = wordF L (CFSG.KD.Fi24PDc2.LT.hw.getD 0 []) p) ∧
    (∀ p < 378, L 5 p = wordF L (CFSG.KD.Fi24PDc2.LT.hw.getD 1 []) p) ∧
    (∀ i < 4, ∀ p < 378, L i p = wordF L (CFSG.KD.Fi24PDc2.LT.sgw.getD i []) p) := by
  have h := facts.2.2.2.1
  unfold letOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h4, h5⟩, h0⟩, h1⟩, h2⟩, h3⟩ := h
  have wk : ∀ {l : Nat} {w : List Nat}, wOK l w = true → ∀ p < 378, L l p = wordF L w p :=
    fun {l w} hw p hp => by
      unfold wOK at hw
      exact Nat.eq_of_beq_eq_true (CFSG.KC.SLOm.all_range hw p hp)
  refine ⟨wk h4, wk h5, fun i hi p hp => ?_⟩
  interval_cases i
  · exact wk h0 p hp
  · exact wk h1 p hp
  · exact wk h2 p hp
  · exact wk h3 p hp

end Facts

theorem good_congr' {t : Array Nat} {f g : Nat → Nat} (h : Good 378 t f)
    (e : ∀ p < 378, f p = g p) : Good 378 t g :=
  ⟨h.1, fun p hp => by rw [← e p hp]; exact h.2 p hp⟩

section Letters


theorem good_a : Good 378 (tab 378 ga).toArray (L 6) := by
  refine ⟨tabA_size ga, fun p hp => ⟨?_, ?_⟩⟩
  · have ha : act 378 ga p = (fi24Pa ⟨p, hp⟩ : Nat) := by
      have e := act_eq ga ⟨p, hp⟩
      rw [Subgroup.smul_def, Equiv.Perm.smul_def] at e
      exact e
    rw [tabA_getD, ha, ← rep_fi24Pa ⟨p, hp⟩, facts.2.1 0 (by norm_num) p hp]
  · rw [← facts.2.1 0 (by norm_num) p hp, rep_fi24Pa ⟨p, hp⟩]
    exact Fin.isLt _

theorem good_b : Good 378 (tab 378 gb).toArray (L 7) := by
  refine ⟨tabA_size gb, fun p hp => ⟨?_, ?_⟩⟩
  · have ha : act 378 gb p = (fi24Pb ⟨p, hp⟩ : Nat) := by
      have e := act_eq gb ⟨p, hp⟩
      rw [Subgroup.smul_def, Equiv.Perm.smul_def] at e
      exact e
    rw [tabA_getD, ha, ← rep_fi24Pb ⟨p, hp⟩, facts.2.1 1 (by norm_num) p hp]
  · rw [← facts.2.1 1 (by norm_num) p hp, rep_fi24Pb ⟨p, hp⟩]
    exact Fin.isLt _

theorem good_E0 {l : Nat} (hl : l = 6 ∨ l = 7) :
    Good 378 (tab 378 (E0.getD l 1)).toArray (L l) := by
  rcases hl with rfl | rfl
  · exact good_a
  · exact good_b

theorem good_hh0 : Good 378 (tab 378 (hh 0)).toArray (L 4) :=
  good_congr' (good_evalElt E0 L fun l hl => good_E0 (shape_parts.1 0 (by norm_num) l hl))
    fun p hp => (let_parts.1 p hp).symm

theorem good_hh1 : Good 378 (tab 378 (hh 1)).toArray (L 5) :=
  good_congr' (good_evalElt E0 L fun l hl => good_E0 (shape_parts.1 1 (by norm_num) l hl))
    fun p hp => (let_parts.2.1 p hp).symm

theorem good_E1 {l : Nat} (hl : l = 4 ∨ l = 5) :
    Good 378 (tab 378 (E1.getD l 1)).toArray (L l) := by
  rcases hl with rfl | rfl
  · exact good_hh0
  · exact good_hh1

theorem good_sg {i : Nat} (hi : i < 4) : Good 378 (tab 378 (sg i)).toArray (L i) :=
  good_congr' (good_evalElt E1 L fun l hl => good_E1 (shape_parts.2 i hi l hl))
    fun p hp => (let_parts.2.2 i hi p hp).symm

theorem hL : ∀ l < C.nl, Good 378 (tab 378 (els.getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 8 := hl
  interval_cases l
  · exact good_sg (i := 0) (by norm_num)
  · exact good_sg (i := 1) (by norm_num)
  · exact good_sg (i := 2) (by norm_num)
  · exact good_sg (i := 3) (by norm_num)
  · exact good_hh0
  · exact good_hh1
  · exact good_a
  · exact good_b

end Letters

section Sylow


theorem hsep : ∀ g : ↥fi24P, (∀ p ∈ D.sep, act 378 g p = p) → g = 1 := by
  rw [facts.2.2.2.2.1]
  exact sep0

theorem card_S : Nat.card (Subgroup.closure {x | x ∈ els.take C.ns}) = 2 ^ C.k := by
  have hS : ∀ l < (els.take C.ns).length,
      Good 378 (tab 378 ((els.take C.ns).getD l 1)).toArray (L l) := by
    intro l hl
    have hl' : l < 4 := by simpa [els, C] using hl
    interval_cases l
    · exact hL 0 (by decide)
    · exact hL 1 (by decide)
    · exact hL 2 (by decide)
    · exact hL 3 (by decide)
  have hlen : (els.take C.ns).length = 4 := rfl
  have h := card_closure_of_omC (els.take C.ns) L hS (x0 := [0, 1, 2, 5]) (by decide) sep0
    (by rw [hlen]; exact facts.2.2.2.2.2.1)
  rw [h, facts.2.2.2.2.2.2]
  rfl

end Sylow

theorem fi24P_k105 :
    ∀ S H : Subgroup ↥CFSG.Sporadic.FischerOddCore.fi24P, IsSylowTwoOf S ⊤ → S ≤ H →
      Group.IsSolvable ↥H → ¬ 3 ∣ Nat.card ↥H → H ≤ S := by
  intro S H hS hSH _hsol h3
  have hsound := CFSG.KC.SLD2.dc2Check_sound (n := 378) C (by rfl) D els (by rfl) hL card_S hN
    hsep Certificates.certificate10511.1
  have hodd : ¬ 2 ∣ C.N1 * C.N2 := by
    change ¬ 2 ∣ 567 * 135
    decide
  have hS₀ : IsSylowTwoOf (Subgroup.closure {x | x ∈ els.take C.ns}) ⊤ := by
    refine ⟨le_top, IsPGroup.of_card card_S, ?_⟩
    rw [show ((Subgroup.closure {x | x ∈ els.take C.ns}).subgroupOf ⊤).index =
      (Subgroup.closure {x | x ∈ els.take C.ns}).index from Subgroup.relIndex_top_right _]
    have hi := Subgroup.card_mul_index (Subgroup.closure {x | x ∈ els.take C.ns})
    rw [card_S, hN, mul_comm (C.N1 * C.N2)] at hi
    rw [Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hi]
    exact hodd
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K.le_of_overgroups_sylow hS₀
    (fun Z hZ => hsound Z hZ) S H hS hSH h3

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24P

end
