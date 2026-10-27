module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34LocalC
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Glue
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Model
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DC
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.F112HypW

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G]

structure L34LocalData (L1 L2 S : Subgroup G) : Prop where
  bigB_le : bigB L1 L2 S ≤ L1 ⊓ L2
  card_S : Nat.card S = 2 ^ 6
  elem_left : IsElemAbelian 2 (pCoreOf 2 L1)
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ 4
  nat_left : NatSec L1 ⊥ (pCoreOf 2 L1)
  elem_right : IsElemAbelian 2 (pCoreOf 2 L2)
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ 4
  nat_right : NatSec L2 ⊥ (pCoreOf 2 L2)
  card_inf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ 2

private theorem exists_orderOf_eq_three_of_isL2Quot [Finite G] {L : Subgroup G}
    (h : IsL2Quot 2 (oTwoQuot ↥L)) : ∃ x ∈ L, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) h]
    norm_num
  have hcard : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  have h3dvd : 3 ∣ Nat.card ↥L := by
    rw [hcard, h60]
    exact (show (3 : ℕ) ∣ 60 by norm_num).trans (dvd_mul_right 60 _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem isAmalgamOfGroup_psl3_of_l34LocalData [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : L34LocalData L1 L2 S) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hSL1 : S ≤ L1 := hSB.trans (hD.bigB_le.trans inf_le_left)
  have hSL2 : S ≤ L2 := hSB.trans (hD.bigB_le.trans inf_le_right)
  have hB1 : L1 ⊔ bigB L1 L2 S = L1 := sup_eq_left.mpr (hD.bigB_le.trans inf_le_left)
  have hB2 : L2 ⊔ bigB L1 L2 S = L2 := sup_eq_left.mpr (hD.bigB_le.trans inf_le_right)
  have hsyl1 : IsSylowTwoOf S L1 := by
    have := hR.hyp.h1.sylow
    rwa [inf_eq_left.mpr hSL1] at this
  have hsyl2 : IsSylowTwoOf S L2 := by
    have := hR.hyp.h2.sylow
    rwa [inf_eq_left.mpr hSL2] at this
  have hQ1S : pCoreOf 2 L1 ≤ S := F7.isSylowTwoOf_pCoreOf_le hsyl1
  have hQ2S : pCoreOf 2 L2 ≤ S := F7.isSylowTwoOf_pCoreOf_le hsyl2
  have hQ1eq : dsQ L1 L2 S = pCoreOf 2 L1 := by
    unfold dsQ
    rw [hB1]
  have hQ2eq : dsQ L2 L1 S = pCoreOf 2 L2 := by
    unfold dsQ
    rw [bigB_comm, hB2]
  have hS64 : Nat.card S = 64 := by rw [hD.card_S]; norm_num
  have hQ1c : Nat.card (pCoreOf 2 L1) = 16 := by rw [hD.card_left]; norm_num
  have hQ2c : Nat.card (pCoreOf 2 L2) = 16 := by rw [hD.card_right]; norm_num
  have hEcard : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 4 := by
    rw [hD.card_inf]; norm_num
  have hEcard' : Nat.card ↥(pCoreOf 2 L2 ⊓ pCoreOf 2 L1) = 4 := by
    rw [inf_comm]
    exact hEcard
  have hne : pCoreOf 2 L1 ≠ pCoreOf 2 L2 := by
    intro heq
    rw [heq, inf_idem, hQ2c] at hEcard
    norm_num at hEcard
  obtain ⟨x1, hx1L, hx1_3⟩ := exists_orderOf_eq_three_of_isL2Quot h1
  have hnt1 : ∃ l ∈ L1, ∃ e ∈ pCoreOf 2 L1, ⁅l, e⁆ ∉ (⊥ : Subgroup G) :=
    L34Loc.nontriv_of_natSec hD.nat_left hQ1c hx1L hx1_3
  obtain ⟨x2, hx2L, hx2_3⟩ := exists_orderOf_eq_three_of_isL2Quot h2
  have hnt2 : ∃ l ∈ L2, ∃ e ∈ pCoreOf 2 L2, ⁅l, e⁆ ∉ (⊥ : Subgroup G) :=
    L34Loc.nontriv_of_natSec hD.nat_right hQ2c hx2L hx2_3
  let Mdl : L34Model := L34.mdlPSL
  have hMdl : L34ModelFacts Mdl := L34.mdl_facts
  haveI : Finite Mdl.Y := by
    obtain ⟨_, F, hFF, hFfin, _, _, hiso⟩ :=
      CFSG.Quasithin.H13.F431.L3.exists_equiv_projSL3 Mdl.lie
    obtain ⟨e⟩ := hiso
    exact Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨x, hx3⟩ : ∃ x : ↥(Mdl.M1 ⊓ Mdl.M2), orderOf x = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [hMdl.card_B0]; norm_num)
  have hx3' : orderOf (x : Mdl.Y) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx3
  obtain ⟨ψ₁, hS1mem, hQ1mem, hN1mem⟩ :=
    L34Loc.side_iso hsyl1 hS64 hQ1S hD.elem_left hQ1c hQ2S hD.elem_right hQ2c hEcard
      hD.nat_left h1 hnt1 hMdl.sylow1 hMdl.card_T0 hMdl.elem1 hMdl.card1 hMdl.nat1 hMdl.quot1
      hMdl.elem2 hMdl.card2 hMdl.le1 hMdl.le2 hMdl.ne x.2 hx3'
  obtain ⟨ψ₂, hS2mem, hQ2mem, hN2mem⟩ :=
    L34Loc.side_iso hsyl2 hS64 hQ2S hD.elem_right hQ2c hQ1S hD.elem_left hQ1c hEcard'
      hD.nat_right h2 hnt2 hMdl.sylow2 hMdl.card_T0 hMdl.elem2 hMdl.card2 hMdl.nat2 hMdl.quot2
      hMdl.elem1 hMdl.card1 hMdl.le2 hMdl.le1 (Ne.symm hMdl.ne) ⟨x.2.2, x.2.1⟩ hx3'
  have hL1B : L1 ⊓ L2 = bigB L1 L2 S := by
    have := F1.parabolic_inf_parabolic hR
    rwa [hB1, hB2] at this
  have hL2B : L2 ⊓ L1 = bigB L1 L2 S := by
    have := F1.parabolic_inf_parabolic hR.symm
    rw [bigB_comm, hB2, hB1] at this
    exact this
  have hBN1 : bigB L1 L2 S = L1 ⊓ Subgroup.normalizer (S : Set G) := by
    have := F1.bigB_eq_parabolic_inf hR
    rw [hB1, inf_eq_left.mpr hsyl1.1] at this
    exact this
  have hBN2 : bigB L1 L2 S = L2 ⊓ Subgroup.normalizer (S : Set G) := by
    have := F1.bigB_eq_parabolic_inf hR.symm
    rw [bigB_comm, hB2, inf_eq_left.mpr hsyl2.1] at this
    exact this
  change IsAmalgamOfGroup
    (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
    (IsLieOverTwo .PSL 3 2)
  rw [hB1, hB2]
  have hQ1S' : dsQ L1 L2 S ≤ S := by rw [hQ1eq]; exact hQ1S
  have hQ2S' : dsQ L2 L1 S ≤ L2 := by rw [hQ2eq]; exact hQ2S.trans hSL2
  have hQ1e' : IsElemAbelian 2 (dsQ L1 L2 S) := by rw [hQ1eq]; exact hD.elem_left
  have hQ1c' : Nat.card (dsQ L1 L2 S) = 16 := by rw [hQ1eq]; exact hQ1c
  have hne' : dsQ L1 L2 S ≠ dsQ L2 L1 S := by rw [hQ1eq, hQ2eq]; exact hne
  have hB1mem : ∀ x : ↥L1, (x : G) ∈ L2 ↔ (ψ₁ x : Mdl.Y) ∈ Mdl.M2 := by
    intro x
    calc (x : G) ∈ L2 ↔ (x : G) ∈ L1 ⊓ L2 := by
          rw [Subgroup.mem_inf]
          exact ⟨fun h2 => ⟨x.2, h2⟩, fun h2 => h2.2⟩
      _ ↔ (x : G) ∈ bigB L1 L2 S := by rw [hL1B]
      _ ↔ (x : G) ∈ Subgroup.normalizer (S : Set G) := by
          rw [hBN1, Subgroup.mem_inf]
          exact ⟨fun h2 => h2.2, fun h2 => ⟨x.2, h2⟩⟩
      _ ↔ (ψ₁ x : Mdl.Y) ∈ Subgroup.normalizer (Mdl.T0 : Set Mdl.Y) := hN1mem x
      _ ↔ (ψ₁ x : Mdl.Y) ∈ Mdl.M2 := by
          rw [hMdl.normalizer_T0, Subgroup.mem_inf]
          exact ⟨fun h2 => h2.2, fun h2 => ⟨(ψ₁ x).2, h2⟩⟩
  have hB2mem : ∀ x : ↥L2, (x : G) ∈ L1 ↔ (ψ₂ x : Mdl.Y) ∈ Mdl.M1 := by
    intro x
    calc (x : G) ∈ L1 ↔ (x : G) ∈ L2 ⊓ L1 := by
          rw [Subgroup.mem_inf]
          exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
      _ ↔ (x : G) ∈ bigB L1 L2 S := by rw [hL2B]
      _ ↔ (x : G) ∈ Subgroup.normalizer (S : Set G) := by
          rw [hBN2, Subgroup.mem_inf]
          exact ⟨fun h1 => h1.2, fun h1 => ⟨x.2, h1⟩⟩
      _ ↔ (ψ₂ x : Mdl.Y) ∈ Subgroup.normalizer (Mdl.T0 : Set Mdl.Y) := hN2mem x
      _ ↔ (ψ₂ x : Mdl.Y) ∈ Mdl.M1 := by
          rw [hMdl.normalizer_T0, Subgroup.mem_inf]
          exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, (ψ₂ x).2⟩⟩
  have hQ1glue : ∀ x : ↥L1, (x : G) ∈ dsQ L1 L2 S ↔
      (ψ₁ x : Mdl.Y) ∈ pCoreOf 2 Mdl.M1 := by
    intro x
    rw [hQ1eq]
    exact hQ1mem x
  have hQ2glue : ∀ x : ↥L2, (x : G) ∈ dsQ L2 L1 S ↔
      (ψ₂ x : Mdl.Y) ∈ pCoreOf 2 Mdl.M2 := by
    intro x
    rw [hQ2eq]
    exact hQ2mem x
  haveI : DSLeaf LeafL34DC := ⟨leafL34DC⟩
  have iso := leafL34Glue Mdl hMdl ψ₁ ψ₂ hSL1 hSL2 hQ1S' hQ2S' hQ1e' hQ1c' hne'
    hS1mem hS2mem hB1mem hB2mem hQ1glue hQ2glue
  exact ⟨Mdl.Y, Mdl.grp, Mdl.lie, Mdl.T0, Mdl.M1, Mdl.M2, Mdl.pair, iso⟩

end CFSG.Quasithin.F112R.St84
