module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4Lemma47c
public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.PLayer.Transfer
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4Meet_split {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hCfg : GGConfig 3 B Bs x L D J) (hCard : Nat.card Bs = 3 ^ 5)
    (hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹) :
    Nat.card (Bs ⊓ L : Subgroup G) = 3 ^ 4 ∧
      ∃ z : G, z ∈ L ∧ z ∈ Bs ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧
        L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({z} : Set G) := by
  have hp3 : Nat.Prime 3 := hCfg.tableB_facts.1
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hSstar : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hxne1 : x ≠ 1 := hSstar.2.2.1
  have hBsEA : IsElemAbelian 3 Bs := hCfg.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hCfg.2.1.2.2.2
  have hxBs : x ∈ Bs := hCfg.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hCfg.tableB_facts.2.2.2.1
  have horderx : orderOf x = 3 := hCfg.orderOf_x
  have hDB : D ≤ B := hCfg.2.2.1.1
  have hDBs : D ≤ Bs := hDB.trans hCfg.2.1.1
  have hDcard : Nat.card D = 3 ^ 2 := hCfg.2.2.1.2.2.1
  have hxD : x ∈ D := hCfg.2.2.1.2.2.2.1
  let A : Subgroup G := Bs ⊓ L
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
  have hCeq : C = Subgroup.zpowers x := by
    dsimp [C]
    exact hCfg.bstar_inf_centralizer_L
  have hcardC : Nat.card C = 3 := by
    rw [hCeq, Nat.card_zpowers, horderx]
  obtain ⟨hsplit_eq, hsplit_disj, -, -, -⟩ :=
    ggLemma47c (p := 3) (Bs := Bs) (X := L) hBsEA hSC hZL hInnL
  have hsplit_eq' : Bs = A ⊔ C := by
    dsimp [A, C]
    exact hsplit_eq
  have hdisj : A ⊓ C = ⊥ := by
    dsimp [A, C]
    simpa [inf_assoc, inf_left_comm, inf_comm] using hsplit_disj
  have hcommAC : ∀ a ∈ A, ∀ c ∈ C, Commute a c := by
    intro a ha c hc
    exact CFSG.Open.IsElemAbelian.comm hBsEA ha.1 hc.1
  have hcard_sup := CFSG.card_sup_eq_mul_of_commute A C hcommAC hdisj
  have hcardA_mul : Nat.card A * 3 = 3 ^ 5 := by
    calc Nat.card A * 3 = Nat.card ↥(A ⊔ C) := by rw [hcard_sup, hcardC]
      _ = Nat.card Bs := by rw [← hsplit_eq']
      _ = 3 ^ 5 := hCard
  have hcardA : Nat.card A = 3 ^ 4 := by
    have h := hcardA_mul
    norm_num at h ⊢
    omega
  have hxL_not : x ∉ L := by
    intro hxL
    have hxcenter : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2)
    have hxord_sub : orderOf (⟨x, hxL⟩ : ↥L) = 3 := by
      rw [Subgroup.orderOf_mk, horderx]
    have hcop := hZL (⟨x, hxL⟩ : ↥L) hxcenter
    rw [hxord_sub] at hcop
    exact (by decide : ¬ Nat.Coprime 3 3) hcop
  have hcardD : Nat.card D = 9 := by
    rw [hDcard]
    norm_num
  have hcardzx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, horderx]
  have hD_ne : D ≠ Subgroup.zpowers x := by
    intro h
    have h9 : Nat.card (Subgroup.zpowers x) = 9 := by
      rw [← h]
      exact hcardD
    rw [hcardzx] at h9
    norm_num at h9
  have hnot_le : ¬ D ≤ Subgroup.zpowers x := by
    intro hle
    exact hD_ne (le_antisymm hle (Subgroup.zpowers_le.mpr hxD))
  obtain ⟨d, hdD, hd_not_zx⟩ := Set.not_subset.mp hnot_le
  have hdBs : d ∈ Bs := hDBs hdD
  have hsplit_zx : Bs = A ⊔ Subgroup.zpowers x := by
    rw [hsplit_eq', hCeq]
  have hdsup : d ∈ A ⊔ Subgroup.zpowers x := by
    rw [← hsplit_zx]
    exact hdBs
  have hcommAzx : ∀ a ∈ A, ∀ c ∈ Subgroup.zpowers x, Commute a c := by
    intro a ha c hc
    exact CFSG.Open.IsElemAbelian.comm hBsEA ha.1 (Subgroup.zpowers_le.mpr hxBs hc)
  obtain ⟨e, heA, c, hc, hdec⟩ := (CFSG.mem_sup_of_commute hcommAzx).mp hdsup
  have hcD : c ∈ D := (Subgroup.zpowers_le.mpr hxD) hc
  have heD : e ∈ D := by
    have he : e = d * c⁻¹ := by
      rw [← hdec]
      group
    rw [he]
    exact D.mul_mem hdD (D.inv_mem hcD)
  have heL : e ∈ L := heA.2
  have heBs : e ∈ Bs := heA.1
  have he_ne1 : e ≠ 1 := by
    intro he1
    apply hd_not_zx
    rw [← hdec, he1, one_mul]
    exact hc
  have he3 : e ^ 3 = 1 := hBsEA.2 e heBs
  have heord : orderOf e = 3 := orderOf_eq_prime he3 he_ne1
  have hx_not_A : x ∉ A := by
    intro hxA
    exact hxL_not hxA.2
  have hxdisj : Subgroup.zpowers x ⊓ A = ⊥ :=
    CFSG.zpowers_inf_eq_bot_of_not_mem hp3 (hBsEA.2 x hxBs) hxne1 hx_not_A
  have hdisj_xe : Subgroup.zpowers x ⊓ Subgroup.zpowers e = ⊥ := by
    apply le_bot_iff.mp
    calc Subgroup.zpowers x ⊓ Subgroup.zpowers e
        ≤ Subgroup.zpowers x ⊓ A := inf_le_inf_left _ (Subgroup.zpowers_le.mpr heA)
      _ = ⊥ := hxdisj
  have hcomm_xe : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers e, Commute a b := by
    intro a ha b hb
    exact CFSG.Open.IsElemAbelian.comm hBsEA
      (Subgroup.zpowers_le.mpr hxBs ha) (Subgroup.zpowers_le.mpr heBs hb)
  have hcardSup_e : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) = 9 := by
    rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers x) (Subgroup.zpowers e)
      hcomm_xe hdisj_xe]
    rw [Nat.card_zpowers, Nat.card_zpowers, horderx, heord]
  have hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr heD)
    · rw [hcardD, hcardSup_e]
  have hcenD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) := by
    rw [hDgen, CFSG.centralizer_sup_zpowers_eq]
  have hL_Cx : L ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton x]
    exact hLx
  have hinf : L ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) = L :=
    inf_eq_left.mpr hL_Cx
  refine ⟨?_, ?_⟩
  · change Nat.card A = 3 ^ 4
    exact hcardA
  · refine ⟨e, heL, heBs, he_ne1, he3, ?_⟩
    rw [hcenD]
    rw [← inf_assoc, hinf]

end CFSG.StandardType

end
