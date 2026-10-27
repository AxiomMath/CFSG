module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.BenderVertex
public import CFSG.Quasithin.Recognition.F112Crit.SettingOf
public import CFSG.Quasithin.Recognition.F112Crit.BenderQuot
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv
public import CFSG.Quasithin.SteinbergCDOddResidualTools

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.GH74.Uniqueness.Bender CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem borelOf_eq_of_vS3 (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1) :
    borelOf L1 S = S := by
  rw [F112TitsSlice.borelOf_eq_vs3 hR.hyp.h1 hS3, inf_eq_left.mpr hS]

theorem P₂_eq_sup_of_vS3 (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1) :
    P₂ L1 L2 S = L2 ⊔ S := by
  rw [P₂_swap_eq L2 L1 S, borelOf_eq_of_vS3 hR hS3 hS, sup_assoc, sup_idem]

theorem benderVertex_P₂ (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1)
    (hS : S ≤ L1) (hBig : VBig L2) (hnL2 : ¬ ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)) :
    BenderVertex (P₂ L1 L2 S) L2 := by
  have hP : P₂ L1 L2 S = L2 ⊔ S := P₂_eq_sup_of_vS3 hR hS3 hS
  have hL : IsRankOneListed (oTwoQuot ↥L2) := hR.hyp.h2.listed
  have hns : ¬ Group.IsSolvable (oTwoQuot ↥L2) := fun h =>
    VBig.not_isSolvable hL hBig (isSolvable_vertex_of_oTwoQuot h)
  have hnorm : P₂ L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    rw [hP]
    exact sup_le Subgroup.le_normalizer hR.hyp.h2.normalizes
  have hcases : Odd (Nat.card (Subgroup.center (oTwoQuot ↥L2))) ∧
      ((∃ a : ℕ, 1 ≤ a ∧ Nonempty
          (oTwoQuot ↥L2 ⧸ Subgroup.center (oTwoQuot ↥L2) ≃* CFSG.Open.Sz a)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
          Nat.card F = (2 ^ f) ^ 2 ∧
            Nonempty (oTwoQuot ↥L2 ⧸ Subgroup.center (oTwoQuot ↥L2) ≃*
              CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f) F)))) := by
    rcases cases_of_listed_of_not_isSolvable hL hns with
      ⟨n, -, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | ⟨n, hn, F, iF, iFin, hF, ⟨e⟩⟩ |
        ⟨n, hn, F, iF, iFin, hF, ⟨e⟩⟩
    · exact absurd ⟨n, ⟨e⟩⟩ hnL2
    ·
      have hns' : ¬ Group.IsSolvable ↥(CFSG.Open.Sz a) := by
        intro hsolv
        haveI := hsolv
        exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom)
          e.injective)
      haveI : IsSimpleGroup ↥(CFSG.Open.Sz a) :=
        (BenderType.suzuki a ha
          (MulEquiv.subgroupCongr (szModel_eq_open_sz a)).symm).isSimple
      have hnc : ∃ x y : ↥(CFSG.Open.Sz a), x * y ≠ y * x := by
        by_contra hcon
        push Not at hcon
        exact hns' (IsSimpleGroup.comm_iff_isSolvable.mp hcon)
      have hZ : Subgroup.center ↥(CFSG.Open.Sz a) = ⊥ :=
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
      have hZK : Subgroup.center (oTwoQuot ↥L2) = ⊥ := by
        have hmap := Subgroup.map_center_eq e
        rw [hZ] at hmap
        exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (oTwoQuot ↥L2))
          (f := (e : oTwoQuot ↥L2 →* ↥(CFSG.Open.Sz a))) e.injective).mp hmap
      refine ⟨?_, Or.inl ⟨a, ha, ⟨?_⟩⟩⟩
      · rw [hZK, Subgroup.card_bot]
        exact odd_one
      · exact (QuotientGroup.quotientMulEquivOfEq hZK).trans
          ((QuotientGroup.quotientBot (G := oTwoQuot ↥L2)).trans e)
    ·
      have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
        intro h
        have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
        have := Nat.pow_right_injective le_rfl h2
        omega
      have hZ : Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ n) F) =
          (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf
            (CFSG.Open.StatedSU 3 (2 ^ n) F) :=
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := n)
          (F := F) (n := 3) hF le_rfl hnq).2
      have hodd : Odd (Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ n) F))) := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
        have hzodd : Odd (orderOf z) := by
          have hmem : (z : CFSG.Open.StatedSU 3 (2 ^ n) F) ∈
              (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf
                (CFSG.Open.StatedSU 3 (2 ^ n) F) := by
            rw [← hZ]
            exact z.2
          have h := CFSG.Quasithin.statedSU_three_scalars_odd (n := n) (F := F)
            (z : CFSG.Open.StatedSU 3 (2 ^ n) F) hmem
          rw [← Subgroup.orderOf_mk (z : CFSG.Open.StatedSU 3 (2 ^ n) F) z.2] at h
          exact h
        rw [hz] at hzodd
        obtain ⟨k, hk⟩ := hzodd
        omega
      refine ⟨?_, Or.inr ⟨n, hn, F, iF, iFin, hF, ⟨?_⟩⟩⟩
      · have hcard : Nat.card (Subgroup.center (oTwoQuot ↥L2)) =
            Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ n) F)) := by
          rw [← Subgroup.card_map_of_injective
              (f := (e : oTwoQuot ↥L2 →* CFSG.Open.StatedSU 3 (2 ^ n) F)) e.injective,
            Subgroup.map_center_eq e]
        rw [hcard]
        exact hodd
      · exact (QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e
          (Subgroup.map_center_eq e)).trans (QuotientGroup.quotientMulEquivOfEq hZ)
    ·
      obtain ⟨eB, hB⟩ := CFSG.Quasithin.benderType_statedProj hn hF
      haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) :=
        hB.isSimple
      have hns' : ¬ Group.IsSolvable
          (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) := by
        intro hsolv
        haveI := hsolv
        exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom)
          e.injective)
      have hnc : ∃ x y : CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F),
          x * y ≠ y * x := by
        by_contra hcon
        push Not at hcon
        exact hns' (IsSimpleGroup.comm_iff_isSolvable.mp hcon)
      have hZP : Subgroup.center
          (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) = ⊥ :=
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
      have hZK : Subgroup.center (oTwoQuot ↥L2) = ⊥ := by
        have hmap := Subgroup.map_center_eq e
        rw [hZP] at hmap
        exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (oTwoQuot ↥L2))
          (f := (e : oTwoQuot ↥L2 →* CFSG.Open.StatedProj
            (CFSG.Open.StatedSU 3 (2 ^ n) F))) e.injective).mp hmap
      refine ⟨?_, Or.inr ⟨n, hn, F, iF, iFin, hF, ⟨?_⟩⟩⟩
      · rw [hZK, Subgroup.card_bot]
        exact odd_one
      · exact (QuotientGroup.quotientMulEquivOfEq hZK).trans
          ((QuotientGroup.quotientBot (G := oTwoQuot ↥L2)).trans e)
  refine ⟨?_, hnorm, ?_, isQuasisimple_of_listed hL hns, hcases.1, hcases.2⟩
  · rw [hP]
    exact le_sup_left
  ·
    intro h hh
    have hL2P : L2 ≤ P₂ L1 L2 S := le_sup_left
    have hSP : S ≤ P₂ L1 L2 S := by
      rw [hP]
      exact le_sup_right
    haveI hN : (L2.subgroupOf (P₂ L1 L2 S)).Normal :=
      (CFSG.Quasithin.BlueprintB2.normal_subgroupOf_iff_le_normalizer hL2P).2 hnorm
    have hsup : L2.subgroupOf (P₂ L1 L2 S) ⊔ S.subgroupOf (P₂ L1 L2 S) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hL2P hSP, ← hP, Subgroup.subgroupOf_self]
    have hSpg : IsPGroup 2 (S.subgroupOf (P₂ L1 L2 S)) := hR.hyp.h2.pgroup.comap_subtype
    obtain ⟨k, hk⟩ :=
      CFSG.Quasithin.SteinbergCD.exists_two_pow_mem_of_sup_eq_top hSpg hsup ⟨h, hh⟩
    exact ⟨k, by simpa using Subgroup.mem_subgroupOf.mp hk⟩

theorem conjClosure_P₂ (hR : Hyp111R L1 L2 S) {W : Subgroup G} (hW : W ≤ omegaOneCenterOf S) :
    conjClosure W (P₂ L1 L2 S) ≤ pCoreOf 2 (P₂ L1 L2 S) ∧
      pCoreOf 2 (P₂ L1 L2 S) ≤ Subgroup.centralizer (conjClosure W (P₂ L1 L2 S) : Set G) ∧
      IsElemAbelian 2 (conjClosure W (P₂ L1 L2 S)) ∧
      IsTwoReducedIn (P₂ L1 L2 S) (conjClosure W (P₂ L1 L2 S)) := by
  have hSyl : IsSylowTwoOf S (P₂ L1 L2 S) := F112W.isSylowTwoOf_parabolic' hR
  have hF : CharTwo (P₂ L1 L2 S) := by
    rw [P₂_swap_eq L2 L1 S]
    exact hR.hyp.h2.charTwo
  obtain ⟨hle, hel, hred⟩ :=
    conjClosure_isTwoReducedIn_of_charTwo hSyl hF hW
  refine ⟨hle.trans inf_le_left, ?_, hel, hred⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hle hv).2 x hx).symm

theorem not_le_centralizer_conjClosure (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1)
    (hc : centerOf (P₂ L1 L2 S) = ⊥) {W : Subgroup G} (hW : W ≤ omegaOneCenterOf S)
    (hW0 : W ≠ ⊥) :
    ¬ L2 ≤ Subgroup.centralizer (conjClosure W (P₂ L1 L2 S) : Set G) := by
  intro hL2
  have hP : P₂ L1 L2 S = L2 ⊔ S := P₂_eq_sup_of_vS3 hR hS3 hS
  have hL2W : L2 ≤ Subgroup.centralizer (W : Set G) :=
    hL2.trans (Subgroup.centralizer_le (le_conjClosure W (P₂ L1 L2 S)))
  have hSW : S ≤ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact hW.trans ((A4.omegaOneCenterOf_le_centerOf S).trans inf_le_right)
  have hSP : S ≤ P₂ L1 L2 S := by
    rw [hP]
    exact le_sup_right
  have hPW : P₂ L1 L2 S ≤ Subgroup.centralizer (W : Set G) := by
    rw [hP]
    exact sup_le hL2W hSW
  have hWP : W ≤ P₂ L1 L2 S :=
    (hW.trans (A4.omegaOneCenterOf_le_centerOf S)).trans (inf_le_left.trans hSP)
  have hWc : W ≤ centerOf (P₂ L1 L2 S) :=
    le_inf hWP (Subgroup.le_centralizer_iff.mpr hPW)
  rw [hc] at hWc
  exact hW0 (le_bot_iff.mp hWc)

end CFSG.Quasithin.F112Crit.APrime

end
