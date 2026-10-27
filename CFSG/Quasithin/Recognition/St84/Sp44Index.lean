module

public import CFSG.Quasithin.Recognition.St84.Sp44Data
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alt
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open CFSG.QuasithinUnique.A5.Delta5 (Alt5)
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Sp44

private theorem centralizer_pCoreOf_eq_of_isL2Quot [Finite G] {L : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L))
    (hQab : IsMulCommutative ↥(pCoreOf 2 L))
    (hQcard : Nat.card (pCoreOf 2 L) = 2 ^ 6)
    (hZcard : Nat.card ↥(centerOf L) = 2 ^ 2) :
    L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) = pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  haveI : IsSimpleGroup (oTwoQuot ↥L) := e.isSimpleGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQsub : (pCoreOf 2 L).subgroupOf L = CFSG.Open.pCore 2 ↥L := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact (F1.mem_pCore_iff_coe x).symm
  have hQn : ((pCoreOf 2 L).subgroupOf L).Normal := by
    rw [hQsub]
    infer_instance
  have hCnorm :
      ((Subgroup.centralizer (pCoreOf 2 L : Set G)).subgroupOf L).Normal :=
    CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel.centralizer_subgroupOf_normal
      hQL hQn
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI hCmap :
      (((Subgroup.centralizer (pCoreOf 2 L : Set G)).subgroupOf L).map π).Normal :=
    Subgroup.Normal.map hCnorm π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((Subgroup.centralizer (pCoreOf 2 L : Set G)).subgroupOf L).map π) with hbot | htop
  · refine le_antisymm ?_ (le_inf hQL ?_)
    · intro x hx
      have hxL : x ∈ L := hx.1
      have hxC : (⟨x, hxL⟩ : ↥L) ∈
          (Subgroup.centralizer (pCoreOf 2 L : Set G)).subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        exact hx.2
      have hxmap : π ⟨x, hxL⟩ ∈
          ((Subgroup.centralizer (pCoreOf 2 L : Set G)).subgroupOf L).map π :=
        Subgroup.mem_map_of_mem π hxC
      rw [hbot, Subgroup.mem_bot] at hxmap
      have hxQ : (⟨x, hxL⟩ : ↥L) ∈ CFSG.Open.pCore 2 ↥L :=
        (QuotientGroup.eq_one_iff _).mp hxmap
      exact (F1.mem_pCore_iff_coe ⟨x, hxL⟩).mp hxQ
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro q' hq'
      exact (congrArg Subtype.val
        (hQab.is_comm.comm ⟨q, hq⟩ ⟨q', hq'⟩)).symm
  · exfalso
    have hLcent : L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hmem : π ⟨l, hl⟩ ∈
          ((Subgroup.centralizer (pCoreOf 2 L : Set G)).subgroupOf L).map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hcC, hck⟩ := Subgroup.mem_map.mp hmem
      have hcQ : (c : G) ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
        Subgroup.mem_subgroupOf.mp hcC
      have hdiff : ((c : ↥L)⁻¹ * ⟨l, hl⟩ : ↥L) ∈ CFSG.Open.pCore 2 ↥L :=
        QuotientGroup.eq.mp hck
      have hdiffQ : (c : G)⁻¹ * l ∈ pCoreOf 2 L := by
        have := (F1.mem_pCore_iff_coe ((c : ↥L)⁻¹ * ⟨l, hl⟩)).mp hdiff
        simpa using this
      have hcq : (c : G) * q = q * (c : G) :=
        (Subgroup.mem_centralizer_iff.mp hcQ q hq).symm
      have hdq : ((c : G)⁻¹ * l) * q = q * ((c : G)⁻¹ * l) :=
        congrArg Subtype.val (hQab.is_comm.comm ⟨_, hdiffQ⟩ ⟨q, hq⟩)
      exact (calc
        l * q = (c : G) * ((c : G)⁻¹ * l) * q := by group
        _ = (c : G) * (((c : G)⁻¹ * l) * q) := by group
        _ = (c : G) * (q * ((c : G)⁻¹ * l)) := by rw [hdq]
        _ = ((c : G) * q) * ((c : G)⁻¹ * l) := by group
        _ = (q * (c : G)) * ((c : G)⁻¹ * l) := by rw [hcq]
        _ = q * ((c : G) * ((c : G)⁻¹ * l)) := by group
        _ = q * l := by group).symm
    have hQcenter : pCoreOf 2 L ≤ centerOf L :=
      le_inf hQL (Subgroup.le_centralizer_iff.mp hLcent)
    have hle := Subgroup.card_le_of_le hQcenter
    rw [hQcard, hZcard] at hle
    norm_num at hle

theorem center_le_inf_of_core [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) (le_left : S ≤ L1) (le_right : S ≤ L2)
    (center_left : Nat.card ↥(centerOf L1) = 2 ^ 2)
    (elem_right : IsElemAbelian 2 (pCoreOf 2 L2))
    (card_right : Nat.card (pCoreOf 2 L2) = 2 ^ 6)
    (center_right : Nat.card ↥(centerOf L2) = 2 ^ 2) :
    centerOf L1 ≤ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl1 : IsSylowTwoOf S L1 := by
    have h := hF.1.h1.sylow
    rwa [inf_eq_left.mpr le_left] at h
  have hsyl2 : IsSylowTwoOf S L2 := by
    have h := hF.1.h2.sylow
    rwa [inf_eq_left.mpr le_right] at h
  have hQ1S : pCoreOf 2 L1 ≤ S := F7.isSylowTwoOf_pCoreOf_le hsyl1
  have hQ2S : pCoreOf 2 L2 ≤ S := F7.isSylowTwoOf_pCoreOf_le hsyl2
  have hZ1p : IsPGroup 2 ↥(centerOf L1) :=
    IsPGroup.of_card (n := 2) (by simpa using center_left)
  have hZ1norm : L1 ≤ Subgroup.normalizer (centerOf L1 : Set G) :=
    (Subgroup.le_centralizer_iff.mpr inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZ1Q1 : centerOf L1 ≤ pCoreOf 2 L1 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hZ1norm hZ1p
  have hZ1S : centerOf L1 ≤ S := hZ1Q1.trans hQ1S
  have hZ1centS : centerOf L1 ≤ Subgroup.centralizer (S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s (le_left hs)
  have hZ1centQ2 : centerOf L1 ≤ Subgroup.centralizer (pCoreOf 2 L2 : Set G) :=
    hZ1centS.trans (Subgroup.centralizer_le hQ2S)
  have hZ1L2 : centerOf L1 ≤ L2 := hZ1S.trans le_right
  have hC : L2 ⊓ Subgroup.centralizer (pCoreOf 2 L2 : Set G) = pCoreOf 2 L2 :=
    centralizer_pCoreOf_eq_of_isL2Quot h2 elem_right.1 card_right center_right
  exact le_inf hZ1Q1 ((le_inf hZ1L2 hZ1centQ2).trans (le_of_eq hC))

theorem idx_eq_three_of_core [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (le_left : S ≤ L1) (le_right : S ≤ L2)
    (center_left : Nat.card ↥(centerOf L1) = 2 ^ 2)
    (hZ : centerOf L1 ≤ pCoreOf 2 L2)
    (nat_right : NatSec L2 (centerOf L2) (pCoreOf 2 L2)) :
    L1.relIndex (L1 ⊔ bigB L1 L2 S) = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hsyl1 : IsSylowTwoOf S L1 := by
    have h := hF.1.h1.sylow
    rwa [inf_eq_left.mpr le_left] at h
  have hsyl2 : IsSylowTwoOf S L2 := by
    have h := hF.1.h2.sylow
    rwa [inf_eq_left.mpr le_right] at h
  have hQ2S : pCoreOf 2 L2 ≤ S := F7.isSylowTwoOf_pCoreOf_le hsyl2
  obtain ⟨e2⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two h2
  obtain ⟨D2, hD2B, hD2card, hD2inf, hD2sup⟩ :=
    CFSG.Quasithin.FA5.exists_cartan_three (L := L2) (S := S) hF.1.h2.sylow e2
  have hD2sup' : S ⊔ D2 = borelOf L2 S := by
    rwa [inf_eq_left.mpr le_right] at hD2sup
  have hD2inf' : D2 ⊓ S = ⊥ := by
    rwa [inf_eq_left.mpr le_right] at hD2inf
  have hD2B2 : D2 ≤ borelOf L2 S := hD2sup' ▸ le_sup_right
  have hD2N : D2 ≤ Subgroup.normalizer (S : Set G) := by
    refine hD2B.trans ?_
    have h := F1.borelOf_le_normalizer L2 S
    rwa [inf_eq_left.mpr le_right] at h
  have hSB1 : S ≤ borelOf L1 S := by
    have h := F1.sylow_le_borelOf L1 S
    rwa [inf_eq_left.mpr le_left] at h
  have hSB2 : S ≤ borelOf L2 S := by
    have h := F1.sylow_le_borelOf L2 S
    rwa [inf_eq_left.mpr le_right] at h
  have hD2notL1 : ¬ D2 ≤ L1 := by
    intro hD2L1
    have h3dvd : 3 ∣ Nat.card ↥D2 := by
      simpa [hD2card] using (dvd_refl 3 : 3 ∣ 3)
    obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    have hxD2 : (x : G) ∈ D2 := x.2
    have hxL1 : (x : G) ∈ L1 := hD2L1 hxD2
    have hxL2 : (x : G) ∈ L2 :=
      hD2B.trans (F1.borelOf_le L2 S) hxD2
    have hxord : orderOf (x : G) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx3
    have hZ12 : centerOf L1 ≤ centerOf L2 := by
      intro z hz
      have hzQ2 : z ∈ pCoreOf 2 L2 := hZ hz
      have hzx : z * (x : G) = (x : G) * z :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 (x : G) hxL1).symm
      have hcomm : ⁅z, (x : G)⁆ = 1 := by
        rw [commutatorElement_def, hzx]
        group
      exact (nat_right (x : G) hxL2 hxord) z hzQ2 (by
        rw [hcomm]
        exact (centerOf L2).one_mem)
    have hZ1p : IsPGroup 2 ↥(centerOf L1) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L2).to_le hZ
    have hZ1le : centerOf L1 ≤ L1 ⊔ L2 ⊔ S :=
      (hZ.trans hQ2S).trans le_sup_right
    have hN1 : L1 ≤ Subgroup.normalizer (centerOf L1 : Set G) :=
      (Subgroup.le_centralizer_iff.mpr inf_le_right).trans
        (Subgroup.centralizer_le_normalizer _)
    have hN2 : L2 ≤ Subgroup.normalizer (centerOf L1 : Set G) := by
      refine (show L2 ≤ Subgroup.centralizer (centerOf L1 : Set G) from ?_).trans
        (Subgroup.centralizer_le_normalizer _)
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (hZ12 hz)).2 l hl).symm
    have hNS : S ≤ Subgroup.normalizer (centerOf L1 : Set G) :=
      le_left.trans hN1
    have hbot := coreFree hF.1 hZ1p hZ1le hN1 hN2 hNS
    have hcard : Nat.card ↥(centerOf L1) = 1 := by
      rw [hbot]
      simp
    rw [center_left] at hcard
    norm_num at hcard
  have hB2notB1 : ¬ borelOf L2 S ≤ borelOf L1 S := fun hle =>
    hD2notL1 (hD2B2.trans (hle.trans (F1.borelOf_le L1 S)))
  have hSrelB2 : S.relIndex (borelOf L2 S) = 3 := by
    have hrel := F1.relIndex_sup_eq_of_le_normalizer (D := S) (T := D2) hD2N
    rw [sup_comm, hD2sup'] at hrel
    have hRHS : S.relIndex D2 = 3 := by
      calc
        S.relIndex D2 = (S ⊓ D2).relIndex D2 :=
          (Subgroup.inf_relIndex_right (H := S) (K := D2)).symm
        _ = (D2 ⊓ S).relIndex D2 := by rw [inf_comm]
        _ = (⊥ : Subgroup G).relIndex D2 := by rw [hD2inf']
        _ = Nat.card ↥D2 := Subgroup.relIndex_bot_left D2
        _ = 3 := hD2card
    exact hrel.trans hRHS
  have hdvd : (borelOf L1 S ⊓ borelOf L2 S).relIndex (borelOf L2 S) ∣
      S.relIndex (borelOf L2 S) :=
    Subgroup.relIndex_dvd_of_le_left (borelOf L2 S) (le_inf hSB1 hSB2)
  rw [hSrelB2] at hdvd
  have hne : (borelOf L1 S ⊓ borelOf L2 S).relIndex (borelOf L2 S) ≠ 1 := by
    intro h1
    exact hB2notB1 ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_left)
  have hI3 : (borelOf L1 S ⊓ borelOf L2 S).relIndex (borelOf L2 S) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hB : bigB L1 L2 S = borelOf L1 S ⊔ borelOf L2 S := by
    simp only [bigB]
    exact sup_eq_left.mpr (hSB1.trans le_sup_left)
  have hP : L1.relIndex (L1 ⊔ bigB L1 L2 S) = L1.relIndex (bigB L1 L2 S) := by
    rw [sup_comm]
    exact F1.relIndex_sup_eq_of_le_normalizer (D := L1) (T := bigB L1 L2 S)
      (F1.bigB_le_normalizer_left hR).1
  have hB2N : borelOf L2 S ≤ Subgroup.normalizer (borelOf L1 S : Set G) :=
    F1.borelOf_le_normalizer_borelOf hR
  calc
    L1.relIndex (L1 ⊔ bigB L1 L2 S)
        = L1.relIndex (bigB L1 L2 S) := hP
    _ = (L1 ⊓ bigB L1 L2 S).relIndex (bigB L1 L2 S) := by
          rw [Subgroup.inf_relIndex_right]
    _ = (borelOf L1 S).relIndex (bigB L1 L2 S) := by
          rw [F1.inf_bigB_eq_borelOf hR]
    _ = (borelOf L1 S).relIndex (borelOf L2 S) := by
          rw [hB, sup_comm]
          exact F1.relIndex_sup_eq_of_le_normalizer hB2N
    _ = (borelOf L1 S ⊓ borelOf L2 S).relIndex (borelOf L2 S) := by
          rw [Subgroup.inf_relIndex_right]
    _ = 3 := hI3

end Sp44

open Sp44 in
theorem Sp44LocalData.of_core [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (le_left : S ≤ L1) (le_right : S ≤ L2) (card_S : Nat.card S = 2 ^ 8)
    (elem_left : IsElemAbelian 2 (pCoreOf 2 L1))
    (card_left : Nat.card (pCoreOf 2 L1) = 2 ^ 6)
    (center_left : Nat.card ↥(centerOf L1) = 2 ^ 2)
    (nat_left : NatSec L1 (centerOf L1) (pCoreOf 2 L1))
    (indec_left : ⁅pCoreOf 2 L1, L1⁆ = pCoreOf 2 L1)
    (elem_right : IsElemAbelian 2 (pCoreOf 2 L2))
    (card_right : Nat.card (pCoreOf 2 L2) = 2 ^ 6)
    (center_right : Nat.card ↥(centerOf L2) = 2 ^ 2)
    (nat_right : NatSec L2 (centerOf L2) (pCoreOf 2 L2))
    (indec_right : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2)
    (card_inf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ 4) :
    Sp44LocalData L1 L2 S := by
  have hZleft : centerOf L1 ≤ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 :=
    Sp44.center_le_inf_of_core hF h2 le_left le_right center_left elem_right card_right
      center_right
  have hZright : centerOf L2 ≤ pCoreOf 2 L2 ⊓ pCoreOf 2 L1 :=
    Sp44.center_le_inf_of_core hF.symm h1 le_right le_left center_right elem_left card_left
      center_left
  have hidx_left : L1.relIndex (L1 ⊔ bigB L1 L2 S) = 3 :=
    Sp44.idx_eq_three_of_core hF h2 le_left le_right center_left
      (hZleft.trans inf_le_right) nat_right
  have hidx_right : L2.relIndex (L2 ⊔ bigB L1 L2 S) = 3 := by
    have h := Sp44.idx_eq_three_of_core (L1 := L2) (L2 := L1) (S := S)
      hF.symm h1 le_right le_left center_right (hZright.trans inf_le_right) nat_left
    rwa [bigB_comm L1 L2 S] at h
  exact
    { le_left := le_left
      le_right := le_right
      card_S := card_S
      elem_left := elem_left
      card_left := card_left
      center_left := center_left
      nat_left := nat_left
      indec_left := indec_left
      idx_left := hidx_left
      elem_right := elem_right
      card_right := card_right
      center_right := center_right
      nat_right := nat_right
      indec_right := indec_right
      idx_right := hidx_right
      card_inf := card_inf }

end CFSG.Quasithin.F112R.St84
