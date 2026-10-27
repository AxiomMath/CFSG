module

public import CFSG.RankThree.GF2n.Parrott.Section3Commutator
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

noncomputable def sigma1Commutator (D : QuotientData (z := z) hN) : Subgroup G :=
  ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆

theorem card_CJ_eq_card_centralizerJ (x : ↥(H z)) :
    Nat.card (CJ z (x : G)) = Nat.card (centralizerJ x) := by
  let C : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G) ⊓ J z
  have hCJ : centralizerJ x = C.subgroupOf (J z) := rfl
  rw [hCJ]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : C ≤ J z)).toEquiv).symm

theorem conjV_mul_mem_J (h : Tim79a.ParrottHyp z) {x j : ↥(H z)}
    (hj : (j : G) ∈ J z) : conjV h (x * j) = conjV h x := by
  have hker : j ∈ (conjV h).ker :=
    J_le_ker_conjV (z := z) h (Subgroup.mem_subgroupOf.mpr hj)
  have hj1 : conjV h j = 1 := MonoidHom.mem_ker.mp hker
  rw [map_mul, hj1, mul_one]

theorem conjV_mem_J_mul (h : Tim79a.ParrottHyp z) {x j : ↥(H z)}
    (hj : (j : G) ∈ J z) : conjV h (j * x) = conjV h x := by
  have hker : j ∈ (conjV h).ker :=
    J_le_ker_conjV (z := z) h (Subgroup.mem_subgroupOf.mpr hj)
  have hj1 : conjV h j = 1 := MonoidHom.mem_ker.mp hker
  rw [map_mul, hj1, one_mul]

theorem CJ_sigma1_le_normalizer_sigma1Commutator :
    CJ z (sigma1Nine D : G) ≤
      Subgroup.normalizer (sigma1Commutator (z := z) D : Set G) := by
  intro a ha
  let f : G →* G := (MulAut.conj (a : G)).toMonoidHom
  have haJ : (a : G) ∈ J z := ha.2
  have haC : (a : G) ∈ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G) := ha.1
  have hcomm : Commute (a : G) (sigma1Nine D : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp haC
  have hconjσ : f (sigma1Nine D : G) = (sigma1Nine D : G) := by
    change (MulAut.conj (a : G)) (sigma1Nine D : G) = (sigma1Nine D : G)
    rw [MulAut.conj_apply]
    calc (a : G) * (sigma1Nine D : G) * (a : G)⁻¹
        = (sigma1Nine D : G) * (a : G) * (a : G)⁻¹ := by rw [hcomm.eq]
      _ = (sigma1Nine D : G) := by group
  have hB : (Subgroup.zpowers (sigma1Nine D : G)).map f =
      Subgroup.zpowers (sigma1Nine D : G) := by
    rw [MonoidHom.map_zpowers, hconjσ]
  have hJ : (J z).map f = J z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := J z) haJ)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (sigma1Commutator (z := z) D).map (MulAut.conj (a : G)).toMonoidHom =
    sigma1Commutator (z := z) D
  rw [sigma1Commutator, Subgroup.map_commutator,
    map_zpowers_sigma_eq (z := z) (σ := sigma1Nine D), hB, hJ]

theorem CJ_eq_sup_inf_sigma1Commutator_of_le (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    (hle : CJ z (sigma1Nine D : G) ≤ CJ z (x : G)) :
    CJ z (x : G) = CJ z (sigma1Nine D : G) ⊔
      (CJ z (x : G) ⊓ sigma1Commutator (z := z) D) := by
  classical
  let A : Subgroup G := CJ z (sigma1Nine D : G)
  let P : Subgroup G := sigma1Commutator (z := z) D
  let C : Subgroup G := CJ z (x : G)
  have hA_N : A ≤ Subgroup.normalizer (P : Set G) :=
    CJ_sigma1_le_normalizer_sigma1Commutator (z := z) D
  have hJ : J z = A ⊔ P := by
    have h := J_eq_centralizer_commutator_sigma1Nine (z := z) h D
    simpa only [A, P, sigma1Commutator, CJ, inf_comm] using h
  apply le_antisymm
  · intro c hc
    have hcJ : c ∈ J z := hc.2
    have hcPA : c ∈ P ⊔ A := by
      rw [sup_comm, ← hJ]
      exact hcJ
    obtain ⟨p, hpP, a, haA, hpa⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
        (H := P) (K := A) hA_N).mp hcPA
    have haC : a ∈ C := hle haA
    have hpC : p ∈ C := by
      have hp_eq : p = (p * a) * a⁻¹ := by group
      rw [hp_eq]
      exact C.mul_mem (hpa ▸ hc) (C.inv_mem haC)
    have hmem : p * a ∈ (C ⊓ P) ⊔ A :=
      Subgroup.mul_mem_sup (S := C ⊓ P) (T := A)
        (Subgroup.mem_inf.mpr ⟨hpC, hpP⟩) haA
    have hmem' : c ∈ (C ⊓ P) ⊔ A := by
      rw [← hpa] at hmem
      exact hmem
    simpa only [sup_comm] using hmem'
  · exact sup_le hle inf_le_left

theorem card_CJ_eq_eight_mul_card_inf_sigma1Commutator (h : Tim79a.ParrottHyp z)
    {x : ↥(H z)} (hle : CJ z (sigma1Nine D : G) ≤ CJ z (x : G)) :
    Nat.card (CJ z (x : G)) = 8 *
      Nat.card ↥(CJ z (x : G) ⊓ sigma1Commutator (z := z) D) := by
  classical
  let A : Subgroup G := CJ z (sigma1Nine D : G)
  let P : Subgroup G := sigma1Commutator (z := z) D
  let C : Subgroup G := CJ z (x : G)
  let K : Subgroup G := C ⊓ P
  have hA_N : A ≤ Subgroup.normalizer (P : Set G) :=
    CJ_sigma1_le_normalizer_sigma1Commutator (z := z) D
  have hA_NK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (K).map (MulAut.conj (a : G)).toMonoidHom = K
    dsimp only [K]
    rw [Subgroup.map_inf C P (MulAut.conj (a : G)).toMonoidHom
      (MulAut.conj (a : G)).injective]
    have hCmap : C.map (MulAut.conj (a : G)).toMonoidHom = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer (H := C) (hle ha))
    have hPmap : P.map (MulAut.conj (a : G)).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA_N ha)
    rw [hCmap, hPmap]
  have hsup : C = A ⊔ K := by
    simpa only [A, P, C, K] using
      CJ_eq_sup_inf_sigma1Commutator_of_le (z := z) (D := D) h (x := x) hle
  have hAP : A ⊓ P = Subgroup.zpowers z := by
    simpa only [A, P, sigma1Commutator, CJ, inf_comm, inf_assoc] using
      centralizer_inf_commutator_eq_sigma1Nine (z := z) h D
  have hAK : A ⊓ K = Subgroup.zpowers z := by
    dsimp only [K]
    rw [← inf_assoc, inf_eq_left.mpr hle, hAP]
  have hAcard : Nat.card A = 16 := by
    show Nat.card (CJ z (sigma1Nine D : G)) = 16
    rw [card_CJ_eq_card_centralizerJ]
    exact card_centralizerJ_sigma1Nine (z := z) h D
  have hZcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, h.1]
  have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := A) (K := K) hA_NK
  rw [← hsup, hAK, hAcard, hZcard] at hcard
  change Nat.card ↥C = 8 * Nat.card ↥K
  omega

theorem fixDimV_eq_four_of_card_inf_sigma1Commutator (h : Tim79a.ParrottHyp z)
    {x : ↥(H z)} (hx : orderOf x = 3) (hZ : conjZ z x = 1)
    (hle : CJ z (sigma1Nine D : G) ≤ CJ z (x : G))
    (hcardK : Nat.card ↥(CJ z (x : G) ⊓ sigma1Commutator (z := z) D) = 8) :
    fixDimV h x = 4 := by
  have hcop : Nat.Coprime (orderOf x) (Nat.card (J z)) := by
    rw [hx, card_J h]
    norm_num
  have hfixed := card_centralizer_eq_card_inf_centerIn_mul_card_fixedBy
    (z := z) h (x := x) hcop
  have hZle : centerIn (J z) ≤ CJ z (x : G) := by
    intro y hy
    rw [mem_CJ]
    exact ⟨centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := x) hZ hy, hy.1⟩
  have hCZ : Subgroup.centralizer ({(x : G)} : Set G) ⊓ centerIn (J z) =
      CJ z (x : G) ⊓ centerIn (J z) := by
    rw [CJ, inf_assoc]
    congr 1
    exact (inf_eq_right.mpr (inf_le_left : centerIn (J z) ≤ J z)).symm
  have hZcard : Nat.card ↥(CJ z (x : G) ⊓ centerIn (J z)) = 4 := by
    rw [inf_eq_right.mpr hZle]
    exact card_centerIn_J (z := z) h
  have hfixcard : Nat.card (MulAction.fixedBy (QuotientV.V z)
      (MulAut.toPerm (QuotientV.V z) (conjV h x))) = 2 ^ fixDimV h x := by
    rw [← card_autFixedSubgroup_conjV_eq_card_fixedBy (z := z) h x,
      card_fix (z := z) h x]
  rw [hCZ] at hfixed
  change Nat.card ↥(CJ z (x : G)) = Nat.card ↥(CJ z (x : G) ⊓ centerIn (J z)) *
      Nat.card (MulAction.fixedBy (QuotientV.V z)
        (MulAut.toPerm (QuotientV.V z) (conjV h x))) at hfixed
  rw [hZcard, hfixcard] at hfixed
  have hCcard := card_CJ_eq_eight_mul_card_inf_sigma1Commutator
    (z := z) (D := D) h (x := x) hle
  rw [hcardK] at hCcard
  have hpow : 2 ^ fixDimV h x = 16 := by omega
  have h4 : 2 ^ (4 : ℕ) = 16 := by norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hpow.trans h4.symm)

theorem sigma1_mul_sigma2_mem_A : sigma1 * sigma2 ∈ QA45.originalSubgroup :=
  QA45.originalSubgroup.mul_mem sigma1_mem_A sigma2_mem_A

theorem sigma1_mul_sigma2_inv_mem_A : sigma1 * sigma2⁻¹ ∈ QA45.originalSubgroup :=
  QA45.originalSubgroup.mul_mem sigma1_mem_A (QA45.originalSubgroup.inv_mem sigma2_mem_A)

theorem card_centralizer_sigma1_mul_sigma2_QA45 :
    Nat.card (Subgroup.centralizer
      ({⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩} : Set QA45.originalSubgroup)) = 216 := by
  rw [card_centralizer_QA45_eq_filter (sigma1 * sigma2) sigma1_mul_sigma2_mem_A]
  exact Certificates.certificate946005.centralizer_sigma1sigma2

theorem card_centralizer_sigma1_mul_sigma2_inv_QA45 :
    Nat.card (Subgroup.centralizer
      ({⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩} : Set QA45.originalSubgroup)) = 108 := by
  rw [card_centralizer_QA45_eq_filter (sigma1 * sigma2⁻¹) sigma1_mul_sigma2_inv_mem_A]
  exact Certificates.certificate946005.centralizer_sigma1sigma2inv

theorem sigma1_mul_sigma2_ne_one :
    (⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩ : QA45.originalSubgroup) ≠ 1 := by
  intro h1
  have hcard := card_centralizer_sigma1_mul_sigma2_QA45
  have htop : Subgroup.centralizer
      ({⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩} : Set QA45.originalSubgroup) = ⊤ := by
    rw [h1]
    simp
  rw [htop, Subgroup.card_top, card_QA45] at hcard
  norm_num at hcard

theorem sigma1_mul_sigma2_inv_ne_one :
    (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : QA45.originalSubgroup) ≠ 1 := by
  intro h1
  have hcard := card_centralizer_sigma1_mul_sigma2_inv_QA45
  have htop : Subgroup.centralizer
      ({⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩} : Set QA45.originalSubgroup) = ⊤ := by
    rw [h1]
    simp
  rw [htop, Subgroup.card_top, card_QA45] at hcard
  norm_num at hcard

end CFSG.RankThree.GF2n.Parrott
