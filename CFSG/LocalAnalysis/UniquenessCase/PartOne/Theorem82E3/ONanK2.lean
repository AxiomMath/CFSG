module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofModel
public import CFSG.GroupTheory.Commutator.SupNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)

private theorem centralizer_decomposition_of_model
    {Y : Type} [Group Y] [Finite Y]
    (ψ : Y ≃* CFSG.RankThree.Native.ONTriple.GM)
    (hZ3 : Nat.card (Subgroup.center Y) = 3)
    {x : Y} (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center Y) :
    ∃ (K : Subgroup Y) (ρ : ↥K →* Equiv.Perm (Fin 6)),
      Subgroup.centralizer ({x} : Set Y) = Subgroup.zpowers x ⊔ K ∧
      Subgroup.zpowers x ⊓ K = ⊥ ∧ Subgroup.center Y ≤ K ∧
      Group.IsPerfect ↥K ∧ ρ.range = alternatingGroup (Fin 6) ∧
      ∀ k : ↥K, ρ k = 1 ↔ (k : Y) ∈ Subgroup.center Y := by
  obtain ⟨K, hCeq, hinf, hZK, ρ, hρ, hker⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Proof156Res4.exists_centralizer_eq (X := Y) ψ hx3 hxZ
  have hKb : K ≤ Subgroup.centralizer ({x} : Set Y) := by
    rw [hCeq]
    exact le_sup_right
  have hperfK : Group.IsPerfect ↥K :=
    CFSG.RankThree.PartTwo.Sec15.Proof156Res4.isPerfect_of_centralizer_eq (X := Y) ψ hZ3 hx3
      hxZ hKb hinf hZK (ρ := ρ) hρ hker
  exact ⟨K, ρ, hCeq, hinf, hZK, hperfK, hρ, hker⟩

private theorem zpowers_le_centralizer_and_normalizer_of_eq_sup {G : Type} [Group G]
    (K : Subgroup G) (x : G)
    (hC : Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x ⊔ K) :
    Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) ∧
      Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) ∧
      Subgroup.zpowers x ≤ Subgroup.centralizer
        (Subgroup.centralizer ({x} : Set G) : Set G) := by
  have hKb : K ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hC]
    exact le_sup_right
  have hxK : x ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKb hk)
  have hBcentK : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hxK
  have hBnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) :=
    le_trans hBcentK (Subgroup.centralizer_le_normalizer (K : Set G))
  have hxcentC : x ∈ Subgroup.centralizer
      (Subgroup.centralizer ({x} : Set G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hBcentC : Subgroup.zpowers x ≤ Subgroup.centralizer
      (Subgroup.centralizer ({x} : Set G) : Set G) :=
    Subgroup.zpowers_le.mpr hxcentC
  exact ⟨hBcentK, hBnorm, hBcentC⟩

private theorem commutator_centralizer_eq_of_perfect_of_eq_sup {G : Type} [Group G]
    (C K : Subgroup G) (x : G) (hC : C = Subgroup.zpowers x ⊔ K)
    (hBnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G))
    (hBcentK : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G))
    (hBcentC : Subgroup.zpowers x ≤ Subgroup.centralizer (C : Set G))
    (hperfK : Group.IsPerfect ↥K) :
    ⁅C, C⁆ = K := by
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hperfK
  have h1 : ⁅K ⊔ Subgroup.zpowers x, C⁆ = ⁅K, C⁆ :=
    CFSG.commutator_sup_eq_commutator_left (A := K) (B := Subgroup.zpowers x) (U := C)
      hBnorm hBcentC
  have h2 : ⁅K, C⁆ = ⁅K ⊔ Subgroup.zpowers x, K⁆ := by
    rw [show C = K ⊔ Subgroup.zpowers x by rw [hC, sup_comm]]
    exact Subgroup.commutator_comm (H₁ := K) (H₂ := K ⊔ Subgroup.zpowers x)
  have h3 : ⁅K ⊔ Subgroup.zpowers x, K⁆ = ⁅K, K⁆ :=
    CFSG.commutator_sup_eq_commutator_left (A := K) (B := Subgroup.zpowers x) (U := K)
      hBnorm hBcentK
  calc ⁅C, C⁆ = ⁅K ⊔ Subgroup.zpowers x, C⁆ := by rw [hC, sup_comm]
    _ = ⁅K, C⁆ := h1
    _ = ⁅K ⊔ Subgroup.zpowers x, K⁆ := h2
    _ = ⁅K, K⁆ := h3
    _ = K := hKK

private theorem card_centralizer_and_quotient_of_eq_sup {G : Type} [Group G] [Finite G]
    (C K : Subgroup G) (x : G) (ρ : ↥K →* Equiv.Perm (Fin 6))
    (hC : C = Subgroup.zpowers x ⊔ K)
    (hZK : Subgroup.center G ≤ K)
    (hinf : Subgroup.zpowers x ⊓ K = ⊥)
    (hZ3 : Nat.card (Subgroup.center G) = 3)
    (hx3 : orderOf x = 3)
    (hBnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G))
    (hρ : ρ.range = alternatingGroup (Fin 6))
    (hker : ∀ k : ↥K, ρ k = 1 ↔ (k : G) ∈ Subgroup.center G) :
    Nat.card C = 3240 ∧ Nat.card K = 1080 ∧
      Nonempty ((K ⧸ (Subgroup.center G).subgroupOf K) ≃* alternatingGroup (Fin 6)) := by
  have hker_eq : ρ.ker = (Subgroup.center G).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, hker k, Subgroup.mem_subgroupOf]
  have hkerCard : Nat.card ρ.ker = 3 := by
    rw [hker_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv).trans hZ3
  have hrangeCard : Nat.card ρ.range = 360 := by
    rw [hρ, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hcardK : Nat.card K = 1080 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hkerCard, hrangeCard] at h
    norm_num at h
    exact h.symm
  have hdisj : Disjoint K (Subgroup.zpowers x) := by
    rw [disjoint_iff, inf_comm]
    exact hinf
  have hcardSup :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer K
      (Subgroup.zpowers x) hBnorm hdisj
  have hsup : C = K ⊔ Subgroup.zpowers x := by rw [hC, sup_comm]
  have hzxCard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hx3]
  have hcardC : Nat.card C = 3240 := by
    rw [hsup, hcardSup, hcardK, hzxCard]
  have hker_eq' : (Subgroup.center G).subgroupOf K = ρ.ker := hker_eq.symm
  refine ⟨hcardC, hcardK, ?_⟩
  change Nonempty
    ((K ⧸ (Subgroup.center G).subgroupOf K) ≃* alternatingGroup (Fin 6))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker_eq').trans
    ((QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hρ))⟩

theorem K2ONanCentralizer_holds :
    K2ONanCentralizer := by
  intro Y _ _ hcover x hx3 hxZ
  dsimp only
  let C : Subgroup Y := Subgroup.centralizer ({x} : Set Y)
  let J : Subgroup Y := ⁅C, C⁆
  change Nat.card C = 3240 ∧ Subgroup.center Y ≤ J ∧ Nat.card J = 1080 ∧
    C = Subgroup.zpowers x ⊔ J ∧
    IsAlt (J ⧸ (Subgroup.center Y).subgroupOf J) 6
  have hZ3 : Nat.card (Subgroup.center Y) = 3 := hcover.2.1
  have hperfY : Group.IsPerfect Y := Group.isPerfect_def.2 hcover.1.1
  have hsp : Nonempty ((Y ⧸ Subgroup.center Y) ≃* CFSG.Blueprint.NativeSporadic.ON) :=
    hcover.2.2
  have hT : IsTripleCover Y CFSG.Blueprint.NativeSporadic.ON := ⟨hZ3, hsp⟩
  obtain ⟨ψ⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.nonempty_equiv_model (X := Y) hperfY hT
  have hx3' : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  obtain ⟨K, ρ, hCeq, hinf, hZK, hperfK, hρ, hker⟩ :=
    centralizer_decomposition_of_model ψ hZ3 hx3' hxZ
  have hC' : C = Subgroup.zpowers x ⊔ K := hCeq
  obtain ⟨hBcentK, hBnorm, hBcentC⟩ :=
    zpowers_le_centralizer_and_normalizer_of_eq_sup K x hC'
  have hJK : J = K := by
    dsimp only [J]
    exact commutator_centralizer_eq_of_perfect_of_eq_sup C K x hC'
      hBnorm hBcentK hBcentC hperfK
  obtain ⟨hcardC, hcardK, hquot⟩ :=
    card_centralizer_and_quotient_of_eq_sup C K x ρ hC' hZK hinf hZ3 hx3 hBnorm hρ hker
  refine ⟨hcardC, ?_, ?_, ?_, ?_⟩
  · rw [hJK]
    exact hZK
  · rw [hJK]
    exact hcardK
  · rw [hJK]
    exact hC'
  · rw [hJK]
    change Nonempty ((K ⧸ (Subgroup.center Y).subgroupOf K) ≃* alternatingGroup (Fin 6))
    exact hquot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

end
