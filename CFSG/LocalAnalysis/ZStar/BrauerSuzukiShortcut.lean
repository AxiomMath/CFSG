module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Suzuki.VI.section_2_2.example_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.LocalAnalysis.ZStar.CentralizerInduction
public import CFSG.LocalAnalysis.ZStar.TerminalIndexTwo
public import CFSG.LocalAnalysis.ZStar.PadicTrace

public section

namespace CFSG

namespace ZStar.BrauerSuzukiShortcut

open ZStar.CentralizerInduction
open ZStar
open ZStar.TransferReduction
open BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G] [Fintype G]

private theorem orderOf_eq_two_of_ne_one_sq_eq_one_local
    {X : Type*} [Group X] [Finite X] {x : X}
    (hx1 : x ≠ 1) (hx2 : x * x = 1) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    simpa [pow_two] using hx2
  have hpos : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos
  have hneOne : orderOf x ≠ 1 := by
    intro hone
    exact hx1 (orderOf_eq_one_iff.mp hone)
  have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  omega

private theorem not_isCyclic_sylow_two_of_commutator_eq_top
    {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G))
    (hperfect : commutator G = ⊤) : ¬ IsCyclic P := by
  intro hPcyclic
  let _ : IsCyclic P := hPcyclic
  let : CommGroup P := IsMulCommutative.instCommGroup
  have htOrder : orderOf t = 2 :=
    orderOf_eq_two_of_ne_one_sq_eq_one_local ht1 ht2
  have htwoCard : 2 ∣ Nat.card G := by
    rw [← htOrder]
    exact orderOf_dvd_natCard t
  have hminFac : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card G)).2 htwoCard
  have hnormalizer := IsCyclic.normalizer_le_centralizer hminFac hPcyclic
  let f : G →* P := MonoidHom.transferSylow P hnormalizer
  have hcomplement : f.ker.IsComplement' (P : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' P hnormalizer
  have hkerTop : f.ker = ⊤ := by
    apply top_unique
    rw [← hperfect]
    exact Abelianization.commutator_subset_ker (A := P) f
  have hdisjoint : Disjoint (P : Subgroup G) ⊤ := by
    have h := hcomplement.disjoint.symm
    rwa [hkerTop] at h
  have hPbot : (P : Subgroup G) = ⊥ := disjoint_top.mp hdisjoint
  apply ht1
  have : t ∈ (⊥ : Subgroup G) := by
    rw [← hPbot]
    exact htP
  simpa using this

private theorem sylow_two_cyclic_or_quaternion_of_uniqueInvolution
    {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G))
    (hunique : UniqueInvolutionIn (P : Subgroup G) t) :
    IsCyclic P ∨
      ∃ n : ℕ, 3 ≤ n ∧
        Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))) := by
  classical
  let z : P := ⟨t, htP⟩
  have hzorder : orderOf z = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_two_of_ne_one_sq_eq_one_local ht1 ht2
  have huniqueP : ∀ x : P, IsInvolution x → x = z := by
    intro x hx
    apply Subtype.ext
    apply hunique (x : G) x.property
    · intro hx1
      exact hx.ne_one (Subtype.ext hx1)
    · simpa [pow_two] using congrArg Subtype.val hx.sq_eq_one
  let U : Subgroup P := Subgroup.zpowers z
  have hUcard : Nat.card U = 2 := by
    change Nat.card (Subgroup.zpowers z) = 2
    rw [Nat.card_zpowers, hzorder]
  have huniqueU : ∀ V : Subgroup P, Nat.card V = 2 → V = U := by
    intro V hVcard
    have htwoV : 2 ∣ Nat.card V := by
      rw [hVcard]
    obtain ⟨v, hvorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := V) 2 htwoV
    have hvorderP : orderOf (v : P) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hvorder
    have hvI : IsInvolution (v : P) := by
      have hv := orderOf_eq_prime_iff.mp hvorderP
      exact ⟨hv.2, by simpa [pow_two] using hv.1⟩
    have hzv : z = (v : P) := (huniqueP (v : P) hvI).symm
    have hzp_le : Subgroup.zpowers (v : P) ≤ V :=
      Subgroup.zpowers_le.mpr v.property
    rw [← hzv] at hzp_le
    exact
      (Subgroup.eq_of_le_of_card_ge hzp_le
        (by rw [hUcard, hVcard])).symm
  have hclass :=
    BenderSuzuki.External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
      (G := P) (p := 2) Nat.prime_two P.isPGroup'
      ⟨U, hUcard, huniqueU⟩
  exact hclass.2 rfl

private theorem zStarConclusion_of_noncyclic_uniqueInvolution
    {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G))
    (hunique : UniqueInvolutionIn (P : Subgroup G) t)
    (hPnoncyclic : ¬ IsCyclic P) :
    ZStarConclusion G t := by
  classical
  rcases
      sylow_two_cyclic_or_quaternion_of_uniqueInvolution
        ht1 ht2 P htP hunique with
    hPcyclic | ⟨n, hn, hquat⟩
  · exact (hPnoncyclic hPcyclic).elim
  have htorder : orderOf t = 2 :=
    orderOf_eq_two_of_ne_one_sq_eq_one_local ht1 ht2
  have htcenter :
      QuotientGroup.mk' (pPrimeCore 2 G) t ∈
        Subgroup.center (G ⧸ pPrimeCore 2 G) :=
    CFSG.BenderSuzuki.Background.Suzuki.VI.suzuki_chapter6_section2_2_example3_involution_mem_center
        P hn hquat t htorder
  refine ⟨pPrimeCore 2 G, inferInstance, ?_, ?_⟩
  · exact (pPrimeCore_coprime_card (G := G) (p := 2)).odd_of_left
  · intro g
    apply (QuotientGroup.eq_one_iff
      (N := pPrimeCore 2 G) (g * t * g⁻¹ * t⁻¹)).mp
    have hcomm :=
      Subgroup.mem_center_iff.mp htcenter
        (QuotientGroup.mk' (pPrimeCore 2 G) g)
    calc
      QuotientGroup.mk' (pPrimeCore 2 G) g *
              QuotientGroup.mk' (pPrimeCore 2 G) t *
              (QuotientGroup.mk' (pPrimeCore 2 G) g)⁻¹ *
              (QuotientGroup.mk' (pPrimeCore 2 G) t)⁻¹ =
          QuotientGroup.mk' (pPrimeCore 2 G) t *
              QuotientGroup.mk' (pPrimeCore 2 G) g *
              (QuotientGroup.mk' (pPrimeCore 2 G) g)⁻¹ *
              (QuotientGroup.mk' (pPrimeCore 2 G) t)⁻¹ := by
            rw [hcomm]
      _ = 1 := by simp

theorem zStarConclusion_of_perfect_uniqueInvolution_brauerSuzuki
    {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G))
    (hunique : UniqueInvolutionIn (P : Subgroup G) t)
    (hperfect : commutator G = ⊤) :
    ZStarConclusion G t := by
  apply zStarConclusion_of_noncyclic_uniqueInvolution
    ht1 ht2 P htP hunique
  exact not_isCyclic_sylow_two_of_commutator_eq_top
    ht1 ht2 P htP hperfect

end ZStar.BrauerSuzukiShortcut

end CFSG
