module

import CFSG.LocalAnalysis.StandardType.GGK1ScLaneA
import CFSG.LocalAnalysis.StandardType.GGK1ScLaneC
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce
import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
import CFSG.CGT.PushingUpLit.SYMB.ProdCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_center_of_qTwoCl
    {Bs K : Subgroup G}
    (hlab : GGInnerDiagOnLabel (fun _ lab => GGQTwoClLabel lab) 3 Bs K) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
  obtain ⟨hperf, lab, hlabΛ, hraw⟩ := hlab
  obtain ⟨R₀, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hQtwo, -⟩ := hQ₀
  have hn : lab.n = 1 := by
    have h1 := hlabΛ.1
    have h2 := hQtwo.1
    omega
  have hgen : GGKacGenericCl lab 3 := by
    refine ⟨Nat.prime_three, by norm_num, Or.inr ?_, ?_, ?_, ?_⟩
    · rw [hn]
      norm_num
    · rcases hQtwo.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rintro ⟨-, -, h⟩
      rw [hn] at h
      norm_num at h
    · rintro ⟨htw, -⟩
      rcases hQtwo.2 with h | h | h
      · rw [h] at htw
        exact absurd htw (by decide)
      · rw [h] at htw
        exact absurd htw (by decide)
      · rw [h] at htw
        exact absurd htw (by decide)
  have derive : LargeEvenLabelAll lab (fun R _ _ _ => GGCenterPrime 3 R) →
      ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
    intro hAll
    obtain ⟨R, hR, I, F, hQ, hcp⟩ := largeEvenRawDatum_exists (hAll _ hraw)
    obtain ⟨-, -, θ, -⟩ := hQ
    let ψ : ↥K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
    have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : ψ.ker ≤ Subgroup.center ↥K := by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have hx1 : QuotientGroup.mk' (Subgroup.center ↥K) x = 1 :=
        θ.injective (by simpa using hx)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      exact hx1
    exact hcp ↥K ψ hψ hker hperf
  rcases hQtwo.2 with hA | hB | hC
  · exact derive (largeEvenLabelAll_centerPrime_clA (p := 3) hlabΛ ⟨hgen, Or.inl hA⟩)
  · exact derive (largeEvenLabelAll_centerPrime_clC (p := 3) hlabΛ ⟨hgen, Or.inl hB⟩)
  · exact derive (largeEvenLabelAll_centerPrime_clC (p := 3) hlabΛ ⟨hgen, Or.inr hC⟩)

theorem exists_mul_of_qTwoCl
    {B Bs K : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hlab : GGInnerDiagOnLabel (fun _ lab => GGQTwoClLabel lab) 3 Bs K)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K)) :
    ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c := by
  obtain ⟨hperf, lab, hlabΛ, hraw⟩ := hlab
  obtain ⟨R₀, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hQtwo, -⟩ := hQ₀
  have hn : lab.n = 1 := by
    have h1 := hlabΛ.1
    have h2 := hQtwo.1
    omega
  have hall : LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
    refine largeEvenLabelAll_subset_inn hlabΛ ?_
    rcases hQtwo.2 with hA | hB | hC
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
      exact ⟨hA, by simp [hn]⟩
    · exact Or.inl (Or.inl hB)
    · exact Or.inl (Or.inr (Or.inl hC))
  obtain ⟨R, _, I, F, hQ, hguard⟩ := largeEvenRawDatum_exists (hall _ hraw)
  obtain ⟨hsR, hnaR, θ, -, hBsN, hind⟩ := hQ
  have hI : I ⊆ LargeEvenInnSet R := hguard hsR hnaR
  have hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹ :=
    F4AutRefl.exists_conj_of_inn hperf θ hI hBsN hind
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3
  exact ggBstar_split_of_inner_coprime Nat.prime_three hBs hcop hBsN hinner

theorem GGConfig.three_pow_three_le_card_subgroupOf {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    3 ^ 3 ≤ Nat.card (Bs.subgroupOf K) := by
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBsE : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hB4 : 3 ^ 4 ≤ Nat.card B := by
    have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
    have hBmax : LargeEvenIsBmax 3 B := hS.1
    unfold LargeEvenIsBmax at hBmax
    obtain ⟨-, hBcard, -⟩ := hBmax
    have h4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hcfg.1.2.2.2.2.2.1.2.2.2
    calc 3 ^ 4 ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) h4
      _ = Nat.card B := hBcard.symm
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G) with hCdef
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b := by
    intro b hb c hc
    exact congrArg Subtype.val (hBsE.1.is_comm.comm ⟨b, hBBs hb⟩ ⟨c, hc.1⟩)
  have hprod := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
    (C := B) (D := C) hcomm
  have hsup_le : B ⊔ C ≤ Bs := sup_le hBBs inf_le_left
  have hstep : Nat.card B * Nat.card C ≤ Nat.card Bs * Nat.card (B ⊓ C : Subgroup G) := by
    rw [← hprod]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hsup_le)
  have hBC : B ⊓ C = Subgroup.zpowers y := by
    rw [hCdef, ← inf_assoc, inf_eq_left.mpr hBBs]
    exact inf_centralizer_eq_zpowers_of_sHat hnb.1
  have hy : orderOf y = 3 :=
    orderOf_eq_prime (hnb.1.1.1.2 y hnb.1.2.1) hnb.1.2.2.1
  have hcardBC : Nat.card (B ⊓ C : Subgroup G) = 3 := by
    rw [hBC, Nat.card_zpowers, hy]
  have hsurj : Nat.card Bs ≤ Nat.card (Bs ⊓ K : Subgroup G) * Nat.card C := by
    let f : ↥(Bs ⊓ K) × ↥C → ↥Bs :=
      fun q => ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
    have hf : Function.Surjective f := by
      rintro ⟨b, hb⟩
      obtain ⟨a, ha, c, hc, rfl⟩ := hsplit b hb
      exact ⟨(⟨a, ha⟩, ⟨c, hc⟩), Subtype.ext rfl⟩
    have h := Nat.card_le_card_of_surjective f hf
    simpa [Nat.card_prod] using h
  have h1 : Nat.card B * Nat.card C ≤ (3 * Nat.card (Bs ⊓ K : Subgroup G)) * Nat.card C := by
    calc Nat.card B * Nat.card C ≤ Nat.card Bs * Nat.card (B ⊓ C : Subgroup G) := hstep
      _ = Nat.card Bs * 3 := by rw [hcardBC]
      _ ≤ (Nat.card (Bs ⊓ K : Subgroup G) * Nat.card C) * 3 := Nat.mul_le_mul_right 3 hsurj
      _ = (3 * Nat.card (Bs ⊓ K : Subgroup G)) * Nat.card C := by ring
  have hmain : Nat.card B ≤ 3 * Nat.card (Bs ⊓ K : Subgroup G) :=
    Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hfinal : 3 ^ 3 ≤ Nat.card (Bs ⊓ K : Subgroup G) := by
    have h : 3 ^ 4 ≤ 3 * Nat.card (Bs ⊓ K : Subgroup G) := hB4.trans hmain
    have h34 : 3 ^ 4 = 3 * 3 ^ 3 := by norm_num
    rw [h34] at h
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hcard : Nat.card (Bs.subgroupOf K) = Nat.card (Bs ⊓ K : Subgroup G) := by
    have h := Subgroup.card_subtype K (Bs.subgroupOf K)
    rw [Subgroup.subgroupOf_map_subtype] at h
    exact h.symm
  rwa [hcard]

omit [Finite G] in
theorem mem_subgroupOf_of_mem_centralizer_subgroupOf {p : ℕ} {Bs K : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    ∀ g ∈ Subgroup.centralizer ((Bs.subgroupOf K : Subgroup ↥K) : Set ↥K), g ^ p = 1 →
      g ∈ Bs.subgroupOf K := by
  intro gK hg hgp
  have hcent : (gK : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := hsplit b hb
    have haK : (⟨a, ha.2⟩ : ↥K) ∈ Bs.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      exact ha.1
    have hga : a * (gK : G) = (gK : G) * a := by
      have h := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg _ haK)
      simpa using h
    have hgc : c * (gK : G) = (gK : G) * c :=
      (Subgroup.mem_centralizer_iff.mp hc.2 (gK : G) gK.2).symm
    calc a * c * (gK : G)
        = a * (c * (gK : G)) := by group
      _ = a * ((gK : G) * c) := by rw [hgc]
      _ = (a * (gK : G)) * c := by group
      _ = ((gK : G) * a) * c := by rw [hga]
      _ = (gK : G) * (a * c) := by group
  have hgp' : (gK : G) ^ p = 1 := by
    simpa using congrArg Subtype.val hgp
  exact Subgroup.mem_subgroupOf.mpr (hSC (gK : G) hcent hgp')

end CFSG.StandardType

end
