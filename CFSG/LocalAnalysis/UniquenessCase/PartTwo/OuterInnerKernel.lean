module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySix
public import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G]

theorem mem_T0_of_rhoL_mem_inner {D : Data G} {X : Subgroup G} (hX : X ∈ calC D.M)
    (hMX : D.M ≤ normalizer (X : Set G)) {u : G} (hu : u ∈ D.T)
    (hin : rhoL X ⟨u, hMX (D.sylowM.le hu)⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X)) :
    u ∈ (D.T ⊓ X) ⊔ (D.T ⊓ F08.CentOverO2 D.M X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  let S : Subgroup (Bar2 X) := ((D.T ⊓ X).subgroupOf X).map π
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.isSylowTwoOf_sylowBar2 hX
  have hin' : rhoL X ⟨u, hMX (D.sylowM.le hu)⟩ ∈
      (MulAut.conj : Bar2 X →* MulAut (Bar2 X)).range := hin
  obtain ⟨x, hxconj⟩ := hin'
  have hTnorm : D.T ≤ normalizer (X : Set G) := fun t ht => hMX (D.sylowM.le ht)
  have hupow : ∃ k, orderOf (rhoL X ⟨u, hMX (D.sylowM.le hu)⟩) = 2 ^ k := by
    have hdvd : orderOf (rhoL X ⟨u, hMX (D.sylowM.le hu)⟩) ∣
        orderOf (⟨u, hu⟩ : ↥D.T) := by
      have h := orderOf_map_dvd ((rhoL X).comp (Subgroup.inclusion hTnorm)) ⟨u, hu⟩
      have h' : orderOf (rhoL X ((Subgroup.inclusion hTnorm) ⟨u, hu⟩)) ∣
          orderOf (⟨u, hu⟩ : ↥D.T) := by
        simpa only [MonoidHom.comp_apply] using h
      have harg : (Subgroup.inclusion hTnorm ⟨u, hu⟩ : ↥(normalizer (X : Set G))) =
          ⟨u, hMX (D.sylowM.le hu)⟩ := Subtype.ext rfl
      rw [harg] at h'
      exact h'
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_orderOf_eq_pow (p := 2) ⟨u, hu⟩
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hconjpow : ∃ k, orderOf (MulAut.conj x) = 2 ^ k := by
    obtain ⟨k, hk⟩ := hupow
    exact ⟨k, by rw [hxconj]; exact hk⟩
  let y : Bar2 X := TauCeti.pPart 2 x
  let z : Bar2 X := TauCeti.pFreePart 2 x
  have hyz : y * z = x := TauCeti.pPart_mul_pFreePart 2 x
  have hypow : ∃ k, orderOf y = 2 ^ k :=
    ⟨(orderOf x).factorization 2,
      TauCeti.orderOf_pPart Nat.prime_two (orderOf_pos x).ne'⟩
  have hzodd : ¬ 2 ∣ orderOf z :=
    TauCeti.not_dvd_orderOf_pFreePart Nat.prime_two (orderOf_pos x).ne'
  have hzzpow : z ∈ Subgroup.zpowers x := TauCeti.pFreePart_mem_zpowers 2 x
  have hzconj : MulAut.conj z = 1 := by
    have hdvdz : orderOf (MulAut.conj z) ∣ orderOf z :=
      orderOf_map_dvd (MulAut.conj : Bar2 X →* MulAut (Bar2 X)) z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzzpow
    have hmem : MulAut.conj z ∈ Subgroup.zpowers (MulAut.conj x) := by
      have hz' : z = x ^ n := hn.symm
      rw [hz']
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [map_zpow]⟩
    have hdvd2 : orderOf (MulAut.conj z) ∣ orderOf (MulAut.conj x) :=
      orderOf_dvd_of_mem_zpowers hmem
    obtain ⟨k, hk⟩ := hconjpow
    have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hzodd)
    have hgcd : orderOf (MulAut.conj z) ∣ Nat.gcd (2 ^ k) (orderOf z) := by
      rw [← hk]
      exact Nat.dvd_gcd hdvd2 hdvdz
    have h1 : orderOf (MulAut.conj z) = 1 := by
      rw [hcop.gcd_eq_one] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact orderOf_eq_one_iff.mp h1
  have hyconj : MulAut.conj y = MulAut.conj x := by
    calc MulAut.conj y = MulAut.conj y * 1 := (mul_one _).symm
      _ = MulAut.conj y * MulAut.conj z := by rw [hzconj]
      _ = MulAut.conj (y * z) := (map_mul MulAut.conj y z).symm
      _ = MulAut.conj x := by rw [hyz]
  have hnorm (t : G) (ht : t ∈ D.T) :
      S.map (rhoL X ⟨t, hTnorm ht⟩).toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro w ⟨s, hsS, rfl⟩
      obtain ⟨y₀, hy₀, hπy₀⟩ := Subgroup.mem_map.mp hsS
      have hy₀' : (y₀ : G) ∈ D.T ⊓ X := Subgroup.mem_subgroupOf.mp hy₀
      have hmem : t * (y₀ : G) * t⁻¹ ∈ D.T ⊓ X := by
        refine ⟨D.T.mul_mem (D.T.mul_mem ht hy₀'.1) (D.T.inv_mem ht), ?_⟩
        exact (Subgroup.mem_normalizer_iff.mp (hMX (D.sylowM.le ht)) (y₀ : G)).mp hy₀'.2
      have hcoe : ((Subgroup.normalizerMonoidHom X ⟨t, hTnorm ht⟩ y₀ : ↥X) : G) =
          t * (y₀ : G) * t⁻¹ := rhoL_mk_coe X ⟨t, hTnorm ht⟩ y₀
      have heq : (Subgroup.normalizerMonoidHom X ⟨t, hTnorm ht⟩ y₀ : ↥X) =
          ⟨t * (y₀ : G) * t⁻¹, hmem.2⟩ := Subtype.ext hcoe
      rw [← hπy₀]
      show rhoL X ⟨t, hTnorm ht⟩ (π y₀) ∈ S
      rw [show rhoL X ⟨t, hTnorm ht⟩ (π y₀) =
          QuotientGroup.mk (Subgroup.normalizerMonoidHom X ⟨t, hTnorm ht⟩ y₀) from
        rhoL_mk X ⟨t, hTnorm ht⟩ y₀]
      rw [heq]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hmem)
    · rw [Subgroup.card_map_of_injective
        (f := (rhoL X ⟨t, hTnorm ht⟩).toMonoidHom)
        (rhoL X ⟨t, hTnorm ht⟩).injective]
  have hxN : x ∈ Subgroup.normalizer (S : Set (Bar2 X)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hxconj]
    exact hnorm u hu
  have hyN : y ∈ Subgroup.normalizer (S : Set (Bar2 X)) :=
    Subgroup.zpowers_le.mpr hxN (TauCeti.pPart_mem_zpowers 2 x)
  have hyS : y ∈ S := by
    let K : Subgroup (Bar2 X) := Subgroup.normalizer (S : Set (Bar2 X))
    have hSK : S ≤ K := Subgroup.le_normalizer
    have hSylK : CFSG.QuasithinUnique.IsSylowTwoOf S K := by
      refine ⟨hSK, hS.isPGroup, ?_⟩
      intro h2
      have hrel : S.relIndex K * K.relIndex ⊤ = S.relIndex ⊤ :=
        Subgroup.relIndex_mul_relIndex S K ⊤ hSK le_top
      have htop : ¬ 2 ∣ S.relIndex ⊤ := by
        simpa [Subgroup.relIndex] using hS.2.2
      exact htop (hrel ▸ dvd_mul_of_dvd_left h2 _)
    have hyord : IsPGroup 2 (Subgroup.zpowers y) := by
      obtain ⟨k, hk⟩ := hypow
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, hk]
    have hleN : Subgroup.zpowers y ≤ K := Subgroup.zpowers_le.mpr hyN
    have hQ : IsPGroup 2 (S ⊔ Subgroup.zpowers y : Subgroup (Bar2 X)) :=
      IsPGroup.to_sup_of_normal_left' hS.isPGroup hyord hleN
    have hQK : (S ⊔ Subgroup.zpowers y : Subgroup (Bar2 X)) ≤ K := sup_le hSK hleN
    have hQeq : (S ⊔ Subgroup.zpowers y : Subgroup (Bar2 X)) = S :=
      CFSG.QuasithinUnique.IsSylowTwoOf.eq_of_le hSylK le_sup_left hQK hQ
    have hyQ : y ∈ (S ⊔ Subgroup.zpowers y : Subgroup (Bar2 X)) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rwa [hQeq] at hyQ
  obtain ⟨s, hs, hπs⟩ := Subgroup.mem_map.mp hyS
  have hsT : (s : G) ∈ D.T ⊓ X := Subgroup.mem_subgroupOf.mp hs
  have hrho_s : rhoL X ⟨(s : G), hTnorm hsT.1⟩ = MulAut.conj y := by
    rw [show (⟨(s : G), hTnorm hsT.1⟩ : ↥(normalizer (X : Set G))) =
        ⟨(s : G), Subgroup.le_normalizer hsT.2⟩ from Subtype.ext rfl]
    rw [rhoL_inner X (s : G) hsT.2]
    have hmk : (QuotientGroup.mk (⟨(s : G), hsT.2⟩ : ↥X) : Bar2 X) = y := by
      rw [show (⟨(s : G), hsT.2⟩ : ↥X) = s from Subtype.ext rfl]
      exact hπs
    rw [hmk]
  have hrho : rhoL X ⟨u, hMX (D.sylowM.le hu)⟩ =
      rhoL X ⟨(s : G), hTnorm hsT.1⟩ := by
    rw [← hxconj, ← hyconj]
    exact hrho_s.symm
  have huM : u ∈ D.M := D.sylowM.le hu
  have hsM : (s : G) ∈ D.M := D.sylowM.le hsT.1
  have hmemM : u * (s : G)⁻¹ ∈ D.M := D.M.mul_mem huM (D.M.inv_mem hsM)
  have hmemker : (⟨u * (s : G)⁻¹, hmemM⟩ : ↥D.M) ∈
      MonoidHom.ker ((rhoL X).comp (Subgroup.inclusion hMX)) := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change rhoL X ⟨u * (s : G)⁻¹, hMX hmemM⟩ = 1
    have hprod : (⟨u * (s : G)⁻¹, hMX hmemM⟩ : ↥(normalizer (X : Set G))) =
        (⟨u, hMX huM⟩ : ↥(normalizer (X : Set G))) *
          (⟨(s : G), hMX hsM⟩ : ↥(normalizer (X : Set G)))⁻¹ := by
      ext
      simp
    rw [hprod, map_mul, map_inv, hrho]
    group
  have hcent : u * (s : G)⁻¹ ∈ F08.CentOverO2 D.M X := by
    rw [centOverO2_eq_ker_map hMX]
    exact Subgroup.mem_map.mpr ⟨⟨u * (s : G)⁻¹, hmemM⟩, hmemker, rfl⟩
  have hmem1 : u * (s : G)⁻¹ ∈ D.T ⊓ F08.CentOverO2 D.M X :=
    ⟨D.T.mul_mem hu (D.T.inv_mem hsT.1), hcent⟩
  have hmem2 : (s : G) ∈ D.T ⊓ X := hsT
  have hueq : u = (u * (s : G)⁻¹) * (s : G) := by group
  rw [hueq, sup_comm]
  exact Subgroup.mul_mem_sup hmem1 hmem2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
