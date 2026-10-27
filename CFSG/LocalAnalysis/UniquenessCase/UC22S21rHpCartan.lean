module

import CFSG.GroupTheory.SolvableFactorizedHall
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rhp_eq_mul_of_isHallSubgroup {Y C T A B : Subgroup G}
    (hY : Group.IsSolvable ↥Y) (hCY : C ≤ Y) (hYCT : (Y : Set G) = (C : Set G) * (T : Set G))
    {π : Set Nat.Primes} (hC : IsHallSubgroup π (C.subgroupOf Y)) (hTA : T ≤ A) (hTB : T ≤ B)
    (hYAB : (Y : Set G) = ((A ⊓ Y : Subgroup G) : Set G) * ((B ⊓ Y : Subgroup G) : Set G)) :
    (C : Set G) = ((C ⊓ A : Subgroup G) : Set G) * ((C ⊓ B : Subgroup G) : Set G) := by
  classical
  have hAB : ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) * ((B.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)
      = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hy : (y : G) ∈ ((A ⊓ Y : Subgroup G) : Set G) * ((B ⊓ Y : Subgroup G) : Set G) := by
      rw [← hYAB]
      exact y.2
    obtain ⟨a, ha, b, hb, hab⟩ := hy
    exact ⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.2 ha.1, ⟨b, hb.2⟩, Subgroup.mem_subgroupOf.2 hb.1,
      Subtype.ext hab⟩
  obtain ⟨K, hK, hKfac⟩ := CFSG.exists_isHallSubgroup_factorized hY hAB π
  obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hY hK hC
  have hgCT : (g : G) ∈ (C : Set G) * (T : Set G) := by
    rw [← hYCT]
    exact g.2
  obtain ⟨c, hc, t, ht, hct⟩ := hgCT
  have hconj : ∀ k ∈ K, (t : G) * (k : G) * t⁻¹ ∈ C := by
    intro k hk
    have h1 : (MulAut.conj g) k ∈ C.subgroupOf Y := by
      rw [hg]
      exact Subgroup.mem_map_of_mem _ hk
    rw [Subgroup.mem_subgroupOf, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hct] at h1
    have he : (t : G) * k * t⁻¹ = c⁻¹ * (c * t * k * (c * t)⁻¹) * c := by group
    rw [he]
    exact C.mul_mem (C.mul_mem (C.inv_mem hc) h1) hc
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · have hcx : c * x * c⁻¹ ∈ Y := hCY (C.mul_mem (C.mul_mem hc hx) (C.inv_mem hc))
    have h2 : (⟨c * x * c⁻¹, hcx⟩ : ↥Y) ∈ C.subgroupOf Y :=
      Subgroup.mem_subgroupOf.2 (C.mul_mem (C.mul_mem hc hx) (C.inv_mem hc))
    rw [hg] at h2
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 h2
    have hkx' : (c * t * k * (c * t)⁻¹ : G) = c * x * c⁻¹ := by
      have := congrArg Subtype.val hkx
      simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hct] using this
    have hxk : x = (t : G) * k * t⁻¹ := by
      have he : x = c⁻¹ * (c * x * c⁻¹) * c := by group
      rw [he, ← hkx']
      group
    have hk' : k ∈ (K : Set ↥Y) := hk
    rw [hKfac] at hk'
    obtain ⟨a, ha, b, hb, hab⟩ := hk'
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.1 ha.2
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb.2
    refine ⟨t * a * t⁻¹, ⟨hconj a ha.1, A.mul_mem (A.mul_mem (hTA ht) haA) (A.inv_mem (hTA ht))⟩,
      t * b * t⁻¹, ⟨hconj b hb.1, B.mul_mem (B.mul_mem (hTB ht) hbB) (B.inv_mem (hTB ht))⟩, ?_⟩
    rw [hxk, ← hab, Subgroup.coe_mul]
    group
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact C.mul_mem ha.1 hb.1

theorem uc22s21rhp_isHallSubgroup_odd {Y C T : Subgroup G} (hCY : C ≤ Y) (hTY : T ≤ Y)
    (hYCT : (Y : Set G) = (C : Set G) * (T : Set G)) (hodd : Odd (Nat.card C))
    (hT : IsPGroup 2 T) :
    IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} (C.subgroupOf Y) := by
  have hCc : Nat.card (C.subgroupOf Y) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe hCY).toEquiv
  have hTc : Nat.card (T.subgroupOf Y) = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTY).toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT
  have hcop : (Nat.card (C.subgroupOf Y)).Coprime (Nat.card (T.subgroupOf Y)) := by
    rw [hCc, hTc, hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hodd)
  have hcomp : IsComplement' (C.subgroupOf Y) (T.subgroupOf Y) := by
    refine isComplement'_of_disjoint_and_mul_eq_univ (disjoint_of_coprime_natCard hcop) ?_
    refine Set.eq_univ_of_forall fun y => ?_
    have hy : (y : G) ∈ (C : Set G) * (T : Set G) := by
      rw [← hYCT]
      exact y.2
    obtain ⟨c, hc, t, ht, hct⟩ := hy
    exact ⟨⟨c, hCY hc⟩, Subgroup.mem_subgroupOf.2 hc, ⟨t, hTY ht⟩, Subgroup.mem_subgroupOf.2 ht,
      Subtype.ext hct⟩
  have hidx : (C.subgroupOf Y).index = 2 ^ n := by
    rw [hcomp.symm.index_eq_card, hTc, hn]
  refine isHallSubgroup_of _ _ (fun p hp => ?_) (fun p hp hdvd => ?_)
  · rw [hCc] at hp
    intro h2
    rw [h2] at hp
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hp)
  · rw [hidx] at hdvd
    exact hp ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 (p.2.dvd_of_dvd_pow hdvd))

theorem uc22s21rhp_cartan_eq_mul (D : Data G) {H₁ H₂ : Subgroup G}
    (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {Y C : Subgroup G} (hYM : Y ≤ D.M) (hTY : D.T ≤ Y) (hYs : Group.IsSolvable ↥Y)
    (hCY : C ≤ Y) (hYCT : (Y : Set G) = (C : Set G) * (D.T : Set G)) (hodd : Odd (Nat.card C)) :
    (C : Set G) = ((C ⊓ H₁ : Subgroup G) : Set G) * ((C ⊓ H₂ : Subgroup G) : Set G) :=
  uc22s21rhp_eq_mul_of_isHallSubgroup hYs hCY hYCT
    (uc22s21rhp_isHallSubgroup_odd hCY hTY hYCT hodd D.sylowM.isPGroup) hH₁.1 hH₂.1
    (hfX Y hYM hTY (Or.inr hYs))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
