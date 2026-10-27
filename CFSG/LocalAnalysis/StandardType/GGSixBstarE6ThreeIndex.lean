module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section Index

open TableBExc.E6Three

variable {K : Type} [Field K] [Finite K]

theorem hatAut_range_eq_sup :
    (hatAut .E6 K).range =
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
        (rootDiagAutHom .E6 K).range := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨⟨x, g, hg, a, rfl⟩, rfl⟩
    have e : hatAut .E6 K ⟨g * rootDiagUnit .E6 a, ⟨g, hg, a, rfl⟩⟩ =
        MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K) * rootDiagAutHom .E6 K a := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [coe_hatAut_apply]
      change _ = (g : ModGL .E6 K) * (rootDiagUnit .E6 a * (h : ModGL .E6 K) *
        (rootDiagUnit .E6 a)⁻¹) * (g : ModGL .E6 K)⁻¹
      simp only [mul_assoc, mul_inv_rev]
    rw [e]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨a, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨⟨g, adjointGroup_le_hatGroup g.2⟩, MulEquiv.ext fun h => Subtype.ext rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact rootDiagAutHom_mem_hatAut_range a

theorem exists_sup_zpowers_of_not_mem_innerAut
    {s : MulAut (adjointGroup .E6 K)} (hs : s ∈ (hatAut .E6 K).range)
    (hsn : s ∉ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range) :
    (hatAut .E6 K).range ≤
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
        Subgroup.zpowers s := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  set N := CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .E6 K) with hN
  haveI : N.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set π := QuotientGroup.mk' N with hπ
  have h3 : Nat.card Φ.ker ∣ 3 := by
    have h := hdvd
    rwa [show Tag.E6.cartan.det.natAbs = 3 by rw [det_cartan_E6]; rfl] at h
  have hmem : ∀ γ ∈ (hatAut .E6 K).range, π γ ∈ Φ.ker := by
    intro γ hγ
    have hγ' : γ ∈ ((N ⊔ (rootDiagAutHom .E6 K).range : Subgroup _) : Set _) := by
      have h := hγ
      rw [hatAut_range_eq_sup] at h
      exact h
    rw [Subgroup.normal_mul] at hγ'
    obtain ⟨i, hi, r, ⟨a, rfl⟩, rfl⟩ := hγ'
    rw [hker]
    refine ⟨a, ?_⟩
    change π (rootDiagAutHom .E6 K a) = π (i * rootDiagAutHom .E6 K a)
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    rw [map_mul, hpi, one_mul]
  have hs1 : (⟨π s, hmem s hs⟩ : Φ.ker) ≠ 1 := by
    intro h
    apply hsn
    have h1 : π s = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff s).1 h1
  have hcard : Nat.card Φ.ker = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
    · exfalso
      exact hs1 (Subsingleton.elim (h := Nat.card_eq_one_iff_unique.1 h1 |>.1) _ _)
    · exact h1
  intro γ hγ
  have hy := mem_zpowers_of_prime_card hcard hs1 (g' := (⟨π γ, hmem γ hγ⟩ : Φ.ker))
  obtain ⟨k, hk⟩ := hy
  have hπk : π γ = π (s ^ k) := by
    have := congrArg Subtype.val hk
    simpa [map_zpow] using this.symm
  have hγk : γ * (s ^ k)⁻¹ ∈ N := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    change π (γ * (s ^ k)⁻¹) = 1
    rw [map_mul, map_inv, hπk, mul_inv_cancel]
  have e : γ = (γ * (s ^ k)⁻¹) * s ^ k := by group
  rw [e]
  exact Subgroup.mul_mem_sup hγk (Subgroup.zpow_mem_zpowers s k)

end Index

end NoOffE6Three

end CFSG.StandardType
