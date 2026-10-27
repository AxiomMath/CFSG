module

public import CFSG.Sporadic.Fi22.LocalType
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartOne.KP.Fi22Unitary
import CFSG.RankThree.PartOne.KP.UnitaryTorus
import CFSG.RankThree.GroupTheory.SteinbergCECentralOddKernelLift
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Sporadic.Fi22
open CFSG.Assembly.RankThreeEven (localRank)

theorem four_le_localRank_three_of_fi22_cover
    {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (ψ : K →* J) (hψ : Function.Surjective ψ) (hZ : ψ.ker ≤ center K)
    (hodd : Odd (Nat.card ψ.ker)) : 4 ≤ localRank 3 G := by
  classical
  obtain ⟨t, hta, hto, htu⟩ :=
    CFSG.RankThree.GroupTheory.exists_unique_involution_lift hψ hZ hodd orderOf_a
  set P : Subgroup K := centralizer ({t} : Set K) with hP
  have hPt : ∀ x : P, (x : K) * t = t * x := fun x => mem_centralizer_singleton_iff.1 x.2
  have hPC : ∀ x : P, ψ x ∈ Ca := by
    intro x
    rw [mem_Ca, ← hta, ← map_mul, ← map_mul, hPt x]
  set φ₀ : P →* Ca := (ψ.comp P.subtype).codRestrict Ca hPC with hφ₀
  have hφ₀s : Function.Surjective φ₀ := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hψ c
    have hkt : k * t * k⁻¹ = t := by
      refine htu _ ?_ ?_
      · rw [map_mul, map_mul, map_inv, hk, hta, mem_Ca.1 hc, mul_inv_cancel_right]
        exact mem_zpowers a
      · have h := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective t
        rw [← hto, ← h]
        rfl
    refine ⟨⟨k, mem_centralizer_singleton_iff.2 ?_⟩, Subtype.ext hk⟩
    calc k * t = k * t * k⁻¹ * k := by group
      _ = t * k := by rw [hkt]
  set φ := CFSG.RankThree.PartOne.statedProjEquivT46.symm.toMonoidHom.comp
    (caQuotEquiv.toMonoidHom.comp ((QuotientGroup.mk' (center Ca)).comp φ₀)) with hφ
  have hφs : Function.Surjective φ :=
    CFSG.RankThree.PartOne.statedProjEquivT46.symm.surjective.comp
      (caQuotEquiv.surjective.comp ((QuotientGroup.mk'_surjective _).comp hφ₀s))
  have hker : φ.ker ≤ center P := by
    intro x hx
    have h0 : (QuotientGroup.mk (φ₀ x) : Ca ⧸ center Ca) = 1 := by
      have h := MonoidHom.mem_ker.1 hx
      simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply] at h
      rwa [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h
    have h1 : φ₀ x ∈ zpowers aCa := by
      rw [← center_Ca_eq]
      exact (QuotientGroup.eq_one_iff (φ₀ x)).1 h0
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
    have h3 : ψ x = a ^ j := by
      have h := congrArg Subtype.val hj
      rw [Subgroup.coe_zpow, aCa_val] at h
      exact h.symm
    have h2 : (t ^ j)⁻¹ * (x : K) ∈ center K := by
      apply hZ
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hta, h3, inv_mul_cancel]
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : K) * x = x * y
    have hyt : Commute (y : K) (t ^ j) := Commute.zpow_right (hPt y) j
    calc (y : K) * x = (y : K) * (t ^ j * ((t ^ j)⁻¹ * x)) := by group
      _ = t ^ j * ((y : K) * ((t ^ j)⁻¹ * x)) := by rw [← mul_assoc, hyt.eq, mul_assoc]
      _ = t ^ j * (((t ^ j)⁻¹ * x) * y) := by rw [mem_center_iff.1 h2 (y : K)]
      _ = x * y := by group
  obtain ⟨U, hU, hUc⟩ := CFSG.RankThree.PartOne.stated_psu6_central_cover φ hφs hker
  have hUel := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 U).mp hU
  set W : Subgroup G := (U.map P.subtype).map K.subtype with hW
  have hWel : CFSG.Open.IsElemAbelian 3 W :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hUel P.subtype) K.subtype
  have hWc : Nat.card W = 3 ^ 4 := by
    rw [hW, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective P.subtype_injective, hUc]
  have ht1 : (t : G) ≠ 1 := by
    intro h
    have h' : t = 1 := Subtype.ext h
    rw [h', orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hT : zpowers (t : G) ≠ ⊥ := by
    rwa [Ne, zpowers_eq_bot]
  have hT2 : IsPGroup 2 (zpowers (t : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hto, pow_one])
  have hWT : W ≤ normalizer ((zpowers (t : G) : Subgroup G) : Set G) := by
    intro w hw
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 ?_)
    obtain ⟨_, ⟨u, -, rfl⟩, rfl⟩ := hw
    rintro _ ⟨n, rfl⟩
    have hu : Commute (t : G) ((u : K) : G) := (congrArg Subtype.val (hPt u)).symm
    exact (Commute.zpow_left hu n).eq
  have := hWel.1
  exact CFSG.RankThree.Theta.le_localRank_of_le_normalizer (by norm_num) hT hT2 hWel.1 hWel.2 hWc
    hWT

end CFSG.LocalAnalysis.UniquenessCase.UCK
