module

public import CFSG.Quasithin.SteinbergCCSylowCoreResidual
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open CFSG.LocalAnalysis.GorensteinLyons (mem_conjugate_iff_conj_mem)
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem perfect_two_extension_conjugate_escape {H M Y : Subgroup G} (hYH : Y ≤ H)
    (hYn : (Y.subgroupOf H).Normal) (hY : Group.IsPerfect Y)
    (hHY : IsPGroup 2 (H ⧸ Y.subgroupOf H)) (hsimple : IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y))
    (hnab : ∃ a b : Y ⧸ CFSG.pCore 2 Y, a * b ≠ b * a) {A : Subgroup G} (hAH : A ≤ H)
    (_hA : IsPGroup 2 A) (hAQ : ¬ A ≤ (CFSG.pCore 2 H).map H.subtype) :
    Y ≤ ⨆ y ∈ Y, CFSG.conjugate A y ∧
      (¬ Y ≤ M → ∃ y ∈ Y, ¬ CFSG.conjugate A y ≤ M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  set K := ⨆ y ∈ Y, CFSG.conjugate A y with hKdef
  have hconjK : ∀ y ∈ Y, CFSG.conjugate A y ≤ K := fun y hy =>
    le_iSup₂ (f := fun y (_ : y ∈ Y) => CFSG.conjugate A y) y hy
  have hAK : A ≤ K := by
    have h1 : CFSG.conjugate A 1 = A := by
      ext z
      rw [mem_conjugate_iff_conj_mem, one_mul, inv_one, mul_one]
    exact h1 ▸ hconjK 1 (one_mem Y)
  have hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y₀ hy₀ k hk
    have hle : K.map (MulAut.conj y₀).toMonoidHom ≤ K := by
      rw [hKdef, Subgroup.map_iSup]
      refine iSup_le fun y => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hy => ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, mem_conjugate_iff_conj_mem] at hz
      refine hconjK (y * y₀⁻¹) (mul_mem hy (inv_mem hy₀)) ?_
      rw [mem_conjugate_iff_conj_mem]
      change y * y₀⁻¹ * (y₀ * z * y₀⁻¹) * (y * y₀⁻¹)⁻¹ ∈ A
      rw [show y * y₀⁻¹ * (y₀ * z * y₀⁻¹) * (y * y₀⁻¹)⁻¹ = y * z * y⁻¹ by group]
      exact hz
    exact hle ⟨k, hk, rfl⟩
  have hcommK : ∀ y ∈ Y, ∀ a ∈ A, ⁅y, a⁆ ∈ K ⊓ Y := by
    intro y hy a ha
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      refine mul_mem (hconjK y⁻¹ (inv_mem hy) ?_) (inv_mem (hAK ha))
      rw [mem_conjugate_iff_conj_mem, show y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a by group]
      exact ha
    · rw [commutatorElement_def, mul_assoc y a, mul_assoc y]
      exact mul_mem hy ((mem_normalizer_iff.mp (hHN (hAH ha)) _).mp (inv_mem hy))
  let π := QuotientGroup.mk' (CFSG.pCore 2 Y)
  have hLn : ((K ⊓ Y).subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      (le_normalizer_of_conj_mem fun y hy z hz => mem_inf.mpr
        ⟨hYK y hy z (mem_inf.mp hz).1, mul_mem (mul_mem hy (mem_inf.mp hz).2) (inv_mem hy)⟩)
  have hπn : (((K ⊓ Y).subgroupOf Y).map π).Normal :=
    Subgroup.Normal.map hLn _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (((K ⊓ Y).subgroupOf Y).map π) with hbot | htop
  ·
    exfalso
    apply hAQ
    have hLO : (K ⊓ Y).subgroupOf Y ≤ CFSG.pCore 2 Y := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
      exact hbot
    have hZ : center (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (center (Y ⧸ CFSG.pCore 2 Y)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (mem_center_iff.mp (h ▸ mem_top b) a)
    let ψ : H →* MulAut (Y ⧸ CFSG.pCore 2 Y) :=
      (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 Y)).comp
        (Y.normalizerMonoidHom.comp (inclusion hHN))
    have hmemD : ∀ h : H, h ∈ ψ.ker ↔
        ∀ y : Y, y⁻¹ * Y.normalizerMonoidHom ⟨h, hHN h.2⟩ y ∈ CFSG.pCore 2 Y := fun h =>
      CFSG.SectionRank.Ccomm.mem_ker_autQuotient (CFSG.pCore 2 Y)
    have hD2 : IsPGroup 2 ψ.ker := by
      intro d
      obtain ⟨k, hk⟩ := hHY ((d : H) : H ⧸ Y.subgroupOf H)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      have hy₀ : ((((d : H) ^ (2 ^ k) : H) : G)) ∈ Y := mem_subgroupOf.mp hk
      have hdk : ((d : H) ^ (2 ^ k) : H) ∈ ψ.ker := pow_mem d.2 _
      have hcen : π ⟨_, hy₀⟩ ∈ center (Y ⧸ CFSG.pCore 2 Y) := by
        rw [mem_center_iff]
        intro v
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ v
        have h1 := (hmemD _).mp hdk y
        have h2 : π (Y.normalizerMonoidHom ⟨_, hHN ((d : H) ^ (2 ^ k)).2⟩ y) = π y :=
          (QuotientGroup.eq.mpr h1).symm
        have h3 : Y.normalizerMonoidHom ⟨_, hHN ((d : H) ^ (2 ^ k)).2⟩ y =
            ⟨_, hy₀⟩ * y * ⟨_, hy₀⟩⁻¹ := rfl
        rw [h3, map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h2
        exact h2.symm
      rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
      obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup ⟨_, hcen⟩
      refine ⟨k + j, Subtype.ext (Subtype.ext ?_)⟩
      have h1 := congrArg (fun z : CFSG.pCore 2 Y => ((z : Y) : G)) hj
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
      exact h1
    have hDO : ψ.ker ≤ CFSG.pCore 2 H := le_pCore_of_normal_of_isPGroup inferInstance hD2
    intro a ha
    refine ⟨⟨a, hAH ha⟩, hDO ((hmemD _).mpr fun y => ?_), rfl⟩
    apply hLO
    rw [mem_subgroupOf]
    have e : (((y⁻¹ * Y.normalizerMonoidHom ⟨a, hHN (hAH ha)⟩ y : Y)) : G) = ⁅(y : G)⁻¹, a⁆ := by
      change (y : G)⁻¹ * (a * y * a⁻¹) = ⁅(y : G)⁻¹, a⁆
      rw [commutatorElement_def, inv_inv]
      group
    rw [e]
    exact hcommK _ (inv_mem y.2) a ha
  ·
    have h2 : IsPGroup 2 (Y ⧸ (K ⊓ Y).subgroupOf Y) := by
      refine CFSG.pCore_isPGroup.of_surjective
        ((QuotientGroup.mk' ((K ⊓ Y).subgroupOf Y)).comp (CFSG.pCore 2 Y).subtype) ?_
      intro v
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ v
      have hy : π y ∈ ((K ⊓ Y).subgroupOf Y).map π := htop ▸ mem_top _
      obtain ⟨l, hl, hly⟩ := hy
      refine ⟨⟨l⁻¹ * y, QuotientGroup.eq.mp hly⟩, ?_⟩
      change ((l⁻¹ * y : Y) : Y ⧸ (K ⊓ Y).subgroupOf Y) = (y : Y ⧸ (K ⊓ Y).subgroupOf Y)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l⁻¹).mpr (inv_mem hl), one_mul]
    have : Group.IsPerfect Y := hY
    have hperf : Group.IsPerfect (Y ⧸ (K ⊓ Y).subgroupOf Y) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have htop' := eq_bot_of_isPerfect_of_isPGroup (K := ⊤)
      (Group.IsPerfect.top_iff.mpr hperf) (h2.to_subgroup ⊤)
    have hYK : Y ≤ K := by
      intro y hy
      have h1 : ((⟨y, hy⟩ : Y) : Y ⧸ (K ⊓ Y).subgroupOf Y) ∈ (⊤ : Subgroup _) := mem_top _
      rw [htop', mem_bot, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact (mem_inf.mp h1).1
    refine ⟨hYK, fun hYM => ?_⟩
    by_contra hcon
    apply hYM
    refine hYK.trans (iSup₂_le fun y hy => ?_)
    by_contra h
    exact hcon ⟨y, hy, h⟩

end CFSG.Quasithin.SteinbergCC
