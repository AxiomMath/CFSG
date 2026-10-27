module

public import CFSG.Quasithin.AppendixH.H16.SextetAction
public import CFSG.Quasithin.MS93.S6Bridge

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc
  CFSG.Quasithin.MS93

@[expose] noncomputable def sxN : Subgroup S24 := sxAct.ker.map sxGen.subtype

theorem mem_sxN_iff (g : S24) : g ∈ sxN ↔ ∃ h : g ∈ sxGen, sxAct ⟨g, h⟩ = 1 := by
  rw [sxN, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hgy⟩
    have hgy' : g = (y : S24) := by simpa using hgy.symm
    subst hgy'
    exact ⟨y.2, (MonoidHom.mem_ker).1 hy⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨g, h⟩, (MonoidHom.mem_ker).2 hh, rfl⟩

theorem sxN_le_sxGen : sxN ≤ sxGen := by
  intro g hg
  rw [sxN, Subgroup.mem_map] at hg
  obtain ⟨y, -, hgy⟩ := hg
  rw [← hgy]
  exact y.2

theorem sxKS_le_sxGen : sxKS ≤ sxGen := sxKS_le_P0.trans sxP0_le_gen

theorem sxKS_le_sxN : sxKS ≤ sxN := by
  intro k hk
  rw [mem_sxN_iff]
  exact ⟨sxKS_le_sxGen hk, sxAct_of_mem_sxKS ⟨k, sxKS_le_sxGen hk⟩ hk⟩

theorem sxN_conj_mem : ∀ g ∈ sxGen, ∀ n ∈ sxN, g * n * g⁻¹ ∈ sxN := by
  intro g hg n hn
  obtain ⟨hnGen, hnKer⟩ := (mem_sxN_iff n).1 hn
  rw [mem_sxN_iff]
  refine ⟨sxGen.mul_mem (sxGen.mul_mem hg hnGen) (sxGen.inv_mem hg), ?_⟩
  have h1 : (⟨g * n * g⁻¹, sxGen.mul_mem (sxGen.mul_mem hg hnGen) (sxGen.inv_mem hg)⟩ : ↥sxGen)
      = ⟨g, hg⟩ * ⟨n, hnGen⟩ * ⟨g, hg⟩⁻¹ := by
    apply Subtype.ext
    rfl
  rw [h1, map_mul, map_mul, map_inv, hnKer, mul_one, mul_inv_cancel]

theorem sxN_subgroupOf : sxN.subgroupOf sxGen = sxAct.ker := by
  show (sxAct.ker.map sxGen.subtype).comap sxGen.subtype = sxAct.ker
  exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective sxGen) sxAct.ker

theorem card_sxN :
    Nat.card ↥sxN = 192 := by
  have hmap : Nat.card ↥sxN = Nat.card ↥sxAct.ker := by
    rw [sxN]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective sxGen)
  have hq : Nat.card (↥sxGen ⧸ sxAct.ker) = 720 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective sxAct sxAct_surjective).toEquiv,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (sxAct.ker : Subgroup ↥sxGen)
  rw [card_sxGen, hq] at hc
  omega

theorem sxN_pow_three_mem :
    ∀ n ∈ sxN, n ^ 3 ∈ sxKS := by
  intro n hn
  have hnormal : (sxKS.subgroupOf sxN).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer sxKS_le_sxN).2
      (sxN_le_sxGen.trans sxGen_le_normalizer_KS)
  haveI := hnormal
  have hcardSub : Nat.card ↥(sxKS.subgroupOf sxN) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sxKS_le_sxN).toEquiv, card_sxKS]
  have hq : Nat.card (↥sxN ⧸ sxKS.subgroupOf sxN) = 3 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (sxKS.subgroupOf sxN)
    rw [card_sxN, hcardSub] at hc
    have hc' : Nat.card (↥sxN ⧸ sxKS.subgroupOf sxN) * 64 = 3 * 64 := by
      rw [← hc]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hc'
  have hpow : (QuotientGroup.mk (⟨n, hn⟩ : ↥sxN) : ↥sxN ⧸ sxKS.subgroupOf sxN) ^ 3 = 1 := by
    rw [← hq]
    exact pow_card_eq_one'
  have h2 : (QuotientGroup.mk ((⟨n, hn⟩ : ↥sxN) ^ 3) :
      ↥sxN ⧸ sxKS.subgroupOf sxN) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact hpow
  have hmem := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
  simpa [Subgroup.coe_pow] using hmem

@[expose] noncomputable def sxPi : ↥sxGen →* ↥(StatedSp 2 (ZMod 2)) :=
  S6B.thetaTwo.toMonoidHom.comp sxAct

theorem sxPi_surjective :
    Function.Surjective sxPi := by
  change Function.Surjective (S6B.thetaTwo.toMonoidHom ∘ sxAct)
  exact Function.Surjective.comp S6B.thetaTwo.surjective sxAct_surjective

theorem sxPi_ker : sxPi.ker = sxN.subgroupOf sxGen := by
  change (S6B.thetaTwo.toMonoidHom.comp sxAct).ker = sxN.subgroupOf sxGen
  rw [sxN_subgroupOf]
  exact MonoidHom.ker_comp_of_injective sxAct S6B.thetaTwo.toMonoidHom S6B.thetaTwo.injective

theorem fixes_US_iff_mem_sxN (g : ↥AutPerm) (hg : (g : S24) ∈ sxGen) :
    (∀ x ∈ US, (rhoC11 AutPerm le_rfl g) x = x) ↔ (g : S24) ∈ sxN := by
  rw [mem_sxN_iff]
  constructor
  · intro hfix
    refine ⟨hg, ?_⟩
    rw [sxAct_eq_one_iff]
    intro u hu
    have hrho : sxRho ⟨(g : S24), hg⟩ = rhoC11 AutPerm le_rfl g := by
      rw [sxRho_apply]
      exact congrArg (fun x => rhoC11 AutPerm le_rfl x) (Subtype.ext rfl)
    rw [hrho]
    exact hfix u hu
  · rintro ⟨h, hker⟩ x hx
    have hrho : sxRho ⟨(g : S24), h⟩ = rhoC11 AutPerm le_rfl g := by
      rw [sxRho_apply]
      exact congrArg (fun x => rhoC11 AutPerm le_rfl x) (Subtype.ext rfl)
    rw [← hrho]
    exact (sxAct_eq_one_iff ⟨(g : S24), h⟩).1 hker x hx

end CFSG.ASVolI.H16
