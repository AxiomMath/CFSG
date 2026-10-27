module

public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.GH74.Uniqueness.SU.KI4Struct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]


theorem exists_inv_mod_centralizer_of_psl2_quotient
    {B K T : Subgroup X}
    (hBK : B ≤ K ⊔ Subgroup.centralizer (K : Set X))
    (hBab : IsMulCommutative B) (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hTp : IsPGroup 2 T)
    (hperm : (B : Set X) * (T : Set X) = (T : Set X) * (B : Set X))
    (hSK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K)
    {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) :
    ∃ t ∈ T ⊓ K, ∀ b ∈ B, t * b * t⁻¹ * b ∈ Subgroup.centralizer (K : Set X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup X := Subgroup.centralizer (K : Set X)
  let H : Subgroup X := K ⊔ C
  have hBH : B ≤ H := hBK
  have hKH : K ≤ H := le_sup_left
  have hKleC : K ≤ Subgroup.centralizer (C : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc k hk).symm
  have hKnormC : K ≤ Subgroup.normalizer (C : Set X) :=
    hKleC.trans (Subgroup.centralizer_le_normalizer (C : Set X))
  have hHcoe : (H : Set X) = (K : Set X) * (C : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K C hKnormC
  have hHsup : (K.subgroupOf H) ⊔
      Subgroup.centralizer ((K.subgroupOf H : Subgroup H) : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro y hy
    have hyH : (y : X) ∈ (H : Set X) := y.2
    rw [hHcoe] at hyH
    obtain ⟨k, hk, c, hc, hkc⟩ := hyH
    have hkH : (⟨k, Subgroup.mem_sup_left hk⟩ : H) ∈ K.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr hk
    have hcH : (⟨c, Subgroup.mem_sup_right hc⟩ : H) ∈
        Subgroup.centralizer ((K.subgroupOf H : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hc (x : X) (Subgroup.mem_subgroupOf.mp hx)
    have hy_eq : y = (⟨k, Subgroup.mem_sup_left hk⟩ : H) *
        (⟨c, Subgroup.mem_sup_right hc⟩ : H) := Subtype.ext hkc.symm
    rw [hy_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkH) (Subgroup.mem_sup_right hcH)
  obtain ⟨f, hf, hfk⟩ :=
    CFSG.GH74.Uniqueness.SU.K.R4.exists_proj_of_sup_centralizer_eq_top (K.subgroupOf H) hHsup
  let e_sub : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  let e_quot : ↥(K.subgroupOf H) ⧸ Subgroup.center ↥(K.subgroupOf H) ≃*
      ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr (Subgroup.center ↥(K.subgroupOf H)) (Subgroup.center ↥K) e_sub
      (Subgroup.map_center_eq e_sub)
  let projK : H →* ↥K ⧸ Subgroup.center ↥K := e_quot.toMonoidHom.comp f
  have hprojK_k : ∀ k : ↥K, projK ⟨k, hKH k.2⟩ = QuotientGroup.mk k := by
    intro k
    let kH : ↥(K.subgroupOf H) := ⟨⟨k, hKH k.2⟩, k.2⟩
    have h1 : projK ⟨k, hKH k.2⟩ = e_quot (f kH) := rfl
    rw [h1, hf kH, QuotientGroup.congr_mk]
    rfl
  have hmemC : ∀ y : H,
      y ∈ Subgroup.centralizer ((K.subgroupOf H : Subgroup H) : Set H) ↔
      (y : X) ∈ Subgroup.centralizer (K : Set X) := by
    intro y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h k hk
      have hkH : (⟨k, Subgroup.mem_sup_left hk⟩ : H) ∈ K.subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr hk
      exact congrArg Subtype.val (h ⟨k, Subgroup.mem_sup_left hk⟩ hkH)
    · intro h k hk
      apply Subtype.ext
      exact h (k : X) (Subgroup.mem_subgroupOf.mp hk)
  let proj : H →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e) :=
    eK.toMonoidHom.comp projK
  have hproj_k : ∀ k : ↥K,
      proj ⟨k, hKH k.2⟩ = eK (QuotientGroup.mk k) := by
    intro k
    show eK (projK ⟨k, hKH k.2⟩) = eK (QuotientGroup.mk k)
    rw [hprojK_k k]
  have hproj_ker : ∀ y : H, proj y = 1 ↔ (y : X) ∈ C := by
    intro y
    show eK (projK y) = 1 ↔ _
    rw [eK.map_eq_one_iff]
    rw [show projK y = 1 ↔ f y = 1 from e_quot.map_eq_one_iff]
    rw [hfk y, hmemC y]
  let ψ : ↥K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e) :=
    proj.comp (Subgroup.inclusion hKH)
  have hψ_apply : ∀ k : ↥K, ψ k = proj ⟨k, hKH k.2⟩ := fun k => rfl
  have hψ_surj : Function.Surjective ψ := by
    intro x
    obtain ⟨q, rfl⟩ := eK.surjective x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) q
    refine ⟨k, ?_⟩
    rw [hψ_apply, hproj_k, QuotientGroup.mk'_apply]
  let SK : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) :=
    ((T ⊓ K).subgroupOf H).map proj
  have hSKmap : ((T ⊓ K).subgroupOf K).map ψ = SK := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨(t : ↥K), hKH t.2⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_subgroupOf.mp ht).1, (Subgroup.mem_subgroupOf.mp ht).2⟩
      · rfl
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyT, hyK⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)
      refine Subgroup.mem_map.mpr ⟨⟨y, hyK⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_inf.mpr ⟨hyT, hyK⟩
      · apply congrArg proj
        exact Subtype.ext rfl
  have hSK_sylow : CFSG.QuasithinUnique.IsSylowTwoOf SK ⊤ := by
    have hSK2 : CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ K).subgroupOf K) ⊤ := by
      obtain ⟨Q, hQ⟩ := hSK.exists_sylow_eq_subgroupOf
      rw [← hQ]
      refine ⟨le_top, Q.isPGroup', ?_⟩
      rw [show ((Q : Subgroup ↥K).subgroupOf ⊤).index = (Q : Subgroup ↥K).index from
        Subgroup.relIndex_top_right (Q : Subgroup ↥K)]
      exact Q.not_dvd_index
    have h := CFSG.Quasithin.A312.isSylowTwoOf_top_map ψ hψ_surj hSK2
    rwa [hSKmap] at h
  let SH : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) :=
    ((T ⊓ H).subgroupOf H).map proj
  have hSH_p : IsPGroup 2 SH :=
    ((hTp.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map proj
  have hSK_le_SH : SK ≤ SH := by
    apply Subgroup.map_mono
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp hx).1, hKH (Subgroup.mem_inf.mp hx).2⟩
  have hSH_eq : SH = SK := by
    have hodd : ¬ 2 ∣ SK.index := by
      have h := hSK_sylow.2.2
      rwa [show (SK.subgroupOf ⊤).index = SK.index from Subgroup.relIndex_top_right SK] at h
    exact (CFSG.Quasithin.H23P4.eq_of_isPGroup_two_of_le hSK_le_SH hSH_p hodd).symm
  let Bbar : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) :=
    (B.subgroupOf H).map proj
  have hBabH : IsMulCommutative ↥(B.subgroupOf H) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (Subgroup.subgroupOfEquivOfLe hBH).injective
    rw [map_mul, map_mul]
    exact hBab.is_comm.comm _ _
  have hBbar_ab : IsMulCommutative Bbar :=
    Subgroup.map_isMulCommutative (B.subgroupOf H) proj
  have hcardBbar_dvd_B : Nat.card Bbar ∣ Nat.card B := by
    have h1 : Nat.card Bbar ∣ Nat.card ↥(B.subgroupOf H) := Subgroup.card_map_dvd (H := B.subgroupOf H) proj
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv] at h1
  have hBbar_odd : Odd (Nat.card Bbar) := Odd.of_dvd_nat hBo hcardBbar_dvd_B
  have hperm_H : (B : Set X) * ((T ⊓ H : Subgroup X) : Set X) =
      ((T ⊓ H : Subgroup X) : Set X) * (B : Set X) :=
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hperm.symm hBH).symm
  have hperm_Hsub : ((B.subgroupOf H : Subgroup H) : Set H) *
      (((T ⊓ H).subgroupOf H : Subgroup H) : Set H) =
      (((T ⊓ H).subgroupOf H : Subgroup H) : Set H) * ((B.subgroupOf H : Subgroup H) : Set H) :=
    CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBH inf_le_right hperm_H
  have hperm_SH : (Bbar : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) *
      (SH : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) =
      (SH : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) *
      (Bbar : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) :=
    CFSG.GroupTheory.map_permutes_map proj hperm_Hsub
  have hperm_SK : (Bbar : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) *
      (SK : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) =
      (SK : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) *
      (Bbar : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e))) := by
    simpa [hSH_eq] using hperm_SH
  by_cases hbot : Bbar = ⊥
  · refine ⟨1, Subgroup.one_mem _, fun b hb => ?_⟩
    have hbBar : proj ⟨b, hBH hb⟩ ∈ Bbar :=
      Subgroup.mem_map_of_mem proj (Subgroup.mem_subgroupOf.mpr hb)
    rw [hbot] at hbBar
    have hbC : b ∈ C := (hproj_ker ⟨b, hBH hb⟩).mp (Subgroup.mem_bot.mp hbBar)
    have hcalc : (1 : X) * b * (1 : X)⁻¹ * b = b * b := by group
    rw [hcalc]
    exact C.mul_mem hbC hbC
  · have hBbar_not3 : ¬ IsPGroup 3 ↥Bbar := by
      intro h3
      rcases h3.card_eq_or_dvd with h1 | h3dvd
      · exact hbot (Subgroup.card_eq_one.mp h1)
      · exact hB3 (h3dvd.trans hcardBbar_dvd_B)
    have hcfg : CFSG.ASVolI.burnsideA315x_Config
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) SK Bbar :=
      ⟨hSK_sylow, hBbar_odd, hBbar_not3, Or.inl hBbar_ab, hperm_SK⟩
    obtain ⟨-, -, s, hs, hinv⟩ := CFSG.ASVolI.burnsideA315x_l2_core hp2 he hcfg
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp hs
    have hyTK : (y : X) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hy
    refine ⟨(y : X), hyTK, fun b hb => ?_⟩
    let bH : H := ⟨b, hBH hb⟩
    let wH : H := y * bH * y⁻¹ * bH
    have hproj_w : proj wH = 1 := by
      have h1 : proj wH = proj y * proj bH * (proj y)⁻¹ * proj bH := by
        simp [wH]
      rw [h1, hys]
      have hbBar : proj bH ∈ Bbar :=
        Subgroup.mem_map_of_mem proj (Subgroup.mem_subgroupOf.mpr hb)
      have h2 := hinv (proj bH) hbBar
      rw [h2, inv_mul_cancel]
    have hwC : (wH : X) ∈ C := (hproj_ker wH).mp hproj_w
    have hwX : (wH : X) = (y : X) * b * (y : X)⁻¹ * b := rfl
    rwa [hwX] at hwC

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
