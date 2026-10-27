module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveSwap
public import CFSG.LocalAnalysis.WeakClosure81.FiveFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma conj_mem_of_normal_subgroupOf {X N : Subgroup G} (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) {g n : G} (hg : g ∈ X) (hn : n ∈ N) :
    g * n * g⁻¹ ∈ N := by
  have h := hN.conj_mem ⟨n, hNX hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem five_five_nonabelian {H M A X : Subgroup G} (h : Sec5Hyp H M A) (hM : maxOver H A = {M})
    (hK : kerMOf M H = ⊥) (hX : IsMinNormalOver H ⊥ X)
    (hnab : ¬ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : IsSimpleGroup ↥X := by
  have hXH : X ≤ H := hX.2.1
  have hXn : (X.subgroupOf H).Normal := hX.2.2.1
  have hmin := hX.2.2.2
  have hHXA : H = X ⊔ A := five_four_one hM (by rw [hK]; exact hX)
  obtain ⟨S, hSX, hSn, hSsimple, hSnab⟩ := exists_simple_normal_of_isMinNormalOver hX hnab
  haveI := hSsimple
  have hSbot : S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot S).1 (inferInstance : Nontrivial ↥S)
  have hAnorm : A ≤ Subgroup.normalizer (S : Set G) := by
    intro a ha
    by_contra hna
    have hSM : S ≤ M :=
      le_M_of_not_mem_normalizer h hM hK hXH hXn hSX hSn hSsimple hSnab ha hna
    have hSker : S ≤ kerMOf M H := by
      intro x hx
      rw [mem_kerMOf_iff]
      refine ⟨hXH (hSX hx), ?_⟩
      intro g hg
      obtain ⟨b, hb, y, hy, rfl⟩ := exists_mul_of_eq_sup_of_normal hXH h.le_group hXn hHXA hg
      have hyS : y * x * y⁻¹ ∈ S := conj_mem_of_normal_subgroupOf hSX hSn hy hx
      have heq : b * y * x * (b * y)⁻¹ = b * (y * x * y⁻¹) * b⁻¹ := by group
      rw [heq]
      exact M.mul_mem (M.mul_mem (h.le_M hb) (hSM hyS)) (M.inv_mem (h.le_M hb))
    have hSbot' : S = ⊥ := by
      have hle : S ≤ (⊥ : Subgroup G) := by rw [← hK]; exact hSker
      exact le_bot_iff.mp hle
    exact hSbot hSbot'
  have hSnH : (S.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hSX.trans hXH)]
    intro g hg
    obtain ⟨b, hb, y, hy, rfl⟩ := exists_mul_of_eq_sup_of_normal hXH h.le_group hXn hHXA hg
    have hyNorm : y ∈ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).1 hSn hy
    exact (Subgroup.normalizer (S : Set G)).mul_mem (hAnorm hb) hyNorm
  have hSXeq : S = X := by
    rcases hmin S bot_le hSX hSnH with hS | hS
    · exact absurd hS hSbot
    · exact hS
  rwa [← hSXeq]

theorem inf_centralizer_eq_bot_of_isSimpleGroup {H A X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAH : A ≤ H) (hXH : X ≤ H) (hX : (X.subgroupOf H).Normal) (hH : H = X ⊔ A)
    (hO2 : pCoreOf 2 H = ⊥) (hsimple : IsSimpleGroup ↥X)
    (hnab : ¬ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : H ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  haveI := hsimple
  set C : Subgroup G := H ⊓ Subgroup.centralizer (X : Set G) with hCdef
  have hCn : (C.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hCdef] at hn ⊢
    obtain ⟨hnH, hnC⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hgH : (g : G) ∈ H := g.2
      exact H.mul_mem (H.mul_mem hgH hnH) (H.inv_mem hgH)
    · rw [Subgroup.mem_centralizer_iff] at hnC ⊢
      intro x hx
      have hconj : (g : G)⁻¹ * x * (g : G) ∈ X := by
        simpa using conj_mem_of_normal_subgroupOf hXH hX (H.inv_mem g.2) hx
      have hcomm := hnC ((g : G)⁻¹ * x * (g : G)) hconj
      have hcoe : (↑(g * n * g⁻¹) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe]
      calc x * ((g : G) * (n : G) * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * x * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((n : G) * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ := by rw [hcomm]
        _ = ((g : G) * (n : G) * (g : G)⁻¹) * x := by group
  have hCXbot : C ⊓ X = ⊥ := by
    have hZn : ((C ⊓ X).subgroupOf X).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.mem_inf] at hn ⊢
      obtain ⟨hnC, hnX⟩ := hn
      have hgX : (g : G) ∈ X := g.2
      have hncent : (n : G) ∈ Subgroup.centralizer (X : Set G) := by
        rw [hCdef] at hnC
        exact hnC.2
      have hcomm : (g : G) * (n : G) = (n : G) * (g : G) :=
        (Subgroup.mem_centralizer_iff.1 hncent) (g : G) hgX
      have hval : (↑(g * n * g⁻¹) : G) = (n : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcomm]
        group
      exact ⟨by rw [hval]; exact hnC, by rw [hval]; exact hnX⟩
    haveI : ((C ⊓ X).subgroupOf X).Normal := hZn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C ⊓ X).subgroupOf X) with hZ | hZ
    · refine le_bot_iff.mp fun z hz => ?_
      have hzZ : (⟨z, hz.2⟩ : ↥X) ∈ (C ⊓ X).subgroupOf X := Subgroup.mem_subgroupOf.2 hz
      rw [hZ, Subgroup.mem_bot] at hzZ
      simpa using congrArg Subtype.val hzZ
    · rw [Subgroup.subgroupOf_eq_top] at hZ
      exfalso
      apply hnab
      intro x hx y hy
      have hxC : x ∈ C := (hZ hx).1
      have hxcent : x ∈ Subgroup.centralizer (X : Set G) := by
        rw [hCdef] at hxC
        exact hxC.2
      exact ((Subgroup.mem_centralizer_iff.1 hxcent) y hy).symm
  have hC2 : ∀ c ∈ C, c * c = 1 := by
    intro c hc
    have hcinf : c ∈ H ⊓ Subgroup.centralizer (X : Set G) := hc
    obtain ⟨hcH, _⟩ := Subgroup.mem_inf.1 hcinf
    obtain ⟨b, hb, y, hy, hcy⟩ := exists_mul_of_eq_sup_of_normal hXH hAH hX hH hcH
    have hbb : b * b = 1 := by
      have hb2 := hA.2 b hb
      rwa [pow_two] at hb2
    have hbinv : b⁻¹ = b := (eq_inv_of_mul_eq_one_right hbb).symm
    have hbybX : b * y * b⁻¹ ∈ X := conj_mem_of_normal_subgroupOf hXH hX (hAH hb) hy
    have hccX : c * c ∈ X := by
      have heq : c * c = b * y * b⁻¹ * y := by
        rw [hcy, hbinv]
        group
      rw [heq]
      exact X.mul_mem hbybX hy
    have hccC : c * c ∈ C := C.mul_mem hc hc
    have hccbot : c * c ∈ (⊥ : Subgroup G) := by
      rw [← hCXbot]
      exact ⟨hccC, hccX⟩
    exact Subgroup.mem_bot.1 hccbot
  have hCp : IsPGroup 2 ↥C := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg2 : g ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hC2 (g : G) g.2
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf g) hdvd with h1 | h2
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h2, pow_one]⟩
  have hCle : C ≤ pCoreOf 2 H := le_pCoreOf_of_isPGroup_of_normal inf_le_left hCn hCp
  rw [hO2] at hCle
  exact le_bot_iff.mp hCle

end CFSG.LocalAnalysis.WeakClosure81
