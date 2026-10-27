module

public import CFSG.LocalAnalysis.WeakClosure81.NineLemmaD
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X A : Subgroup G} {p : ℕ}

private theorem nineStep7_conjSubgroup_iSup {ι : Sort*} (A : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, A i) g = ⨆ i, conjSubgroup (A i) g := by
  unfold conjSubgroup
  rw [Subgroup.map_iSup]

private theorem nineStep7_le_normalClosure {K Y : Subgroup G} :
    Y ≤ ⨆ k : K, conjSubgroup Y (k : G) := by
  have h1 : conjSubgroup Y ((1 : K) : G) ≤ ⨆ k : K, conjSubgroup Y (k : G) :=
    le_iSup (fun k : K => conjSubgroup Y (k : G)) 1
  simpa [conjSubgroup_one] using h1

private theorem nineStep7_normalClosure_le {K Y Z : Subgroup G}
    (h : ∀ k : K, conjSubgroup Y (k : G) ≤ Z) :
    (⨆ k : K, conjSubgroup Y (k : G)) ≤ Z :=
  iSup_le h

private theorem nineStep7_normalClosure_normal {K Y : Subgroup G} (hYK : Y ≤ K) :
    ((⨆ k : K, conjSubgroup Y (k : G)).subgroupOf K).Normal := by
  have hNK : (⨆ k : K, conjSubgroup Y (k : G)) ≤ K := by
    refine iSup_le fun k => ?_
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxK : x = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) := by group
    rw [hxK]
    exact K.mul_mem (K.mul_mem (K.inv_mem k.2) (hYK hx)) k.2
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNK]
  intro k₀ hk₀
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  apply le_antisymm
  · rw [nineStep7_conjSubgroup_iSup]
    refine iSup_le fun k => ?_
    rw [conjSubgroup_conjSubgroup]
    exact le_iSup (fun j : K => conjSubgroup Y (j : G)) ⟨(k : G) * k₀, K.mul_mem k.2 hk₀⟩
  · have hk₀inv : k₀⁻¹ ∈ K := K.inv_mem hk₀
    have h1 : conjSubgroup (⨆ k : K, conjSubgroup Y (k : G)) k₀⁻¹ ≤
        ⨆ k : K, conjSubgroup Y (k : G) := by
      rw [nineStep7_conjSubgroup_iSup]
      refine iSup_le fun k => ?_
      rw [conjSubgroup_conjSubgroup]
      exact le_iSup (fun j : K => conjSubgroup Y (j : G))
        ⟨(k : G) * k₀⁻¹, K.mul_mem k.2 hk₀inv⟩
    have h2 := E3.conjSubgroup_mono_left k₀ h1
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2

theorem commutator_twoResidual_wClos_ne_bot (hV : Hyp7 V) (h : TwoPTwo K S X p)
    (hA : IsGConj V A) (hAS : A ≤ S) (hAR : ¬ A ≤ pCoreOf 2 K)
    (hΓ : A ⊓ pCoreOf 2 K ∈ E3.gammaSet V 1 (pCoreOf 2 K)) (hne : A ⊓ pCoreOf 2 K ≠ ⊥) :
    ⁅twoResidual K, E3.wClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥ := by
  intro hbot
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx₀mem : (x₀ : G) ∈ A ⊓ pCoreOf 2 K := x₀.2
  have hx₀ne' : (x₀ : G) ≠ 1 := fun h1 => hx₀ne (Subtype.ext h1)
  have hx₀A : (x₀ : G) ∈ A := hx₀mem.1
  have hx₀W : (x₀ : G) ∈ E3.wClos V 1 (pCoreOf 2 K) := E3.le_wClos hΓ hx₀mem
  have hcent : twoResidual K ≤ Subgroup.centralizer ↑(E3.wClos V 1 (pCoreOf 2 K)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hcent1 : twoResidual K ≤ Subgroup.centralizer ({(x₀ : G)} : Set G) :=
    hcent.trans (Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hx₀W))
  obtain ⟨g, hg⟩ := hA
  have hx₀g : (x₀ : G) ∈ conjSubgroup V g := by rw [← hg]; exact hx₀A
  have hnormA : twoResidual K ≤ Subgroup.normalizer (A : Set G) := by
    rw [hg]
    exact hcent1.trans (centralizer_le_normalizer_conj hV.2.2 g hx₀g hx₀ne')
  have hconj_le_S : ∀ k ∈ K, conjSubgroup A k ≤ S := by
    intro k hk
    have hsup : S ⊔ twoResidual K = K :=
      sup_twoResidual_eq (show IsSylowTwoOf S K from h.sylowTwo)
    have hSnorm : S ≤ Subgroup.normalizer (twoResidual K : Set G) :=
      h.sylowTwo.le.trans (le_normalizer_twoResidual K)
    have hk'' : k ∈ (↑(twoResidual K ⊔ S) : Set G) := by
      rw [sup_comm, hsup]; exact hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (twoResidual K) S hSnorm] at hk''
    rw [Set.mem_mul] at hk''
    obtain ⟨o, ho, s, hs, hk_eq⟩ := hk''
    rw [← hk_eq]
    have hoN : o ∈ Subgroup.normalizer (A : Set G) := hnormA ho
    have hconj_eq : conjSubgroup A (o * s) = conjSubgroup A s := by
      rw [← conjSubgroup_conjSubgroup A o s, (conjSubgroup_eq_iff_mem_normalizer).mpr hoN]
    rw [hconj_eq]
    calc conjSubgroup A s ≤ conjSubgroup S s := E3.conjSubgroup_mono_left s hAS
      _ = S := (conjSubgroup_eq_iff_mem_normalizer).mpr (Subgroup.le_normalizer hs)
  set N : Subgroup G := ⨆ k : K, conjSubgroup A (k : G) with hNdef
  have hA_le_N : A ≤ N := by
    rw [hNdef]
    exact nineStep7_le_normalClosure
  have hN_le_S : N ≤ S := by
    rw [hNdef]
    exact nineStep7_normalClosure_le (fun k => hconj_le_S (k : G) k.2)
  have hN_le_K : N ≤ K := hN_le_S.trans h.sylowTwo.le
  have hN2 : IsPGroup 2 N := h.sylowTwo.isPGroup.to_le hN_le_S
  have hNnormal : (N.subgroupOf K).Normal := by
    rw [hNdef]
    exact nineStep7_normalClosure_normal (hAS.trans h.sylowTwo.le)
  have hNnorm : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_K).mp hNnormal
  have hNleR : N ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN_le_K hNnorm hN2
  exact hAR (hA_le_N.trans hNleR)

theorem cClos_le_pCoreOf (h : TwoPTwoIrred K S X p)
    (h7 : ⁅twoResidual K, E3.wClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥) :
    E3.cClos V 1 S ≤ pCoreOf 2 K := by
  by_contra hCnot
  set Y : Subgroup G := E3.cClos V 1 S with hYdef
  have hYnotR : ¬ Y ≤ pCoreOf 2 K := by rw [hYdef]; exact hCnot
  have hYS : Y ≤ S := by rw [hYdef]; exact inf_le_left
  have hYK : Y ≤ K := hYS.trans h.sylowTwo.le
  have hY2 : IsPGroup 2 Y := h.sylowTwo.isPGroup.to_le hYS
  have hYnotF : ¬ Y ≤ nineFrattiniR K X :=
    TwoPTwo.not_le_frattiniR_of_isPGroup h.toTwoPTwo hYK hY2 hYnotR
  set N : Subgroup G := ⨆ k : K, conjSubgroup Y (k : G) with hNdef
  have hY_le_N : Y ≤ N := by
    rw [hNdef]
    exact nineStep7_le_normalClosure
  have hN_le_K : N ≤ K := by
    rw [hNdef]
    refine nineStep7_normalClosure_le fun k => ?_
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxK : x = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) := by group
    rw [hxK]
    exact K.mul_mem (K.mul_mem (K.inv_mem k.2) (hYK hx)) k.2
  have hNnormal : (N.subgroupOf K).Normal := by
    rw [hNdef]
    exact nineStep7_normalClosure_normal hYK
  have hNnotF : ¬ N ≤ nineFrattiniR K X := fun hNle => hYnotF (hY_le_N.trans hNle)
  have hres : twoResidual K ≤ N :=
    TwoPTwoIrred.twoResidual_le_of_not_le_frattiniR h hN_le_K hNnormal hNnotF
  have hNcent : N ≤ Subgroup.centralizer ↑(E3.wClos V 1 (pCoreOf 2 K)) := by
    rw [hNdef]
    refine nineStep7_normalClosure_le fun k => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hx' : (k : G) * x * (k : G)⁻¹ ∈ Y := by
      rw [← mem_conjSubgroup_iff]; exact hx
    have hx'c : (k : G) * x * (k : G)⁻¹ ∈
        Subgroup.centralizer ↑(E3.wClos V 1 S) := by
      rw [hYdef] at hx'; exact hx'.2
    have hwS : w ∈ E3.wClos V 1 S :=
      E3.wClos_mono (TwoPTwo.pCoreOf_le_sylowTwo h.toTwoPTwo) hw
    have hkw : (k : G) * w * (k : G)⁻¹ ∈ E3.wClos V 1 (pCoreOf 2 K) := by
      have hkR : (k : G) ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K k.2
      have hkW : (k : G) ∈ Subgroup.normalizer (E3.wClos V 1 (pCoreOf 2 K) : Set G) :=
        E3.normalizer_le_normalizer_wClos (pCoreOf 2 K) hkR
      exact (Subgroup.mem_normalizer_iff.mp hkW w).mp hw
    have hkwS : (k : G) * w * (k : G)⁻¹ ∈ E3.wClos V 1 S :=
      E3.wClos_mono (TwoPTwo.pCoreOf_le_sylowTwo h.toTwoPTwo) hkw
    have hcomm := Subgroup.mem_centralizer_iff.mp hx'c ((k : G) * w * (k : G)⁻¹) hkwS
    have heq : (k : G) * (w * x) * (k : G)⁻¹ = (k : G) * (x * w) * (k : G)⁻¹ := by
      calc (k : G) * (w * x) * (k : G)⁻¹
          = ((k : G) * w * (k : G)⁻¹) * ((k : G) * x * (k : G)⁻¹) := by group
        _ = ((k : G) * x * (k : G)⁻¹) * ((k : G) * w * (k : G)⁻¹) := hcomm
        _ = (k : G) * (x * w) * (k : G)⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel heq)
  have hcomm_bot : ⁅twoResidual K, E3.wClos V 1 (pCoreOf 2 K)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hres.trans hNcent)
  exact h7 hcomm_bot

theorem cClos_le_cClos_pCoreOf (h : TwoPTwoIrred K S X p)
    (h7 : ⁅twoResidual K, E3.wClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥) :
    E3.cClos V 1 S ≤ E3.cClos V 1 (pCoreOf 2 K) := by
  rw [E3.cClos]
  refine le_inf (cClos_le_pCoreOf h h7) ?_
  exact inf_le_right.trans
    (Subgroup.centralizer_le fun x hx =>
      E3.wClos_mono (TwoPTwo.pCoreOf_le_sylowTwo h.toTwoPTwo) hx)

theorem commutator_twoResidual_cClos_ne_bot (h : TwoPTwoIrred K S X p)
    (h7 : ⁅twoResidual K, E3.wClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥)
    (hC : ⁅twoResidual K, E3.cClos V 1 S⁆ ≠ ⊥) :
    ⁅twoResidual K, E3.cClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥ := by
  intro hbot
  apply hC
  have hle := Subgroup.commutator_mono (le_refl (twoResidual K)) (cClos_le_cClos_pCoreOf h h7)
  rw [hbot] at hle
  exact le_antisymm hle bot_le

end CFSG.LocalAnalysis.WeakClosure81
