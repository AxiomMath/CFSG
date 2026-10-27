module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardTorus
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFNontrivial
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFElementary
public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsBase
public import CFSG.LocalAnalysis.SteinbergSFFullCenterRootNormalizersOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.SteinbergSFCentralInvolutionFusion

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section SixKAux

variable {G : Type} [Group G]

theorem sixK_conj_mem_of_normal {X T : Subgroup G} (hle : X ≤ T)
    (hn : (X.subgroupOf T).Normal) {g : G} (hg : g ∈ T) {x : G} (hx : x ∈ X) :
    g * x * g⁻¹ ∈ X :=
  ((Subgroup.normal_subgroupOf_iff hle).mp hn) x g hx hg

theorem sixK_mem_normalizer_of_normal {X T : Subgroup G} (hle : X ≤ T)
    (hn : (X.subgroupOf T).Normal) {g : G} (hg : g ∈ T) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact sixK_conj_mem_of_normal hle hn hg hx
  · intro hx
    have h := sixK_conj_mem_of_normal hle hn (T.inv_mem hg) hx
    simpa [mul_assoc] using h

theorem sixK_comm_of_conj_eq {t m : G} (h : t * m * t⁻¹ = m) : t * m = m * t := by
  calc t * m = (t * m * t⁻¹) * t := by group
    _ = m * t := by rw [h]

theorem sixK_factor_unique {N K : Subgroup G} (hI : N ⊓ K = ⊥) {m₁ m₂ v₁ v₂ : G}
    (hm₁ : m₁ ∈ N) (hm₂ : m₂ ∈ N) (hv₁ : v₁ ∈ K) (hv₂ : v₂ ∈ K)
    (h : m₁ * v₁ = m₂ * v₂) : m₁ = m₂ ∧ v₁ = v₂ := by
  have e : m₂⁻¹ * m₁ = v₂ * v₁⁻¹ := by
    calc m₂⁻¹ * m₁ = m₂⁻¹ * (m₁ * v₁) * v₁⁻¹ := by group
      _ = m₂⁻¹ * (m₂ * v₂) * v₁⁻¹ := by rw [h]
      _ = v₂ * v₁⁻¹ := by group
  have hmem : m₂⁻¹ * m₁ ∈ N ⊓ K :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hm₂) hm₁, by rw [e]; exact mul_mem hv₂ (inv_mem hv₁)⟩
  rw [hI, Subgroup.mem_bot] at hmem
  have hm : m₁ = m₂ := (inv_mul_eq_one.mp hmem).symm
  subst hm
  exact ⟨rfl, mul_left_cancel h⟩

theorem sixK_mem_sup_factor {N K : Subgroup G} (hK : K ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ N ⊔ K) : ∃ n ∈ N, ∃ k ∈ K, n * k = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N K hK] at hx
  exact Set.mem_mul.mp hx

theorem sixK_mem_cent_iff {t x : G} : x ∈ centralizer ({t} : Set G) ↔ t * x = x * t := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h t (Set.mem_singleton t)
  · intro h y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact h

theorem sixK_conj_comm {t c x : G} (hc : c * t = t * c) (hx : t * x = x * t) :
    t * (c * x * c⁻¹) = c * x * c⁻¹ * t := by
  have hc' : t * c⁻¹ = c⁻¹ * t := by
    calc t * c⁻¹ = c⁻¹ * (c * t) * c⁻¹ := by group
      _ = c⁻¹ * (t * c) * c⁻¹ := by rw [hc]
      _ = c⁻¹ * t := by group
  calc t * (c * x * c⁻¹) = (t * c) * x * c⁻¹ := by group
    _ = (c * t) * x * c⁻¹ := by rw [hc]
    _ = c * (t * x) * c⁻¹ := by group
    _ = c * (x * t) * c⁻¹ := by rw [hx]
    _ = c * x * (t * c⁻¹) := by group
    _ = c * x * (c⁻¹ * t) := by rw [hc']
    _ = c * x * c⁻¹ * t := by group

theorem sixK_t_normalizes_conj {t : G} {V : Subgroup G} {c : G}
    (hV : t ∈ Subgroup.normalizer (V : Set G)) (hc : c * t = t * c) {x : G}
    (hx : x ∈ V.map (MulAut.conj c⁻¹).toMonoidHom) :
    t * x * t⁻¹ ∈ V.map (MulAut.conj c⁻¹).toMonoidHom := by
  rw [FullCenterWeyl.mem_map_conj_inv] at hx ⊢
  have e : c * (t * x * t⁻¹) * c⁻¹ = t * (c * x * c⁻¹) * t⁻¹ := by
    calc c * (t * x * t⁻¹) * c⁻¹ = (c * t) * x * (c * t)⁻¹ := by group
      _ = (t * c) * x * (t * c)⁻¹ := by rw [hc]
      _ = t * (c * x * c⁻¹) * t⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hV (c * x * c⁻¹)).mp hx

end SixKAux

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixK_rootA_sup_swap (k : Axis) :
    rootA K k ⊔ rootA K k.swap = antiUnipotent K := by
  cases k
  · show radA1 K ⊔ radA2 K = antiUnipotent K
    exact (antiUnipotent_eq_radA1_sup_radA2 (K := K)).symm
  · show radA2 K ⊔ radA1 K = antiUnipotent K
    rw [sup_comm]
    exact (antiUnipotent_eq_radA1_sup_radA2 (K := K)).symm

theorem sixK_P_eq_A_sup (k : Axis) : A φ k ⊔ A φ k.swap = P φ := by
  have key := sixK_rootA_sup_swap (K := K) k
  calc A φ k ⊔ A φ k.swap = GomiFusion.pull φ (rootA K k ⊔ rootA K k.swap) :=
        (GomiFusion.pull_sup φ _ _).symm
    _ = GomiFusion.pull φ (antiUnipotent K) := by rw [key]
    _ = P φ := rfl

theorem sixK_Mhat_le_S (k : Axis) : Mhat φ t i k ≤ S φ t i := by
  cases k
  · exact le_sup_left
  · exact le_sup_right

theorem sixK_k11
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) : K11Concl φ t i := by
  show S φ t i ⊓ centralizer ({t} : Set G) = P φ
  have hK : (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom ≤
      normalizer (Mhat φ t i i : Set G) :=
    hE.Vw_le_Ytilde.trans hE.Ytilde_le
  have hI : Mhat φ t i i ⊓ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom = ⊥ :=
    hE.inf_Vw
  have hsup : Mhat φ t i i ⊔ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom =
      S φ t i :=
    hE.sup_Vw
  have hMC : Mhat φ t i i ⊓ centralizer ({t} : Set G) = A φ i :=
    SixF.Mhat_inf_C hS.fc i hS.ne_bot hS.eq_bot
  have hMC' : Mhat φ t i i.swap ⊓ centralizer ({t} : Set G) = A φ i.swap :=
    SixF.Mhat_inf_C_swap hS.fc i hS.ne_bot hS.eq_bot
  have htV : t ∈ normalizer ((Vtor φ t i i : Subgroup G) : Set G) :=
    RootStandard.t_mem_normalizer_V hS.fc i hS.ne_bot hS.eq_bot i
  have hVC : Vtor φ t i i ⊓ centralizer ({t} : Set G) = U φ i :=
    RootStandard.V_inf_C hS.fc i hS.ne_bot hS.eq_bot
  have htT : t ∈ Tplus φ t i := by
    rw [← hH.sup_t]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨hleM, hnM, -⟩ := hH.normal_Mhat i
  obtain ⟨hwC, hwN, -⟩ := FullCenterWeyl.w_facts hS.fc i.swap
  have hwC' : w φ i.swap ∈ centralizer ({t} : Set G) := hwC
  have hwN' : w φ i.swap ∈ normalizer (A φ i.swap : Set G) := hwN
  have hwt : w φ i.swap * t = t * w φ i.swap := (sixK_mem_cent_iff.mp hwC').symm
  have hPA : A φ i ⊔ A φ i.swap = P φ := sixK_P_eq_A_sup i
  apply le_antisymm
  · intro s hs
    obtain ⟨hsS, hsC⟩ := Subgroup.mem_inf.mp hs
    have hsMV : s ∈ Mhat φ t i i ⊔
        (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom := by
      rw [hsup]
      exact hsS
    obtain ⟨m, hm, v, hv, hmv⟩ := sixK_mem_sup_factor hK hsMV
    have hcomm : t * s = s * t := sixK_mem_cent_iff.mp hsC
    have hprod : (t * m * t⁻¹) * (t * v * t⁻¹) = m * v := by
      calc (t * m * t⁻¹) * (t * v * t⁻¹) = t * (m * v) * t⁻¹ := by group
        _ = t * s * t⁻¹ := by rw [hmv]
        _ = s * t * t⁻¹ := by rw [hcomm]
        _ = s := by group
        _ = m * v := hmv.symm
    have hmt : t * m * t⁻¹ ∈ Mhat φ t i i := sixK_conj_mem_of_normal hleM hnM htT hm
    have hvt : t * v * t⁻¹ ∈ (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom :=
      sixK_t_normalizes_conj htV hwt hv
    obtain ⟨hmeq, hveq⟩ := sixK_factor_unique hI hmt hm hvt hv hprod
    have hmC : m ∈ centralizer ({t} : Set G) :=
      sixK_mem_cent_iff.mpr (sixK_comm_of_conj_eq hmeq)
    have hmA : m ∈ A φ i := by
      rw [← hMC]
      exact Subgroup.mem_inf.mpr ⟨hm, hmC⟩
    have hvC : t * v = v * t := sixK_comm_of_conj_eq hveq
    have hyV : w φ i.swap * v * (w φ i.swap)⁻¹ ∈ Vtor φ t i i :=
      FullCenterWeyl.mem_map_conj_inv.mp hv
    have hyC : w φ i.swap * v * (w φ i.swap)⁻¹ ∈ centralizer ({t} : Set G) :=
      sixK_mem_cent_iff.mpr (sixK_conj_comm hwt hvC)
    have hyU : w φ i.swap * v * (w φ i.swap)⁻¹ ∈ U φ i := by
      rw [← hVC]
      exact Subgroup.mem_inf.mpr ⟨hyV, hyC⟩
    have hUA : U φ i ≤ A φ i.swap :=
      GomiFusion.pull_mono φ ((FullCenter.rootU_le_center (K := K) i).trans
        (FullCenter.center_le_rootA (K := K) i.swap))
    have hvA : v ∈ A φ i.swap := (Subgroup.mem_normalizer_iff.mp hwN' v).mpr (hUA hyU)
    rw [← hPA, ← hmv]
    exact mul_mem (Subgroup.mem_sup_left hmA) (Subgroup.mem_sup_right hvA)
  · rw [← hPA]
    apply sup_le
    · rw [← hMC]
      intro x hx
      obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨sixK_Mhat_le_S i hxM, hxC⟩
    · rw [← hMC']
      intro x hx
      obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨sixK_Mhat_le_S i.swap hxM, hxC⟩

theorem sixK_k12 (hH : SixHConclusion φ t i) (k11 : K11Concl φ t i) :
    Tplus φ t i ⊓ centralizer ({t} : Set G) = P φ ⊔ zpowers t := by
  have k11' : S φ t i ⊓ centralizer ({t} : Set G) = P φ := k11
  have hST : S φ t i ≤ Tplus φ t i := by
    rw [← hH.sup_t]
    exact le_sup_left
  have htT : t ∈ Tplus φ t i := by
    rw [← hH.sup_t]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have ht_cent : t ∈ centralizer ({t} : Set G) := sixK_mem_cent_iff.mpr rfl
  obtain ⟨hle1, hn1, -⟩ := hH.normal_Mhat Axis.one
  obtain ⟨hle2, hn2, -⟩ := hH.normal_Mhat Axis.two
  have hSn : ((S φ t i).subgroupOf (Tplus φ t i)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hST).mpr ?_
    intro x g hx hg
    exact RootAxisTwoCore.conj_mem_sup (fun y hy => sixK_conj_mem_of_normal hle1 hn1 hg hy)
      (fun y hy => sixK_conj_mem_of_normal hle2 hn2 hg hy) hx
  have htS : t ∈ normalizer (S φ t i : Set G) := sixK_mem_normalizer_of_normal hST hSn htT
  have hzK : zpowers t ≤ normalizer (S φ t i : Set G) := Subgroup.zpowers_le.mpr htS
  have hzC : zpowers t ≤ centralizer ({t} : Set G) := Subgroup.zpowers_le.mpr ht_cent
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [← hH.sup_t] at hxT
    obtain ⟨s, hs, u, hu, rfl⟩ := sixK_mem_sup_factor hzK hxT
    have huC : u ∈ centralizer ({t} : Set G) := hzC hu
    have hsC : s ∈ centralizer ({t} : Set G) := by
      have h := mul_mem hxC (inv_mem huC)
      rwa [mul_inv_cancel_right] at h
    have hsP : s ∈ P φ := by
      rw [← k11']
      exact Subgroup.mem_inf.mpr ⟨hs, hsC⟩
    exact mul_mem (Subgroup.mem_sup_left hsP) (Subgroup.mem_sup_right hu)
  · apply sup_le
    · intro x hx
      rw [← k11'] at hx
      obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hST hxS, hxC⟩
    · exact le_inf (Subgroup.zpowers_le.mpr htT) hzC

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
