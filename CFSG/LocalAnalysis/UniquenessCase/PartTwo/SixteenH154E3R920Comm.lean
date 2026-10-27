module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelOrders
import CFSG.Quasithin.EmptyFaithful.R3c2Excl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Inv9')
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem r920comm_conj_eq_of_order_three
    {H : Type*} [Group H] [Finite H] {K : Subgroup H} (hK : IsSimpleGroup K)
    (h3 : 3 ∣ Nat.card K) {b : H}
    (hb : ∀ x ∈ K, orderOf x = 3 → MulAut.conj b x = x) :
    ∀ x ∈ K, MulAut.conj b x = x := by
  have htop := CFSG.Quasithin.R3c2.closure_orderOf_three_eq_top_of_simple (X := K) h3
  intro x hx
  let xK : K := ⟨x, hx⟩
  have hxcl : xK ∈ Subgroup.closure {y : K | orderOf y = 3} := by
    rw [htop]
    exact Subgroup.mem_top xK
  have hxcl' : MulAut.conj b ((xK : K) : H) = ((xK : K) : H) := by
    refine Subgroup.closure_induction (G := K)
      (p := fun y _ => MulAut.conj b (y : H) = (y : H)) ?_ ?_ ?_ ?_ hxcl
    · intro y hy
      have hy3 : orderOf (y : H) = 3 := by
        rw [Subgroup.orderOf_coe]
        exact hy
      exact hb y y.2 hy3
    · simp
    · intro y z hy hz ihy ihz
      rw [Subgroup.coe_mul, map_mul, ihy, ihz]
    · intro y hy ihy
      rw [Subgroup.coe_inv, map_inv, ihy]
  simpa using hxcl'

theorem commutator_le_pCoreOf_of_mem_inv9' {M L B : Subgroup G} (hL : L ∈ calC M)
    (hL2 : IsL2 (Bar2 L) 3) (hB : B ∈ Inv9' M L 3) : ⁅B, L⁆ ≤ pCoreOf 2 B := by
  obtain ⟨hBM, hB3, hLnormB⟩ := hB
  have hLM : L ≤ M := hL.1.le
  let π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let Lm : Subgroup ↥M := L.subgroupOf M
  let Bm : Subgroup ↥M := B.subgroupOf M
  let Lq : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := Lm.map π
  let Bq : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := Bm.map π
  obtain ⟨hLsn, hLperf, hLqis, hLcen⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_subgroupOf hL
  have hLcomp : CFSG.IsComponent Lq :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.isComponent_image hLsn hLqis
  let eL : Bar2 Lm ≃* Bar2 L :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.bar2Equiv (Subgroup.subgroupOfEquivOfLe hLM)
  let e : Bar2 L ≃* Lq :=
    eL.symm.trans (CFSG.LocalAnalysis.UniquenessCase.UC6S846.barIso hLsn)
  have hLsimpleBar : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have hLqsimple : IsSimpleGroup Lq := by
    haveI := hLsimpleBar
    exact MulEquiv.isSimpleGroup e.symm
  have hcardBar : Nat.card (Bar2 L) = 504 := by
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hL2]
    decide
  have hcardLq : Nat.card Lq = 504 := by
    rw [← Nat.card_congr e.toEquiv, hcardBar]
  have h3Lq : 3 ∣ Nat.card Lq := by rw [hcardLq]; norm_num
  have hBq3 : ¬ 3 ∣ Nat.card Bq := by
    have hdvd : Nat.card Bq ∣ Nat.card B := by
      have h1 : Nat.card Bq ∣ Nat.card Bm := Subgroup.card_map_dvd (H := Bm) π
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv] at h1
    exact fun h => hB3 (h.trans hdvd)
  have hLm_norm_Bm : Lm ≤ Subgroup.normalizer (Bm : Set ↥M) := by
    rw [Subgroup.le_normalizer_iff]
    intro l hl x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hLnormB hl) (x : G)).mp hx
  have hLq_le_norm_Bq : Lq ≤ Subgroup.normalizer (Bq : Set _) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hlB : Bm.map (MulAut.conj l).toMonoidHom = Bm :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLm_norm_Bm hl)
    have hcomp : ((MulAut.conj (π l)).toMonoidHom.comp π) =
        (π.comp (MulAut.conj l).toMonoidHom) := by
      ext x
      simp [MulAut.conj_apply, map_mul]
    calc Bq.map (MulAut.conj (π l)).toMonoidHom
        = (Bm.map π).map (MulAut.conj (π l)).toMonoidHom := rfl
      _ = Bm.map ((MulAut.conj (π l)).toMonoidHom.comp π) := by rw [Subgroup.map_map]
      _ = Bm.map (π.comp (MulAut.conj l).toMonoidHom) := by rw [hcomp]
      _ = (Bm.map (MulAut.conj l).toMonoidHom).map π := by rw [Subgroup.map_map]
      _ = Bq := by rw [hlB]
  have hBq_le_norm_Lq : Bq ≤ Subgroup.normalizer (Lq : Set _) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    let Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := Lq.map (MulAut.conj b).toMonoidHom
    have hLb_comp : CFSG.IsComponent Lb :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj b) hLcomp
    by_contra hne
    change Lb ≠ Lq at hne
    have hcomm : ⁅Lb, Lq⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hLb_comp hLcomp with h | h
      · exact absurd h hne
      · exact h
    have hcentral : ∀ x ∈ Lq, orderOf x = 3 → MulAut.conj b x = x := by
      intro x hx hx3
      have hy : MulAut.conj b x ∈ Lb := Subgroup.mem_map_of_mem _ hx
      have hcommute : x * MulAut.conj b x = MulAut.conj b x * x := by
        have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
        exact Subgroup.mem_centralizer_iff.mp (hc hy) x hx
      let c : ↥M ⧸ CFSG.pCore 2 ↥M := x⁻¹ * MulAut.conj b x
      have hcB : c ∈ Bq := by
        have hxinv : x⁻¹ ∈ Subgroup.normalizer (Bq : Set _) :=
          hLq_le_norm_Bq (Lq.inv_mem hx)
        have hconj : MulAut.conj x⁻¹ b ∈ Bq :=
          (Subgroup.mem_normalizer_iff.mp hxinv b).mp hb
        have hc_eq : c = MulAut.conj x⁻¹ b * b⁻¹ := by
          simp [c, MulAut.conj_apply]
          group
        rw [hc_eq]
        exact Bq.mul_mem hconj (Bq.inv_mem hb)
      have hc3 : c ^ 3 = 1 := by
        have hx3' : x ^ 3 = 1 := by
          rw [← hx3]
          exact pow_orderOf_eq_one x
        have hyord : orderOf (MulAut.conj b x) = 3 := by
          change orderOf ((MulAut.conj b).toMonoidHom x) = 3
          rw [orderOf_injective (MulAut.conj b).toMonoidHom (MulAut.conj b).injective x, hx3]
        have hy3 : (MulAut.conj b x) ^ 3 = 1 := by
          rw [← hyord]
          exact pow_orderOf_eq_one (MulAut.conj b x)
        have hcommxy : Commute x (MulAut.conj b x) := hcommute
        rw [show c = x⁻¹ * MulAut.conj b x from rfl]
        rw [(hcommxy.inv_left).mul_pow]
        simp [hx3', hy3]
      have hc_dvd3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
      have hc_dvdB : orderOf c ∣ Nat.card Bq := by
        simpa [Subgroup.orderOf_coe] using Subgroup.orderOf_dvd_natCard Bq hcB
      rcases (Nat.dvd_prime Nat.prime_three).mp hc_dvd3 with h1 | h3
      · rw [orderOf_eq_one_iff] at h1
        rw [h1] at hc_dvdB
        have : MulAut.conj b x = x := by
          have h := h1
          rw [show c = x⁻¹ * MulAut.conj b x from rfl] at h
          calc MulAut.conj b x = x * (x⁻¹ * MulAut.conj b x) := by group
            _ = x * 1 := by rw [h]
            _ = x := by rw [mul_one]
        exact this
      · exact absurd (h3 ▸ hc_dvdB) hBq3
    have hcentralAll : ∀ x ∈ Lq, MulAut.conj b x = x :=
      r920comm_conj_eq_of_order_three hLqsimple h3Lq hcentral
    have hfix : Lq.map (MulAut.conj b).toMonoidHom = Lq := by
      apply le_antisymm
      · rintro y ⟨x, hx, rfl⟩
        rw [show (MulAut.conj b).toMonoidHom x = x from hcentralAll x hx]
        exact hx
      · intro y hy
        exact ⟨y, hy, hcentralAll y hy⟩
    exact hne (by simpa [Lb] using hfix)
  have hC_normal : ((Bq ⊓ Lq).subgroupOf Lq).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact (le_inf hLq_le_norm_Bq Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Bq) (K := Lq))
  have hCbot : Bq ⊓ Lq = ⊥ := by
    haveI := hC_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Bq ⊓ Lq).subgroupOf Lq) with h | h
    · have hdisj := Subgroup.subgroupOf_eq_bot.mp h
      have h' : (Bq ⊓ Lq) ⊓ Lq = ⊥ := disjoint_iff.mp hdisj
      simpa [inf_assoc] using h'
    · have hle : Lq ≤ Bq ⊓ Lq := Subgroup.subgroupOf_eq_top.mp h
      have hLqB : Lq ≤ Bq := hle.trans inf_le_left
      have hdvd : Nat.card Lq ∣ Nat.card Bq := Subgroup.card_dvd_of_le hLqB
      have h3dvd : 3 ∣ Nat.card Bq := by
        rw [hcardLq] at hdvd
        exact (by norm_num : 3 ∣ 504).trans hdvd
      exact absurd h3dvd hBq3
  have hcommBL : ⁅Bq, Lq⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b hb x hx
    have hx' : b * x * b⁻¹ ∈ Lq :=
      (Subgroup.mem_normalizer_iff.mp (hBq_le_norm_Lq hb) x).mp hx
    have hb' : x * b⁻¹ * x⁻¹ ∈ Bq :=
      (Subgroup.mem_normalizer_iff.mp (hLq_le_norm_Bq hx) b⁻¹).mp (Bq.inv_mem hb)
    have hmemL : ⁅b, x⁆ ∈ Lq := by
      rw [commutatorElement_def]
      exact Lq.mul_mem hx' (Lq.inv_mem hx)
    have hmemB : ⁅b, x⁆ ∈ Bq := by
      rw [commutatorElement_def]
      rw [show b * x * b⁻¹ * x⁻¹ = b * (x * b⁻¹ * x⁻¹) by group]
      exact Bq.mul_mem hb hb'
    have hmem : ⁅b, x⁆ ∈ Bq ⊓ Lq := ⟨hmemB, hmemL⟩
    rw [hCbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hker : ∀ x : ↥M, π x = 1 ↔ (x : G) ∈ pCoreOf 2 M := by
    intro x
    change QuotientGroup.mk' (CFSG.pCore 2 ↥M) x = 1 ↔ (x : G) ∈ pCoreOf 2 M
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact Subgroup.mem_map_of_mem M.subtype hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have : y = x := Subtype.ext hyx
      simpa [this] using hy
  have hBL_le_pCoreM : ⁅B, L⁆ ≤ pCoreOf 2 M := by
    rw [Subgroup.commutator_le]
    intro b hb l hl
    let bm : ↥M := ⟨b, hBM hb⟩
    let lm : ↥M := ⟨l, hLM hl⟩
    have hbm : π bm ∈ Bq :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb)
    have hlm : π lm ∈ Lq :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hl)
    have hcommq : ⁅π bm, π lm⁆ = 1 := by
      have hmem : ⁅π bm, π lm⁆ ∈ ⁅Bq, Lq⁆ :=
        Subgroup.commutator_mem_commutator hbm hlm
      rw [hcommBL] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hpi : π ⁅bm, lm⁆ = 1 := by
      rw [map_commutatorElement]
      exact hcommq
    have hmemG : (⁅bm, lm⁆ : ↥M) ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq_one_iff]
      exact hpi
    have hmemG' : ((⁅bm, lm⁆ : ↥M) : G) ∈ pCoreOf 2 M :=
      Subgroup.mem_map_of_mem M.subtype hmemG
    change ⁅b, l⁆ ∈ pCoreOf 2 M
    exact hmemG'
  have hBL_le_B : ⁅B, L⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro b hb l hl
    have h1 : l * b⁻¹ * l⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hLnormB hl) b⁻¹).mp (B.inv_mem hb)
    rw [commutatorElement_def]
    rw [show b * l * b⁻¹ * l⁻¹ = b * (l * b⁻¹ * l⁻¹) by group]
    exact B.mul_mem hb h1
  have hcore_le : B ⊓ pCoreOf 2 M ≤ pCoreOf 2 B := by
    have hB_norm_B : B ≤ Subgroup.normalizer (B : Set G) := Subgroup.le_normalizer
    have hB_norm_P : B ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      hBM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    have hnormal : ((B ⊓ pCoreOf 2 M).subgroupOf B).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      exact (le_inf hB_norm_B hB_norm_P).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := pCoreOf 2 M))
    have hp : IsPGroup 2 (B ⊓ pCoreOf 2 M : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right
    exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2)
      (N := (B ⊓ pCoreOf 2 M : Subgroup G)) (H := B) inf_le_left hnormal hp
  exact (le_inf hBL_le_B hBL_le_pCoreM).trans hcore_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
