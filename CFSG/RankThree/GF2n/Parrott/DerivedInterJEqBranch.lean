module

public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
import all CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.CommutatorTripleIndexTwo
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem P_H_conjV_fixes_Fsub (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) {hH : ↥(H z)} (hhH : hH ∈ P_H (z := z) D)
    {v : QuotientV.V z} (hv : v ∈ Fsub (z := z) (sigma1Nine (z := z) D)) :
    conjV h hH v = v := by
  have hq : qH (z := z) (D := D) hH ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    (mem_P_H_iff (z := z) (D := D) hH).mp hhH
  let a : QP45.originalSubgroup :=
    ⟨qH (z := z) (D := D) hH, Subgroup.mem_subgroupOf.mp hq⟩
  have hact : actFsub (z := z) (D := D) h hJ0
      (QuotientGroup.mk' ((J z).subgroupOf (H z)) hH) = 1 := by
    have h1 : actQFsub (z := z) (D := D) h hJ0 a = 1 := by
      rw [actQFsub_eq_one (z := z) (D := D) h hJ0]
      rfl
    have h2 : (D.toQA45 (z := z) (hN := hN)).symm
        (Subgroup.inclusion QP45_le_QA45 a) =
        QuotientGroup.mk' ((J z).subgroupOf (H z)) hH := by
      have h3 : Subgroup.inclusion QP45_le_QA45 a = qH (z := z) (D := D) hH := rfl
      rw [h3, toQA45_symm_qH]
    simpa [actQFsub, h2] using h1
  have happ : actionA h (QuotientGroup.mk' ((J z).subgroupOf (H z)) hH) v = v := by
    have hfix : actFsub (z := z) (D := D) h hJ0
        (QuotientGroup.mk' ((J z).subgroupOf (H z)) hH) ⟨v, hv⟩ = ⟨v, hv⟩ := by
      rw [hact]
      rfl
    exact congrArg Subtype.val hfix
  rw [← actionA_mk (z := z) h hH]
  exact happ

theorem P_H_commutator_CJ_le_center (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) :
    ⁅(P_H (z := z) D).map (H z).subtype, CJ z (sigma1Nine (z := z) D : G)⁆ ≤ centerIn (J z) := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨hH, hhH, rfl⟩ x hx
  have hxJ : x ∈ J z := hx.2
  let xJ : J z := ⟨x, hxJ⟩
  have hxc : (xJ : G) * (sigma1Nine (z := z) D : G) =
      (sigma1Nine (z := z) D : G) * (xJ : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hx.1
  have hxJc : xJ ∈ centralizerJ (sigma1Nine (z := z) D) := by
    rw [mem_centralizerJ_iff]
    exact hxc
  have hv : QuotientV.pi z xJ ∈ Fsub (z := z) (sigma1Nine (z := z) D) :=
    Subgroup.mem_map.mpr ⟨xJ, hxJc, rfl⟩
  have hfix := P_H_conjV_fixes_Fsub (z := z) (D := D) h hJ0 hhH hv
  rw [conjV_mk] at hfix
  have hker : conjJ' z hH xJ * xJ⁻¹ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfix]
    simp
  have hmemZ : ((conjJ' z hH xJ * xJ⁻¹ : J z) : G) ∈ centerIn (J z) := by
    have h := hker
    rwa [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at h
  have hcomm_eq : ⁅((hH : ↥(H z)) : G), x⁆ = ((conjJ' z hH xJ * xJ⁻¹ : J z) : G) := by
    have h1 : ((conjJ' z hH xJ : J z) : G) = (hH : G) * x * (hH : G)⁻¹ := by
      rw [conjJ'_apply_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1]
    simp [xJ, commutatorElement_def]
  show ⁅((hH : ↥(H z)) : G), x⁆ ∈ centerIn (J z)
  rw [hcomm_eq]
  exact hmemZ

theorem P_H_commute_centerIn (h : Tim79a.ParrottHyp z) {hH : ↥(H z)}
    (hhH : hH ∈ P_H (z := z) D) {w : G} (hw : w ∈ centerIn (J z)) :
    (hH : G) * w = w * (hH : G) := by
  have hq : ((qH (z := z) (D := D) hH : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) ∈
      QP45.originalSubgroup :=
    Subgroup.mem_subgroupOf.mp ((mem_P_H_iff (z := z) (D := D) hH).mp hhH)
  have h1 := conjZ_eq_one_of_qH_mem_QP45 (z := z) D h hH hq
  have h2 := congrArg (fun φ => ((φ ⟨w, hw⟩ : ↥(centerIn (J z))) : G)) h1
  simp only [conjZ_apply_coe, MulAut.one_apply] at h2
  calc (hH : G) * w = ((hH : G) * w * (hH : G)⁻¹) * (hH : G) := by group
    _ = w * (hH : G) := by rw [h2]

theorem P_H_derived_commutator_CJ_eq_bot (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) :
    ⁅⁅(P_H (z := z) D).map (H z).subtype, (P_H (z := z) D).map (H z).subtype⁆,
      CJ z (sigma1Nine (z := z) D : G)⁆ = ⊥ := by
  have hZP : centerIn (J z) ≤
      Subgroup.centralizer (((P_H (z := z) D).map (H z).subtype : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨hH, hhH, rfl⟩
    exact P_H_commute_centerIn (z := z) D h hhH hw
  have h1 : ⁅⁅(P_H (z := z) D).map (H z).subtype, CJ z (sigma1Nine (z := z) D : G)⁆,
      (P_H (z := z) D).map (H z).subtype⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (P_H_commutator_CJ_le_center (z := z) D h hJ0).trans hZP
  have h2 : ⁅⁅CJ z (sigma1Nine (z := z) D : G), (P_H (z := z) D).map (H z).subtype⁆,
      (P_H (z := z) D).map (H z).subtype⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (CJ z (sigma1Nine (z := z) D : G))]
    exact h1
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem derived_inter_J_le_J1sub_of_J0sub_normal (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) :
    ⁅H z, ⁅H z, H z⁆⁆ ⊓ J z ≤ J1sub (z := z) (D := D) h := by
  classical
  have hK : IsKleinFour ↥(centerIn (J z)) := isKleinFour_centerIn_J h
  set P : Subgroup ↥(H z) := P_H (z := z) D with hPdef
  set J0 : Subgroup ↥(H z) := J0sub (z := z) (D := D) with hJ0def
  have hPn : P.Normal := P_H_normal D
  have hCn : (Subgroup.centralizer (J0 : Set ↥(H z))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ J0 := hJ0.conj_mem y hy g⁻¹
    have hc := Subgroup.mem_centralizer_iff.mp hn _ hy'
    calc y * (g * n * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
      _ = g * n * g⁻¹ * y := by group
  set N : Subgroup ↥(H z) := P ⊓ Subgroup.centralizer (J0 : Set ↥(H z)) with hNdef
  haveI : N.Normal := by
    haveI := hPn
    haveI := hCn
    infer_instance
  have hL1 := P_H_commutator_CJ_le_center (z := z) D h hJ0
  have hL2 := P_H_derived_commutator_CJ_eq_bot (z := z) D h hJ0
  have hJ0mem : ∀ y : ↥(H z), y ∈ J0 → (y : G) ∈ CJ z (sigma1Nine (z := z) D : G) := by
    intro y hy
    obtain ⟨hyJ, hyc⟩ := (mem_J0sub_iff' (z := z) (D := D)).mp hy
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyc, hyJ⟩
  have hPmap : ∀ a ∈ P, (a : G) ∈ P.map (H z).subtype := fun a ha => Subgroup.mem_map_of_mem _ ha
  have hH3 : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ N := by
    intro a ha b hb
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    · intro y hy
      have hu : ((⁅a, b⁆ : ↥(H z)) : G) ∈
          ⁅(P.map (H z).subtype), (P.map (H z).subtype)⁆ := by
        have := Subgroup.commutator_mem_commutator (hPmap a ha) (hPmap b hb)
        simpa [commutatorElement_def] using this
      have hcomm := Subgroup.commutator_mem_commutator hu (hJ0mem y hy)
      rw [hL2] at hcomm
      have h1 : ⁅((⁅a, b⁆ : ↥(H z)) : G), (y : G)⁆ = 1 := Subgroup.mem_bot.mp hcomm
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact Subtype.ext h1.symm
  have hH4 : ∀ a ∈ P, a * a ∈ N := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨P.mul_mem ha ha, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hc : ⁅(a : G), (y : G)⁆ ∈ centerIn (J z) :=
      hL1 (Subgroup.commutator_mem_commutator (hPmap a ha) (hJ0mem y hy))
    obtain ⟨c, hcdef⟩ : ∃ c : G, c = ⁅(a : G), (y : G)⁆ := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have E1 : (a : G) * y = c * y * a := by
      rw [hcdef, commutatorElement_def]
      group
    have E2 : (a : G) * c = c * a := P_H_commute_centerIn (z := z) D h ha hc
    have E3 : c * c = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨c, hc⟩ : ↥(centerIn (J z))))
    apply Subtype.ext
    show (y : G) * ((a : G) * a) = ((a : G) * a) * y
    calc (y : G) * ((a : G) * a) = y * a * a := by group
      _ = c * c * y * a * a := by rw [E3]; group
      _ = c * (c * y * a) * a := by group
      _ = c * (a * y) * a := by rw [← E1]
      _ = (c * a) * y * a := by group
      _ = (a * c) * y * a := by rw [E2]
      _ = a * (c * y * a) := by group
      _ = a * (a * y) := by rw [← E1]
      _ = (a * a) * y := by group
  set π := QuotientGroup.mk' N with hπ
  have hPidx : (P.map π).index = 2 := by
    rw [Subgroup.index_map_eq P (QuotientGroup.mk'_surjective N)
      (by rw [QuotientGroup.ker_mk']; exact inf_le_left)]
    exact index_P_H D
  have hcomm' : ∀ a' ∈ P.map π, ∀ b' ∈ P.map π, a' * b' = b' * a' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hH3 b⁻¹ (P.inv_mem hb) a⁻¹ (P.inv_mem ha)
  have hsq' : ∀ a' ∈ P.map π, a' * a' = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (a * a)).mpr (hH4 a ha)
  have hcl := commutator_triple_eq_one_of_index_two_elemAbelian (P.map π) hPidx hcomm' hsq'
  have hKcomm : ⁅(⊤ : Subgroup ↥(H z)), (⊤ : Subgroup ↥(H z))⁆ ≤
      (Subgroup.center (↥(H z) ⧸ N)).comap π := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro a'
    have h1 := hcl a' (π x) (π y)
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    rw [map_commutatorElement]
    exact h1
  have hγ3 : ⁅(⊤ : Subgroup ↥(H z)), ⁅(⊤ : Subgroup ↥(H z)), (⊤ : Subgroup ↥(H z))⁆⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a _ u hu
    have hu' := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp (hKcomm hu))
    have hmem : ⁅a, u⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hu' (π a)
    rwa [hπ, QuotientGroup.ker_mk'] at hmem
  intro x hx
  obtain ⟨hxγ, hxJ⟩ := Subgroup.mem_inf.mp hx
  have hmap : ⁅H z, ⁅H z, H z⁆⁆ = (⁅(⊤ : Subgroup ↥(H z)),
      ⁅(⊤ : Subgroup ↥(H z)), (⊤ : Subgroup ↥(H z))⁆⁆).map (H z).subtype := by
    simp only [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [hmap] at hxγ
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hxγ
  have hnc : n ∈ Subgroup.centralizer (J0 : Set ↥(H z)) := (hγ3 hn).2
  have hxJ' : ((n : ↥(H z)) : G) ∈ J z := hxJ
  let xJ : J z := ⟨(n : G), hxJ'⟩
  have hyJ_c : xJ ∈ Subgroup.centralizer
      (centralizerJ (sigma1Nine (z := z) D) : Set (J z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcJ0 : (⟨(c : G), J_le_H (z := z) c.2⟩ : ↥(H z)) ∈ J0 :=
      (mem_J0sub_iff' (z := z) (D := D)).mpr ⟨c.2, mem_centralizerJ_iff.mp hc⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hnc _ hcJ0
    have hcomm' : (c : G) * ((n : ↥(H z)) : G) = ((n : ↥(H z)) : G) * (c : G) :=
      congrArg Subtype.val hcomm
    exact Subtype.ext hcomm'
  have hyMap : ((n : ↥(H z)) : G) ∈ (Subgroup.centralizer
      (centralizerJ (sigma1Nine (z := z) D) : Set (J z))).map (J z).subtype :=
    Subgroup.mem_map.mpr ⟨xJ, hyJ_c, rfl⟩
  rwa [centralizer_centralizerJ_eq_J1sub (z := z) (D := D) h] at hyMap

theorem derived_inter_J_le_J1sub_of_equalityBranch (h : Tim79a.ParrottHyp z)
    (hEq : ParrottEqualityBranch (z := z) (D := D) h) :
    ⁅H z, ⁅H z, H z⁆⁆ ⊓ J z ≤ J1sub (z := z) (D := D) h := by
  obtain ⟨σ₂, hs₂, hq₂, hCJ⟩ := hEq
  exact derived_inter_J_le_J1sub_of_J0sub_normal (z := z) D h
    (J0sub_normal (z := z) (D := D) h hCJ hs₂ hq₂)

end CFSG.RankThree.GF2n.Parrott
