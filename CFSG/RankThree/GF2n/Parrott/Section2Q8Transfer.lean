module

public import CFSG.RankThree.GF2n.Parrott.Section2Q8

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

omit
  hN in
theorem map_centralizerJ_conj (g x : ↥(H z)) :
    (centralizerJ x).map (conjJ' z g).toMonoidHom =
      centralizerJ (g * x * g⁻¹) := by
  ext j
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha'' : a ∈ centralizerJ x := ha
    have ha' : (a : G) * (x : G) = (x : G) * (a : G) :=
      mem_centralizerJ_iff.mp ha''
    have hgoal : (conjJ' z g a : J z) ∈ centralizerJ (g * x * g⁻¹) := by
      rw [mem_centralizerJ_iff]
      rw [conjJ'_apply_coe]
      calc ((g : G) * (a : G) * (g : G)⁻¹) *
            ((g * x * g⁻¹ : ↥(H z)) : G)
          = (g : G) * ((a : G) * (x : G)) * (g : G)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = (g : G) * ((x : G) * (a : G)) * (g : G)⁻¹ := by rw [ha']
        _ = ((g * x * g⁻¹ : ↥(H z)) : G) *
            ((g : G) * (a : G) * (g : G)⁻¹) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    exact hgoal
  · intro hj
    have hj'' : j ∈ centralizerJ (g * x * g⁻¹) := hj
    have hj' : (j : G) * ((g * x * g⁻¹ : ↥(H z)) : G) =
        ((g * x * g⁻¹ : ↥(H z)) : G) * (j : G) :=
      mem_centralizerJ_iff.mp hj''
    refine ⟨(conjJ' z g).symm j, ?_, by simp⟩
    have hgoal : ((conjJ' z g).symm j : J z) ∈ centralizerJ x := by
      rw [mem_centralizerJ_iff]
      have hsymm : ((conjJ' z g).symm j : G) =
          (g : G)⁻¹ * (j : G) * (g : G) := by
        have h1 : (conjJ' z g).symm j = conjJ' z g⁻¹ j := by
          rw [← MulAut.inv_apply, ← map_inv]
        rw [h1, conjJ'_apply_coe]
        simp only [Subgroup.coe_inv, inv_inv]
      rw [hsymm]
      calc ((g : G)⁻¹ * (j : G) * (g : G)) * (x : G)
          = (g : G)⁻¹ * ((j : G) * ((g * x * g⁻¹ : ↥(H z)) : G)) * (g : G) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = (g : G)⁻¹ * (((g * x * g⁻¹ : ↥(H z)) : G) * (j : G)) * (g : G) := by
            rw [hj']
        _ = (x : G) * ((g : G)⁻¹ * (j : G) * (g : G)) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    exact hgoal

theorem map_sigma1Commutator_subgroupOf_conj (g : ↥(H z))
    (hnorm : ∀ p : G, p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ↔
      (g : G) * p * (g : G)⁻¹ ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z)).map
        (conjJ' z g).toMonoidHom =
      (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z) := by
  ext j
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha'' : a ∈
        (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
          (J z) := ha
    have ha' : (a : G) ∈
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
      (Subgroup.mem_subgroupOf).mp ha''
    change ((conjJ' z g a : J z) : G) ∈
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆
    rw [conjJ'_apply_coe]
    exact (hnorm (a : G)).mp ha'
  · intro hj
    have hj'' : j ∈
        (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
          (J z) := hj
    have hj' : (j : G) ∈
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
      (Subgroup.mem_subgroupOf).mp hj''
    refine ⟨(conjJ' z g).symm j, ?_, by simp⟩
    change (((conjJ' z g).symm j : J z) : G) ∈
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆
    have hsymm : ((conjJ' z g).symm j : G) =
        (g : G)⁻¹ * (j : G) * (g : G) := by
      have h1 : (conjJ' z g).symm j = conjJ' z g⁻¹ j := by
        rw [← MulAut.inv_apply, ← map_inv]
      rw [h1, conjJ'_apply_coe]
      simp only [Subgroup.coe_inv, inv_inv]
    rw [hsymm]
    refine (hnorm ((g : G)⁻¹ * (j : G) * (g : G))).mpr ?_
    have hg : (g : G) * ((g : G)⁻¹ * (j : G) * (g : G)) * (g : G)⁻¹ =
        (j : G) := by group
    rwa [hg]

theorem map_CJcomm_conj (g x : ↥(H z))
    (hnorm : ∀ p : G, p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ↔
      (g : G) * p * (g : G)⁻¹ ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    (CJcomm (z := z) (D := D) x).map (conjJ' z g).toMonoidHom =
      CJcomm (z := z) (D := D) (g * x * g⁻¹) := by
  have hC := map_centralizerJ_conj (z := z) g x
  have hP := map_sigma1Commutator_subgroupOf_conj (z := z) (D := D) g hnorm
  rw [CJcomm, Subgroup.map_inf _ _ _ (conjJ' z g).injective, hC, hP]
  rfl

theorem card_CJcomm_conj (g x : ↥(H z))
    (hnorm : ∀ p : G, p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ↔
      (g : G) * p * (g : G)⁻¹ ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    Nat.card ↥(CJcomm (z := z) (D := D) (g * x * g⁻¹)) =
      Nat.card ↥(CJcomm (z := z) (D := D) x) := by
  have hmap := map_CJcomm_conj (z := z) (D := D) g x hnorm
  calc Nat.card ↥(CJcomm (z := z) (D := D) (g * x * g⁻¹))
      = Nat.card ↥((CJcomm (z := z) (D := D) x).map
          (conjJ' z g).toMonoidHom) := by rw [hmap]
    _ = Nat.card ↥(CJcomm (z := z) (D := D) x) :=
        Subgroup.card_map_of_injective (conjJ' z g).injective

theorem mem_fixW_iff_of_mem_K_of_odd (h : Tim79a.ParrottHyp z) (x : ↥(H z))
    (hxK : x ∈ K D) (hxodd : Odd (orderOf x))
    (v : Additive (QuotientV.V z)) :
    v ∈ fixW (D := D) h x ↔
      Additive.toMul v ∈ (CJcomm (z := z) (D := D) x).map (QuotientV.pi z) := by
  classical
  have hxnorm : (x : G) ∈ Subgroup.normalizer
      ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :
        Subgroup G) : Set G) :=
    K_le_normalizer_commutator_sigma1Nine D x hxK
  constructor
  · intro hv
    have hvfix : Additive.toMul v ∈ autFixedSubgroup (conjV h x) :=
      (mem_fixSubmodule_iff h x v).mp hv.1
    have hvfixed : conjV h x (Additive.toMul v) = Additive.toMul v :=
      mem_autFixedSubgroup.mp hvfix
    have hvW : Additive.toMul v ∈
        ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
          (J z)).map (QuotientV.pi z) := hv.2
    obtain ⟨p, hpP, hpv⟩ := Subgroup.mem_map.mp hvW
    let c : J z := conjJ' z x p * p⁻¹
    have hfpP : conjJ' z x p ∈
        (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z) := by
      rw [Subgroup.mem_subgroupOf]
      rw [conjJ'_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hxnorm (p : G)).mp
        (Subgroup.mem_subgroupOf.mp hpP)
    have hcP : (c : G) ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      have h1 : (conjJ' z x p : G) ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
        Subgroup.mem_subgroupOf.mp hfpP
      have h2 : (p : G)⁻¹ ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
        (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).inv_mem (Subgroup.mem_subgroupOf.mp hpP)
      simpa [c] using (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).mul_mem h1 h2
    have hπfp : QuotientV.pi z (conjJ' z x p) = QuotientV.pi z p := by
      rw [← conjV_mk h x p, hpv, hvfixed]
    have hcZ : (c : G) ∈ centerIn (J z) := by
      have hker : c ∈ (QuotientV.pi z).ker := by
        rw [MonoidHom.mem_ker]
        show QuotientV.pi z (conjJ' z x p * p⁻¹) = 1
        rw [map_mul, map_inv, hπfp, mul_inv_cancel]
      rw [QuotientV.pi_ker] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    have hc_mem : (c : G) ∈ Subgroup.zpowers z := by
      rw [← commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
      exact Subgroup.mem_inf.mpr ⟨hcP, hcZ⟩
    have hc_cases : (c : G) = 1 ∨ (c : G) = z := by
      have hrange : (c : G) ∈ (Finset.range (orderOf z)).image (fun k => z ^ k) :=
        (mem_zpowers_iff_mem_range_orderOf (x := z)).mp hc_mem
      rw [h.1] at hrange
      simp only [Finset.mem_image, Finset.mem_range] at hrange
      obtain ⟨k, hklt, hk⟩ := hrange
      interval_cases k
      · left; simpa using hk.symm
      · right; simpa using hk.symm
    have hc2 : (c : G) ^ 2 = 1 := by
      rcases hc_cases with hc | hc
      · rw [hc]; norm_num
      · rw [hc]
        simpa [h.1] using pow_orderOf_eq_one z
    have hcfix : conjJ' z x c = c := by
      apply Subtype.ext
      rw [conjJ'_apply_coe]
      rcases hc_cases with hc | hc
      · rw [hc]; group
      · rw [hc]
        have hzx : (x : G) * z = z * (x : G) :=
          Subgroup.mem_centralizer_iff.mp (z_centralizes_H (z := z) h) (x : G) x.2
        calc (x : G) * z * (x : G)⁻¹ = z * (x : G) * (x : G)⁻¹ := by rw [hzx]
          _ = z := by group
    have hfp : conjJ' z x p = c * p := by
      change conjJ' z x p = (conjJ' z x p * p⁻¹) * p
      group
    have hiter : ∀ n : ℕ, ((conjJ' z x) ^ n) p = c ^ n * p := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hcfix, hfp, pow_succ']
        group
    have hf_n : (conjJ' z x) ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hp_eq : p = c ^ orderOf x * p := by
      have h := hiter (orderOf x)
      rw [hf_n, MulAut.one_apply] at h
      exact h
    have hcG_pow : (c : G) ^ orderOf x = c := by
      obtain ⟨m, hm⟩ := hxodd
      rw [hm, pow_add, pow_mul, hc2, one_pow, one_mul, pow_one]
    have hc_pow : c ^ orderOf x = c := by
      apply Subtype.ext
      simpa using hcG_pow
    have hc1 : c = 1 := by
      have hcp : c * p = p := by
        calc c * p = c ^ orderOf x * p := by rw [hc_pow]
          _ = p := hp_eq.symm
      exact mul_right_cancel (b := 1) (by simpa using hcp)
    have hfp1 : conjJ' z x p = p := by
      rw [hfp, hc1, one_mul]
    refine Subgroup.mem_map.mpr ⟨p, ?_, hpv⟩
    refine Subgroup.mem_inf.mpr ⟨?_, hpP⟩
    rw [← autFixedSubgroup_conjJ'_eq_centralizerJ (z := z) (x := x)]
    exact mem_autFixedSubgroup.mpr hfp1
  · rintro ⟨p, hp, hpv⟩
    have hpfix : conjJ' z x p = p := by
      have hpCJ : p ∈ centralizerJ x := hp.1
      rw [← autFixedSubgroup_conjJ'_eq_centralizerJ (z := z) (x := x)] at hpCJ
      exact mem_autFixedSubgroup.mp hpCJ
    have hfix : conjV h x (QuotientV.pi z p) = QuotientV.pi z p := by
      rw [conjV_mk, hpfix]
    have hv : v = Additive.ofMul (QuotientV.pi z p) := by
      rw [hpv]
      simp
    rw [hv]
    change Additive.ofMul (QuotientV.pi z p) ∈
      fixSubmodule h x ⊓ WsubModule (z := z) (D := D) h
    constructor
    · exact (mem_fixSubmodule_iff h x (Additive.ofMul (QuotientV.pi z p))).mpr
        (mem_autFixedSubgroup.mpr (by simpa using hfix))
    · change QuotientV.pi z p ∈ Wsub h (sigma1Nine (z := z) D)
      exact Subgroup.mem_map.mpr ⟨p, hp.2, rfl⟩

theorem card_CJcomm_eq_of_mem_K_of_odd (h : Tim79a.ParrottHyp z) (x : ↥(H z))
    (hxK : x ∈ K D) (hxodd : Odd (orderOf x)) :
    Nat.card ↥(CJcomm (z := z) (D := D) x) =
      2 ^ Module.finrank (ZMod 2) (fixW (D := D) h x) * 2 := by
  classical
  let : CommGroup (QuotientV.V z) := commGroupV h
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  let f : CJcomm (z := z) (D := D) x →* QuotientV.V z :=
    (QuotientV.pi z).comp (CJcomm (z := z) (D := D) x).subtype
  have hker : f.ker =
      ((Subgroup.zpowers z).subgroupOf (J z)).subgroupOf
        (CJcomm (z := z) (D := D) x) := by
    ext j
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · intro hj
      have hjZ : (j : J z) ∈ (centerIn (J z)).subgroupOf (J z) := by
        rw [← QuotientV.pi_ker]
        exact MonoidHom.mem_ker.mpr hj
      have hjP : (j : J z) ∈
          (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z) := j.2.2
      have hPZ : (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z) ⊓
            (centerIn (J z)).subgroupOf (J z) =
          (Subgroup.zpowers z).subgroupOf (J z) := by
        apply le_antisymm
        · rintro y ⟨hyP, hyZ⟩
          have hyP' : (y : G) ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
            Subgroup.mem_subgroupOf.mp hyP
          have hyZ' : (y : G) ∈ centerIn (J z) := Subgroup.mem_subgroupOf.mp hyZ
          rw [← commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
          exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hyP', hyZ'⟩)
        · intro y hy
          have hy' : (y : G) ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ⊓ centerIn (J z) := by
            rw [commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
            exact Subgroup.mem_subgroupOf.mp hy
          exact Subgroup.mem_inf.mpr
            ⟨Subgroup.mem_subgroupOf.mpr hy'.1, Subgroup.mem_subgroupOf.mpr hy'.2⟩
      have hmem : (j : J z) ∈
          (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z) ⊓
            (centerIn (J z)).subgroupOf (J z) :=
        Subgroup.mem_inf.mpr ⟨hjP, hjZ⟩
      rw [hPZ] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    · intro hj
      have hzJ : Subgroup.zpowers z ≤ J z := Subgroup.zpowers_le.mpr (z_mem_J h)
      have hjPZ : (j : J z) ∈
          (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z) ⊓
            (centerIn (J z)).subgroupOf (J z) := by
        apply Subgroup.mem_inf.mpr
        constructor
        · rw [Subgroup.mem_subgroupOf]
          have hzP : z ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
            have hz : z ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ⊓ centerIn (J z) := by
              rw [commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
              exact Subgroup.mem_zpowers z
            exact hz.1
          exact Subgroup.zpowers_le.mpr hzP hj
        · rw [Subgroup.mem_subgroupOf]
          have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
          exact Subgroup.zpowers_le.mpr hzZ hj
      have hjZ : (j : J z) ∈ (centerIn (J z)).subgroupOf (J z) :=
        (Subgroup.mem_inf.mp hjPZ).2
      rw [← MonoidHom.mem_ker, QuotientV.pi_ker]
      exact hjZ
  have hkercard : Nat.card ↥f.ker = 2 := by
    rw [hker]
    have hzJ : Subgroup.zpowers z ≤ J z := Subgroup.zpowers_le.mpr (z_mem_J h)
    have hzP : z ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      have hz : z ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ⊓ centerIn (J z) := by
        rw [commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
        exact Subgroup.mem_zpowers z
      exact hz.1
    have hzle : (Subgroup.zpowers z).subgroupOf (J z) ≤
        CJcomm (z := z) (D := D) x := by
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_centralizerJ_iff]
        have hyz : Commute (x : G) (y : G) := by
          have hxz : Commute (x : G) z := by
            have hzx : (x : G) * z = z * (x : G) :=
              Subgroup.mem_centralizer_iff.mp (z_centralizes_H (z := z) h) (x : G) x.2
            exact hzx
          have hy' : (y : G) ∈ Subgroup.zpowers z := hy
          rw [Subgroup.mem_zpowers_iff] at hy'
          obtain ⟨m, hm⟩ := hy'
          rw [← hm]
          exact hxz.zpow_right m
        exact hyz.symm.eq
      · rw [Subgroup.mem_subgroupOf]
        exact Subgroup.zpowers_le.mpr hzP hy
    calc Nat.card ↥(((Subgroup.zpowers z).subgroupOf (J z)).subgroupOf
          (CJcomm (z := z) (D := D) x))
        = Nat.card ↥((Subgroup.zpowers z).subgroupOf (J z)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv
      _ = Nat.card ↥(Subgroup.zpowers z) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzJ).toEquiv
      _ = 2 := by rw [Nat.card_zpowers, h.1]
  have hrange : f.range = (CJcomm (z := z) (D := D) x).map (QuotientV.pi z) := by
    rw [show f = (QuotientV.pi z).comp
        (CJcomm (z := z) (D := D) x).subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard_fixW : Nat.card ↥(fixW (D := D) h x) =
      2 ^ Module.finrank (ZMod 2) (fixW (D := D) h x) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixW (D := D) h x)),
      Nat.card_zmod]
  have hcard_map_fixW : Nat.card ↥((CJcomm (z := z) (D := D) x).map
        (QuotientV.pi z)) =
      Nat.card ↥(fixW (D := D) h x) := by
    apply Nat.card_congr
    refine
      { toFun := fun v => ⟨Additive.ofMul v.1,
          (mem_fixW_iff_of_mem_K_of_odd (z := z) (D := D) h x hxK hxodd
            (Additive.ofMul v.1)).mpr (by simp)⟩
        invFun := fun w => ⟨Additive.toMul w.1,
          (mem_fixW_iff_of_mem_K_of_odd (z := z) (D := D) h x hxK hxodd
            w.1).mp w.2⟩
        left_inv := by intro v; ext; simp
        right_inv := by intro w; ext; simp }
  have hcard_range : Nat.card ↥f.range =
      2 ^ Module.finrank (ZMod 2) (fixW (D := D) h x) := by
    rw [hrange, hcard_map_fixW, hcard_fixW]
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hkercard, hcard_range] at hmul
  rw [← hmul, mul_comm]

theorem mul_sigma2_inv_mem_K (σ₂ : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    sigma1Nine (z := z) D * σ₂⁻¹ ∈ K D := by
  rw [K, Subgroup.mem_centralizer_singleton_iff]
  exact ((Commute.refl (sigma1Nine (z := z) D)).mul_right hcomm.inv_right).symm.eq

theorem mul_sigma2_mem_K (σ₂ : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    sigma1Nine (z := z) D * σ₂ ∈ K D := by
  rw [K, Subgroup.mem_centralizer_singleton_iff]
  exact ((Commute.refl (sigma1Nine (z := z) D)).mul_right hcomm).symm.eq

theorem odd_orderOf_mul_sigma2_inv (σ₂ : ↥(H z))
    (hσ2ord : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    Odd (orderOf (sigma1Nine (z := z) D * σ₂⁻¹)) := by
  have hσ1cube : (sigma1Nine (z := z) D) ^ 3 = 1 := by
    rw [← sigma1Nine_order (z := z) D]
    exact pow_orderOf_eq_one _
  have hσ2cube : σ₂ ^ 3 = 1 := by
    rw [← hσ2ord]
    exact pow_orderOf_eq_one _
  have h3 : (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1 := by
    rw [hcomm.inv_right.mul_pow 3, hσ1cube, inv_pow, hσ2cube, inv_one, mul_one]
  have hdvd : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> norm_num

theorem odd_orderOf_mul_sigma2 (σ₂ : ↥(H z))
    (hσ2ord : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    Odd (orderOf (sigma1Nine (z := z) D * σ₂)) := by
  have hσ1cube : (sigma1Nine (z := z) D) ^ 3 = 1 := by
    rw [← sigma1Nine_order (z := z) D]
    exact pow_orderOf_eq_one _
  have hσ2cube : σ₂ ^ 3 = 1 := by
    rw [← hσ2ord]
    exact pow_orderOf_eq_one _
  have h3 : (sigma1Nine (z := z) D * σ₂) ^ 3 = 1 := by
    rw [hcomm.mul_pow 3, hσ1cube, hσ2cube, mul_one]
  have hdvd : orderOf (sigma1Nine (z := z) D * σ₂) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> norm_num

theorem card_CJcomm_sigma1sigma2inv_eq_eight_of_conj (h : Tim79a.ParrottHyp z)
    (σ₂ : ↥(H z)) (g : ↥(H z)) (x : ↥(O3H D))
    (hx : x ∉ Subgroup.zpowers
      (⟨sigma1Nine (z := z) D, sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D)))
    (hgx : g * (x : ↥(H z)) * g⁻¹ = sigma1Nine (z := z) D * σ₂⁻¹)
    (hnormg : ∀ p : G,
      p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ↔
        (g : G) * p * (g : G)⁻¹ ∈
          ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    Nat.card ↥(CJcomm (z := z) (D := D)
      (sigma1Nine (z := z) D * σ₂⁻¹)) = 8 := by
  calc Nat.card ↥(CJcomm (z := z) (D := D) (sigma1Nine (z := z) D * σ₂⁻¹))
      = Nat.card ↥(CJcomm (z := z) (D := D) (g * (x : ↥(H z)) * g⁻¹)) := by
          rw [← hgx]
    _ = Nat.card ↥(CJcomm (z := z) (D := D) (x : ↥(H z))) :=
        card_CJcomm_conj (z := z) (D := D) g (x : ↥(H z)) hnormg
    _ = 8 := card_CJcomm_eq_eight_of_O3H (z := z) (D := D) h x hx

end CFSG.RankThree.GF2n.Parrott
