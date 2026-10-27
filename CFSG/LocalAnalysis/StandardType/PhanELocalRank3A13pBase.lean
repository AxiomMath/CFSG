module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13pDict
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13cNonrat
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13pVec

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem D13p_link (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ p L, BFl p L → (D13p (K := K) f).okL p L →
      ∃ L₂ L₃, L₂ ≠ L₃ ∧ BFl p L₂ ∧ BFl p L₃ ∧ (D13p (K := K) f).okL p L₂ ∧
        (D13p (K := K) f).okL p L₃ := by
  intro p L hpL hok
  have hpL' : p ≤ L ∧ L ≤ Vtail ∧ finrank K p = 1 ∧ finrank K L = 2 := hpL
  obtain ⟨hpLle, hLV, hp1, hLfin⟩ := hpL'
  have hok' : (p ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (p ⊔ Vsub 4 1) = Vsub 4 1 ∧
      (L ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (L ⊔ Vsub 4 1) = Vsub 4 1 := hok
  obtain ⟨hokp, hokL⟩ := hok'
  have hp_pt : BPt p := ⟨le_trans hpLle hLV, hp1⟩
  obtain ⟨x, hx0, hx_ne, hp_eq⟩ := exists_vec_of_BPt hp_pt
  have hnot_Lp : ¬ L ≤ p := by
    intro hle
    have h21 : (2 : ℕ) ≤ 1 := by
      rw [← hLfin, ← hp1]
      exact Submodule.finrank_mono hle
    omega
  obtain ⟨w₀, hw₀L, hw₀p⟩ := Set.not_subset.mp hnot_Lp
  have hw₀_ne : w₀ ≠ 0 := fun h => hw₀p (h ▸ Submodule.zero_mem p)
  have hw₀V : w₀ ∈ Vtail := hLV hw₀L
  have hne : Submodule.span K {x} ≠ Submodule.span K {w₀} := by
    intro heq
    apply hw₀p
    rw [hp_eq, heq]
    exact Submodule.mem_span_singleton_self w₀
  have hsup_le_L : Submodule.span K {x} ⊔ Submodule.span K {w₀} ≤ L :=
    sup_le (hp_eq ▸ hpLle)
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw₀L))
  have hfin_pair : finrank K ↥(Submodule.span K {x} ⊔ Submodule.span K {w₀}) = 2 :=
    finrank_sup_of_ne_pts (finrank_span_singleton hx_ne) (finrank_span_singleton hw₀_ne) hne
  have hL_eq : L = Submodule.span K {x} ⊔ Submodule.span K {w₀} :=
    (Submodule.eq_of_le_of_finrank_eq hsup_le_L (by rw [hfin_pair, hLfin])).symm
  have hw₀0 : w₀ 0 = 0 := by simpa [Vtail] using hw₀V
  have hax : Aniso f x := by
    have h := hokp
    rw [hp_eq] at h
    exact (okL_pt_iff (K := K) (f := f) hx0 hx_ne).mp h
  have hgw : gram f x w₀ ≠ 0 :=
    (okL_line_iff (K := K) (f := f) hK hx0 hw₀0 hx_ne hw₀_ne hne).mp (by rwa [hL_eq] at hokL)
  have hVtail_not_le : ¬ (Vtail : Submodule K (Fin 4 → K)) ≤ L := by
    intro hle
    have h32 : (3 : ℕ) ≤ 2 := by
      rw [← finrank_Vtail (K := K), ← hLfin]
      exact Submodule.finrank_mono hle
    omega
  obtain ⟨r, hrV, hrL⟩ := Set.not_subset.mp hVtail_not_le
  obtain ⟨s, hgs⟩ := link_vec (K := K) (f := f) hK hq (p := x) (w₀ := w₀) (r := r) hgw
  let L₃ : Submodule K (Fin 4 → K) := Submodule.span K {x} ⊔ Submodule.span K {s • w₀ + r}
  have hL₃_def : L₃ = Submodule.span K {x} ⊔ Submodule.span K {s • w₀ + r} := rfl
  have hzV : s • w₀ + r ∈ Vtail :=
    (Vtail : Submodule K (Fin 4 → K)).add_mem
      ((Vtail : Submodule K (Fin 4 → K)).smul_mem s hw₀V) hrV
  have hz0 : (s • w₀ + r) 0 = 0 := by simpa [Vtail] using hzV
  have hz_ne : s • w₀ + r ≠ 0 := by
    intro h
    exact hgs (by rw [h]; exact gram_zero_right (f := f) x)
  have hne' : Submodule.span K {x} ≠ Submodule.span K {s • w₀ + r} :=
    span_ne_of_gram_ne (f := f) hgs
  have hL₃_ne : L ≠ L₃ := by
    intro hEq
    have hmem_L₃ : s • w₀ + r ∈ L₃ :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self (s • w₀ + r))
    have hmem_L : s • w₀ + r ∈ L := hEq ▸ hmem_L₃
    exact hrL (by
      have := L.sub_mem hmem_L (L.smul_mem s hw₀L)
      simpa using this)
  have hL₃_Vtail : L₃ ≤ Vtail :=
    sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by simpa [Vtail] using hx0)))
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzV))
  have hp_le_L₃ : p ≤ L₃ := hp_eq.le.trans le_sup_left
  have hL₃_fin : finrank K ↥L₃ = 2 :=
    finrank_sup_of_ne_pts (finrank_span_singleton hx_ne) (finrank_span_singleton hz_ne) hne'
  have hbf3 : BFl p L₃ := ⟨hp_le_L₃, hL₃_Vtail, hp1, hL₃_fin⟩
  have hokp' : (p ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (p ⊔ Vsub 4 1) = Vsub 4 1 := hokp
  have hokL₃ : (D13p (K := K) f).okL p L₃ := by
    have hline : (L₃ ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (L₃ ⊔ Vsub 4 1) = Vsub 4 1 :=
      (okL_line_iff (K := K) (f := f) hK hx0 hz0 hx_ne hz_ne hne').mpr hgs
    have h' : (p ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (p ⊔ Vsub 4 1) = Vsub 4 1 ∧
        (L₃ ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (L₃ ⊔ Vsub 4 1) = Vsub 4 1 := ⟨hokp', hline⟩
    exact h'
  exact ⟨L, L₃, hL₃_ne, hpL, hbf3, hok, hokL₃⟩

theorem D13p_nbr2 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ u v, (∃ L, BFl u L ∧ (D13p (K := K) f).okL u L) →
      (∃ L, BFl v L ∧ (D13p (K := K) f).okL v L) →
      ∃ t, BPt t ∧ BAdj (D13p (K := K) f) u t ∧ BAdj (D13p (K := K) f) v t := by
  intro u v hu hv
  obtain ⟨Lu, huLu, hoku⟩ := hu
  obtain ⟨Lv, hvLv, hokv⟩ := hv
  have huL : u ≤ Lu ∧ Lu ≤ Vtail ∧ finrank K u = 1 ∧ finrank K Lu = 2 := huLu
  have hvL : v ≤ Lv ∧ Lv ≤ Vtail ∧ finrank K v = 1 ∧ finrank K Lv = 2 := hvLv
  have hu_pt : BPt u := ⟨le_trans huL.1 huL.2.1, huL.2.2.1⟩
  have hv_pt : BPt v := ⟨le_trans hvL.1 hvL.2.1, hvL.2.2.1⟩
  obtain ⟨xu, hxu0, hxu_ne, hxu_eq⟩ := exists_vec_of_BPt hu_pt
  obtain ⟨xv, hxv0, hxv_ne, hxv_eq⟩ := exists_vec_of_BPt hv_pt
  have hoku' : (u ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (u ⊔ Vsub 4 1) = Vsub 4 1 ∧
      (Lu ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (Lu ⊔ Vsub 4 1) = Vsub 4 1 := hoku
  have hokv' : (v ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (v ⊔ Vsub 4 1) = Vsub 4 1 ∧
      (Lv ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (Lv ⊔ Vsub 4 1) = Vsub 4 1 := hokv
  have haxu : Aniso f xu := by
    rw [hxu_eq] at hoku'
    exact (okL_pt_iff (K := K) (f := f) hxu0 hxu_ne).mp hoku'.1
  have haxv : Aniso f xv := by
    rw [hxv_eq] at hokv'
    exact (okL_pt_iff (K := K) (f := f) hxv0 hxv_ne).mp hokv'.1
  obtain ⟨t, ht0, ht_aniso, hgut, hgvt⟩ :=
    nbr2_vec (K := K) (f := f) hK hq (u := xu) (v := xv) hxu0 haxu haxv
  have ht_ne : t ≠ 0 := ne_zero_of_aniso (f := f) ht_aniso
  refine ⟨Submodule.span K {t}, ?_, ?_, ?_⟩
  · exact ⟨Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by simpa [Vtail] using ht0)),
      finrank_span_singleton ht_ne⟩
  · rw [hxu_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hxu0 ht0 hxu_ne ht_ne).mpr
      ⟨haxu, ht_aniso, hgut⟩
  · rw [hxv_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hxv0 ht0 hxv_ne ht_ne).mpr
      ⟨haxv, ht_aniso, hgvt⟩

theorem D13p_nbr3 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ u c d, (∃ L, BFl u L ∧ (D13p (K := K) f).okL u L) → BPt c → BPt d →
      BAdj (D13p (K := K) f) c d →
      ∃ t, BPt t ∧ BAdj (D13p (K := K) f) u t ∧ BAdj (D13p (K := K) f) c t ∧
        BAdj (D13p (K := K) f) d t := by
  intro u c d hu hc hd hcd
  obtain ⟨Lu, huLu, hoku⟩ := hu
  have huL : u ≤ Lu ∧ Lu ≤ Vtail ∧ finrank K u = 1 ∧ finrank K Lu = 2 := huLu
  have hu_pt : BPt u := ⟨le_trans huL.1 huL.2.1, huL.2.2.1⟩
  obtain ⟨xu, hxu0, hxu_ne, hxu_eq⟩ := exists_vec_of_BPt hu_pt
  obtain ⟨xc, hxc0, hxc_ne, hxc_eq⟩ := exists_vec_of_BPt hc
  obtain ⟨xd, hxd0, hxd_ne, hxd_eq⟩ := exists_vec_of_BPt hd
  have hoku' : (u ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (u ⊔ Vsub 4 1) = Vsub 4 1 ∧
      (Lu ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (Lu ⊔ Vsub 4 1) = Vsub 4 1 := hoku
  have haxu : Aniso f xu := by
    rw [hxu_eq] at hoku'
    exact (okL_pt_iff (K := K) (f := f) hxu0 hxu_ne).mp hoku'.1
  have hcd' := (bAdj_span_iff (K := K) (f := f) hK hxc0 hxd0 hxc_ne hxd_ne).mp
    (by rwa [hxc_eq, hxd_eq] at hcd)
  have haxc : Aniso f xc := hcd'.1
  have hgcd : gram f xc xd ≠ 0 := hcd'.2.2
  obtain ⟨t, ht0, ht_aniso, hgut, hgct, hgdt⟩ :=
    nbr3_vec (K := K) (f := f) hK hq (u := xu) (c := xc) (d := xd)
      hxc0 hxd0 haxu haxc hgcd
  have ht_ne : t ≠ 0 := ne_zero_of_aniso (f := f) ht_aniso
  refine ⟨Submodule.span K {t}, ?_, ?_, ?_, ?_⟩
  · exact ⟨Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by simpa [Vtail] using ht0)),
      finrank_span_singleton ht_ne⟩
  · rw [hxu_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hxu0 ht0 hxu_ne ht_ne).mpr
      ⟨haxu, ht_aniso, hgut⟩
  · rw [hxc_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hxc0 ht0 hxc_ne ht_ne).mpr
      ⟨haxc, ht_aniso, hgct⟩
  · rw [hxd_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hxd0 ht0 hxd_ne ht_ne).mpr
      ⟨hcd'.2.1, ht_aniso, hgdt⟩

theorem D13p_nbr4 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ a b c d, BPt a → BPt b → BPt c → BPt d → BAdj (D13p (K := K) f) a b →
      BAdj (D13p (K := K) f) b c → BAdj (D13p (K := K) f) c d → BAdj (D13p (K := K) f) d a →
      ¬ BAdj (D13p (K := K) f) a c → ¬ BAdj (D13p (K := K) f) b d →
      ∃ t, BPt t ∧ BAdj (D13p (K := K) f) a t ∧ BAdj (D13p (K := K) f) b t ∧
        BAdj (D13p (K := K) f) c t ∧ BAdj (D13p (K := K) f) d t := by
  intro a b c d ha hb hc hd hab hbc hcd hda _hnac hnbd
  obtain ⟨xa, ha0, ha_ne, ha_eq⟩ := exists_vec_of_BPt ha
  obtain ⟨xb, hb0, hb_ne, hb_eq⟩ := exists_vec_of_BPt hb
  obtain ⟨xc, hc0, hc_ne, hc_eq⟩ := exists_vec_of_BPt hc
  obtain ⟨xd, hd0, hd_ne, hd_eq⟩ := exists_vec_of_BPt hd
  have hab' := (bAdj_span_iff (K := K) (f := f) hK ha0 hb0 ha_ne hb_ne).mp
    (by rwa [ha_eq, hb_eq] at hab)
  have haxa : Aniso f xa := hab'.1
  have habag : gram f xa xb ≠ 0 := hab'.2.2
  have hbc' := (bAdj_span_iff (K := K) (f := f) hK hb0 hc0 hb_ne hc_ne).mp
    (by rwa [hb_eq, hc_eq] at hbc)
  have hcd' := (bAdj_span_iff (K := K) (f := f) hK hc0 hd0 hc_ne hd_ne).mp
    (by rwa [hc_eq, hd_eq] at hcd)
  have hda' := (bAdj_span_iff (K := K) (f := f) hK hd0 ha0 hd_ne ha_ne).mp
    (by rwa [hd_eq, ha_eq] at hda)
  have hbd0 : gram f xb xd = 0 := by
    by_contra hg
    have hbd : BAdj (D13p (K := K) f) (Submodule.span K {xb}) (Submodule.span K {xd}) :=
      (bAdj_span_iff (K := K) (f := f) hK hb0 hd0 hb_ne hd_ne).mpr
        ⟨hab'.2.1, hcd'.2.1, hg⟩
    exact hnbd (by rwa [← hb_eq, ← hd_eq] at hbd)
  obtain ⟨t, ht0, ht_aniso, hgat, hgbt, hgct, hgdt⟩ :=
    nbr4_vec (K := K) (f := f) hK hq (a := xa) (b := xb) (c := xc) (d := xd)
      ha0 hb0 haxa habag hbc'.2.2 hda'.2.2 hbd0
  have ht_ne : t ≠ 0 := ne_zero_of_aniso (f := f) ht_aniso
  refine ⟨Submodule.span K {t}, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by simpa [Vtail] using ht0)),
      finrank_span_singleton ht_ne⟩
  · rw [ha_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK ha0 ht0 ha_ne ht_ne).mpr
      ⟨haxa, ht_aniso, hgat⟩
  · rw [hb_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hb0 ht0 hb_ne ht_ne).mpr
      ⟨hab'.2.1, ht_aniso, hgbt⟩
  · rw [hc_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hc0 ht0 hc_ne ht_ne).mpr
      ⟨hbc'.2.1, ht_aniso, hgct⟩
  · rw [hd_eq]
    exact (bAdj_span_iff (K := K) (f := f) hK hd0 ht0 hd_ne ht_ne).mpr
      ⟨hcd'.2.1, ht_aniso, hgdt⟩

theorem D13p_cone (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∀ x y z, BPt x → BPt y → BPt z → BAdj (D13p (K := K) f) x y → BAdj (D13p (K := K) f) y z →
      BAdj (D13p (K := K) f) z x → finrank K ↥(x ⊔ y ⊔ z) ≠ 3 →
      ∃ t, BPt t ∧ BAdj (D13p (K := K) f) x t ∧ BAdj (D13p (K := K) f) y t ∧
        BAdj (D13p (K := K) f) z t ∧ finrank K ↥(x ⊔ y ⊔ t) = 3 ∧ finrank K ↥(y ⊔ z ⊔ t) = 3 ∧
        finrank K ↥(z ⊔ x ⊔ t) = 3 := by
  intro x y z hx hy hz hxy hyz hzx hdim
  have hx' : x ≤ Vtail ∧ finrank K x = 1 := hx
  have hy' : y ≤ Vtail ∧ finrank K y = 1 := hy
  have hz' : z ≤ Vtail ∧ finrank K z = 1 := hz
  obtain ⟨xv, hxv0, hxv_ne, hxv_eq⟩ := exists_vec_of_BPt hx
  obtain ⟨yv, hyv0, hyv_ne, hyv_eq⟩ := exists_vec_of_BPt hy
  obtain ⟨zv, hzv0, hzv_ne, hzv_eq⟩ := exists_vec_of_BPt hz
  have hxy' := (bAdj_span_iff (K := K) (f := f) hK hxv0 hyv0 hxv_ne hyv_ne).mp
    (by rwa [hxv_eq, hyv_eq] at hxy)
  obtain ⟨haxv, hayv, hgxy⟩ := hxy'
  have hyz' := (bAdj_span_iff (K := K) (f := f) hK hyv0 hzv0 hyv_ne hzv_ne).mp
    (by rwa [hyv_eq, hzv_eq] at hyz)
  obtain ⟨-, hazv, -⟩ := hyz'
  have hxy_ne : x ≠ y := hxy.1
  have hyz2 : finrank K ↥(y ⊔ z) = 2 := finrank_sup_of_ne_pts hy'.2 hz'.2 hyz.1
  have hxy2 : finrank K ↥(x ⊔ y) = 2 := finrank_sup_of_ne_pts hx'.2 hy'.2 hxy_ne
  have hxyz3_le : finrank K ↥(x ⊔ y ⊔ z) ≤ 3 := by
    have hsub : (x ⊔ y ⊔ z) ≤ (Vtail : Submodule K (Fin 4 → K)) :=
      sup_le (sup_le hx'.1 hy'.1) hz'.1
    have := Submodule.finrank_mono hsub
    rwa [finrank_Vtail (K := K)] at this
  have hxyz2 : finrank K ↥(x ⊔ y ⊔ z) = 2 := by
    have h2le : 2 ≤ finrank K ↥(x ⊔ y ⊔ z) := by
      have := Submodule.finrank_mono (le_sup_left : x ⊔ y ≤ x ⊔ y ⊔ z)
      rwa [hxy2] at this
    omega
  have hxyz_eq : x ⊔ y ⊔ z = x ⊔ y :=
    (Submodule.eq_of_le_of_finrank_eq le_sup_left (by rw [hxyz2, hxy2])).symm
  have hz_le : z ≤ x ⊔ y := by
    rw [← hxyz_eq]
    exact le_sup_right
  have hzv_span : zv ∈ Submodule.span K {xv, yv} := by
    rw [Submodule.span_insert]
    rw [← hxv_eq, ← hyv_eq]
    exact hz_le (by rw [hzv_eq]; exact Submodule.mem_span_singleton_self zv)
  obtain ⟨hp_aniso, hgxp, hgyp, hgzp, hp_notin⟩ :=
    cone_vec (K := K) (f := f) (x := xv) (y := yv) (z := zv) hK haxv hayv hazv hgxy hzv_span
  have hp_ne : polar f xv yv ≠ 0 := ne_zero_of_aniso (f := f) hp_aniso
  have ht_pt : BPt (Submodule.span K {polar f xv yv}) := by
    refine ⟨Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_),
      finrank_span_singleton hp_ne⟩
    show polar f xv yv 0 = 0
    exact polar_zero (f := f) xv yv
  have hxt : BAdj (D13p (K := K) f) x (Submodule.span K {polar f xv yv}) := by
    rw [hxv_eq]
    exact (bAdj_span_iff (K := K) (f := f) (x := xv) (y := polar f xv yv) hK hxv0
      (polar_zero (f := f) xv yv) hxv_ne hp_ne).mpr ⟨haxv, hp_aniso, hgxp⟩
  have hyt : BAdj (D13p (K := K) f) y (Submodule.span K {polar f xv yv}) := by
    rw [hyv_eq]
    exact (bAdj_span_iff (K := K) (f := f) (x := yv) (y := polar f xv yv) hK hyv0
      (polar_zero (f := f) xv yv) hyv_ne hp_ne).mpr ⟨hayv, hp_aniso, hgyp⟩
  have hzt : BAdj (D13p (K := K) f) z (Submodule.span K {polar f xv yv}) := by
    rw [hzv_eq]
    exact (bAdj_span_iff (K := K) (f := f) (x := zv) (y := polar f xv yv) hK hzv0
      (polar_zero (f := f) xv yv) hzv_ne hp_ne).mpr ⟨hazv, hp_aniso, hgzp⟩
  have ht_notle : ¬ Submodule.span K {polar f xv yv} ≤ x ⊔ y := by
    intro hle
    have hp_in : polar f xv yv ∈ x ⊔ y := hle (Submodule.mem_span_singleton_self _)
    rw [hxv_eq, hyv_eq] at hp_in
    apply hp_notin
    rwa [← Submodule.span_insert] at hp_in
  have h3a : finrank K ↥(x ⊔ y ⊔ Submodule.span K {polar f xv yv}) = 3 :=
    finrank_sup_sup_eq_three (a := x) (b := y) (t := Submodule.span K {polar f xv yv})
      hx hy ht_pt hxy_ne ht_notle
  have hyz_eq : y ⊔ z = x ⊔ y :=
    Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_right hz_le) (by rw [hyz2, hxy2])
  have hzx_eq : z ⊔ x = x ⊔ y := by
    have hzx2 : finrank K ↥(z ⊔ x) = 2 := finrank_sup_of_ne_pts hz'.2 hx'.2 hzx.1
    exact Submodule.eq_of_le_of_finrank_eq (sup_le hz_le le_sup_left) (by rw [hzx2, hxy2])
  exact ⟨Submodule.span K {polar f xv yv}, ht_pt, hxt, hyt, hzt, h3a,
    by rw [hyz_eq]; exact h3a, by rw [hzx_eq]; exact h3a⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
