module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

private lemma plh_base_of_flag {D : TData K} {p L H : Submodule K (Fin 4 → K)}
    (hh : AdmCh (AdmT D) p L H) :
    IsFlag p L H ∧ H ⊓ Vsub 4 1 = ⊥ ∧ BFl (p.map tailProj) (L.map tailProj) ∧
      D.okL (p.map tailProj) (L.map tailProj) := by
  obtain ⟨hflag, hH, hok⟩ := hh
  have hpV : p ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    calc p ⊓ Vsub 4 1 ≤ H ⊓ Vsub 4 1 := inf_le_inf_right _ (hflag.pL.trans hflag.LH)
      _ = ⊥ := hH
  have hLV : L ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    calc L ⊓ Vsub 4 1 ≤ H ⊓ Vsub 4 1 := inf_le_inf_right _ hflag.LH
      _ = ⊥ := hH
  refine ⟨hflag, hH, ⟨Submodule.map_mono hflag.pL, ?_, ?_, ?_⟩, hok⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro v _
    exact tailProj_mem v
  · rw [finrank_map_tailProj hpV, hflag.p1]
  · rw [finrank_map_tailProj hLV, hflag.L2]

private lemma plh_point_data {D : TData K} {u : Submodule K (Fin 4 → K)}
    (hu : ∃ L H, AdmCh (AdmT D) u L H) :
    finrank K u = 1 ∧ u ⊓ Vsub 4 1 = ⊥ ∧ BPt (u.map tailProj) ∧
      ∃ L, BFl (u.map tailProj) L ∧ D.okL (u.map tailProj) L := by
  obtain ⟨L, H, hch⟩ := hu
  obtain ⟨hflag, hH, hB, hok⟩ := plh_base_of_flag hch
  have huV : u ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    calc u ⊓ Vsub 4 1 ≤ H ⊓ Vsub 4 1 := inf_le_inf_right _ (hflag.pL.trans hflag.LH)
      _ = ⊥ := hH
  exact ⟨hflag.p1, huV, ⟨hB.1.trans hB.2.1, hB.2.2.1⟩, ⟨L.map tailProj, hB, hok⟩⟩

private lemma plh_adj_base {D : TData K} {x y : Submodule K (Fin 4 → K)}
    (hxy : AdmAdj (AdmT D) x y) : BAdj D (x.map tailProj) (y.map tailProj) := by
  obtain ⟨hne, L, H, hxch, hych⟩ := hxy
  obtain ⟨hxf, hxH, -, hxok⟩ := plh_base_of_flag hxch
  obtain ⟨hyf, -, -, hyok⟩ := plh_base_of_flag hych
  have hLV : L ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    calc L ⊓ Vsub 4 1 ≤ H ⊓ Vsub 4 1 := inf_le_inf_right _ hxf.LH
      _ = ⊥ := hxH
  have hxysup : x ⊔ y = L := by
    have h2 : finrank K ↥(x ⊔ y) = 2 := finrank_sup_of_ne_pts hxf.p1 hyf.p1 hne
    exact Submodule.eq_of_le_of_finrank_eq (sup_le hxf.pL hyf.pL) (by rw [h2, hxf.L2])
  have hsup' : x.map tailProj ⊔ y.map tailProj = L.map tailProj := by
    rw [← map_tailProj_sup, hxysup]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hne (map_tailProj_inj hLV hxf.pL hyf.pL h)
  · rw [hsup']; exact hxok
  · rw [hsup']; exact hyok

private lemma plh_lift {D : TData K} {u t : Submodule K (Fin 4 → K)}
    (hu1 : finrank K u = 1) (huV : u ⊓ Vsub 4 1 = ⊥) (ht : BPt t)
    (hb : BAdj D (u.map tailProj) t) : AdmAdj (AdmT D) u t := by
  obtain ⟨htne, hoku, hokt⟩ := hb
  obtain ⟨htV, ht1⟩ := ht
  have hu'1 : finrank K (u.map tailProj) = 1 := by
    rw [finrank_map_tailProj huV, hu1]
  have htmap : t.map tailProj = t := map_tailProj_of_le htV
  have hsupmap : (u ⊔ t).map tailProj = u.map tailProj ⊔ t := by
    rw [map_tailProj_sup, htmap]
  have hsup2 : finrank K ↥(u.map tailProj ⊔ t) = 2 :=
    finrank_sup_of_ne_pts hu'1 ht1 htne
  have hle2 : finrank K ↥(u ⊔ t) ≤ 2 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq u t
    rw [hu1, ht1] at hd
    omega
  have hLfin : finrank K ↥(u ⊔ t) = 2 := by
    have hle : finrank K ((u ⊔ t).map tailProj) ≤ finrank K ↥(u ⊔ t) :=
      Submodule.finrank_map_le (tailProj (K := K)) (u ⊔ t)
    rw [hsupmap, hsup2] at hle
    omega
  have hLV : (u ⊔ t) ⊓ Vsub 4 1 = ⊥ := by
    have hdle : finrank K ↥(u ⊔ t) ≤ finrank K ((u ⊔ t).map tailProj) := by
      rw [hsupmap, hsup2, hLfin]
    have hdisj : Disjoint (u ⊔ t) (LinearMap.ker (tailProj (K := K))) :=
      Submodule.disjoint_ker_of_finrank_le (L := u ⊔ t) (tailProj (K := K)) hdle
    rw [ker_tailProj] at hdisj
    exact disjoint_iff.mp hdisj
  have hne : u ≠ t := by
    intro h
    exact htne (by rw [h, htmap])
  obtain ⟨H, hLH, hH3, hHV⟩ := exists_plane_avoiding hLfin hLV
  refine ⟨hne, u ⊔ t, H, ⟨⟨hu1, hLfin, hH3, le_sup_left, hLH⟩, ⟨hHV, ?_⟩⟩,
    ⟨⟨ht1, hLfin, hH3, le_sup_right, hLH⟩, ⟨hHV, ?_⟩⟩⟩
  · rw [hsupmap]; exact hoku
  · rw [hsupmap, htmap]; exact hokt

theorem clsT_commonNbrW (D : TData K) (h : TBase D) : AdmCommonNbrW (AdmT D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨hu1, huV, -, huL⟩ := plh_point_data hu
    obtain ⟨hv1, hvV, -, hvL⟩ := plh_point_data hv
    obtain ⟨t, ht, htu, htv⟩ := h.nbr2 (u.map tailProj) (v.map tailProj) huL hvL
    exact ⟨t, plh_lift hu1 huV ht htu, plh_lift hv1 hvV ht htv⟩
  · intro a b c d hab hbc hcd hda
    have hBab := plh_adj_base hab
    have hBbc := plh_adj_base hbc
    have hBcd := plh_adj_base hcd
    have hBda := plh_adj_base hda
    obtain ⟨-, La, Ha, hach, -⟩ := hab
    obtain ⟨-, Lb, Hb, hbch, -⟩ := hbc
    obtain ⟨-, Lc, Hc, hcch, -⟩ := hcd
    obtain ⟨-, Ld, Hd, hdch, -⟩ := hda
    obtain ⟨ha1, haV, haP, -⟩ := plh_point_data ⟨La, Ha, hach⟩
    obtain ⟨hb1, hbV, hbP, -⟩ := plh_point_data ⟨Lb, Hb, hbch⟩
    obtain ⟨hc1, hcV, hcP, -⟩ := plh_point_data ⟨Lc, Hc, hcch⟩
    obtain ⟨hd1, hdV, hdP, -⟩ := plh_point_data ⟨Ld, Hd, hdch⟩
    obtain ⟨t, ht, hta, htb, htc, htd⟩ :=
      h.nbr4 (a.map tailProj) (b.map tailProj) (c.map tailProj) (d.map tailProj) haP hbP hcP hdP
        hBab hBbc hBcd hBda
    exact ⟨t, plh_lift ha1 haV ht hta, plh_lift hb1 hbV ht htb,
      plh_lift hc1 hcV ht htc, plh_lift hd1 hdV ht htd⟩
  · intro u c d hu hcd
    obtain ⟨hu1, huV, -, huL⟩ := plh_point_data hu
    have hBcd := plh_adj_base hcd
    obtain ⟨-, Lc, Hc, hcch, hdch⟩ := hcd
    obtain ⟨hc1, hcV, hcP, -⟩ := plh_point_data ⟨Lc, Hc, hcch⟩
    obtain ⟨hd1, hdV, hdP, -⟩ := plh_point_data ⟨Lc, Hc, hdch⟩
    obtain ⟨t, ht, htu, htc, htd⟩ :=
      h.nbr3 (u.map tailProj) (c.map tailProj) (d.map tailProj) huL hcP hdP hBcd
    exact ⟨t, plh_lift hu1 huV ht htu, plh_lift hc1 hcV ht htc, plh_lift hd1 hdV ht htd⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
