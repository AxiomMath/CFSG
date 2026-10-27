module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

private theorem pld_map_le_Vtail (S : Submodule K (Fin 4 → K)) :
    S.map tailProj ≤ (Vtail : Submodule K (Fin 4 → K)) := by
  rintro _ ⟨v, -, rfl⟩
  exact tailProj_mem v

private theorem pld_inf_Vsub_eq_bot_of_finrank_map_eq {S : Submodule K (Fin 4 → K)}
    (h : finrank K (S.map tailProj) = finrank K S) : S ⊓ Vsub 4 1 = ⊥ := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (tailProj.domRestrict S)
  rw [LinearMap.range_domRestrict] at hrk
  have hker : finrank K (LinearMap.ker (tailProj.domRestrict S)) = 0 := by
    rw [h] at hrk
    omega
  have hmapker : (LinearMap.ker (tailProj.domRestrict S)).map S.subtype = S ⊓ Vsub 4 1 := by
    rw [LinearMap.ker_domRestrict, ker_tailProj, Submodule.map_comap_subtype]
  apply Submodule.finrank_eq_zero.mp
  rw [← hmapker, Submodule.finrank_map_subtype_eq]
  exact hker

private theorem pld_admCh_of (D : TData K) {p L H : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hL : finrank K L = 2) (hH : finrank K H = 3)
    (hpL : p ≤ L) (hLH : L ≤ H) (hH1 : H ⊓ Vsub 4 1 = ⊥)
    (hok : D.okL (p.map tailProj) (L.map tailProj)) : AdmCh (AdmT D) p L H :=
  ⟨⟨hp, hL, hH, hpL, hLH⟩, hH1, hok⟩

private theorem pld_adm_point (D : TData K) {a b : Submodule K (Fin 4 → K)}
    (hab : AdmAdj (AdmT D) a b) : finrank K a = 1 ∧ a ⊓ Vsub 4 1 = ⊥ := by
  obtain ⟨-, L, H, ha, -⟩ := hab
  obtain ⟨haFlag, haAdm⟩ := ha
  obtain ⟨ha1, -, -, haL, hLH⟩ := haFlag
  obtain ⟨hHV, -⟩ := haAdm
  have hLV : L ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hvL, hvV⟩ := Submodule.mem_inf.mp hv
    have : v ∈ H ⊓ Vsub 4 1 := ⟨hLH hvL, hvV⟩
    rw [hHV] at this
    simpa using this
  refine ⟨ha1, ?_⟩
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  obtain ⟨hva, hvV⟩ := Submodule.mem_inf.mp hv
  have : v ∈ L ⊓ Vsub 4 1 := ⟨haL hva, hvV⟩
  rw [hLV] at this
  simpa using this

private theorem pld_bpt_of_adj (D : TData K) {a b : Submodule K (Fin 4 → K)}
    (hab : AdmAdj (AdmT D) a b) : BPt (a.map tailProj) := by
  obtain ⟨ha1, haV⟩ := pld_adm_point D hab
  exact ⟨pld_map_le_Vtail a, by rw [finrank_map_tailProj haV, ha1]⟩

private theorem pld_badj_of_adj (D : TData K) {a b : Submodule K (Fin 4 → K)}
    (hab : AdmAdj (AdmT D) a b) : BAdj D (a.map tailProj) (b.map tailProj) := by
  obtain ⟨habne, L, H, ha, hb⟩ := hab
  obtain ⟨haFlag, haAdm⟩ := ha
  obtain ⟨hbFlag, hbAdm⟩ := hb
  obtain ⟨ha1, hL2, -, haL, hLH⟩ := haFlag
  obtain ⟨hb1, -, -, hbL, -⟩ := hbFlag
  obtain ⟨hHV, haok⟩ := haAdm
  obtain ⟨-, hbok⟩ := hbAdm
  have hLV : L ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hvL, hvV⟩ := Submodule.mem_inf.mp hv
    have : v ∈ H ⊓ Vsub 4 1 := ⟨hLH hvL, hvV⟩
    rw [hHV] at this
    simpa using this
  have hsup : a ⊔ b = L := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le haL hbL)
    rw [finrank_sup_of_ne_pts ha1 hb1 habne, hL2]
  have hne' : a.map tailProj ≠ b.map tailProj := by
    intro hmap
    exact habne (map_tailProj_inj hLV haL hbL hmap)
  have hsup' : a.map tailProj ⊔ b.map tailProj = L.map tailProj := by
    rw [← map_tailProj_sup, hsup]
  refine ⟨hne', ?_, ?_⟩
  · rw [hsup']; exact haok
  · rw [hsup']; exact hbok

private theorem pld_plane_finrank_inf {a b t : Submodule K (Fin 4 → K)}
    (ha1 : finrank K a = 1) (hb1 : finrank K b = 1) (ht1 : finrank K t = 1)
    (hab : a ≠ b) (htV : t ≤ Vtail)
    (h3 : finrank K ↥(a.map tailProj ⊔ b.map tailProj ⊔ t) = 3) :
    finrank K ↥(a ⊔ b ⊔ t) = 3 ∧ (a ⊔ b ⊔ t) ⊓ Vsub 4 1 = ⊥ := by
  have hab2 : finrank K ↥(a ⊔ b) = 2 := finrank_sup_of_ne_pts ha1 hb1 hab
  have hsupdim := Submodule.finrank_sup_add_finrank_inf_eq (a ⊔ b) t
  rw [hab2, ht1] at hsupdim
  have hle : finrank K ↥(a ⊔ b ⊔ t) ≤ 3 := by omega
  have hmap : (a ⊔ b ⊔ t).map tailProj = a.map tailProj ⊔ b.map tailProj ⊔ t := by
    rw [map_tailProj_sup (a ⊔ b) t, map_tailProj_sup a b, map_tailProj_of_le htV]
  have hge : 3 ≤ finrank K ↥(a ⊔ b ⊔ t) := by
    have hml := Submodule.finrank_map_le tailProj (a ⊔ b ⊔ t)
    rw [hmap, h3] at hml
    exact hml
  have hH : finrank K ↥(a ⊔ b ⊔ t) = 3 := le_antisymm hle hge
  refine ⟨hH, ?_⟩
  apply pld_inf_Vsub_eq_bot_of_finrank_map_eq
  rw [hmap, h3, hH]

private lemma pld_base_of_flag {D : TData K} {p L H : Submodule K (Fin 4 → K)}
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

private lemma pld_point_data {D : TData K} {u : Submodule K (Fin 4 → K)}
    (hu : ∃ L H, AdmCh (AdmT D) u L H) :
    finrank K u = 1 ∧ u ⊓ Vsub 4 1 = ⊥ ∧ BPt (u.map tailProj) ∧
      ∃ L, BFl (u.map tailProj) L ∧ D.okL (u.map tailProj) L := by
  obtain ⟨L, H, hch⟩ := hu
  obtain ⟨hflag, hH, hB, hok⟩ := pld_base_of_flag hch
  have huV : u ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    calc u ⊓ Vsub 4 1 ≤ H ⊓ Vsub 4 1 := inf_le_inf_right _ (hflag.pL.trans hflag.LH)
      _ = ⊥ := hH
  exact ⟨hflag.p1, huV, ⟨hB.1.trans hB.2.1, hB.2.2.1⟩, ⟨L.map tailProj, hB, hok⟩⟩

private lemma pld_adj_base {D : TData K} {x y : Submodule K (Fin 4 → K)}
    (hxy : AdmAdj (AdmT D) x y) : BAdj D (x.map tailProj) (y.map tailProj) := by
  obtain ⟨hne, L, H, hxch, hych⟩ := hxy
  obtain ⟨hxf, hxH, -, hxok⟩ := pld_base_of_flag hxch
  obtain ⟨hyf, -, -, hyok⟩ := pld_base_of_flag hych
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

private lemma pld_lift {D : TData K} {u t : Submodule K (Fin 4 → K)}
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

private lemma pld_lift_gen {D : TData K} {u t : Submodule K (Fin 4 → K)}
    (hu1 : finrank K u = 1) (huV : u ⊓ Vsub 4 1 = ⊥)
    (ht1 : finrank K t = 1) (htV : t ⊓ Vsub 4 1 = ⊥)
    (hb : BAdj D (u.map tailProj) (t.map tailProj)) : AdmAdj (AdmT D) u t := by
  obtain ⟨htne, hoku, hokt⟩ := hb
  have hu'1 : finrank K (u.map tailProj) = 1 := by
    rw [finrank_map_tailProj huV, hu1]
  have ht'1 : finrank K (t.map tailProj) = 1 := by
    rw [finrank_map_tailProj htV, ht1]
  have hsupmap : (u ⊔ t).map tailProj = u.map tailProj ⊔ t.map tailProj :=
    map_tailProj_sup u t
  have hsup2 : finrank K ↥(u.map tailProj ⊔ t.map tailProj) = 2 :=
    finrank_sup_of_ne_pts hu'1 ht'1 htne
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
    exact htne (by rw [h])
  obtain ⟨H, hLH, hH3, hHV⟩ := exists_plane_avoiding hLfin hLV
  refine ⟨hne, u ⊔ t, H, ⟨⟨hu1, hLfin, hH3, le_sup_left, hLH⟩, ⟨hHV, ?_⟩⟩,
    ⟨⟨ht1, hLfin, hH3, le_sup_right, hLH⟩, ⟨hHV, ?_⟩⟩⟩
  · rw [hsupmap]; exact hoku
  · rw [hsupmap]; exact hokt

private theorem pld_side_data (D : TData K) {a b t : Submodule K (Fin 4 → K)}
    (hab : AdmAdj (AdmT D) a b) (ht : BPt t)
    (hat : BAdj D (a.map tailProj) t) (hbt : BAdj D (b.map tailProj) t)
    (h3 : finrank K ↥(a.map tailProj ⊔ b.map tailProj ⊔ t) = 3) :
    AdmAdj (AdmT D) a t ∧ AdmAdj (AdmT D) b t ∧ AdmPlanar (AdmT D) a b t := by
  obtain ⟨-, haok', hbok'⟩ := pld_badj_of_adj D hab
  obtain ⟨habne, L₀, H₀, ha₀, hb₀⟩ := hab
  obtain ⟨haFlag, haAdm⟩ := ha₀
  obtain ⟨hbFlag, -⟩ := hb₀
  obtain ⟨ha1, -, -, -, hL₀H₀⟩ := haFlag
  obtain ⟨hb1, -, -, -, -⟩ := hbFlag
  obtain ⟨hH₀V, -⟩ := haAdm
  obtain ⟨hbt_ne', hbtok, hbtok'⟩ := hbt
  obtain ⟨hat_ne', hatok, hatok'⟩ := hat
  have htV : t ≤ Vtail := ht.1
  have ht1 : finrank K t = 1 := ht.2
  have hLV : L₀ ⊓ Vsub 4 1 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hvL, hvV⟩ := Submodule.mem_inf.mp hv
    have : v ∈ H₀ ⊓ Vsub 4 1 := ⟨hL₀H₀ hvL, hvV⟩
    rw [hH₀V] at this
    simpa using this
  obtain ⟨hH3, hHV⟩ := pld_plane_finrank_inf ha1 hb1 ht1 habne htV h3
  have hL₁2 : finrank K ↥(a ⊔ b) = 2 := finrank_sup_of_ne_pts ha1 hb1 habne
  have hbt_ne : b ≠ t := by
    intro h
    exact hbt_ne' (by rw [h, map_tailProj_of_le htV])
  have hat_ne : a ≠ t := by
    intro h
    exact hat_ne' (by rw [h, map_tailProj_of_le htV])
  have hL₂2 : finrank K ↥(b ⊔ t) = 2 := finrank_sup_of_ne_pts hb1 ht1 hbt_ne
  have hL₃2 : finrank K ↥(t ⊔ a) = 2 := finrank_sup_of_ne_pts ht1 ha1 (Ne.symm hat_ne)
  have hL₂H : b ⊔ t ≤ a ⊔ b ⊔ t :=
    sup_le (le_trans le_sup_right le_sup_left) le_sup_right
  have hL₃H : t ⊔ a ≤ a ⊔ b ⊔ t :=
    sup_le le_sup_right (le_trans le_sup_left le_sup_left)
  have f1 : AdmCh (AdmT D) a (a ⊔ b) (a ⊔ b ⊔ t) :=
    pld_admCh_of D ha1 hL₁2 hH3 le_sup_left le_sup_left hHV (by
      rw [map_tailProj_sup]; exact haok')
  have f2 : AdmCh (AdmT D) b (a ⊔ b) (a ⊔ b ⊔ t) :=
    pld_admCh_of D hb1 hL₁2 hH3 le_sup_right le_sup_left hHV (by
      rw [map_tailProj_sup]; exact hbok')
  have f3 : AdmCh (AdmT D) b (b ⊔ t) (a ⊔ b ⊔ t) :=
    pld_admCh_of D hb1 hL₂2 hH3 le_sup_left hL₂H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV]; exact hbtok)
  have f4 : AdmCh (AdmT D) t (b ⊔ t) (a ⊔ b ⊔ t) :=
    pld_admCh_of D ht1 hL₂2 hH3 le_sup_right hL₂H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV]; exact hbtok')
  have f5 : AdmCh (AdmT D) t (t ⊔ a) (a ⊔ b ⊔ t) :=
    pld_admCh_of D ht1 hL₃2 hH3 le_sup_left hL₃H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV, sup_comm]
      exact hatok')
  have f6 : AdmCh (AdmT D) a (t ⊔ a) (a ⊔ b ⊔ t) :=
    pld_admCh_of D ha1 hL₃2 hH3 le_sup_right hL₃H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV, sup_comm]
      exact hatok)
  exact ⟨⟨hat_ne, t ⊔ a, a ⊔ b ⊔ t, f6, f5⟩, ⟨hbt_ne, b ⊔ t, a ⊔ b ⊔ t, f3, f4⟩,
    ⟨a ⊔ b ⊔ t, a ⊔ b, b ⊔ t, t ⊔ a, f1, f2, f3, f4, f5, f6⟩⟩

private theorem pld_planar_of_indep (D : TData K) {x y z : Submodule K (Fin 4 → K)}
    (hxy : AdmAdj (AdmT D) x y) (hyz : AdmAdj (AdmT D) y z) (hzx : AdmAdj (AdmT D) z x)
    (h3 : finrank K ↥(x.map tailProj ⊔ y.map tailProj ⊔ z.map tailProj) = 3) :
    AdmPlanar (AdmT D) x y z := by
  obtain ⟨hx1, -⟩ := pld_adm_point D hxy
  obtain ⟨hy1, -⟩ := pld_adm_point D hyz
  obtain ⟨hz1, -⟩ := pld_adm_point D hzx
  have hxy_ne : x ≠ y := hxy.1
  have hyz_ne : y ≠ z := hyz.1
  have hzx_ne : z ≠ x := hzx.1
  have hxy' : BAdj D (x.map tailProj) (y.map tailProj) := pld_badj_of_adj D hxy
  have hyz' : BAdj D (y.map tailProj) (z.map tailProj) := pld_badj_of_adj D hyz
  have hzx' : BAdj D (z.map tailProj) (x.map tailProj) := pld_badj_of_adj D hzx
  have hmap : (x ⊔ y ⊔ z).map tailProj = x.map tailProj ⊔ y.map tailProj ⊔ z.map tailProj := by
    rw [map_tailProj_sup (x ⊔ y) z, map_tailProj_sup x y]
  have hH3 : finrank K ↥(x ⊔ y ⊔ z) = 3 := by
    have hxy2 : finrank K ↥(x ⊔ y) = 2 := finrank_sup_of_ne_pts hx1 hy1 hxy_ne
    have hsupdim := Submodule.finrank_sup_add_finrank_inf_eq (x ⊔ y) z
    rw [hxy2, hz1] at hsupdim
    have hle : finrank K ↥(x ⊔ y ⊔ z) ≤ 3 := by omega
    have hge : 3 ≤ finrank K ↥(x ⊔ y ⊔ z) := by
      have hml := Submodule.finrank_map_le tailProj (x ⊔ y ⊔ z)
      rw [hmap, h3] at hml
      exact hml
    exact le_antisymm hle hge
  have hHV : (x ⊔ y ⊔ z) ⊓ Vsub 4 1 = ⊥ := by
    apply pld_inf_Vsub_eq_bot_of_finrank_map_eq
    rw [hmap, h3, hH3]
  have hLxy2 : finrank K ↥(x ⊔ y) = 2 := finrank_sup_of_ne_pts hx1 hy1 hxy_ne
  have hLyz2 : finrank K ↥(y ⊔ z) = 2 := finrank_sup_of_ne_pts hy1 hz1 hyz_ne
  have hLzx2 : finrank K ↥(z ⊔ x) = 2 := finrank_sup_of_ne_pts hz1 hx1 hzx_ne
  have hLxyH : x ⊔ y ≤ x ⊔ y ⊔ z := le_sup_left
  have hLyzH : y ⊔ z ≤ x ⊔ y ⊔ z :=
    sup_le (le_trans le_sup_right le_sup_left) le_sup_right
  have hLzxH : z ⊔ x ≤ x ⊔ y ⊔ z :=
    sup_le le_sup_right (le_trans le_sup_left le_sup_left)
  have f1 : AdmCh (AdmT D) x (x ⊔ y) (x ⊔ y ⊔ z) :=
    pld_admCh_of D hx1 hLxy2 hH3 le_sup_left hLxyH hHV (by
      rw [map_tailProj_sup]; exact hxy'.2.1)
  have f2 : AdmCh (AdmT D) y (x ⊔ y) (x ⊔ y ⊔ z) :=
    pld_admCh_of D hy1 hLxy2 hH3 le_sup_right hLxyH hHV (by
      rw [map_tailProj_sup]; exact hxy'.2.2)
  have f3 : AdmCh (AdmT D) y (y ⊔ z) (x ⊔ y ⊔ z) :=
    pld_admCh_of D hy1 hLyz2 hH3 le_sup_left hLyzH hHV (by
      rw [map_tailProj_sup]; exact hyz'.2.1)
  have f4 : AdmCh (AdmT D) z (y ⊔ z) (x ⊔ y ⊔ z) :=
    pld_admCh_of D hz1 hLyz2 hH3 le_sup_right hLyzH hHV (by
      rw [map_tailProj_sup]; exact hyz'.2.2)
  have f5 : AdmCh (AdmT D) z (z ⊔ x) (x ⊔ y ⊔ z) :=
    pld_admCh_of D hz1 hLzx2 hH3 le_sup_left hLzxH hHV (by
      rw [map_tailProj_sup]; exact hzx'.2.1)
  have f6 : AdmCh (AdmT D) x (z ⊔ x) (x ⊔ y ⊔ z) :=
    pld_admCh_of D hx1 hLzx2 hH3 le_sup_right hLzxH hHV (by
      rw [map_tailProj_sup]; exact hzx'.2.2)
  exact ⟨x ⊔ y ⊔ z, x ⊔ y, y ⊔ z, z ⊔ x, f1, f2, f3, f4, f5, f6⟩

theorem clsT_commonNbrD (D : TData K)
    (nbr2 : ∀ u v, (∃ L, BFl u L ∧ D.okL u L) → (∃ L, BFl v L ∧ D.okL v L) →
      ∃ t, BPt t ∧ BAdj D u t ∧ BAdj D v t)
    (nbr4 : ∀ a b c d, BPt a → BPt b → BPt c → BPt d → BAdj D a b → BAdj D b c →
      BAdj D c d → BAdj D d a → ¬ BAdj D a c → ¬ BAdj D b d →
      ∃ t, BPt t ∧ BAdj D a t ∧ BAdj D b t ∧ BAdj D c t ∧ BAdj D d t)
    (nbr3 : ∀ u c d, (∃ L, BFl u L ∧ D.okL u L) → BPt c → BPt d → BAdj D c d →
      ∃ t, BPt t ∧ BAdj D u t ∧ BAdj D c t ∧ BAdj D d t) :
    AdmCommonNbrD (AdmT D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨hu1, huV, -, huL⟩ := pld_point_data hu
    obtain ⟨hv1, hvV, -, hvL⟩ := pld_point_data hv
    obtain ⟨t, ht, htu, htv⟩ := nbr2 (u.map tailProj) (v.map tailProj) huL hvL
    exact ⟨t, pld_lift hu1 huV ht htu, pld_lift hv1 hvV ht htv⟩
  · intro a b c d hab hbc hcd hda hac hnac hbd hnbd
    have hBab := pld_adj_base hab
    have hBbc := pld_adj_base hbc
    have hBcd := pld_adj_base hcd
    have hBda := pld_adj_base hda
    obtain ⟨-, La, Ha, hach, -⟩ := hab
    obtain ⟨-, Lb, Hb, hbch, -⟩ := hbc
    obtain ⟨-, Lc, Hc, hcch, -⟩ := hcd
    obtain ⟨-, Ld, Hd, hdch, -⟩ := hda
    obtain ⟨ha1, haV, haP, -⟩ := pld_point_data ⟨La, Ha, hach⟩
    obtain ⟨hb1, hbV, hbP, -⟩ := pld_point_data ⟨Lb, Hb, hbch⟩
    obtain ⟨hc1, hcV, hcP, -⟩ := pld_point_data ⟨Lc, Hc, hcch⟩
    obtain ⟨hd1, hdV, hdP, -⟩ := pld_point_data ⟨Ld, Hd, hdch⟩
    have hnBac : ¬ BAdj D (a.map tailProj) (c.map tailProj) := fun h =>
      hnac (pld_lift_gen ha1 haV hc1 hcV h)
    have hnBbd : ¬ BAdj D (b.map tailProj) (d.map tailProj) := fun h =>
      hnbd (pld_lift_gen hb1 hbV hd1 hdV h)
    obtain ⟨t, ht, hta, htb, htc, htd⟩ :=
      nbr4 (a.map tailProj) (b.map tailProj) (c.map tailProj) (d.map tailProj)
        haP hbP hcP hdP hBab hBbc hBcd hBda hnBac hnBbd
    exact ⟨t, pld_lift ha1 haV ht hta, pld_lift hb1 hbV ht htb,
      pld_lift hc1 hcV ht htc, pld_lift hd1 hdV ht htd⟩
  · intro u c d hu hcd
    obtain ⟨hu1, huV, -, huL⟩ := pld_point_data hu
    have hBcd := pld_adj_base hcd
    obtain ⟨-, Lc, Hc, hcch, hdch⟩ := hcd
    obtain ⟨hc1, hcV, hcP, -⟩ := pld_point_data ⟨Lc, Hc, hcch⟩
    obtain ⟨hd1, hdV, hdP, -⟩ := pld_point_data ⟨Lc, Hc, hdch⟩
    obtain ⟨t, ht, htu, htc, htd⟩ :=
      nbr3 (u.map tailProj) (c.map tailProj) (d.map tailProj) huL hcP hdP hBcd
    exact ⟨t, pld_lift hu1 huV ht htu, pld_lift hc1 hcV ht htc, pld_lift hd1 hdV ht htd⟩

theorem clsT_coneTriD (D : TData K)
    (cone : ∀ x y z, BPt x → BPt y → BPt z → BAdj D x y → BAdj D y z → BAdj D z x →
      finrank K ↥(x ⊔ y ⊔ z) ≠ 3 →
      ∃ t, BPt t ∧ BAdj D x t ∧ BAdj D y t ∧ BAdj D z t ∧ finrank K ↥(x ⊔ y ⊔ t) = 3 ∧
        finrank K ↥(y ⊔ z ⊔ t) = 3 ∧ finrank K ↥(z ⊔ x ⊔ t) = 3) :
    AdmConeTriD (AdmT D) := by
  intro x y z hxy hyz hzx
  have hx' : BPt (x.map tailProj) := pld_bpt_of_adj D hxy
  have hy' : BPt (y.map tailProj) := pld_bpt_of_adj D hyz
  have hz' : BPt (z.map tailProj) := pld_bpt_of_adj D hzx
  have hxy' : BAdj D (x.map tailProj) (y.map tailProj) := pld_badj_of_adj D hxy
  have hyz' : BAdj D (y.map tailProj) (z.map tailProj) := pld_badj_of_adj D hyz
  have hzx' : BAdj D (z.map tailProj) (x.map tailProj) := pld_badj_of_adj D hzx
  by_cases h3 : finrank K ↥(x.map tailProj ⊔ y.map tailProj ⊔ z.map tailProj) = 3
  · exact Or.inl (pld_planar_of_indep D hxy hyz hzx h3)
  · obtain ⟨t, ht, hxt, hyt, hzt, h3xy, h3yz, h3zx⟩ :=
      cone (x.map tailProj) (y.map tailProj) (z.map tailProj) hx' hy' hz' hxy' hyz' hzx' h3
    obtain ⟨hxt_adj, hyt_adj, hplan_xy⟩ := pld_side_data D hxy ht hxt hyt h3xy
    obtain ⟨-, hzt_adj, hplan_yz⟩ := pld_side_data D hyz ht hyt hzt h3yz
    obtain ⟨-, -, hplan_zx⟩ := pld_side_data D hzx ht hzt hxt h3zx
    exact Or.inr ⟨t, hxt_adj, hyt_adj, hzt_adj, hplan_xy, hplan_yz, hplan_zx⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
