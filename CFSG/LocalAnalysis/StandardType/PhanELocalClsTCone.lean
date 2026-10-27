module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

private theorem plh_map_le_Vtail (S : Submodule K (Fin 4 → K)) :
    S.map tailProj ≤ (Vtail : Submodule K (Fin 4 → K)) := by
  rintro _ ⟨v, -, rfl⟩
  exact tailProj_mem v

private theorem plh_inf_Vsub_eq_bot_of_finrank_map_eq {S : Submodule K (Fin 4 → K)}
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

private theorem plh_admCh_of (D : TData K) {p L H : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hL : finrank K L = 2) (hH : finrank K H = 3)
    (hpL : p ≤ L) (hLH : L ≤ H) (hH1 : H ⊓ Vsub 4 1 = ⊥)
    (hok : D.okL (p.map tailProj) (L.map tailProj)) : AdmCh (AdmT D) p L H :=
  ⟨⟨hp, hL, hH, hpL, hLH⟩, hH1, hok⟩

private theorem plh_adm_point (D : TData K) {a b : Submodule K (Fin 4 → K)}
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

private theorem plh_bpt_of_adj (D : TData K) {a b : Submodule K (Fin 4 → K)}
    (hab : AdmAdj (AdmT D) a b) : BPt (a.map tailProj) := by
  obtain ⟨ha1, haV⟩ := plh_adm_point D hab
  exact ⟨plh_map_le_Vtail a, by rw [finrank_map_tailProj haV, ha1]⟩

private theorem plh_badj_of_adj (D : TData K) {a b : Submodule K (Fin 4 → K)}
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

private theorem plh_plane_finrank_inf {a b t : Submodule K (Fin 4 → K)}
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
  apply plh_inf_Vsub_eq_bot_of_finrank_map_eq
  rw [hmap, h3, hH]

private theorem plh_side_data (D : TData K) {a b t : Submodule K (Fin 4 → K)}
    (hab : AdmAdj (AdmT D) a b) (ht : BPt t)
    (hat : BAdj D (a.map tailProj) t) (hbt : BAdj D (b.map tailProj) t)
    (h3 : finrank K ↥(a.map tailProj ⊔ b.map tailProj ⊔ t) = 3) :
    AdmAdj (AdmT D) a t ∧ AdmAdj (AdmT D) b t ∧ AdmPlanar (AdmT D) a b t := by
  obtain ⟨-, haok', hbok'⟩ := plh_badj_of_adj D hab
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
  obtain ⟨hH3, hHV⟩ := plh_plane_finrank_inf ha1 hb1 ht1 habne htV h3
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
    plh_admCh_of D ha1 hL₁2 hH3 le_sup_left le_sup_left hHV (by
      rw [map_tailProj_sup]; exact haok')
  have f2 : AdmCh (AdmT D) b (a ⊔ b) (a ⊔ b ⊔ t) :=
    plh_admCh_of D hb1 hL₁2 hH3 le_sup_right le_sup_left hHV (by
      rw [map_tailProj_sup]; exact hbok')
  have f3 : AdmCh (AdmT D) b (b ⊔ t) (a ⊔ b ⊔ t) :=
    plh_admCh_of D hb1 hL₂2 hH3 le_sup_left hL₂H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV]; exact hbtok)
  have f4 : AdmCh (AdmT D) t (b ⊔ t) (a ⊔ b ⊔ t) :=
    plh_admCh_of D ht1 hL₂2 hH3 le_sup_right hL₂H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV]; exact hbtok')
  have f5 : AdmCh (AdmT D) t (t ⊔ a) (a ⊔ b ⊔ t) :=
    plh_admCh_of D ht1 hL₃2 hH3 le_sup_left hL₃H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV, sup_comm]
      exact hatok')
  have f6 : AdmCh (AdmT D) a (t ⊔ a) (a ⊔ b ⊔ t) :=
    plh_admCh_of D ha1 hL₃2 hH3 le_sup_right hL₃H hHV (by
      rw [map_tailProj_sup, map_tailProj_of_le htV, sup_comm]
      exact hatok)
  exact ⟨⟨hat_ne, t ⊔ a, a ⊔ b ⊔ t, f6, f5⟩, ⟨hbt_ne, b ⊔ t, a ⊔ b ⊔ t, f3, f4⟩,
    ⟨a ⊔ b ⊔ t, a ⊔ b, b ⊔ t, t ⊔ a, f1, f2, f3, f4, f5, f6⟩⟩

theorem clsT_coneTri (D : TData K) (h : TBase D) : AdmConeTri (AdmT D) := by
  intro x y z hxy hyz hzx
  have hx' : BPt (x.map tailProj) := plh_bpt_of_adj D hxy
  have hy' : BPt (y.map tailProj) := plh_bpt_of_adj D hyz
  have hz' : BPt (z.map tailProj) := plh_bpt_of_adj D hzx
  have hxy' : BAdj D (x.map tailProj) (y.map tailProj) := plh_badj_of_adj D hxy
  have hyz' : BAdj D (y.map tailProj) (z.map tailProj) := plh_badj_of_adj D hyz
  have hzx' : BAdj D (z.map tailProj) (x.map tailProj) := plh_badj_of_adj D hzx
  obtain ⟨t, ht, hxt, hyt, hzt, h3xy, h3yz, h3zx⟩ :=
    h.cone (x.map tailProj) (y.map tailProj) (z.map tailProj) hx' hy' hz' hxy' hyz' hzx'
  obtain ⟨hxt_adj, hyt_adj, hplan_xy⟩ := plh_side_data D hxy ht hxt hyt h3xy
  obtain ⟨hyt_adj', hzt_adj, hplan_yz⟩ := plh_side_data D hyz ht hyt hzt h3yz
  obtain ⟨hzt_adj', hxt_adj', hplan_zx⟩ := plh_side_data D hzx ht hzt hxt h3zx
  exact ⟨t, hxt_adj, hyt_adj, hzt_adj, hplan_xy, hplan_yz, hplan_zx⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
