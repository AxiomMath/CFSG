module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BEC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BED
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3WJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNineLP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_zz_cent_eq_alpha
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x = ⊥) :
    Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        centSub (imgTil ⊥ V h.hyp151.isElemAbelian
          (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L)) ≤
      Subgroup.normalizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L :
          Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
          Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
  have hV := h.hyp151.isElemAbelian
  intro φ hφ
  rw [Subgroup.mem_inf] at hφ
  obtain ⟨hφM, hφc⟩ := hφ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  obtain ⟨L', hL'ne, F⟩ := s16h_sl4_two_frame_of_setting D h hs2
  have hLx : lBar ⊥ V hV (conjSubgroup L x) = L' :=
    s16h_sl4_lBar_conj_eq_of_frame D h F hxM hxn
  rcases F.perm φ hφM with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exfalso
    have hMs : D.M ≤ stabTil ⊥ V :=
      le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
        h.hyp151.hyp125.pairFacts.le_normalizer₀
    have hLst : L ≤ stabTil ⊥ V := h.hyp151.le.trans hMs
    have hxs : x ∈ stabTil ⊥ V := hMs hxM
    have hv1 : wSub ⊥ V hV L ⊓ centralizer (L : Set G) ≤ v1Sub D.M ⊥ V hV L := by
      rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
      have hh := le_iSup (fun m : D.M =>
        conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) (m : G)) 1
      rwa [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one] at hh
    have hZt_Ut : commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) ≤
        imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) := by
      change wTil ⊥ V hV L ⊓ fixV (lBar ⊥ V hV L) ≤
        imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L)
      rw [← s16h_sl4be_imgTil_wSub_inf_cent hV hLst]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono V hv1)
    have hfixZt : ∀ z ∈ commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L), φ z = z :=
      fun z hz => (mem_centSub.1 hφc) z (hZt_Ut hz)
    set Zt : Subgroup (Vtil ⊥ V hV) :=
      commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) with hZtdef
    set Zt' : Subgroup (Vtil ⊥ V hV) := commSub ⊤ L' ⊓ fixV L' with hZt'def
    have hmap_comm : (commSub ⊤ (lBar ⊥ V hV L)).map φ.toMonoidHom =
        commSub ⊤ ((lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom) := by
      have hh := s15_Core_commSub_map_conj (⊤ : Subgroup (Vtil ⊥ V hV))
        (lBar ⊥ V hV L) φ
      rw [Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective] at hh
      exact hh.symm
    have hmap_fix : (fixV (lBar ⊥ V hV L)).map φ.toMonoidHom =
        fixV ((lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom) :=
      (s16h_sl4be_fixV_map_conj (lBar ⊥ V hV L) φ).symm
    have hmap_Zt : Zt.map φ.toMonoidHom = Zt' := by
      rw [hZtdef, hZt'def, Subgroup.map_inf _ _ φ.toMonoidHom φ.injective,
        hmap_comm, hmap_fix, h1]
    have hZt_eq : Zt = Zt' := by
      rw [← hmap_Zt]
      refine le_antisymm ?_ ?_
      · intro z hz
        exact ⟨z, hz, hfixZt z hz⟩
      · rintro z ⟨y, hy, rfl⟩
        simpa [hfixZt y hy] using hy
    have hwsubV : wSub ⊥ V hV L ≤ V := preTil_le ⊥ V hV _
    have hconjV : conjSubgroup (wSub ⊥ V hV L) x ≤ V := by
      rw [← s15_Infra_wSub_conjSubgroup ⊥ V L hV hxs]
      exact preTil_le ⊥ V hV _
    have hinf : wTil ⊥ V hV L ⊓ wTil ⊥ V hV (conjSubgroup L x) = ⊥ := by
      have h1' : wTil ⊥ V hV L = imgTil ⊥ V hV (wSub ⊥ V hV L) :=
        (imgTil_preTil ⊥ V hV (wTil ⊥ V hV L)).symm
      have h2' : wTil ⊥ V hV (conjSubgroup L x) =
          imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) x) := by
        rw [← imgTil_preTil ⊥ V hV (wTil ⊥ V hV (conjSubgroup L x)), ← wSub,
          s15_Infra_wSub_conjSubgroup ⊥ V L hV hxs]
      rw [h1', h2', ← s16h_sl4be_imgTil_inf hV hwsubV hconjV, hZ0,
        s16c167_twenty_two_imgTil_bot]
    have hZt_bot : Zt = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have hzL : z ∈ wTil ⊥ V hV L := hz.1
      have hzLx : z ∈ wTil ⊥ V hV (conjSubgroup L x) := by
        have hz' : z ∈ Zt' := hZt_eq ▸ hz
        have hcomm : commSub ⊤ L' = wTil ⊥ V hV (conjSubgroup L x) := by
          rw [← hLx]; rfl
        exact hcomm ▸ hz'.1
      have hmem : z ∈ wTil ⊥ V hV L ⊓ wTil ⊥ V hV (conjSubgroup L x) := ⟨hzL, hzLx⟩
      rwa [hinf] at hmem
    exact hZ (hZtdef ▸ hZt_bot)

theorem s16h_sl4_zz_cent_eq_beta
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        Subgroup.normalizer
          ((lBar ⊥ V h.hyp151.isElemAbelian L :
            Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
            Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) ⊓
        centSub (imgTil ⊥ V h.hyp151.isElemAbelian
          (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L)) ≤
      lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨L', hne', F⟩ := s16h_sl4_two_frame_of_setting D h hs2
  have hconj := s16h_sl4_lBar_conj_eq_of_frame D h F hxM hxn
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hLst : L ≤ stabTil ⊥ V := h.hyp151.le.trans hMs
  have hLxM : conjSubgroup L x ≤ D.M := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.hyp151.le hy)) hxM
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at hy'
  have hLxst : conjSubgroup L x ≤ stabTil ⊥ V := hLxM.trans hMs
  have hL : barSub ⊥ V hV L ≠ ⊥ := by
    intro h0
    apply hZ
    have h1 : lBar ⊥ V hV L = ⊥ := h0
    have hc : commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (⊥ : Subgroup (MulAut (Vtil ⊥ V hV))) = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro v _ x hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      rfl
    rw [h1, hc]
    exact bot_inf_eq _
  have hJoin : commSub ⊤ (lBar ⊥ V hV L) ⊔ commSub ⊤ L' = ⊤ := by
    have h2 := s16h_wTil_sup_conj_eq_top_of_conc h.hyp151 hV hs2 hL hW hxM hxn
    unfold wTil at h2
    rw [← hconj]
    exact h2
  obtain ⟨t', ht'T, ht'L⟩ := F.swap
  have ht'n : t' ∉ Subgroup.normalizer ((lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))) :
      Set (MulAut (Vtil ⊥ V hV))) := by
    intro hn
    apply hne'
    rw [← ht'L]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 hn
  obtain ⟨hL'c, hLc⟩ := s16h_sl4_conc_cent hW (F.t_le ht'T) ht'n
  rw [ht'L] at hL'c hLc
  have hv1 := s16h_e3_v1Sub_eq_sup_zx D h hs2 hxM hxn
  have hZ1 := s16h_sl4be_imgTil_wSub_inf_cent hV hLst
  have hZ2 := s16h_sl4be_imgTil_wSub_inf_cent hV hLxst
  have hZ2' : wSub ⊥ V hV (conjSubgroup L x) ⊓ Subgroup.centralizer (conjSubgroup L x : Set G) =
      conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs hxM)]
  have hsup : (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) ⊔
      (commSub ⊤ L' ⊓ fixV L') ≤ imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) := by
    refine sup_le ?_ ?_
    · have h3 : commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) =
          imgTil ⊥ V hV (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) := hZ1.symm
      rw [h3]
      exact s15_LP_imgTil_mono hV (by rw [hv1]; exact le_sup_left)
    · have h3 : commSub ⊤ L' ⊓ fixV L' =
          imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x) := by
        rw [← hZ2', ← hconj]
        exact hZ2.symm
      rw [h3]
      exact s15_LP_imgTil_mono hV (by rw [hv1]; exact le_sup_right)
  intro τ hτ
  obtain ⟨hτMN, hτC⟩ := Subgroup.mem_inf.1 hτ
  obtain ⟨hτM, hτN⟩ := Subgroup.mem_inf.1 hτMN
  have key := s16h_sl4_frame_normalizer_cent_Z (s15_Infra_vtil_sq_eq_one ⊥ V hV) F hne'.symm
    hrow hZ4 hJoin hLc hL'c hτM hτN (fun z hz => hτC z (hsup hz))
  rw [← hconj] at key
  exact key

theorem s16h_sl4_zz_cent_eq_gamma
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) ≤
      centSub (imgTil ⊥ V h.hyp151.isElemAbelian
        (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L)) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hLst : L ≤ stabTil ⊥ V := h.hyp151.le.trans hMs
  have hLxM : conjSubgroup L x ≤ D.M := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.hyp151.le hy)) hxM
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at hy'
  have hLxst : conjSubgroup L x ≤ stabTil ⊥ V := hLxM.trans hMs
  have hcent := s16h_sl4_L_sup_le_cent_v1 D S hσ hJP h hs2 hxM hxn
  change barSub ⊥ V hV L ⊔ barSub ⊥ V hV (conjSubgroup L x) ≤
    centSub (imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L))
  rw [← s16c7_barSub_sup ⊥ V hV hLst hLxst]
  exact s15_LP_barSub_le_centSub_imgTil hV (sup_le hLst hLxst) hcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
