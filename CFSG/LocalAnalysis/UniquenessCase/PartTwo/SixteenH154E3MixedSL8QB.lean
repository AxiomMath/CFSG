module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8QBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23CoreA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenBlocksA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_zz_cent_eq_normalizer
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x = ⊥)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian)) :
    T ⊓ centSub (imgTil ⊥ V h.hyp151.isElemAbelian (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L)) =
      T ⊓ Subgroup.normalizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
          Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
  classical
  have hV := h.hyp151.isElemAbelian
  let W := Vtil ⊥ V hV
  let Lb : Subgroup (MulAut W) := lBar ⊥ V hV L
  let Lx : Subgroup (MulAut W) := lBar ⊥ V hV (conjSubgroup L x)
  let Wt : Subgroup W := commSub ⊤ Lb
  let Zt : Subgroup W := Wt ⊓ fixV Lb
  let Wxt : Subgroup W := commSub ⊤ Lx
  let Zxt : Subgroup W := Wxt ⊓ fixV Lx
  let Ut : Subgroup W := imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L)
  change T ⊓ centSub Ut = T ⊓ Subgroup.normalizer (Lb : Set (MulAut W))
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxst : x ∈ stabTil ⊥ V := hMs hxM
  let φ : MulAut W := (actTil ⊥ V hV ⟨x, hxst⟩)⁻¹
  have hLbmap : Lb.map (MulAut.conj φ).toMonoidHom = Lx :=
    (s15_Infra_barSub_conjSubgroup ⊥ V hV hxst L).symm
  have hZtImg : Zt = imgTil ⊥ V hV (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) := by
    rw [s16h_wSub_inf_centralizer_eq_preTil D h, imgTil_preTil]
  have hZtMap : Zt.map φ.toMonoidHom = Zxt := by
    show (commSub ⊤ Lb ⊓ fixV Lb).map φ.toMonoidHom = commSub ⊤ Lx ⊓ fixV Lx
    rw [Subgroup.map_inf (commSub ⊤ Lb) (fixV Lb) φ.toMonoidHom φ.injective,
      ← s15_Infra_commSub_top_map_conj Lb φ,
      ← s16t_blk_fixV_map_conj Lb φ, hLbmap]
  have hZV : wSub ⊥ V hV L ⊓ centralizer (L : Set G) ≤ V :=
    inf_le_left.trans (preTil_le ⊥ V hV (wTil ⊥ V hV L))
  have hZVx : conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) x ≤ V := by
    calc conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) x ≤ conjSubgroup V x :=
          E3.conjSubgroup_mono_left x hZV
      _ = V := conjSubgroup_eq_iff_mem_normalizer.mpr (stabTil_le_normalizer ⊥ V hxst)
  have hUt : Ut = Zt ⊔ Zxt := by
    show imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) = Zt ⊔ Zxt
    rw [s16h_e3_v1Sub_eq_sup_zx D h hs2 hxM hxn, s15_Core_imgTil_sup hV hZV hZVx]
    congr 1
    · exact hZtImg.symm
    · show imgTil ⊥ V hV
        (conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) x) = Zxt
      rw [s15_Infra_imgTil_conjSubgroup ⊥ V
          (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) hV hxst,
        s16h_wSub_inf_centralizer_eq_preTil D h, imgTil_preTil]
      exact hZtMap
  have hZtleUt : Zt ≤ Ut := by
    rw [hUt]; exact le_sup_left
  have hWtbot : Wt ⊓ Wxt = ⊥ := by
    have hpre : preTil ⊥ V hV Wt ⊓ preTil ⊥ V hV Wxt = ⊥ := by
      show wSub ⊥ V hV L ⊓ wSub ⊥ V hV (conjSubgroup L x) = ⊥
      rw [s15_Infra_wSub_conjSubgroup ⊥ V L hV hxst]
      exact hZ0
    have h := congrArg (imgTil ⊥ V hV) hpre
    rwa [s16h_imgTil_preTil_inf, s16h_imgTil_bot] at h
  have hLbZt : Lb ≤ centSub Zt := fun g hg u hu => mem_fixV.1 hu.2 g hg
  have hLbWxt : Lb ≤ centSub Wxt :=
    fun g hg => c23_fix_wTil_conj h.hyp151 hV hxM hxn g hg
  have hLxZxt : Lx ≤ centSub Zxt := fun g hg u hu => mem_fixV.1 hu.2 g hg
  have hLxWt : Lx ≤ centSub Wt :=
    fun g hg => c23_fix_wTil_of_nBar h.hyp151 hV hxM hxn g hg
  have hLbUt : Lb ≤ centSub Ut := by
    rw [hUt, s16h_centSub_sup_eq]
    exact le_inf hLbZt (hLbWxt.trans fun g hg u hu => hg u hu.1)
  have hLxUt : Lx ≤ centSub Ut := by
    rw [hUt, s16h_centSub_sup_eq]
    exact le_inf (hLxWt.trans fun g hg u hu => hg u hu.1) hLxZxt
  have hNle : T ⊓ Subgroup.normalizer (Lb : Set (MulAut W)) ≤ centSub Ut := by
    obtain ⟨TA, TB, -, -, hTAsy, hTBsy, hshapeeq⟩ :=
      s16h_sl28_sylow_normalizer_shape D S h hs2 hW hrow hxM hxn T hT
    rw [hshapeeq]
    exact sup_le (hTAsy.le.trans hLbUt) (hTBsy.le.trans hLxUt)
  have hle : T ⊓ centSub Ut ≤ T ⊓ Subgroup.normalizer (Lb : Set (MulAut W)) := by
    refine le_inf inf_le_left ?_
    intro s hs
    have hsT : s ∈ T := hs.1
    have hsc : s ∈ centSub Ut := hs.2
    have hsMb : s ∈ Mbar D.M ⊥ V hV := hT.le hsT
    obtain ⟨L', -, F⟩ := s16h_sl4_two_frame_of_setting D h hs2
    have hLconj : Lx = L' := s16h_sl4_lBar_conj_eq_of_frame D h F hxM hxn
    rcases F.perm s hsMb with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 h1
    · exfalso
      have hsmap : Zt.map s.toMonoidHom = Zxt := by
        show (commSub ⊤ Lb ⊓ fixV Lb).map s.toMonoidHom = commSub ⊤ Lx ⊓ fixV Lx
        rw [Subgroup.map_inf (commSub ⊤ Lb) (fixV Lb) s.toMonoidHom s.injective,
          ← s15_Infra_commSub_top_map_conj Lb s,
          ← s16t_blk_fixV_map_conj Lb s, h1, ← hLconj]
      have hZfix : Zt.map s.toMonoidHom = Zt := by
        apply le_antisymm
        · rintro _ ⟨z, hz, rfl⟩
          have hzfix : s z = z := hsc z (hZtleUt hz)
          simpa [hzfix] using hz
        · intro z hz
          exact ⟨z, hz, hsc z (hZtleUt hz)⟩
      have hZeq : Zt = Zxt := hZfix.symm.trans hsmap
      have hZle : Zt ≤ Wt ⊓ Wxt := le_inf inf_le_left ((le_of_eq hZeq).trans inf_le_left)
      have hZbot : Zt = ⊥ := le_bot_iff.1 (hWtbot ▸ hZle)
      exact hZ hZbot
  exact le_antisymm hle (le_inf inf_le_left hNle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
