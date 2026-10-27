module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1BAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8QBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3WJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_SL4MixedAux1
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_mixed_module_facts
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
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
    {r : G} (hrM : r ∈ D.M) (hr3 : orderOf r = 3)
    (hmixed : s16h_SL4Mixed V L h.hyp151.isElemAbelian x r)
    (hrB : barSub ⊥ V h.hyp151.isElemAbelian (Subgroup.zpowers r) ≤
      lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    ∃ a b : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      a ∈ lBar ⊥ V h.hyp151.isElemAbelian L ∧
      b ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) ∧
      a ^ 3 = 1 ∧ a ≠ 1 ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊔
        commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) = ⊤) ∧
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) =
        commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
      (∀ u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)), a u = u) ∧
      (∀ u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L), b u = u) ∧
      (∀ u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L),
        a u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
      (∀ u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)),
        b u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x))) ∧
      (∀ v ∈ fixV (barSub ⊥ V h.hyp151.isElemAbelian (Subgroup.zpowers r)),
        (a * b) v = v) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨L', hL'ne, F⟩ := s16h_sl4_two_frame_of_setting D h hs2
  have hLx : lBar ⊥ V hV (conjSubgroup L x) = L' :=
    s16h_sl4_lBar_conj_eq_of_frame D h F hxM hxn
  have hLbne : lBar ⊥ V hV L ≠ ⊥ := by
    intro hb
    have h1 : commSub (⊤ : Subgroup (Vtil ⊥ V hV))
        (⊥ : Subgroup (MulAut (Vtil ⊥ V hV))) = ⊥ := by
      simpa [commSub_eq_bot_iff, B1.fixV_bot]
    rw [hb, h1] at hZ4
    simp at hZ4
  let ρ : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨r, hMs hrM⟩
  have hr3' : r ^ 3 = 1 := hr3 ▸ pow_orderOf_eq_one r
  have hρ3 : ρ ^ 3 = 1 := by
    show actTil ⊥ V hV ⟨r, hMs hrM⟩ ^ 3 = 1
    rw [← map_pow]
    have h3 : (⟨r, hMs hrM⟩ : stabTil ⊥ V) ^ 3 = 1 :=
      Subtype.ext (by simpa using hr3')
    rw [h3, map_one]
  have hbarSub_zpowers : barSub ⊥ V hV (Subgroup.zpowers r) = Subgroup.zpowers ρ := by
    change ((Subgroup.zpowers r).subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV) =
      Subgroup.zpowers ρ
    have hsub : (Subgroup.zpowers r).subgroupOf (stabTil ⊥ V) =
        Subgroup.zpowers (⟨r, hMs hrM⟩ : stabTil ⊥ V) := by
      ext u
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, congrArg Subtype.val hn⟩
    rw [hsub, MonoidHom.map_zpowers]
  have hρmem : ρ ∈ barSub ⊥ V hV (Subgroup.zpowers r) :=
    actTil_mem_barSub ⊥ V hV (Subgroup.mem_zpowers r) (hMs hrM)
  have hρsup : ρ ∈ lBar ⊥ V hV L ⊔ lBar ⊥ V hV (conjSubgroup L x) := hrB hρmem
  rw [hLx] at hρsup
  obtain ⟨a, haL, b, hbL', hab⟩ := s16h_sl4_mem_sup_of_commute F.comm hρsup
  have hbLx : b ∈ lBar ⊥ V hV (conjSubgroup L x) := by
    rw [hLx]; exact hbL'
  have hcommab : Commute a b := F.comm a haL b hbL'
  have h1 : a ^ 3 * b ^ 3 = 1 := by
    rw [← hcommab.mul_pow 3, hab, hρ3]
  have hLbL'bot : lBar ⊥ V hV L ⊓ L' = ⊥ := by
    obtain ⟨e⟩ := s16h_sl4_isAlt_of_rowSL2 hrow
    exact s16h_sl4_alt_inf_eq_bot F.comm e
  have ha3eq : a ^ 3 = (b ^ 3)⁻¹ := eq_inv_iff_mul_eq_one.mpr h1
  have ha3mem : a ^ 3 ∈ lBar ⊥ V hV L ⊓ L' :=
    ⟨(lBar ⊥ V hV L).pow_mem haL 3, by
      rw [ha3eq]
      exact L'.inv_mem (L'.pow_mem hbL' 3)⟩
  have ha3 : a ^ 3 = 1 := Subgroup.mem_bot.1 (hLbL'bot ▸ ha3mem)
  have hb3 : b ^ 3 = 1 := by
    have h1' := h1
    rw [ha3, one_mul] at h1'
    exact h1'
  have hm1 : ¬ (barSub ⊥ V hV (Subgroup.zpowers r) ≤ barSub ⊥ V hV L) := hmixed.1
  have hm2 : ¬ (barSub ⊥ V hV (Subgroup.zpowers r) ≤
      barSub ⊥ V hV (conjSubgroup L x)) := hmixed.2
  have ha1 : a ≠ 1 := by
    intro ha1'
    apply hm2
    have hρb : ρ = b := by rw [← hab, ha1', one_mul]
    rw [hbarSub_zpowers]
    exact Subgroup.zpowers_le.mpr (hρb ▸ hbLx)
  have hb1 : b ≠ 1 := by
    intro hb1'
    apply hm1
    have hρa : ρ = a := by rw [← hab, hb1', mul_one]
    rw [hbarSub_zpowers]
    exact Subgroup.zpowers_le.mpr (hρa ▸ haL)
  have hsup : commSub ⊤ (lBar ⊥ V hV L) ⊔
      commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)) = ⊤ := by
    have h := s16h_wTil_sup_conj_eq_top_of_conc h.hyp151 hV hs2 hLbne hW hxM hxn
    simpa [wTil, lBar] using h
  have hw : wSub ⊥ V hV (conjSubgroup L x) = conjSubgroup (wSub ⊥ V hV L) x :=
    s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs hxM)
  have hZ0' : wSub ⊥ V hV L ⊓ wSub ⊥ V hV (conjSubgroup L x) =
      preTil ⊥ V hV (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) := by
    rw [hw, hZ0, s16h_wSub_inf_centralizer_eq_preTil D h]
  have hC := congrArg (imgTil ⊥ V hV) hZ0'
  simp only [wSub] at hC
  rw [s16h_imgTil_preTil_inf, imgTil_preTil] at hC
  have hinf : commSub ⊤ (lBar ⊥ V hV L) ⊓
      commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)) =
      commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) := by
    simpa [wTil, lBar] using hC
  have hcommU₂Lb : commSub (commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)))
      (lBar ⊥ V hV L) = ⊥ := by
    have hne : (1 : G) * x⁻¹ ∉ nBar D.M ⊥ V hV L := by
      rw [one_mul]
      intro hxinv
      exact hxn ((Subgroup.inv_mem_iff (nBar D.M ⊥ V hV L)).mp hxinv)
    have h := (s15_Kbar_commute_conj h.hyp151 (m := x) (m' := 1) hxM D.M.one_mem hne).2
    rw [conjSubgroup_one] at h
    simpa [lBar] using h
  have haU₂ : ∀ u ∈ commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)), a u = u := by
    have hle : commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)) ≤ fixV (lBar ⊥ V hV L) :=
      commSub_eq_bot_iff.mp hcommU₂Lb
    intro u hu
    exact hle hu a haL
  have hcommU₁Lx : commSub (commSub ⊤ (lBar ⊥ V hV L))
      (lBar ⊥ V hV (conjSubgroup L x)) = ⊥ := by
    have h := (h.hyp151.commute x hxM hxn).2
    simpa [wTil, lBar] using h
  have hbU₁ : ∀ u ∈ commSub ⊤ (lBar ⊥ V hV L), b u = u := by
    have hle : commSub ⊤ (lBar ⊥ V hV L) ≤ fixV (lBar ⊥ V hV (conjSubgroup L x)) :=
      commSub_eq_bot_iff.mp hcommU₁Lx
    intro u hu
    exact hle hu b hbLx
  have haU₁ : ∀ u ∈ commSub ⊤ (lBar ⊥ V hV L),
      a u ∈ commSub ⊤ (lBar ⊥ V hV L) :=
    fun u hu => CFSG.Quasithin.Asc81c.commSub_stable' haL hu
  have hbU₂ : ∀ u ∈ commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)),
      b u ∈ commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)) :=
    fun u hu => CFSG.Quasithin.Asc81c.commSub_stable' hbLx hu
  have hfix : ∀ v ∈ fixV (barSub ⊥ V hV (Subgroup.zpowers r)), (a * b) v = v := by
    intro v hv
    rw [hab]
    exact hv ρ hρmem
  exact ⟨a, b, haL, hbLx, ha3, ha1, hb3, hb1, hsup, hinf, haU₂, hbU₁, haU₁, hbU₂, hfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
