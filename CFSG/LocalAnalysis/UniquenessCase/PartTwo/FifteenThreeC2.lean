module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTI
import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Cover

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

section C2H

private theorem s15_Three_comm_of_commutator_eq_bot {A : Type} [Group A] {S T : Subgroup A}
    (h : ⁅S, T⁆ = ⊥) : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x := by
  intro x hx y hy
  have h1 : ⁅x, y⁆ ∈ ⁅S, T⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

private theorem s15_Three_actTil_mk_eq_iff {hV : IsElemAbelian 2 V} (hV0 : V₀ = ⊥)
    {x : G} (hx : x ∈ stabTil V₀ V) (v : IntMod V hV) :
    actTil V₀ V hV ⟨x, hx⟩ (mkTil V₀ V hV v) = mkTil V₀ V hV v ↔
      x * v.val * x⁻¹ = v.val := by
  subst hV0
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one]

private theorem s15_Three_cent_conj (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hV0 : V₀ = ⊥)
    {m m' : G} (hm : m ∈ D.M) (hm' : m' ∈ D.M) {g w : G} (hg : g ∈ conjSubgroup L m)
    (hw : w ∈ conjSubgroup (wSub V₀ V hV L ⊓ centralizer (L : Set G)) m') :
    g * w * g⁻¹ = w := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  set ℓ : G := m * g * m⁻¹ with hℓdef
  have hℓ : ℓ ∈ L := by
    rw [hℓdef]
    exact mem_conjSubgroup_iff.mp hg
  set w₀ : G := m' * w * m'⁻¹ with hw₀def
  have hw₀ : w₀ ∈ wSub V₀ V hV L ⊓ centralizer (L : Set G) := by
    simpa [hw₀def] using mem_conjSubgroup_iff.mp hw
  have hw₀V : w₀ ∈ V := preTil_le V₀ V hV (wTil V₀ V hV L) hw₀.1
  have hw₀C : w₀ ∈ centralizer (L : Set G) := hw₀.2
  have hgM : g ∈ D.M := by
    have hgm : m * g * m⁻¹ ∈ D.M := by
      have : ℓ ∈ D.M := h.le hℓ
      rwa [hℓdef] at this
    have hgg : g = m⁻¹ * (m * g * m⁻¹) * m := by group
    rw [hgg, mul_assoc]
    exact D.M.mul_mem (D.M.inv_mem hm) (D.M.mul_mem hgm hm)
  set g' : G := m' * g * m'⁻¹ with hg'def
  have hg'M : g' ∈ D.M := by
    rw [hg'def]
    exact D.M.mul_mem (D.M.mul_mem hm' hgM) (D.M.inv_mem hm')
  have hgs : g' ∈ stabTil V₀ V := hMs hg'M
  set n : G := m' * m⁻¹ with hndef
  have hn : n ∈ D.M := D.M.mul_mem hm' (D.M.inv_mem hm)
  have hg'conj : g' ∈ conjSubgroup L n⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have h : n⁻¹ * g' * (n⁻¹)⁻¹ = ℓ := by rw [hndef, hg'def, hℓdef]; group
    rw [h]
    exact hℓ
  have hmain : g' * w₀ * g'⁻¹ = w₀ := by
    by_cases hnbar : n⁻¹ ∈ nBar D.M V₀ V hV L
    · obtain ⟨-, hstab, hnorm⟩ :=
        (mem_preBarSub D.M V₀ V hV
          (normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))).1 hnbar
      have hnst : n ∈ stabTil V₀ V := hMs hn
      have hnormn : actTil V₀ V hV ⟨n, hnst⟩ ∈
          normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
        have h := Subgroup.inv_mem _ hnorm
        have hsn : (⟨n, hnst⟩ : stabTil V₀ V) = (⟨n⁻¹, hstab⟩ : stabTil V₀ V)⁻¹ :=
          Subtype.ext (by simp)
        rw [hsn, map_inv]
        exact h
      have hle : ℓ ∈ stabTil V₀ V := hMs (h.le hℓ)
      have hs : actTil V₀ V hV ⟨ℓ, hle⟩ ∈ barSub V₀ V hV L :=
        actTil_mem_barSub V₀ V hV hℓ hle
      have hdecomp : (⟨g', hgs⟩ : stabTil V₀ V) =
          ⟨n, hnst⟩ * ⟨ℓ, hle⟩ * (⟨n, hnst⟩)⁻¹ := by
        refine Subtype.ext ?_
        have : g' = n * ℓ * n⁻¹ := by rw [hndef, hℓdef, hg'def]; group
        simpa using this
      have hactL : actTil V₀ V hV ⟨g', hgs⟩ ∈ barSub V₀ V hV L := by
        have hacteq : actTil V₀ V hV ⟨g', hgs⟩ =
            actTil V₀ V hV ⟨n, hnst⟩ * actTil V₀ V hV ⟨ℓ, hle⟩ *
              (actTil V₀ V hV ⟨n, hnst⟩)⁻¹ := by
          rw [hdecomp, map_mul, map_mul, map_inv]
        rw [hacteq]
        exact (Subgroup.mem_normalizer_iff.1 hnormn (actTil V₀ V hV ⟨ℓ, hle⟩)).1 hs
      obtain ⟨ℓ₁, hℓ₁, hℓ₁eq⟩ :=
        (mem_barSub V₀ V hV L (actTil V₀ V hV ⟨g', hgs⟩)).1 hactL
      have hℓ₁w : (ℓ₁ : G) * w₀ * (ℓ₁ : G)⁻¹ = w₀ := by
        have hc := Subgroup.mem_centralizer_iff.1 hw₀C (ℓ₁ : G) hℓ₁
        rw [hc]
        group
      have hfix : actTil V₀ V hV ⟨g', hgs⟩
          (mkTil V₀ V hV (IntMod.mk hV ⟨w₀, hw₀V⟩)) =
            mkTil V₀ V hV (IntMod.mk hV ⟨w₀, hw₀V⟩) := by
        rw [← hℓ₁eq]
        exact (s15_Three_actTil_mk_eq_iff hV0 ℓ₁.2
          (IntMod.mk hV ⟨w₀, hw₀V⟩)).mpr hℓ₁w
      exact (s15_Three_actTil_mk_eq_iff hV0 hgs
        (IntMod.mk hV ⟨w₀, hw₀V⟩)).mp hfix
    · have hcomm := (h.commute n⁻¹ (D.M.inv_mem hn) hnbar).2
      have hfixmem : mkTil V₀ V hV (IntMod.mk hV ⟨w₀, hw₀V⟩) ∈ wTil V₀ V hV L :=
        (mem_preTil_iff_of_mem V₀ V hV (wTil V₀ V hV L) hw₀V).1 hw₀.1
      have hactconj : actTil V₀ V hV ⟨g', hgs⟩ ∈ barSub V₀ V hV (conjSubgroup L n⁻¹) :=
        actTil_mem_barSub V₀ V hV hg'conj hgs
      have hfixV : wTil V₀ V hV L ≤ fixV (barSub V₀ V hV (conjSubgroup L n⁻¹)) :=
        commSub_eq_bot_iff.mp hcomm
      have hfix := (mem_fixV.mp (hfixV hfixmem)) (actTil V₀ V hV ⟨g', hgs⟩) hactconj
      exact (s15_Three_actTil_mk_eq_iff hV0 hgs
        (IntMod.mk hV ⟨w₀, hw₀V⟩)).mp hfix
  have hg_eq : g = m'⁻¹ * g' * m' := by rw [hg'def]; group
  have hw_eq : w = m'⁻¹ * w₀ * m' := by rw [hw₀def]; group
  calc g * w * g⁻¹ = m'⁻¹ * (g' * w₀ * g'⁻¹) * m' := by rw [hg_eq, hw_eq]; group
    _ = m'⁻¹ * w₀ * m' := by rw [hmain]
    _ = w := by rw [← hw_eq]

private theorem s15_Three_cent_V1 (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hV0 : V₀ = ⊥) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hYX : barSub V₀ V hV Y ≤ s15XBar D V₀ V hV K₀) :
    ∀ y ∈ Y, ∀ w ∈ v1Sub D.M V₀ V hV L, y * w * y⁻¹ = w := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hV1le : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  let T : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨅ w : ↥(v1Sub D.M V₀ V hV L),
      MulAction.stabilizer (MulAut (Vtil V₀ V hV))
        (mkTil V₀ V hV (IntMod.mk hV ⟨(w : G), hV1le w.2⟩))
  have hXT : s15XBar D V₀ V hV K₀ ≤ T := by
    refine iSup₂_le fun m hm φ hφ => ?_
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV (conjSubgroup K₀ m) φ).1 hφ
    rw [Subgroup.mem_iInf]
    intro w
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    have hgL : (g : G) ∈ conjSubgroup L m := by
      rw [mem_conjSubgroup_iff] at hg ⊢
      exact hshape.1 hg
    have hcent : v1Sub D.M V₀ V hV L ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
      rw [v1Sub_of_eq_bot D.M V₀ V hV L hV0]
      refine iSup_le fun m' => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgw := s15_Three_cent_conj h hV hV0 hm m'.2 hgL hx
      calc x * (g : G) = ((g : G) * x * (g : G)⁻¹) * (g : G) := by rw [hgw]
        _ = (g : G) * x := by group
    have hwC := hcent w.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hwC
    rw [s15_Three_actTil_mk_eq_iff hV0 g.2 (IntMod.mk hV ⟨(w : G), hV1le w.2⟩)]
    calc (g : G) * (w : G) * (g : G)⁻¹ = ((w : G) * (g : G)) * (g : G)⁻¹ := by rw [← hwC]
      _ = (w : G) := by group
  intro y hy w hw
  have hyM : y ∈ D.M := hYM hy
  have hyst : y ∈ stabTil V₀ V := hMs hyM
  have hφ : actTil V₀ V hV ⟨y, hyst⟩ ∈ T :=
    hXT (hYX (actTil_mem_barSub V₀ V hV hy hyst))
  have hfix := (Subgroup.mem_iInf.mp hφ) ⟨w, hw⟩
  rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hfix
  exact (s15_Three_actTil_mk_eq_iff hV0 hyst (IntMod.mk hV ⟨w, hV1le hw⟩)).mp hfix

private theorem s15_Three_isCyclic_of_map {S : Type*} [Group S] {H : Subgroup S}
    {P : Subgroup H} (hc : IsCyclic ↥(P.map H.subtype)) : IsCyclic ↥P :=
  isCyclic_of_surjective
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.toMonoidHom
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.surjective

private theorem s15_Three_not_isCyclic {A : Type} [Group A] {p : ℕ} (hp : p.Prime)
    {E : Subgroup A} (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) :
    ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 := hp.one_lt
  nlinarith

private theorem s15_Three_not_thin {Y : Subgroup G} {A : Type} [Group A] [Finite A]
    (f : ↥Y →* A) {H : Subgroup A} (hH : H ≤ f.range) (h2 : 2 ≤ CFSG.Open.pRank 3 H) :
    ¬ F09.Thin9 Y := by
  intro hthin
  obtain ⟨E, hEH, hE, hEcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank Nat.prime_three (k := 2) h2
  have hEnc : ¬ IsCyclic E :=
    s15_Three_not_isCyclic Nat.prime_three hE (by rw [hEcard])
  obtain ⟨Q, hQ3, hQnc, -⟩ := s15_Three_lift_sylow f (hEH.trans hH) hE.isPGroup hEnc
  have hQ3' : IsPGroup 3 (Q.map Y.subtype) := hQ3.map Y.subtype
  have hQnc' : ¬ IsCyclic (Q.map Y.subtype) := fun hc =>
    hQnc (s15_Three_isCyclic_of_map (H := Y) hc)
  have hQle : Q.map Y.subtype ≤ Y := by
    rintro x ⟨q, -, rfl⟩
    exact q.2
  have h2le : 2 ≤ CFSG.Open.pRank 3 Y := s15_Three_two_le_pRank hQle hQ3' hQnc'
  have hle1 : CFSG.Open.pRank 3 Y ≤ 1 := hthin 3 Nat.prime_three (by norm_num)
  omega

end C2H

theorem s15_Three_cover (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hX2 : 2 ≤ CFSG.Open.pRank 3 (s15XStar D V₀ V hV L K₀)) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧
      barSub (v1Sub D.M V₀ V hV L) V hV Y = s15XStar D V₀ V hV L K₀ ∧
      ∀ y ∈ Y, ∀ w ∈ v1Sub D.M V₀ V hV L, y * w * y⁻¹ = w := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  haveI := s15_Three_cTilde_normal hV hMs
  obtain ⟨X, Y, -, hXM, -, -, hYbar, hYstar, H⟩ :=
    s15_Three_Y119 hSimple h127 h119 h1217 h hV hshape hperf
  have H' : F11.IsY119 D.M V₀ V X Y ∧ (¬ F09.Thin9 Y → ⁅Y, V₀⁆ = ⊥) :=
    @H (s15_Three_cTilde_normal hV hMs)
  obtain ⟨hY119, hYthin⟩ := H'
  have hYM : Y ≤ D.M := hY119.1.trans hXM
  refine ⟨Y, hYM, hYstar, ?_⟩
  by_cases hV0 : V₀ = ⊥
  · exact s15_Three_cent_V1 h hV hshape hV0 hYM hYbar.le
  · have hV1 : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV0
    have hMs₁ : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer
        (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
    let f : ↥Y →* MulAut (vStar D.M V₀ V hV L) :=
      (actTil (v1Sub D.M V₀ V hV L) V hV).comp (Subgroup.inclusion (hYM.trans hMs₁))
    have hfr : s15XStar D V₀ V hV L K₀ ≤ f.range := by
      intro φ hφ
      rw [← hYstar] at hφ
      obtain ⟨g, hg, rfl⟩ :=
        (mem_barSub (v1Sub D.M V₀ V hV L) V hV Y φ).1 hφ
      refine ⟨⟨(g : G), hg⟩, ?_⟩
      have hgg : (⟨(g : G), hMs₁ (hYM hg)⟩ :
          ↥(stabTil (v1Sub D.M V₀ V hV L) V)) = g := Subtype.ext rfl
      show actTil (v1Sub D.M V₀ V hV L) V hV
        ⟨(g : G), hMs₁ (hYM hg)⟩ = actTil (v1Sub D.M V₀ V hV L) V hV g
      rw [hgg]
    have hthin : ¬ F09.Thin9 Y := s15_Three_not_thin f hfr hX2
    have hYV₀ : ⁅Y, V₀⁆ = ⊥ := hYthin hthin
    intro y hy w hw
    rw [hV1] at hw
    have hcy := s15_Three_comm_of_commutator_eq_bot hYV₀ y hy w hw
    rw [hcy]
    group

theorem s15_Three_O1a (hT : RTable137) (hRk : RRank3List153) (hAbs : RAbsIrr153)
    (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hnot : ¬ (s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L))) :
    s15O1a D V := by
  intro v hvV hv1
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  obtain ⟨E₀, hE₀X, hE₀3, hE₀nc, -⟩ :=
    s15_Three_stab_rank hT hRk hAbs h1217 h hV hL hshape hperf hnot 1
  have hX2 : 2 ≤ CFSG.Open.pRank 3 (s15XStar D V₀ V hV L K₀) :=
    s15_Three_two_le_pRank hE₀X hE₀3 hE₀nc
  obtain ⟨Y, hYM, hYX, hY1⟩ := s15_Three_cover hSimple h127 h119 h1217 h hV hshape hperf hX2
  obtain ⟨E, hEX, hE3, hEnc, hEz⟩ := s15_Three_stab_rank hT hRk hAbs h1217 h hV hL hshape hperf
    hnot (mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hvV⟩))
  have := s15_Three_lift_rank (M := D.M) hV (s15_Infra_v1Sub_le h.hyp125 hV) hYM
    (hYM.trans hMs1) hY1 hvV (by rw [hYX]; exact hEX) hE3 hEnc hEz
  omega

theorem s15_Three_trich (hT : RTable137) (hRk : RRank3List153) (hAbs : RAbsIrr153)
    (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hshape : s15Shape D V₀ V hV L K₀) :
    s15Trich D V₀ V hV L K₀ := by
  by_cases hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3
  · exact Or.inr (Or.inl hZ)
  by_cases hbig : s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L)
  · exact Or.inr (Or.inr hbig)
  have hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :=
    hshape.2.2.2.1.resolve_right (fun hz => hZ hz.1)
  exact Or.inl (s15_Three_O1a hT hRk hAbs hSimple h127 h119 h1217 h hV hL hshape hperf hbig)

end Cover

section TI

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

theorem s15_Three_inCalV {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) : InCalV D.M V := by
  rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
  · exact hW.1.1.1
  · exact h0.2.1

private theorem s15_Three_uniqueMax_of_le {M E C : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hEC : E ≤ C) (hCM : C ≤ M) (hE : UniqueMax M E) : UniqueMax M C := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hM, hCM⟩, fun N hN => ?_⟩
  have hN' : N ∈ calMOf E := ⟨hN.1, hEC.trans hN.2⟩
  rw [hE] at hN'
  exact hN'

theorem s15_Three_TI_of_O1a (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (hVc : InCalV D.M V)
    (hu : 3 ∈ D.sig ∨ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (hO1 : s15O1a D V) :
    CFSG.CGT.Timmesfeld75.IsTI V := by
  obtain ⟨-, -, hMV, hV⟩ := hVc
  rcases hu with h3 | hs
  · exact s16_TI_of_pRank D h61 hV hMV fun w hw hw1 => ⟨3, h3, hO1 w hw hw1⟩
  · refine s15_FiveTen_isTI_of_uniqueMax D hV hMV fun w hw hw1 => ?_
    obtain ⟨E, hEC, hE, hEcard⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank Nat.prime_three
        (k := 2) (hO1 w hw hw1)
    have hEM : E ≤ D.M := hEC.trans inf_le_left
    exact s15_Three_uniqueMax_of_le D.maxLocal hEC inf_le_left
      (h63 3 Nat.prime_three (by norm_num) E hEM hE hEcard
        (hs.rankThreeGamma_one_le_of_le Nat.prime_three hE.isPGroup hEM))

theorem s15_Three_not_O1a_of_unique (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D)
    (h : Hyp125 D V₀ V)
    (hu : 3 ∈ D.sig ∨ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    ¬ s15O1a D V := fun hO1 =>
  (twelve_nine D h127 h).1
    (s15_Three_TI_of_O1a h61 h63 (s15_Three_inCalV h) hu hO1)

theorem s15_Three_unique_of_O1a (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D)
    (h : Hyp125 D V₀ V) (hO1 : s15O1a D V) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M ∧ 3 ∉ D.sig := by
  refine ⟨fun hs => ?_, fun h3 => ?_⟩
  · exact s15_Three_not_O1a_of_unique h61 h63 h127 h (Or.inr hs) hO1
  · exact s15_Three_not_O1a_of_unique h61 h63 h127 h (Or.inl h3) hO1

end TI

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
