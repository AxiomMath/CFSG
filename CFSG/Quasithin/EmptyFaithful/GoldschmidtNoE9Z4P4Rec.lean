module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Ex2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Pl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Rec

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem IsE9Dat.setup (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    ∃ h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H,
      ∃ _ : (∀ w : UMod h98.toHypF91, ∃ a ∈ kOf (rhoH h98.toHypF91),
          ∃ c ∈ fixV (rhoH h98.toHypF91).range, w = a * c),
        ∃ Q₁ Q₂ : Subgroup (MulAut ↥(kOf (rhoH h98.toHypF91))),
          E9Z4Str (resBeta (rhoH h98.toHypF91)).range
            ((T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)))
            ((PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91))) ∧
          PlanePair ((T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)))
            ((PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91))) Q₁ Q₂ ∧
          R₁ = HLb (resBeta (rhoH h98.toHypF91)) Q₁ ∧
          R₂ = HLb (resBeta (rhoH h98.toHypF91)) Q₂ := by
  classical
  have hcls : ClassAutShapeStmt := classAutShapeStmt
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  obtain ⟨hsplit, -, -⟩ := shape_splitting h35 S hred h98
  have hstr := e9z4Str_of_shape hcls h35 S hred hshape h98
  obtain ⟨Q₁, hQ₁P, hQ₁3, hrk₁, hR₁⟩ := hdat.plane₁.exists_HLb S hred h98 hsplit
  obtain ⟨Q₂, hQ₂P, hQ₂3, hrk₂, hR₂⟩ := hdat.plane₂.exists_HLb S hred h98 hsplit
  have hr₁ : Q₁ ≤ (resBeta (rhoH h98.toHypF91)).range := hQ₁P.trans (Subgroup.map_le_range _ _)
  have hr₂ : Q₂ ≤ (resBeta (rhoH h98.toHypF91)).range := hQ₂P.trans (Subgroup.map_le_range _ _)
  subst hR₁ hR₂
  refine ⟨h98, hsplit, Q₁, Q₂, hstr, ?_, rfl, rfl⟩
  have hdisj : Disjoint (commV Q₁) (commV Q₂) := by
    rw [disjoint_iff, eq_bot_iff]
    intro k ⟨hk₁, hk₂⟩
    obtain ⟨u₁, hu₁U, hu₁, hc₁⟩ := exists_mem_uHi_of_mem_commV h98.toHypF91 hsplit hr₁ hk₁
    obtain ⟨u₂, hu₂U, hu₂, hc₂⟩ := exists_mem_uHi_of_mem_commV h98.toHypF91 hsplit hr₂ hk₂
    have hz : u₁⁻¹ * u₂ ∈ quasithinOmegaOneCenter T :=
      (clsU_eq_iff h98.toHypF91 hu₁U hu₂U).mp (hc₁.trans hc₂.symm)
    have hz' : u₂⁻¹ * u₁ ∈ quasithinOmegaOneCenter T := by
      have := (quasithinOmegaOneCenter T).inv_mem hz
      simpa using this
    have hu₁₂ : u₁ ∈ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₂) := by
      have e : u₁ = u₂ * (u₂⁻¹ * u₁) := by group
      rw [e]
      exact Subgroup.mul_mem _ hu₂ (Z_le_uHi _ _ _ _ hz')
    have hu₁Z : u₁ ∈ quasithinOmegaOneCenter T := by
      have h12 : u₁ ∈ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₁) ⊓
          uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₂) := ⟨hu₁, hu₁₂⟩
      rwa [hdat.dir_inf] at h12
    have h1 : (k : UMod h98.toHypF91) = 1 := by
      rw [← hc₁]
      exact (clsU_eq_one_iff h98.toHypF91 hu₁U).mpr hu₁Z
    exact Subtype.ext h1
  have hsupK : commV Q₁ ⊔ commV Q₂ = ⊤ := by
    have hinf : commV Q₁ ⊓ commV Q₂ = ⊥ := disjoint_iff.mp hdisj
    have hsum := rk_sup_add_rk_inf (commV Q₁) (commV Q₂)
    rw [hinf, rk_bot, hrk₁, hrk₂] at hsum
    exact eq_of_le_of_rk_le hstr.sq le_top (by rw [rk_top, hstr.rk_four]; omega)
  have hsupQ : Q₁ ⊔ Q₂ = (PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) := by
    refine HLb_injective (sup_le hr₁ hr₂) (Subgroup.map_le_range _ _) ?_
    rw [HLb_sup hr₁ hr₂, hdat.sup, HLb_map_eq h98.toHypF91 hsplit hred.lt.le hred.le]
  have hfix : ∀ {Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h98.toHypF91)))},
      Qa ≤ (resBeta (rhoH h98.toHypF91)).range → Qb ≤ (resBeta (rhoH h98.toHypF91)).range →
      ⁅uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Qa),
        HLb (resBeta (rhoH h98.toHypF91)) Qb⁆ ≤ quasithinOmegaOneCenter T →
        commV Qa ≤ fixV Qb := by
    intro Qa Qb hQa hQb hcent k hk q hq
    obtain ⟨u, hU, hu, hc⟩ := exists_mem_uHi_of_mem_commV h98.toHypF91 hsplit hQa hk
    obtain ⟨r, hr⟩ := hQb hq
    have hrR : (r : G) ∈ HLb (resBeta (rhoH h98.toHypF91)) Qb :=
      mem_HLb_of_mem (by rw [hr]; exact hq)
    have hcomm := hcent (Subgroup.commutator_mem_commutator hu hrR)
    have hρ : rhoH h98.toHypF91 r (clsU h98.toHypF91 hU) = clsU h98.toHypF91 hU := by
      rw [rhoH_clsU_eq_iff]
      have e : (r : G) * u * (r : G)⁻¹ * u⁻¹ = (⁅u, (r : G)⁆)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (quasithinOmegaOneCenter T).inv_mem hcomm
    rw [← hr]
    refine Subtype.ext ((resBeta_apply _ _ _).trans ?_)
    rw [← hc]
    exact hρ
  have hsH : s ∈ H := hred.isHTM.1.1 hdat.s_mem
  have hσT : resBeta (rhoH h98.toHypF91) ⟨s, hsH⟩ ∈
      (T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hdat.s_mem)
  have hconj : conjSub s (HLb (resBeta (rhoH h98.toHypF91)) Q₁) =
      HLb (resBeta (rhoH h98.toHypF91)) (conjBy (resBeta (rhoH h98.toHypF91) ⟨s, hsH⟩) Q₁) :=
    conjSub_HLb hsH (fun y => by rw [← mem_conjBy_iff])
  have hcQ : conjBy (resBeta (rhoH h98.toHypF91) ⟨s, hsH⟩) Q₁ ≤
      (resBeta (rhoH h98.toHypF91)).range := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨b, rfl⟩ := hr₁ hq
    exact ⟨⟨s, hsH⟩ * b * ⟨s, hsH⟩⁻¹, by simp [MulAut.conj_apply]⟩
  have hσ : conjBy (resBeta (rhoH h98.toHypF91) ⟨s, hsH⟩) Q₁ = Q₂ := by
    refine HLb_injective hcQ hr₂ ?_
    rw [← hconj]
    exact hdat.conj
  exact ⟨hQ₁P, hQ₂P, hQ₁3, hQ₂3, hsupQ, hdisj, hsupK, hfix hr₁ hr₂ hdat.cent₁,
    hfix hr₂ hr₁ hdat.cent₂, _, hσT, hσ⟩

theorem resBeta_mem_zpowers_of_mem_normalizer
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Tb P : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hTb : Tb = (T.subgroupOf H).map (resBeta (rhoH h)))
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) {Q : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hQP : Q ≤ P) (hQ3 : Nat.card Q = 3) {t : MulAut ↥(kOf (rhoH h))} (htT : t ∈ Tb)
    (ht2 : orderOf t = 2) {x : G} (hxH : x ∈ H) (hxT : x ∈ T)
    (hxN : x ∈ Subgroup.normalizer (HLb (resBeta (rhoH h)) Q : Set G)) :
    resBeta (rhoH h) ⟨x, hxH⟩ ∈ Subgroup.zpowers t := by
  have hQr : Q ≤ (resBeta (rhoH h)).range := hQP.trans hstr.P_le_X
  have hyT : resBeta (rhoH h) ⟨x, hxH⟩ ∈ Tb :=
    hTb ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxT)
  have hyN : resBeta (rhoH h) ⟨x, hxH⟩ ∈ Subgroup.normalizer (Q : Set (MulAut ↥(kOf (rhoH h)))) :=
    (mem_normalizer_HLb_iff h hQr).mp hxN
  rcases hstr.orderOf_Tb hyT with h1 | h2 | h4
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · rw [hstr.eq_of_orderOf_eq_two hyT htT h2 ht2]
    exact Subgroup.mem_zpowers t
  · exact absurd (E9Z4Str.mem_normalizer_iff_conjBy.mp hyN)
      (hstr.conjBy_ne_of_orderOf_four (hstr.Tb_le_X hyT) h4 hQP hQ3)

theorem exists_mem_normalizer_resBeta_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Tb P : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hTb : Tb = (T.subgroupOf H).map (resBeta (rhoH h)))
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) {Q : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hQP : Q ≤ P) {t : MulAut ↥(kOf (rhoH h))} (htT : t ∈ Tb) (ht2 : orderOf t = 2) :
    ∃ x : G, ∃ hxH : x ∈ H, x ∈ T ∧
      x ∈ Subgroup.normalizer (HLb (resBeta (rhoH h)) Q : Set G) ∧
        resBeta (rhoH h) ⟨x, hxH⟩ = t := by
  have hQr : Q ≤ (resBeta (rhoH h)).range := hQP.trans hstr.P_le_X
  obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp (hTb ▸ htT)
  have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
  refine ⟨y, y.2, hyT, ?_, hyt⟩
  refine (mem_normalizer_HLb_iff h hQr).mpr ?_
  rw [hyt]
  exact hstr.zpowers_le_normalizer_of_le (hstr.Tb_le_X htT) ht2 hQP (Subgroup.mem_zpowers t)

end Rec

end CFSG.Quasithin
