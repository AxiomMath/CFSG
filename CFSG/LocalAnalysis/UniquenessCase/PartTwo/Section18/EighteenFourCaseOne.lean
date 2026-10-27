module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourWeak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L K : Subgroup G}

namespace A5Config18

private theorem commutator_barSub_eq_bot (c : A5Config18 D V₀ V L K) (hV₀ : V₀ = ⊥)
    (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 D.M) :
    ⁅barSub V₀ V c.elemAbelian L, barSub V₀ V c.elemAbelian K⁆ = ⊥ := by
  subst hV₀
  have hV := c.elemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil c.pair.data.hyp.hyp125.pairFacts.le_normalizer
      c.pair.data.hyp.hyp125.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil ⊥ V := (s13_le_of_mem_calC c.pair.mem_calC_L).trans hMs
  have hKstab : K ≤ stabTil ⊥ V := (s13_le_of_mem_calC c.pair.mem_calC).trans hMs
  have hbotM : barSub ⊥ V hV (pCoreOf 2 D.M) = ⊥ :=
    barSub_pCoreOf_eq_bot_of_hyp125 c.pair.data.hyp.hyp125
  have hmap : barSub ⊥ V hV ⁅L, K⁆ = ⊥ :=
    le_bot_iff.1 (hbotM ▸ barSub_mono ⊥ V hV hcomm)
  have hlebar := commutator_barSub_le (V₀ := ⊥) (V := V) hV hLstab hKstab
  exact le_bot_iff.1 (hmap ▸ hlebar)

theorem hyp151_of_case_one (c : A5Config18 D V₀ V L K)
    (hcase : CaseOne18 D V L K c.elemAbelian) :
    Hyp151 D ⊥ V L := by
  have hcomm : commSub (commSub (⊤ : Subgroup (Vtil ⊥ V c.elemAbelian))
      (barSub ⊥ V c.elemAbelian L)) (barSub ⊥ V c.elemAbelian K) = ⊥ := hcase.2
  have hV0 : V₀ = ⊥ := c.v0
  subst hV0
  have hV := c.elemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil c.pair.data.hyp.hyp125.pairFacts.le_normalizer
      c.pair.data.hyp.hyp125.pairFacts.le_normalizer₀
  have hLbar : barSub ⊥ V hV L ∈ compBar D.M ⊥ V hV ∨ barSub ⊥ V hV L = ⊥ := by
    by_cases hb : barSub ⊥ V hV L = ⊥
    · exact Or.inr hb
    · exact Or.inl (barSub_mem_compBar_of_ne_bot c.pair.data.hyp.hyp125
        c.pair.mem_calC_L hb)
  refine ⟨c.pair.data.hyp.hyp125, s13_le_of_mem_calC c.pair.mem_calC_L, ?_, ?_, ?_⟩
  · exact CFSG.Quasithin.S151S4.twoResidual_eq_self_of_perfect c.pair.mem_calC_L.2.1
  · rcases hLbar with hc | hb
    · exact fstar_eq_self_of_isQuasisimple hc.2.2
    · rw [hb]
      exact le_bot_iff.1 (Subgroup.map_subtype_le _)
  · intro g hgM hgn
    have hLgcal : conjSubgroup L g ∈ calC D.M := by
      have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (K := L) Subgroup.le_normalizer
        c.pair.mem_calC_L (m := g) hgM
      rwa [show uniqueFourConj g L = conjSubgroup L g from rfl] at h
    have hLg : conjSubgroup L g = K := by
      rcases c.pair.calC_eq (conjSubgroup L g) hLgcal with h | h
      · exact absurd ((s15_Infra_mem_nBar_iff c.pair.data.hyp.hyp125 hV hgM).2 (by rw [h])) hgn
      · exact h
    rw [hLg]
    exact ⟨c.commutator_barSub_eq_bot rfl c.pair.commutator_le, hcomm⟩

theorem v1Sub_eq_bot_of_case_one (c : A5Config18 D V₀ V L K)
    (hcase : CaseOne18 D V L K c.elemAbelian) :
    v1Sub D.M ⊥ V c.elemAbelian L = ⊥ := by
  have hcomm : commSub (commSub (⊤ : Subgroup (Vtil ⊥ V c.elemAbelian))
      (barSub ⊥ V c.elemAbelian L)) (barSub ⊥ V c.elemAbelian K) = ⊥ := hcase.2
  have hV0 : V₀ = ⊥ := c.v0
  subst hV0
  have hV := c.elemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil c.pair.data.hyp.hyp125.pairFacts.le_normalizer
      c.pair.data.hyp.hyp125.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil ⊥ V := (s13_le_of_mem_calC c.pair.mem_calC_L).trans hMs
  have hKstab : K ≤ stabTil ⊥ V := (s13_le_of_mem_calC c.pair.mem_calC).trans hMs
  have hbsup : barSub ⊥ V hV (L ⊔ K) = barSub ⊥ V hV L ⊔ barSub ⊥ V hV K := by
    rw [barSub, barSub, barSub, Subgroup.subgroupOf_sup hLstab hKstab, Subgroup.map_sup]
  have hfix : CFSG.Quasithin.fixV (barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) = ⊥ := by
    rw [← hbsup]
    exact c.fixV
  have hCW : wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxV : x ∈ V := preTil_le ⊥ V hV _ hxW
    have hxT : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ wTil ⊥ V hV L :=
      (mem_preTil_iff_of_mem ⊥ V hV _ hxV).1 hxW
    have hfixK : wTil ⊥ V hV L ≤ CFSG.Quasithin.fixV (barSub ⊥ V hV K) :=
      commSub_eq_bot_iff.1 (hcomm)
    have hfixL : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ CFSG.Quasithin.fixV (barSub ⊥ V hV L) := by
      rw [mem_fixV]
      intro l hl
      obtain ⟨l', hl'L, rfl⟩ := (mem_barSub ⊥ V hV L l).1 hl
      rw [actTil_mk]
      have hcomm : (l' : G) * x * (l' : G)⁻¹ = x := by
        have h1 : (l' : G) * x = x * (l' : G) :=
          (Subgroup.mem_centralizer_iff.1 hxC) (l' : G) hl'L
        calc (l' : G) * x * (l' : G)⁻¹ = x * (l' : G) * (l' : G)⁻¹ := by
              rw [h1]
          _ = x := by group
      apply congrArg (mkTil ⊥ V hV)
      apply IntMod.val_injective
      rw [actStab_apply_val]
      exact hcomm
    have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈
        CFSG.Quasithin.fixV (barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) := by
      rw [FixVLat.fixV_sup_eq]
      exact Subgroup.mem_inf.2 ⟨hfixL, mem_fixV.1 (hfixK hxT)⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    have hmem1 : mkTil ⊥ V hV (IntMod.mk hV ⟨x, hxV⟩) = 1 := by
      rw [← map_one (mkTil ⊥ V hV)]
      exact hmem
    have hxmem : IntMod.mk hV ⟨x, hxV⟩ ∈ modNull ⊥ V hV :=
      (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) _).1 hmem1
    rw [mem_modNull] at hxmem
    exact hxmem
  rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
  have hbot : ∀ m : D.M, conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G))
      (m : G) = ⊥ := by
    intro m
    rw [hCW, E3.conjSubgroup_bot]
  simp [hbot]

end A5Config18

private theorem s15_eq_two_of_swap {D : Data G} {V : Subgroup G} {L K : Subgroup G}
    (c : A5Config18 D ⊥ V L K) (h151 : Hyp151 D ⊥ V L)
    (hswap : ∃ x ∈ D.M, K = conjSubgroup L x) :
    s15 D.M ⊥ V c.elemAbelian L = 2 := by
  have hV := c.elemAbelian
  have hne : barSub ⊥ V hV L ≠ barSub ⊥ V hV K := by
    intro heq
    have hcomm : ⁅barSub ⊥ V hV L, barSub ⊥ V hV K⁆ = ⊥ :=
      c.commutator_barSub_eq_bot rfl c.pair.commutator_le
    have hcentK : barSub ⊥ V hV L ≤
        Subgroup.centralizer (barSub ⊥ V hV K : Set (MulAut (Vtil ⊥ V hV))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hcent : barSub ⊥ V hV L ≤
        Subgroup.centralizer (barSub ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
      rwa [← heq] at hcentK
    have hcomm' : ∀ a b : ↥(barSub ⊥ V hV L), a * b = b * a := by
      intro a b
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent a.2) b b.2).symm
    have hcomp := barSub_mem_compBar_of_ne_bot c.pair.data.hyp.hyp125
      c.pair.mem_calC_L c.barSubL
    have hqC : CFSG.IsQuasisimple ↥(barSub ⊥ V hV L) :=
      CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2
    exact CFSG.Quasithin.Insp9.qs_not_commutative hqC hcomm'
  have hrange : Set.range (fun m : D.M => barSub ⊥ V hV (conjSubgroup L (m : G))) =
      {barSub ⊥ V hV L, barSub ⊥ V hV K} := by
    ext φ
    constructor
    · rintro ⟨m, rfl⟩
      change barSub ⊥ V hV (conjSubgroup L (m : G)) ∈ {barSub ⊥ V hV L, barSub ⊥ V hV K}
      have hcal : conjSubgroup L (m : G) ∈ calC D.M := by
        have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (K := L) Subgroup.le_normalizer
          c.pair.mem_calC_L (m := (m : G)) m.2
        rwa [show uniqueFourConj (m : G) L = conjSubgroup L (m : G) from rfl] at h
      rcases c.pair.calC_eq _ hcal with h | h
      · rw [h]; simp
      · rw [h]; simp
    · rintro (rfl | rfl)
      · refine ⟨1, ?_⟩
        change barSub ⊥ V hV (conjSubgroup L ((1 : D.M) : G)) = barSub ⊥ V hV L
        rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
      · obtain ⟨x, hxM, hK⟩ := hswap
        refine ⟨⟨x, hxM⟩, ?_⟩
        change barSub ⊥ V hV (conjSubgroup L ((⟨x, hxM⟩ : D.M) : G)) = barSub ⊥ V hV K
        rw [show ((⟨x, hxM⟩ : D.M) : G) = x from rfl]
        exact congrArg (barSub ⊥ V hV) hK.symm
  rw [s15_Core_s15_eq_ncard_range h151, hrange, Set.ncard_pair hne]

private theorem s15_eq_one_of_no_swap {D : Data G} {V : Subgroup G} {L K : Subgroup G}
    (c : A5Config18 D ⊥ V L K) (h151 : Hyp151 D ⊥ V L)
    (hnoswap : ¬ ∃ x ∈ D.M, K = conjSubgroup L x) :
    s15 D.M ⊥ V c.elemAbelian L = 1 := by
  have hV := c.elemAbelian
  have hLnorm : (L.subgroupOf D.M).Normal := by
    rcases c.pair.dichotomy with h | h
    · exact absurd h.2 hnoswap
    · exact h.2.1
  have hMn : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (s13_le_of_mem_calC c.pair.mem_calC_L)).1 hLnorm
  have hrange : Set.range (fun m : D.M => barSub ⊥ V hV (conjSubgroup L (m : G))) =
      {barSub ⊥ V hV L} := by
    ext φ
    constructor
    · rintro ⟨m, rfl⟩
      change barSub ⊥ V hV (conjSubgroup L (m : G)) ∈ {barSub ⊥ V hV L}
      rw [Quasithin.conjSubgroup_eq_iff_mem_normalizer.2 (hMn m.2)]
      simp
    · rintro rfl
      refine ⟨1, ?_⟩
      change barSub ⊥ V hV (conjSubgroup L ((1 : D.M) : G)) = barSub ⊥ V hV L
      rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
  rw [s15_Core_s15_eq_ncard_range h151, hrange, Set.ncard_singleton]

namespace A5Config18

private theorem mem_centralizer_wSub_of_case_one {D : Data G} {V : Subgroup G} {L K : Subgroup G}
    (c : A5Config18 D ⊥ V L K)
    (hcase : CaseOne18 D V L K c.elemAbelian)
    {k w : G} (hk : k ∈ K) (hw : w ∈ wSub ⊥ V c.elemAbelian L) :
    k * w * k⁻¹ = w := by
  have hcomm : commSub (commSub (⊤ : Subgroup (Vtil ⊥ V c.elemAbelian))
      (barSub ⊥ V c.elemAbelian L)) (barSub ⊥ V c.elemAbelian K) = ⊥ := hcase.2
  have hV := c.elemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil c.pair.data.hyp.hyp125.pairFacts.le_normalizer
      c.pair.data.hyp.hyp125.pairFacts.le_normalizer₀
  have hkM : k ∈ D.M := (s13_le_of_mem_calC c.pair.mem_calC) hk
  have hwV : w ∈ V := preTil_le ⊥ V hV _ hw
  have hkw : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ wTil ⊥ V hV L :=
    (mem_preTil_iff_of_mem ⊥ V hV _ hwV).1 hw
  have hKfix : wTil ⊥ V hV L ≤ CFSG.Quasithin.fixV (barSub ⊥ V hV K) :=
    commSub_eq_bot_iff.1 (hcomm)
  have hkbar : actTil ⊥ V hV ⟨k, hMs hkM⟩ ∈ barSub ⊥ V hV K :=
    actTil_mem_barSub ⊥ V hV hk (hMs hkM)
  have hfix := mem_fixV.1 (hKfix hkw) (actTil ⊥ V hV ⟨k, hMs hkM⟩) hkbar
  rw [actTil_mk] at hfix
  have h1 : (actStab ⊥ V hV ⟨k, hMs hkM⟩ (IntMod.mk hV ⟨w, hwV⟩)).val *
      (IntMod.mk hV ⟨w, hwV⟩).val⁻¹ ∈ (⊥ : Subgroup G) :=
    (mkTil_eq_iff ⊥ V hV _ _).1 hfix
  rw [Subgroup.mem_bot] at h1
  rw [actStab_apply_val] at h1
  have h2 : k * w * k⁻¹ * w⁻¹ = 1 := by
    simpa only [IntMod.mk, IntMod.val] using h1
  calc k * w * k⁻¹ = (k * w * k⁻¹ * w⁻¹) * w := by group
    _ = w := by rw [h2, one_mul]

theorem hyp154_of_case_one (c : A5Config18 D V₀ V L K)
    (hcase : CaseOne18 D V L K c.elemAbelian)
    (h151 : Hyp151 D ⊥ V L)
    (hV1 : v1Sub D.M ⊥ V c.elemAbelian L = ⊥)
    (hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥) :
    Hyp154 D ⊥ V L := by
  have hcomm : commSub (commSub (⊤ : Subgroup (Vtil ⊥ V c.elemAbelian))
      (barSub ⊥ V c.elemAbelian L)) (barSub ⊥ V c.elemAbelian K) = ⊥ := hcase.2
  have hV0 : V₀ = ⊥ := c.v0
  subst hV0
  have hV := c.elemAbelian
  have hW1c : F12.Wi 1 D.T V ≤ Subgroup.centralizer (V : Set G) := by
    rw [S17.Wi_eq_wClos 1 D.T V hV]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW1
  have hW1M : F12.Wi 1 D.T V ≤ D.M := by
    rw [S17.Wi_eq_wClos 1 D.T V hV]
    exact (iSup_le fun A => iSup_le fun hA => hA.1).trans D.sylowM.le
  have hunique₁ : ∀ w ∈ wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ Subgroup.centralizer ({w} : Set G)) := by
    intro w hw hw1
    rw [hV1, sup_bot_eq] at hw
    have hwV : w ∈ V := preTil_le ⊥ V hV _ hw
    have hle : K ⊔ F12.Wi 1 D.T V ≤ D.M ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine le_inf (sup_le (s13_le_of_mem_calC c.pair.mem_calC) hW1M) ?_
      refine sup_le ?_ ?_
      · intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hk1 : k * w * k⁻¹ = w := c.mem_centralizer_wSub_of_case_one hcase hk hw
        calc k * w = (k * w * k⁻¹) * k := by group
          _ = w * k := by rw [hk1]
      · intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.1 (hW1c hl)) w hwV).symm
    exact uc22p22u_uniqueMax_mono D hle inf_le_left c.uniqueMaxK
  refine ⟨h151, hunique₁, ?_, ?_⟩
  ·
    intro x hxM y hyM _hxy w hw hw1
    by_cases hswap : ∃ m ∈ D.M, K = conjSubgroup L m
    · have hs := s15_eq_two_of_swap c h151 hswap
      exact c23_unique₂_of_unique₁ D h151 hs hunique₁ x hxM y hyM w hw hw1
    ·
      have hs := s15_eq_one_of_no_swap c h151 hswap
      have hcard : (Set.range (fun n : D.M =>
          barSub ⊥ V hV (conjSubgroup L (n : G)))).ncard = 1 := by
        rw [← s15_Core_s15_eq_ncard_range h151]
        exact hs
      obtain ⟨A, hA⟩ := Set.ncard_eq_one.1 hcard
      have hbase : barSub ⊥ V hV L ∈
          Set.range (fun k : D.M => barSub ⊥ V hV (conjSubgroup L (k : G))) := by
        refine ⟨1, ?_⟩
        change barSub ⊥ V hV (conjSubgroup L ((1 : D.M) : G)) = barSub ⊥ V hV L
        rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
      have hLimage : ∀ n ∈ D.M, barSub ⊥ V hV (conjSubgroup L (n : G)) =
          barSub ⊥ V hV L := by
        intro n hn
        have h1 : barSub ⊥ V hV (conjSubgroup L (n : G)) ∈
            Set.range (fun k : D.M => barSub ⊥ V hV (conjSubgroup L (k : G))) :=
          ⟨⟨n, hn⟩, rfl⟩
        rw [hA, Set.mem_singleton_iff] at h1 hbase
        exact h1.trans hbase.symm
      have hWconj : ∀ n ∈ D.M, wSub ⊥ V hV (conjSubgroup L (n : G)) = wSub ⊥ V hV L := by
        intro n hn
        unfold wSub
        rw [show wTil ⊥ V hV (conjSubgroup L (n : G)) = wTil ⊥ V hV L from by
          unfold wTil
          rw [hLimage n hn]]
      have hbot : (⨆ X ∈ {X : Subgroup G | X ∈ wConj D.M ⊥ V hV L ∧
          X ≠ conjSubgroup (wSub ⊥ V hV L) x ∧
          X ≠ conjSubgroup (wSub ⊥ V hV L) y}, X) = ⊥ := by
        refine iSup_eq_bot.mpr fun X => ?_
        by_cases hX : X ∈ {X : Subgroup G | X ∈ wConj D.M ⊥ V hV L ∧
            X ≠ conjSubgroup (wSub ⊥ V hV L) x ∧
            X ≠ conjSubgroup (wSub ⊥ V hV L) y}
        · exfalso
          obtain ⟨hXw, hXx, -⟩ := hX
          obtain ⟨m, hm, rfl⟩ := hXw
          have hMs : D.M ≤ stabTil ⊥ V :=
            le_stabTil c.pair.data.hyp.hyp125.pairFacts.le_normalizer
              c.pair.data.hyp.hyp125.pairFacts.le_normalizer₀
          have hmstab : (m : G) ∈ stabTil ⊥ V := hMs hm
          have hxstab : x ∈ stabTil ⊥ V := hMs hxM
          have hmW : conjSubgroup (wSub ⊥ V hV L) (m : G) = wSub ⊥ V hV L := by
            rw [← s15_Infra_wSub_conjSubgroup ⊥ V L hV hmstab, hWconj m hm]
          have hxW : conjSubgroup (wSub ⊥ V hV L) x = wSub ⊥ V hV L := by
            rw [← s15_Infra_wSub_conjSubgroup ⊥ V L hV hxstab, hWconj x hxM]
          exact hXx (hmW.trans hxW.symm)
        · exact iSup_neg hX
      rw [hV1, bot_sup_eq] at hw
      rw [hbot] at hw
      exact absurd (Subgroup.mem_bot.1 hw) hw1
  ·
    intro g hgM X hX Y hY hXY hne
    have hγ2 := two_le_gamma15 D h151 hV c.barSubL
    by_cases hswap : ∃ m ∈ D.M, K = conjSubgroup L m
    · refine ⟨s15_eq_two_of_swap c h151 hswap, ?_⟩
      have hδ0 : delta15 D.M ⊥ V hV L = 0 := by
        rw [delta15, hV1, bot_inf_eq, mSub]
        exact rk_bot
      omega
    · exfalso
      have hs := s15_eq_one_of_no_swap c h151 hswap
      have hcard : (wConj D.M ⊥ V hV L).ncard = 1 := by
        rw [ncard_wConj D h151 hV]
        exact hs
      obtain ⟨A, hA⟩ := Set.ncard_eq_one.1 hcard
      have hXA : X = A := by
        have h1 : X ∈ ({A} : Set (Subgroup G)) := hA ▸ hX
        simpa using h1
      have hYA : Y = A := by
        have h1 : Y ∈ ({A} : Set (Subgroup G)) := hA ▸ hY
        simpa using h1
      exact hXY (hXA.trans hYA.symm)

theorem false_of_case_one (c : A5Config18 D V₀ V L K)
    (hcase : CaseOne18 D V L K c.elemAbelian)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h111 : W3Thm111 G) (h1513 : R15_13Small D) : False := by
  have hV0 : V₀ = ⊥ := c.v0
  subst hV0
  have hV := c.elemAbelian
  have h151 : Hyp151 D ⊥ V L := c.hyp151_of_case_one hcase
  have hV1 : v1Sub D.M ⊥ V hV L = ⊥ := c.v1Sub_eq_bot_of_case_one hcase
  have hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥ :=
    c.pair.wOne_commute rfl h1669 h111 (by rw [c.numerics.2.1])
  have h154 : Hyp154 D ⊥ V L := c.hyp154_of_case_one hcase h151 hV1 hW1
  have hbar : barSub ⊥ V hV L ≠ ⊥ := c.barSubL
  obtain ⟨hγ3, -⟩ := h1513 ⊥ V L h154 (by rw [mSub, rk_bot]; omega) hbar
  have hδ1 : delta15 D.M ⊥ V hV L ≤ 1 := by
    rw [delta15, hV1, bot_inf_eq, mSub]
    rw [rk_bot]
    norm_num
  have hact := exists_involution_not_le_fixV c.pair.data.hyp h151 hbar
  have hmle := mBar_le_gamma15 D h151 hδ1 hact
  have hm4 : mBar D.M ⊥ V hV = 4 := c.numerics.1
  omega

end A5Config18

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
