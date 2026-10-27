module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HSym
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Mirror

variable {G : Type} [Group G] [Finite G]

theorem mirror_of_symData (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hK : KFacts.KS12NormalizerMoves) {A L K S : Subgroup G} {c b a : G}
    (cfg : Cfg129 G A c L b a K S) {x : G} (hxD : x ∈ D129 a b)
    (hxb : x ∉ Subgroup.zpowers b) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 x)
    (hD : SymData129 A c x Y)
    (hlt : ¬ (resCent Y c ⊔ inSubgroup (aschbacherSolvableCore 3) Y = Y)) (hSY : S ≤ Y)
    {q'' : TauCeti.PrimePower}
    (hq1 : Sec4.IsSLThreePiAt (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c))
      q''.card)
    (hq2 : Sec4.IsoGTwo (Y ⧸ CFSG.pCore 2 Y) q'') :
    ∃ J : Subgroup G, Cfg129 G A c J x b Y S ∧ GTwoType129At J Y q'' ∧ b ∈ J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hcA := hstd.mem_A
  have hc1 := hstd.ne_one
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hxB := cfg.not_mem_B_of_mem_D hxD hxb
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hstd.mem_thetaComponentsAt
  have hcB : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hstd.mem_L hLc
  have hxc : x ∉ Subgroup.zpowers c := fun h => hxB ((Subgroup.zpowers_le.mpr hcB) h)
  obtain ⟨J, hJ, hIJ, hJL, hJeq, hCeq, hxL, hbJ, hAJ, hJ'eq, hj⟩ :=
    sym_core h45 h48 cfg hxD hxb hY hD
  have hcJ : c ∈ J := hIJ hD.mem
  obtain ⟨eJ⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hIJ hJeq
  have hqJ : Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) q''.card :=
    isSLThreePiAt_congr eJ hq1
  have hxAJ : x ∈ A ⊓ Sec4.thetaQuotCentralizer J := hCeq ▸ ⟨hxA, hxL⟩
  have hstdJ : Sec12StdBar G A c J :=
    { toPartTwoStanding := hstd.toPartTwoStanding
      partTwoF_eq := hstd.partTwoF_eq
      isE27 := hstd.isE27
      mem_A := hcA
      ne_one := hc1
      mem_thetaComponentsAt := hJ
      mem_L := hcJ
      card_B := by rw [hCeq]; exact card_inf_eq_nine_of_list hstd cfg.list
      sup_eq := by
        obtain ⟨j, hjAJ, hjL⟩ := hj
        have hB9 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer J : Subgroup G) = 9 := by
          rw [hCeq]; exact card_inf_eq_nine_of_list hstd cfg.list
        exact eq_of_card_nine_lt hA27 (sup_le inf_le_left inf_le_left) le_sup_left hB9
          (Subgroup.mem_sup_right hjAJ) (by rw [hCeq]; exact hjL)
      exists_sylow := by
        obtain ⟨P, hP, hPB⟩ := hstd.exists_sylow
        refine ⟨P, hP, fun hle => ?_⟩
        have hZ := card_center_eq_three_of_list cfg.list
        obtain ⟨hPaut, hP9⟩ := autIn_eq_transvectionGroup_bar h45 hstd hZ
          (fun T hT hT9 hZT => hK _ (isQuasisimple_thetaQuot_of_mem hstd.mem_thetaComponentsAt)
            cfg.list T hT hT9 hZT) hP hPB
        obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp (hle hxAJ)
        have hPx : ∀ g ∈ P, g * x = x * g := fun g hg => by
          have h1 := Subgroup.mem_center_iff.mp hp ⟨g, hg⟩
          have h2 := congrArg Subtype.val h1
          simpa [← hpx] using h2
        have hfix : ∀ σ ∈ Sec4.autIn P A, σ ⟨x, hxA⟩ = ⟨x, hxA⟩ := by
          intro σ hσ
          obtain ⟨g, hgN, hgP, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
          apply Subtype.ext
          rw [Sec4.normalizerMonoidHom_apply_coe, hPx g hgP, mul_inv_cancel_right]
        have hcx : c ∉ Subgroup.zpowers x := fun h =>
          hxc (mem_of_mem_zpowers_of_ne_one (orderOf_eq_prime hx3 hx1) h hc1
            (Subgroup.mem_zpowers c))
        have h3 := Proof128.card_le_three_of_le_transvectionGroup hAe hA27 hxA hcA hx1 hc1 hcx
          (S := Sec4.autIn P A) hPaut.le hfix
        omega }
  have hSD : S ≤ Subgroup.centralizer ((D129 b x : Subgroup G) : Set G) := by
    refine cfg.hS_cent.trans (Subgroup.centralizer_le ?_)
    intro y hy
    have hDD : D129 b x ≤ D129 a b := sup_le (le_sup_right) (Subgroup.zpowers_le.mpr hxD)
    exact hDD hy
  have hcfg : Cfg129 G A c J x b Y S :=
    { std := hstdJ
      mem_E := cfg.mem_E
      mem_S := cfg.mem_S
      list := Or.inl ⟨q''.card, hqJ⟩
      hb := hxAJ
      hb_not := hxc
      hK := hY
      hIK := by rw [hJ'eq]; exact (resCent_le Y c).trans (inf_le_left)
      hlt := by rw [hJ'eq]; exact hlt
      ha := ⟨hbA, hbJ⟩
      ha_not := cfg.hb_not
      hS_le := hSY
      hS2 := cfg.hS2
      hS_ne := cfg.hS_ne
      hS_norm := cfg.hS_norm
      hS_cent := hSD
      hS_comm := cfg.hS_comm }
  exact ⟨J, hcfg, ⟨hqJ, Or.inl hq2⟩, hbJ⟩

end Mirror

end CFSG.RankThree.PartTwo.Sec12
