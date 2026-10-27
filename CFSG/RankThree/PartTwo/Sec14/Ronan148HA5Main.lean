module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HA5Theta1
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HA5RowsChar2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem sixty_dvd_card_of_A5 {X : Type} [Group X] {F : Subgroup X}
    (hF : Nonempty (F ⧸ aschbacherSolvableCore 3 F ≃* alternatingGroup (Fin 5))) :
    60 ∣ Nat.card F := by
  obtain ⟨e⟩ := hF
  have h60 : Nat.card (↥F ⧸ aschbacherSolvableCore 3 ↥F) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; rfl
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥F), h60]
  exact Dvd.intro _ rfl

namespace A5Cfg

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P : Subgroup X} {q : X} {M F : Subgroup X}

theorem a5Data (h : A5Cfg P q M F) (hθ : aschbacherSolvableCore 3 ↥M = ⊥) (hne : M ≠ ⊤) :
    A5Data ↥M := by
  have hqN : q ∈ Subgroup.normalizer (M : Set X) := h.PM h.qP
  refine ⟨IsQuasisimple.of_mulEquiv (equivThetaQuotOfBot hθ).symm h.Mq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← card_X h.triple]
    exact Subgroup.card_subgroup_dvd_card M
  · intro hc
    exact hne (Subgroup.eq_top_of_card_eq M (by rw [hc, card_X h.triple]))
  · intro E hE
    have hinj : Function.Injective M.subtype := M.subtype_injective
    have hEX : CFSG.Assembly.IsElemAbelian 2 (E.map M.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
        obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
        apply Subtype.ext
        change (x : X) * y = y * x
        rw [← hux, ← hvy, ← map_mul, ← map_mul]
        exact congrArg M.subtype (congrArg Subtype.val (hE.1.is_comm.comm (⟨u, hu⟩ : E) ⟨v, hv⟩))
      · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
        rw [← map_pow, hE.2 u hu, map_one]
    have h8 := card_le_eight_of_isTripleCover h.triple _ hEX
    rwa [Subgroup.card_map_of_injective hinj] at h8
  · intro hZ R hR
    exact isElemAbelian_of_isPGroup_of_inf h.triple (inf_center_eq_bot hZ) hR
  · refine ⟨conjAut hqN, F.subgroupOf M, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← conjAut_pow hqN 3]
      apply (conjAut_eq_one_iff _).mpr
      intro l _
      rw [h.q_cube]
      group
    · intro h1
      apply h.qs
      refine ⟨h.qP, fun y hy => ?_⟩
      have hθM : inSubgroup (aschbacherSolvableCore 3) M = ⊥ := by
        rw [inSubgroup, hθ, Subgroup.map_bot]
      rw [hθM, Subgroup.mem_bot]
      have := (conjAut_eq_one_iff hqN).mp h1 y hy
      rw [this]
      group
    · intro x hx
      apply Subtype.ext
      rw [coe_conjAut_apply]
      have hxq : (x : X) * q = q * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (h.Fq (Subgroup.mem_subgroupOf.mp hx))
      rw [← hxq]
      group
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.FM).toEquiv]
      exact sixty_dvd_card_of_A5 h.FA5
    · intro x hx hx3 hxc
      have hxF : (x : X) ∈ F := Subgroup.mem_subgroupOf.mp hx
      set x' : ↥F := ⟨x, hxF⟩
      have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using congrArg Subtype.val hx3)
      by_contra hx1
      have hx'1 : x' ≠ 1 := fun h1 => hx1 (Subtype.ext (congrArg Subtype.val h1 : (x : X) = 1))
      refine h.not_mem_center_of_cube hx'3 hx'1 (Subgroup.mem_center_iff.mpr fun g => ?_)
      apply Subtype.ext
      have hg : (⟨g, h.FM g.2⟩ : ↥M) ∈ F.subgroupOf M := Subgroup.mem_subgroupOf.mpr g.2
      have := congrArg Subtype.val (hxc _ hg)
      exact this.symm

end A5Cfg

section Main

set_option linter.unusedSectionVars false


theorem item464OneA5K_holds : Item464OneA5K := by
  intro X _ _ hperf hT P hP q hqP hqZ M F hPM hMp hMq hlist hFM hFq hFp hFA5 hqs
  have h : A5Cfg P q M F := ⟨hperf, hT, hP, hqP, hqZ, hPM, hMp, hMq, hFM, hFq, hFp, hFA5, hqs⟩
  have hθ : aschbacherSolvableCore 3 ↥M = ⊥ := by
    have := h.thetaM_eq_bot
    rwa [A5Cfg.thetaM, inSubgroup, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
      at this
  by_contra hne
  exact a5_of_rows a5Rows_holds ↥M (h.a5Data hθ hne)
    (Sec21.Item223PrintProof.isList46_of_mulEquiv (equivThetaQuotOfBot hθ) hlist)


theorem step148HJTypeYdONA5_of_items (h131 : Sec13.Item131) (h134 : Sec13.Item134)
    (h48 : Sec4.Item4_8)
    (h46 : Sec4.Item4_6) : Step148HJTypeYdONA5 :=
  step148HJTypeYdONA5_of_res h131 h134 h48 h46 item464OneA5K_holds

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
