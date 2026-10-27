module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SBar
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SJ

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section KP4


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}
  [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem B_bar_facts (h : Cfg A c L R S J) :
    CFSG.Open.IsElemAbelian 3 (img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L)) ∧
      Nat.card (img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L)) = 9 ∧
      img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L) ≤
        img148 A (Subgroup.normalizer (S : Set G)) (L ⊓ Subgroup.normalizer (R : Set G)) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  have hA : IsE27 A := h.pt.std.isE27
  obtain ⟨-, -, hAR, -⟩ := h.pt.R_facts h.R_mem
  have hB : CFSG.Open.IsElemAbelian 3 (A ⊓ L) :=
    Sec4.Ronan431.isElemAbelian_of_le hA.1 inf_le_left
  refine ⟨CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hB) _, ?_,
    img148_mono (B_le_K hAR)⟩
  have hBMA : A ⊓ L ≤ M ⊔ A := inf_le_left.trans le_sup_right
  rw [img148, card_map_eq_of_ker148, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBMA).toEquiv,
    h.pt.card_B]
  intro x hx h1
  rw [mk'_ker148_eq_one_iff] at h1
  apply Subtype.ext
  have hx3 : (x : G) ^ 3 = 1 := hA.1.2 _ (Subgroup.mem_subgroupOf.mp hx).1
  exact eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 M) h1 (k := 1)
    (by rw [pow_one]; exact hx3)

theorem eq_one_of_mem_B_of_commute (h : Cfg A c L R S J)
    {x : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸ ker148 A (Subgroup.normalizer (S : Set G))}
    (hx : x ∈ img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L))
    (hcomm : ∀ k ∈ img148 A (Subgroup.normalizer (S : Set G))
      (L ⊓ Subgroup.normalizer (R : Set G)), k * x = x * k) : x = 1 := by
  obtain ⟨-, -, hBK⟩ := h.B_bar_facts
  obtain ⟨φ⟩ := h.nonempty_K_equiv
  have hsimple6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
    have : Nontrivial (alternatingGroup (Fin 6)) := hsimple6.toNontrivial
    obtain ⟨a, b, hab⟩ := Main148.exists_ne_comm_of_isPerfect isPerfect_alternatingGroup_six
    rcases (Subgroup.center (alternatingGroup (Fin 6))).normal_of_characteristic.eq_bot_or_eq_top
      with h0 | h0
    · exact h0
    · exfalso
      have ha : a ∈ Subgroup.center (alternatingGroup (Fin 6)) := h0 ▸ Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  have hxK := hBK hx
  have hz : (⟨x, hxK⟩ : ↥(img148 A (Subgroup.normalizer (S : Set G))
      (L ⊓ Subgroup.normalizer (R : Set G)))) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hcomm k k.2)
  have hφz : φ ⟨x, hxK⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := congrArg φ (hz (φ.symm g))
    simpa using this
  rw [hZ6, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hφz
  exact congrArg Subtype.val hφz

theorem zpowers_eq_inf_centralizer_K (h : Cfg A c L R S J) :
    Subgroup.zpowers (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A) =
      img148 A (Subgroup.normalizer (S : Set G)) A ⊓
        Subgroup.centralizer (img148 A (Subgroup.normalizer (S : Set G))
          (L ⊓ Subgroup.normalizer (R : Set G)) :
            Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
              ker148 A (Subgroup.normalizer (S : Set G)))) := by
  have hA : IsE27 A := h.pt.std.isE27
  obtain ⟨hBe, hB9, hBK⟩ := h.B_bar_facts
  exact Sec4.Ronan431.zpowers_eq_inf_centralizer (h.pRank_le ⊤) (img148_isE27 hA)
    (alpha148_mem_img148 h.pt.mem_A)
    (Main148.alpha148_ne_one h.pt.mem_A h.c_ne_one (hA.1.2 c h.pt.mem_A))
    (h.K_le_centralizer.1.trans inf_le_right) hBK hBe hB9
    (fun x hx hcomm => h.eq_one_of_mem_B_of_commute hx hcomm)

theorem normal_J (h : Cfg A c L R S J) :
    (img148 A (Subgroup.normalizer (S : Set G)) J).Normal := by
  obtain ⟨hBe, hB9, hBK⟩ := h.B_bar_facts
  have hJc : IsComponent (img148 A (Subgroup.normalizer (S : Set G)) J) :=
    Ronan148J.isComponent_img148_of_three_dvd h.A_le_NM h.J_mem h.three_dvd_card_J
  have hKJ := img148_mono (A := A) (Y := Subgroup.normalizer (S : Set G)) h.K_le
  exact Sec4.Ronan431.normal_of_pRank_le (h.pRank_le ⊤) hJc (hBK.trans hKJ) hBe hB9
    (fun x hx hcomm => h.eq_one_of_mem_B_of_commute hx (fun k hk => hcomm k (hKJ hk)))

end Cfg

end KP4

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
