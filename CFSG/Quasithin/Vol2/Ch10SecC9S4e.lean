module

public import CFSG.Quasithin.Vol2.Ch10SecC9Case5
public import CFSG.Quasithin.Vol2.Ch10SecC9S4d
public import CFSG.Quasithin.Vol2.Ch10SecC9S3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

omit [Finite G] in
theorem le_normalizer_conjugate_of' {W : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    L ≤ Subgroup.normalizer (CFSG.conjugate W s : Set G) := by
  intro l hl
  have hsl : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hs l).mp hl
  have hw : CFSG.conjugate W (s * l * s⁻¹) = W := SecA.conjugate_eq_self_iff.mpr (hLW hsl)
  rw [← SecA.conjugate_eq_self_iff, SecA.conjugate_conjugate,
    show s * l = (s * l * s⁻¹) * s by group, ← SecA.conjugate_conjugate, hw]

namespace Conf

variable (c : Conf T L I t w J)
include c

theorem centralizer_VI_le (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1026 : Stmt10_2_6)
    (h1027 : Stmt10_2_7) (hK8a : FactK8a) (hK8b : FactK8b) :
    Subgroup.centralizer (VI T L I J w : Set G) ≤ fsuM T L := by
  have hyp := c.hyp
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G) with hTw
  have hTw1 : Tw ≤ T1 T L := c.Tw_le_T1 h37 h38
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hV1T : fsuUL T L I ≤ T := hV1V.trans (SecA.fsuVM_le_T hyp)
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hTwV1 : Tw ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_sup_right.trans (c.le_normalizer_fsuUL' h37 h38)
  by_cases hC : cV1 T L I = ⊥
  ·
    apply centralizer_le_of_fsuUL_le hyp h1026
    have hC' : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuUL T L I) = ⊥ :=
      (cV1_eq h37 h38 hyp h1011 c.ht c.htn) ▸ hC
    have hLVI : L ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
      c.le.trans (le_sup_left.trans (le_normalizer_VI T L I J w))
    have hTwVI : Tw ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
      le_sup_right.trans (le_normalizer_VI T L I J w)
    have hLY : L ≤ Subgroup.normalizer ((VI T L I J w ⊓ fsuUL T L I : Subgroup G) : Set G) :=
      fun l hl => mem_normalizer_inf' (hLVI hl) (le_normalizer_fsuUL T L I hl)
    have hTwY : Tw ≤ Subgroup.normalizer ((VI T L I J w ⊓ fsuUL T L I : Subgroup G) : Set G) :=
      fun s hs => mem_normalizer_inf' (hTwVI hs) (hTwV1 hs)
    have hfix : fsuUL T L I ⊓ Subgroup.centralizer (Tw : Set G) ≤
        VI T L I J w ⊓ fsuUL T L I := le_inf (le_conjClosure _ _) inf_le_left
    rcases irrG_or_case5 (modCase_of h37 h38 hyp h1011 h1027 c.ht c.htn) hC' hK8a hK8b with
      hirr | ⟨s, hs, W, -, hLW, hsup, hinf, hirrW, hni⟩
    · obtain ⟨u, huV, hu1, huC⟩ :=
        exists_mem_centralizer_ne_one hT2 hV1T inf_le_left hTwV1 hirr.1
      rcases hirr.2 _ inf_le_right hLY with h | h
      · exfalso
        have hu : u ∈ VI T L I J w ⊓ fsuUL T L I := hfix ⟨huV, huC⟩
        rw [h, Subgroup.mem_bot] at hu
        exact hu1 hu
      · exact h ▸ inf_le_left
    · have hc : ∀ a ∈ W ⊔ CFSG.conjugate W s, ∀ b ∈ W ⊔ CFSG.conjugate W s, a * b = b * a :=
        fun a ha b hb => fsuVM_comm hyp (hV1V (hsup ▸ ha)) (hV1V (hsup ▸ hb))
      have key := le_of_case5 (T := Tw) (P := T) (Y := VI T L I J w ⊓ fsuUL T L I) hc hinf hLW
        (le_normalizer_conjugate_of' hs hLW) hirrW (irrG_conjugate hirrW hs) hni
        (by rw [hsup]; exact inf_le_right) hLY hTwY (hTw1.trans inf_le_right)
        (by rw [hsup]; exact hTwV1) hT2 (by rw [hsup]; exact hV1T) inf_le_left
        (by rw [hsup]; exact hfix)
      rw [hsup] at key
      exact key.trans inf_le_left
  ·
    obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC
    have hU : fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≠ ⊥ := by
      intro h
      have hv' : (v : G) ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) :=
        ⟨v.2, Subgroup.mem_subgroupOf.mp hv⟩
      rw [h, Subgroup.mem_bot] at hv'
      exact hv1 (Subtype.ext (Subtype.ext hv'))
    have hT1U : T1 T L ≤ Subgroup.normalizer
        ((fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) : Subgroup G) : Set G) :=
      fun s hs => mem_normalizer_inf' (T1_le_normalizer_fsuUL T L I hs)
        (mem_normalizer_centralizer' (SecA.le_fsuM T L hs.1))
    obtain ⟨z, hzU, hz1, hzC⟩ :=
      exists_mem_centralizer_ne_one hT2 (inf_le_left.trans hV1T) inf_le_left hT1U hU
    have hzVI : z ∈ VI T L I J w := le_conjClosure _ _
      ⟨hzU.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTw1) hzC⟩
    refine centralizer_le_of_mem hyp h1026 hzVI hz1
      ((SecA.isElemAbelian_fsuVM hyp).2 z (hV1V hzU.1)) (sup_le ?_ ?_)
    · intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hzU.2 l hl)
    · intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hzC l hl)

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
