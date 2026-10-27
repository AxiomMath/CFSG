module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.FiveCentralA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem eq_one_of_mem_centQuot_fixV {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hL : IsAlt ↥L 5) {x : MulAut W} (hx : x ∈ L)
    (hxc : x ∈ centQuot (fixV L)) : x = 1 := by
  set C := fixV L with hC
  obtain ⟨e⟩ := hL
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup ↥L := MulEquiv.isSimpleGroup e
  have htop : commutator ↥L = ⊤ :=
    (CFSG.Fischer.commutator_eq_top_congr e).mpr
      (commutator_alternatingGroup_eq_top (α := Fin 5) (by simp))
  set N : Subgroup ↥L := (centQuot C).subgroupOf L with hN
  have hNnormal : N.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hnc : (n : MulAut W) ∈ centQuot C := Subgroup.mem_subgroupOf.mp hn
    refine Subgroup.mem_subgroupOf.mpr ?_
    simpa using conj_mem_centQuot
      (fun c hc => by rw [mem_fixV.mp hc g.1 g.2]; exact hc) hnc
  haveI : N.Normal := hNnormal
  have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have haL : (a : MulAut W) ∈ L := a.2
    have hac : (a : MulAut W) ∈ centQuot C := Subgroup.mem_subgroupOf.mp ha
    have hbL : (b : MulAut W) ∈ L := b.2
    have hbc : (b : MulAut W) ∈ centQuot C := Subgroup.mem_subgroupOf.mp hb
    have hcomm : (a : MulAut W) * (b : MulAut W) = (b : MulAut W) * (a : MulAut W) := by
      ext v
      have hbC : (b : MulAut W) v * v⁻¹ ∈ C := mem_centQuot.mp hbc v
      have haC : (a : MulAut W) v * v⁻¹ ∈ C := mem_centQuot.mp hac v
      have hafix : (a : MulAut W) ((b : MulAut W) v * v⁻¹) = (b : MulAut W) v * v⁻¹ :=
        mem_fixV.mp hbC (a : MulAut W) haL
      have hbfix : (b : MulAut W) ((a : MulAut W) v * v⁻¹) = (a : MulAut W) v * v⁻¹ :=
        mem_fixV.mp haC (b : MulAut W) hbL
      calc (a : MulAut W) ((b : MulAut W) v)
          = (a : MulAut W) (((b : MulAut W) v * v⁻¹) * v) := by rw [show
              ((b : MulAut W) v * v⁻¹) * v = (b : MulAut W) v by group]
        _ = (a : MulAut W) ((b : MulAut W) v * v⁻¹) * (a : MulAut W) v := map_mul _ _ _
        _ = ((b : MulAut W) v * v⁻¹) * (a : MulAut W) v := by rw [hafix]
        _ = ((a : MulAut W) v * v⁻¹) * (b : MulAut W) v := by ac_rfl
        _ = (b : MulAut W) ((a : MulAut W) v * v⁻¹) * (b : MulAut W) v := by rw [hbfix]
        _ = (b : MulAut W) (((a : MulAut W) v * v⁻¹) * v) := (map_mul _ _ _).symm
        _ = (b : MulAut W) ((a : MulAut W) v) := by rw [show
              ((a : MulAut W) v * v⁻¹) * v = (a : MulAut W) v by group]
    exact Subtype.ext hcomm
  rcases Subgroup.Normal.eq_bot_or_eq_top N with hbot | htopN
  · have hxN : (⟨x, hx⟩ : ↥L) ∈ N := Subgroup.mem_subgroupOf.mpr hxc
    rw [hbot] at hxN
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxN)
  · exfalso
    have hcommL : ∀ a b : ↥L, a * b = b * a := by
      intro a b
      exact hNcomm a (by rw [htopN]; exact Subgroup.mem_top a)
        b (by rw [htopN]; exact Subgroup.mem_top b)
    have habel : IsMulCommutative ↥L := ⟨⟨hcommL⟩⟩
    have hbotL : commutator ↥L = ⊥ := (commutator_eq_bot_iff (G := ↥L)).mpr habel
    exact top_ne_bot (show (⊤ : Subgroup ↥L) = ⊥ by rw [← htop, hbotL])

theorem isAlt_autQuot_fixV {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (hL : IsAlt ↥L 5) : IsAlt ↥(autQuot L (fixV L)) 5 := by
  set C := fixV L with hC
  have hAlt : IsAlt ↥L 5 := hL
  obtain ⟨e⟩ := hL
  have hLstab : L ≤ stabSub C :=
    fun l hl => centSub_le_stabSub C (fun c hc => mem_fixV.mp hc l hl)
  let ρ : ↥L →* ↥(autQuot L C) :=
    ((quotHom C).comp (Subgroup.inclusion hLstab)).codRestrict (autQuot L C)
      (fun l => mem_autQuot.mpr ⟨Subgroup.inclusion hLstab l, l.2, rfl⟩)
  have hinj : Function.Injective ρ := by
    intro a b hab
    have h1 : ρ (a * b⁻¹) = 1 := by
      rw [map_mul, hab]
      exact mul_inv_cancel (ρ b)
    have h2 : ((quotHom C) (Subgroup.inclusion hLstab (a * b⁻¹)) : MulAut (W ⧸ C)) = 1 := by
      simpa [ρ] using congrArg Subtype.val h1
    have h3 : Subgroup.inclusion hLstab (a * b⁻¹) ∈ (quotHom C).ker :=
      MonoidHom.mem_ker.mpr h2
    rw [ker_quotHom, Subgroup.mem_subgroupOf] at h3
    have h5 : ((a * b⁻¹ : ↥L) : MulAut W) ∈ centQuot C := by
      simpa using h3
    have h6 : (a * b⁻¹ : ↥L) = 1 :=
      Subtype.ext (eq_one_of_mem_centQuot_fixV hAlt (a * b⁻¹).2 h5)
    have h7 := congrArg (fun z : ↥L => z * b) h6
    simpa using h7
  have hsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨g, hg, hgeq⟩ := mem_autQuot.mp y.2
    refine ⟨⟨(g : MulAut W), hg⟩, Subtype.ext ?_⟩
    show (quotHom C (Subgroup.inclusion hLstab ⟨(g : MulAut W), hg⟩) : MulAut (W ⧸ C)) = y.1
    have hg' : Subgroup.inclusion hLstab ⟨(g : MulAut W), hg⟩ = g := Subtype.ext rfl
    rw [hg', hgeq]
  exact ⟨(MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩).symm.trans e⟩

theorem fixV_autQuot_fixV_eq_bot {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hQ : QuadTrivial L) : fixV (autQuot L (fixV L)) = ⊥ := by
  set C := fixV L with hC
  have hLstab : L ≤ stabSub C :=
    fun l hl => centSub_le_stabSub C (fun c hc => mem_fixV.mp hc l hl)
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective C v
  have hw : ∀ l ∈ L, l w * w⁻¹ ∈ C := by
    intro l hl
    have h := hv (quotHom C ⟨l, hLstab hl⟩) (mem_autQuot.mpr ⟨⟨l, hLstab hl⟩, hl, rfl⟩)
    rw [QuotientGroup.mk'_apply, quotHom_mk] at h
    exact (mk_eq_mk_iff _ _).mp h
  set J := Subgroup.closure {w} ⊔ C with hJ
  have hJs : StableUnder L J := by
    intro l hl u hu
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, hc l hl]
    refine J.mul_mem ?_ (le_sup_right (α := Subgroup W) hc)
    obtain ⟨k, rfl⟩ := Subgroup.mem_closure_singleton.mp ha
    rw [map_zpow]
    refine J.zpow_mem ?_ k
    have hlw : l w = (l w * w⁻¹) * w := by group
    rw [hlw]
    exact J.mul_mem (le_sup_right (α := Subgroup W) (hw l hl))
      (le_sup_left (α := Subgroup W) (Subgroup.mem_closure_singleton.mpr ⟨1, by simp⟩))
  have hJc : commSub J L ≤ fixV L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, hc l hl, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    obtain ⟨k, rfl⟩ := Subgroup.mem_closure_singleton.mp ha
    rw [map_zpow, ← inv_zpow, ← mul_zpow]
    exact C.zpow_mem (hw l hl) k
  have h0 := hQ J hJs hJc
  have hwJ : w ∈ C := by
    have hwmem : w ∈ J :=
      le_sup_left (α := Subgroup W) (Subgroup.mem_closure_singleton.mpr ⟨1, by simp⟩)
    exact commSub_eq_bot_iff.mp h0 hwmem
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hwJ

theorem rkIdx_fixV_zpowers_quotHom_le {W : Type} [CommGroup W] [Finite W] {C : Subgroup W}
    {t : MulAut W} (ht : t ∈ stabSub C) :
    rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨t, ht⟩))) ≤
      rkIdx (fixV (Subgroup.zpowers t)) := by
  have hle : (fixV (Subgroup.zpowers t)).map (QuotientGroup.mk' C) ≤
      fixV (Subgroup.zpowers (quotHom C ⟨t, ht⟩)) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_fixV_zpowers_iff_apply]
    have htv : t v = v := mem_fixV_zpowers_iff_apply.mp hv
    rw [QuotientGroup.mk'_apply, quotHom_mk, htv]
  have hdvd1 : (fixV (Subgroup.zpowers (quotHom C ⟨t, ht⟩))).index ∣
      ((fixV (Subgroup.zpowers t)).map (QuotientGroup.mk' C)).index :=
    Subgroup.index_dvd_of_le hle
  have hdvd2 : ((fixV (Subgroup.zpowers t)).map (QuotientGroup.mk' C)).index ∣
      (fixV (Subgroup.zpowers t)).index :=
    Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective C)
  unfold rkIdx
  exact (padicValNat_two_le_of_dvd
      (Subgroup.index_ne_zero_of_finite
        (H := (fixV (Subgroup.zpowers t)).map (QuotientGroup.mk' C))) hdvd1).trans
    (padicValNat_two_le_of_dvd
      (Subgroup.index_ne_zero_of_finite (H := fixV (Subgroup.zpowers t))) hdvd2)

theorem commSub_le_fixV_of_commute_of_isAlt_five {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsAlt ↥L 5) {t : MulAut W}
    (htL : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (hnc : ∃ x ∈ L, t * x ≠ x * t)
    (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3) {c : MulAut W} (hc5 : c ^ 5 = 1)
    (hcL : ∀ x ∈ L, c * x = x * c) :
    commSub (⊤ : Subgroup W) (Subgroup.zpowers c) ≤ fixV L := by
  set C := fixV L with hC
  have hAlt : IsAlt ↥L 5 := hL
  obtain ⟨e⟩ := hL
  have htop : commutator ↥L = ⊤ :=
    (CFSG.Fischer.commutator_eq_top_congr e).mpr
      (commutator_alternatingGroup_eq_top (α := Fin 5) (by simp))
  have hQ : QuadTrivial L := quadTrivial_of_commutator_eq_top htop
  have hLstab : L ≤ stabSub C :=
    fun l hl => centSub_le_stabSub C (fun c hc => mem_fixV.mp hc l hl)
  have hnorm_le : Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub C :=
    le_stabSub_fixV (Y := Subgroup.normalizer (L : Set (MulAut W))) (H := L)
      (fun y hy h hl => (Subgroup.mem_set_normalizer_iff.mp hy h).mp hl)
  have htC : t ∈ stabSub C := hnorm_le htL
  have hcN : c ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    refine Subgroup.centralizer_le_normalizer (L : Set (MulAut W)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcL x hx).symm
  have hcStab : c ∈ stabSub C := hnorm_le hcN
  have hLbar : IsAlt ↥(autQuot L C) 5 := isAlt_autQuot_fixV hAlt
  have hfixbar : fixV (autQuot L C) = ⊥ := fixV_autQuot_fixV_eq_bot hQ
  have htbarN : quotHom C ⟨t, htC⟩ ∈
      Subgroup.normalizer (autQuot L C : Set (MulAut (W ⧸ C))) := by
    have htNsub : (⟨t, htC⟩ : ↥(stabSub C)) ∈
        Subgroup.normalizer (L.subgroupOf (stabSub C)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        refine Subgroup.mem_subgroupOf.mpr ?_
        show t * (g : MulAut W) * t⁻¹ ∈ L
        exact (Subgroup.mem_normalizer_iff.mp htL (g : MulAut W)).mp hg
      · intro hg
        have hg' : t * (g : MulAut W) * t⁻¹ ∈ L := Subgroup.mem_subgroupOf.mp hg
        exact (Subgroup.mem_normalizer_iff.mp htL (g : MulAut W)).mpr hg'
    have hmem : quotHom C ⟨t, htC⟩ ∈
        (Subgroup.normalizer (L.subgroupOf (stabSub C))).map (quotHom C) :=
      Subgroup.mem_map_of_mem (quotHom C) htNsub
    exact Subgroup.le_normalizer_map (f := quotHom C) hmem
  have hncbar : ∃ x ∈ autQuot L C,
      quotHom C ⟨t, htC⟩ * x ≠ x * quotHom C ⟨t, htC⟩ := by
    obtain ⟨x, hxL, hxne⟩ := hnc
    refine ⟨quotHom C ⟨x, hLstab hxL⟩, mem_autQuot.mpr ⟨⟨x, hLstab hxL⟩, hxL, rfl⟩, ?_⟩
    intro h
    have h1 : quotHom C ⟨t, htC⟩ * quotHom C ⟨x, hLstab hxL⟩ *
        (quotHom C ⟨t, htC⟩)⁻¹ * (quotHom C ⟨x, hLstab hxL⟩)⁻¹ = 1 := by
      rw [h]
      group
    have hq : quotHom C (⟨t, htC⟩ * ⟨x, hLstab hxL⟩ * ⟨t, htC⟩⁻¹ *
        ⟨x, hLstab hxL⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact h1
    have hcent : (t * x * t⁻¹ * x⁻¹ : MulAut W) ∈ centQuot C := by
      have hker : (⟨t, htC⟩ * ⟨x, hLstab hxL⟩ * ⟨t, htC⟩⁻¹ *
          ⟨x, hLstab hxL⟩⁻¹ : ↥(stabSub C)) ∈ (quotHom C).ker :=
        MonoidHom.mem_ker.mpr hq
      rw [ker_quotHom, Subgroup.mem_subgroupOf] at hker
      simpa using hker
    have hxL' : t * x * t⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp htL x).mp hxL) (L.inv_mem hxL)
    have hone : t * x * t⁻¹ * x⁻¹ = 1 := eq_one_of_mem_centQuot_fixV hAlt hxL' hcent
    exact hxne (by
      calc t * x = (t * x * t⁻¹ * x⁻¹) * (x * t) := by group
        _ = x * t := by rw [hone, one_mul])
  have htmbar : rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨t, htC⟩))) ≤ 3 :=
    (rkIdx_fixV_zpowers_quotHom_le htC).trans htm
  have hc5bar : (quotHom C ⟨c, hcStab⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have hc5' : (⟨c, hcStab⟩ : ↥(stabSub C)) ^ 5 = 1 := by
      apply Subtype.ext
      simpa using hc5
    rw [hc5', map_one]
  have hcLbar : ∀ x ∈ autQuot L C,
      quotHom C ⟨c, hcStab⟩ * x = x * quotHom C ⟨c, hcStab⟩ := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hx
    have hcomm : (⟨c, hcStab⟩ * g : ↥(stabSub C)) = g * ⟨c, hcStab⟩ := by
      apply Subtype.ext
      simpa using hcL (g : MulAut W) hg
    rw [← map_mul, ← map_mul, hcomm]
  have hWbar : ∀ w : W ⧸ C, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hW v, QuotientGroup.mk_one]
  have hcbar1 : quotHom C ⟨c, hcStab⟩ = 1 :=
    eq_one_of_commute_of_isAlt_five (W := W ⧸ C) hWbar hLbar hfixbar htbarN hncbar htmbar
      hc5bar hcLbar
  have hcCent : c ∈ centQuot C := by
    have hker : (⟨c, hcStab⟩ : ↥(stabSub C)) ∈ (quotHom C).ker :=
      MonoidHom.mem_ker.mpr hcbar1
    rw [ker_quotHom, Subgroup.mem_subgroupOf] at hker
    exact hker
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, -, rfl⟩
  exact mem_centQuot.mp (Subgroup.zpowers_le.mpr hcCent hx) w

theorem commSub_le_fixV_of_isAlt_five_pair {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L K : Subgroup (MulAut W)} (hL : IsAlt ↥L 5)
    (hK : IsAlt ↥K 5) (hcomm : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a) {t : MulAut W}
    (htL : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (hnc : ∃ x ∈ L, t * x ≠ x * t)
    (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3) :
    commSub (⊤ : Subgroup W) K ≤ fixV L := by
  obtain ⟨eK⟩ := hK
  have hcardK : Nat.card ↥K = 60 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    norm_num
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 (by rw [hcardK]; norm_num)
  have hc5 : (k : MulAut W) ^ 5 = 1 := by
    have hord : orderOf (k : MulAut W) = 5 := by rwa [Subgroup.orderOf_coe]
    simpa [hord] using pow_orderOf_eq_one (k : MulAut W)
  have hcL : ∀ x ∈ L, (k : MulAut W) * x = x * (k : MulAut W) :=
    fun x hx => (hcomm x hx k k.2).symm
  have hB := commSub_le_fixV_of_commute_of_isAlt_five hW hL htL hnc htm hc5 hcL
  have hKcent : K ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro k' hk'
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx k' hk'
  have hKnorm : K ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    hKcent.trans (Subgroup.centralizer_le_normalizer (L : Set (MulAut W)))
  have hKstab : K ≤ stabSub (fixV L) :=
    hKnorm.trans (le_stabSub_fixV (Y := Subgroup.normalizer (L : Set (MulAut W))) (H := L)
      (fun y hy h hl => (Subgroup.mem_set_normalizer_iff.mp hy h).mp hl))
  have hKsimple : IsSimpleGroup ↥K := by
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    exact MulEquiv.isSimpleGroup eK
  have hc1 : (k : MulAut W) ≠ 1 := by
    intro h
    have hord : orderOf (k : MulAut W) = 5 := by rwa [Subgroup.orderOf_coe]
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  exact commSub_le_of_isSimpleGroup hKsimple hKstab k.2 hc1 hB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
