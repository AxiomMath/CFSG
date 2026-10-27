module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaE1
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139McL
import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
  (mcLaughlin1969_holds centralizer_eq_bot_of_cost_one)

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_commSub_map_conj (A : Subgroup (MulAut W)) (φ : MulAut W) :
    commSub (⊤ : Subgroup W) (A.map (MulAut.conj φ).toMonoidHom) =
      (commSub (⊤ : Subgroup W) A).map φ.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, w, -, rfl⟩
    refine ⟨x (φ⁻¹ w) * (φ⁻¹ w)⁻¹, ⟨x, hx, φ⁻¹ w, Subgroup.mem_top _, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨d, ⟨x, hx, w, -, rfl⟩, rfl⟩
    refine ⟨φ * x * φ⁻¹, ⟨x, hx, rfl⟩, φ w, Subgroup.mem_top _, ?_⟩
    simp [MulAut.mul_apply]

private theorem w1369_mem_commSub_map_conj {A : Subgroup (MulAut W)} (φ : MulAut W) {u : W}
    (hu : u ∈ commSub (⊤ : Subgroup W) A) :
    φ u ∈ commSub (⊤ : Subgroup W) (A.map (MulAut.conj φ).toMonoidHom) := by
  rw [w1369_commSub_map_conj A φ]
  exact ⟨u, hu, rfl⟩

private theorem w1369_rk_commSub_zpowers_conj {M : Type} [CommGroup M] [Finite M]
    (k d : MulAut M) :
    rk ↥(commSub (⊤ : Subgroup M) (Subgroup.zpowers (k * d * k⁻¹))) =
      rk ↥(commSub (⊤ : Subgroup M) (Subgroup.zpowers d)) := by
  have hzp : Subgroup.zpowers (k * d * k⁻¹) =
      (Subgroup.zpowers d).map (MulAut.conj k).toMonoidHom := by
    rw [← MulAut.conj_apply k d, MonoidHom.map_zpowers]
    rfl
  rw [hzp, w1369_commSub_map_conj]
  unfold rk
  rw [Subgroup.card_map_of_injective (f := k.toMonoidHom) k.injective]

private theorem w1369_inducesTransvection_conj {M : Type} [CommGroup M] [Finite M]
    {d : MulAut M} (hd : InducesTransvection d ⊤) (k : MulAut M) :
    InducesTransvection (k * d * k⁻¹) ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [mem_stabSub]
    intro u
    exact Iff.rfl
  · exact (w1369_rk_commSub_zpowers_conj k d).trans hd.2

private theorem w1369_mem_stabSub_of_forall_mem {U : Subgroup W} {g : MulAut W}
    (h : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U := by
  rw [mem_stabSub]
  intro u
  exact ⟨fun hgu => by
    have h' := inv_mem_of_forall_mem g h (g u) hgu
    simpa using h', h u⟩

private theorem w1369_secHom_eq_secAut {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hAU : A ≤ stabSub U) (hAZ : A ≤ stabSub Z) (a : ↥A)
    (hU : ∀ u ∈ U, (a : MulAut W) u ∈ U) (hZ : ∀ z ∈ Z, (a : MulAut W) z ∈ Z) :
    B5.secHom A hAU hAZ a = secAut U Z a hU hZ := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H u =>
      rw [B5.secHom_mk, secAut_mk]

private theorem w1369_index_sup_zpowers_le_two {A : Type*} [Group A] [Finite A] {K : Subgroup A}
    {e : A} (he2 : e ^ 2 = 1) (hN : Subgroup.zpowers e ≤ Subgroup.normalizer (K : Set A)) :
    (K.subgroupOf (K ⊔ Subgroup.zpowers e)).index ≤ 2 := by
  classical
  have hNsub : (K.subgroupOf (K ⊔ Subgroup.zpowers e)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hN)
  have htop : (K.subgroupOf (K ⊔ Subgroup.zpowers e)) ⊔
      (Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : K ≤ K ⊔ Subgroup.zpowers e)
      (le_sup_right : Subgroup.zpowers e ≤ K ⊔ Subgroup.zpowers e), Subgroup.subgroupOf_self]
  have hindex_eq : (K.subgroupOf (K ⊔ Subgroup.zpowers e)).index =
      (K.subgroupOf (K ⊔ Subgroup.zpowers e)).relIndex
        ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) := by
    rw [← Subgroup.relIndex_top_right (H := K.subgroupOf (K ⊔ Subgroup.zpowers e))]
    rw [← htop, Subgroup.relIndex_sup_left]
  rw [hindex_eq]
  have hbound : (K.subgroupOf (K ⊔ Subgroup.zpowers e)).relIndex
      ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) ≤
      Nat.card ↥((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) := by
    have h := Subgroup.relIndex_mul_card
      (K.subgroupOf (K ⊔ Subgroup.zpowers e))
      ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e))
    have hpos : 0 < Nat.card ↥((K.subgroupOf (K ⊔ Subgroup.zpowers e)) ⊓
        ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e))) := Nat.card_pos
    nlinarith [h, hpos]
  refine hbound.trans ?_
  have hcard_le : Nat.card ↥((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) ≤
      Nat.card ↥(Subgroup.zpowers e) := by
    refine Nat.card_le_card_of_injective
      (fun z : ↥((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) =>
        (⟨((z.1 : ↥(K ⊔ Subgroup.zpowers e)) : A), z.2⟩ : ↥(Subgroup.zpowers e))) ?_
    intro z w h
    have h' : (z.1 : A) = (w.1 : A) :=
      congrArg (fun t : ↥(Subgroup.zpowers e) => (t : A)) h
    exact Subtype.ext (Subtype.ext h')
  have hcard_e : Nat.card ↥(Subgroup.zpowers e) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr he2)
  exact hcard_le.trans hcard_e

private theorem w1369_commutator_eq_self_of_isQuasisimple {G : Type*} [Group G] {L : Subgroup G}
    (h : CFSG.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h.1.commutator_eq_top] at h1
  rw [← h1, Subgroup.map_top, Subgroup.range_subtype]

private theorem w1369_ne_bot_of_isQuasisimple {G : Type*} [Group G] {K : Subgroup G}
    (h : CFSG.IsQuasisimple ↥K) : K ≠ ⊥ := by
  intro hbot
  haveI : Nontrivial (↥K ⧸ Subgroup.center ↥K) := h.2.1.toNontrivial
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥K)) :=
    QuotientGroup.mk'_surjective _
  haveI hnt : Nontrivial ↥K := hsurj.nontrivial
  have hsub : Subsingleton ↥K := by
    rw [hbot]
    exact ⟨fun a b => Subtype.ext (by
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt

theorem cost_one_summand (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    {J : Subgroup W} (hCJ : Cd L ≤ J) (hJW : J ≤ Wd L) (hJ : IsIrrOn L J (Cd L))
    (hLJ : commSub J L ⊔ Cd L = J) (hJt : StableUnder (Subgroup.zpowers t) J)
    (hcost : tcost t L J = 1) :
    Subgroup.centralizer ((secSub J (Cd L) L : Subgroup (MulAut (Sect J (Cd L)))) :
      Set (MulAut (Sect J (Cd L)))) = ⊥ ∧ McLShape (secSub J (Cd L) L) := by
  classical
  have hmapL : L.map (MulAut.conj t).toMonoidHom = L := c.hfix L c.comp
  have hJt' : ∀ u ∈ J, t u ∈ J := fun u hu => hJt t (Subgroup.mem_zpowers t) u hu
  have htC : ∀ z ∈ Cd L, t z ∈ Cd L := by
    intro z hz
    rw [Subgroup.mem_inf] at hz ⊢
    refine ⟨?_, ?_⟩
    · have h := w1369_mem_commSub_map_conj (A := L) t hz.1
      rwa [hmapL] at h
    · rw [mem_fixV]
      intro l hl
      have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapL
      have htinvN : t⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.normalizer (L : Set (MulAut W))).inv_mem htN
      have hl' : t⁻¹ * l * t ∈ L :=
        ((Subgroup.mem_normalizer_iff.mp htinvN) l).mp hl
      calc l (t z) = t ((t⁻¹ * l * t) z) := by simp [MulAut.mul_apply]
        _ = t z := by rw [hz.2 _ hl']
  have hStabL : StabPair L J (Cd L) :=
    fun l hl => ⟨hJ.2.1 l hl, hJ.2.2.1 l hl⟩
  have htStab : t ∈ stabSub (Cd L) :=
    w1369_mem_stabSub_of_forall_mem htC
  have hStabT : StabPair (Subgroup.zpowers t) J (Cd L) := by
    intro a ha
    refine ⟨hJt a ha, fun z hz => ?_⟩
    have haz : a ∈ stabSub (Cd L) := Subgroup.zpowers_le.mpr htStab ha
    exact (mem_stabSub.mp haz z).2 hz
  let tb : MulAut (Sect J (Cd L)) := secAut J (Cd L) t hJt' htC
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [c.std.t2] at h
  have hAU : Subgroup.zpowers t ≤ stabSub J :=
    Subgroup.zpowers_le.mpr (w1369_mem_stabSub_of_forall_mem hJt')
  have hAZ : Subgroup.zpowers t ≤ stabSub (Cd L) := Subgroup.zpowers_le.mpr htStab
  have htb_eq : tb = B5.secHom (Subgroup.zpowers t) hAU hAZ
      ⟨t, Subgroup.mem_zpowers t⟩ := by
    dsimp only [tb]
    rw [w1369_secHom_eq_secAut hAU hAZ ⟨t, Subgroup.mem_zpowers t⟩ hJt' htC]
  have htb2 : tb ^ 2 = 1 := by
    rw [htb_eq, ← map_pow]
    have h1 : (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) ^ 2 = 1 :=
      Subtype.ext (by simpa using ht2)
    rw [h1, map_one]
  have htb_rk : rk ↥(commSub (⊤ : Subgroup (Sect J (Cd L)))
      (Subgroup.zpowers tb)) = 1 := by
    dsimp only [tb]
    rw [rk_secAut_comm hCJ hJt' htC]
    exact hcost
  have htbTv : InducesTransvection tb ⊤ := by
    refine ⟨?_, htb_rk⟩
    rw [mem_stabSub]
    intro u
    exact Iff.rfl
  have hnt : ¬ ∀ l ∈ L, ∀ u ∈ J, l u * u⁻¹ ∈ Cd L := by
    intro h
    have hle : commSub J L ≤ Cd L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, u, hu, rfl⟩
      exact h l hl u hu
    have hJC : J = Cd L := by
      rw [← hLJ, sup_eq_right.mpr hle]
    exact (ne_of_lt hJ.1) hJC.symm
  have hq : IsQuasisimple ↥(secSub J (Cd L) L) :=
    isQuasisimple_secSub hStabL (B1Red.isQuasisimple_of_open c.comp.2.2) hnt
  have hperf : ⁅secSub J (Cd L) L, secSub J (Cd L) L⁆ = secSub J (Cd L) L :=
    w1369_commutator_eq_self_of_isQuasisimple hq
  have hK1 : secSub J (Cd L) L ≠ ⊥ := w1369_ne_bot_of_isQuasisimple hq
  have hdN : (secSub J (Cd L) L).map (MulAut.conj tb).toMonoidHom = secSub J (Cd L) L := by
    dsimp only [tb]
    rw [secSub_map_conj hStabL hJt' htC, hmapL]
  have hIrr : IsIrrOn (secSub J (Cd L) L) ⊤ ⊥ := (secSub_irr hStabL hJ.1).mpr hJ
  have hcent : Subgroup.centralizer
      (secSub J (Cd L) L : Set (MulAut (Sect J (Cd L)))) = ⊥ :=
    centralizer_eq_bot_of_cost_one (sect_exp_two hw2 J (Cd L)) hperf hK1 hIrr htb2 hdN htb_rk
  refine ⟨hcent, ?_⟩
  let G0 : Subgroup (MulAut (Sect J (Cd L))) := secSub J (Cd L) L ⊔ Subgroup.zpowers tb
  have hLe : secSub J (Cd L) L ≤ G0 := by
    dsimp only [G0]
    exact le_sup_left
  have htbN : tb ∈ Subgroup.normalizer (secSub J (Cd L) L : Set (MulAut (Sect J (Cd L)))) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hdN
  have htbNzp : Subgroup.zpowers tb ≤
      Subgroup.normalizer (secSub J (Cd L) L : Set (MulAut (Sect J (Cd L)))) :=
    Subgroup.zpowers_le.mpr htbN
  have hNormal : ((secSub J (Cd L) L).subgroupOf G0).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      dsimp only [G0]
      exact sup_le Subgroup.le_normalizer htbNzp)
  have hIndex : ((secSub J (Cd L) L).subgroupOf G0).index ≤ 2 := by
    dsimp only [G0]
    exact w1369_index_sup_zpowers_le_two htb2 htbNzp
  have hG0irr : IsIrrOn G0 ⊤ ⊥ := by
    refine ⟨hIrr.1, ?_, ?_, ?_⟩
    · intro x _ u _
      exact Subgroup.mem_top (x u)
    · intro x _ u hu
      rw [Subgroup.mem_bot.mp hu]
      exact Subgroup.mem_bot.mpr (map_one x)
    · intro J' hJ' _ _
      exact hIrr.2.2.2 J' (fun x hx u hu => hJ' x (hLe hx) u hu) bot_le le_top
  have hLcomm : secSub J (Cd L) L = ⁅secSub J (Cd L) L, Subgroup.zpowers tb⁆ := by
    dsimp only [tb]
    rw [← secSub_zpowers hJt' htC, secSub_commutator hStabL hStabT, c.Lt]
  have hGen : G0 = Subgroup.closure
      {t : MulAut (Sect J (Cd L)) | t ∈ G0 ∧ InducesTransvection t ⊤} := by
    apply le_antisymm
    · dsimp only [G0]
      refine sup_le ?_ ?_
      · conv_lhs => rw [hLcomm]
        refine Subgroup.commutator_le.mpr ?_
        intro k hk y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [zpow_eq_zpow_emod j (show tb ^ (2 : ℤ) = 1 by simpa using htb2)]
        rcases Int.emod_two_eq_zero_or_one j with h0 | h1
        · rw [h0, zpow_zero, commutatorElement_one_right]
          exact Subgroup.one_mem _
        · rw [h1, zpow_one]
          have heq : ⁅k, tb⁆ = (k * tb * k⁻¹) * tb⁻¹ := by
            rw [commutatorElement_def]
          rw [heq]
          refine Subgroup.mul_mem _ ?_ ?_
          · refine Subgroup.subset_closure ⟨?_, w1369_inducesTransvection_conj htbTv k⟩
            exact (secSub J (Cd L) L ⊔ Subgroup.zpowers tb).mul_mem
              ((secSub J (Cd L) L ⊔ Subgroup.zpowers tb).mul_mem (Subgroup.mem_sup_left hk)
                (Subgroup.mem_sup_right (Subgroup.mem_zpowers tb)))
              ((secSub J (Cd L) L ⊔ Subgroup.zpowers tb).inv_mem (Subgroup.mem_sup_left hk))
          · refine Subgroup.inv_mem _ (Subgroup.subset_closure ⟨?_, htbTv⟩)
            exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tb)
      · rw [Subgroup.zpowers_le]
        refine Subgroup.subset_closure ⟨?_, htbTv⟩
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tb)
    · rw [Subgroup.closure_le]
      exact fun t ht => ht.1
  unfold McLShape
  exact mcLaughlin1969_holds (Sect J (Cd L)) (sect_exp_two hw2 J (Cd L)) G0 (secSub J (Cd L) L)
    hLe hNormal hIndex hq hG0irr hGen

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
