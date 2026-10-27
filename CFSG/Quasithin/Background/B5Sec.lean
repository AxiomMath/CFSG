module

public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
import CFSG.Quasithin.EmptyFaithful.S14113bFStar
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B5

section SecHom

variable {V : Type*} [CommGroup V] {W U : Subgroup V} (X : Subgroup (MulAut V))
  (hXW : X ≤ stabSub W) (hXU : X ≤ stabSub U)

@[expose] def secRho : ↥X →* ↥(stabSub (U.subgroupOf W)) :=
  ((resHom W).comp (Subgroup.inclusion hXW)).codRestrict (stabSub (U.subgroupOf W))
    (fun g => autSub_le_stabSub_subgroupOf hXU (mem_autSub.2 ⟨⟨g, hXW g.2⟩, g.2, rfl⟩))

@[expose] def secHom : ↥X →* MulAut (Sec W U) :=
  (quotHom (U.subgroupOf W)).comp (secRho X hXW hXU)

theorem secHom_mk (g : ↥X) (w : ↥W) :
    secHom X hXW hXU g (QuotientGroup.mk w) = QuotientGroup.mk ⟨(g : MulAut V) (w : V), (hXW g.2 w).2 w.2⟩ :=
  rfl


theorem map_secHom_eq_autSec {L : Subgroup (MulAut V)} (hLX : L ≤ X) :
    (L.subgroupOf X).map (secHom X hXW hXU) = autSec L W U := by
  ext φ
  rw [Subgroup.mem_map, autSec, mem_autQuot]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨secRho X hXW hXU g, ?_, rfl⟩
    exact mem_autSub.2 ⟨⟨g, hXW g.2⟩, hg, rfl⟩
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨g₀, hg₀, hg₀'⟩ := mem_autSub.1 hg'
    refine ⟨⟨g₀, hLX hg₀⟩, hg₀, ?_⟩
    have : secRho X hXW hXU ⟨g₀, hLX hg₀⟩ = g' := by
      apply Subtype.ext
      exact hg₀'
    rw [secHom, MonoidHom.comp_apply, this]

theorem range_secHom : (secHom X hXW hXU).range = autSec X W U := by
  rw [← map_secHom_eq_autSec X hXW hXU (le_refl X), Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem mem_ker_secHom (g : ↥X) :
    g ∈ (secHom X hXW hXU).ker ↔ (g : MulAut V) ∈ centSec W U := by
  rw [MonoidHom.mem_ker, mem_centSec]
  constructor
  · intro h
    refine ⟨hXW g.2, fun w hw => ?_⟩
    have := congrArg (fun φ : MulAut (Sec W U) => φ (QuotientGroup.mk ⟨w, hw⟩)) h
    simp only [secHom_mk, MulAut.one_apply] at this
    have h2 := (mk_eq_mk_iff (U := U.subgroupOf W) _ _).1 this
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  · rintro ⟨-, h⟩
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [secHom_mk]
      refine (mk_eq_mk_iff (U := U.subgroupOf W) _ _).2 ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using h w w.2


theorem ker_secHom_eq_bot (hfaith : X ⊓ centSec W U = ⊥) : (secHom X hXW hXU).ker = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_ker_secHom] at hg
  have : (g : MulAut V) ∈ X ⊓ centSec W U := ⟨g.2, hg⟩
  rw [hfaith, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

@[expose] noncomputable def secEquiv (hfaith : X ⊓ centSec W U = ⊥) : ↥X ≃* ↥(autSec X W U) :=
  (MonoidHom.ofInjective (f := secHom X hXW hXU)
    ((MonoidHom.ker_eq_bot_iff _).1 (ker_secHom_eq_bot X hXW hXU hfaith))).trans
    (MulEquiv.subgroupCongr (range_secHom X hXW hXU))

theorem secEquiv_apply (hfaith : X ⊓ centSec W U = ⊥) (g : ↥X) :
    (((secEquiv X hXW hXU hfaith g : ↥(autSec X W U)) : MulAut (Sec W U))) = secHom X hXW hXU g :=
  rfl

end SecHom

section GenFitting

theorem fitting_map_le {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (CFSG.ComponentClassification.Fitting.subgroup G).map e.toMonoidHom ≤
      CFSG.ComponentClassification.Fitting.subgroup H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro c hc
  have : c.Normal := hc.1
  have : Group.IsNilpotent c := hc.2
  have : (c.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have : Group.IsNilpotent (c.map e.toMonoidHom) :=
    (Group.isNilpotent_congr (e.subgroupMap c)).mp inferInstance
  exact Subgroup.map_le_iff_le_comap.mp
    (CFSG.ComponentClassification.Fitting.maximal (c.map e.toMonoidHom))

theorem genFitting_map_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (CFSG.ComponentClassification.GeneralizedFitting.subgroup G).map e.toMonoidHom =
      CFSG.ComponentClassification.GeneralizedFitting.subgroup H := by
  simp only [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup]
  rw [Subgroup.map_sup, CFSG.ComponentClassification.Layer.equiv_invariant e]
  congr 1
  apply le_antisymm (fitting_map_le e)
  intro x hx
  have h2 := fitting_map_le e.symm (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx)
  exact ⟨e.symm x, h2, e.apply_symm_apply x⟩

end GenFitting

section GenFittingSec

variable {V : Type*} [CommGroup V] {W U : Subgroup V}

theorem genFitting_autSec {M L : Subgroup (MulAut V)} (hLM : L ≤ M) (hMW : M ≤ stabSub W)
    (hMU : M ≤ stabSub U) (hfaith : M ⊓ centSec W U = ⊥) (hF : quasithinGenFitting M = L) :
    quasithinGenFitting (autSec M W U) = autSec L W U := by
  set e := secEquiv M hMW hMU hfaith with he
  have h1 : (CFSG.ComponentClassification.GeneralizedFitting.subgroup ↥M).map M.subtype = L := by
    rw [← quasithinGenFitting_eq_map_subtype, hF]
  have h2 : CFSG.ComponentClassification.GeneralizedFitting.subgroup ↥M = L.subgroupOf M := by
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm
  rw [quasithinGenFitting_eq_map_subtype, ← genFitting_map_equiv e, h2, Subgroup.map_map]
  have h3 : (autSec M W U).subtype.comp e.toMonoidHom = secHom M hMW hMU := by
    ext g
    rfl
  rw [h3]
  exact map_secHom_eq_autSec M hMW hMU hLM

end GenFittingSec

section Transport

variable {V : Type} [CommGroup V] [Finite V] {W U : Subgroup V} {L : Subgroup (MulAut V)}
  (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hfaith : L ⊓ centSec W U = ⊥)

include hLW hLU hfaith

omit [Finite V] in
theorem isQuasisimple_autSec (hq : CFSG.IsQuasisimple ↥L) :
    CFSG.IsQuasisimple ↥(autSec L W U) := by
  have e := secEquiv L hLW hLU hfaith
  exact B1Red.isQuasisimple_of_open
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
      (B1Red.isQuasisimple_to_open hq))

theorem sqtk_autSec (hM : SQTKGroup ↥L) : SQTKGroup ↥(autSec L W U) := by
  have e := secEquiv L hLW hLU hfaith
  refine ⟨fun p hp hp2 => ?_, hM.2.of_mulEquiv e.symm⟩
  show CFSG.Open.pRank p (⊤ : Subgroup ↥(autSec L W U)) ≤ 2
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact hM.1 p hp hp2

omit [Finite V] hLW hLU hfaith in
theorem secHom_symm (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hfaith : L ⊓ centSec W U = ⊥)
    (x : ↥(autSec L W U)) :
    ((x : ↥(autSec L W U)) : MulAut (Sec W U)) =
      secHom L hLW hLU ((secEquiv L hLW hLU hfaith).symm x) := by
  have := secEquiv_apply L hLW hLU hfaith ((secEquiv L hLW hLU hfaith).symm x)
  rw [MulEquiv.apply_symm_apply] at this
  exact this

end Transport

section Realizes

variable {V : Type} [CommGroup V] {W U : Subgroup V} {L : Subgroup (MulAut V)}
  (hUW : U ≤ W) (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hfaith : L ⊓ centSec W U = ⊥)

include hUW hLW hLU hfaith

theorem realizesVia_of_autSec {D : FFModel} {π' : D.Gam →* ↥(autSec L W U)}
    (h : D.RealizesVia (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ π') :
    D.RealizesVia L W U ((secEquiv L hLW hLU hfaith).symm.toMonoidHom.comp π') := by
  obtain ⟨hsurj, -, hkerle, -, -, hsec, hkerinv, β', hβs, hβk, hβe⟩ := h
  set e := secEquiv L hLW hLU hfaith with he
  let q : ↥W →* ↥(⊤ : Subgroup (Sec W U)) :=
    (Subgroup.topEquiv (G := Sec W U)).symm.toMonoidHom.comp (QuotientGroup.mk' (U.subgroupOf W))
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (y : Sec W U)
    exact ⟨w, Subtype.ext hw⟩
  refine ⟨e.symm.surjective.comp hsurj, hUW, hkerle, fun g u hu => (hLW g.2 u).2 hu,
    fun g z hz => (hLU g.2 z).2 hz, hsec, hkerinv, β'.comp q, hβs.comp hq_surj, ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply, hβk]
    simp only [Subgroup.mem_bot]
    show (QuotientGroup.mk u : Sec W U) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro γ u m hu hm hum
    have hπ : (((π' γ : ↥(autSec L W U))) : MulAut (Sec W U)) =
        secHom L hLW hLU (e.symm (π' γ)) := secHom_symm hLW hLU hfaith (π' γ)
    have key := hβe γ (q u) m (by trivial) hm hum
    have hqu : (⟨(((π' γ : ↥(autSec L W U))) : MulAut (Sec W U)) ((q u : ↥(⊤ : Subgroup (Sec W U))) : Sec W U),
        by trivial⟩ : ↥(⊤ : Subgroup (Sec W U))) = q ⟨((e.symm (π' γ) : ↥L) : MulAut V) (u : V), hu⟩ := by
      apply Subtype.ext
      rw [hπ]
      rfl
    show β' (q ⟨((e.symm (π' γ) : ↥L) : MulAut V) (u : V), hu⟩) = _
    rw [← hqu]
    exact key

end Realizes

section Irr

variable {V : Type*} [CommGroup V] {W C : Subgroup V} {L : Subgroup (MulAut V)}

theorem isIrrSec_autSec (hCW : C < W)
    (hirr : ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → C ≤ J → J ≤ W → J = C ∨ J = W)
    (hLW : L ≤ stabSub W) (hLC : L ≤ stabSub C) :
    XMod.IsIrrSec ↥(autSec L W C) (⊥ : Subgroup (Sec W C)) ⊤ := by
  refine ⟨?_, fun J' hJ' _ _ => ?_⟩
  ·
    obtain ⟨w, hwW, hwC⟩ := IsConcreteLE.exists_of_lt hCW
    refine lt_of_le_of_ne bot_le fun h => ?_
    have : (QuotientGroup.mk (⟨w, hwW⟩ : ↥W) : Sec W C) ∈ (⊤ : Subgroup (Sec W C)) := trivial
    rw [← h, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    exact hwC this
  · set π : ↥W →* Sec W C := QuotientGroup.mk' (C.subgroupOf W) with hπ
    set J : Subgroup V := (J'.comap π).map W.subtype with hJ
    have hJinv : ∀ x ∈ L, ∀ w ∈ J, x w ∈ J := by
      intro x hx w hw
      obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
      have hxW : x ∈ stabSub W := hLW hx
      refine Subgroup.mem_map.2 ⟨⟨x (w' : V), (hxW _).2 w'.2⟩, ?_, rfl⟩
      have hx' : secHom L hLW hLC ⟨x, hx⟩ ∈ autSec L W C := by
        rw [← range_secHom L hLW hLC]
        exact ⟨⟨x, hx⟩, rfl⟩
      have := hJ' ⟨_, hx'⟩ (π w') hw'
      exact this
    have hCJ : C ≤ J := by
      intro c hc
      refine Subgroup.mem_map.2 ⟨⟨c, hCW.le hc⟩, ?_, rfl⟩
      show π ⟨c, hCW.le hc⟩ ∈ J'
      have : π ⟨c, hCW.le hc⟩ = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hc
      rw [this]
      exact J'.one_mem
    have hJW : J ≤ W := Subgroup.map_subtype_le _
    rcases hirr J hJinv hCJ hJW with hJC | hJW'
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective s
      have hw : (w' : V) ∈ J := Subgroup.mem_map.2 ⟨w', hs, rfl⟩
      rw [hJC] at hw
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hw
    · right
      rw [eq_top_iff]
      intro s _
      obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective s
      have hw : (w' : V) ∈ J := by rw [hJW']; exact w'.2
      obtain ⟨w2, hw2, hw3⟩ := Subgroup.mem_map.1 hw
      have : w2 = w' := Subtype.ext hw3
      rw [this] at hw2
      exact hw2

end Irr

end B5

end CFSG.Quasithin
