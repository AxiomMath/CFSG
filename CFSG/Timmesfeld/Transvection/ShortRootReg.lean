module

public import CFSG.Timmesfeld.Transvection.ShortRoot
public import CFSG.Timmesfeld.Transvection.ShortRootField
public import CFSG.Timmesfeld.Transvection.FrameBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem PairFrame.shortRootGroup_inf_eq_bot {A E D E' : Subgroup G} (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) : shortRootGroup Δ E A D E' ⊓ D = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hxS : x ∈ lineStab Δ E' E := by
    rw [← lineStab_comm]
    exact hx.1.2
  exact eq_one_of_mem_lineStab hΔ P.memD P.memE' P.memE P.oppD P.commuting_EE'.symm hx.2 hxS

namespace Sp4Frame

variable {A E D E' C : Subgroup G} {t t' : G}

theorem inf_centralizer_eq_sup [Finite G] (F : Sp4Frame Δ A E D E' C)
    (hpts : PointsDetermined Δ) (S : TriangleSetting Δ A E C t) (htY : t ∈ A ⊔ E ⊔ C)
    (S' : TriangleSetting Δ D E' C t') (htY' : t' ∈ D ⊔ E' ⊔ C) (hq : 4 ≤ Nat.card A) :
    corrN A E t ⊓ Subgroup.centralizer (A : Set G) = D ⊔ (corrN A E t ⊓ corrN D E' t') := by
  have hΔ := S.cls
  obtain ⟨k, φ, h, μ, hh, hμ, hμ1⟩ := exists_sl2Coords_torus hΔ.root F.memA F.memE F.oppA hq
  obtain ⟨-, hCZ, -, -⟩ := S.centralizer_corrN_spec htY hq hpts (S.coordsOf htY hq φ) hh hμ hμ1
  rwa [← S.eq_corrN_inf_centralizer htY hq hpts (F.mem_lineOf hΔ hpts) F.commuting_ED.symm,
    F.commSub_eq_inf hpts S htY S' htY' hq (S.coordsOf htY hq φ) hh hμ hμ1] at hCZ

theorem inf_centralizer_E_eq_sup [Finite G] (F : Sp4Frame Δ A E D E' C)
    (hpts : PointsDetermined Δ) (S : TriangleSetting Δ A E C t) (htY : t ∈ A ⊔ E ⊔ C)
    (S' : TriangleSetting Δ D E' C t') (htY' : t' ∈ D ⊔ E' ⊔ C) (hq : 4 ≤ Nat.card A) {w : G}
    (hw : w ∈ A ⊔ E) (hAw : conjSub A w = E) :
    corrN A E t ⊓ Subgroup.centralizer (E : Set G) =
      D ⊔ conjSub (corrN A E t ⊓ corrN D E' t') w := by
  have hΔ := S.cls
  have hcA := F.inf_centralizer_eq_sup hpts S htY S' htY' hq
  have hDN : D ≤ corrN A E t := by
    rw [S.eq_corrN_inf_centralizer htY hq hpts (F.mem_lineOf hΔ hpts) F.commuting_ED.symm]
    exact inf_le_left
  have hRA : corrN A E t ⊓ corrN D E' t' ≤ corrN A E t ⊓ Subgroup.centralizer (A : Set G) :=
    le_sup_right.trans hcA.ge
  have hwD : ∀ d ∈ D, Commute w d := fun d hd =>
    (commute_of_mem_sup_left F.commuting_AD F.commuting_ED hw hd).symm
  refine le_antisymm (fun m hm => ?_) (sup_le (fun d hd => ⟨hDN hd,
    Subgroup.mem_centralizer_iff.2 fun e he => (F.commuting_ED e he d hd).eq⟩) ?_)
  ·
    have hm' : w⁻¹ * m * w ∈ corrN A E t ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨?_, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      · have := conj_mem_corrN (Subgroup.inv_mem _ hw) hm.1
        rwa [inv_inv] at this
      · have hae : w * a * w⁻¹ ∈ E := by
          have := conj_mem_conjSub w ha
          rwa [hAw] at this
        have hc := Subgroup.mem_centralizer_iff.1 hm.2 _ hae
        calc a * (w⁻¹ * m * w) = w⁻¹ * ((w * a * w⁻¹) * m) * w := by group
          _ = w⁻¹ * (m * (w * a * w⁻¹)) * w := by rw [hc]
          _ = w⁻¹ * m * w * a := by group
    rw [hcA] at hm'
    have hc : Commuting D (corrN A E t ⊓ corrN D E' t') := fun x hx y hy =>
      S.commute_of_mem_corrN' htY hq (hDN hx) hy.1
    obtain ⟨d, hd, r, hr, hdr⟩ := mem_sup_of_commuting hc hm'
    have hmeq : m = d * (w * r * w⁻¹) := by
      calc m = w * (w⁻¹ * m * w) * w⁻¹ := by group
        _ = w * (d * r) * w⁻¹ := by rw [hdr]
        _ = w * d * w⁻¹ * (w * r * w⁻¹) := by group
        _ = d * (w * r * w⁻¹) := by rw [(hwD d hd).eq, mul_inv_cancel_right]
    rw [hmeq]
    exact Subgroup.mul_mem_sup hd (conj_mem_conjSub w hr)
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_conjSub_iff.1 hx
    refine ⟨conj_mem_corrN hw hr.1, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    rw [← hAw] at he
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 he
    have hc := Subgroup.mem_centralizer_iff.1 (hRA hr).2 a ha
    calc w * a * w⁻¹ * (w * r * w⁻¹) = w * (a * r) * w⁻¹ := by group
      _ = w * (r * a) * w⁻¹ := by rw [hc]
      _ = w * r * w⁻¹ * (w * a * w⁻¹) := by group

theorem conjSub_inf_corrN_le_shortRootGroup [Finite G] (F : Sp4Frame Δ A E D E' C)
    (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ) (S : TriangleSetting Δ A E C t)
    (htY : t ∈ A ⊔ E ⊔ C) (S' : TriangleSetting Δ D E' C t') (htY' : t' ∈ D ⊔ E' ⊔ C)
    (hq : 4 ≤ Nat.card A) {w : G} (hw : w ∈ A ⊔ E) (hAw : conjSub A w = E)
    (hEw : conjSub E w = A) :
    conjSub (corrN A E t ⊓ corrN D E' t') w ≤ shortRootGroup Δ E A D E' := by
  have hΔ := S.cls
  have hD : conjSub D w = D := conjSub_of_forall_commute fun d hd =>
    F.comm w hw d (Subgroup.mem_sup_left hd)
  have hE' : conjSub E' w = E' := conjSub_of_forall_commute fun d hd =>
    F.comm w hw d (Subgroup.mem_sup_right hd)
  have h : conjSub (corrN A E t ⊓ corrN D E' t') w ≤ conjSub (shortRootGroup Δ A E D E') w :=
    Subgroup.map_mono (F.toPairFrame.inf_corrN_le_shortRootGroup hpts hlines F.memB F.neA F.neD
      S htY S' htY' hq)
  rwa [← shortRootGroup_conjSub hΔ.root, hAw, hEw, hD, hE'] at h

theorem inf_centralizer_inf_shortRootGroup [Finite G] (F : Sp4Frame Δ A E D E' C)
    (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ) (S : TriangleSetting Δ A E C t)
    (htY : t ∈ A ⊔ E ⊔ C) (S' : TriangleSetting Δ D E' C t') (htY' : t' ∈ D ⊔ E' ⊔ C)
    (hq : 4 ≤ Nat.card A) {w : G} (hw : w ∈ A ⊔ E) (hAw : conjSub A w = E)
    (hEw : conjSub E w = A) :
    corrN A E t ⊓ Subgroup.centralizer (E : Set G) ⊓ shortRootGroup Δ E A D E' =
      conjSub (corrN A E t ⊓ corrN D E' t') w := by
  have hΔ := S.cls
  have hcE := F.inf_centralizer_E_eq_sup hpts S htY S' htY' hq hw hAw
  have hRX := F.conjSub_inf_corrN_le_shortRootGroup hpts hlines S htY S' htY' hq hw hAw hEw
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_right.trans hcE.ge) hRX)
  have hx1 := hx.1
  rw [hcE] at hx1
  obtain ⟨d, hd, r, hr, rfl⟩ := mem_sup_of_commuting (fun y hy z hz =>
    S.commute_of_mem_corrN' htY hq (le_sup_left.trans hcE.ge hy).1
      (le_sup_right.trans hcE.ge hz).1) hx1
  have hdX : d ∈ shortRootGroup Δ E A D E' := by
    have := (shortRootGroup Δ E A D E').mul_mem hx.2
      ((shortRootGroup Δ E A D E').inv_mem (hRX hr))
    rwa [mul_inv_cancel_right] at this
  have hd1 : d = 1 := by
    have : d ∈ shortRootGroup Δ E A D E' ⊓ D := ⟨hdX, hd⟩
    rwa [F.toPairFrame.shortRootGroup_inf_eq_bot hΔ, Subgroup.mem_bot] at this
  rw [hd1, one_mul]
  exact hr

end Sp4Frame

namespace PairFrame

variable {A E D E' : Subgroup G}

theorem eq_one_of_conjSub_eq [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (hxA : conjSub A x = A) : x = 1 := by
  have hR := hΔ.root
  have hqE : 4 ≤ Nat.card E := by rwa [hR.card_eq P.memE P.memA]
  have hxE : ∀ e ∈ E, Commute x e := fun e he =>
    commute_of_mem_lineGroup hΔ P.memE P.memD P.commuting_ED hx.1.1
      (le_lineGroup (left_mem_lineOf P.memE) he)
  have hxA' : ∀ a ∈ A, Commute x a := fun a ha =>
    commute_of_commute_partner P.oppA.symm hxA hxE ha
  obtain ⟨k, φ, h, μ, hh, hμ, hμ1⟩ := exists_sl2Coords_torus hR P.memE P.memA P.oppA.symm hqE
  have hDE : D ≠ E := by
    intro hDE
    have h1 := P.commuting_AD
    rw [hDE] at h1
    exact ModelRank.not_commuting_of_opposite P.oppA h1.symm
  have hxD := (commute_lineGroup_iff φ hh hμ hΔ hiso hpts P.memE P.memA P.memD P.oppA.symm
    P.commuting_ED P.commuting_AD hDE hqE hμ1 hx.1.1).1 (commute_of_mem_sup_of_commute hxE hxA' hh)
  have : x ∈ shortRootGroup Δ E A D E' ⊓ D := ⟨hx, hxD⟩
  rwa [P.shortRootGroup_inf_eq_bot hΔ, Subgroup.mem_bot] at this

theorem eq_of_conjSub_eq [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A) {x y : G}
    (hx : x ∈ shortRootGroup Δ E A D E') (hy : y ∈ shortRootGroup Δ E A D E')
    (hxy : conjSub A x = conjSub A y) : x = y := by
  have h1 : x⁻¹ * y ∈ shortRootGroup Δ E A D E' := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
  have h2 : conjSub A (x⁻¹ * y) = A := by
    rw [conjSub_mul, ← hxy, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have := P.eq_one_of_conjSub_eq hΔ hiso hpts hq h1 h2
  rwa [inv_mul_eq_one] at this

theorem conjSub_ne_right (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) {x : G}
    (hx : x ∈ shortRootGroup Δ E A D E') : conjSub A x ≠ D := by
  intro hAx
  have hDx : conjSub D x = D := conjSub_of_forall_commute fun d hd =>
    commute_of_mem_lineGroup hΔ P.memE P.memD P.commuting_ED hx.1.1
      (le_lineGroup (right_mem_lineOf P.memD) hd)
  exact P.ne_AD (conjSub_injective x (hAx.trans hDx.symm))

theorem exists_mem_inf_conjSub_eq [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) (hq : 4 ≤ Nat.card A) {C : Subgroup G} (hC : C ∈ lineOf Δ A D)
    (hCA : C ≠ A) (hCD : C ≠ D) {t : G} (S : TriangleSetting Δ A E C t) (htY : t ∈ A ⊔ E ⊔ C) :
    ∃ x ∈ corrN A E t ⊓ Subgroup.centralizer (E : Set G) ⊓ shortRootGroup Δ E A D E',
      conjSub A x = C := by
  have F := P.toSp4Frame hC hCA hCD
  obtain ⟨t', htY', S'⟩ := exists_triangleSetting hΔ hiso (F.swap.isTriangle hΔ hpts)
  obtain ⟨w, hw, -, hAw, hEw⟩ := exists_weylElt hΔ P.memA P.memE P.oppA
  have hw' : w ∈ A ⊔ E := sup_comm E A ▸ hw
  have hcE := F.inf_centralizer_E_eq_sup hpts S htY S' htY' hq hw' hAw
  have hRX := F.inf_centralizer_inf_shortRootGroup hpts hlines S htY S' htY' hq hw' hAw hEw
  obtain ⟨e, he, he1⟩ := hΔ.root.exists_ne_one P.memE
  have hmC : conjSub A (partnerElt A E C e) = C := S.conjSub_partnerElt he he1
  have hmE : partnerElt A E C e ∈ corrN A E t ⊓ Subgroup.centralizer (E : Set G) :=
    ⟨corrM_le_corrN (S.partnerElt_mem_corrM he he1), Subgroup.mem_centralizer_iff.2 fun y hy =>
      (S.commute_partnerElt he he1 hy).symm.eq⟩
  rw [hcE] at hmE
  obtain ⟨d, hd, r, hr, hdr⟩ := mem_sup_of_commuting (fun y hy z hz =>
    S.commute_of_mem_corrN' htY hq (le_sup_left.trans hcE.ge hy).1
      (le_sup_right.trans hcE.ge hz).1) hmE
  refine ⟨r, by rw [hRX]; exact hr, ?_⟩
  have hr' : r = d⁻¹ * partnerElt A E C e := by
    rw [← hdr]
    group
  rw [hr', conjSub_mul, hmC]
  exact conjSub_of_forall_commute fun c hc =>
    commuting_of_mem_lineOf_of_mem_lineOf hΔ P.memA P.memD P.commuting_AD
      (right_mem_lineOf P.memD) hC _ (D.inv_mem hd) c hc

theorem exists_conjSub_eq [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) {C : Subgroup G} (hC : C ∈ lineOf Δ A D) (hCD : C ≠ D) :
    ∃ x ∈ shortRootGroup Δ E A D E', conjSub A x = C := by
  by_cases hCA : C = A
  · exact ⟨1, Subgroup.one_mem _, by rw [conjSub_one, hCA]⟩
  have F := P.toSp4Frame hC hCA hCD
  obtain ⟨t, htY, S⟩ := exists_triangleSetting hΔ hiso (F.isTriangle hΔ hpts)
  obtain ⟨x, hx, hxC⟩ := P.exists_mem_inf_conjSub_eq hΔ hiso hpts hlines hq hC hCA hCD S htY
  exact ⟨x, hx.2, hxC⟩

theorem ncard_lineOf [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) :
    (lineOf Δ A D).ncard = Nat.card ↥(shortRootGroup Δ E A D E') + 1 := by
  have himage : (fun x => conjSub A x) '' (shortRootGroup Δ E A D E' : Set G) =
      lineOf Δ A D \ {D} := by
    ext C
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_lineStab_iff.1 hx.1.2 A).2 (left_mem_lineOf P.memA), P.conjSub_ne_right hΔ hx⟩
    · rintro ⟨hC, hCD⟩
      obtain ⟨x, hx, hxC⟩ := P.exists_conjSub_eq hΔ hiso hpts hlines hq hC hCD
      exact ⟨x, hx, hxC⟩
  have hinj : Set.InjOn (fun x => conjSub A x) (shortRootGroup Δ E A D E' : Set G) :=
    fun x hx y hy hxy => P.eq_of_conjSub_eq hΔ hiso hpts hq hx hy hxy
  have hcard : Nat.card ↥(shortRootGroup Δ E A D E') =
      (shortRootGroup Δ E A D E' : Set G).ncard :=
    Nat.card_coe_set_eq (shortRootGroup Δ E A D E' : Set G)
  rw [← Set.ncard_sdiff_singleton_add_one (right_mem_lineOf (A := A) P.memD)
    (Set.toFinite _), ← himage, hinj.ncard_image, hcard]

theorem mem_corrN_of_mem_shortRootGroup [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) (hq : 4 ≤ Nat.card A) {x : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (hx1 : x ≠ 1) :
    conjSub A x ∈ lineOf Δ A D ∧ conjSub A x ≠ A ∧ conjSub A x ≠ D ∧
      ∀ t, TriangleSetting Δ A E (conjSub A x) t → t ∈ A ⊔ E ⊔ conjSub A x →
        x ∈ corrN A E t ⊓ Subgroup.centralizer (E : Set G) := by
  have hCl : conjSub A x ∈ lineOf Δ A D := (mem_lineStab_iff.1 hx.1.2 A).2 (left_mem_lineOf P.memA)
  have hCA : conjSub A x ≠ A := fun h => hx1 (P.eq_one_of_conjSub_eq hΔ hiso hpts hq hx h)
  have hCD := P.conjSub_ne_right hΔ hx
  refine ⟨hCl, hCA, hCD, fun t S htY => ?_⟩
  obtain ⟨r, hr, hrC⟩ := P.exists_mem_inf_conjSub_eq hΔ hiso hpts hlines hq hCl hCA hCD S htY
  rw [P.eq_of_conjSub_eq hΔ hiso hpts hq hx hr.2 hrC.symm]
  exact hr.1

theorem shortRootFieldHyp [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A)
    (hlines : MeetsLines Δ) : ShortRootFieldHyp Δ A E D E' :=
  ⟨fun _ hx hx1 => P.mem_corrN_of_mem_shortRootGroup hΔ hiso hpts hlines hq hx hx1,
    fun _ hx hxA => P.eq_one_of_conjSub_eq hΔ hiso hpts hq hx hxA⟩

theorem conjSub_shortRootGroup_torus [Finite G] (P : PairFrame Δ A E D E') (hR : IsRootClass Δ)
    {k : ℕ} (φ : SL2Coords A E k) {h : G} (hh : h ∈ A ⊔ E) {μ : (GaloisField 2 k)ˣ}
    (hμ : φ.mat h = diagElt μ) :
    conjSub (shortRootGroup Δ E A D E') h = shortRootGroup Δ E A D E' ∧
      conjSub (shortRootGroup Δ A E D E') h = shortRootGroup Δ A E D E' := by
  obtain ⟨hA, hE⟩ := φ.conjSub_eq_of_mat_eq_diagElt hh hμ
  have hD : conjSub D h = D := conjSub_of_forall_commute fun d hd =>
    P.comm h hh d (Subgroup.mem_sup_left hd)
  have hE' : conjSub E' h = E' := conjSub_of_forall_commute fun d hd =>
    P.comm h hh d (Subgroup.mem_sup_right hd)
  constructor <;> rw [← shortRootGroup_conjSub hR, hA, hE, hD, hE']

end PairFrame

end CFSG.Timmesfeld.Transvection
