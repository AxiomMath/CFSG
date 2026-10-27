module

public import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.PartTwo.Sec12.Item12ResProofThree

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res5Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec13.Item131bProof
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open scoped commutatorElement

structure HeisCtx (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop extends PartTwoStanding G where
  partTwoF_eq : partTwoF G = partTwoE G
  mem_partTwoE : A ∈ partTwoE G
  eq_of_le : ∀ {B : Subgroup G}, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A
  mem_A : c ∈ A
  orderOf_eq : orderOf c = 3
  mem_thetaComponentsAt : L ∈ thetaComponentsAt 3 c
  le_normalizer : A ≤ Subgroup.normalizer (L : Set G)
  sectionCentralizer_eq :
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G)

section Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem HeisCtx.isElemAbelian (h : HeisCtx G A c L) : CFSG.Assembly.IsElemAbelian 3 A :=
  h.mem_partTwoE.1

theorem HeisCtx.card_eq (h : HeisCtx G A c L) : Nat.card A = 27 :=
  h.mem_partTwoE.2.1

theorem HeisCtx.card_zpowers (h : HeisCtx G A c L) : Nat.card (Subgroup.zpowers c) = 3 := by
  rw [Nat.card_zpowers, h.orderOf_eq]

theorem HeisCtx.ne_one (h : HeisCtx G A c L) : c ≠ 1 := by
  intro h1
  have := h.orderOf_eq
  rw [h1, orderOf_one] at this
  omega

theorem HeisCtx.le_centralizer (h : HeisCtx G A c L) :
    L ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt

theorem HeisCtx.commute (h : HeisCtx G A c L) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x :=
  congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem HeisCtx.A_le_centralizer (h : HeisCtx G A c L) :
    A ≤ Subgroup.centralizer ({c} : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx h.mem_A)

theorem HeisCtx.A_le_normalizer_zpowers (h : HeisCtx G A c L) :
    A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
  h.A_le_centralizer.trans (centralizer_le_normalizer_zpowers c)

omit [Finite G] in
theorem mem_of_le_centralizerH (hFE : partTwoF G = partTwoE G) {E : Subgroup G}
    (hE : E ∈ partTwoE G) {d : G} (hd3 : d ^ 3 = 1)
    (hEd : E ≤ Subgroup.centralizer ({d} : Set G)) : d ∈ E := by
  have hEF : E ∈ partTwoF G := hFE ▸ hE
  have hab := Sec15.isElemAbelian_sup_zpowers hE.1 hd3 fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hEd he)
  have heq := hEF.2.1 _ hab le_sup_left
  exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers d)

@[expose] noncomputable def aBarHomH (h : HeisCtx G A c L) : A →* lBarA c L A where
  toFun a := ⟨QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
      ⟨(a : G), h.A_le_normalizer_zpowers a.2⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right a.2))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul]; rfl)

theorem aBarHomH_apply (h : HeisCtx G A c L) (a : A) :
    ((aBarHomH h a : lBarA c L A) : _) =
      QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
        ⟨(a : G), h.A_le_normalizer_zpowers a.2⟩ :=
  rfl

theorem aBarHomH_injective (h : HeisCtx G A c L) : Function.Injective (aBarHomH h) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 := congrArg Subtype.val ha
  simp only [aBarHomH_apply, Subgroup.coe_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  have h3 : (⟨(a : G), h.A_le_normalizer_zpowers a.2⟩ :
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using h.isElemAbelian.2 _ a.2)
  have hdvd1 := orderOf_dvd_of_pow_eq_one h3
  have hdvd2 := Subgroup.orderOf_dvd_natCard _ h1
  have hord : orderOf (⟨(a : G), h.A_le_normalizer_zpowers a.2⟩ :
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd1 with h' | h'
    · exact h'
    · exact absurd (h' ▸ hdvd2) (solvable_prime_complement_core_characterization
        (H := Subgroup.normalizer (Subgroup.zpowers c : Set G)) Nat.prime_three).2.2.1
  have := orderOf_eq_one_iff.mp hord
  exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem lBar_sup_range_aBarHomH (h : HeisCtx G A c L) :
    (Sec12.lBar c L).subgroupOf (lBarA c L A) ⊔ (aBarHomH h).range = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨_, ⟨z, hz0, rfl⟩⟩ -
  have hLN := le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt
  have hz : z ∈ L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    rw [← Subgroup.subgroupOf_sup hLN h.A_le_normalizer_zpowers]
    exact hz0
  have hnorm : A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      Subgroup.normalizer ((L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
        Subgroup _) : Set (Subgroup.normalizer (Subgroup.zpowers c : Set G))) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (h.le_normalizer (Subgroup.mem_subgroupOf.mp hy)) x
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  rw [sup_comm] at hz
  have hz' : z ∈ ((A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
        Subgroup (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
          Set (Subgroup.normalizer (Subgroup.zpowers c : Set G))) := hz
  rw [hmul] at hz'
  obtain ⟨y, hy, x, hx, rfl⟩ := hz'
  have hxl : (⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))⟩ : lBarA c L A) ∈
      (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hx)
  have hya : (⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)))⟩ : lBarA c L A) ∈
      (aBarHomH h).range :=
    ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have e : (⟨QuotientGroup.mk' _ (y * x), Subgroup.mem_map_of_mem _ hz0⟩ : lBarA c L A) =
      ⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)))⟩ *
      ⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])
  show (⟨QuotientGroup.mk' _ (y * x), Subgroup.mem_map_of_mem _ hz0⟩ : lBarA c L A) ∈ _
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hya hxl

theorem mkC_mem_centerH (h : HeisCtx G A c L) :
    mkC (L := L) h.mem_A ∈ Subgroup.center (lBarA c L A) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, ⟨z, hz, rfl⟩⟩
  apply Subtype.ext
  have hzC : (z : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    sup_le h.le_centralizer h.A_le_centralizer (Subgroup.mem_subgroupOf.mp hz)
  have hcomm : z * ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ =
      ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ * z :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzC)
  simp only [mkC, Subgroup.coe_mul, ← map_mul, hcomm]

theorem mkC_ne_oneH (h : HeisCtx G A c L) : mkC (L := L) h.mem_A ≠ 1 := by
  intro h1
  have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
      (⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ :
        Subgroup.normalizer (Subgroup.zpowers c : Set G)) = 1 :=
    congrArg Subtype.val h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G)
  have hdvd : orderOf (⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ : N) ∣
      Nat.card (aschbacherSolvableCore 3 N) := Subgroup.orderOf_dvd_natCard _ h2
  rw [Subgroup.orderOf_mk, h.orderOf_eq] at hdvd
  exact (solvable_prime_complement_core_characterization (H := N) Nat.prime_three).2.2.1 hdvd

theorem mem_of_mkC_memH (h : HeisCtx G A c L)
    (hmem : (mkC (L := L) h.mem_A : _) ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A)) : c ∈ L := by
  have h3 : (⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ :
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) ^ 3 ^ 1 = 1 := by
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← h.orderOf_eq]
    exact pow_orderOf_eq_one c
  exact mem_of_mk_mem_lBar h.mem_thetaComponentsAt h3 (Subgroup.mem_subgroupOf.mp hmem)

theorem lBar_normalH (h : HeisCtx G A c L) :
    ((Sec12.lBar c L).subgroupOf (lBarA c L A)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨_, ⟨z, hz, rfl⟩⟩ := g
  obtain ⟨l, hl, hlx⟩ := hx
  have hzN : (z : G) ∈ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer h.le_normalizer (Subgroup.mem_subgroupOf.mp hz)
  refine ⟨z * l * z⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hzN _).mp (Subgroup.mem_subgroupOf.mp hl)
  · simp only [map_mul, map_inv, hlx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem isPerfect_lBarH (h : HeisCtx G A c L) : Group.IsPerfect (Sec12.lBar c L) := by
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hLN := le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt
  set e : L ≃* L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
    (Subgroup.subgroupOfEquivOfLe hLN).symm
  have : Group.IsPerfect (L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.ofSurjective
    (f := (QuotientGroup.mk' _).subgroupMap (L.subgroupOf _))
    ((QuotientGroup.mk' _).subgroupMap_surjective _)

theorem lBar_ne_botH (h : HeisCtx G A c L) : Sec12.lBar c L ≠ ⊥ := by
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hq.2.1
  have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
  have : Nontrivial (Sec12.lBar c L) := η.symm.surjective.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this

theorem isPerfect_subgroupOf_lBarH (h : HeisCtx G A c L) :
    Group.IsPerfect ((Sec12.lBar c L).subgroupOf (lBarA c L A)) := by
  have := isPerfect_lBarH h
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective

theorem subgroupOf_lBar_ne_botH (h : HeisCtx G A c L) :
    (Sec12.lBar c L).subgroupOf (lBarA c L A) ≠ ⊥ := by
  intro hbot
  apply lBar_ne_botH h
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, lBar_le_lBarA hx⟩ : lBarA c L A) ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem mem_of_isHeisCentralH (h : HeisCtx G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) : c ∈ L := by
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hZU : (Subgroup.center U).map U.subtype = U ⊓ V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rintro w ⟨hwU, hwV⟩
      refine ⟨⟨w, hwU⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
      exact hcomm u u.2 w hwV
    · rw [hcard, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  let φ : U × V →* lBarA c L A := MonoidHom.noncommCoprod U.subtype V.subtype
    (fun u v => hcomm u u.2 v v.2)
  have hφapp : ∀ y : U × V, φ y = (y.1 : lBarA c L A) * y.2 := fun y => rfl
  have hφ : ∀ x : lBarA c L A, ∃ y : U × V, φ y = x := by
    have hrange : φ.range = ⊤ := by
      rw [eq_top_iff, ← hUV, sup_le_iff]
      constructor
      · intro u hu
        exact ⟨(⟨u, hu⟩, 1), by rw [hφapp]; simp⟩
      · intro v hv
        exact ⟨(1, ⟨v, hv⟩), by rw [hφapp]; simp⟩
    intro x
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top x)
  have hZ : Subgroup.center (lBarA c L A) ≤ V := by
    intro x hx
    obtain ⟨⟨u, v⟩, rfl⟩ := hφ x
    rw [hφapp]
    have huZ : (u : lBarA c L A) ∈ (Subgroup.center U).map U.subtype := by
      refine ⟨u, Subgroup.mem_center_iff.mpr fun u' => Subtype.ext ?_, rfl⟩
      have h1 := Subgroup.mem_center_iff.mp hx (u' : lBarA c L A)
      rw [hφapp] at h1
      have h2 : (v : lBarA c L A) * u' = u' * v := (hcomm u' u'.2 v v.2).symm
      have : (u' : lBarA c L A) * u * v = u * u' * v := by
        calc (u' : lBarA c L A) * u * v = u' * (u * v) := by group
          _ = u * v * u' := h1
          _ = u * (v * u') := by group
          _ = u * (u' * v) := by rw [h2]
          _ = u * u' * v := by group
      exact mul_right_cancel this
    rw [hZU] at huZ
    exact V.mul_mem huZ.2 v.2
  have hcommV : commutator (lBarA c L A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨⟨u, v⟩, rfl⟩ := hφ x
    obtain ⟨⟨u', v'⟩, rfl⟩ := hφ y
    rw [← map_commutatorElement, hφapp]
    have h1 : ((⁅(u, v), (u', v')⁆ : U × V).1 : lBarA c L A) ∈ V := by
      have h2 : (⁅u, u'⁆ : U) ∈ commutator U :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hU.1.2.1] at h2
      have h3 : ((⁅u, u'⁆ : U) : lBarA c L A) ∈ (Subgroup.center U).map U.subtype := ⟨_, h2, rfl⟩
      rw [hZU] at h3
      exact h3.2
    exact V.mul_mem h1 (⁅(u, v), (u', v')⁆ : U × V).2.2
  have hΛperf : Group.IsPerfect Λ := by
    have := isPerfect_lBarH h
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective
  have hΛV : Λ ≤ V := by
    have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
      _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator (lBarA c L A) := Subgroup.commutator_mono le_top le_top
      _ ≤ V := hcommV
  have hVq : IsQuasisimple V := LocalCores.isQuasisimple_of_mulEquiv eV.symm
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
  have hΛn : (Λ.subgroupOf V).Normal := (lBar_normalH h).subgroupOf V
  have hVΛ : V ≤ Λ := by
    rcases LocalCores.quasisimple_normal_subgroups hVq hΛn with htop | hcen
    · intro v hv
      have : (⟨v, hv⟩ : V) ∈ Λ.subgroupOf V := htop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hab : ∀ x y : Λ, x * y = y * x := by
        intro x y
        have hx : (⟨x, hΛV x.2⟩ : V) ∈ Subgroup.center V := hcen x.2
        have := Subgroup.mem_center_iff.mp hx ⟨y, hΛV y.2⟩
        exact Subtype.ext (congrArg Subtype.val this).symm
      have hbot : commutator Λ = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hΛperf.commutator_eq_top] at hbot
      apply lBar_ne_botH h
      rw [eq_bot_iff]
      intro x hx
      have hxΛ : (⟨x, lBar_le_lBarA hx⟩ : lBarA c L A) ∈ Λ := hx
      have h1 : (⟨⟨x, lBar_le_lBarA hx⟩, hxΛ⟩ : Λ) ∈ (⊥ : Subgroup Λ) :=
        hbot ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at h1
      have h2 := congrArg (fun y : Λ => ((y : lBarA c L A) :
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
          aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) h1
      simpa using h2
  exact mem_of_mkC_memH h (hVΛ (hZ (mkC_mem_centerH h)))

theorem mem_zpowers_of_aBarHomH_commute (h : HeisCtx G A c L) (a : A)
    (hcomm : ∀ y ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A),
      aBarHomH h a * y = y * aBarHomH h a) : (a : G) ∈ Subgroup.zpowers c := by
  have hmem := mem_thetaQuotCentralizer_of_mk_commute h.mem_thetaComponentsAt
    (g := ⟨a, h.A_le_normalizer_zpowers a.2⟩) (h.le_normalizer a.2) (fun l hl => by
      have hlN : (l : _) ∈ (L ⊔ A).subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl)
      have hy : (⟨QuotientGroup.mk' _ l, Subgroup.mem_map_of_mem _ hlN⟩ : lBarA c L A) ∈
          (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
        Subgroup.mem_subgroupOf.mpr ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      exact congrArg Subtype.val (hcomm _ hy))
  obtain ⟨-, hzl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hmem
  have hsc : (a : G) ∈
      Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨a.2, fun x hx => ?_⟩
    have h1 := hzl x hx
    have h2 : (a : G) * x * (a : G)⁻¹ * x⁻¹ = x * (x⁻¹ * ((a : G) * x * (a : G)⁻¹)) * x⁻¹ := by
      group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hx) _).mp h1
  rw [h.sectionCentralizer_eq] at hsc
  exact hsc

theorem isHeisCentral_factsH (h : HeisCtx G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ U : Subgroup (lBarA c L A), Sec4.IsHeisThree U ∧
      (∀ u ∈ U, ∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * v = v * u) ∧
      U ⊔ (Sec12.lBar c L).subgroupOf (lBarA c L A) = ⊤ ∧
      (Subgroup.center U).map U.subtype = U ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) := by
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hZU : (Subgroup.center U).map U.subtype = U ⊓ V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rintro w ⟨hwU, hwV⟩
      refine ⟨⟨w, hwU⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
      exact hcomm u u.2 w hwV
    · rw [hcard, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  let φ : U × V →* lBarA c L A := MonoidHom.noncommCoprod U.subtype V.subtype
    (fun u v => hcomm u u.2 v v.2)
  have hφapp : ∀ y : U × V, φ y = (y.1 : lBarA c L A) * y.2 := fun y => rfl
  have hφ : ∀ x : lBarA c L A, ∃ y : U × V, φ y = x := by
    have hrange : φ.range = ⊤ := by
      rw [eq_top_iff, ← hUV, sup_le_iff]
      constructor
      · intro u hu
        exact ⟨(⟨u, hu⟩, 1), by rw [hφapp]; simp⟩
      · intro v hv
        exact ⟨(1, ⟨v, hv⟩), by rw [hφapp]; simp⟩
    intro x
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top x)
  have hcommV : commutator (lBarA c L A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨⟨u, v⟩, rfl⟩ := hφ x
    obtain ⟨⟨u', v'⟩, rfl⟩ := hφ y
    rw [← map_commutatorElement, hφapp]
    have h1 : ((⁅(u, v), (u', v')⁆ : U × V).1 : lBarA c L A) ∈ V := by
      have h2 : (⁅u, u'⁆ : U) ∈ commutator U :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hU.1.2.1] at h2
      have h3 : ((⁅u, u'⁆ : U) : lBarA c L A) ∈ (Subgroup.center U).map U.subtype :=
        ⟨_, h2, rfl⟩
      rw [hZU] at h3
      exact h3.2
    exact V.mul_mem h1 (⁅(u, v), (u', v')⁆ : U × V).2.2
  have hΛperf : Group.IsPerfect Λ := isPerfect_subgroupOf_lBarH h
  have hΛV : Λ ≤ V := by
    have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
      _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator (lBarA c L A) := Subgroup.commutator_mono le_top le_top
      _ ≤ V := hcommV
  have hVq : IsQuasisimple V := LocalCores.isQuasisimple_of_mulEquiv eV.symm
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
  have hΛn : (Λ.subgroupOf V).Normal := (lBar_normalH h).subgroupOf V
  have hVΛ : V ≤ Λ := by
    rcases LocalCores.quasisimple_normal_subgroups hVq hΛn with htop | hcen
    · intro v hv
      have : (⟨v, hv⟩ : V) ∈ Λ.subgroupOf V := htop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hab : ∀ x y : Λ, x * y = y * x := by
        intro x y
        have hx : (⟨x, hΛV x.2⟩ : V) ∈ Subgroup.center V := hcen x.2
        have := Subgroup.mem_center_iff.mp hx ⟨y, hΛV y.2⟩
        exact Subtype.ext (congrArg Subtype.val this).symm
      have hbot : commutator Λ = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hΛperf.commutator_eq_top] at hbot
      apply subgroupOf_lBar_ne_botH h
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx⟩ : Λ) ∈ (⊥ : Subgroup Λ) := hbot ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
  have hVeq : V = Λ := le_antisymm hVΛ hΛV
  subst hVeq
  exact ⟨U, hU, hcomm, hUV, hZU⟩

theorem mkC_eq_aBarHomH (h : HeisCtx G A c L) :
    mkC (L := L) h.mem_A = aBarHomH h ⟨c, h.mem_A⟩ :=
  Subtype.ext rfl

theorem orderOf_mkCH (h : HeisCtx G A c L) : orderOf (mkC (L := L) h.mem_A) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ (mkC_ne_oneH h)
  rw [mkC_eq_aBarHomH h, ← map_pow]
  have : (⟨c, h.mem_A⟩ : A) ^ 3 = 1 := Subtype.ext (by
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← h.orderOf_eq]
    exact pow_orderOf_eq_one c)
  rw [this, map_one]

theorem mkC_mem_lBarH (h : HeisCtx G A c L) (hcL : c ∈ L) :
    mkC (L := L) h.mem_A ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
  Subgroup.mem_subgroupOf.mpr ⟨⟨c, le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt hcL⟩,
    Subgroup.mem_subgroupOf.mpr hcL, rfl⟩

theorem card_center_lBarH (h : HeisCtx G A c L) :
    Nat.card (Subgroup.center ((Sec12.lBar c L).subgroupOf (lBarA c L A))) =
      Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  set e := (Subgroup.subgroupOfEquivOfLe (lBar_le_lBarA (A := A))).trans η.symm
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem exists_U_of_isHeisCentralH (h : HeisCtx G A c L) (hcL : c ∈ L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    ∃ U : Subgroup (lBarA c L A), mkC (L := L) h.mem_A ∈ U ∧ 9 ≤ Nat.card U ∧
      (∀ x ∈ U, x ^ 3 = 1) ∧
      (∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u) ∧
      (∀ u ∈ U, u ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) →
        u ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) ∧
      (∀ a ∈ (aBarHomH h).range, ∀ u ∈ U,
        a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) := by
  obtain ⟨U, hU, hUΛ, hUV, hZU⟩ := isHeisCentral_factsH h hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set z := mkC (L := L) h.mem_A with hz
  have hzΛ : z ∈ Λ := mkC_mem_lBarH h hcL
  set ZΛ := (Subgroup.center Λ).map Λ.subtype with hZΛ
  have hZΛcard : Nat.card ZΛ = 3 := by
    rw [hZΛ, Subgroup.card_map_of_injective Λ.subtype_injective, card_center_lBarH h, hZ3]
  have hUΛZ : U ⊓ Λ ≤ ZΛ := by
    rintro x ⟨hxU, hxΛ⟩
    refine ⟨⟨x, hxΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact (hUΛ x hxU y y.2).symm
  have hUΛcard : Nat.card (U ⊓ Λ : Subgroup _) = 3 := by
    rw [← hZU, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  have hUΛeq : U ⊓ Λ = ZΛ := Subgroup.eq_of_le_of_card_ge hUΛZ (by rw [hZΛcard, hUΛcard])
  have hzZ : z ∈ ZΛ := by
    refine ⟨⟨z, hzΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_center_iff.mp (mkC_mem_centerH h) y
  rw [← hUΛeq] at hzZ
  have hzpow : Subgroup.zpowers z = U ⊓ Λ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_
    rw [hUΛcard, Nat.card_zpowers, orderOf_mkCH h]
  refine ⟨U, hzZ.1, ?_, ?_, hUΛ, ?_, ?_⟩
  · rw [hU.2.1]
    norm_num
  · intro x hx
    have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : U)
    rw [hU.2.2] at h1
    simpa using congrArg Subtype.val h1
  · intro u hu huΛ
    rw [hzpow]
    exact ⟨hu, huΛ⟩
  · intro a _ u hu
    have hcoe := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U Λ hUΛ).2
    have ha : a ∈ ((U ⊔ Λ : Subgroup _) : Set _) := by rw [hUV]; exact Subgroup.mem_top a
    rw [hcoe] at ha
    obtain ⟨u', hu', v', hv', rfl⟩ := Set.mem_mul.mp ha
    have hvu : v' * u = u * v' := (hUΛ u hu v' hv').symm
    have h1 : u' * v' * u * (u' * v')⁻¹ * u⁻¹ = u' * u * u'⁻¹ * u⁻¹ := by
      calc u' * v' * u * (u' * v')⁻¹ * u⁻¹ = u' * (v' * u) * v'⁻¹ * u'⁻¹ * u⁻¹ := by group
        _ = u' * (u * v') * v'⁻¹ * u'⁻¹ * u⁻¹ := by rw [hvu]
        _ = u' * u * u'⁻¹ * u⁻¹ := by group
    rw [h1, hzpow, ← hZU]
    have h2 : (⁅(⟨u', hu'⟩ : U), ⟨u, hu⟩⁆ : U) ∈ commutator U :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hU.1.2.1] at h2
    exact ⟨_, h2, by simp [commutatorElement_def]⟩

theorem exists_E_of_UH (h : HeisCtx G A c L) (hcL : c ∈ L) {U : Subgroup (lBarA c L A)}
    (hzU : mkC (L := L) h.mem_A ∈ U) (hU9 : 9 ≤ Nat.card U) (hU3 : ∀ x ∈ U, x ^ 3 = 1)
    (hUΛ : ∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u)
    (hUΛz : ∀ u ∈ U, u ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) →
      u ∈ Subgroup.zpowers (mkC (L := L) h.mem_A))
    (hAbU : ∀ a ∈ (aBarHomH h).range, ∀ u ∈ U,
      a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) :
    ∃ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∧
      ¬ IsCyclic (E ⊓ L : Subgroup G) ∧ A ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set Ab := (aBarHomH h).range with hAb
  set z := mkC (L := L) h.mem_A with hz
  have hzo : orderOf z = 3 := orderOf_mkCH h
  have hzAb : z ∈ Ab := ⟨⟨c, h.mem_A⟩, (mkC_eq_aBarHomH h).symm⟩
  have hzΛ : z ∈ Λ := mkC_mem_lBarH h hcL
  have hΛn : Λ.Normal := lBar_normalH h
  have hAbΛ : Ab ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hΛn.conj_mem y hy x, fun hy => ?_⟩
    have h1 := hΛn.conj_mem _ hy x⁻¹
    simpa [mul_assoc] using h1
  have hAbel : CFSG.Assembly.IsElemAbelian 3 Ab := by
    have := h.isElemAbelian.1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, rfl⟩⟩ := y
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, mul_comm' a b]
    · rintro _ ⟨a, rfl⟩
      have h3 : a ^ 3 = 1 := Subtype.ext (by simpa using h.isElemAbelian.2 _ a.2)
      rw [← map_pow, h3, map_one]
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, ← Nat.card_congr (MonoidHom.ofInjective (aBarHomH_injective h)).toEquiv,
      h.card_eq]
  have hQcard : Nat.card (⊤ : Subgroup (lBarA c L A)) ≤ 9 * Nat.card Λ := by
    have h1 := CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf hAbΛ
    have h2 : Ab ⊔ Λ = ⊤ := by rw [sup_comm]; exact lBar_sup_range_aBarHomH h
    have h3 : 3 ≤ Nat.card (Ab ⊓ Λ : Subgroup (lBarA c L A)) := by
      have := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr (show z ∈ Ab ⊓ Λ from ⟨hzAb, hzΛ⟩))
      rwa [Nat.card_zpowers, hzo] at this
    rw [h2, hAb27] at h1
    nlinarith
  have hAbUz : ∀ a ∈ Ab, a ∈ U → a ∈ Subgroup.zpowers z := by
    rintro _ ⟨a, rfl⟩ haU
    have hac := mem_zpowers_of_aBarHomH_commute h a (fun y hy => hUΛ _ haU y hy)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hac
    have hai : a = (⟨c, h.mem_A⟩ : A) ^ i := Subtype.ext (by simp [hi])
    rw [hai, map_zpow, ← mkC_eq_aBarHomH h]
    exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨hexp, hcomm, Eb, hEbAU, hEbab, hEb27, hzEb, hEbU, hEbΛ⟩ :=
    exists_elemAbelian_heis (X := lBarA c L A) (Q := ⊤) (Λ := Λ) (Ab := Ab) (U := U) (z := z) le_top
      le_top le_top hQcard hAbΛ hAbel hAb27 hzAb hzΛ
      (fun x _ => (Subgroup.mem_center_iff.mp (mkC_mem_centerH h) x).symm) hzo hzU hU9 hU3 hUΛ
      hUΛz hAbU hAbUz
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3
    (Subgroup.normalizer (Subgroup.zpowers c : Set G))) with hπ
  set M := (L ⊔ A).subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hM
  set Ebar := Eb.map (lBarA c L A).subtype with hEbar
  set B := (Ab ⊔ Eb).map (lBarA c L A).subtype with hB
  have hAbEbU : Ab ⊔ Eb ≤ Ab ⊔ U := sup_le le_sup_left hEbAU
  have hB3 : IsPGroup 3 B := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have h1 := hexp w (hAbEbU hw)
    simpa using congrArg Subtype.val h1
  have hBM : B ≤ M.map π := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  set A₁ := A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hA₁
  have hA₁3 : IsPGroup 3 A₁ := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using h.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2)
  have hA₁M : A₁ ≤ M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  have hπa : ∀ a : Subgroup.normalizer (Subgroup.zpowers c : Set G), ∀ ha : (a : G) ∈ A,
      π a = ((aBarHomH h ⟨a, ha⟩ : lBarA c L A) : _) := fun a ha => by
    rw [aBarHomH_apply]
  have hA₁B : A₁.map π ≤ B := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hπa a (Subgroup.mem_subgroupOf.mp ha)]
    exact ⟨_, Subgroup.mem_sup_left ⟨_, rfl⟩, rfl⟩
  obtain ⟨S, hA₁S, hSM, hS3, hSB⟩ := exists_isPGroup_le_map_eq hB3 hBM hA₁3 hA₁M hA₁B
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
  set E₁ := S ⊓ Ebar.comap π with hE₁
  have hE₁S : E₁ ≤ S := inf_le_left
  have hE₁map : E₁.map π = Ebar := by
    rw [hE₁, map_inf_comap_eq, hSB]
    exact inf_eq_right.mpr (Subgroup.map_mono le_sup_right)
  have hinjE : Set.InjOn π E₁ := hinj.mono hE₁S
  have hE₁card : Nat.card E₁ = 27 := by
    rw [← card_map_eq_of_injOn π hinjE, hE₁map, hEbar,
      Subgroup.card_map_of_injective (lBarA c L A).subtype_injective, hEb27]
  have hE₁ab : CFSG.Assembly.IsElemAbelian 3 E₁ :=
    isElemAbelian_of_injOn π hinjE (by rw [hE₁map]; exact isElemAbelian_map hEbab _)
  have hEmem : ∀ e ∈ E₁, ∃ eb ∈ Eb, ((eb : lBarA c L A) : _) = π e := by
    rintro e ⟨-, he⟩
    obtain ⟨eb, heb, hebe⟩ := he
    exact ⟨eb, heb, hebe⟩
  have hzEbar : ∀ w ∈ Subgroup.zpowers z, w ∈ Eb := fun w hw => (Subgroup.zpowers_le.mpr hzEb) hw
  have hzAbar : ∀ w ∈ Subgroup.zpowers z, w ∈ Ab := fun w hw => (Subgroup.zpowers_le.mpr hzAb) hw
  have hconjE : ∀ a ∈ A₁, ∀ e ∈ E₁, a * e * a⁻¹ ∈ E₁ := by
    intro a ha e he
    refine ⟨S.mul_mem (S.mul_mem (hA₁S ha) (hE₁S he)) (S.inv_mem (hA₁S ha)), ?_⟩
    obtain ⟨eb, heb, hebe⟩ := hEmem e he
    set a' := aBarHomH h ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
    have ha' : a' ∈ Ab := ⟨_, rfl⟩
    have hk := hcomm a' ha' eb (hEbAU heb)
    have hmem : a' * eb * a'⁻¹ ∈ Eb := by
      have h1 : a' * eb * a'⁻¹ = (a' * eb * a'⁻¹ * eb⁻¹) * eb := by group
      rw [h1]
      exact Eb.mul_mem (hzEbar _ hk) heb
    refine ⟨_, hmem, ?_⟩
    change ((a' : _) * (eb : _) * (a' : _)⁻¹) = π (a * e * a⁻¹)
    rw [hebe, map_mul, map_mul, map_inv, hπa a (Subgroup.mem_subgroupOf.mp ha)]
    rfl
  have hconjA : ∀ e ∈ E₁, ∀ a ∈ A₁, e * a * e⁻¹ ∈ A₁ := by
    intro e he a ha
    have hxS : e * a * e⁻¹ ∈ S := S.mul_mem (S.mul_mem (hE₁S he) (hA₁S ha)) (S.inv_mem (hE₁S he))
    obtain ⟨eb, heb, hebe⟩ := hEmem e he
    set a' := aBarHomH h ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
    have ha' : a' ∈ Ab := ⟨_, rfl⟩
    have hk := hcomm a'⁻¹ (Ab.inv_mem ha') eb (hEbAU heb)
    have hmem : eb * a' * eb⁻¹ ∈ Ab := by
      have h1 : eb * a' * eb⁻¹ = a' * (a'⁻¹ * eb * a'⁻¹⁻¹ * eb⁻¹) := by group
      rw [h1]
      exact Ab.mul_mem ha' (hzAbar _ hk)
    obtain ⟨b, hb⟩ := hmem
    have hb₁ : (⟨b, h.A_le_normalizer_zpowers b.2⟩ :
        Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∈ A₁ :=
      Subgroup.mem_subgroupOf.mpr b.2
    have heq : π (e * a * e⁻¹) = π ⟨b, h.A_le_normalizer_zpowers b.2⟩ := by
      have h3 : π ⟨b, h.A_le_normalizer_zpowers b.2⟩ = ((aBarHomH h b : lBarA c L A) : _) :=
        hπa ⟨b, h.A_le_normalizer_zpowers b.2⟩ b.2
      rw [h3, map_mul, map_mul, map_inv, ← hebe, hπa a (Subgroup.mem_subgroupOf.mp ha), hb]
      rfl
    have := hinj hxS (hA₁S hb₁) heq
    rw [this]
    exact hb₁
  have hE₁N : E₁ ≤ Subgroup.normalizer (A₁ : Set (Subgroup.normalizer
      (Subgroup.zpowers c : Set G))) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨hconjA e he a, fun ha => ?_⟩
    have h1 := hconjA e⁻¹ (E₁.inv_mem he) _ ha
    simpa [mul_assoc] using h1
  have hA₁N : A₁ ≤ Subgroup.normalizer (E₁ : Set (Subgroup.normalizer
      (Subgroup.zpowers c : Set G))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨hconjE a ha e, fun he => ?_⟩
    have h1 := hconjE a⁻¹ (A₁.inv_mem ha) _ he
    simpa [mul_assoc] using h1
  have hAmap : A₁.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype = A := by
    rw [hA₁, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.A_le_normalizer_zpowers]
  set E := E₁.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype with hE
  have hLAN : L ⊔ A ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer h.le_normalizer
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := (isElemAbelian_map hE₁ab _).2
  have hEcard : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective Subtype.coe_injective, hE₁card]
  have hcardInf : ∀ T : Subgroup (lBarA c L A), Nat.card (Eb ⊓ T : Subgroup _) ≤
      Nat.card ((E₁ ⊓ (T.map (lBarA c L A).subtype).comap π).map
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype) := by
    intro T
    rw [Subgroup.card_map_of_injective Subtype.coe_injective,
      ← card_map_eq_of_injOn π (hinjE.mono inf_le_left), map_inf_comap_eq, hE₁map, hEbar,
      ← Subgroup.map_inf_eq _ _ _ (lBarA c L A).subtype_injective,
      Subgroup.card_map_of_injective (lBarA c L A).subtype_injective]
  refine ⟨E, le_inf ?_ ?_, isElemAbelian_map hE₁ab _, hEcard, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hSM (hE₁S he))
  · rw [← hAmap]
    exact (Subgroup.map_mono hE₁N).trans (Subgroup.le_normalizer_map _)
  · refine not_isCyclic_of_nine_le (fun x hx => hEexp x hx.1) ?_
    refine (hEbU.trans (hcardInf U)).trans (Subgroup.card_le_of_le ?_)
    rintro _ ⟨e, ⟨he, heU⟩, rfl⟩
    refine ⟨⟨e, he, rfl⟩, ?_⟩
    obtain ⟨u₀, hu₀, hu₀e⟩ := heU
    refine mem_thetaQuotCentralizer_of_mk_commute h.mem_thetaComponentsAt
      (hLAN (Subgroup.mem_subgroupOf.mp (hSM (hE₁S he)))) fun l hl => ?_
    have hlA : l ∈ M := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl)
    have hlb : (⟨π l, Subgroup.mem_map_of_mem π hlA⟩ : lBarA c L A) ∈ Λ :=
      Subgroup.mem_subgroupOf.mpr ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have h1 := congrArg Subtype.val (hUΛ u₀ hu₀ _ hlb)
    simp only [Subgroup.coe_mul] at h1
    change π e * π l = π l * π e
    rw [← hu₀e]
    exact h1
  · refine not_isCyclic_of_nine_le (fun x hx => hEexp x hx.1) ?_
    refine (hEbΛ.trans (hcardInf Λ)).trans (Subgroup.card_le_of_le ?_)
    rintro _ ⟨e, ⟨he, heΛ⟩, rfl⟩
    refine ⟨⟨e, he, rfl⟩, ?_⟩
    obtain ⟨l₀, hl₀, hl₀e⟩ := heΛ
    have he3 : e ^ 3 ^ 1 = 1 := by
      rw [pow_one]
      exact hE₁ab.2 e he
    refine mem_of_mk_mem_lBar h.mem_thetaComponentsAt he3 ?_
    have := Subgroup.mem_subgroupOf.mp hl₀
    change π e ∈ Sec12.lBar c L
    rw [← hl₀e]
    exact this
  · intro a ha
    have ha₁ : (⟨a, h.A_le_normalizer_zpowers ha⟩ :
        Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∈ A₁ := Subgroup.mem_subgroupOf.mpr ha
    exact Subgroup.le_normalizer_map _ ⟨_, hA₁N ha₁, rfl⟩

theorem no_E27_leH (hD : HeisCtx G A c L) (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L))
    {D : Subgroup G} (hDe : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27)
    (hDC : D ≤ Sec4.thetaQuotCentralizer L) : False := by
  have hFE : partTwoF G = partTwoE G := hD.partTwoF_eq
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := (Sec12.isQuasisimple_thetaQuot_of_mem hD.mem_thetaComponentsAt).1
    rwa [Group.isPerfect_def] at h1
  exact Sec12.false_of_E27_le_thetaQuotCentralizer hFE hperf (card_center_eq_three hty)
    (KFacts.two_dvd_card_of_item122_type (type122_of hty)) hDe hD27 hDC

theorem e_factsH (hD : HeisCtx G A c L) (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L))
    (hcL : c ∈ L) {E : Subgroup G} (hEle : E ≤ L ⊔ A) (hEe : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hEC : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
    (hEL : ¬ IsCyclic (E ⊓ L : Subgroup G)) :
    c ∈ E ∧ Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 ∧
      Nat.card (E ⊓ L : Subgroup G) = 9 ∧
      (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hEe.2
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEc : E ≤ Subgroup.centralizer ({c} : Set G) :=
    hEle.trans (sup_le hD.le_centralizer hD.A_le_centralizer)
  have hcC : c ∈ Sec4.thetaQuotCentralizer L :=
    Sec12.mem_thetaQuotCentralizer_of_central hcL hD.le_centralizer
  have hZ3 := card_center_eq_three hty
  have hdvd : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_dvd_of_le hS
  set C := E ⊓ Sec4.thetaQuotCentralizer L with hCdef
  have hC9 : Nat.card C = 9 := by
    have h9 := nine_le_card (S := C) (fun x hx => hE3 x hx.1) hEC
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd C inf_le_left)
    interval_cases k
    · rw [hk] at h9; norm_num at h9
    · rw [hk] at h9; norm_num at h9
    · rw [hk]; norm_num
    · exfalso
      have hCE : C = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE27]; norm_num)
      exact no_E27_leH hD hty hEe hE27 (hCE ▸ inf_le_right)
  have hcE : c ∈ E := by
    by_contra hcE
    have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
    have hCe : CFSG.Assembly.IsElemAbelian 3 C := isElemAbelian_of_le hEe inf_le_left
    have hDe := Sec15.isElemAbelian_sup_zpowers hCe hc3 fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hEc he.1))
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (C : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun e he => ?_
      have hce : c * e = e * c := (Subgroup.mem_centralizer_singleton_iff.mp (hEc he.1)).symm
      rw [hce, mul_inv_cancel_right]
      exact he
    have hcard := Sec6.card_sup_mul_card_inf hcN
    have hbot : Subgroup.zpowers c ⊓ C = ⊥ := by
      rw [inf_comm]
      exact Sec12.inf_zpowers_eq_bot_of_not_mem hD.orderOf_eq fun h => hcE h.1
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, hC9] at hcard
    rw [sup_comm] at hcard
    exact no_E27_leH hD hty hDe (by rw [hcard]) (sup_le inf_le_right (Subgroup.zpowers_le.mpr hcC))
  have hCL : ∀ S : Subgroup G, S ≤ C → S ≤ L → Nat.card S ≤ 3 := fun S hSC hSL => by
    have hS3 : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hE3 g (hSC g.2).1)⟩
    have h := Sec19.Step1910O2Proof.card_le_card_center_thetaQuot hS3 hSL
      (hSC.trans inf_le_right)
    rwa [hZ3] at h
  have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have h9 := nine_le_card (S := E ⊓ L) (fun x hx => hE3 x hx.1) hEL
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd _ inf_le_left)
    interval_cases k
    · rw [hk] at h9; norm_num at h9
    · rw [hk] at h9; norm_num at h9
    · rw [hk]; norm_num
    · exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE27]; norm_num)
      have hEL'' : E ≤ L := calc E = E ⊓ L := hEL'.symm
        _ ≤ L := inf_le_right
      have h := hCL C le_rfl (inf_le_left.trans hEL'')
      omega
  refine ⟨hcE, hC9, hEL9, ?_⟩
  have hTN : C ≤ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := fun t ht =>
    Subgroup.mem_normalizer_fintype fun b hb => by
      rw [hEcomm t ht.1 b hb.1, mul_inv_cancel_right]
      exact hb
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
  have h1 := Sec6.card_sup_mul_card_inf hTN
  have h2 : Nat.card (C ⊓ (E ⊓ L) : Subgroup G) ≤ 3 :=
    hCL _ inf_le_left (inf_le_right.trans inf_le_right)
  have hpos : 0 < Nat.card (C ⊓ (E ⊓ L) : Subgroup G) := Nat.card_pos
  rw [hC9, hEL9] at h1
  rw [hE27]
  nlinarith

theorem range_aBarHomH_inf_lBar (hD : HeisCtx G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) (hcL : c ∈ L)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    (aBarHomH hD).range ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) =
      Subgroup.zpowers (mkC (L := L) hD.mem_A) := by
  obtain ⟨U, hU, hUΛ, -, -⟩ := isHeisCentral_factsH hD hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set Ab := (aBarHomH hD).range with hAb
  set N := Subgroup.centralizer (Λ : Set (lBarA c L A)) with hN
  have hUN : U ≤ N := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hUΛ u hu v hv).symm
  have hU27 : Nat.card U = 27 := hU.2.1
  have hΛn : Λ.Normal := lBar_normalH hD
  have hNΛ : Nat.card (N ⊓ Λ : Subgroup (lBarA c L A)) ≤ 3 := by
    have hle : (N ⊓ Λ).subgroupOf Λ ≤ Subgroup.center Λ := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.1) y y.2)
    have h1 : Nat.card ((N ⊓ Λ).subgroupOf Λ) = Nat.card (N ⊓ Λ : Subgroup (lBarA c L A)) := by
      rw [← Subgroup.card_map_of_injective Λ.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_assoc, inf_idem]
    calc Nat.card (N ⊓ Λ : Subgroup (lBarA c L A)) = Nat.card ((N ⊓ Λ).subgroupOf Λ) := h1.symm
      _ ≤ Nat.card (Subgroup.center Λ) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [card_center_lBarH hD, hZ3]
  have hall : ∀ x : lBarA c L A, x ∈ Subgroup.normalizer (Λ : Set (lBarA c L A)) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hΛn.conj_mem y hy x, fun hy => by
      have h1 := hΛn.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using h1⟩
  have hNnorm : N ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := fun x _ => hall x
  have hAbnorm : Ab ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := fun x _ => hall x
  have h1 := Sec6.card_sup_mul_card_inf hNnorm
  have h2 := Sec6.card_sup_mul_card_inf hAbnorm
  have hAbΛ : Ab ⊔ Λ = ⊤ := by
    rw [sup_comm]
    exact lBar_sup_range_aBarHomH hD
  have hle : Nat.card (N ⊔ Λ : Subgroup (lBarA c L A)) ≤ Nat.card (Ab ⊔ Λ : Subgroup _) := by
    rw [hAbΛ]
    exact Subgroup.card_le_of_le le_top
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, ← Nat.card_congr (MonoidHom.ofInjective (aBarHomH_injective hD)).toEquiv,
      hD.card_eq]
  have hN27 : 27 ≤ Nat.card N := hU27 ▸ Subgroup.card_le_of_le hUN
  have hΛpos : 0 < Nat.card Λ := Nat.card_pos
  have hkey : Nat.card (Ab ⊓ Λ : Subgroup (lBarA c L A)) ≤ 3 := by
    set x := Nat.card (Ab ⊓ Λ : Subgroup (lBarA c L A))
    set l := Nat.card Λ
    have h3 : Nat.card N * l ≤ Nat.card (Ab ⊔ Λ : Subgroup _) * 3 := by
      rw [← h1]
      exact Nat.mul_le_mul hle hNΛ
    have h4 : 27 * l * x ≤ 81 * l := by
      calc 27 * l * x ≤ Nat.card N * l * x := by
            exact Nat.mul_le_mul (Nat.mul_le_mul hN27 le_rfl) le_rfl
        _ ≤ Nat.card (Ab ⊔ Λ : Subgroup _) * 3 * x := Nat.mul_le_mul h3 le_rfl
        _ = 3 * (Nat.card (Ab ⊔ Λ : Subgroup _) * x) := by ring
        _ = 81 * l := by rw [h2, hAb27]; ring
    have h5 : l * (27 * x) ≤ l * 81 := by nlinarith
    have h6 := Nat.le_of_mul_le_mul_left h5 hΛpos
    omega
  set z := mkC (L := L) hD.mem_A with hz
  have hzAb : z ∈ Ab := ⟨⟨c, hD.mem_A⟩, (mkC_eq_aBarHomH hD).symm⟩
  have hzΛ : z ∈ Λ := mkC_mem_lBarH hD hcL
  have hzeq : Subgroup.zpowers z = Ab ⊓ Λ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzAb, hzΛ⟩) ?_
    rw [Nat.card_zpowers, orderOf_mkCH hD]
    exact hkey
  exact hzeq.symm

theorem inf_le_zpowersH (hD : HeisCtx G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) (hcL : c ∈ L)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    A ⊓ L ≤ Subgroup.zpowers c := by
  have hzeq := (range_aBarHomH_inf_lBar hD hH hcL hZ3).symm
  intro a ha
  set a' : A := ⟨a, ha.1⟩ with ha'
  have hmem : aBarHomH hD a' ∈ (aBarHomH hD).range ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) := by
    refine ⟨⟨a', rfl⟩, Subgroup.mem_subgroupOf.mpr ?_⟩
    rw [aBarHomH_apply]
    exact ⟨⟨a, hD.A_le_normalizer_zpowers ha.1⟩, Subgroup.mem_subgroupOf.mpr ha.2, rfl⟩
  rw [← hzeq] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : aBarHomH hD ((⟨c, hD.mem_A⟩ : A) ^ k) = aBarHomH hD a' := by
    rw [map_zpow, ← mkC_eq_aBarHomH hD, hk]
  have heq := aBarHomH_injective hD hk'
  have : a = c ^ k := by
    have h := congrArg Subtype.val heq
    simpa [ha'] using h.symm
  rw [this]
  exact Subgroup.zpow_mem_zpowers c k

theorem le_lcBarH (hD : HeisCtx G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) :
    A ≤ Sec12.lcBar c L := by
  obtain ⟨U, -, hUΛ, hUV, -⟩ := isHeisCentral_factsH hD hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  intro a ha
  refine ⟨⟨a, hD.A_le_normalizer_zpowers ha⟩, ?_, rfl⟩
  change QuotientGroup.mk' _ ⟨a, hD.A_le_normalizer_zpowers ha⟩ ∈
    Sec12.lBar c L ⊔ Subgroup.centralizer (Sec12.lBar c L : Set _)
  have hmem : aBarHomH hD ⟨a, ha⟩ ∈ U ⊔ Λ := by
    rw [hUV]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (lBarA c L A).subtype hmem
  rw [Subgroup.coe_subtype, aBarHomH_apply, Subgroup.map_sup] at hmap
  refine (sup_le ?_ ?_ : _ ≤ Sec12.lBar c L ⊔ Subgroup.centralizer (Sec12.lBar c L : Set _))
    hmap
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    have h := hUΛ u hu ⟨x, lBar_le_lBarA hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    exact (congrArg Subtype.val h).symm
  · rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hv)

theorem inf_thetaQuotCentralizer_eqH (hD : HeisCtx G A c L) :
    A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
  have hsc := hD.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
  exact SetLike.coe_injective hsc

theorem sec12StdBar_of_heisH (hD : HeisCtx G A c L) (hcL : c ∈ L) {E : Subgroup G}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hcE : c ∈ E)
    (hC9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hsup : (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) = E)
    (hAN : A ≤ Subgroup.normalizer (E : Set G)) : Sec12.Sec12StdBar G E c L := by
  have hst := hD.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G := hD.partTwoF_eq
  have hAC := inf_thetaQuotCentralizer_eqH hD
  refine ⟨hst, hFE, ⟨hEe, hE27⟩, hcE, hD.ne_one, hD.mem_thetaComponentsAt, hcL, hC9, hsup, ?_⟩
  set H := Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)
    with hH
  have hAH : A ≤ H := fun a ha => ⟨hAN ha, hD.A_le_normalizer_zpowers ha⟩
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 g g.2)⟩
  obtain ⟨Q, hQ⟩ := (hA3.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨Q, rfl⟩, fun hle => ?_⟩
  have hAP : ∀ a ∈ A, a ∈ (Q : Subgroup H).map H.subtype := fun a ha =>
    ⟨⟨a, hAH ha⟩, hQ (Subgroup.mem_comap.mpr ha), rfl⟩
  have hDc : E ⊓ Sec4.thetaQuotCentralizer L ≤ Subgroup.zpowers c := by
    intro d hd
    obtain ⟨z, hz, hzd⟩ := hle hd
    have hdA : d ∈ A := mem_of_le_centralizerH hFE hD.mem_partTwoE (hEe.2 d hd.1)
      fun a ha => by
        have h1 := Subgroup.mem_center_iff.mp hz ⟨a, hAP a ha⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← hzd]
        exact (congrArg Subtype.val h1)
    rw [← hAC]
    exact ⟨hdA, hd.2⟩
  have h1 := Subgroup.card_le_of_le hDc
  rw [Nat.card_zpowers, hD.orderOf_eq, hC9] at h1
  omega

theorem normalizer_le_of_heis_threeH (h125 : Sec12.Item125BarThree) (hD : HeisCtx G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hcL := mem_of_isHeisCentralH hD hH
  have hZ3 := card_center_eq_three hty
  obtain ⟨U, hzU, hU9, hU3, hUΛ, hUΛz, hAbU⟩ := exists_U_of_isHeisCentralH hD hcL hH hZ3
  obtain ⟨E, hEle, hEe, hE27, hEC, hEL, hAN⟩ :=
    exists_E_of_UH hD hcL hzU hU9 hU3 hUΛ hUΛz hAbU
  obtain ⟨hcE, hC9, -, hsup⟩ := e_factsH hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hstd := sec12StdBar_of_heisH hD hcL hEe hE27 hcE hC9 hsup hAN
  have hB3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
    rw [inf_thetaQuotCentralizer_eqH hD, hD.card_zpowers]
  have hAL3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
    have heq : A ⊓ L = Subgroup.zpowers c :=
      le_antisymm (inf_le_zpowersH hD hH hcL hZ3)
        (Subgroup.zpowers_le.mpr ⟨hD.mem_A, hcL⟩)
    rw [heq, hD.card_zpowers]
  exact h125 G E c L hstd (type122_of hty) A ⟨hD.isElemAbelian, hD.card_eq⟩ (le_lcBarH hD hH)
    hD.mem_A hB3 hAL3

end Ctx

end CFSG.RankThree.PartTwo.Sec21.Item2130Res5Proof
