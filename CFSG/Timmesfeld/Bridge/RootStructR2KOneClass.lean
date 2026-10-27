module

public import CFSG.Timmesfeld.Bridge.RootStructR2KOneBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity RootClosure
open scoped commutatorElement

namespace RootKOne

namespace KOneConf

variable {G : Type} [Group G] {D : Set G} {q : ℕ} {a x y h : G} {T₁ T₂ : Subgroup G}
  (K1 : KOneConf G D q a x y h T₁ T₂)
include K1

theorem finite : Finite G := K1.counter.hyp.finite

theorem root : IsRootInvolutionSet D := K1.counter.hyp.root

theorem isClass : ∃ d₀ : G, D = {g | IsConj d₀ g} := K1.counter.hyp.isClass

theorem conj_mem (g : G) {z : G} (hz : z ∈ D) : g * z * g⁻¹ ∈ D :=
  conj_mem_of_isClass K1.isClass g hz

theorem lineSetting : LineSetting G D := RootMany.lineSetting_of_counter K1.counter

theorem noPolar : Moufang.NoPolar D := by
  obtain ⟨b, hb, d, hd, hbd, hbdD, hdT, hTI⟩ := K1.lineSetting.line
  exact noPolar_of_lineTI K1.counter.hyp K1.counter.closure K1.counter.special K1.counter.conn hb
    hd hbd hbdD hdT hTI

theorem mem_rootSet_of_commute {c : G} (hcD : c ∈ D)
    (hcU : c ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) (hac : Commute a c) :
    c ∈ rootSet D a := by
  by_contra hcT
  rcases K1.lineSetting.mem_rootSet_or_collinear K1.ha hcD hac.symm with h' | ⟨-, h'⟩
  · exact hcT h'
  · exact K1.false_of_collinear hcD hcU hac h' hcT

theorem orderOf_mul_ne_four {w : G} (hw : w ∈ D)
    (hwU : w ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) : orderOf (a * w) ≠ 4 := by
  intro h4
  have hD := K1.root
  obtain ⟨hsqD, hac, hwc, -⟩ := sq_mem_of_orderOf_eq_four hD K1.ha hw h4
  refine K1.false_of_collinear hsqD (Subgroup.pow_mem _ (Subgroup.mul_mem _ K1.a_mem_U hwU) 2)
    hac (mul_sq_mem_of_orderOf_eq_four K1.isClass hD K1.ha hw h4) fun hT => ?_
  exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one K1.ha) (hD.mul_self_eq_one hw) h4
    ((hT.2 w hw).1 hwc.symm)

theorem conj_inv_mem {g w : G} (hgU : g ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)
    (hw : w ∈ D) (hwU : w ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) :
    g⁻¹ * w * g ∈ D ∧ g⁻¹ * w * g ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y := by
  refine ⟨by simpa using K1.conj_mem g⁻¹ hw, ?_⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgU) hwU) hgU

theorem mem_rootSet_of_mem_classIn {e c : G}
    (he : e ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) (hcD : c ∈ D)
    (hcU : c ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) (hec : Commute e c) :
    c ∈ rootSet D e := by
  obtain ⟨g, hgU, rfl⟩ := he
  obtain ⟨hc'D, hc'U⟩ := K1.conj_inv_mem hgU hcD hcU
  have hc' : g⁻¹ * c * g ∈ rootSet D a := K1.mem_rootSet_of_commute hc'D hc'U (by
    have := (Commute.conj_iff g⁻¹).2 hec
    simpa [mul_assoc] using this)
  rw [rootSet_conj K1.isClass]
  exact ⟨_, hc', by simp [mul_assoc]⟩

theorem orderOf_mul_ne_four_of_mem_classIn {e w : G}
    (he : e ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) (hw : w ∈ D)
    (hwU : w ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) : orderOf (e * w) ≠ 4 := by
  obtain ⟨g, hgU, rfl⟩ := he
  obtain ⟨hw'D, hw'U⟩ := K1.conj_inv_mem hgU hw hwU
  have h1 := K1.orderOf_mul_ne_four hw'D hw'U
  rwa [show a * (g⁻¹ * w * g) = g⁻¹ * (g * a * g⁻¹ * w) * g⁻¹⁻¹ by group, orderOf_conj_eq] at h1

theorem mem_D_of_mem_classIn {e : G}
    (he : e ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) : e ∈ D :=
  classIn_subset_of_normal (fun g _ hz => K1.conj_mem g hz) _ K1.ha he

theorem mem_U_of_mem_classIn {e : G}
    (he : e ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) :
    e ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y :=
  classIn_subset _ K1.a_mem_U he

theorem x_mem_classIn : x ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a :=
  mem_classIn_of_odd K1.root K1.ha K1.hx K1.a_mem_U K1.x_mem_U K1.hoddax

theorem y_mem_classIn : y ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a :=
  mem_classIn_of_odd K1.root K1.ha K1.hy K1.a_mem_U K1.y_mem_U K1.hodday

theorem mem_classIn_of_mem_rootSet {t : G} (ht : t ∈ rootSet D a) :
    t ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a := by
  have hD := K1.root
  have htx := opposite_of_mem_rootSet_of_opposite hD K1.hx K1.ha (mem_rootSet_self K1.hx) ht
    ⟨fun h' => K1.hax h'.symm, by rw [orderOf_mul_comm_eq]; exact K1.hoddax⟩
  rw [← classIn_eq_of_mem K1.x_mem_classIn]
  exact mem_classIn_of_odd hD K1.hx ht.1 K1.x_mem_U
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a ht))) htx.2

theorem closure_subClass :
    Subgroup.closure (subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) = ⊤ := by
  have hD := K1.root
  set U := rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y with hU
  have hSc : rootSet D a ∪ rootSet D x ∪ rootSet D y ⊆ classIn U a := by
    rintro t ((ht | ht) | ht)
    · exact K1.mem_classIn_of_mem_rootSet ht
    · exact mem_classIn_of_odd hD K1.ha ht.1 K1.a_mem_U
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right (rootSet_subset_rootGroup D x ht)))
        (opposite_of_mem_rootSet_of_opposite hD K1.ha K1.hx (mem_rootSet_self K1.ha) ht
          ⟨K1.hax, K1.hoddax⟩).2
    · exact mem_classIn_of_odd hD K1.ha ht.1 K1.a_mem_U
        (Subgroup.mem_sup_right (rootSet_subset_rootGroup D y ht))
        (opposite_of_mem_rootSet_of_opposite hD K1.ha K1.hy (mem_rootSet_self K1.ha) ht
          ⟨K1.hay, K1.hodday⟩).2
  have hUS : U = Subgroup.closure (rootSet D a ∪ rootSet D x ∪ rootSet D y) := by
    rw [Subgroup.closure_union, Subgroup.closure_union]
    rfl
  exact closure_subClass_eq_top hSc hUS

theorem not_mem_pCore {w : G} (hw : w ∈ D) :
    w ∉ (CFSG.pCore 2 ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)).map
      (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y).subtype := by
  intro hwP
  have hD := K1.root
  set U := rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y with hU
  set P : Subgroup G := (CFSG.pCore 2 U).map U.subtype with hP
  have hP2 : IsPGroup 2 P := (CFSG.pCore_isPGroup).map U.subtype
  have hPn : ∀ g ∈ U, ∀ v ∈ P, g * v * g⁻¹ ∈ P := by
    intro g hg v hv
    obtain ⟨v', hv', rfl⟩ := hv
    exact ⟨⟨g, hg⟩ * v' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem _ hv' _, by simp⟩
  have hwU : w ∈ U := by
    obtain ⟨w', -, rfl⟩ := hwP
    exact w'.2
  have hodd1 : ∀ e ∈ D, e ∈ U → Odd (orderOf (w * e)) → w * e = 1 := by
    intro e he heU hodd
    have hsq : (w * e) ^ 2 ∈ P := by
      have h1 := P.mul_mem hwP (hPn e heU w hwP)
      rwa [hD.inv_eq he, show w * (e * w * e) = (w * e) ^ 2 by rw [sq]; group] at h1
    have h2 : (w * e) ^ 2 = 1 :=
      Special.eq_one_of_mem_of_isPGroup hP2 hsq (Odd.of_dvd_nat hodd (orderOf_pow_dvd 2))
    have h3 : orderOf (w * e) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h' | h'
      · exact h'
      · rw [h'] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.1 h3
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hw K1.ha with hwa | h4 | ⟨hodd, hnc⟩
  ·
    have hwT := K1.mem_rootSet_of_commute hw hwU hwa.symm
    have hopp := opposite_of_mem_rootSet_of_opposite hD K1.ha K1.hx hwT (mem_rootSet_self K1.hx)
      ⟨K1.hax, K1.hoddax⟩
    have hwx : w = x :=
      (eq_inv_of_mul_eq_one_left (hodd1 x K1.hx K1.x_mem_U hopp.2)).trans (hD.inv_eq K1.hx)
    exact hopp.1 (by rw [hwx])
  · exact K1.orderOf_mul_ne_four hw hwU (by rwa [orderOf_mul_comm_eq])
  · have hwa : w = a :=
      (eq_inv_of_mul_eq_one_left (hodd1 a K1.ha K1.a_mem_U hodd)).trans (hD.inv_eq K1.ha)
    exact hnc (by rw [hwa])

theorem isOddTransp_subClass :
    Asc72.IsOddTransp (subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) := by
  have hD := K1.root
  refine ⟨fun d hd => ?_, fun d hd e he => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hD.orderOf_eq_two (K1.mem_D_of_mem_classIn hd)
  · have hoG : orderOf (d * e) = orderOf ((d : G) * e) := by
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    rw [hoG]
    rcases hD.orderOf_mul (K1.mem_D_of_mem_classIn hd) (K1.mem_D_of_mem_classIn he) with
      h' | h' | h'
    · exact Or.inl (by rw [h'])
    · exact absurd h' (K1.orderOf_mul_ne_four_of_mem_classIn hd (K1.mem_D_of_mem_classIn he)
        (K1.mem_U_of_mem_classIn he))
    · exact Or.inr h'

omit K1 in
theorem isNormalSet_subClass :
    IsNormalSet (subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) := by
  intro g z hz
  show ((g * z * g⁻¹ : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) : G) ∈
    classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a
  simpa using conj_mem_classIn hz g.2

theorem exists_mul_mem_subClass :
    ∃ u ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a,
      ∃ v ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a,
        u ≠ v ∧ Commute u v ∧
          u * v ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a := by
  have hD := K1.root
  have hclass := K1.isClass
  obtain ⟨d₀, hd₀, e₀, he₀, hne₀⟩ := K1.counter.nontrivial
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 (isConj_of_isClass hclass hd₀ K1.ha)
  have htT : g₀ * e₀ * g₀⁻¹ ∈ rootSet D a := by
    rw [← hg₀, rootSet_conj hclass]
    exact ⟨e₀, he₀, rfl⟩
  have htne : a ≠ g₀ * e₀ * g₀⁻¹ := by
    rw [← hg₀]
    intro e
    apply hne₀
    have := congrArg (fun z => g₀⁻¹ * z * g₀) e
    simpa [mul_assoc] using this.symm
  have hmul : a * (g₀ * e₀ * g₀⁻¹) ∈ rootSet D a :=
    K1.counter.closure a K1.ha a (mem_rootSet_self K1.ha) _ htT htne
  have hU : ∀ {t : G}, t ∈ rootSet D a → t ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y :=
    fun ht => Subgroup.mem_sup_left (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a ht))
  refine ⟨⟨a, K1.a_mem_U⟩, K1.mem_classIn_of_mem_rootSet (mem_rootSet_self K1.ha),
    ⟨_, hU htT⟩, K1.mem_classIn_of_mem_rootSet htT, fun e => htne (congrArg Subtype.val e),
    Subtype.ext ?_, K1.mem_classIn_of_mem_rootSet hmul⟩
  exact ((htT.2 a K1.ha).2 (Commute.refl a)).symm.eq

theorem disconnected_subClass :
    Disconnected (subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a) := by
  set U := rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y with hU
  refine ⟨⟨a, K1.a_mem_U⟩, K1.mem_classIn_of_mem_rootSet (mem_rootSet_self K1.ha),
    ⟨x, K1.x_mem_U⟩, K1.x_mem_classIn, fun hreach => ?_⟩
  have key : ∀ v : U, Reach (subClass U a) ⟨a, K1.a_mem_U⟩ v → (v : G) ∈ rootSet D a := by
    intro v hv
    induction hv with
    | refl => exact mem_rootSet_self K1.ha
    | tail _ hrel ih =>
      have hcD := K1.mem_D_of_mem_classIn hrel.2.1
      exact K1.mem_rootSet_of_commute hcD (K1.mem_U_of_mem_classIn hrel.2.1)
        ((ih.2 _ hcD).1 (hrel.2.2.map U.subtype))
  have hxT := key _ hreach
  exact K1.hax ((hxT.2 a K1.ha).2 (Commute.refl a)).symm

theorem not_mem_zStar {w : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)}
    (hw : (w : G) ∈ D) : w ∉ zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) := by
  intro hwZ
  have hD := K1.root
  have hw2 : w * w = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hw)
  have hcomm : ∀ {e : G}, e ∈ classIn (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a →
      Commute (w : G) e := by
    intro e he
    have heX := K1.mem_U_of_mem_classIn he
    have heD := K1.mem_D_of_mem_classIn he
    set e' : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) := ⟨e, heX⟩ with he'
    have he2 : e' * e' = 1 := Subtype.ext (by simpa [e'] using hD.mul_self_eq_one heD)
    have hc := (OddTransp.mem_zStar_iff.mp hwZ) e'
    rw [Special.commutatorElement_eq_mul_sq hw2 he2] at hc
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hw heD with h' | h4 | ⟨hodd, hnc⟩
    · exact h'
    · exfalso
      exact K1.not_mem_pCore (hD.sq_mem hw heD h4) ⟨_, hc, by simp [e']⟩
    · exfalso
      have hoG : orderOf (w * e') = orderOf ((w : G) * e) := by
        rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
      have hodd2 : Odd (orderOf ((w * e') ^ 2)) :=
        Odd.of_dvd_nat (hoG ▸ hodd) (orderOf_pow_dvd 2)
      have h1 := OddLocal.eq_one_of_odd_of_mem_pCore hc hodd2
      have h2 : orderOf (w * e') = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1) with h' | h'
        · exact h'
        · rw [← hoG, h'] at hodd
          exact absurd hodd (by decide)
      rw [orderOf_eq_one_iff] at h2
      apply hnc
      have h3 : (w : G) * e = 1 := by simpa [e'] using congrArg Subtype.val h2
      rw [eq_inv_of_mul_eq_one_left h3, hD.inv_eq heD]
  have hwT := K1.mem_rootSet_of_commute hw w.2 (hcomm (mem_classIn_self _ a)).symm
  exact K1.hax ((hwT.2 x K1.hx).1 (hcomm K1.x_mem_classIn))

theorem eq_of_mk_eq {e f : ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)}
    (he : e ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a)
    (hf : f ∈ subClass (rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) a)
    (hef : QuotientGroup.mk' (zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) e =
      QuotientGroup.mk' (zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) f) :
    e = f := by
  have hD := K1.root
  have hcomm : Commute e f :=
    (OddLocal.commute_iff_mod_zStar K1.isOddTransp_subClass he hf).1 (by rw [hef])
  by_contra hne
  have heD := K1.mem_D_of_mem_classIn he
  have hfD := K1.mem_D_of_mem_classIn hf
  have hefD : (e : G) * f ∈ D :=
    K1.noPolar _ heD _ hfD (hcomm.map (Subgroup.subtype _)) fun h' => hne (Subtype.ext h')
  apply K1.not_mem_zStar (w := e * f) (by simpa using hefD)
  have hf2 : f * f = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hfD)
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, hef, ← map_mul, hf2,
    map_one]

theorem isBenderGroup :
    CFSG.BenderSuzuki.IsBenderGroup (↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) ⧸
      zStar ↥(rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y)) := by
  have := K1.finite
  exact OddTransp.oddTranspZStar _ _ K1.isOddTransp_subClass isNormalSet_subClass
    K1.closure_subClass K1.exists_mul_mem_subClass K1.disconnected_subClass

end KOneConf

end RootKOne

end CFSG.Timmesfeld.Bridge
