module

public import CFSG.Timmesfeld.Bridge.RootStructR2Sub
public import CFSG.Timmesfeld.Bridge.OddTranspMain
public import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity RootClosure
open scoped commutatorElement

namespace RootDegen

structure DegenConf {G : Type} [Group G] (D : Set G) (a b x : G) : Prop where
  hyp : Hyp G D
  closure : RootClosure D
  special : SpecialClosure D
  conn : Moufang.ExcCollConnected D
  allTI : AllLinesTI D
  hb : b ∈ D
  ha : a ∈ D
  hba : Commute b a
  hbaD : b * a ∈ D
  haT : a ∉ rootSet D b
  hx : x ∈ D
  hbx : ¬ Commute b x
  hoddbx : Odd (orderOf (b * x))
  nogate : ∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a → orderOf (x * p) ≠ 4
  deg : ∀ e ∈ barClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x,
    ∀ f ∈ barClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x, orderOf (e * f) ≠ 4

namespace DegenConf

variable {G : Type} [Group G] {D : Set G} {a b x : G} (C : DegenConf D a b x)
include C

theorem finite : Finite G := C.hyp.finite

theorem root : IsRootInvolutionSet D := C.hyp.root

theorem isClass : ∃ d₀ : G, D = {g | IsConj d₀ g} := C.hyp.isClass

theorem conj_mem (g : G) {y : G} (hy : y ∈ D) : g * y * g⁻¹ ∈ D :=
  conj_mem_of_isClass C.isClass g hy

theorem lineTI : LineTI D b a := C.allTI b C.hb a C.ha C.hba C.hbaD C.haT

theorem noPolar : Moufang.NoPolar D :=
  noPolar_of_lineTI C.hyp C.closure C.special C.conn C.hb C.ha C.hba C.hbaD C.haT C.lineTI

omit C in
theorem le_X : rootGroup D b ⊔ rootGroup D a ≤ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x :=
  le_sup_left

theorem x_mem_X : x ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x :=
  Subgroup.mem_sup_right (rootSet_subset_rootGroup D x (mem_rootSet_self C.hx))

theorem b_mem_L : b ∈ rootGroup D b ⊔ rootGroup D a := left_mem_line C.hb

theorem a_mem_L : a ∈ rootGroup D b ⊔ rootGroup D a := right_mem_line C.ha

theorem mem_of_mem_L {u : G} (hu : u ∈ rootGroup D b ⊔ rootGroup D a) (hu1 : u ≠ 1) : u ∈ D :=
  mem_of_mem_sup_rootGroup C.hyp C.closure C.special C.hb C.ha C.hba C.hbaD C.haT hu hu1

theorem commute_of_mem_L {u v : G} (hu : u ∈ rootGroup D b ⊔ rootGroup D a)
    (hv : v ∈ rootGroup D b ⊔ rootGroup D a) : Commute u v :=
  commute_of_mem_sup_rootGroup C.hb C.ha C.hba hu hv

theorem mem_L_of_commute {f : G} (hf : f ∈ D) (hfb : Commute f b) (hfa : Commute f a) :
    f ∈ rootGroup D b ⊔ rootGroup D a :=
  mem_sup_of_commute_of_lineTI C.hyp C.closure C.special C.conn C.hb C.ha C.hba C.hbaD C.haT
    C.lineTI hf hfb hfa

theorem opposite_of_mem_L {t : G} (ht : t ∈ D) (htL : t ∈ rootGroup D b ⊔ rootGroup D a) :
    ¬ Commute t x ∧ Odd (orderOf (x * t)) := by
  have hxt := not_commute_of_mem_line_of_opposite C.hyp C.closure C.special C.hb C.ha C.hba
    C.hbaD C.haT C.hx C.hbx C.hoddbx ht htL
  refine ⟨fun h' => hxt h'.symm, ?_⟩
  rcases commute_or_orderOf_mul_eq_four_or_odd C.root C.hx ht with h' | h4 | ⟨ho, -⟩
  · exact absurd h' hxt
  · exact absurd h4 (C.nogate t ht htL)
  · exact ho

theorem mem_classIn_of_mem_L {t : G} (ht : t ∈ D) (htL : t ∈ rootGroup D b ⊔ rootGroup D a) :
    t ∈ classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x :=
  mem_classIn_of_odd C.root C.hx ht C.x_mem_X (le_X htL) (C.opposite_of_mem_L ht htL).2

theorem b_mem_classIn : b ∈ classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x :=
  C.mem_classIn_of_mem_L C.hb C.b_mem_L

theorem mem_D_of_mem_classIn {e : G}
    (he : e ∈ classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x) : e ∈ D :=
  classIn_subset_of_normal (fun g _ hy => C.conj_mem g hy) _ C.hx he

theorem not_mem_pCore {w : G} (hw : w ∈ D) :
    w ∉ (CFSG.pCore 2 ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)).map
      (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x).subtype := by
  intro hwP
  obtain ⟨p, hp, hpL, h4⟩ := exists_special_of_mem_pCore C.hyp C.closure C.special C.conn
    C.allTI C.hb C.ha C.hba C.hbaD C.haT C.hx C.hbx C.hoddbx (le_X C.b_mem_L)
    (le_X C.a_mem_L) C.x_mem_X ⟨w, hw, hwP⟩
  exact C.nogate p hp hpL h4

theorem closure_subClass :
    Subgroup.closure (subClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x) = ⊤ := by
  have hD := C.root
  set X := rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x with hX
  have hSc : rootSet D b ∪ rootSet D a ∪ rootSet D x ⊆ classIn X x := by
    rintro t ((ht | ht) | ht)
    · exact C.mem_classIn_of_mem_L ht.1 (Subgroup.mem_sup_left (rootSet_subset_rootGroup D b ht))
    · exact C.mem_classIn_of_mem_L ht.1 (Subgroup.mem_sup_right (rootSet_subset_rootGroup D a ht))
    · rw [← classIn_eq_of_mem C.b_mem_classIn]
      have htx := opposite_of_mem_rootSet_of_opposite hD C.hb C.hx (mem_rootSet_self C.hb) ht
        ⟨C.hbx, C.hoddbx⟩
      exact mem_classIn_of_odd hD C.hb ht.1 (le_X C.b_mem_L)
        (Subgroup.mem_sup_right (rootSet_subset_rootGroup D x ht)) htx.2
  have hXS : X = Subgroup.closure (rootSet D b ∪ rootSet D a ∪ rootSet D x) := by
    rw [Subgroup.closure_union, Subgroup.closure_union]
    rfl
  exact closure_subClass_eq_top hSc hXS

theorem orderOf_ne_four {e f : G}
    (he : e ∈ classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x)
    (hf : f ∈ classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x) :
    orderOf (e * f) ≠ 4 := by
  intro h4
  have hD := C.root
  set X := rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x with hX
  have heX : e ∈ X := classIn_subset X C.x_mem_X he
  have hfX : f ∈ X := classIn_subset X C.x_mem_X hf
  set e' : X := ⟨e, heX⟩
  set f' : X := ⟨f, hfX⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hsq : (e * f) ^ 2 ∈ D := hD.sq_mem (C.mem_D_of_mem_classIn he) (C.mem_D_of_mem_classIn hf) h4
  have hne : π ((e' * f') ^ 2) ≠ 1 := by
    intro h1
    apply C.not_mem_pCore hsq
    exact ⟨(e' * f') ^ 2, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hoG : orderOf (e' * f') = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact h4
  have hdvd : orderOf (π e' * π f') ∣ 4 := by
    rw [← map_mul, ← hoG]
    exact orderOf_map_dvd _ _
  apply C.deg (π e') ⟨e', he, rfl⟩ (π f') ⟨f', hf, rfl⟩
  have h2 : ¬ orderOf (π e' * π f') ∣ 2 := by
    intro h2
    apply hne
    rw [map_pow, map_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 h2
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf (π e' * π f') ∣ 2 ^ 2 from hdvd) with
    ⟨i, hi, hi'⟩
  interval_cases i
  · exact absurd (hi' ▸ one_dvd 2) h2
  · exact absurd (hi' ▸ dvd_refl 2) h2
  · exact hi'

theorem isOddTransp_subClass :
    Asc72.IsOddTransp (subClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x) := by
  have hD := C.root
  refine ⟨fun d hd => ?_, fun d hd e he => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hD.orderOf_eq_two (C.mem_D_of_mem_classIn hd)
  · have hoG : orderOf (d * e) = orderOf ((d : G) * e) := by
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    rw [hoG]
    rcases hD.orderOf_mul (C.mem_D_of_mem_classIn hd) (C.mem_D_of_mem_classIn he) with
      h' | h' | h'
    · exact Or.inl (by rw [h'])
    · exact absurd h' (C.orderOf_ne_four hd he)
    · exact Or.inr h'

theorem mem_line_of_commute {e t : G}
    (he : e ∈ classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x) (ht : t ∈ D)
    (htL : t ∈ rootGroup D b ⊔ rootGroup D a) (het : Commute e t) :
    e ∈ rootGroup D b ⊔ rootGroup D a := by
  have hD := C.root
  have heD := C.mem_D_of_mem_classIn he
  by_contra heL
  have key : ∀ {s : G}, s ∈ D → s ∈ rootGroup D b ⊔ rootGroup D a → ¬ Commute e s → False := by
    intro s hs hsL hes
    have hsc := C.mem_classIn_of_mem_L hs hsL
    have hodd : Odd (orderOf (e * s)) := by
      rcases commute_or_orderOf_mul_eq_four_or_odd hD heD hs with h' | h4 | ⟨ho, -⟩
      · exact absurd h' hes
      · exact absurd h4 (C.orderOf_ne_four he hsc)
      · exact ho
    by_cases htT : t ∈ rootSet D s
    · exact hes ((htT.2 e heD).1 het.symm).symm
    · have hst : Commute s t := C.commute_of_mem_L hsL htL
      have hst1 : s * t ≠ 1 := by
        intro h1
        apply htT
        rw [eq_inv_of_mul_eq_one_right h1, hD.inv_eq hs]
        exact mem_rootSet_self hs
      have hstD : s * t ∈ D := C.mem_of_mem_L (Subgroup.mul_mem _ hsL htL) hst1
      have := Moufang.eq_of_collinear_of_odd_of_mem hD hs ht hst hstD heD het hodd
      exact heL (this ▸ hsL)
  by_cases heb : Commute e b
  · by_cases hea : Commute e a
    · exact heL (C.mem_L_of_commute heD heb hea)
    · exact key C.ha C.a_mem_L hea
  · exact key C.hb C.b_mem_L heb

theorem not_mem_zStar {w : ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)}
    (hw : (w : G) ∈ D) : w ∉ zStar ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) := by
  intro hwZ
  have hD := C.root
  have hw2 : w * w = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hw)
  have hcomm : ∀ {e : G}, e ∈ classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x →
      Commute (w : G) e := by
    intro e he
    have heX : e ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x := classIn_subset _ C.x_mem_X he
    have heD := C.mem_D_of_mem_classIn he
    set e' : ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) := ⟨e, heX⟩ with he'
    have he2 : e' * e' = 1 := Subtype.ext (by simpa [e'] using hD.mul_self_eq_one heD)
    have hc := (OddTransp.mem_zStar_iff.mp hwZ) e'
    rw [Special.commutatorElement_eq_mul_sq hw2 he2] at hc
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hw heD with h' | h4 | ⟨hodd, hnc⟩
    · exact h'
    · exfalso
      exact C.not_mem_pCore (hD.sq_mem hw heD h4) ⟨_, hc, by simp [e']⟩
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
  have hwb := hcomm C.b_mem_classIn
  have hwa := hcomm (C.mem_classIn_of_mem_L C.ha C.a_mem_L)
  have hwx := hcomm (mem_classIn_self _ x)
  exact (C.opposite_of_mem_L hw (C.mem_L_of_commute hw hwb hwa)).1 hwx

theorem eq_of_mk_eq {e f : ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)}
    (he : e ∈ subClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x)
    (hf : f ∈ subClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x)
    (h : QuotientGroup.mk' (zStar ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)) e =
      QuotientGroup.mk' (zStar ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)) f) :
    e = f := by
  have hD := C.root
  have hcomm : Commute e f :=
    (OddLocal.commute_iff_mod_zStar C.isOddTransp_subClass he hf).1 (by rw [h])
  by_contra hne
  have heD := C.mem_D_of_mem_classIn he
  have hfD := C.mem_D_of_mem_classIn hf
  have hefD : (e : G) * f ∈ D :=
    C.noPolar _ heD _ hfD (hcomm.map (Subgroup.subtype _)) fun h' => hne (Subtype.ext h')
  apply C.not_mem_zStar (w := e * f) (by simpa using hefD)
  have hf2 : f * f = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hfD)
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, h, ← map_mul, hf2,
    map_one]

theorem isBenderGroup :
    CFSG.BenderSuzuki.IsBenderGroup (↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) ⧸
      zStar ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)) := by
  have := C.finite
  set X := rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x with hX
  have hbX : b ∈ X := le_X C.b_mem_L
  have haX : a ∈ X := le_X C.a_mem_L
  refine OddTransp.oddTranspZStar X (subClass X x) C.isOddTransp_subClass ?_ C.closure_subClass
    ?_ ?_
  · intro g y hy
    show ((g * y * g⁻¹ : X) : G) ∈ classIn X x
    simpa using conj_mem_classIn hy g.2
  · refine ⟨⟨b, hbX⟩, C.b_mem_classIn, ⟨a, haX⟩, C.mem_classIn_of_mem_L C.ha C.a_mem_L,
      fun h => C.haT ?_, Subtype.ext C.hba.eq, ?_⟩
    · have hab : b = a := congrArg Subtype.val h
      rw [← hab]
      exact mem_rootSet_self C.hb
    · show b * a ∈ classIn X x
      exact C.mem_classIn_of_mem_L C.hbaD (Subgroup.mul_mem _ C.b_mem_L C.a_mem_L)
  · refine ⟨⟨b, hbX⟩, C.b_mem_classIn, ⟨x, C.x_mem_X⟩, mem_classIn_self X x, fun hreach => ?_⟩
    have key : ∀ v : X, Reach (subClass X x) ⟨b, hbX⟩ v →
        (v : G) ∈ rootGroup D b ⊔ rootGroup D a := by
      intro v hv
      induction hv with
      | refl => exact C.b_mem_L
      | tail _ hrel ih =>
        exact C.mem_line_of_commute hrel.2.1 (C.mem_D_of_mem_classIn hrel.1) ih
          (hrel.2.2.map X.subtype).symm
    exact (C.opposite_of_mem_L C.hx (key _ hreach)).1 (Commute.refl x)

end DegenConf

end RootDegen

end CFSG.Timmesfeld.Bridge
