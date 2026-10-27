module

public import CFSG.Timmesfeld.Bridge.RootStructR2Gate
public import CFSG.Timmesfeld.Bridge.RootClosureRankOne

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

theorem not_commute_of_mem_line_of_opposite (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) {a b x t : G} (hb : b ∈ D) (ha : a ∈ D) (hba : Commute b a)
    (hbaD : b * a ∈ D) (haT : a ∉ rootSet D b) (hx : x ∈ D) (hbx : ¬ Commute b x)
    (hoddbx : Odd (orderOf (b * x))) (ht : t ∈ D) (htL : t ∈ rootGroup D b ⊔ rootGroup D a) :
    ¬ Commute x t := by
  have hD := h.root
  by_cases htT : t ∈ rootSet D b
  · exact fun hxt => hbx ((htT.2 x hx).1 hxt.symm)
  have hne : b * t ≠ 1 := by
    intro h1
    apply htT
    rw [(eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hb)]
    exact mem_rootSet_self hb
  exact not_commute_of_collinear hD hx ht (fun h' => hbx h'.symm)
    (by rw [orderOf_mul_comm_eq]; exact hoddbx)
    (commute_of_mem_sup_rootGroup hb ha hba (left_mem_line hb) htL)
    (mem_of_mem_sup_rootGroup h hc hs hb ha hba hbaD haT
      (Subgroup.mul_mem _ (left_mem_line hb) htL) hne)

theorem conj_inv_mem_line (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {c f e u : G}
    (hu : u ∈ rootGroup D (e * c * e⁻¹) ⊔ rootGroup D (e * f * e⁻¹)) :
    e⁻¹ * u * e ∈ rootGroup D c ⊔ rootGroup D f := by
  rw [rootGroup_conj hclass, rootGroup_conj hclass, ← Subgroup.map_sup, Subgroup.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  simpa [mul_assoc] using hv

theorem exists_special_of_mem_pCore (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) {a b x : G} (hb : b ∈ D)
    (ha : a ∈ D) (hba : Commute b a) (hbaD : b * a ∈ D) (haT : a ∉ rootSet D b) (hx : x ∈ D)
    (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x))) {X : Subgroup G} (hbX : b ∈ X)
    (haX : a ∈ X) (hxX : x ∈ X) (hW : ∃ w ∈ D, w ∈ (CFSG.pCore 2 X).map X.subtype) :
    ∃ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a ∧ orderOf (x * p) = 4 := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D := fun g y hy => conj_mem_of_isClass hclass g hy
  have hLb := hAll b hb a ha hba hbaD haT
  have hNP := noPolar_of_lineTI h hc hs hconn hb ha hba hbaD haT hLb
  set P : Subgroup G := (CFSG.pCore 2 X).map X.subtype with hP
  have hP2 : IsPGroup 2 P := (CFSG.pCore_isPGroup).map X.subtype
  have hPn : ∀ g ∈ X, ∀ w ∈ P, g * w * g⁻¹ ∈ P := by
    intro g hg w hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact ⟨⟨g, hg⟩ * w' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem _ hw' _, by simp⟩
  set W : Set G := {w | w ∈ D ∧ w ∈ P} with hWdef
  have hWX : ∀ g ∈ X, ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    ⟨hN g w hw.1, hPn g hg w hw.2⟩
  have hWcomm : ∀ s ∈ W, ∀ t ∈ W, Commute s t ∨ (orderOf (s * t) = 4 ∧ (s * t) ^ 2 ∈ W) := by
    intro s hs t ht
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hs.1 ht.1 with h' | h4 | ⟨hodd, hnc⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h4, hD.sq_mem hs.1 ht.1 h4,
        Subgroup.pow_mem _ (Subgroup.mul_mem _ hs.2 ht.2) 2⟩
    · exfalso
      have h1 := Special.eq_one_of_mem_of_isPGroup hP2 (Subgroup.mul_mem _ hs.2 ht.2) hodd
      apply hnc
      rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq ht.1]
  set N : Subgroup G := Subgroup.closure W with hNdef
  have hNP2 : IsPGroup 2 N := hP2.to_le ((Subgroup.closure_le _).2 fun w hw => hw.2)
  have : Group.IsNilpotent N := hNP2.isNilpotent
  obtain ⟨w₀, hw₀D, hw₀P⟩ := hW
  have hNbot : N ≠ ⊥ := fun h' => by
    have hw : w₀ ∈ N := Subgroup.subset_closure ⟨hw₀D, hw₀P⟩
    rw [h', Subgroup.mem_bot] at hw
    exact hD.ne_one hw₀D hw
  have hcomm' : ∀ s ∈ W, ∀ t ∈ W, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ ∈ W := by
    intro s hs t ht
    rw [Special.commutatorElement_eq_mul_sq (hD.mul_self_eq_one hs.1) (hD.mul_self_eq_one ht.1)]
    rcases hWcomm s hs t ht with h' | ⟨-, h'⟩
    · exact Or.inl ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hs.1)
        (hD.mul_self_eq_one ht.1)).1 h')
    · exact Or.inr h'
  obtain ⟨c, hcW, hcN, hcZ, -⟩ := exists_mem_center_of_ne_bot (S := W) (N := N)
    (fun w hw => Subgroup.subset_closure hw) rfl hcomm' hNbot
  have hcW' : ∀ w ∈ W, Commute c w := by
    intro w hw
    have := Subgroup.mem_center_iff.1 hcZ ⟨w, Subgroup.subset_closure hw⟩
    exact (congrArg Subtype.val this).symm
  have hcconj : ∀ g ∈ X, ∀ w ∈ W, Commute (g * c * g⁻¹) w := by
    intro g hg w hw
    have hw' : g⁻¹ * w * g ∈ W := by simpa using hWX g⁻¹ (X.inv_mem hg) w hw
    have := (Commute.conj_iff g).2 (hcW' _ hw')
    simpa [mul_assoc] using this
  by_cases hA : ∀ w ∈ W, w ∈ rootSet D c
  · exfalso
    have hcb : Commute c b :=
      commute_of_conj_mem_rootSet hclass hD hcW.1 hb (hA _ (hWX b hbX c hcW))
    have hcx : Commute c x :=
      commute_of_conj_mem_rootSet hclass hD hcW.1 hx (hA _ (hWX x hxX c hcW))
    by_cases hcb' : c ∈ rootSet D b
    · exact hbx ((hcb'.2 x hx).1 hcx)
    · have hne : c ≠ b := fun e => hcb' (by rw [e]; exact mem_rootSet_self hb)
      exact not_commute_of_collinear hD hx hcW.1 (fun h' => hbx h'.symm)
        (by rw [orderOf_mul_comm_eq]; exact hoddbx) hcb.symm
        (by rw [← hcb.eq]; exact hNP c hcW.1 b hb hcb hne) hcx.symm
  push Not at hA
  obtain ⟨f, hfW, hfT⟩ := hA
  have hcf : Commute c f := hcW' f hfW
  have hcfne : c ≠ f := fun e => hfT (by rw [← e]; exact mem_rootSet_self hcW.1)
  have hcfD : c * f ∈ D := hNP c hcW.1 f hfW.1 hcf hcfne
  have hL₀ := hAll c hcW.1 f hfW.1 hcf hcfD hfT
  have hf2 := hD.mul_self_eq_one hfW.1
  have hnorm : ∀ e ∈ D, e ∈ X → NormalizesLine D c f e := by
    intro e he heX
    set y := e * f * e⁻¹ with hy
    have hyW : y ∈ W := hWX e heX f hfW
    have hce : e * c * e⁻¹ ∈ W := hWX e heX c hcW
    have hy2 : y * y = 1 := hD.mul_self_eq_one hyW.1
    have hyinv : y⁻¹ = y := hD.inv_eq hyW.1
    have hN1 : NormalizesLine D c f y := normalizesLine_of_commute h hc hs hcW.1 hfW.1 hcf hcfD
      hfT hL₀ hcW.1 (left_mem_line hcW.1) hyW.1 (hcW' _ hyW).symm
    have hcfe : Commute (e * c * e⁻¹) y := (Commute.conj_iff e).2 hcf
    have hcfeD : e * c * e⁻¹ * y ∈ D := by
      rw [hy, show e * c * e⁻¹ * (e * f * e⁻¹) = e * (c * f) * e⁻¹ by group]
      exact hN e _ hcfD
    have hfeT : y ∉ rootSet D (e * c * e⁻¹) := by
      rw [hy, rootSet_conj hclass]
      rintro ⟨y', hy', hyf⟩
      apply hfT
      have : y' = f := by
        have := congrArg (fun z => e⁻¹ * z * e) hyf
        simpa [mul_assoc] using this
      rw [← this]
      exact hy'
    have hL₀e := hAll _ hce.1 _ hyW.1 hcfe hcfeD hfeT
    have hN2 : NormalizesLine D (e * c * e⁻¹) y f := normalizesLine_of_commute h hc hs hce.1
      hyW.1 hcfe hcfeD hfeT hL₀e hce.1 (left_mem_line hce.1) hfW.1 (hcconj e heX f hfW).symm
    have hzL₀ : (f * y) ^ 2 ∈ rootGroup D c ⊔ rootGroup D f := by
      rw [show (f * y) ^ 2 = f * (y * f * y⁻¹) by rw [hyinv, sq]; group]
      exact Subgroup.mul_mem _ (right_mem_line hfW.1) (hN1 f (right_mem_line hfW.1))
    have hsq : (f * y) ^ 2 = (y * f) ^ 2 := by
      rcases hWcomm f hfW y hyW with h' | ⟨h4, -⟩
      · rw [(commute_iff_mul_sq_eq_one hf2 hy2).1 h',
          (commute_iff_mul_sq_eq_one hy2 hf2).1 h'.symm]
      · exact mul_sq_eq_mul_sq_comm hf2 hy2 h4
    have hzL₀e : (f * y) ^ 2 ∈ rootGroup D (e * c * e⁻¹) ⊔ rootGroup D (e * f * e⁻¹) := by
      rw [hsq, show (y * f) ^ 2 = y * (f * y * f⁻¹) by rw [hD.inv_eq hfW.1, sq]; group]
      exact Subgroup.mul_mem _ (right_mem_line hyW.1) (hN2 y (right_mem_line hyW.1))
    by_cases hz1 : (f * y) ^ 2 = 1
    · have hfy : Commute f y := (commute_iff_mul_sq_eq_one hf2 hy2).2 hz1
      have hyL₀ : y ∈ rootGroup D c ⊔ rootGroup D f := mem_sup_of_commute_of_lineTI h hc hs
        hconn hcW.1 hfW.1 hcf hcfD hfT hL₀ hyW.1 (hcW' y hyW).symm hfy.symm
      exact normalizesLine_of_lineTI h hc hs hcW.1 hfW.1 hcf hcfD hfT hL₀ hfW.1
        (right_mem_line hfW.1) he hyL₀
    · have hzD := mem_of_mem_sup_rootGroup h hc hs hcW.1 hfW.1 hcf hcfD hfT hzL₀ hz1
      have hz' : e⁻¹ * (f * y) ^ 2 * e ∈ rootGroup D c ⊔ rootGroup D f :=
        conj_inv_mem_line hclass hzL₀e
      have hz'D : e⁻¹ * (f * y) ^ 2 * e ∈ D := by simpa using hN e⁻¹ _ hzD
      exact normalizesLine_of_lineTI h hc hs hcW.1 hfW.1 hcf hcfD hfT hL₀ hz'D hz' he
        (by rwa [show e * (e⁻¹ * (f * y) ^ 2 * e) * e⁻¹ = (f * y) ^ 2 by group])
  obtain ⟨t, htD, htL, htc, htf⟩ : ∃ t ∈ D, t ∈ rootGroup D b ⊔ rootGroup D a ∧
      Commute t c ∧ Commute t f := by
    by_cases hb0 : Commute b c ∧ Commute b f
    · exact ⟨b, hb, left_mem_line hb, hb0.1, hb0.2⟩
    by_cases ha0 : Commute a c ∧ Commute a f
    · exact ⟨a, ha, right_mem_line ha, ha0.1, ha0.2⟩
    obtain ⟨eb, heb, hebL, hbeb⟩ :=
      exists_commute_of_normalizesLine h hc hs hcW.1 hfW.1 hcf hcfD hfT hb (hnorm b hb hbX)
    obtain ⟨ea, hea, heaL, haea⟩ :=
      exists_commute_of_normalizesLine h hc hs hcW.1 hfW.1 hcf hcfD hfT ha (hnorm a ha haX)
    by_cases hT : ea ∈ rootSet D eb
    · have hbeT : eb ∈ rootSet D ea := mem_rootSet_comm heb hT
      have hebA : Commute eb a := ((hbeT.2 a ha).2 haea.symm)
      have hebLb : eb ∈ rootGroup D b ⊔ rootGroup D a :=
        mem_sup_of_commute_of_lineTI h hc hs hconn hb ha hba hbaD haT hLb heb hbeb.symm hebA
      exact ⟨eb, heb, hebLb,
        commute_of_mem_sup_rootGroup hcW.1 hfW.1 hcf hebL (left_mem_line hcW.1),
        commute_of_mem_sup_rootGroup hcW.1 hfW.1 hcf hebL (right_mem_line hfW.1)⟩
    · exact absurd hba (opposite_of_normalizesLine h hc hs hcW.1 hfW.1 hcf hcfD hfT hb ha
        (hnorm b hb hbX) (hnorm a ha haX) hb0 ha0 heb hea hebL heaL hbeb haea hT).1
  have htL₀ : t ∈ rootGroup D c ⊔ rootGroup D f := mem_sup_of_commute_of_lineTI h hc hs hconn
    hcW.1 hfW.1 hcf hcfD hfT hL₀ htD htc htf
  have hxt := not_commute_of_mem_line_of_opposite h hc hs hb ha hba hbaD haT hx hbx hoddbx htD
    htL
  have hNx := hnorm x hx hxX
  obtain ⟨ex, hex, hexL, hxex⟩ :=
    exists_commute_of_normalizesLine h hc hs hcW.1 hfW.1 hcf hcfD hfT hx hNx
  obtain ⟨h4, -⟩ := sq_mem_rootSet_of_normalizesLine h hc hs hcW.1 hfW.1 hcf hcfD hfT hx hNx hex
    hexL htD htL₀ hxex hxt
  exact ⟨t, htD, htL, by rw [orderOf_mul_comm_eq]; exact h4⟩

theorem commute_sq_of_conj_eq_inv {g h : G} (hg : g * h * g⁻¹ = h⁻¹) : Commute (g ^ 2) h := by
  have h2 : g ^ 2 * h * (g ^ 2)⁻¹ = h := by
    rw [sq, mul_inv_rev, show g * g * h * (g⁻¹ * g⁻¹) = g * (g * h * g⁻¹) * g⁻¹ by group, hg,
      show g * h⁻¹ * g⁻¹ = (g * h * g⁻¹)⁻¹ by group, hg, inv_inv]
  show g ^ 2 * h = h * g ^ 2
  calc g ^ 2 * h = g ^ 2 * h * (g ^ 2)⁻¹ * g ^ 2 := by group
    _ = h * g ^ 2 := by rw [h2]

theorem false_of_commute_of_inv (hD : IsRootInvolutionSet D)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hNP : Moufang.NoPolar D) {h c y : G}
    (hodd : Odd (orderOf h)) (h1 : h ≠ 1) (hc : c ∈ D) (hy : y ∈ D) (hch : Commute c h)
    (hyh : y * h * y⁻¹ = h⁻¹) : False := by
  have hyinv := hD.inv_eq hy
  have hinv1 : h ≠ h⁻¹ := by
    intro e
    apply h1
    have h2 : h ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [e]
      exact mul_inv_cancel h
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
      (Nat.coprime_two_right.2 hodd) (orderOf_dvd_of_pow_eq_one h2))
  have key : ∀ {d : G}, d ∈ D → Commute d h → Commute d y → False := by
    intro d hd hdh hdy
    have hne : d ≠ y := by
      rintro rfl
      exact hinv1 (by rw [← hyh, hdh.eq, mul_inv_cancel_right])
    have hdyD := hNP d hd y hy hdy hne
    have hy'D : h * y * h⁻¹ ∈ D := conj_mem_of_isClass hclass h hy
    have heq : d * y * (h * y * h⁻¹) = h⁻¹ ^ 2 * d := by
      have hyh' : y * h * y = h⁻¹ := by rw [← hyh, hyinv]
      calc d * y * (h * y * h⁻¹) = d * (y * h * y) * h⁻¹ := by group
        _ = d * h⁻¹ ^ 2 := by rw [hyh', sq, mul_assoc]
        _ = h⁻¹ ^ 2 * d := ((hdh.inv_right).pow_right 2).eq
    have hodd2 : Odd (orderOf (h⁻¹ ^ 2)) :=
      Odd.of_dvd_nat (by rw [orderOf_inv]; exact hodd) (orderOf_pow_dvd 2)
    have hne1 : orderOf (h⁻¹ ^ 2) ≠ 1 := by
      intro e
      rw [orderOf_eq_one_iff] at e
      apply hinv1
      have : h⁻¹ * h⁻¹ = 1 := by rw [← sq]; exact e
      have h' := inv_eq_of_mul_eq_one_right this
      rwa [inv_inv] at h'
    have hord := hD.orderOf_mul hdyD hy'D
    rw [heq, orderOf_mul_eq_two_mul_of_odd ((hdh.inv_right).pow_right 2).symm hodd2
      (hD.orderOf_eq_two hd)] at hord
    obtain ⟨k, hk⟩ := hodd2
    rcases hord with h' | h' | h'
    · omega
    · omega
    · rw [Nat.odd_iff] at h'
      omega
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hc hy with hcy | h4 | ⟨hoddcy, -⟩
  · exact key hc hch hcy
  ·
    obtain ⟨hdD, -, hyd, -⟩ := sq_mem_of_orderOf_eq_four hD hc hy h4
    have hg : (c * y) * h * (c * y)⁻¹ = h⁻¹ := by
      rw [mul_inv_rev, show c * y * h * (y⁻¹ * c⁻¹) = c * (y * h * y⁻¹) * c⁻¹ by group, hyh,
        (hch.inv_right).eq, mul_inv_cancel_right]
    exact key hdD (commute_sq_of_conj_eq_inv hg) hyd.symm
  ·
    have hg : (c * y) * h * (c * y)⁻¹ = h⁻¹ := by
      rw [mul_inv_rev, show c * y * h * (y⁻¹ * c⁻¹) = c * (y * h * y⁻¹) * c⁻¹ by group, hyh,
        (hch.inv_right).eq, mul_inv_cancel_right]
    obtain ⟨j, hj⟩ := hoddcy
    have hpow : (c * y) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have hsq : Commute ((c * y) ^ 2) h := commute_sq_of_conj_eq_inv hg
    have hcy : c * y = (((c * y) ^ 2) ^ j)⁻¹ := by
      rw [← pow_mul, eq_inv_iff_mul_eq_one, ← pow_succ']
      exact hpow
    have hcomm : Commute (c * y) h := by
      rw [hcy]
      exact (hsq.pow_left j).inv_left
    apply hinv1
    rw [← hg, hcomm.eq, mul_inv_cancel_right]

section Quotient

open RootClosure

variable {X : Subgroup G} {x : G}

@[expose] def barCenterMk (X : Subgroup G) :
    X →* (X ⧸ CFSG.pCore 2 X) ⧸ Subgroup.center (X ⧸ CFSG.pCore 2 X) :=
  (QuotientGroup.mk' _).comp (QuotientGroup.mk' _)

theorem commute_barCenterMk_iff [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D) (hx : x ∈ D) (hxX : x ∈ X)
    (hroot : IsRootInvolutionSet (barClass X x))
    (hnd : ∃ e ∈ barClass X x, ∃ f ∈ barClass X x, orderOf (e * f) = 4)
    (hW0 : ∀ w ∈ D, w ∉ (CFSG.pCore 2 X).map X.subtype) {e f : X} (he : e ∈ subClass X x)
    (hf : f ∈ subClass X x) :
    Commute (barCenterMk X e) (barCenterMk X f) ↔ Commute (e : G) f := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hclassB : ∃ d₀, barClass X x = {g | IsConj d₀ g} := ⟨_, barClass_eq hxX⟩
  have heD := mem_of_mem_subClass hN hx he
  have hfD := mem_of_mem_subClass hN hx hf
  have he2 : e * e = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one heD)
  have hf2 : f * f = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hfD)
  constructor
  · intro hcomm
    rcases commute_or_orderOf_mul_eq_four_or_odd hD heD hfD with h' | h4 | ⟨hodd, hnc⟩
    · exact h'
    · exfalso
      rcases sq_mem_classIn_or_mem_pCoreOf hD hN hx hxX he hf h4 with hw | hw
      · have hwS : (e * f) ^ 2 ∈ subClass X x := by
          show (((e * f) ^ 2 : X) : G) ∈ classIn X x
          simpa using hw
        have hnc : π ((e * f) ^ 2) ∉ Subgroup.center (X ⧸ CFSG.pCore 2 X) :=
          not_mem_center hclassB hroot hnd _ ⟨_, hwS, rfl⟩
        apply hnc
        rw [← QuotientGroup.eq_one_iff (N := Subgroup.center (X ⧸ CFSG.pCore 2 X))]
        have h1 := (commute_iff_mul_sq_eq_one
          (show barCenterMk X e * barCenterMk X e = 1 by rw [← map_mul, he2, map_one])
          (show barCenterMk X f * barCenterMk X f = 1 by rw [← map_mul, hf2, map_one])).1 hcomm
        rw [← map_mul, ← map_pow] at h1
        exact h1
      · exact hW0 _ (hD.sq_mem heD hfD h4) hw
    · exfalso
      have hopp := (opposite_mk_center_iff hroot (⟨e, he, rfl⟩ : π e ∈ barClass X x)
        (⟨f, hf, rfl⟩ : π f ∈ barClass X x)).2 ((opposite_mk_iff hD hN hx he hf).2 ⟨hnc, hodd⟩)
      exact hopp.1 hcomm
  · intro hc
    have hc' : Commute e f := Subtype.ext hc.eq
    exact hc'.map (barCenterMk X)

theorem orderOf_eq_three_of_barCenterMk [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D) (hx : x ∈ D) {e f : X} (he : e ∈ subClass X x)
    (hf : f ∈ subClass X x) (h3 : orderOf (barCenterMk X e * barCenterMk X f) = 3) :
    orderOf ((e : G) * f) = 3 := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  set Z := Subgroup.center (X ⧸ CFSG.pCore 2 X) with hZ
  have heD := mem_of_mem_subClass hN hx he
  have hfD := mem_of_mem_subClass hN hx hf
  have he2 : e * e = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one heD)
  have hf2 : f * f = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hfD)
  have hoG : orderOf ((e : G) * f) = orderOf (e * f) := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  rw [← map_mul] at h3
  have hdvd : 3 ∣ orderOf (e * f) := h3 ▸ orderOf_map_dvd _ _
  have hodd : Odd (orderOf (e * f)) := by
    rcases hD.orderOf_mul heD hfD with h' | h' | h' <;> rw [hoG] at h'
    · rw [h'] at hdvd
      exact absurd hdvd (by decide)
    · rw [h'] at hdvd
      exact absurd hdvd (by decide)
    · exact h'
  have hπo : orderOf (π (e * f)) = orderOf (e * f) :=
    orderOf_mk_eq_of_odd (CFSG.pCore_isPGroup (G := X) (p := 2)) hodd
  set g := π (e * f) with hg
  have hg3 : g ^ 3 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff (N := Z), ← QuotientGroup.mk'_apply, map_pow, ← h3]
    exact pow_orderOf_eq_one _
  have hinv : π e * g * (π e)⁻¹ = g⁻¹ := by
    rw [hg, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right he2, inv_eq_of_mul_eq_one_right hf2]
    calc e * (e * f) * e = (e * e) * f * e := by group
      _ = f * e := by rw [he2, one_mul]
  have hinv3 : π e * g ^ 3 * (π e)⁻¹ = (g ^ 3)⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hc3 : π e * g ^ 3 * (π e)⁻¹ = g ^ 3 := by
    rw [Subgroup.mem_center_iff.1 hg3 (π e), mul_inv_cancel_right]
  have h6 : g ^ 6 = 1 := by
    have hh := hc3.symm.trans hinv3
    calc g ^ 6 = g ^ 3 * g ^ 3 := by rw [← pow_add]
      _ = (g ^ 3)⁻¹ * g ^ 3 := by rw [← hh]
      _ = 1 := inv_mul_cancel _
  have hdvd6 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  rw [hπo] at hdvd6
  rw [hoG]
  have hle : orderOf (e * f) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨j, hj⟩ := hdvd
  omega

end Quotient

open RootClosure in
theorem gate_or_degenerate {G : Type} [Group G] {D : Set G} (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    (IH : RootIHStructE G) (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) {a b x : G} (hb : b ∈ D)
    (ha : a ∈ D) (hba : Commute b a) (hbaD : b * a ∈ D) (haT : a ∉ rootSet D b) (hx : x ∈ D)
    (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x)))
    (hU : rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x ≠ ⊤) :
    (∃ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a ∧ orderOf (x * p) = 4) ∨
      ∀ e ∈ barClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x,
        ∀ f ∈ barClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x,
          orderOf (e * f) ≠ 4 := by
  classical
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D := fun g y hy => conj_mem_of_isClass hclass g hy
  have hLb := hAll b hb a ha hba hbaD haT
  have hNP := noPolar_of_lineTI h hc hs hconn hb ha hba hbaD haT hLb
  set L : Subgroup G := rootGroup D b ⊔ rootGroup D a with hL
  set X : Subgroup G := L ⊔ rootGroup D x with hX
  by_contra hcon
  push Not at hcon
  obtain ⟨hno, hnd⟩ := hcon
  have hLX : L ≤ X := le_sup_left
  have hxX : x ∈ X := Subgroup.mem_sup_right (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
  have hbX : b ∈ X := hLX (left_mem_line hb)
  have haX : a ∈ X := hLX (right_mem_line ha)
  have hoppL : ∀ t ∈ D, t ∈ L → ¬ Commute t x ∧ Odd (orderOf (x * t)) := by
    intro t ht htL
    have hxt := not_commute_of_mem_line_of_opposite h hc hs hb ha hba hbaD haT hx hbx hoddbx ht
      htL
    refine ⟨fun h' => hxt h'.symm, ?_⟩
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hx ht with h' | h4 | ⟨ho, -⟩
    · exact absurd h' hxt
    · exact absurd h4 (hno t ht htL)
    · exact ho
  have hW0 : ∀ w ∈ D, w ∉ (CFSG.pCore 2 X).map X.subtype := by
    intro w hw hwP
    obtain ⟨p, hp, hpL, h4⟩ := exists_special_of_mem_pCore h hc hs hconn hAll hb ha hba hbaD haT
      hx hbx hoddbx hbX haX hxX ⟨w, hw, hwP⟩
    exact hno p hp hpL h4
  have hLc : ∀ t ∈ D, t ∈ L → t ∈ classIn X x := fun t ht htL =>
    mem_classIn_of_odd hD hx ht hxX (hLX htL) (hoppL t ht htL).2
  have hbc : b ∈ classIn X x := hLc b hb (left_mem_line hb)
  have hSc : rootSet D b ∪ rootSet D a ∪ rootSet D x ⊆ classIn X x := by
    rintro t ((ht | ht) | ht)
    · exact hLc t ht.1 (Subgroup.mem_sup_left (rootSet_subset_rootGroup D b ht))
    · exact hLc t ht.1 (Subgroup.mem_sup_right (rootSet_subset_rootGroup D a ht))
    · rw [← classIn_eq_of_mem hbc]
      have htx := opposite_of_mem_rootSet_of_opposite hD hb hx (mem_rootSet_self hb) ht
        ⟨hbx, hoddbx⟩
      exact mem_classIn_of_odd hD hb ht.1 hbX
        (Subgroup.mem_sup_right (rootSet_subset_rootGroup D x ht)) htx.2
  have hXS : X = Subgroup.closure (rootSet D b ∪ rootSet D a ∪ rootSet D x) := by
    rw [Subgroup.closure_union, Subgroup.closure_union]
    rfl
  have hgen : Subgroup.closure (subClass X x) = ⊤ := closure_subClass_eq_top hSc hXS
  have hroot := isRootInvolutionSet_barClass hD hN hx hxX hbX hbx hoddbx hgen
  have hclassB : ∃ d₀, barClass X x = {g | IsConj d₀ g} := ⟨_, barClass_eq hxX⟩
  have hgenB : Subgroup.closure (barClass X x) = ⊤ := by
    rw [barClass, ← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hO2 : CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := pCore_quotient_pCore_eq_bot
  have hO2' : ∀ N : Subgroup (X ⧸ CFSG.pCore 2 X), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hNn hNp => eq_bot_iff.2 (hO2 ▸ le_sSup ⟨hNn, hNp⟩)
  set K := X ⧸ CFSG.pCore 2 X with hK
  set F' := QuotientGroup.mk' (Subgroup.center K) '' barClass X x with hF'
  have hH := hyp_quotient_center hclassB hroot hgenB hnd hO2'
  have hlt : Nat.card (K ⧸ Subgroup.center K) < Nat.card G := by
    have h1 : Nat.card (K ⧸ Subgroup.center K) ≤ Nat.card K :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card K ≤ Nat.card X :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h3 : Nat.card X < Nat.card G :=
      lt_of_le_of_ne (Subgroup.card_le_card_group X) fun heq =>
        hU ((Subgroup.card_eq_iff_eq_top X).1 heq)
    omega
  obtain ⟨-, hIH⟩ := IH _ _ hH hlt
  have himg : ∀ y ∈ subClass X x, barCenterMk X y ∈ F' := fun y hy => ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hpre : ∀ y' ∈ F', ∃ y ∈ subClass X x, barCenterMk X y = y' := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  have hcommC : ∀ {e f : X}, e ∈ subClass X x → f ∈ subClass X x →
      (Commute (barCenterMk X e) (barCenterMk X f) ↔ Commute (e : G) f) := fun he hf =>
    commute_barCenterMk_iff hD hN hx hxX hroot hnd hW0 he hf
  have hS : ∀ {t : G} (htL : t ∈ L), t ∈ D → (⟨t, hLX htL⟩ : X) ∈ subClass X x :=
    fun htL ht => hLc _ ht htL
  have hoff : ∀ {c : G}, c ∈ classIn X x → ∃ f₀ ∈ subClass X x, Commute (f₀ : G) c ∧
      (f₀ : G) * c ∈ D ∧ (f₀ : G) ∉ L := by
    intro c hcc
    obtain ⟨_, ⟨e₁, he₁, rfl⟩, _, ⟨f₁, hf₁, rfl⟩, h4⟩ := hnd
    have he₁D := mem_of_mem_subClass hN hx he₁
    have hf₁D := mem_of_mem_subClass hN hx hf₁
    have h4G : orderOf ((e₁ : G) * f₁) = 4 := by
      rw [← map_mul] at h4
      have hdvd := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 X)) (e₁ * f₁)
      rw [h4] at hdvd
      have hoG : orderOf ((e₁ : G) * f₁) = orderOf (e₁ * f₁) := by
        rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
      rcases hD.orderOf_mul he₁D hf₁D with h' | h' | h'
      · rw [hoG] at h'
        rw [h'] at hdvd
        exact absurd hdvd (by decide)
      · exact h'
      · rw [hoG] at h'
        exact absurd (h'.of_dvd_nat hdvd) (by decide)
    rcases sq_mem_classIn_or_mem_pCoreOf hD hN hx hxX he₁ hf₁ h4G with hw | hw
    swap
    · exact absurd hw (hW0 _ (hD.sq_mem he₁D hf₁D h4G))
    obtain ⟨-, he₁w, hf₁w, -⟩ := sq_mem_of_orderOf_eq_four hD he₁D hf₁D h4G
    have he₁wD := mul_sq_mem_of_orderOf_eq_four hclass hD he₁D hf₁D h4G
    have hf₁wD : (f₁ : G) * ((e₁ : G) * f₁) ^ 2 ∈ D := by
      have h4' : orderOf ((f₁ : G) * e₁) = 4 := by rwa [orderOf_mul_comm_eq]
      rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one he₁D) (hD.mul_self_eq_one hf₁D) h4G]
      exact mul_sq_mem_of_orderOf_eq_four hclass hD hf₁D he₁D h4'
    have hcc' := hcc
    rw [← classIn_eq_of_mem hw] at hcc'
    obtain ⟨u, huX, hcu⟩ := hcc'
    have hcol : ∀ {e : X}, e ∈ subClass X x → Commute (e : G) (((e₁ : G) * f₁) ^ 2) →
        (e : G) * ((e₁ : G) * f₁) ^ 2 ∈ D → ∃ e' ∈ subClass X x, Commute (e' : G) c ∧
          (e' : G) * c ∈ D ∧ (e' : G) = u * e * u⁻¹ := by
      intro e he hew hewD
      refine ⟨⟨u, huX⟩ * e * ⟨u, huX⟩⁻¹, ?_, ?_, ?_, by simp⟩
      · show ((⟨u, huX⟩ * e * ⟨u, huX⟩⁻¹ : X) : G) ∈ classIn X x
        simpa using conj_mem_classIn he huX
      · rw [hcu]
        simpa using (Commute.conj_iff u).2 hew
      · rw [hcu]
        simpa [mul_assoc] using hN u _ hewD
    obtain ⟨e₂, he₂, he₂c, he₂cD, he₂eq⟩ := hcol he₁ he₁w he₁wD
    obtain ⟨f₂, hf₂, hf₂c, hf₂cD, hf₂eq⟩ := hcol hf₁ hf₁w hf₁wD
    by_cases he₂L : (e₂ : G) ∈ L
    · by_cases hf₂L : (f₂ : G) ∈ L
      · exfalso
        have hcm := commute_of_mem_sup_rootGroup hb ha hba he₂L hf₂L
        rw [he₂eq, hf₂eq] at hcm
        exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one he₁D)
          (hD.mul_self_eq_one hf₁D) h4G ((Commute.conj_iff u).1 hcm)
      · exact ⟨f₂, hf₂, hf₂c, hf₂cD, hf₂L⟩
    · exact ⟨e₂, he₂, he₂c, he₂cD, he₂L⟩
  have hlift : ∀ {c : G} (hcL : c ∈ L), c ∈ D → ∀ {y : X}, y ∈ subClass X x →
      barCenterMk X y ∈ rootSet F' (barCenterMk X ⟨c, hLX hcL⟩) → (y : G) ∈ rootSet D c := by
    intro c hcL hcD y hy hyT
    have hyD := mem_of_mem_subClass hN hx hy
    have hcS := hS hcL hcD
    have hy' : ∀ f ∈ subClass X x, Commute (y : G) f ↔ Commute c f := by
      intro f hf
      rw [← hcommC hy hf, ← hcommC hcS hf]
      exact hyT.2 _ (himg f hf)
    have hyc : Commute (y : G) c := (hy' _ hcS).2 (Commute.refl c)
    by_contra hyT'
    have hne : (y : G) ≠ c := fun e => hyT' (by rw [e]; exact mem_rootSet_self hcD)
    have hycD := hNP _ hyD c hcD hyc hne
    have hyb : Commute (y : G) b := (hy' _ (hS (left_mem_line hb) hb)).2
      (commute_of_mem_sup_rootGroup hb ha hba hcL (left_mem_line hb))
    have hya : Commute (y : G) a := (hy' _ (hS (right_mem_line ha) ha)).2
      (commute_of_mem_sup_rootGroup hb ha hba hcL (right_mem_line ha))
    have hyL : (y : G) ∈ L :=
      mem_sup_of_commute_of_lineTI h hc hs hconn hb ha hba hbaD haT hLb hyD hyb hya
    obtain ⟨f₀, hf₀, hf₀c, hf₀cD, hf₀L⟩ := hoff (hLc c hcD hcL)
    have hf₀D := mem_of_mem_subClass hN hx hf₀
    have hyf₀ : Commute (y : G) f₀ := (hy' _ hf₀).2 hf₀c.symm
    have hyT2 : (y : G) ∉ rootSet D c := hyT'
    have hLeq := sup_rootGroup_eq_of_mem h hc hs hb ha hba hbaD haT hcL hyL (hD.ne_one hcD)
      (hD.ne_one hyD) hyT2
    have hcyD : c * y ∈ D := by rw [← hyc.eq]; exact hycD
    have hne' : (f₀ : G) ≠ y := fun e => hf₀L (by rw [e]; exact hyL)
    have hf₀yD := hNP _ hf₀D _ hyD hyf₀.symm hne'
    apply hf₀L
    rw [hL, ← hLeq]
    exact mem_sup_of_collinear_of_lineTI h hc hs hcD hyD hyc.symm hcyD hyT2
      (hAll c hcD _ hyD hyc.symm hcyD hyT2) hf₀D hf₀c hf₀cD hyf₀.symm hf₀yD
  have hbS := hS (left_mem_line hb) hb
  have haS := hS (right_mem_line ha) ha
  have hxS : (⟨x, hxX⟩ : X) ∈ subClass X x := mem_subClass_self hxX
  obtain ⟨d₀, hd₀, e₀, he₀, hne₀⟩ := hl
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 (isConj_of_isClass hclass hd₀ hb)
  have hb'T : g₀ * e₀ * g₀⁻¹ ∈ rootSet D b := by
    rw [← hg₀, rootSet_conj hclass]
    exact ⟨e₀, he₀, rfl⟩
  have hb'ne : g₀ * e₀ * g₀⁻¹ ≠ b := by
    rw [← hg₀]
    intro e
    apply hne₀
    have := congrArg (fun z => g₀⁻¹ * z * g₀) e
    simpa [mul_assoc] using this
  have hb'L : g₀ * e₀ * g₀⁻¹ ∈ L := Subgroup.mem_sup_left (rootSet_subset_rootGroup D b hb'T)
  have hb'S := hS hb'L hb'T.1
  have hb'root : barCenterMk X ⟨_, hLX hb'L⟩ ∈ rootSet F' (barCenterMk X ⟨b, hbX⟩) := by
    refine ⟨himg _ hb'S, ?_⟩
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := hpre f' hf'
    rw [hcommC hb'S hf, hcommC hbS hf]
    exact hb'T.2 _ (mem_of_mem_subClass hN hx hf)
  have hb'ne' : barCenterMk X ⟨_, hLX hb'L⟩ ≠ barCenterMk X ⟨b, hbX⟩ := by
    intro e
    have hbbT : g₀ * e₀ * g₀⁻¹ * b ∈ rootSet D b := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hb
      (Subgroup.mul_mem _ (rootSet_subset_rootGroup D b hb'T)
        (rootSet_subset_rootGroup D b (mem_rootSet_self hb)))
      (fun h1 => hb'ne ((eq_inv_of_mul_eq_one_left h1).trans (hD.inv_eq hb)))
    have hbbL : g₀ * e₀ * g₀⁻¹ * b ∈ L := Subgroup.mem_sup_left (rootSet_subset_rootGroup D b hbbT)
    have h1 := hH.root.ne_one (himg _ (hS hbbL hbbT.1))
    apply h1
    have hb2 : (⟨b, hbX⟩ : X) * ⟨b, hbX⟩ = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hb)
    rw [show (⟨g₀ * e₀ * g₀⁻¹ * b, hLX hbbL⟩ : X) = ⟨_, hLX hb'L⟩ * ⟨b, hbX⟩ from rfl, map_mul, e,
      ← map_mul, hb2, map_one]
  obtain ⟨-, -, hM, -⟩ := hIH ⟨_, himg _ hbS, _, hb'root, hb'ne'⟩
  have hpartner : ∀ {c : G} (hcL : c ∈ L) (hcD : c ∈ D),
      ∃ c' ∈ rootSet D c, orderOf (x * c') = 3 := by
    intro c hcL hcD
    have hcS := hS hcL hcD
    have hopp := (opposite_mk_center_iff hroot (⟨_, hxS, rfl⟩ :
      QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hxX⟩ ∈ barClass X x)
      (⟨_, hcS, rfl⟩ : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨c, hLX hcL⟩ ∈ barClass X x)).2
      ((opposite_mk_iff hD hN hx hxS hcS).2
        ⟨fun h' => (hoppL c hcD hcL).1 h'.symm, (hoppL c hcD hcL).2⟩)
    obtain ⟨y', hy'T, h3⟩ := hM _ (himg _ hxS) _ (himg _ hcS) hopp.1 hopp.2 _
      (mem_rootSet_self (himg _ hxS))
    obtain ⟨y, hy, rfl⟩ := hpre _ hy'T.1
    exact ⟨y, hlift hcL hcD hy hy'T,
      orderOf_eq_three_of_barCenterMk hD hN hx hxS hy h3⟩
  obtain ⟨b', hb', h3b⟩ := hpartner (left_mem_line hb) hb
  obtain ⟨a', ha', h3a⟩ := hpartner (right_mem_line ha) ha
  obtain ⟨p, hp, hpL, h4⟩ := exists_mem_line_special_of_orderOf_eq_three h hc hs hb ha hba hbaD
    haT hx hb' ha' h3b h3a
  exact hno p hp hpL h4

end CFSG.Timmesfeld.Bridge
