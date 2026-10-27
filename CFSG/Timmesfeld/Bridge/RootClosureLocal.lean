module

public import CFSG.Timmesfeld.Bridge.RootSetsThird
public import CFSG.Timmesfeld.Bridge.RootStructOD
public import CFSG.Timmesfeld.Bridge.RootSetsBasic

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

theorem orderOf_mul_ne_two (hD : IsRootInvolutionSet D) {d a b x : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) : orderOf (x * (a * b)) ≠ 2 := by
  intro h2
  have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
  have hc : Commute x (a * b) := (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx) hu2).2
    (by rw [← h2, pow_orderOf_eq_one])
  exact not_opposite_of_commute_mul hD hd ha hb hab hx hc ⟨hdx, hodd⟩

theorem exists_opposite_not_opposite [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D) (he : e ∈ D) (hed : e ∉ rootSet D d) :
    ∃ c ∈ D, (¬ Commute e c ∧ Odd (orderOf (e * c))) ∧
      ¬ (¬ Commute d c ∧ Odd (orderOf (d * c))) := by
  by_contra hne
  have hsub : opposites D e ⊆ opposites D d := by
    rintro c ⟨hc, hec⟩
    by_contra hcd
    exact hne ⟨c, hc, hec, fun h => hcd ⟨hc, h⟩⟩
  have heq := opposites_eq_of_subset hclass he hd hsub
  refine hed (hOD d hd e he fun c hc => ?_)
  have h := Set.ext_iff.mp heq c
  exact ⟨fun h' => (h.2 ⟨hc, h'⟩).2, fun h' => (h.1 ⟨hc, h'⟩).2⟩

private theorem eq_one_of_two_mul_dvd_two_pow {m k : ℕ} (hm : Odd m) (h : 2 * m ∣ 2 ^ k) :
    m = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
    (dvd_trans (dvd_mul_left m 2) h)

theorem commute_of_twoOdd (h : Hyp G D) {d a b x : G} (hd : d ∈ D) (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) (hab : a ≠ b) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hodd : Odd (orderOf (d * x))) {m : ℕ} (hm : Odd m) (hxu : orderOf (x * (a * b)) = 2 * m) :
    Commute (a * b * (x * (a * b)) ^ m) a := by
  have := h.finite
  have hclass := h.isClass
  have hD := h.root
  have hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D := fun g y hy => conj_mem_of_isClass hclass g hy
  have hOD := oppositeDetermines_of_hyp h
  have haD := ha.1
  have ha2 := hD.mul_self_eq_one haD
  have hx2 := hD.mul_self_eq_one hx
  have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
  obtain ⟨heD, heu, hnopp⟩ := mem_of_twoOdd hclass hD hd ha hb hx hab hm hxu
  obtain ⟨hzx, -, -⟩ := Closure.third_kind hx2 hu2 hm hxu
  have hbA : b ∈ rootSet D a := mem_rootSet_of_mem_rootSet_pair ha hb
  have hdA : d ∈ rootSet D a := mem_rootSet_comm hd ha
  have huA : a * b ∈ rootGroup D a := mul_mem_rootGroup (mem_rootSet_self haD) hbA
  set u := a * b with hu
  set z := (x * u) ^ m with hz
  set e := u * z with he
  have he2 := hD.mul_self_eq_one heD
  have heinv : e⁻¹ = e := hD.inv_eq heD
  by_contra hea
  have h4 : orderOf (a * e) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD heD haD with hc | h4 | ⟨ho, hnc⟩
    · exact absurd hc hea
    · rwa [orderOf_mul_comm_eq]
    · exact absurd ⟨fun hc => hnc ((ha.2 e heD).2 hc).symm,
        (odd_orderOf_mul_iff_of_mem_rootSet hD haD hdA heD fun hc => hnc hc.symm).2
          (by rwa [orderOf_mul_comm_eq] at ho)⟩ hnopp
  obtain ⟨hwD, haw, -, hewa⟩ := sq_mem_of_orderOf_eq_four hD haD heD h4
  set w := (a * e) ^ 2 with hw
  set a' := e * a * e with ha'
  have hw2 : w * w = 1 := hD.mul_self_eq_one hwD
  have ha'D : a' ∈ D := by simpa [heinv] using hN e a haD
  have ha'w : a' = a * w := hewa
  have haa' : Commute a a' := by rw [ha'w]; exact (Commute.refl a).mul_right haw
  have hwaa : a * a' = w := by rw [ha'w, ← mul_assoc, ha2, one_mul]
  have haa'D : a * a' ∈ D := by rw [hwaa]; exact hwD
  have ha'e : a' = e * a * e⁻¹ := by rw [heinv]
  have ha'T : a' ∉ rootSet D a := fun hmem =>
    hea (commute_of_conj_mem_rootSet hclass hD haD heD (by rw [← ha'e]; exact hmem)).symm
  obtain ⟨y, hyD, ⟨hay, hoay⟩, hnya'⟩ := exists_opposite_not_opposite hclass hOD ha'D haD
    fun hmem => ha'T (mem_rootSet_comm ha'D hmem)
  have hya'4 : orderOf (y * a') = 4 := by
    have hna'y := (not_commute_of_opposite_of_line hD haD ha'D haa' haa'D hyD hay hoay).1
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hyD ha'D with hc | h4' | ⟨ho, hnc⟩
    · exact absurd hc.symm hna'y
    · exact h4'
    · exact absurd ⟨fun hc => hnc hc.symm, by rwa [orderOf_mul_comm_eq]⟩ hnya'
  obtain ⟨t, htD, htQ, -, -, hta⟩ := exists_conj_eq_mul_of_odd_special hD hN haD hyD ha'D hay
    hoay hya'4 haa' haa'D
  have ht2 := hD.mul_self_eq_one htD
  have htinv : t⁻¹ = t := hD.inv_eq htD
  have hta' : Commute t a' := qdCore_commute hD hN haD hyD ha'D hay hoay hya'4 haa' t htQ a'
    self_mem_qdCore
  rw [hwaa] at hta
  have hwt : w = t * a * t⁻¹ := by rw [htinv, hta]
  have huA' : u ∈ rootGroup D a' := by
    rw [ha'e, rootGroup_conj hclass]
    refine ⟨u, huA, ?_⟩
    show e * u * e⁻¹ = u
    rw [heinv, heu.eq, mul_assoc, he2, mul_one]
  have htu : Commute t u := (commute_of_mem_rootGroup_of_commute huA' htD hta'.symm).symm
  have huW : u ∈ rootGroup D w := by
    rw [hwt, rootGroup_conj hclass]
    refine ⟨u, huA, ?_⟩
    show t * u * t⁻¹ = u
    rw [htinv, htu.eq, mul_assoc, ht2, mul_one]
  set b' := t * b * t with hb'
  have hb'T : b' ∈ rootSet D w := by
    rw [hwt, rootSet_conj hclass]
    exact ⟨b, hbA, by rw [htinv]⟩
  have hb'D := hb'T.1
  have hb'2 := hD.mul_self_eq_one hb'D
  have hwb' : w * b' = u := by
    calc w * b' = t * a * t * (t * b * t) := by rw [← hta]
      _ = t * u * t := by
        rw [show t * a * t * (t * b * t) = t * a * (t * t) * b * t by group, ht2, mul_one, hu]
        group
      _ = u := by rw [htu.eq, mul_assoc, ht2, mul_one]
  have hb'w : b' = w * u := by rw [← hwb', ← mul_assoc, hw2, one_mul]
  have hzu : z = u * e := by rw [he, ← mul_assoc, hu2, one_mul]
  have key : a * e * a * (a * e * (a * e)) = e := by
    rw [show a * e * a * (a * e * (a * e)) = a * e * (a * a) * e * (a * e) by group, ha2,
      mul_one, mul_assoc a e e, he2, mul_one, ← mul_assoc, ha2, one_mul]
  set ea := a * e * a with hea'
  have hzeb : z = ea * b' := by
    rw [hb'w, hzu, ← heu.eq, hw, sq,
      show ea * (a * e * (a * e) * u) = (a * e * a * (a * e * (a * e))) * u by
        rw [hea']; group, key]
  have hxu2 : ¬ Commute x u := fun hc =>
    not_opposite_of_commute_mul hD hd ha hb hab hx hc ⟨hdx, hodd⟩
  have hwx : ¬ Commute w x ∧ Odd (orderOf (w * x)) := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hwD hx with hc | h4' | ⟨ho, hnc⟩
    · exact absurd (commute_of_mem_rootGroup_of_commute huW hx hc).symm hxu2
    · exfalso
      have hP := isPGroup_sup_rootGroup hD hwD hx (Or.inr h4')
      have hxmem : x * u ∈ rootGroup D w ⊔ rootGroup D x :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right
          (rootSet_subset_rootGroup D x (mem_rootSet_self hx))) (Subgroup.mem_sup_left huW)
      obtain ⟨k, hk⟩ := hP ⟨x * u, hxmem⟩
      have hk' : (x * u) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hdvd := orderOf_dvd_of_pow_eq_one hk'
      rw [hxu] at hdvd
      have hm1 := eq_one_of_two_mul_dvd_two_pow hm hdvd
      rw [hm1, mul_one] at hxu
      exact hxu2 ((commute_iff_mul_sq_eq_one hx2 hu2).2 (by rw [← hxu, pow_orderOf_eq_one]))
    · exact ⟨hnc, ho⟩
  have hb'x : ¬ Commute b' x := fun hc => hwx.1 ((hb'T.2 x hx).1 hc)
  have hoxb' : Odd (orderOf (x * b')) := by
    rw [orderOf_mul_comm_eq]
    exact (odd_orderOf_mul_iff_of_mem_rootSet hD hwD hb'T hx hwx.1).2 hwx.2
  have heaD : ea ∈ D := by simpa [hD.inv_eq haD] using hN a e heD
  have hea2 := hD.mul_self_eq_one heaD
  have hz2 : z * z = 1 := by
    rw [hz, ← pow_add, ← two_mul, ← hxu, pow_orderOf_eq_one]
  have heab' : Commute ea b' :=
    (commute_iff_mul_sq_eq_one hea2 hb'2).2 (by rw [sq, ← hzeb, hz2])
  have hzb' : Commute z b' := by rw [hzeb]; exact heab'.mul_left (Commute.refl b')
  have hzxb' : Commute z (x * b') := hzx.mul_right hzb'
  have hxea : x * ea = z * (x * b') := by
    have hez : ea = z * b' := by rw [hzeb, mul_assoc, hb'2, mul_one]
    rw [hez, ← mul_assoc, ← hzx.eq, mul_assoc]
  have hz1 : z ≠ 1 := by
    intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one (show (x * u) ^ m = 1 from h1)
    rw [hxu] at hdvd
    have := Nat.le_of_dvd hm.pos hdvd
    have := hm.pos
    omega
  have hoz : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hz2]) hz1
  have hord : orderOf (x * ea) = 2 * orderOf (x * b') := by
    rw [hxea, hzxb'.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [hoz]; exact Nat.coprime_two_left.2 hoxb'), hoz]
  rcases hD.orderOf_mul hx heaD with h2 | h4'' | ho
  · rw [hord] at h2
    have h1 : orderOf (x * b') = 1 := by omega
    rw [orderOf_eq_one_iff] at h1
    have hxb : x = b' := by rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hb'D]
    exact hb'x (by simp [hxb])
  · rw [hord] at h4''
    obtain ⟨k, hk⟩ := hoxb'
    omega
  · rw [hord] at ho
    exact (Nat.not_odd_iff_even.2 (even_two_mul _)) ho

theorem commute_rootSet_of_twoOdd (h : Hyp G D) {d a b x : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) {m : ℕ} (hm : Odd m)
    (hxu : orderOf (x * (a * b)) = 2 * m) {t : G} (ht : t ∈ rootSet D d) :
    Commute (a * b * (x * (a * b)) ^ m) t := by
  have hea := commute_of_twoOdd h hd ha hb hab hx hdx hodd hm hxu
  have heD := (mem_of_twoOdd h.isClass h.root hd ha hb hx hab hm hxu).1
  exact ((ht.2 _ heD).2 ((ha.2 _ heD).1 hea.symm)).symm

theorem commute_of_mem_closure_of_twoOdd (h : Hyp G D) {d a b x : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) {m : ℕ} (hm : Odd m)
    (hxu : orderOf (x * (a * b)) = 2 * m) {g : G}
    (hg : g ∈ Subgroup.closure (insert x (rootSet D d))) : Commute ((x * (a * b)) ^ m) g := by
  have hD := h.root
  have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
  obtain ⟨hzx, -, -⟩ := Closure.third_kind (hD.mul_self_eq_one hx) hu2 hm hxu
  have hz : (x * (a * b)) ^ m = a * b * (a * b * (x * (a * b)) ^ m) := by
    rw [← mul_assoc (a * b) (a * b), hu2, one_mul]
  have huW : a * b ∈ rootGroup D d := mul_mem_rootGroup ha hb
  have hgen : ∀ y ∈ insert x (rootSet D d), Commute ((x * (a * b)) ^ m) y := by
    rintro y (rfl | hy)
    · exact hzx
    · rw [hz]
      exact (commute_of_mem_rootGroup_of_commute huW hy.1
        ((hy.2 d hd).2 (Commute.refl d)).symm).mul_left
          (commute_rootSet_of_twoOdd h hd ha hb hab hx hdx hodd hm hxu hy)
  induction hg using Subgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | one => exact Commute.one_right _
  | mul y y' _ _ ihy ihy' => exact ihy.mul_right ihy'
  | inv y _ ihy => exact ihy.inv_right

theorem closure_ne_top_of_twoOdd (h : Hyp G D) {d a b x : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) {m : ℕ} (hm : Odd m)
    (hxu : orderOf (x * (a * b)) = 2 * m) {S : Set G} (hS : S ⊆ rootSet D d) :
    Subgroup.closure (insert x S) ≠ ⊤ := by
  intro htop
  have hle : Subgroup.closure (insert x S) ≤ Subgroup.closure (insert x (rootSet D d)) :=
    Subgroup.closure_mono (Set.insert_subset_insert hS)
  have hcent : (x * (a * b)) ^ m ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (commute_of_mem_closure_of_twoOdd h hd ha hb hab hx hdx hodd hm hxu
      (hle (htop ▸ Subgroup.mem_top g))).symm.eq
  rw [h.center_eq_bot, Subgroup.mem_bot] at hcent
  have hdvd := orderOf_dvd_of_pow_eq_one hcent
  rw [hxu] at hdvd
  have := Nat.le_of_dvd hm.pos hdvd
  have := hm.pos
  omega

end CFSG.Timmesfeld.Bridge.RootClosure
