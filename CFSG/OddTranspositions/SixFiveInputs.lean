module

public import CFSG.OddTranspositions.SixFiveNormal

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_of_mul_mem_of_isPGroup (hD : IsOddTransp D) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : x * y ∈ Q) :
    Commute x y := by
  obtain ⟨n, hn⟩ := hQ ⟨x * y, hxy⟩
  have hpow : (x * y) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hdvd : orderOf (x * y) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf (x * y) ∣ 2 := by
    rcases hD.2 x hx y hy with h | ho
    · exact h
    · obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rw [hm] at ho ⊢
      cases m with
      | zero => simp
      | succ m => exact absurd ho (by simp [pow_succ, Nat.not_odd_iff_even])
  have hsq : (x * y) * (x * y) = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hx2 : x * x = 1 := hD.mul_self_eq_one hx
  have hy2 : y * y = 1 := hD.mul_self_eq_one hy
  show x * y = y * x
  have hinv : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hsq
  rw [← hinv, mul_inv_rev, inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hy2]

def commSetQ (D : Set G) (Q : Subgroup G) (u : G) : Set G := {y | y ∈ D ∧ y * u ∈ Q}

theorem commute_of_mem_commSetQ (hD : IsOddTransp D) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    {u y z : G} (hu : u ∈ D) (hy : y ∈ commSetQ D Q u) (hz : z ∈ commSetQ D Q u) :
    Commute y z := by
  refine commute_of_mul_mem_of_isPGroup hD hQ hy.1 hz.1 ?_
  have hu2 : u * u = 1 := hD.mul_self_eq_one hu
  have hz2 : z * z = 1 := hD.mul_self_eq_one hz.1
  have : y * z = (y * u) * (z * u)⁻¹ := by
    calc y * z = (y * u) * (u * u)⁻¹ * u * (z * z) * z⁻¹ := by group
      _ = (y * u) * (z * u)⁻¹ := by
        rw [hu2, hz2]
        have : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
        rw [mul_inv_rev, this, hu']; group
  rw [this]
  exact Q.mul_mem hy.2 (Q.inv_mem hz.2)

theorem closure_commSetQ_le_centralizer (hD : IsOddTransp D) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {u : G} (hu : u ∈ D) :
    Subgroup.closure (commSetQ D Q u) ≤
      Subgroup.centralizer (Subgroup.closure (commSetQ D Q u) : Set G) := by
  have h1 : Subgroup.closure (commSetQ D Q u) ≤ Subgroup.centralizer (commSetQ D Q u) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    exact (commute_of_mem_commSetQ hD hQ hu hz hy).eq
  rw [Subgroup.le_centralizer_iff]
  rw [Subgroup.closure_le]
  intro y hy
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro z hz
  have := h1 hz
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this y hy).symm

theorem mem_commSetQ_self (hD : IsOddTransp D) {Q : Subgroup G} {u : G} (hu : u ∈ D) :
    u ∈ commSetQ D Q u := ⟨hu, by rw [hD.mul_self_eq_one hu]; exact Q.one_mem⟩

theorem commutator_zpowers_le_closure_commSetQ (hD : IsOddTransp D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) {Q : Subgroup G} (hQn : Q.Normal) {u : G}
    (hu : u ∈ D) : ⁅Q, Subgroup.zpowers u⁆ ≤ Subgroup.closure (commSetQ D Q u) := by
  rw [Subgroup.commutator_le]
  intro q hq x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hord : orderOf u = 2 := hD.1 u hu
  rw [← zpow_mod_orderOf, hord]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [Nat.cast_ofNat, h]; simp
  · rw [Nat.cast_ofNat, h, zpow_one]
    have hu' : u⁻¹ = u := hD.inv_eq hu
    rw [commutatorElement_def, hu']
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hN q u hu, ?_⟩)
      (Subgroup.subset_closure (mem_commSetQ_self hD hu))
    have : q * u * q⁻¹ * u = q * (u * q⁻¹ * u⁻¹) := by rw [hu']; group
    rw [this]
    exact Q.mul_mem hq (hQn.conj_mem _ (Q.inv_mem hq) u)

theorem sixFive_hZc (hS : Setup G D) {Q : Subgroup G} (hQn : Q.Normal) (hQp : IsPGroup 2 Q)
    {u w : G} (hu : u ∈ D) (hw : w ∈ D)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hQF : Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆) :
    (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) ≤ Subgroup.center G := by
  intro z hz
  have hPu := commutator_zpowers_le_closure_commSetQ hS.oddT hS.normal hQn hu
  have hRw := commutator_zpowers_le_closure_commSetQ hS.oddT hS.normal hQn hw
  have hAu := closure_commSetQ_le_centralizer hS.oddT hQp hu
  have hAw := closure_commSetQ_le_centralizer hS.oddT hQp hw
  have hzu : z ∈ Subgroup.closure (commSetQ D Q u) := hPu hz.1
  have hzw : z ∈ Subgroup.closure (commSetQ D Q w) := hRw hz.2
  have key : (⊤ : Subgroup G) ≤ Subgroup.centralizer {z} := by
    rw [← hgenQ]
    refine sup_le ?_ ?_
    · rw [hQF]
      refine sup_le (fun p hp => ?_) (fun p hp => ?_)
      · have := hAu (hPu hp)
        rw [Subgroup.mem_centralizer_iff] at this
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (this z hzu).symm
      · have := hAw (hRw hp)
        rw [Subgroup.mem_centralizer_iff] at this
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (this z hzw).symm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · have := hAu (Subgroup.subset_closure (mem_commSetQ_self hS.oddT hu))
        rw [Subgroup.mem_centralizer_iff] at this
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (this z hzu).symm
      · have := hAw (Subgroup.subset_closure (mem_commSetQ_self hS.oddT hw))
        rw [Subgroup.mem_centralizer_iff] at this
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (this z hzw).symm
  rw [Subgroup.mem_center_iff]
  intro g
  have := key (Subgroup.mem_top g)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_of_mem_commutator_zpowers (hD : IsOddTransp D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) {Q : Subgroup G} (hQn : Q.Normal)
    (hQp : IsPGroup 2 Q) {u p : G} (hu : u ∈ D) (hp : p ∈ ⁅Q, Subgroup.zpowers u⁆) :
    Commute p u := by
  have := closure_commSetQ_le_centralizer hD hQp hu
    (commutator_zpowers_le_closure_commSetQ hD hN hQn hu hp)
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this u (Subgroup.subset_closure (mem_commSetQ_self hD hu))).symm

theorem centralizer_inf_le_commutator_zpowers (hS : Setup G D) {Q : Subgroup G}
    (hQn : Q.Normal) (hQp : IsPGroup 2 Q) {u w : G} (hu : u ∈ D) (hw : w ∈ D)
    (hnc : ¬ Commute u w) (hQF : Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆) :
    Subgroup.centralizer {u} ⊓ Q ≤ ⁅Q, Subgroup.zpowers u⁆ := by
  rintro q ⟨hqu, hqQ⟩
  rw [hQF] at hqQ
  have hmem : q ∈ ((⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G) :=
    hqQ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (sixFive_hPR hQn u w)] at hmem
  obtain ⟨p, hp, r, hr, rfl⟩ := hmem
  have hpu : Commute p u := commute_of_mem_commutator_zpowers hS.oddT hS.normal hQn hQp hu hp
  have hrw : Commute r w := commute_of_mem_commutator_zpowers hS.oddT hS.normal hQn hQp hw hr
  have hru : Commute r u := by
    have hqu' : p * r ∈ Subgroup.centralizer {u} := hqu
    rw [Subgroup.mem_centralizer_singleton_iff] at hqu'
    show r * u = u * r
    calc r * u = p⁻¹ * (p * r * u) := by group
      _ = p⁻¹ * (u * (p * r)) := by rw [hqu']
      _ = p⁻¹ * (u * p) * r := by group
      _ = u * r := by rw [← hpu.eq]; group
  obtain ⟨h, hh, hhu⟩ := hS.oddT.exists_conj hu hw hnc
  have hcl : Subgroup.closure ({u, w} : Set G) ≤ Subgroup.centralizer {r} := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]; exact hru.eq.symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]; exact hrw.eq.symm
  have hrh : h * r = r * h := by
    have := hcl hh
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hR : ⁅Q, Subgroup.zpowers w⁆ =
      (⁅Q, Subgroup.zpowers u⁆).map (MulAut.conj h).toMonoidHom := by
    rw [← hhu]; exact commutator_zpowers_conj hQn u h
  rw [hR] at hr
  obtain ⟨p', hp', hp'r⟩ := Subgroup.mem_map.mp hr
  have hp'r' : h * p' * h⁻¹ = r := hp'r
  have hrp : r = p' := by
    calc r = h⁻¹ * (h * r) := by group
      _ = h⁻¹ * (r * h) := by rw [hrh]
      _ = h⁻¹ * (h * p' * h⁻¹) * h := by rw [hp'r']; group
      _ = p' := by group
  exact Subgroup.mul_mem _ hp (hrp ▸ hp')

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem zpow_eq_one_of_zpow_two_mul {c : G} (hodd : Odd (orderOf c)) {k : ℤ}
    (h : c ^ (2 * k) = 1) : c ^ k = 1 := by
  have h1 : (orderOf c : ℤ) ∣ 2 * k := orderOf_dvd_iff_zpow_eq_one.mpr h
  have h2 : orderOf c ∣ 2 * k.natAbs := by
    have := Int.natCast_dvd.mp h1
    rwa [Int.natAbs_mul] at this
  have h3 : orderOf c ∣ k.natAbs := (hodd.coprime_two_right.dvd_mul_left).mp h2
  exact orderOf_dvd_iff_zpow_eq_one.mp (Int.natCast_dvd.mpr h3)

theorem mul_zpow_conj {u w : G} (hu2 : u * u = 1) (hw2 : w * w = 1) (l : ℤ) :
    u * (u * w) ^ l = (u * w) ^ (-l) * u := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h1 : u * (u * w) * u⁻¹ = (u * w)⁻¹ := by
    rw [mul_inv_rev, hui, hwi]
    calc u * (u * w) * u = (u * u) * w * u := by group
      _ = w * u := by rw [hu2, one_mul]
  have h2 : u * (u * w) ^ l * u⁻¹ = (u * w) ^ (-l) := by
    rw [← conj_zpow, h1, inv_zpow']
  calc u * (u * w) ^ l = (u * (u * w) ^ l * u⁻¹) * u := by group
    _ = (u * w) ^ (-l) * u := by rw [h2]

theorem closure_pair_normal_form {u w : G} (hu2 : u * u = 1) (hw2 : w * w = 1) {a : G}
    (ha : a ∈ Subgroup.closure ({u, w} : Set G)) :
    ∃ k : ℤ, a = (u * w) ^ k ∨ a = (u * w) ^ k * u := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hc := mul_zpow_conj hu2 hw2
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, mul_inv_rev, hui, hwi, mul_assoc, hu2, mul_one]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨k, rfl | rfl⟩ := ihx <;> obtain ⟨l, rfl | rfl⟩ := ihy
    · exact ⟨k + l, Or.inl (by rw [zpow_add])⟩
    · exact ⟨k + l, Or.inr (by rw [zpow_add]; group)⟩
    · refine ⟨k - l, Or.inr ?_⟩
      rw [mul_assoc, hc, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨k - l, Or.inl ?_⟩
      rw [show (u * w) ^ k * u * ((u * w) ^ l * u) = (u * w) ^ k * (u * (u * w) ^ l) * u by group,
        hc, sub_eq_add_neg, zpow_add]
      rw [show (u * w) ^ k * ((u * w) ^ (-l) * u) * u = (u * w) ^ k * (u * w) ^ (-l) * (u * u) by
        group, hu2, mul_one]
  | inv x _ ih =>
    obtain ⟨k, rfl | rfl⟩ := ih
    · exact ⟨-k, Or.inl (by rw [zpow_neg])⟩
    · refine ⟨k, Or.inr ?_⟩
      rw [mul_inv_rev, hui, ← zpow_neg, hc, neg_neg]

theorem eq_one_or_eq_of_mem_closure_pair (hD : IsOddTransp D) {u w : G} (hu : u ∈ D)
    (hw : w ∈ D) (hnc : ¬ Commute u w) {a : G} (ha : a ∈ Subgroup.closure ({u, w} : Set G))
    (hau : Commute a u) : a = 1 ∨ a = u := by
  have hu2 := hD.mul_self_eq_one hu
  have hw2 := hD.mul_self_eq_one hw
  have hodd := hD.odd_of_not_commute hu hw hnc
  have hc := mul_zpow_conj hu2 hw2
  have key : ∀ k : ℤ, (u * w) ^ k * u = u * (u * w) ^ k → (u * w) ^ k = 1 := by
    intro k hk
    rw [hc] at hk
    have hk' : (u * w) ^ k = (u * w) ^ (-k) := mul_right_cancel hk
    apply zpow_eq_one_of_zpow_two_mul hodd
    rw [two_mul, zpow_add]
    nth_rewrite 1 [hk']
    rw [← zpow_add, neg_add_cancel, zpow_zero]
  obtain ⟨k, rfl | rfl⟩ := closure_pair_normal_form hu2 hw2 ha
  · exact Or.inl (key k hau.eq)
  · refine Or.inr ?_
    have h1 : (u * w) ^ k * u * u = u * ((u * w) ^ k * u) := hau.eq
    have h2 : (u * w) ^ k * u = u * (u * w) ^ k := by
      calc (u * w) ^ k * u = ((u * w) ^ k * u * u) * u := by
            rw [show (u * w) ^ k * u * u * u = (u * w) ^ k * (u * u) * u by group, hu2, mul_one]
        _ = u * ((u * w) ^ k * u) * u := by rw [h1]
        _ = u * (u * w) ^ k * (u * u) := by group
        _ = u * (u * w) ^ k := by rw [hu2, mul_one]
    rw [key k h2, one_mul]

theorem sixFive_hZtop (hS : Setup G D) {Q : Subgroup G} (hQn : Q.Normal) (hQp : IsPGroup 2 Q)
    {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hQF : Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆) :
    Subgroup.center G ≤ (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) := by
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hzmem : z ∈ ((Q ⊔ Subgroup.closure ({u, w} : Set G) : Subgroup G) : Set G) := by
    rw [hgenQ]; trivial
  haveI := hQn
  rw [Subgroup.normal_mul] at hzmem
  obtain ⟨q, hq, a, ha, rfl⟩ := hzmem
  have hAQ := inf_closure_pair_eq_bot hS hQn hQp hu hw hnc
  have hcomm : ∀ x ∈ ({u, w} : Set G), Commute a x := by
    intro x hx
    have hxA : x ∈ Subgroup.closure ({u, w} : Set G) := Subgroup.subset_closure hx
    have hzx : x * (q * a) = q * a * x := hz x
    have hmem : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.closure ({u, w} : Set G) ⊓ Q := by
      refine ⟨?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hxA)
          (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hxA)
      · have : a * x * a⁻¹ * x⁻¹ = q⁻¹ * (x * q * x⁻¹) := by
          calc a * x * a⁻¹ * x⁻¹ = q⁻¹ * ((q * a) * x) * (q * a)⁻¹ * q * x⁻¹ := by group
            _ = q⁻¹ * (x * (q * a)) * (q * a)⁻¹ * q * x⁻¹ := by rw [hzx]
            _ = q⁻¹ * (x * q * x⁻¹) := by group
        rw [this]
        exact Q.mul_mem (Q.inv_mem hq) (hQn.conj_mem q hq x)
    rw [hAQ, Subgroup.mem_bot] at hmem
    show a * x = x * a
    calc a * x = (a * x * a⁻¹ * x⁻¹) * (x * a) := by group
      _ = x * a := by rw [hmem, one_mul]
  have ha1 : a = 1 := by
    rcases eq_one_or_eq_of_mem_closure_pair hS.oddT hu hw hnc ha (hcomm u (by simp)) with h | h
    · exact h
    · exact absurd (h ▸ hcomm w (by simp)) hnc
  subst ha1
  have hz' : ∀ g, g * q = q * g := by simpa using hz
  show q * 1 ∈ _
  rw [mul_one]
  replace hz := hz'
  have hzu : q ∈ Subgroup.centralizer {u} ⊓ Q :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hz u).symm, hq⟩
  have hzw : q ∈ Subgroup.centralizer {w} ⊓ Q :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hz w).symm, hq⟩
  exact ⟨centralizer_inf_le_commutator_zpowers hS hQn hQp hu hw hnc hQF hzu,
    centralizer_inf_le_commutator_zpowers hS hQn hQp hw hu (fun h => hnc h.symm)
      (by rw [sup_comm]; exact hQF) hzw⟩

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem D_inter_centralizer_eq_conj_Q (hS : Setup G D) {Q : Subgroup G} (hQn : Q.Normal)
    (hQp : IsPGroup 2 Q) {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤) :
    D ∩ (Subgroup.centralizer {u} : Set G) = {x | ∃ q ∈ Q, q * u * q⁻¹ = x} := by
  have hu2 := hS.oddT.mul_self_eq_one hu
  have hui : u⁻¹ = u := hS.oddT.inv_eq hu
  ext d
  constructor
  · rintro ⟨hdD, hdu⟩
    have hdu' : u * d = d * u :=
      (Subgroup.mem_centralizer_singleton_iff.mp (show d ∈ Subgroup.centralizer {u} from hdu)).symm
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isClass hS.isClass hu hdD)
    have hgmem : g ∈ ((Q ⊔ Subgroup.closure ({u, w} : Set G) : Subgroup G) : Set G) := by
      rw [hgenQ]; trivial
    haveI := hQn
    rw [Subgroup.normal_mul] at hgmem
    obtain ⟨q, hq, a, ha, rfl⟩ := hgmem
    set v := a * u * a⁻¹ with hv
    have hvA : v ∈ Subgroup.closure ({u, w} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (Subgroup.subset_closure (by simp)))
        (Subgroup.inv_mem _ ha)
    have hvD : v ∈ D := hS.normal a u hu
    have hdv : d = q * v * q⁻¹ := by rw [← hg]; simp only [hv]; group
    set n := q⁻¹ * (d * q * d⁻¹) with hn
    have hnQ : n ∈ Q := Q.mul_mem (Q.inv_mem hq) (hQn.conj_mem q hq d)
    have hvn : v = n * d := by
      calc v = q⁻¹ * (q * v * q⁻¹) * q := by group
        _ = n * d := by rw [← hdv, hn]; group
    have hcomm : v * u * v⁻¹ * u⁻¹ ∈ Subgroup.closure ({u, w} : Set G) ⊓ Q := by
      refine ⟨?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hvA
          (Subgroup.subset_closure (by simp))) (Subgroup.inv_mem _ hvA))
          (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      · have : v * u * v⁻¹ * u⁻¹ = n * (u * n⁻¹ * u⁻¹) := by
          calc v * u * v⁻¹ * u⁻¹ = n * (d * u) * d⁻¹ * n⁻¹ * u⁻¹ := by rw [hvn]; group
            _ = n * (u * d) * d⁻¹ * n⁻¹ * u⁻¹ := by rw [hdu']
            _ = n * (u * n⁻¹ * u⁻¹) := by group
        rw [this]
        exact Q.mul_mem hnQ (hQn.conj_mem _ (Q.inv_mem hnQ) u)
    rw [inf_closure_pair_eq_bot hS hQn hQp hu hw hnc, Subgroup.mem_bot] at hcomm
    have hvu : Commute v u := by
      show v * u = u * v
      calc v * u = (v * u * v⁻¹ * u⁻¹) * (u * v) := by group
        _ = u * v := by rw [hcomm, one_mul]
    rcases eq_one_or_eq_of_mem_closure_pair hS.oddT hu hw hnc hvA hvu with h | h
    · exact absurd h (hS.oddT.ne_one hvD)
    · exact ⟨q, hq, by rw [hdv, h]⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hS.normal q u hu, ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h := commute_of_mul_mem_of_isPGroup hS.oddT hQp (hS.normal q u hu) hu (by
      have : q * u * q⁻¹ * u = q * (u * q⁻¹ * u⁻¹) := by rw [hui]; group
      rw [this]; exact Q.mul_mem hq (hQn.conj_mem _ (Q.inv_mem hq) u))
    exact h.eq

theorem ncard_mul_card_commutator_zpowers (hS : Setup G D) {Q : Subgroup G} (hQn : Q.Normal)
    (hQp : IsPGroup 2 Q) {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hQF : Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆) :
    (D ∩ (Subgroup.centralizer {u} : Set G)).ncard * Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G)
      = Nat.card Q := by
  classical
  set P : Subgroup G := ⁅Q, Subgroup.zpowers u⁆ with hP
  let e : G ≃* ConjAct G := ConjAct.toConjAct
  set Q' : Subgroup (ConjAct G) := Q.map e.toMonoidHom with hQ'
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hPle : P ≤ Q := commutator_zpowers_le_of_normal hQn u
  have hstab : (MulAction.stabilizer Q' u).map Q'.subtype = P.map e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨q, hq, hqs⟩ := Subgroup.mem_map.mp s.2
      have hs' : (s : ConjAct G) • u = u := hs
      rw [ConjAct.smul_def, ← hqs] at hs'
      have hqs' : q * u * q⁻¹ = u := by simpa [e] using hs'
      refine Subgroup.mem_map.mpr ⟨q, ?_, hqs⟩
      refine centralizer_inf_le_commutator_zpowers hS hQn hQp hu hw hnc hQF
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hq⟩)
      calc q * u = (q * u * q⁻¹) * q := by group
        _ = u * q := by rw [hqs']
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      have hpQ' : e.toMonoidHom p ∈ Q' := Subgroup.mem_map_of_mem _ (hPle hp)
      refine ⟨⟨_, hpQ'⟩, ?_, rfl⟩
      show (e.toMonoidHom p : ConjAct G) • u = u
      rw [ConjAct.smul_def]
      have hpu := commute_of_mem_commutator_zpowers hS.oddT hS.normal hQn hQp hu hp
      simp only [e, MulEquiv.coe_toMonoidHom, ConjAct.ofConjAct_toConjAct]
      rw [hpu.eq]; group
  have horbit : MulAction.orbit Q' u = D ∩ (Subgroup.centralizer {u} : Set G) := by
    rw [D_inter_centralizer_eq_conj_Q hS hQn hQp hu hw hnc hgenQ]
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨q, hq, hqs⟩ := Subgroup.mem_map.mp s.2
      refine ⟨q, hq, ?_⟩
      show q * u * q⁻¹ = (s : ConjAct G) • u
      rw [ConjAct.smul_def, ← hqs]; simp [e]
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨e.toMonoidHom q, Subgroup.mem_map_of_mem _ hq⟩, ?_⟩
      show (e.toMonoidHom q : ConjAct G) • u = q * u * q⁻¹
      rw [ConjAct.smul_def]; simp [e]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer Q' u)
  rw [MulAction.index_stabilizer, horbit] at h1
  have h2 : Nat.card (MulAction.stabilizer Q' u) = Nat.card P := by
    rw [← Subgroup.card_map_of_injective (f := Q'.subtype) Q'.subtype_injective, hstab,
      Subgroup.card_map_of_injective hinj]
  have h3 : Nat.card Q' = Nat.card Q := Subgroup.card_map_of_injective hinj
  rw [← h3, ← h1, h2, mul_comm]

theorem sixFive_hcardP (hS : Setup G D) {Q : Subgroup G} (hQn : Q.Normal)
    (hQp : IsPGroup 2 Q) {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hQF : Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆) :
    Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) =
      (D ∩ Subgroup.centralizer ({u} : Set G)).ncard *
        Nat.card (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) := by
  set P : Subgroup G := ⁅Q, Subgroup.zpowers u⁆ with hP
  set R : Subgroup G := ⁅Q, Subgroup.zpowers w⁆ with hR
  set m := (D ∩ Subgroup.centralizer ({u} : Set G)).ncard
  have hprod : Nat.card Q * Nat.card (P ⊓ R : Subgroup G) = Nat.card P * Nat.card R := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := P) (K := R) (sixFive_hPR hQn u w)
    rw [hQF]; exact h
  have hRP : Nat.card R = Nat.card P :=
    (card_commutator_zpowers_eq_of_isConj hQn (isConj_of_isClass hS.isClass hu hw)).symm
  have hm : m * Nat.card P = Nat.card Q :=
    ncard_mul_card_commutator_zpowers hS hQn hQp hu hw hnc hgenQ hQF
  have hPpos : 0 < Nat.card P := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hPpos
  calc Nat.card P * Nat.card P = Nat.card Q * Nat.card (P ⊓ R : Subgroup G) := by
        rw [hprod, hRP]
    _ = Nat.card P * (m * Nat.card (P ⊓ R : Subgroup G)) := by rw [← hm]; ring

theorem sixFiveGlobal_unconditional (hS : Setup G D)
    {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G) {u w : G}
    (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤) :
    Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ ∧
      Subgroup.center G = ⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ ∧
      Nat.card Q = (D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 *
        Nat.card (Subgroup.center G) := by
  have hQn : Q.Normal := by rw [hQ]; exact CFSG.pCore_normal
  have hQp : IsPGroup 2 Q := by rw [hQ]; exact CFSG.pCore_isPGroup
  have hQF : Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ :=
    sixFive_pCore_eq hS hQ hu hw hnc hgenQ
  exact sixFiveGlobal_of_center_inputs hS hQ hu hw hnc hgenQ
    (sixFive_hZc hS hQn hQp hu hw hgenQ hQF)
    (sixFive_hZtop hS hQn hQp hu hw hnc hgenQ hQF)
    (sixFive_hcardP hS hQn hQp hu hw hnc hgenQ hQF)

end CFSG.OddTranspositions

