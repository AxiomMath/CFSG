module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

variable {G : Type*} [Group G]

theorem exists_fixed_of_involutive {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  classical
  let := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hsq : hf.toPerm f ^ 2 ^ 1 = 1 := by
    ext x
    simp only [pow_one, pow_two, Equiv.Perm.mul_apply, Function.Involutive.coe_toPerm, hf x,
      Equiv.Perm.one_apply]
  exact Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hnot hsq

theorem card_diff_one (Q : Subgroup G) :
    Nat.card ↥((Q : Set G) \ {1}) = Nat.card Q - 1 := by
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (s := (Q : Set G)) Q.one_mem,
    ← Nat.card_coe_set_eq]
  rfl

theorem odd_two_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Odd (2 ^ e - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one

theorem conj_ne_one {a w : G} (ha : a ≠ 1) : w⁻¹ * a * w ≠ 1 := by
  intro h
  apply ha
  have h' := congrArg (fun x : G => w * x * w⁻¹) h
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h'

theorem mem_centralizer_of_conj_eq {a w : G} (h : w⁻¹ * a * w = a) :
    a ∈ Subgroup.centralizer ({w} : Set G) := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h' := congrArg (fun x : G => w * x) h
  simpa only [mul_assoc, mul_inv_cancel_left] using h'

theorem conj_eq_of_mem_centralizer {a w : G}
    (h : a ∈ Subgroup.centralizer ({w} : Set G)) : w⁻¹ * a * w = a := by
  rw [mul_assoc, Subgroup.mem_centralizer_singleton_iff.mp h, inv_mul_cancel_left]

theorem mul_self_eq_one_of_orderOf_eq_two {w : G} (hw : orderOf w = 2) : w * w = 1 := by
  have h := pow_orderOf_eq_one w
  rwa [hw, pow_two] at h

theorem exists_nonidentity_commute [Finite G] {Q : Subgroup G} {e : ℕ}
    (hQcard : Nat.card Q = 2 ^ e) (he : 1 ≤ e) {w : G} (hw : orderOf w = 2)
    (hnorm : ∀ v ∈ Q, w⁻¹ * v * w ∈ Q) :
    ∃ v ∈ Q, v ≠ 1 ∧ v ∈ Subgroup.centralizer ({w} : Set G) := by
  have hwinv : w⁻¹ = w := inv_eq_self_of_orderOf_eq_two hw
  let S := (Q : Set G) \ {1}
  let f : S → S := fun v => ⟨w⁻¹ * v * w, hnorm v v.2.1, conj_ne_one v.2.2⟩
  have hf : Function.Involutive f := by
    intro v
    apply Subtype.ext
    change w⁻¹ * (w⁻¹ * v * w) * w = v
    rw [hwinv]
    have hww : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hw
    calc
      w * (w * (v : G) * w) * w = (w * w) * v * (w * w) := by simp only [mul_assoc]
      _ = v := by rw [hww, one_mul, mul_one]
  have hodd : Odd (Nat.card S) := by
    rw [card_diff_one, hQcard]
    exact odd_two_pow_sub_one he
  obtain ⟨v, hv⟩ := exists_fixed_of_involutive hf hodd
  exact ⟨v, v.2.1, v.2.2, mem_centralizer_of_conj_eq (congrArg Subtype.val hv)⟩

theorem card_eq_of_regular {K : Subgroup G} {S : Set G}
    (hS : ∀ k ∈ K, ∀ a ∈ S, k⁻¹ * a * k ∈ S)
    (hreg : ∀ a ∈ S, ∀ b ∈ S, ∃! k : K, (k : G)⁻¹ * a * k = b) {a : G} (ha : a ∈ S) :
    Nat.card K = Nat.card S := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun k : K => (⟨(k : G)⁻¹ * a * k, hS k k.2 a ha⟩ : S)) ⟨?_, ?_⟩
  · intro k₁ k₂ hk
    obtain ⟨k, _, huniq⟩ := hreg a ha _ (hS k₁ k₁.2 a ha)
    exact (huniq k₁ rfl).trans (huniq k₂ (congrArg Subtype.val hk).symm).symm
  · rintro ⟨b, hb⟩
    obtain ⟨k, hk, _⟩ := hreg a ha b hb
    exact ⟨k, Subtype.ext hk⟩

theorem regular_restrict {Q X : Subgroup G} {u : G}
    (hXu : ∀ x ∈ X, u⁻¹ * x * u ∈ X)
    (hreg : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b) :
    ∀ a ∈ ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) \ {1},
        ∃! x : (X ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G),
          (x : G)⁻¹ * a * x = b := by
  intro a ha b hb
  obtain ⟨x, hx, huniq⟩ := hreg a ⟨ha.1.1, ha.2⟩ b ⟨hb.1.1, hb.2⟩
  have hau : u * a * u⁻¹ = a := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp ha.1.2, mul_inv_cancel_right]
  let x' : X := ⟨u⁻¹ * x * u, hXu x x.2⟩
  have hx' : (x' : G)⁻¹ * a * x' = b := by
    change (u⁻¹ * x * u)⁻¹ * a * (u⁻¹ * x * u) = b
    calc
      (u⁻¹ * x * u)⁻¹ * a * (u⁻¹ * x * u) = u⁻¹ * ((x : G)⁻¹ * (u * a * u⁻¹) * x) * u := by
        group
      _ = u⁻¹ * b * u := by rw [hau, hx]
      _ = b := conj_eq_of_mem_centralizer hb.1.2
  have hxx : x' = x := huniq x' hx'
  have hxu : (x : G) ∈ Subgroup.centralizer ({u} : Set G) :=
    mem_centralizer_of_conj_eq (congrArg Subtype.val hxx)
  refine ⟨⟨x, x.2, hxu⟩, hx, ?_⟩
  intro y hy
  have hyx : (y : G) = x := congrArg Subtype.val (huniq ⟨y, y.2.1⟩ hy)
  exact Subtype.ext hyx

theorem card_le_card_fixed_sq [Finite G] {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q)
    {u : G} (hu : orderOf u = 2) (hQu : ∀ v ∈ Q, u⁻¹ * v * u ∈ Q) :
    Nat.card Q ≤ Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ^ 2 := by
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm (⟨a, ha⟩ : Q) ⟨b, hb⟩)
  have hinv : ∀ a ∈ Q, a⁻¹ = a := fun a ha =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hQ.2 a ha)
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  let E : Subgroup G := Q ⊓ Subgroup.centralizer ({u} : Set G)
  let c : Q →* Q :=
    { toFun := fun v => ⟨(v : G)⁻¹ * (u⁻¹ * v * u), Q.mul_mem (Q.inv_mem v.2) (hQu v v.2)⟩
      map_one' := by
        apply Subtype.ext
        simp only [OneMemClass.coe_one, inv_one, mul_one, inv_mul_cancel]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hA : (a : G)⁻¹ * (u⁻¹ * a * u) ∈ Q := Q.mul_mem (Q.inv_mem a.2) (hQu a a.2)
        calc
          ((a : G) * b)⁻¹ * (u⁻¹ * (a * b) * u) =
              (b : G)⁻¹ * ((a : G)⁻¹ * (u⁻¹ * a * u)) * (u⁻¹ * b * u) := by group
          _ = ((a : G)⁻¹ * (u⁻¹ * a * u)) * (b : G)⁻¹ * (u⁻¹ * b * u) := by
            rw [hcomm _ (Q.inv_mem b.2) _ hA]
          _ = (a : G)⁻¹ * (u⁻¹ * a * u) * ((b : G)⁻¹ * (u⁻¹ * b * u)) := by group }
  have hc (v : Q) : (c v : G) = (v : G)⁻¹ * (u⁻¹ * v * u) := rfl
  have hker (v : Q) : v ∈ c.ker ↔ (v : G) ∈ E := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hv
      have hv' : (v : G)⁻¹ * (u⁻¹ * v * u) = 1 := congrArg Subtype.val hv
      refine ⟨v.2, mem_centralizer_of_conj_eq ?_⟩
      have h' := congrArg (fun x : G => (v : G) * x) hv'
      simpa only [mul_inv_cancel_left, mul_one] using h'
    · intro hv
      apply Subtype.ext
      change (v : G)⁻¹ * (u⁻¹ * v * u) = 1
      rw [conj_eq_of_mem_centralizer hv.2, inv_mul_cancel]
  have hrange (v : Q) : (c v : G) ∈ E := by
    refine ⟨(c v).2, mem_centralizer_of_conj_eq ?_⟩
    rw [hc]
    have hw : u⁻¹ * (v : G) * u ∈ Q := hQu v v.2
    have hconj2 : u⁻¹ * (u⁻¹ * (v : G) * u) * u = v := by
      calc
        u⁻¹ * (u⁻¹ * (v : G) * u) * u = (u * u)⁻¹ * v * (u * u) := by group
        _ = v := by rw [huu, inv_one, one_mul, mul_one]
    calc
      u⁻¹ * ((v : G)⁻¹ * (u⁻¹ * v * u)) * u =
          (u⁻¹ * (v : G) * u)⁻¹ * (u⁻¹ * (u⁻¹ * (v : G) * u) * u) := by group
      _ = (u⁻¹ * (v : G) * u) * v := by rw [hinv _ hw, hconj2]
      _ = (v : G) * (u⁻¹ * v * u) := hcomm _ hw _ v.2
      _ = (v : G)⁻¹ * (u⁻¹ * v * u) := by rw [hinv _ v.2]
  have hkercard : Nat.card c.ker = Nat.card E := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun v : c.ker => (⟨((v : Q) : G), (hker v).mp v.2⟩ : E))
      ⟨?_, ?_⟩
    · intro v w hvw
      have h' : ((v : Q) : G) = ((w : Q) : G) := congrArg (fun x : E => (x : G)) hvw
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨x, hx⟩
      exact ⟨⟨⟨x, hx.1⟩, (hker ⟨x, hx.1⟩).mpr hx⟩, rfl⟩
  have hrangecard : Nat.card c.range ≤ Nat.card E := by
    refine Nat.card_le_card_of_injective
      (fun v : c.range => (⟨((v : Q) : G), ?_⟩ : E)) ?_
    · obtain ⟨w, hw⟩ := v.2
      rw [← hw]
      exact hrange w
    · intro v w hvw
      have h' : ((v : Q) : G) = ((w : Q) : G) := congrArg (fun x : E => (x : G)) hvw
      exact Subtype.ext (Subtype.ext h')
  have hcard := c.ker.index_mul_card
  rw [Subgroup.index_ker] at hcard
  calc
    Nat.card Q = Nat.card c.range * Nat.card c.ker := hcard.symm
    _ ≤ Nat.card E * Nat.card E := Nat.mul_le_mul hrangecard hkercard.le
    _ = Nat.card E ^ 2 := (sq _).symm

theorem exponent_eq_two_mul {e f : ℕ} (hdvd : 2 ^ f - 1 ∣ 2 ^ e - 1) (hle : e ≤ 2 * f)
    (hlt : f < e) : e = 2 * f := by
  have hgcd := Nat.pow_sub_one_gcd_pow_sub_one 2 f e
  rw [Nat.gcd_eq_left hdvd] at hgcd
  have hpow : 2 ^ f = 2 ^ Nat.gcd f e := by
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ Nat.gcd f e := Nat.one_le_two_pow
    omega
  have hf : f = Nat.gcd f e := Nat.pow_right_injective le_rfl hpow
  have hfe : f ∣ e := hf ▸ Nat.gcd_dvd_right f e
  obtain ⟨m, rfl⟩ := hfe
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      simp at hlt
    · exact h0
  have hm1 : 1 < m := by
    by_contra hm
    have : f * m ≤ f * 1 := Nat.mul_le_mul_left f (by omega)
    omega
  have hm2 : m ≤ 2 := by
    by_contra hm
    have : f * 3 ≤ f * m := Nat.mul_le_mul_left f (by omega)
    omega
  have hm : m = 2 := by omega
  rw [hm, mul_comm]

theorem fixed_field_structure [Finite G] {Q X : Subgroup G} {e : ℕ}
    (hQ : CFSG.Open.IsElemAbelian 2 Q) (hQcard : Nat.card Q = 2 ^ e) (hQ4 : 4 ≤ Nat.card Q)
    (hXQ : ∀ x ∈ X, ∀ v ∈ Q, x⁻¹ * v * x ∈ Q)
    (hXcyclic : IsCyclic X) (hXcard : Nat.card X = Nat.card Q - 1)
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    {u : G} (hu : orderOf u = 2) (huQ : ∀ v ∈ Q, u⁻¹ * v * u ∈ Q)
    (huX : ∀ x ∈ X, u⁻¹ * x * u ∈ X) :
    let Y := Subgroup.centralizer ({u} : Set G)
    let E := Q ⊓ Y
    let X₀ := X ⊓ Y
    2 ≤ Nat.card E ∧
      (Q ≤ Y → Nat.card E = Nat.card Q ∧ X₀ = X) ∧
      (¬ Q ≤ Y → Even e ∧ Nat.card E = 2 ^ (e / 2) ∧ Nat.card Q = Nat.card E ^ 2) ∧
      IsCyclic X₀ ∧ Nat.card X₀ = Nat.card E - 1 ∧
      (∀ a ∈ (E : Set G) \ {1}, ∀ b ∈ (E : Set G) \ {1},
        ∃! x : X₀, (x : G)⁻¹ * a * x = b) := by
  intro Y E X₀
  have he : 2 ≤ e := by
    by_contra he
    have hle : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨v, hvQ, hv1, hvY⟩ := exists_nonidentity_commute hQcard (by omega) hu huQ
  have hvE : v ∈ (E : Set G) \ {1} := ⟨⟨hvQ, hvY⟩, hv1⟩
  have hreg := regular_restrict (Q := Q) huX hXregular
  have hS : ∀ x ∈ X₀, ∀ a ∈ (E : Set G) \ {1}, x⁻¹ * a * x ∈ (E : Set G) \ {1} := by
    intro x hx a ha
    refine ⟨⟨hXQ x hx.1 a ha.1.1, ?_⟩, conj_ne_one ha.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2) ha.1.2) hx.2
  have hX₀card : Nat.card X₀ = Nat.card E - 1 := by
    rw [card_eq_of_regular hS hreg hvE, card_diff_one]
  have hE2 : 2 ≤ Nat.card E := by
    have hpos : 0 < Nat.card X₀ := Nat.card_pos
    omega
  have hEQ : E ≤ Q := inf_le_left
  have hX₀X : X₀ ≤ X := inf_le_left
  obtain ⟨f, -, hEcard⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (hQcard ▸ Subgroup.card_dvd_of_le hEQ)
  refine ⟨hE2, ?_, ?_, Subgroup.isCyclic_of_le hX₀X, hX₀card, hreg⟩
  · intro hQY
    have hEeq : E = Q := inf_eq_left.mpr hQY
    have hEQcard : Nat.card E = Nat.card Q := by rw [hEeq]
    refine ⟨hEQcard, Subgroup.eq_of_le_of_card_ge hX₀X ?_⟩
    rw [hX₀card, hEQcard, hXcard]
  · intro hQY
    have hEne : E ≠ Q := fun hEeq => hQY (inf_eq_left.mp hEeq)
    have hlt : Nat.card E < Nat.card Q :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hEQ hEne)
    rw [hEcard, hQcard] at hlt
    have hflt : f < e := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    have hsq := card_le_card_fixed_sq hQ hu huQ
    change Nat.card Q ≤ Nat.card E ^ 2 at hsq
    rw [hEcard, hQcard, ← pow_mul] at hsq
    have hfle : e ≤ f * 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hsq
    have hdvd : 2 ^ f - 1 ∣ 2 ^ e - 1 := by
      rw [← hEcard, ← hQcard, ← hX₀card, ← hXcard]
      exact Subgroup.card_dvd_of_le hX₀X
    have he2 : e = 2 * f := exponent_eq_two_mul hdvd (by omega) hflt
    refine ⟨⟨f, by omega⟩, ?_, ?_⟩
    · rw [hEcard, he2, Nat.mul_div_cancel_left f (by norm_num)]
    · rw [hEcard, hQcard, he2, pow_mul', ← pow_mul, mul_comm]

end CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
