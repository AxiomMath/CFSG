module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

open Equiv Equiv.Perm Subgroup

@[expose] def unitVec : Fin 3 → Fin 3 → ZMod 3 := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

theorem hyperplane_cases : ∀ u w : Fin 3 → ZMod 3, u ≠ 0 → (∀ k : ZMod 3, w ≠ k • u) →
    (∃ i j : ZMod 3, ∀ s, (i • u + j • w) s ≠ 0) ∨
      (∃ a b : Fin 3, a ≠ b ∧ (∃ i j : ZMod 3, i • u + j • w = unitVec a) ∧
        ∃ i j : ZMod 3, i • u + j • w = unitVec b) := by
  decide +kernel

@[expose] def cyc9 : Fin 3 → Perm (Fin 9) := ![c1 9, c2 9, c3 9]

theorem cyc9_eq : ∀ a : Fin 3, cyc9 a = vecPerm 9 (unitVec a) := by decide +kernel

theorem cyc9_mem_A0 (a : Fin 3) : cyc9 a ∈ A0 9 := by
  rw [cyc9_eq]
  exact vecPerm_mem_A0 wFacts_nine.toA0Facts _

theorem card_support_cyc9 : ∀ a : Fin 3, (cyc9 a).support.card = 3 := by decide +kernel

theorem cyc9_isThreeCycle (a : Fin 3) : (cyc9 a).IsThreeCycle :=
  card_support_eq_three_iff.mp (card_support_cyc9 a)

theorem cyc9_cover : ∀ x : Fin 9, ∃ a : Fin 3, cyc9 a x ≠ x := by decide +kernel

theorem cyc9_pow_facts : ∀ (a b : Fin 3) (k l : ZMod 3), k ≠ 0 → l ≠ 0 →
    (cyc9 a ^ k.val).support.card = 3 ∧
      (a ≠ b → ∀ x : Fin 9, (cyc9 a ^ k.val) x = x ∨ (cyc9 b ^ l.val) x = x) := by
  decide +kernel

theorem cycleType_vecPerm_nine (v : Fin 3 → ZMod 3) (hv : ∀ s, v s ≠ 0) :
    (vecPerm 9 v).cycleType = {3, 3, 3} := by
  have h3 : ∀ a : Fin 3, (cyc9 a ^ (v a).val).cycleType = {3} := fun a =>
    (card_support_eq_three_iff.mp (cyc9_pow_facts a a (v a) (v a) (hv a) (hv a)).1).cycleType
  have hd : ∀ a b : Fin 3, a ≠ b → (cyc9 a ^ (v a).val).Disjoint (cyc9 b ^ (v b).val) :=
    fun a b hab => (cyc9_pow_facts a b (v a) (v b) (hv a) (hv b)).2 hab
  have e : vecPerm 9 v = cyc9 0 ^ (v 0).val * cyc9 1 ^ (v 1).val * cyc9 2 ^ (v 2).val := rfl
  rw [e, Disjoint.cycleType_mul ((hd 0 2 (by decide)).mul_left (hd 1 2 (by decide))),
    Disjoint.cycleType_mul (hd 0 1 (by decide)), h3, h3, h3]
  rfl

theorem card_centralizer_vecPerm_nine {v : Fin 3 → ZMod 3} (hv : ∀ s, v s ≠ 0) :
    Nat.card (centralizer {vecPerm 9 v}) = 162 := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_vecPerm_nine v hv]
  decide

theorem card_fix_cyc9 : ∀ a b : Fin 3, a ≠ b →
    (Finset.univ.filter fun x : Fin 9 => cyc9 a x = x ∧ cyc9 b x = x).card = 3 := by
  decide +kernel

theorem swap_mul_conj_cyc9 : ∀ a b : Fin 3, a ≠ b → ∀ p q : Fin 9, p ≠ q →
    cyc9 a p = p → cyc9 b p = p → cyc9 a q = q → cyc9 b q = q →
    ∃ r : Fin 3, (swap p q * (cyc9 r * swap p q * (cyc9 r)⁻¹)) ^ 3 = 1 ∧
      swap p q * (cyc9 r * swap p q * (cyc9 r)⁻¹) ≠ 1 := by
  decide +kernel

theorem coprime_orderOf_of_mem {G : Type*} [Group G] [Finite G] {Y : Subgroup G}
    (hY : Nat.Coprime (Nat.card Y) 3) {y : G} (hy : y ∈ Y) : Nat.Coprime (orderOf y) 3 := by
  have h := orderOf_dvd_natCard (⟨y, hy⟩ : Y)
  rw [Subgroup.orderOf_mk] at h
  exact Nat.Coprime.coprime_dvd_left h hY

theorem eq_bot_of_le_centralizer_fpf {Y : Subgroup (Perm (Fin 9))}
    (hY3 : Nat.Coprime (Nat.card Y) 3) (hYn : A0 9 ≤ normalizer (Y : Set (Perm (Fin 9))))
    {v : Fin 3 → ZMod 3} (hv : ∀ s, v s ≠ 0) (hYv : Y ≤ centralizer {vecPerm 9 v}) : Y = ⊥ := by
  have hdvd : Nat.card Y ∣ 162 := by
    rw [← card_centralizer_vecPerm_nine hv]
    exact Subgroup.card_dvd_of_le hYv
  have h2 : Nat.card Y ∣ 2 := by
    have hc : Nat.Coprime (Nat.card Y) 81 := Nat.Coprime.pow_right 4 hY3
    exact hc.dvd_of_dvd_mul_right (by simpa using hdvd)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    obtain ⟨⟨y, hyY⟩, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp h2'
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hcomm : ∀ a : Fin 3, y * cyc9 a = cyc9 a * y := by
      intro a
      have hmem : cyc9 a * y * (cyc9 a)⁻¹ ∈ Y :=
        (mem_normalizer_iff.mp (hYn (cyc9_mem_A0 a)) y).mp hyY
      have hne : (⟨cyc9 a * y * (cyc9 a)⁻¹, hmem⟩ : Y) ≠ 1 := by
        intro h
        apply hy1'
        have h' : cyc9 a * y * (cyc9 a)⁻¹ = 1 := congrArg Subtype.val h
        rw [mul_inv_eq_one, mul_eq_left] at h'
        exact h'
      obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp h2'
      have e1 := hz _ hne
      have e2 := hz _ hy1
      have e : cyc9 a * y * (cyc9 a)⁻¹ = y := congrArg Subtype.val (e1.trans e2.symm)
      calc y * cyc9 a = cyc9 a * y * (cyc9 a)⁻¹ * cyc9 a := by rw [e]
        _ = cyc9 a * y := by group
    have hy3 := coprime_orderOf_of_mem hY3 hyY
    apply hy1'
    refine Equiv.ext fun x => ?_
    obtain ⟨a, ha⟩ := cyc9_cover x
    rw [Perm.one_apply]
    exact apply_eq_self_of_commute_isThreeCycle (cyc9_isThreeCycle a) (hcomm a) hy3 ha

theorem eq_bot_of_le_centralizer_pair {Y : Subgroup (Perm (Fin 9))}
    (hY3 : Nat.Coprime (Nat.card Y) 3) (hYn : A0 9 ≤ normalizer (Y : Set (Perm (Fin 9))))
    {a b : Fin 3} (hab : a ≠ b) (hYa : Y ≤ centralizer {cyc9 a})
    (hYb : Y ≤ centralizer {cyc9 b}) : Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hyY
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hy3 := coprime_orderOf_of_mem hY3 hyY
  have hfa : ∀ x, cyc9 a x ≠ x → y x = x := fun x hx =>
    apply_eq_self_of_commute_isThreeCycle (cyc9_isThreeCycle a)
      (mem_centralizer_singleton_iff.mp (hYa hyY)) hy3 hx
  have hfb : ∀ x, cyc9 b x ≠ x → y x = x := fun x hx =>
    apply_eq_self_of_commute_isThreeCycle (cyc9_isThreeCycle b)
      (mem_centralizer_singleton_iff.mp (hYb hyY)) hy3 hx
  have hsupp : y.support ⊆ Finset.univ.filter fun x : Fin 9 => cyc9 a x = x ∧ cyc9 b x = x := by
    intro x hx
    rw [mem_support] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by_contra fun h => hx (hfa x h), by_contra fun h => hx (hfb x h)⟩
  have hcard : y.support.card ≤ 3 := (Finset.card_le_card hsupp).trans_eq (card_fix_cyc9 a b hab)
  have hne0 : y.support.card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, support_eq_empty_iff]
    exact hy1
  have hne1 := card_support_ne_one y
  rcases (by omega : y.support.card = 2 ∨ y.support.card = 3) with h2 | h3
  ·
    obtain ⟨p, q, hpq, rfl⟩ := card_support_eq_two.mp h2
    have hp : p ∈ (swap p q).support := by
      rw [mem_support, swap_apply_left]
      exact hpq.symm
    have hq : q ∈ (swap p q).support := by
      rw [mem_support, swap_apply_right]
      exact hpq
    have hp' := hsupp hp
    have hq' := hsupp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp' hq'
    obtain ⟨r, hr3, hr1⟩ := swap_mul_conj_cyc9 a b hab p q hpq hp'.1 hp'.2 hq'.1 hq'.2
    have hmem : swap p q * (cyc9 r * swap p q * (cyc9 r)⁻¹) ∈ Y :=
      mul_mem hyY ((mem_normalizer_iff.mp (hYn (cyc9_mem_A0 r)) _).mp hyY)
    have ho := coprime_orderOf_of_mem hY3 hmem
    rw [orderOf_eq_prime hr3 hr1] at ho
    exact absurd ho (by norm_num)
  ·
    have ho := (card_support_eq_three_iff.mp h3).orderOf
    rw [ho] at hy3
    exact absurd hy3 (by norm_num)

theorem vecPerm_nsmul {n : ℕ} [NeZero n] (hf : A0Facts n) (m : ℕ) (u : Fin 3 → ZMod 3) :
    vecPerm n (m • u) = vecPerm n u ^ m := by
  have h := map_pow (vecHom hf) (Multiplicative.ofAdd u) m
  rw [← ofAdd_nsmul] at h
  exact h

theorem vecPerm_smul_add {n : ℕ} [NeZero n] (hf : A0Facts n) (i j : ZMod 3)
    (u w : Fin 3 → ZMod 3) :
    vecPerm n (i • u + j • w) = vecPerm n u ^ i.val * vecPerm n w ^ j.val := by
  have hi : i • u = i.val • u := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  have hj : j • w = j.val • w := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [hi, hj, hf.add, vecPerm_nsmul hf, vecPerm_nsmul hf]

theorem eq_bot_of_A0_le_normalizer {X : Subgroup (Perm (Fin 9))} (hX : ¬ 3 ∣ Nat.card X)
    (hA : A0 9 ≤ normalizer (X : Set (Perm (Fin 9)))) : X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wFacts_nine.toA0Facts
  have hab := isElemAbelian_A0 hf
  have hX3 : Nat.Coprime 3 (Nat.card X) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hab
    (by rw [card_A0 hf]; norm_num) hA hX3 fun H hHA hH9 => ?_
  set Y := X ⊓ centralizer (H : Set (Perm (Fin 9))) with hY
  have hY3 : Nat.Coprime (Nat.card Y) 3 := by
    refine Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) ?_
    exact Nat.coprime_comm.mp hX3
  have hYn : A0 9 ≤ normalizer (Y : Set (Perm (Fin 9))) := by
    refine (le_inf hA ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    refine le_trans ?_ (le_normalizer (H := centralizer (H : Set (Perm (Fin 9)))))
    intro a ha
    rw [mem_centralizer_iff]
    intro x hx
    exact commute_of_mem_A0 hf (hHA hx) ha
  have hH1 : H ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hH9
    norm_num at hH9
  obtain ⟨⟨x, hxH⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hzx : ¬ H ≤ zpowers x := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hH9, Nat.card_zpowers] at h1
    have h2 : orderOf x ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hab.2 x (hHA hxH)))
    omega
  obtain ⟨w, hwH, hwx⟩ : ∃ w ∈ H, w ∉ zpowers x := by
    by_contra hc
    push Not at hc
    exact hzx hc
  obtain ⟨u, rfl⟩ := (mem_A0 hf).mp (hHA hxH)
  obtain ⟨w', rfl⟩ := (mem_A0 hf).mp (hHA hwH)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx1' (by simp [vecPerm])
  have hw0 : ∀ k : ZMod 3, w' ≠ k • u := by
    rintro k rfl
    apply hwx
    rw [show k • u = k.val • u by rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val],
      vecPerm_nsmul hf]
    exact pow_mem (mem_zpowers _) _
  have hmemH : ∀ i j : ZMod 3, vecPerm 9 (i • u + j • w') ∈ H := fun i j => by
    rw [vecPerm_smul_add hf]
    exact mul_mem (pow_mem hxH _) (pow_mem hwH _)
  have hYH : ∀ z ∈ H, Y ≤ centralizer {z} := by
    intro z hz y hy
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 z hz).symm
  rcases hyperplane_cases u w' hu0 hw0 with ⟨i, j, hij⟩ | ⟨a, b, hab', ⟨i, j, hij⟩, ⟨i', j', hij'⟩⟩
  · rw [eq_bot_of_le_centralizer_fpf hY3 hYn hij (hYH _ (hmemH i j))]
  · have ha := hmemH i j
    have hb := hmemH i' j'
    rw [hij, ← cyc9_eq] at ha
    rw [hij', ← cyc9_eq] at hb
    rw [eq_bot_of_le_centralizer_pair hY3 hYn hab' (hYH _ ha) (hYH _ hb)]

end CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
