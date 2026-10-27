module

public import CFSG.RankThree.GF2n.Tim79a34BigM12
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2M12
public import CFSG.Quasithin.Background.SmithB45MatM12Cls
public import CFSG.Sporadic.Schreier.M12OrderTwelve
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf
import CFSG.Quasithin.Background.RonanF610Sylow

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Blueprint

section Certified


theorem m12_orderOf_ne_of_mem {m : ℕ} (hm : m ∈ [9, 15, 33, 55]) (g : ↥NativeSporadic.M12) :
    orderOf g ≠ m := by
  have hg : (g : Equiv.Perm (Fin 12)) ∈ CFSG.Sporadic.Schreier.m12Certificate.originalSubgroup := by
    rw [CFSG.Sporadic.Schreier.m12Certificate_originalSubgroup]
    exact g.2
  rw [← Subgroup.orderOf_coe]
  exact CFSG.Quasithin.B45Mat.M12.orderOf_ne_of_mem hg hm

theorem m12_sq_eq_one_of_commute {x a b : ↥NativeSporadic.M12} (ha : orderOf a = 5)
    (hb : orderOf b = 3) (hxa : Commute x a) (hxb : Commute x b) : x ^ 2 = 1 := by
  have hk : orderOf x ∣ 95040 := by
    rw [← CFSG.Sporadic.Mathieu.card_M12]
    exact orderOf_dvd_natCard x
  have hpos : 0 < orderOf x := by
    exact Nat.pos_of_ne_zero (fun h => by rw [h] at hk; simp at hk)
  have key : ∀ (p r : ℕ) (c : ↥NativeSporadic.M12), Commute x c → orderOf c = r →
      Nat.Coprime p r → p ∣ orderOf x → orderOf (x ^ (orderOf x / p) * c) = p * r := by
    intro p r c hxc hc hpr hp
    have hy : orderOf (x ^ (orderOf x / p)) = p := orderOf_pow_orderOf_div hpos.ne' hp
    have hyc : Commute (x ^ (orderOf x / p)) c := hxc.pow_left _
    rw [hyc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy, hc]; exact hpr), hy, hc]
  have h3 : ¬ 3 ∣ orderOf x := fun h => m12_orderOf_ne_of_mem (m := 15) (by simp) _
    (by rw [key 3 5 a hxa ha (by norm_num) h])
  have h5 : ¬ 5 ∣ orderOf x := fun h => m12_orderOf_ne_of_mem (m := 15) (by simp) _
    (by rw [key 5 3 b hxb hb (by norm_num) h])
  have h11 : ¬ 11 ∣ orderOf x := fun h => m12_orderOf_ne_of_mem (m := 33) (by simp) _
    (by rw [key 11 3 b hxb hb (by norm_num) h])
  have h4 : ¬ 4 ∣ orderOf x := fun h => CFSG.Sporadic.Schreier.m12_no_order_twelve _
    (by rw [key 4 3 b hxb hb (by norm_num) h])
  have hcop : Nat.Coprime (orderOf x) 1485 := by
    have e : (1485 : ℕ) = 3 ^ 3 * (5 * 11) := by norm_num
    rw [e]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) (Nat.Coprime.mul_right ?_ ?_)
    · exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h3 |>.symm
    · exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5 |>.symm
    · exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h11 |>.symm
  have h64 : orderOf x ∣ 64 := hcop.dvd_of_dvd_mul_right (by simpa using hk)
  have hle : orderOf x ≤ 64 := Nat.le_of_dvd (by norm_num) h64
  have h2 : orderOf x ∣ 2 := by
    interval_cases h : orderOf x <;> omega
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem closure_sq_comm_of_pairwise {G : Type*} [Group G] {T : Set G}
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT2 : ∀ x ∈ T, x * x = 1) :
    ∀ a ∈ Subgroup.closure T, a * a = 1 ∧ ∀ b ∈ Subgroup.closure T, a * b = b * a := by
  have h1 : ∀ t ∈ T, Subgroup.closure T ≤ Subgroup.centralizer {t} := fun t ht =>
    (Subgroup.closure_le _).2 fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hT x hx t ht)
  have h2 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure T : Set G) :=
    (Subgroup.closure_le _).2 fun t ht => Subgroup.mem_centralizer_iff.2 fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.1 (h1 t ht hg)
  have hcomm : ∀ a ∈ Subgroup.closure T, ∀ b ∈ Subgroup.closure T, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.1 (h2 ha) b hb).symm
  intro a ha
  refine ⟨?_, hcomm a ha⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hT2 x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : x * y * (x * y) = x * x * (y * y) := by
      rw [mul_assoc, ← mul_assoc y x y, ← hcomm x hx y hy]; group
    rw [e, ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem m12A5CentralizerStatement_holds : M12A5CentralizerStatement := by
  classical
  intro R' hcard hperf
  set C := Subgroup.centralizer (R' : Set ↥NativeSporadic.M12) with hCdef
  haveI hP : Group.IsPerfect ↥R' := ⟨hperf⟩
  haveI hS : IsSimpleGroup ↥R' :=
    CFSG.Quasithin.A312J2.isSimpleGroup_of_perfect_card_sixty hP hcard
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥R') 5 (by rw [hcard]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥R') 3 (by rw [hcard]; norm_num)
  have ha' : orderOf (a : ↥NativeSporadic.M12) = 5 := by rw [Subgroup.orderOf_coe, ha]
  have hb' : orderOf (b : ↥NativeSporadic.M12) = 3 := by rw [Subgroup.orderOf_coe, hb]
  have hC2 : ∀ x ∈ C, x * x = 1 := by
    intro x hx
    have hxr : ∀ r ∈ R', x * r = r * x := fun r hr =>
      (Subgroup.mem_centralizer_iff.1 hx r hr).symm
    have := m12_sq_eq_one_of_commute ha' hb' (hxr _ a.2) (hxr _ b.2)
    rwa [pow_two] at this
  haveI : Nontrivial ↥R' := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have hcen : ∀ r ∈ R', (∀ r' ∈ R', r * r' = r' * r) → r = 1 := by
    intro r hr hcomm
    have hz : (⟨r, hr⟩ : ↥R') ∈ Subgroup.center ↥R' :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm g g.2).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥R') with h | h
    · rw [h, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    · exfalso
      have hmem : ∀ g : ↥R', g ∈ Subgroup.center ↥R' := fun g => by
        rw [h]; exact Subgroup.mem_top g
      haveI : IsMulCommutative ↥R' := ⟨⟨fun g g' => Subgroup.mem_center_iff.1 (hmem g') g⟩⟩
      exact Group.IsPerfect.not_isMulCommutative ↥R' inferInstance
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R') := inferInstance
  have hScard : Nat.card ↥(S : Subgroup ↥R') = 4 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 S.isPGroup'
    have hmul := (S : Subgroup ↥R').card_mul_index
    have hnd := S.not_dvd_index
    rw [hk, hcard] at hmul
    have hpos : 0 < (S : Subgroup ↥R').index := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0] at hmul; omega)
    have hk60 : 2 ^ k ≤ 60 := by
      calc 2 ^ k ≤ 2 ^ k * (S : Subgroup ↥R').index := Nat.le_mul_of_pos_right _ hpos
        _ = 60 := hmul
    have hk6 : k < 6 := by
      by_contra hk6
      have h64 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h64
      omega
    rw [hk]
    interval_cases k <;> norm_num at hmul ⊢ <;> omega
  have hSnc : ¬ IsCyclic ↥(S : Subgroup ↥R') :=
    CFSG.Quasithin.RonanF610.not_isCyclic_sylow_two_of_isPerfect hP S (by rw [hScard]; norm_num)
  have hS2 : ∀ s : ↥(S : Subgroup ↥R'), s * s = 1 := by
    intro s
    have hd : orderOf s ∣ 4 := hScard ▸ orderOf_dvd_natCard s
    have hne : orderOf s ≠ 4 := fun h4 =>
      hSnc (isCyclic_of_orderOf_eq_card s (by rw [h4, hScard]))
    have h2 : orderOf s ∣ 2 := by
      have hle : orderOf s ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      interval_cases h : orderOf s <;> omega
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have hsq_comm : ∀ {H : Type} [Group H] (x y : H), x * x = 1 → y * y = 1 →
      x * y * (x * y) = 1 → x * y = y * x := by
    intro H _ x y hx hy hxy
    calc x * y = x * (x * y * (x * y)) * y := by rw [hxy, mul_one]
      _ = (x * x) * y * x * (y * y) := by group
      _ = y * x := by rw [hx, hy, one_mul, mul_one]
  have hScomm' : ∀ s t : ↥(S : Subgroup ↥R'),
      ((s : ↥R') : ↥NativeSporadic.M12) * ((t : ↥R') : ↥NativeSporadic.M12) =
        ((t : ↥R') : ↥NativeSporadic.M12) * ((s : ↥R') : ↥NativeSporadic.M12) := fun s t =>
    congrArg (fun z : ↥(S : Subgroup ↥R') => ((z : ↥R') : ↥NativeSporadic.M12))
      (hsq_comm s t (hS2 s) (hS2 t) (hS2 (s * t)))
  let T : Set ↥NativeSporadic.M12 :=
    Set.range (fun s : ↥(S : Subgroup ↥R') => ((s : ↥R') : ↥NativeSporadic.M12)) ∪ (C : Set _)
  have hTS : ∀ s : ↥(S : Subgroup ↥R'), ((s : ↥R') : ↥NativeSporadic.M12) ∈ T :=
    fun s => Or.inl ⟨s, rfl⟩
  have hTC : ∀ c ∈ C, c ∈ T := fun c hc => Or.inr hc
  have hpair : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro x (⟨s, rfl⟩ | hx) y (⟨t, rfl⟩ | hy)
    · have h := hScomm' s t
      exact h
    · exact Subgroup.mem_centralizer_iff.1 hy _ (s : ↥R').2
    · exact (Subgroup.mem_centralizer_iff.1 hx _ (t : ↥R').2).symm
    · exact hsq_comm x y (hC2 x hx) (hC2 y hy) (hC2 _ (C.mul_mem hx hy))
  have hT2 : ∀ x ∈ T, x * x = 1 := by
    rintro x (⟨s, rfl⟩ | hx)
    · exact congrArg (fun z : ↥(S : Subgroup ↥R') => ((z : ↥R') : ↥NativeSporadic.M12)) (hS2 s)
    · exact hC2 x hx
  have hE := closure_sq_comm_of_pairwise hpair hT2
  have hE8 : Nat.card ↥(Subgroup.closure T) ≤ 8 :=
    CFSG.GH74.GLS.C3.Layer1.Bk.M12.m12_rank_le_three (Q := ↥NativeSporadic.M12)
      ⟨MulEquiv.refl _⟩ (Subgroup.closure T) hE
  let φ : ↥(S : Subgroup ↥R') × ↥C → ↥(Subgroup.closure T) := fun p =>
    ⟨((p.1 : ↥R') : ↥NativeSporadic.M12) * (p.2 : ↥NativeSporadic.M12),
      (Subgroup.closure T).mul_mem (Subgroup.subset_closure (hTS p.1))
        (Subgroup.subset_closure (hTC _ p.2.2))⟩
  have hφ : Function.Injective φ := by
    rintro ⟨s, c⟩ ⟨s', c'⟩ h
    have h' : ((s : ↥R') : ↥NativeSporadic.M12) * (c : ↥NativeSporadic.M12) =
        ((s' : ↥R') : ↥NativeSporadic.M12) * (c' : ↥NativeSporadic.M12) := congrArg Subtype.val h
    have hy1 : ((s' : ↥R') : ↥NativeSporadic.M12)⁻¹ * ((s : ↥R') : ↥NativeSporadic.M12) =
        (c' : ↥NativeSporadic.M12) * (c : ↥NativeSporadic.M12)⁻¹ := by
      calc ((s' : ↥R') : ↥NativeSporadic.M12)⁻¹ * ((s : ↥R') : ↥NativeSporadic.M12)
          = ((s' : ↥R') : ↥NativeSporadic.M12)⁻¹ *
              (((s : ↥R') : ↥NativeSporadic.M12) * (c : ↥NativeSporadic.M12)) *
              (c : ↥NativeSporadic.M12)⁻¹ := by group
        _ = ((s' : ↥R') : ↥NativeSporadic.M12)⁻¹ *
              (((s' : ↥R') : ↥NativeSporadic.M12) * (c' : ↥NativeSporadic.M12)) *
              (c : ↥NativeSporadic.M12)⁻¹ := by rw [h']
        _ = (c' : ↥NativeSporadic.M12) * (c : ↥NativeSporadic.M12)⁻¹ := by group
    have hyR : ((s' : ↥R') : ↥NativeSporadic.M12)⁻¹ * ((s : ↥R') : ↥NativeSporadic.M12) ∈ R' :=
      R'.mul_mem (R'.inv_mem (s' : ↥R').2) (s : ↥R').2
    have hyC : (c' : ↥NativeSporadic.M12) * (c : ↥NativeSporadic.M12)⁻¹ ∈ C :=
      C.mul_mem c'.2 (C.inv_mem c.2)
    have hy : ((s' : ↥R') : ↥NativeSporadic.M12)⁻¹ * ((s : ↥R') : ↥NativeSporadic.M12) = 1 :=
      hcen _ hyR fun r hr => by
        rw [hy1]
        exact (Subgroup.mem_centralizer_iff.1 hyC r hr).symm
    have hss : ((s : ↥R') : ↥NativeSporadic.M12) = ((s' : ↥R') : ↥NativeSporadic.M12) :=
      (inv_mul_eq_one.mp hy).symm
    have hcc : (c : ↥NativeSporadic.M12) = (c' : ↥NativeSporadic.M12) :=
      (mul_inv_eq_one.mp (hy1 ▸ hy)).symm
    exact Prod.ext (Subtype.ext (Subtype.ext hss)) (Subtype.ext hcc)
  have hle : Nat.card ↥(S : Subgroup ↥R') * Nat.card ↥C ≤ 8 := by
    rw [← Nat.card_prod]
    exact (Nat.card_le_card_of_injective φ hφ).trans hE8
  rw [hScard] at hle
  show Nat.card ↥C ≤ 2
  omega

end Certified

end CFSG.RankThree.GF2n.Tim79a
