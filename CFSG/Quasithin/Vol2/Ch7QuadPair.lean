module

public import CFSG.Quasithin.Background.A4Coprime
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace QuadPair

theorem conj_mul_inv_mem_of_relIndex_two {V B : Subgroup G} (hBV : B ≤ V)
    (hidx : B.relIndex V = 2) {y : G} (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hyB : y ∈ Subgroup.centralizer (B : Set G)) {v : G} (hv : v ∈ V) :
    y * v * y⁻¹ * v⁻¹ ∈ B := by
  have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
  have hidx' : (B.subgroupOf V).index = 2 := hidx
  have hiff := Subgroup.mul_mem_iff_of_index_two hidx' (a := (⟨y * v * y⁻¹, hyv⟩ : V))
    (b := (⟨v, hv⟩ : V)⁻¹)
  by_cases hvB : v ∈ B
  · have h1 : y * v * y⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.mp hyB v hvB
      rw [← this, mul_inv_cancel_right]
    rw [h1, mul_inv_cancel]
    exact B.one_mem
  · have h2 : y * v * y⁻¹ ∉ B := by
      intro h
      apply hvB
      have h3 := Subgroup.mem_centralizer_iff.mp hyB _ h
      have h4 : v = y⁻¹ * (y * v * y⁻¹) * y := by group
      rw [h4]
      have h5 : y⁻¹ * (y * v * y⁻¹) * y = y * v * y⁻¹ := by
        rw [mul_assoc, h3, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h5]
      exact h
    have hm : ((⟨y * v * y⁻¹, hyv⟩ : V) * (⟨v, hv⟩ : V)⁻¹ : V) ∈ B.subgroupOf V := by
      rw [hiff]
      constructor
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp h) h2
      · intro h
        exact absurd (by simpa [Subgroup.mem_subgroupOf] using h : v ∈ B) hvB
    exact Subgroup.mem_subgroupOf.mp hm

theorem mem_centralizer_sup_of {B B' : Subgroup G} {y : G}
    (hB : y ∈ Subgroup.centralizer (B : Set G)) (hB' : y ∈ Subgroup.centralizer (B' : Set G)) :
    y ∈ Subgroup.centralizer ((B ⊔ B' : Subgroup G) : Set G) := by
  have hle : B ⊔ B' ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hB b hb
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hB' b hb
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)

@[expose] def stabSeries (N B : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (N : Set G) ∧ x ∈ Subgroup.centralizer (B : Set G) ∧
    ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ B}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun n _ => by simp⟩
  mul_mem' := fun {x y} hx hy => by
    refine ⟨Subgroup.mul_mem _ hx.1 hy.1, Subgroup.mul_mem _ hx.2.1 hy.2.1, fun n hn => ?_⟩
    have h1 := hy.2.2 n hn
    have h2 := hx.2.2 n hn
    have h3 : x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ = y * n * y⁻¹ * n⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp hx.2.1 _ h1, mul_inv_cancel_right]
    have e : x * y * n * (x * y)⁻¹ * n⁻¹ =
        x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ * (x * n * x⁻¹ * n⁻¹) := by group
    rw [e, h3]
    exact B.mul_mem h1 h2
  inv_mem' := fun {x} hx => by
    refine ⟨Subgroup.inv_mem _ hx.1, Subgroup.inv_mem _ hx.2.1, fun n hn => ?_⟩
    have hm : x⁻¹ * n * x ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx.1) n).mp hn
      simpa using this
    have h1 := hx.2.2 _ hm
    have e : x⁻¹ * n * x⁻¹⁻¹ * n⁻¹ = (x * (x⁻¹ * n * x) * x⁻¹ * (x⁻¹ * n * x)⁻¹)⁻¹ := by group
    rw [e]
    exact B.inv_mem h1

theorem mem_stabSeries {N B : Subgroup G} {x : G} :
    x ∈ stabSeries N B ↔ x ∈ Subgroup.normalizer (N : Set G) ∧
      x ∈ Subgroup.centralizer (B : Set G) ∧ ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ B := Iff.rfl

theorem comm_mem_of_closure {N B : Subgroup G} {S : Set G} (hNS : N = Subgroup.closure S)
    (hBN : ∀ n ∈ N, n ∈ Subgroup.centralizer (B : Set G)) {x : G}
    (hS : ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ B) : ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ B := by
  subst hNS
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul n m hn hm ihn ihm =>
    have h1 : n * (x * m * x⁻¹ * m⁻¹) * n⁻¹ = x * m * x⁻¹ * m⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp (hBN n hn) _ ihm, mul_inv_cancel_right]
    have e : x * (n * m) * x⁻¹ * (n * m)⁻¹ =
        (x * n * x⁻¹ * n⁻¹) * (n * (x * m * x⁻¹ * m⁻¹) * n⁻¹) := by group
    rw [e, h1]
    exact B.mul_mem ihn ihm
  | inv n hn ihn =>
    have h1 : n⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ * n⁻¹⁻¹ = (x * n * x⁻¹ * n⁻¹)⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp (hBN n⁻¹ (Subgroup.inv_mem _ hn)) _
        (B.inv_mem ihn), mul_inv_cancel_right]
    have e : x * n⁻¹ * x⁻¹ * n⁻¹⁻¹ = n⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ * n⁻¹⁻¹ := by group
    rw [e, h1]
    exact B.inv_mem ihn

theorem mem_normalizer_bot (x : G) : x ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top x

theorem comm_eq_one_of_odd {B D : Subgroup G} (hBD : B ≤ D) (hD : IsPGroup 2 D) {y : G}
    (hy : Odd (orderOf y)) (h5 : ∀ d ∈ D, y * d * y⁻¹ * d⁻¹ ∈ B)
    (h6 : ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ = 1) : ∀ d ∈ D, y * d * y⁻¹ * d⁻¹ = 1 := by
  have h := A4.commutator_mem_of_series (N := ⊥) (B := B) (D := D) hy (mem_normalizer_bot y)
    (fun d _ => mem_normalizer_bot d) hBD
    (fun d hd => by
      obtain ⟨j, hj⟩ := hD ⟨d, hd⟩
      exact ⟨j, Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hj)⟩)
    h5 (fun b hb => Subgroup.mem_bot.mpr (h6 b hb))
  exact fun d hd => Subgroup.mem_bot.mp (h d hd)

end QuadPair

theorem isPGroup_sup_of_quadratic {V V' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV' : IsElemAbelian 2 V')
    (hA₁ : (V ⊓ Subgroup.normalizer (V' : Set G)).relIndex V = 2)
    (hA : (V' ⊓ Subgroup.normalizer (V : Set G)).relIndex V' = 2)
    (hq : ∀ v ∈ V, ∀ a ∈ V' ⊓ Subgroup.normalizer (V : Set G),
      a * v * a⁻¹ * v⁻¹ ∈ Subgroup.centralizer (V' : Set G))
    (hq' : ∀ v ∈ V', ∀ a ∈ V ⊓ Subgroup.normalizer (V' : Set G),
      a * v * a⁻¹ * v⁻¹ ∈ Subgroup.centralizer (V : Set G))
    (hr : Subgroup.centralizer ((V ⊓ Subgroup.normalizer (V' : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V : Set G))
    (hr' : Subgroup.centralizer ((V' ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V' : Set G)) :
    IsPGroup 2 ↥(V ⊔ V') := by
  set A := V' ⊓ Subgroup.normalizer (V : Set G) with hAdef
  set A₁ := V ⊓ Subgroup.normalizer (V' : Set G) with hA₁def
  set U := V ⊓ Subgroup.centralizer (V' : Set G) with hUdef
  set U₁ := V' ⊓ Subgroup.centralizer (V : Set G) with hU₁def
  set N := A ⊔ A₁ with hNdef
  set B := U ⊔ U₁ with hBdef
  have hcV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcV' : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV'.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsqV : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v hv
  have hsqV' : ∀ v ∈ V', v * v = 1 := fun v hv => by rw [← sq]; exact hV'.2 v hv
  have hpV : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hpV' : IsPGroup 2 V' := B2F.isPGroup_of_isElemAbelian hV'
  have hUA₁ : U ≤ A₁ := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hU₁A : U₁ ≤ A := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hBN : B ≤ N := sup_le (hUA₁.trans le_sup_right) (hU₁A.trans le_sup_left)
  have hAA₁ : A ≤ Subgroup.normalizer (A₁ : Set G) := by
    intro a ha
    have haN := ha.2
    have haN' : a ∈ Subgroup.normalizer (V' : Set G) := Subgroup.le_normalizer ha.1
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact ⟨(Subgroup.mem_normalizer_iff.mp haN w).mp hw.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ haN' hw.2) (Subgroup.inv_mem _ haN')⟩
    · intro hw
      have hw1 : w ∈ V := (Subgroup.mem_normalizer_iff.mp haN w).mpr hw.1
      have hw2 : w ∈ Subgroup.normalizer (V' : Set G) := by
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN') hw.2) haN'
        simpa [mul_assoc] using this
      exact ⟨hw1, hw2⟩
  have hpN : IsPGroup 2 N :=
    IsPGroup.to_sup_of_normal_right' (hpV'.to_le inf_le_left) (hpV.to_le inf_le_left) hAA₁
  have hNB : ∀ n ∈ N, n ∈ Subgroup.centralizer (B : Set G) := by
    have hle : N ≤ Subgroup.centralizer (B : Set G) := by
      refine sup_le (fun a ha => QuadPair.mem_centralizer_sup_of ?_ ?_)
        (fun a ha => QuadPair.mem_centralizer_sup_of ?_ ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (Subgroup.mem_centralizer_iff.mp hu.2 a ha.1).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact hcV' u hu.1 a ha.1
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact hcV u hu.1 a ha.1
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (Subgroup.mem_centralizer_iff.mp hu.2 a ha.1).symm
    exact fun n hn => hle hn
  have hgen : ∀ x : G, x * x = 1 → x ∈ Subgroup.centralizer (B : Set G) →
      (∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ B) → x ∈ QuadPair.stabSeries N B := by
    intro x hxx hxB hxN
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
    have hconj : ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun n hn => by
      have := N.mul_mem (hBN (hxN n hn)) hn
      simpa [mul_assoc] using this
    refine QuadPair.mem_stabSeries.mpr ⟨?_, hxB, hxN⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hconj n, fun h => ?_⟩
    have := hconj _ h
    rwa [hxinv, ← mul_assoc, ← mul_assoc, hxx, one_mul, mul_assoc, hxx, mul_one] at this
  have hsupN : N = Subgroup.closure ((A : Set G) ∪ (A₁ : Set G)) := Subgroup.sup_eq_closure A A₁
  have hVS : V ≤ QuadPair.stabSeries N B := by
    intro v hv
    refine hgen v (hsqV v hv) (QuadPair.mem_centralizer_sup_of ?_ ?_)
      (QuadPair.comm_mem_of_closure hsupN hNB ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hcV u hu.1 v hv
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp hu.2 v hv).symm
    · rintro s (hs | hs)
      ·
        have h1 := hq v hv s hs
        have h2 : s * v * s⁻¹ * v⁻¹ ∈ V :=
          V.mul_mem ((Subgroup.mem_normalizer_iff.mp hs.2 v).mp hv) (V.inv_mem hv)
        have e : v * s * v⁻¹ * s⁻¹ = (s * v * s⁻¹ * v⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.mem_sup_left (U.inv_mem ⟨h2, h1⟩)
      · have e : v * s * v⁻¹ * s⁻¹ = 1 := by
          rw [hcV v hv s hs.1, mul_inv_cancel_right, mul_inv_cancel]
        rw [e]
        exact B.one_mem
  have hV'S : V' ≤ QuadPair.stabSeries N B := by
    intro v hv
    refine hgen v (hsqV' v hv) (QuadPair.mem_centralizer_sup_of ?_ ?_)
      (QuadPair.comm_mem_of_closure hsupN hNB ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp hu.2 v hv).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hcV' u hu.1 v hv
    · rintro s (hs | hs)
      · have e : v * s * v⁻¹ * s⁻¹ = 1 := by
          rw [hcV' v hv s hs.1, mul_inv_cancel_right, mul_inv_cancel]
        rw [e]
        exact B.one_mem
      · have h1 := hq' v hv s hs
        have h2 : s * v * s⁻¹ * v⁻¹ ∈ V' :=
          V'.mul_mem ((Subgroup.mem_normalizer_iff.mp hs.2 v).mp hv) (V'.inv_mem hv)
        have e : v * s * v⁻¹ * s⁻¹ = (s * v * s⁻¹ * v⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.mem_sup_right (U₁.inv_mem ⟨h2, h1⟩)
  have hXS : V ⊔ V' ≤ QuadPair.stabSeries N B := sup_le hVS hV'S
  have hodd : ∀ y ∈ V ⊔ V', Odd (orderOf y) →
      y ∈ Subgroup.centralizer (V : Set G) ∧ y ∈ Subgroup.centralizer (V' : Set G) := by
    intro y hyX hyo
    obtain ⟨-, hyB, hyN⟩ := QuadPair.mem_stabSeries.mp (hXS hyX)
    have hyN' := QuadPair.comm_eq_one_of_odd hBN hpN hyo hyN fun b hb => by
      rw [← Subgroup.mem_centralizer_iff.mp hyB b hb, mul_inv_cancel_right, mul_inv_cancel]
    have hcen : ∀ {K : Subgroup G}, K ≤ N → y ∈ Subgroup.centralizer (K : Set G) := by
      intro K hKN
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := hyN' k (hKN hk)
      have : y * k * y⁻¹ = k := by rw [← mul_inv_eq_one]; exact h
      calc k * y = y * k * y⁻¹ * y := by rw [this]
        _ = y * k := by group
    have hyA₁ := hcen (le_sup_right : A₁ ≤ N)
    have hyA := hcen (le_sup_left : A ≤ N)
    have hyV := hr hyA₁
    have hyV' := hr' hyA
    have h1 := QuadPair.comm_eq_one_of_odd inf_le_left hpV hyo
      (fun v hv => QuadPair.conj_mul_inv_mem_of_relIndex_two inf_le_left hA₁ hyV hyA₁ hv)
      (fun b hb => by
        rw [← Subgroup.mem_centralizer_iff.mp hyA₁ b hb, mul_inv_cancel_right, mul_inv_cancel])
    have h2 := QuadPair.comm_eq_one_of_odd inf_le_left hpV' hyo
      (fun v hv => QuadPair.conj_mul_inv_mem_of_relIndex_two inf_le_left hA hyV' hyA hv)
      (fun b hb => by
        rw [← Subgroup.mem_centralizer_iff.mp hyA b hb, mul_inv_cancel_right, mul_inv_cancel])
    have hfin : ∀ {K : Subgroup G}, (∀ d ∈ K, y * d * y⁻¹ * d⁻¹ = 1) →
        y ∈ Subgroup.centralizer (K : Set G) := by
      intro K hK
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have : y * k * y⁻¹ = k := by rw [← mul_inv_eq_one]; exact hK k hk
      calc k * y = y * k * y⁻¹ * y := by rw [this]
        _ = y * k := by group
    exact ⟨hfin h1, hfin h2⟩
  obtain ⟨b, hbV, hbA₁⟩ : ∃ b ∈ V, b ∉ A₁ := by
    by_contra h
    push Not at h
    have : A₁.relIndex V = 1 := Subgroup.relIndex_eq_one.mpr fun x hx => h x hx
    omega
  obtain ⟨a, haV', haA⟩ : ∃ a ∈ V', a ∉ A := by
    by_contra h
    push Not at h
    have : A.relIndex V' = 1 := Subgroup.relIndex_eq_one.mpr fun x hx => h x hx
    omega
  have hbb := hsqV b hbV
  have haa := hsqV' a haV'
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hbb
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left haa
  set c := b * a with hc
  have hcX : c ∈ V ⊔ V' :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hbV) (Subgroup.mem_sup_right haV')
  have hbc : b * c * b⁻¹ = c⁻¹ := by
    rw [hc, mul_inv_rev, hbinv, hainv, ← mul_assoc, hbb, one_mul]
  obtain ⟨e, m, hm, hce⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  set y := c ^ 2 ^ e with hy
  have hyX : y ∈ V ⊔ V' := Subgroup.pow_mem _ hcX _
  have hyo : Odd (orderOf y) := by
    have hdvd : orderOf y ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hy, ← pow_mul, ← hce, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat hm hdvd
  have hy1 : y = 1 := by
    have hyb : b * y * b⁻¹ = y := by
      have h := Subgroup.mem_centralizer_iff.mp (hodd y hyX hyo).1 b hbV
      rw [h, mul_inv_cancel_right]
    have hyb' : b * y * b⁻¹ = y⁻¹ := by
      rw [hy, ← conj_pow, hbc, inv_pow]
    have hyy : y * y = 1 := by
      have h := hyb.symm.trans hyb'
      rw [eq_inv_iff_mul_eq_one] at h
      exact h
    have hdvd2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hyy)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hyo
      exact absurd hyo (by decide)
  have hpc : IsPGroup 2 (Subgroup.zpowers c) := by
    have hdvd : orderOf c ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (by rw [← hy]; exact hy1)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hpb : IsPGroup 2 (Subgroup.zpowers b) := by
    have hdvd : orderOf b ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hbb)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    have hfwd : ∀ h ∈ Subgroup.zpowers c, b * h * b⁻¹ ∈ Subgroup.zpowers c := by
      rintro _ ⟨k, rfl⟩
      refine ⟨-k, ?_⟩
      change c ^ (-k) = b * c ^ k * b⁻¹
      rw [← conj_zpow, hbc, inv_zpow']
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have := hfwd _ hh
    rwa [hbinv, ← mul_assoc, ← mul_assoc, hbb, one_mul, mul_assoc, hbb, mul_one] at this
  have hpD : IsPGroup 2 ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers b) :=
    IsPGroup.to_sup_of_normal_left' hpc hpb (Subgroup.zpowers_le.mpr hbN)
  have hDX : Subgroup.zpowers c ⊔ Subgroup.zpowers b ≤ V ⊔ V' :=
    sup_le (Subgroup.zpowers_le.mpr hcX) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hbV))
  have hpND : IsPGroup 2 ↥(N ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers b)) :=
    IsPGroup.to_sup_of_normal_left' hpN hpD fun d hd =>
      (QuadPair.mem_stabSeries.mp (hXS (hDX hd))).1
  refine hpND.to_le (sup_le ?_ ?_)
  · intro v hv
    by_cases hvA₁ : v ∈ A₁
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hvA₁)
    · have hidx : (A₁.subgroupOf V).index = 2 := hA₁
      have hvb : v * b⁻¹ ∈ A₁ := by
        have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨v, hv⟩ : V))
          (b := (⟨b, hbV⟩ : V)⁻¹)).mpr (by
            constructor
            · intro h'; exact absurd h' hvA₁
            · intro h'; exact absurd (by simpa [Subgroup.mem_subgroupOf] using h' : b ∈ A₁) hbA₁)
        exact h
      have e : v = v * b⁻¹ * b := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hvb))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))
  · intro v hv
    have haD : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b := by
      have e : a = b⁻¹ * c := by rw [hc, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    by_cases hvA : v ∈ A
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hvA)
    · have hidx : (A.subgroupOf V').index = 2 := hA
      have hva : v * a⁻¹ ∈ A := by
        have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨v, hv⟩ : V'))
          (b := (⟨a, haV'⟩ : V')⁻¹)).mpr (by
            constructor
            · intro h'; exact absurd h' hvA
            · intro h'; exact absurd (by simpa [Subgroup.mem_subgroupOf] using h' : a ∈ A) haA)
        exact h
      have e : v = v * a⁻¹ * a := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hva))
        (Subgroup.mem_sup_right haD)

end CFSG.Quasithin.H13
