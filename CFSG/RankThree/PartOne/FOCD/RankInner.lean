module

public import CFSG.RankThree.PartOne.FOCD.Bridge

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo innerAut fixSub)

@[expose] def PRankLeTwo (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ R : Subgroup T, (∀ r ∈ R, r ^ p = 1) → (∀ r ∈ R, ∀ s ∈ R, r * s = s * r) →
    Nat.card R ≤ p ^ 2

@[expose] def InnerCompN (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  LocalRankLeTwo p T → ∀ b y : T, b ^ p = 1 → y ^ p = 1 → b * y = y * b →
    ∀ E : Subgroup T, IsComponentOf (Subgroup.centralizer ({b} : Set T)) E →
      y ∈ Subgroup.normalizer (E : Set T) → y ∈ E ⊔ Subgroup.centralizer (E : Set T)

theorem fieldInnerT_of_compN {p : ℕ} {T : Type} [Group T] [Finite T]
    (hcen : Subgroup.center T = ⊥) (hin : InnerCompN p T) (hout : OuterComp p T) :
    FieldInnerT p T := by
  intro hLR x β E hxp hβp hβx hβinn hE hxN hxnot hLie
  by_cases hβ : β ∈ innerAut T
  · obtain ⟨b, hb⟩ := hβ
    obtain ⟨hbp, hfix, hbx⟩ := inner_case hcen hb hβp hβx
    rw [hfix] at hE
    exact hxnot (hin hLR b x hbp hxp hbx E hE hxN)
  · exact hxnot (Subgroup.mem_sup_left (hout hLR β hβp hβ (hβinn hβ) x hβx hxp E hE))

section Closure

variable {T : Type} [Group T]

theorem commute_of_mem_closure {S : Set T} (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ r ∈ Subgroup.closure S, ∀ s ∈ Subgroup.closure S, r * s = s * r := by
  have h1 : S ⊆ (Subgroup.centralizer S : Set T) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (h b hb a ha)
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 h1
  intro r hr s hs
  have := h2 hr
  rw [← Subgroup.centralizer_closure] at this
  exact (Subgroup.mem_centralizer_iff.1 this s hs).symm

theorem pow_eq_one_of_mem_closure {S : Set T} {n : ℕ} (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hS : ∀ a ∈ S, a ^ n = 1) : ∀ r ∈ Subgroup.closure S, r ^ n = 1 := by
  have hc := commute_of_mem_closure h
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow n
  | mul x y hx hy hx1 hy1 =>
    rw [(Commute.mul_pow (show Commute x y from (hc x hx y hy)))]
    simp [hx1, hy1]
  | inv x hx hx1 => rw [inv_pow, hx1, inv_one]

theorem p_mul_card_le_of_not_mem {p : ℕ} (hp : p.Prime) {H K : Subgroup T} [Finite K]
    (hHK : H ≤ K) (hK : IsPGroup p K) {x : T} (hxK : x ∈ K) (hxH : x ∉ H) :
    p * Nat.card H ≤ Nat.card K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hK
  have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK
  rw [hn] at hdvd
  obtain ⟨l, hl, hlH⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hne : Nat.card H ≠ Nat.card K := by
    intro heq
    have := Subgroup.eq_of_le_of_card_ge hHK (le_of_eq heq.symm)
    exact hxH (this ▸ hxK)
  have hln : l < n := by
    rcases Nat.lt_or_ge l n with h | h
    · exact h
    · exfalso
      have : l = n := le_antisymm hl h
      rw [hn, hlH, this] at hne
      exact hne rfl
  rw [hn, hlH]
  calc p * p ^ l = p ^ (l + 1) := by ring
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hln

end Closure

section Rank

variable {p : ℕ} {T : Type} [Group T] [Finite T]

omit [Finite T] in
theorem isPGroup_closure {p : ℕ} (hp : p.Prime) {S : Set T}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hS : ∀ a ∈ S, a ^ p = 1) :
    IsPGroup p (Subgroup.closure S) := by
  have hpow := pow_eq_one_of_mem_closure h hS
  have : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    have := hpow g.1 g.2
    simpa using this))
  rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
  · exact ⟨0, by rw [h2]; simp⟩
  · exact ⟨1, by rw [h2]; simp⟩

theorem innerCompN_of_rank' [IsSimpleGroup T] (hp : p.Prime) (hA : PRankLeTwo p T)
    (hB : ∀ b : T, b ≠ 1 → b ^ p = 1 → ∀ E : Subgroup T,
      IsComponentOf (Subgroup.centralizer ({b} : Set T)) E →
        (∀ z ∈ E ⊓ Subgroup.centralizer (E : Set T), z ^ p = 1 → z = 1) ∧ p ∣ Nat.card E) :
    InnerCompN p T := by
  classical
  intro _ b y hbp hyp hby E hE hyN
  by_cases hb1 : b = 1
  · subst hb1
    rw [centralizer_one_eq_top] at hE
    have hs : IsSimpleGroup ↥(⊤ : Subgroup T) := Subgroup.topEquiv.isSimpleGroup
    have hEtop : E = ⊤ := @eq_of_isComponentOf_simple T _ ⊤ E hs hE
    rw [hEtop]
    exact Subgroup.mem_sup_left (Subgroup.mem_top y)
  obtain ⟨hEZ, hpE⟩ := hB b hb1 hbp E hE
  by_contra hyE
  have : Fact p.Prime := ⟨hp⟩
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hbE : ∀ e ∈ E, b * e = e * b := fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hE.1 he)).symm
  have hbC : b ∈ Subgroup.centralizer (E : Set T) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hbE e he).symm
  have hyb : y ∉ Subgroup.zpowers b := fun h =>
    hyE (Subgroup.mem_sup_right ((Subgroup.zpowers_le.2 hbC) h))
  have hynorm : ∀ h : T, h ∈ E ↔ y * h * y⁻¹ ∈ E := Subgroup.mem_normalizer_iff.1 hyN
  have : Fintype E := Fintype.ofFinite E
  let f : Function.End ↥E := fun e => ⟨y * (e : T) * y⁻¹, (hynorm e).1 e.2⟩
  have hfpow : ∀ (n : ℕ) (e : ↥E), (((f ^ n) e : ↥E) : T) = y ^ n * (e : T) * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro e; change (e : T) = y ^ 0 * (e : T) * (y ^ 0)⁻¹; simp
    | succ n ih =>
      intro e
      rw [pow_succ]
      change (((f ^ n) (f e) : ↥E) : T) = _
      rw [ih]
      change y ^ n * (y * (e : T) * y⁻¹) * (y ^ n)⁻¹ = y ^ (n + 1) * (e : T) * (y ^ (n + 1))⁻¹
      rw [pow_succ', mul_inv_rev]
      group
  have hf1 : f ^ p ^ 1 = 1 := by
    funext e
    apply Subtype.ext
    rw [pow_one]
    change (((f ^ p) e : ↥E) : T) = (e : T)
    rw [hfpow p e, hyp]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf1
  have hpcard : p ∣ Fintype.card E := by
    rw [← Nat.card_eq_fintype_card]
    exact hpE
  have hpfix : p ∣ Fintype.card (Function.fixedPoints f) :=
    (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hpcard)))
  let CE : Subgroup T := E ⊓ Subgroup.centralizer ({y} : Set T)
  have hCEcard : Nat.card CE = Fintype.card (Function.fixedPoints f) := by
    rw [← Nat.card_eq_fintype_card (α := (Function.fixedPoints f : Set ↥E))]
    refine Nat.card_congr ⟨fun z => ⟨⟨z.1, (Subgroup.mem_inf.1 z.2).1⟩, ?_⟩,
      fun e => ⟨(e.1 : T), Subgroup.mem_inf.2 ⟨e.1.2, ?_⟩⟩, ?_, ?_⟩
    · apply Subtype.ext
      have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 z.2).2
      change y * (z : T) * y⁻¹ = (z : T)
      calc y * (z : T) * y⁻¹ = ((z : T) * y) * y⁻¹ := by rw [h]
        _ = (z : T) := by group
    · have h : f e.1 = e.1 := e.2
      have h' : y * (e.1 : T) * y⁻¹ = (e.1 : T) := congrArg Subtype.val h
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (e.1 : T) * y = (y * (e.1 : T) * y⁻¹) * y := by rw [h']
        _ = y * (e.1 : T) := by group
    · intro z; rfl
    · intro e; rfl
  have hpCE : p ∣ Nat.card CE := hCEcard ▸ hpfix
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := CE) p hpCE
  set z' : T := (z : T) with hz'
  have hz'E : z' ∈ E := (Subgroup.mem_inf.1 z.2).1
  have hz'y : y * z' = z' * y :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 z.2).2).symm
  have hz'ord : orderOf z' = p := by
    rw [hz', Subgroup.orderOf_coe]
    exact hz
  have hz'p : z' ^ p = 1 := hz'ord ▸ pow_orderOf_eq_one z'
  have hz'b : b * z' = z' * b := hbE z' hz'E
  have h21 : y * b = b * y := hby.symm
  have h31 : z' * b = b * z' := hz'b.symm
  have h32 : z' * y = y * z' := hz'y.symm
  have hcomm₂ : ∀ a ∈ ({b, y} : Set T), ∀ c ∈ ({b, y} : Set T), a * c = c * a := by
    intro a ha c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> first | rfl | assumption
  have hpow₂ : ∀ a ∈ ({b, y} : Set T), a ^ p = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hbp
    · exact hyp
  have hcomm₃ : ∀ a ∈ ({b, y, z'} : Set T), ∀ c ∈ ({b, y, z'} : Set T), a * c = c * a := by
    intro a ha c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
    rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
      first | rfl | assumption
  have hpow₃ : ∀ a ∈ ({b, y, z'} : Set T), a ^ p = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hbp
    · exact hyp
    · exact hz'p
  set A₁ : Subgroup T := Subgroup.zpowers b with hA₁
  set A₂ : Subgroup T := Subgroup.closure {b, y} with hA₂
  set A₃ : Subgroup T := Subgroup.closure {b, y, z'} with hA₃
  have hA₁₂ : A₁ ≤ A₂ := by
    rw [hA₁, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hA₂₃ : A₂ ≤ A₃ := by
    rw [hA₂, Subgroup.closure_le]
    intro a ha
    exact Subgroup.subset_closure (by rcases ha with rfl | rfl <;> simp)
  have hyA₂ : y ∈ A₂ := Subgroup.subset_closure (by simp)
  have hz'A₃ : z' ∈ A₃ := Subgroup.subset_closure (by simp)
  have hP₂ : IsPGroup p A₂ := isPGroup_closure hp hcomm₂ hpow₂
  have hP₃ : IsPGroup p A₃ := isPGroup_closure hp hcomm₃ hpow₃
  have hcardA₁ : Nat.card A₁ = p := by rw [hA₁, Nat.card_zpowers, hbord]
  have h12 : p * p ≤ Nat.card A₂ := by
    have := p_mul_card_le_of_not_mem hp hA₁₂ hP₂ hyA₂ hyb
    rwa [hcardA₁] at this
  have hA₂le : Nat.card A₂ ≤ p ^ 2 :=
    hA (A₂) (fun r hr => pow_eq_one_of_mem_closure hcomm₂ hpow₂ r hr)
      (fun r hr s hs => commute_of_mem_closure hcomm₂ r hr s hs)
  have hA₂card : Nat.card A₂ = p ^ 2 := by nlinarith
  set N : Subgroup T := E ⊔ Subgroup.centralizer (E : Set T) with hN
  have hA₁N : A₁ ≤ A₂ ⊓ N := le_inf hA₁₂ ((Subgroup.zpowers_le.2 hbC).trans le_sup_right)
  have hyN' : y ∉ A₂ ⊓ N := fun h => hyE (Subgroup.mem_inf.1 h).2
  have hp₂N : p * Nat.card ↥(A₂ ⊓ N) ≤ Nat.card A₂ :=
    p_mul_card_le_of_not_mem hp (inf_le_left : A₂ ⊓ N ≤ A₂) hP₂ hyA₂ hyN'
  have hcardAN : Nat.card A₁ ≤ Nat.card ↥(A₂ ⊓ N) := Subgroup.card_le_of_le hA₁N
  have hAN : A₂ ⊓ N = A₁ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hA₁N ?_
    rw [hcardA₁]
    have : p * Nat.card ↥(A₂ ⊓ N) ≤ p * p := by rw [hA₂card] at hp₂N; nlinarith
    exact Nat.le_of_mul_le_mul_left this hp.pos
  have hz'A₂ : z' ∉ A₂ := by
    intro h
    have h1 : z' ∈ A₂ ⊓ N := Subgroup.mem_inf.2 ⟨h, Subgroup.mem_sup_left hz'E⟩
    rw [hAN] at h1
    have h2 : z' ∈ Subgroup.centralizer (E : Set T) := (Subgroup.zpowers_le.2 hbC) h1
    have h3 : z' ∈ E ⊓ Subgroup.centralizer (E : Set T) := Subgroup.mem_inf.2 ⟨hz'E, h2⟩
    have h4 := hEZ z' h3 hz'p
    rw [h4, orderOf_one] at hz'ord
    exact hp.one_lt.ne hz'ord
  have h23 : p * Nat.card A₂ ≤ Nat.card A₃ := p_mul_card_le_of_not_mem hp hA₂₃ hP₃ hz'A₃ hz'A₂
  have hA₃le : Nat.card A₃ ≤ p ^ 2 :=
    hA A₃ (fun r hr => pow_eq_one_of_mem_closure hcomm₃ hpow₃ r hr)
      (fun r hr s hs => commute_of_mem_closure hcomm₃ r hr s hs)
  rw [hA₂card] at h23
  have : p * p ^ 2 ≤ p ^ 2 := h23.trans hA₃le
  have hp2 : 2 ≤ p := hp.two_le
  nlinarith [pow_pos hp.pos 2]

theorem innerCompN_of_rank [IsSimpleGroup T] (hp : p.Prime) (hA : PRankLeTwo p T)
    (hB : ∀ b : T, b ≠ 1 → b ^ p = 1 → ∀ E : Subgroup T,
      IsComponentOf (Subgroup.centralizer ({b} : Set T)) E →
        E ⊓ Subgroup.centralizer (E : Set T) = ⊥ ∧ p ∣ Nat.card E) :
    InnerCompN p T := by
  refine innerCompN_of_rank' hp hA fun b hb1 hbp E hE => ?_
  obtain ⟨h1, h2⟩ := hB b hb1 hbp E hE
  refine ⟨fun z hz _ => ?_, h2⟩
  rw [h1] at hz
  exact Subgroup.mem_bot.1 hz

end Rank

end CFSG.RankThree.PartOne.FOCD
