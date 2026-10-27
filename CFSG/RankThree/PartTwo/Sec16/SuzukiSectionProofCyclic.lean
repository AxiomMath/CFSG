module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.Data.Nat.Choose.Dvd
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Subgroup
open scoped commutatorElement

universe u

section ClassTwo

variable {T : Type*} [Group T]

theorem mul_pow_eq_of_central' {x y c : T} (hc : ∀ g : T, g * c = c * g)
    (hyx : y * x = c * x * y) (n : ℕ) : y * x ^ n = c ^ n * x ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y * x ^ (n + 1) = (y * x ^ n) * x := by rw [pow_succ, mul_assoc]
      _ = c ^ n * x ^ n * (y * x) := by rw [ih, mul_assoc]
      _ = c ^ n * (x ^ n * c) * x * y := by rw [hyx]; simp only [mul_assoc]
      _ = c ^ (n + 1) * x ^ (n + 1) * y := by
        rw [hc (x ^ n), pow_succ, pow_succ]; simp only [mul_assoc]

theorem mul_pow_eq_of_central {x y c : T} (hc : ∀ g : T, g * c = c * g)
    (hyx : y * x = c * x * y) (n : ℕ) : (x * y) ^ n = c ^ n.choose 2 * x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hC : ∀ g : T, g * c ^ n.choose 2 = c ^ n.choose 2 * g := fun g =>
      ((Commute.pow_right (hc g) _)).eq
    have hcn : ∀ g : T, g * c ^ n = c ^ n * g := fun g => ((Commute.pow_right (hc g) n)).eq
    have hch : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = x * (y * (x * y) ^ n) := by rw [pow_succ', mul_assoc]
      _ = x * (y * c ^ n.choose 2) * x ^ n * y ^ n := by rw [ih]; simp only [mul_assoc]
      _ = c ^ n.choose 2 * (x * (y * x ^ n)) * y ^ n := by
        rw [hC y, ← mul_assoc x, hC x]; simp only [mul_assoc]
      _ = c ^ n.choose 2 * (x * c ^ n) * x ^ n * (y * y ^ n) := by
        rw [mul_pow_eq_of_central' hc hyx n]; simp only [mul_assoc]
      _ = c ^ (n + 1).choose 2 * x ^ (n + 1) * y ^ (n + 1) := by
        rw [hcn x, hch, pow_add, pow_succ', pow_succ', (Commute.pow_pow (Commute.refl c) _ _).eq]
        simp only [mul_assoc]

end ClassTwo

section Cyclic

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem card_pow_eq_one_subgroup_le {T : Type*} [Group T] [Finite T] (H : Subgroup T) :
    Nat.card {x : H // x ^ p = 1} ≤ Nat.card {x : T // x ^ p = 1} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : T), by
    rw [← Subgroup.coe_pow, x.2, Subgroup.coe_one]⟩) ?_
  intro a b hab
  have h1 := congrArg Subtype.val hab
  simp only at h1
  exact Subtype.ext (Subtype.ext h1)

theorem isCyclic_of_card_pow_eq_one_le' (hp2 : p ≠ 2) (n : ℕ) :
    ∀ (T : Type u) [Group T] [Finite T], Nat.card T = n → IsPGroup p T →
      Nat.card {x : T // x ^ p = 1} ≤ p → IsCyclic T := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T _ _ hn hT hcard
  by_contra hnc
  have hsub : ∀ H : Subgroup T, H ≠ ⊤ → ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro H hH a ha b hb
    have hlt : Nat.card H < n := by
      rw [← hn]
      exact (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)).trans_eq Subgroup.card_top
    have : IsCyclic H := ih _ hlt H rfl (hT.to_subgroup H)
      ((card_pow_eq_one_subgroup_le H).trans hcard)
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := H)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnt : Nontrivial T := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnc isCyclic_of_subsingleton
  obtain ⟨M₁, hM₁, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup T)).resolve_left bot_ne_top
  obtain ⟨x, hx⟩ : ∃ x, x ∉ M₁ := by
    by_contra h
    push Not at h
    exact hM₁.1 (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨M₂, hM₂, hxM₂⟩ : ∃ M : Subgroup T, IsCoatom M ∧ zpowers x ≤ M := by
    rcases eq_top_or_exists_le_coatom (zpowers x) with h | h
    · exact absurd (show IsCyclic T from ⟨⟨x, fun y => mem_zpowers_iff.mp (by
        rw [h]; exact mem_top y)⟩⟩) hnc
    · exact h
  have hne : M₁ ≠ M₂ := fun h => hx (h ▸ hxM₂ (mem_zpowers x))
  obtain ⟨hN₁, hi₁⟩ := CFSG.SectionRank.Ccomm.normal_and_index_eq_of_isCoatom hT hM₁
  obtain ⟨hN₂, hi₂⟩ := CFSG.SectionRank.Ccomm.normal_and_index_eq_of_isCoatom hT hM₂
  have hM₂₁ : ¬ M₂ ≤ M₁ := by
    intro h
    rcases lt_or_eq_of_le h with h | h
    · exact hM₁.1 (hM₂.2 M₁ h)
    · exact hne h.symm
  have hM₁₂ : ¬ M₁ ≤ M₂ := by
    intro h
    rcases lt_or_eq_of_le h with h | h
    · exact hM₂.1 (hM₁.2 M₂ h)
    · exact hne h
  have hsup : M₁ ⊔ M₂ = ⊤ :=
    hM₁.2 _ (lt_of_le_of_ne le_sup_left fun h => hM₂₁ (by rw [h]; exact le_sup_right))
  have hZ : ∀ z ∈ M₁ ⊓ M₂, ∀ g : T, g * z = z * g := by
    intro z hz g
    have hle : M₁ ⊔ M₂ ≤ centralizer ({z} : Set T) := sup_le
      (fun m hm => mem_centralizer_singleton_iff.mpr (hsub M₁ hM₁.1 _ hm _ hz.1))
      (fun m hm => mem_centralizer_singleton_iff.mpr (hsub M₂ hM₂.1 _ hm _ hz.2))
    rw [hsup] at hle
    exact mem_centralizer_singleton_iff.mp (hle (mem_top g))
  have hquot : ∀ M : Subgroup T, M.Normal → M.index = p →
      (∀ a b : T, ⁅a, b⁆ ∈ M) ∧ ∀ a : T, a ^ p ∈ M := by
    intro M hM hi
    have hcardQ : Nat.card (T ⧸ M) = p := by rw [← Subgroup.index, hi]
    have : IsCyclic (T ⧸ M) := isCyclic_of_prime_card hcardQ
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' M ⁅a, b⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (IsCyclic.commGroup (α := T ⧸ M)).mul_comm _ _
    · rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' M (a ^ p) = 1
      rw [map_pow, ← hcardQ]
      exact pow_card_eq_one'
  obtain ⟨hc₁, hp₁⟩ := hquot M₁ hN₁ hi₁
  obtain ⟨hc₂, hp₂⟩ := hquot M₂ hN₂ hi₂
  have hpow : ∀ a b : T, (a * b) ^ p = a ^ p * b ^ p := by
    intro a b
    set c := ⁅b, a⁆ with hcdef
    have hc : ∀ g : T, g * c = c * g := hZ c ⟨hc₁ b a, hc₂ b a⟩
    have hba : b * a = c * a * b := by rw [hcdef, commutatorElement_def]; group
    have hcp : c ^ p = 1 := by
      have h1 := mul_pow_eq_of_central' hc hba p
      have h2 : b * a ^ p = a ^ p * b := hZ _ ⟨hp₁ a, hp₂ a⟩ b
      rw [h2] at h1
      have h3 : a ^ p * b = c ^ p * (a ^ p * b) := by rw [← mul_assoc]; exact h1
      exact right_eq_mul.mp h3
    have h2p : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
    obtain ⟨k, hk⟩ := hp.out.dvd_choose_self (k := 2) two_ne_zero h2p
    rw [mul_pow_eq_of_central hc hba p, hk, pow_mul, hcp, one_pow, one_mul]
  let f : T →* T := MonoidHom.mk' (fun a => a ^ p) hpow
  have hker : Nat.card f.ker ≤ p := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun a => (⟨(a : T), MonoidHom.mem_ker.mp a.2⟩ : {x : T // x ^ p = 1})) ?_) hcard
    intro a b hab
    exact Subtype.ext (congrArg Subtype.val hab)
  have hrange : f.range ≤ M₁ ⊓ M₂ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨hp₁ a, hp₂ a⟩
  have hlt : Nat.card f.range < Nat.card M₁ := by
    have h1 : M₁ ⊓ M₂ < M₁ :=
      lt_of_le_of_ne inf_le_left fun h => hM₁₂ (by rw [← h]; exact inf_le_right)
    exact (Subgroup.card_le_of_le hrange).trans_lt (Subgroup.card_lt_of_lt h1)
  have hT₁ : Nat.card T = Nat.card f.ker * Nat.card f.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hT₂ : Nat.card T = Nat.card M₁ * p := by rw [← hi₁, Subgroup.card_mul_index]
  have h1 : Nat.card M₁ * p ≤ p * Nat.card f.range := by
    rw [← hT₂, hT₁]
    exact Nat.mul_le_mul_right _ hker
  have h2 : p * Nat.card f.range < p * Nat.card M₁ := Nat.mul_lt_mul_of_pos_left hlt hp.out.pos
  rw [mul_comm] at h1
  exact absurd (h1.trans_lt h2) (lt_irrefl _)

theorem isCyclic_of_card_pow_eq_one_le (hp2 : p ≠ 2) {T : Type u} [Group T] [Finite T]
    (hT : IsPGroup p T) (hcard : Nat.card {x : T // x ^ p = 1} ≤ p) : IsCyclic T :=
  isCyclic_of_card_pow_eq_one_le' hp2 _ T rfl hT hcard

end Cyclic

section Burnside

variable {X : Type*} [Group X] {p : ℕ} [hp : Fact p.Prime]

theorem mem_centralizer_of_coprime {T : Subgroup X} (hT : IsPGroup p T)
    (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {g : X} (hg : g ∈ normalizer (T : Set X)) {k : ℕ}
    (hk : ¬ p ∣ k) (hgk : ∀ t ∈ T, g ^ k * t = t * g ^ k)
    (hgp : ∀ t ∈ T, t ^ p = 1 → g * t = t * g) (t : X) (ht : t ∈ T) : g * t = t * g := by
  by_contra hne
  set s := g * t * g⁻¹ * t⁻¹ with hs
  have hgt : g * t * g⁻¹ ∈ T := (mem_normalizer_iff.mp hg t).mp ht
  have hsT : s ∈ T := mul_mem hgt (inv_mem ht)
  have hs1 : s ≠ 1 := by
    intro h
    apply hne
    have h1 : g * t * g⁻¹ = t := by rw [hs, mul_inv_eq_one] at h; exact h
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]
  obtain ⟨e, he⟩ := hT ⟨s, hsT⟩
  have he' : s ^ p ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one he')
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hs1 hj
  set s' := s ^ p ^ (j - 1) with hs'
  set u := t ^ p ^ (j - 1) with hu
  have hs'p : s' ^ p = 1 := by
    rw [hs', ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0), ← hj,
      pow_orderOf_eq_one]
  have hs'1 : s' ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.out.ne_zero) ?_
    rw [hj]
    exact Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos)
  have hs'T : s' ∈ T := pow_mem hsT _
  have huT : u ∈ T := pow_mem ht _
  have hgu : g * u = s' * u * g := by
    have h1 : g * t * g⁻¹ = s * t := by rw [hs]; group
    have h2 : (g * t * g⁻¹) ^ p ^ (j - 1) = g * u * g⁻¹ := by
      rw [hu, conj_pow]
    have h3 : (s * t) ^ p ^ (j - 1) = s' * u :=
      Commute.mul_pow (hTc s hsT t ht) _
    rw [h1, h3] at h2
    calc g * u = g * u * g⁻¹ * g := by group
      _ = s' * u * g := by rw [← h2]
  have hgs' : g * s' = s' * g := hgp s' hs'T hs'p
  have hiter : ∀ i : ℕ, g ^ i * u = s' ^ i * u * g ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hcs : ∀ m : ℕ, g * s' ^ m = s' ^ m * g := fun m => (Commute.pow_right hgs' m).eq
      calc g ^ (i + 1) * u = g * (g ^ i * u) := by rw [pow_succ', mul_assoc]
        _ = g * (s' ^ i * u * g ^ i) := by rw [ih]
        _ = s' ^ i * (g * u) * g ^ i := by
          rw [← mul_assoc, ← mul_assoc, hcs i, mul_assoc (s' ^ i) g u]
        _ = s' ^ (i + 1) * u * g ^ (i + 1) := by
          rw [hgu, pow_succ s' i, pow_succ' g i]
          simp only [mul_assoc]
  have h1 := hiter k
  rw [hgk u huT] at h1
  have h2 : s' ^ k = 1 := by
    have h3 : u * g ^ k = s' ^ k * (u * g ^ k) := by rw [← mul_assoc]; exact h1
    exact right_eq_mul.mp h3
  have h4 : orderOf s' ∣ k := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_eq_prime hs'p hs'1] at h4
  exact hk h4

variable [Finite X]

theorem normalizer_le_centralizer_of_comm (P : Sylow p X)
    (hPc : ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a)
    (hcent : ∀ x : X, x ^ p = 1 → x ∈ center X) :
    normalizer (P : Set X) ≤ centralizer (P : Set X) := by
  intro n hn
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' p
    hp.out.ne_one
  have hh : n ^ b ∈ (P : Subgroup X) := by
    have hord : (n ^ b) ^ p ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    have hzp : IsPGroup p (zpowers (n ^ b)) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hord)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hle : zpowers (n ^ b) ≤ normalizer (P : Set X) :=
      (zpowers_le).mpr (pow_mem hn b)
    have h1 := P.is_maximal' (IsPGroup.to_sup_of_normal_left' P.isPGroup' hzp hle) le_sup_left
    have h2 : n ^ b ∈ (P : Subgroup X) ⊔ zpowers (n ^ b) := mem_sup_right (mem_zpowers _)
    rwa [h1] at h2
  have hg : ∀ t ∈ (P : Subgroup X), n ^ p ^ a * t = t * n ^ p ^ a := by
    intro t ht
    refine mem_centralizer_of_coprime P.isPGroup' hPc (pow_mem hn _) hb ?_ ?_ t ht
    · intro t' _
      have hnb : (n ^ p ^ a) ^ b = 1 := by rw [← pow_mul, ← hab, pow_orderOf_eq_one]
      rw [hnb, one_mul, mul_one]
    · intro t' _ ht'
      exact (mem_center_iff.mp (hcent t' ht')) _
  rw [mem_centralizer_iff]
  intro t ht
  have hcop : Nat.Coprime (p ^ a) b :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
  have hbez := Nat.gcd_eq_gcd_ab (p ^ a) b
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  have hn1 : n = (n ^ p ^ a) ^ (p ^ a).gcdA b * (n ^ b) ^ (p ^ a).gcdB b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez, zpow_one]
  have hC1 : n ^ p ^ a ∈ centralizer (P : Set X) :=
    mem_centralizer_iff.mpr fun t ht => (hg t ht).symm
  have hC2 : n ^ b ∈ centralizer (P : Set X) :=
    mem_centralizer_iff.mpr fun t ht => hPc t ht _ hh
  have hC : n ∈ centralizer (P : Set X) := by
    rw [hn1]
    exact mul_mem (zpow_mem hC1 _) (zpow_mem hC2 _)
  exact mem_centralizer_iff.mp hC t ht

theorem exists_normal_complement (hp2 : p ≠ 2)
    (hcent : ∀ x : X, x ^ p = 1 → x ∈ center X) (hcard : Nat.card {x : X // x ^ p = 1} ≤ p) :
    ∃ (K : Subgroup X) (_ : K.Normal), ¬ p ∣ Nat.card K ∧ IsPGroup p (X ⧸ K) := by
  obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
  have hPcyc : IsCyclic (P : Subgroup X) := isCyclic_of_card_pow_eq_one_le hp2 P.isPGroup'
    ((card_pow_eq_one_subgroup_le (P : Subgroup X)).trans hcard)
  have hPc : ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := (P : Subgroup X))).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hN := normalizer_le_centralizer_of_comm P hPc hcent
  refine ⟨(MonoidHom.transferSylow P hN).ker, MonoidHom.normal_ker _,
    MonoidHom.not_dvd_card_ker_transferSylow P hN, ?_⟩
  exact P.isPGroup'.of_injective (QuotientGroup.kerLift (MonoidHom.transferSylow P hN))
    (QuotientGroup.kerLift_injective _)

omit [Finite X] in
theorem mem_iff_not_dvd_orderOf {K : Subgroup X} [K.Normal] (hK : ¬ p ∣ Nat.card K)
    (hQ : IsPGroup p (X ⧸ K)) (x : X) : x ∈ K ↔ ¬ p ∣ orderOf x := by
  constructor
  · intro hx hdvd
    apply hK
    refine hdvd.trans ?_
    have := orderOf_dvd_natCard (⟨x, hx⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  · intro hx
    obtain ⟨e, he⟩ := hQ (x : X ⧸ K)
    have h1 : orderOf (x : X ⧸ K) ∣ p ^ e := orderOf_dvd_of_pow_eq_one he
    have h2 : orderOf (x : X ⧸ K) ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' K) x
    have hcop : Nat.Coprime (p ^ e) (orderOf x) :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hx)
    have h3 : orderOf (x : X ⧸ K) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3

theorem isSolvable_of_isPGroup_quotient {K : Subgroup X} [K.Normal] (hQ : IsPGroup p (X ⧸ K))
    (hK : Group.IsSolvable K) : Group.IsSolvable X := by
  have : Group.IsNilpotent (X ⧸ K) := hQ.isNilpotent
  have := hK
  refine Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

end Burnside

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
