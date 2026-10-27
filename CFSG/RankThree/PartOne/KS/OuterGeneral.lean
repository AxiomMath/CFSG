module

public import CFSG.RankThree.PartOne.KS.Lines

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

theorem mem_of_pow_eq_one_of_not_dvd_card_outer {H : Type*} [Group H] {K : Subgroup H}
    [K.Normal] {p : ℕ} (hp : p.Prime) (hC : centralizer (K : Set H) = ⊥)
    (hout : ¬ p ∣ Nat.card (Outer K)) {x : H} (hx : x ^ p = 1) : x ∈ K := by
  set α : MulAut K := MulAut.conjNormal x with hα
  have hαp : α ^ p = 1 := by rw [hα, ← map_pow, hx, map_one]
  set o : Outer K := QuotientGroup.mk α with ho
  have hop : o ^ p = 1 := by rw [ho, ← QuotientGroup.mk_pow, hαp, QuotientGroup.mk_one]
  have hdvd : orderOf o ∣ p := orderOf_dvd_of_pow_eq_one hop
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · have ho1 : o = 1 := orderOf_eq_one_iff.1 h1
    have hmem : α ∈ inner K := (QuotientGroup.eq_one_iff _).1 ho1
    obtain ⟨k, hk⟩ := hmem
    have hkx : (k : H)⁻¹ * x ∈ centralizer (K : Set H) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h2 := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : H)) hk
      simp only [MulAut.conj_apply, hα, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h2
      calc y * ((k : H)⁻¹ * x) = (k : H)⁻¹ * ((k : H) * y * (k : H)⁻¹) * x := by group
        _ = (k : H)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
        _ = (k : H)⁻¹ * x * y := by group
    rw [hC, mem_bot, inv_mul_eq_one] at hkx
    rw [← hkx]
    exact k.2
  · exfalso
    apply hout
    rw [← h1]
    exact orderOf_dvd_natCard o

theorem pow_eq_one_of_congr_conjNormal_pow {H P : Type*} [Group H] [Group P] {K : Subgroup H}
    [K.Normal] (hC : centralizer (K : Set H) = ⊥) (φ : K ≃* P) {n : ℕ} {h : H}
    (hh : (MulAut.congr φ (MulAut.conjNormal h)) ^ n = 1) : h ^ n = 1 := by
  have h1 : MulAut.congr φ (MulAut.conjNormal (h ^ n)) = MulAut.congr φ 1 := by
    rw [map_one, map_pow, map_pow, hh]
  have h2 : (MulAut.conjNormal (h ^ n) : MulAut K) = 1 := (MulAut.congr φ).injective h1
  have h3 : h ^ n ∈ centralizer (K : Set H) := by
    rw [mem_centralizer_iff]
    intro y hy
    have := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : H)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc y * h ^ n = (h ^ n * y * (h ^ n)⁻¹) * h ^ n := by rw [this]
      _ = h ^ n * y := by group
  rw [hC, mem_bot] at h3
  exact h3

theorem pow_eq_one_of_fixes_conj {P : Type*} [Group P] {S : Set P} {n : ℕ}
    (hinput : ∀ α : MulAut P, (∀ c ∈ S, α c = c) → α ^ n = 1) {β : MulAut P} (g : P)
    (hβ : ∀ c ∈ S, β (g * c * g⁻¹) = g * c * g⁻¹) : β ^ n = 1 := by
  have h1 := hinput (MulAut.conj g⁻¹ * β * (MulAut.conj g⁻¹)⁻¹) ?_
  · rw [conj_pow] at h1
    calc β ^ n = (MulAut.conj g⁻¹)⁻¹ * (MulAut.conj g⁻¹ * β ^ n * (MulAut.conj g⁻¹)⁻¹) *
          MulAut.conj g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro c hc
    have h2 : ((MulAut.conj g⁻¹)⁻¹ : MulAut P) c = g * c * g⁻¹ := by simp
    simp only [MulAut.mul_apply, h2, hβ c hc, MulAut.conj_apply, inv_inv]
    group

theorem pow_eq_one_of_centralizes_of_exists_conj {H P : Type*} [Group H] [Group P]
    {K : Subgroup H} [K.Normal] (hC : centralizer (K : Set H) = ⊥) (φ : K ≃* P) {S : Set P}
    {x : P} {n : ℕ} (hS : ∀ c ∈ S, c * x = x * c)
    (hinput : ∀ α : MulAut P, (∀ c ∈ S, α c = c) → α ^ n = 1) {a : K} {g : P}
    (hag : φ a = g * x * g⁻¹) {h : H}
    (hh : ∀ k : K, k * a = a * k → h * (k : H) = (k : H) * h) : h ^ n = 1 := by
  refine pow_eq_one_of_congr_conjNormal_pow hC φ (pow_eq_one_of_fixes_conj hinput g ?_)
  intro c hc
  set k : K := φ.symm (g * c * g⁻¹) with hk
  have hφk : φ k = g * c * g⁻¹ := φ.apply_symm_apply _
  have hka : k * a = a * k := by
    apply φ.injective
    rw [map_mul, map_mul, hφk, hag]
    calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [hS c hc]
      _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group
  have hhk : MulAut.conjNormal h k = k := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hh k hka]
    group
  show φ (MulAut.conjNormal h (φ.symm (g * c * g⁻¹))) = g * c * g⁻¹
  rw [← hk, hhk, hφk]

theorem inf_core_centralizes_of_inner_core_bot {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (K : Subgroup H) [K.Normal] {a : H} (ha : a ∈ K)
    (hcore : inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨a, ha⟩ : K)} : Set K)) = ⊥) :
    (∀ x ∈ inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set H)),
      x ∈ K → x = 1) ∧
    ∀ x ∈ inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set H)),
      ∀ y ∈ K, y * a = a * y → x * y = y * x := by
  set A := inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set H)) with hA
  have hmeet : ∀ x ∈ A, x ∈ K → x = 1 := by
    intro x hx hxK
    have hle := SteinbergBM.subgroupOf_inSubgroup_aschbacherSolvableCore_le hp K ha
    have hx' : (⟨x, hxK⟩ : K) ∈ A.subgroupOf K := hx
    have h1 := hle hx'
    rw [hcore, mem_bot] at h1
    exact congrArg Subtype.val h1
  refine ⟨hmeet, fun x hx y hyK hya => ?_⟩
  have hyC : y ∈ centralizer ({a} : Set H) := mem_centralizer_singleton_iff.2 hya
  have hyN : y ∈ normalizer (A : Set H) :=
    SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _
      (Subgroup.le_normalizer hyC)
  have h1 : y * x⁻¹ * y⁻¹ ∈ A := (mem_normalizer_iff.1 hyN x⁻¹).1 (A.inv_mem hx)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ A := by
    have := A.mul_mem hx h1
    rwa [show x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ by group] at this
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ K :=
    K.mul_mem (‹K.Normal›.conj_mem y hyK x) (K.inv_mem hyK)
  have h4 := hmeet _ h2 h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h4, one_mul]

theorem mem_of_central_of_abelian_sq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {F E : Subgroup G} (hFcard : Nat.card F = p ^ 3) (hEF : E ≤ F)
    (hEcard : Nat.card E = p ^ 2) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {z : G}
    (hz : z ∈ F) (hzc : ∀ f ∈ F, z * f = f * z)
    (hnab : ∃ f₁ ∈ F, ∃ f₂ ∈ F, f₁ * f₂ ≠ f₂ * f₁) : z ∈ E := by
  by_contra hzE
  set D : Subgroup G := Subgroup.closure ((E : Set G) ∪ {z}) with hD
  have hDF : D ≤ F :=
    (Subgroup.closure_le F).2 (Set.union_subset hEF (Set.singleton_subset_iff.2 hz))
  have hED : E ≤ D := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hzD : z ∈ D := Subgroup.subset_closure (Or.inr rfl)
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    have h := closure_le_centralizer_closure_of_forall_comm (S := (E : Set G) ∪ {z}) (by
      rintro a (ha | ha) b (hb | hb)
      · exact hEcomm a ha b hb
      · rw [Set.mem_singleton_iff] at hb
        rw [hb]
        exact (hzc a (hEF ha)).symm
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact hzc b (hEF hb)
      · rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb])
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.1 (h hb) a ha
  have hDcard : Nat.card D ∣ p ^ 3 := hFcard ▸ Subgroup.card_dvd_of_le hDF
  have hEdvd : p ^ 2 ∣ Nat.card D := hEcard ▸ Subgroup.card_dvd_of_le hED
  obtain ⟨i, hi, hDi⟩ := (Nat.dvd_prime_pow hp).1 hDcard
  rw [hDi] at hEdvd
  have hi2 : 2 ≤ i := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hEdvd
  interval_cases i
  · have : E = D := Subgroup.eq_of_le_of_card_ge hED (by rw [hDi, hEcard])
    exact hzE (this ▸ hzD)
  · have : D = F := Subgroup.eq_of_le_of_card_ge hDF (by rw [hDi, hFcard])
    obtain ⟨f₁, hf₁, f₂, hf₂, hne⟩ := hnab
    rw [← this] at hf₁ hf₂
    exact hne (hDcomm f₁ hf₁ f₂ hf₂)

theorem exists_conj_le_of_isPGroup_of_card {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {F E : Subgroup G}
    (hF : Nat.card F = p ^ (Nat.card G).factorization p) (hE : IsPGroup p E) :
    ∃ g : G, ∀ y ∈ E, g⁻¹ * y * g ∈ F := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (Sylow.ofCard F hF) S
  refine ⟨g, fun y hy => ?_⟩
  have hyS : y ∈ (S : Subgroup G) := hS hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hyS

theorem exists_conj_mem_of_central_of_abelian_sq {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {F E : Subgroup G} (hFcard : Nat.card F = p ^ 3)
    (hSyl : Nat.card F = p ^ (Nat.card G).factorization p) (hEcard : Nat.card E = p ^ 2)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {z : G} (hz : z ∈ F)
    (hzc : ∀ f ∈ F, z * f = f * z) (hnab : ∃ f₁ ∈ F, ∃ f₂ ∈ F, f₁ * f₂ ≠ f₂ * f₁) :
    ∃ g : G, g * z * g⁻¹ ∈ E := by
  obtain ⟨g, hg⟩ := exists_conj_le_of_isPGroup_of_card hp hSyl (IsPGroup.of_card hEcard)
  set E₂ : Subgroup G := E.map (MulAut.conj g⁻¹).toMonoidHom with hE₂
  have hE₂F : E₂ ≤ F := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hg y hy
  have hE₂card : Nat.card E₂ = p ^ 2 := by
    rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEcard]
  have hE₂comm : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hEcomm y hy w hw]
  obtain ⟨y, hy, hyz⟩ := mem_of_central_of_abelian_sq hp hFcard hE₂F hE₂card hE₂comm hz hzc hnab
  refine ⟨g, ?_⟩
  have : y = g * z * g⁻¹ := by
    rw [← hyz]
    change y = g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹
    group
  rw [← this]
  exact hy

theorem centralizer_singleton_pow_eq {G : Type*} [Group G] {y : G} {e : ℕ}
    (he : Nat.Coprime e (orderOf y)) :
    centralizer ({y ^ e} : Set G) = centralizer ({y} : Set G) := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime he
  ext c
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : Commute c (y ^ e) := h
    have := h'.pow_right m
    rw [hm] at this
    exact this
  · intro h
    have h' : Commute c y := h
    exact h'.pow_right e

end CFSG.RankThree.PartOne
