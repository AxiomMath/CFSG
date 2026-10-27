module

public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

theorem pRank_le_of_injective {E F : Type*} [Group E] [Group F] [Finite E] [Finite F] {p : ℕ}
    (hp : p.Prime) (f : E →* F) (hf : Function.Injective f) :
    CFSG.pRank p E ≤ CFSG.pRank p F := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt f hf

theorem card_le_of_pRank_le_one {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    (hE : IsPGroup p E) (hexp : ∀ x : E, x ^ p = 1) (hrank : CFSG.pRank p E ≤ 1) :
    Nat.card E ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra h
  have := CFSG.RankThree.PartTwo.two_le_pRank hE hexp (not_le.mp h)
  omega

theorem pRank_quotient_eq_of_sup_eq_top {p : ℕ} (hp : p.Prime) {K₁ K₂ : Subgroup H}
    [K₂.Normal] (hK : K₁ ⊔ K₂ = ⊤) (hI : ¬ p ∣ Nat.card (K₁ ⊓ K₂ : Subgroup H)) :
    CFSG.pRank p (H ⧸ K₂) = CFSG.pRank p K₁ := by
  let φ : K₁ →* H ⧸ K₂ := (QuotientGroup.mk' K₂).comp K₁.subtype
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K₂ y
    have hx : x ∈ (↑(K₁ ⊔ K₂) : Set H) := by
      rw [hK]
      exact mem_top x
    rw [mul_normal] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    have hab : a * b = x := hab
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a : H) : H ⧸ K₂) = ((x : H) : H ⧸ K₂)
    rw [← hab, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).mpr hb, mul_one]
  have hker : ¬ p ∣ Nat.card φ.ker := by
    intro h
    apply hI
    let ι : φ.ker →* (K₁ ⊓ K₂ : Subgroup H) :=
      { toFun := fun x => ⟨((x : K₁) : H), mem_inf.mpr ⟨(x : K₁).2,
          (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y hxy => by
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    exact h.trans (card_dvd_of_injective ι hι)
  rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp φ.ker hker,
    CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).symm

theorem card_le_mul_card_inf {p : ℕ} (hp : p.Prime) {K₁ K₂ : Subgroup H} [K₂.Normal]
    (hK : K₁ ⊔ K₂ = ⊤) (hI : ¬ p ∣ Nat.card (K₁ ⊓ K₂ : Subgroup H))
    (h₁ : CFSG.pRank p K₁ ≤ 1) (h₂ : CFSG.pRank p K₂ ≤ 1) {P : Subgroup H}
    (hPp : IsPGroup p P) (hexp : ∀ x ∈ P, x ^ p = 1) :
    Nat.card P ≤ p * Nat.card (P ⊓ K₂ : Subgroup H) ∧ Nat.card (P ⊓ K₂ : Subgroup H) ≤ p := by
  have hinf : Nat.card (P ⊓ K₂ : Subgroup H) ≤ p := by
    refine card_le_of_pRank_le_one hp (hPp.to_le inf_le_left) (fun x => ?_) ?_
    · exact Subtype.ext (by
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact hexp x (mem_inf.mp x.2).1)
    · exact (pRank_le_of_injective hp (inclusion inf_le_right) (inclusion_injective _)).trans h₂
  refine ⟨?_, hinf⟩
  let ψ : P →* H ⧸ K₂ := (QuotientGroup.mk' K₂).comp P.subtype
  have hrange : Nat.card ψ.range ≤ p := by
    refine card_le_of_pRank_le_one hp (hPp.of_surjective ψ.rangeRestrict
      ψ.rangeRestrict_surjective) (fun y => ?_) ?_
    · obtain ⟨x, hx⟩ := ψ.rangeRestrict_surjective y
      have hx1 : x ^ p = 1 := Subtype.ext (by
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact hexp x x.2)
      rw [← hx, ← map_pow, hx1, map_one]
    · refine (pRank_le_of_injective hp ψ.range.subtype (subtype_injective _)).trans ?_
      rw [pRank_quotient_eq_of_sup_eq_top hp hK hI]
      exact h₁
  have hker : Nat.card ψ.ker ≤ Nat.card (P ⊓ K₂ : Subgroup H) := by
    let ι : ψ.ker →* (P ⊓ K₂ : Subgroup H) :=
      { toFun := fun x => ⟨((x : P) : H), mem_inf.mpr ⟨(x : P).2,
          (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Nat.card_le_card_of_injective ι fun x y hxy => by
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
  rw [← card_ker_mul_card_range ψ, mul_comm p]
  exact Nat.mul_le_mul hker hrange

theorem rank_one_normal_product_exponent_prime_intersection_splitting {p : ℕ} (hp : p.Prime)
    {K₁ K₂ : Subgroup H} [K₁.Normal] [K₂.Normal] (hK : K₁ ⊔ K₂ = ⊤)
    (hI : ¬ p ∣ Nat.card (K₁ ⊓ K₂ : Subgroup H)) (h₁ : CFSG.pRank p K₁ ≤ 1)
    (h₂ : CFSG.pRank p K₂ ≤ 1) {P : Subgroup H} (hPp : IsPGroup p P) (hPc : ¬ IsCyclic P)
    (hexp : ∀ x ∈ P, x ^ p = 1) :
    Nat.card P = p ^ 2 ∧ Nat.card (P ⊓ K₁ : Subgroup H) = p ∧
      Nat.card (P ⊓ K₂ : Subgroup H) = p ∧ Disjoint (P ⊓ K₁) (P ⊓ K₂) ∧
      (∀ x ∈ P ⊓ K₁, ∀ y ∈ P ⊓ K₂, Commute x y) ∧ (P ⊓ K₁) ⊔ (P ⊓ K₂) = P ∧
      ∃ e : (P ⊓ K₁ : Subgroup H) × (P ⊓ K₂ : Subgroup H) ≃* P, ∀ x, (e x : H) = x.1 * x.2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hPI : ∀ x ∈ P, x ∈ K₁ → x ∈ K₂ → x = 1 := by
    intro x hxP hx1 hx2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨x, hxP⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : orderOf x ∣ Nat.card (K₁ ⊓ K₂ : Subgroup H) :=
      Subgroup.orderOf_dvd_natCard _ (mem_inf.mpr ⟨hx1, hx2⟩)
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at hk
    · exact absurd ((dvd_pow_self p k.succ_ne_zero).trans (hk ▸ hdvd)) hI
  obtain ⟨hb₂, hc₂⟩ := card_le_mul_card_inf hp hK hI h₁ h₂ hPp hexp
  obtain ⟨hb₁, hc₁⟩ := card_le_mul_card_inf hp (K₁ := K₂) (K₂ := K₁) (by rw [sup_comm, hK])
    (by rwa [inf_comm]) h₂ h₁ hPp hexp
  have hge : p ^ 2 ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk]
    refine Nat.pow_le_pow_right hp.pos ?_
    by_contra hk2
    apply hPc
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · rw [pow_zero] at hk
      have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  have hP2 : Nat.card P = p ^ 2 := by
    refine le_antisymm ?_ hge
    calc Nat.card P ≤ p * Nat.card (P ⊓ K₂ : Subgroup H) := hb₂
      _ ≤ p * p := Nat.mul_le_mul_left p hc₂
      _ = p ^ 2 := (sq p).symm
  have hsq : p ^ 2 = p * p := sq p
  have hK₂ : Nat.card (P ⊓ K₂ : Subgroup H) = p :=
    le_antisymm hc₂ (Nat.le_of_mul_le_mul_left (hsq ▸ hP2 ▸ hb₂) hp.pos)
  have hK₁ : Nat.card (P ⊓ K₁ : Subgroup H) = p :=
    le_antisymm hc₁ (Nat.le_of_mul_le_mul_left (hsq ▸ hP2 ▸ hb₁) hp.pos)
  have hdisj : Disjoint (P ⊓ K₁) (P ⊓ K₂) := by
    rw [disjoint_def]
    intro x hx1 hx2
    exact hPI x (mem_inf.mp hx1).1 (mem_inf.mp hx1).2 (mem_inf.mp hx2).2
  have hcomm : ∀ x ∈ P ⊓ K₁, ∀ y ∈ P ⊓ K₂, Commute x y := by
    intro x hx y hy
    have hc : ⁅x, y⁆ ∈ K₁ ⊓ K₂ :=
      commutator_le_inf K₁ K₂ (commutator_mem_commutator (mem_inf.mp hx).2 (mem_inf.mp hy).2)
    have hcP : ⁅x, y⁆ ∈ P := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).1 (mem_inf.mp hy).1)
        (inv_mem (mem_inf.mp hx).1)) (inv_mem (mem_inf.mp hy).1)
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (hPI _ hcP (mem_inf.mp hc).1 (mem_inf.mp hc).2)
  refine ⟨hP2, hK₁, hK₂, hdisj, hcomm, ?_⟩
  let f := MonoidHom.noncommCoprod (P ⊓ K₁).subtype (P ⊓ K₂).subtype
    fun a b => hcomm a a.2 b b.2
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr ⟨subtype_injective _, subtype_injective _,
      by rwa [range_subtype, range_subtype]⟩
  have hfr : f.range = (P ⊓ K₁) ⊔ (P ⊓ K₂) := by
    have h := MonoidHom.noncommCoprod_range (P ⊓ K₁).subtype (P ⊓ K₂).subtype
      fun a b => hcomm a a.2 b b.2
    rwa [range_subtype, range_subtype] at h
  have hsup : (P ⊓ K₁) ⊔ (P ⊓ K₂) = P := by
    refine eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    rw [← hfr, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, hK₁, hK₂, hP2,
      sq]
  exact ⟨hsup, (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr (hfr.trans hsup)),
    fun x => rfl⟩

end CFSG.Quasithin.SteinbergCC
