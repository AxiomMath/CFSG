
module

public import CFSG.Quasithin.Background.A3Structure36BElemBase

public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {X : Type} [Group X]

theorem elem_case (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) {q : ℕ} (hq : q.Prime)
    (D : PrimeData X q) (hDK : D.K = K) (hE : IsElemAbelianOfRank q 2 ↥D.P) {t : X}
    (ht2 : t ^ 2 = 1) (htK : t ∉ K) :
    (∀ x y : ↥(CFSG.pCore q X), x * y = y * x) ∧
    (∀ r : ↥(CFSG.pCore q X), MulAut.conjNormal t r = r⁻¹) ∧
    ∃ e : ℕ, 1 ≤ e ∧
      Nonempty (↥(CFSG.pCore q X) ≃*
        (Multiplicative (ZMod (q ^ e)) × Multiplicative (ZMod (q ^ e)))) ∧
      (e = 1 → D.P = ⊤) ∧
      (2 ≤ e → ∃ T : Subgroup X, T.Normal ∧ T ≤ CFSG.pCore q X ∧
        D.P.map (CFSG.pCore q X).subtype ≤ T ∧
        Nonempty (↥T ≃* (Multiplicative (ZMod (q ^ 2)) × Multiplicative (ZMod (q ^ 2))))) := by
  have hfin : Finite X := h.finite
  have hfq : Fact q.Prime := ⟨hq⟩
  have hDchar : D.P.Characteristic := D.characteristic
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  have hRF : CFSG.pCore q X ≤ CFSG.fittingSubgroup X := CFSG.pCore_le_fitting X q
  have hRK : CFSG.pCore q X ≤ K := hKF ▸ hRF
  have hRp : IsPGroup q ↥(CFSG.pCore q X) := CFSG.pCore_isPGroup
  have hPp : IsPGroup q ↥D.P := hRp.to_subgroup D.P
  have hΦ : frattini ↥D.P = ⊥ := (frattini_eq_bot_iff hPp).2 (IsElemAbelianOfRank.comm_pow hE)
  have hcardP : Nat.card ↥D.P = q ^ 2 := by
    have h1 := D.card_W
    rw [hΦ] at h1
    have h3 : Nat.card (↥D.P ⧸ (⊥ : Subgroup ↥D.P)) = Nat.card ↥D.P := by
      rw [← Subgroup.index_eq_card, Subgroup.index_bot]
    rw [h3] at h1
    exact h1
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 : Nat.card ↥(CFSG.pCore 2 X) = 1 := by
      rw [h.o2]
      exact Subgroup.card_bot
    have h2 : Nat.card ↥D.P ≤ Nat.card ↥(CFSG.pCore 2 X) := Subgroup.card_le_card_group _
    rw [hcardP, h1] at h2
    omega
  have hcentP : ∀ r : ↥(CFSG.pCore q X), ∀ d ∈ D.P, r * d = d * r := by
    intro r d hd
    have hrK : (r : X) ∈ D.K := hDK ▸ hRK r.2
    obtain ⟨y, hy, hyd⟩ := (D.mem_K (r : X)).1 hrK d hd
    rw [hΦ] at hy
    have hy1 : y = 1 := Subgroup.mem_bot.1 hy
    have h1 : d⁻¹ * MulAut.conjNormal (r : X) d = 1 := by
      rw [← hyd, hy1]
      rfl
    have h2 : MulAut.conjNormal (r : X) d = d := (inv_mul_eq_one.1 h1).symm
    have h3 : r * d * r⁻¹ = d := Subtype.ext (congrArg Subtype.val h2)
    exact mul_inv_eq_iff_eq_mul.1 h3
  have hinvP : ∀ d ∈ D.P, MulAut.conjNormal t d = d⁻¹ := by
    intro d hd
    obtain ⟨y, hy, hyd⟩ := D.inv_W t (by rw [hDK]; exact htK)
      (by rw [hDK, ht2]; exact K.one_mem) d hd
    rw [hΦ] at hy
    have hy1 : y = 1 := Subgroup.mem_bot.1 hy
    have h1 : d * MulAut.conjNormal t d = 1 := by
      rw [← hyd, hy1]
      rfl
    exact eq_inv_of_mul_eq_one_right h1
  have hσσ : ∀ x : ↥(CFSG.pCore q X),
      MulAut.conjNormal t (MulAut.conjNormal t x) = x := by
    intro x
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    have : t * (t * (x : X) * t⁻¹) * t⁻¹ = t ^ 2 * (x : X) * (t ^ 2)⁻¹ := by
      rw [pow_two, mul_inv_rev]
      simp only [mul_assoc]
    rw [this, ht2]
    simp
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup X, P' = D.P.map (CFSG.pCore q X).subtype := ⟨_, rfl⟩
  have hP'le : P' ≤ CFSG.pCore q X := hP' ▸ Subgroup.map_subtype_le D.P
  have hmemP' : ∀ x : X, x ∈ P' ↔ ∃ d : ↥(CFSG.pCore q X), d ∈ D.P ∧ (d : X) = x := by
    intro x
    rw [hP']
    exact Subgroup.mem_map
  have hP'card : Nat.card P' = q ^ 2 := by
    rw [hP', Subgroup.card_map_of_injective (CFSG.pCore q X).subtype_injective]
    exact hcardP
  have hP'comm : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := (hmemP' a).1 ha
    obtain ⟨b', hb', rfl⟩ := (hmemP' b).1 hb
    have := (IsElemAbelianOfRank.comm_pow hE).1 ⟨a', ha'⟩ ⟨b', hb'⟩
    exact congrArg (fun z : ↥D.P => ((z : ↥(CFSG.pCore q X)) : X)) this
  have hP'pow : ∀ a ∈ P', a ^ q = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := (hmemP' a).1 ha
    have := (IsElemAbelianOfRank.comm_pow hE).2 ⟨a', ha'⟩
    exact congrArg (fun z : ↥D.P => ((z : ↥(CFSG.pCore q X)) : X)) this
  have hfix : ∀ x : ↥(CFSG.pCore q X), MulAut.conjNormal t x = x → x = 1 := by
    intro x hx
    by_contra hx1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hRp) x
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply hx1
      exact orderOf_eq_one_iff.1 (by simpa using hj)
    have hdvd : q ∣ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hj]
      exact dvd_pow_self q hj0
    obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) q hdvd
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(CFSG.pCore q X), y₀ = (y : ↥(CFSG.pCore q X)) := ⟨_, rfl⟩
    have hy₀o : orderOf y₀ = q := by
      rw [hy₀, Subgroup.orderOf_coe]
      exact hyo
    have hy₀fix : MulAut.conjNormal t y₀ = y₀ := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 y.2
      rw [hy₀, ← hm, map_zpow, hx]
    have hy₀q : y₀ ^ q = 1 := by
      have h5 := pow_orderOf_eq_one y₀
      rwa [hy₀o] at h5
    have hy₀1 : y₀ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy₀o
      exact hq.one_lt.ne hy₀o
    have hy₀P : (y₀ : X) ∉ P' := by
      intro hmem
      obtain ⟨d, hd, hdy⟩ := (hmemP' _).1 hmem
      have hdy' : d = y₀ := Subtype.ext hdy
      rw [hdy'] at hd
      have h1 := hinvP y₀ hd
      rw [hy₀fix] at h1
      have h2 : y₀ ^ 2 = 1 := by
        have : y₀ * y₀ = 1 := mul_eq_one_iff_eq_inv.2 h1
        rwa [pow_two]
      have h3 : q ∣ 2 := by
        rw [← hy₀o]
        exact orderOf_dvd_of_pow_eq_one h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h3)
    have hy₀comm : ∀ d ∈ P', (y₀ : X) * d = d * (y₀ : X) := by
      intro d hd
      obtain ⟨d', hd', rfl⟩ := (hmemP' d).1 hd
      exact congrArg (fun z : ↥(CFSG.pCore q X) => (z : X)) (hcentP y₀ d' hd')
    obtain ⟨E, hE'⟩ : ∃ E : Subgroup X, E = Subgroup.closure ((P' : Set X) ∪ {(y₀ : X)}) :=
      ⟨_, rfl⟩
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      have hpair : ((P' : Set X) ∪ {(y₀ : X)}).Pairwise Commute := by
        intro a ha b hb hab
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact hP'comm a ha b hb
        · rw [Set.mem_singleton_iff.1 hb]
          exact (hy₀comm a ha).symm
        · rw [Set.mem_singleton_iff.1 ha]
          exact hy₀comm b hb
        · exact absurd ((Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm) hab
      have := Subgroup.isMulCommutative_closure hpair
      intro a ha b hb
      rw [hE'] at ha hb
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure
        ((P' : Set X) ∪ {(y₀ : X)})) ⟨b, hb⟩)
    have hEpow : ∀ a ∈ E, a ^ q = 1 := by
      intro a ha
      rw [hE'] at ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact hP'pow x hx
        · rw [Set.mem_singleton_iff.1 hx]
          have := congrArg (fun z : ↥(CFSG.pCore q X) => (z : X)) hy₀q
          simpa using this
      | one => exact one_pow q
      | mul x y hxE hyE hxq hyq =>
        have hc : Commute x y := hEcomm x (hE' ▸ hxE) y (hE' ▸ hyE)
        rw [hc.mul_pow, hxq, hyq, one_mul]
      | inv x hxE hxq => rw [inv_pow, hxq, inv_one]
    have hEle : E ≤ CFSG.pCore q X := by
      rw [hE', Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hP'le hx
      · rw [Set.mem_singleton_iff.1 hx]
        exact (y₀ : ↥(CFSG.pCore q X)).2
    have hP'E : P' ≤ E := by
      rw [hE']
      exact fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hy₀E : (y₀ : X) ∈ E := by
      rw [hE']
      exact Subgroup.subset_closure (Or.inr rfl)
    have hEp : IsPGroup q ↥E := (CFSG.pCore_isPGroup (p := q) (G := X)).to_le hEle
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hEel : CFSG.Open.IsElemAbelian q E :=
      ⟨⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩, hEpow⟩
    have hk3 : k ≤ CFSG.Open.pRank q (⊤ : Subgroup X) :=
      le_pRank hq.one_lt le_top hEel hk
    have hk2 := h.rank q hq hq2
    have hlt : Nat.card P' < Nat.card E := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hP'E) fun hEq => ?_
      exact hy₀P ((Subgroup.eq_of_le_of_card_ge hP'E (by rw [hEq])) ▸ hy₀E)
    rw [hP'card, hk] at hlt
    have : 2 < k := (Nat.pow_lt_pow_iff_right hq.one_lt).1 hlt
    omega
  obtain ⟨hinvR, hcommR⟩ := eq_inv_of_fixedPointFree (MulAut.conjNormal t) hσσ hfix
  let _ : CommGroup ↥(CFSG.pCore q X) :=
    { (inferInstance : Group ↥(CFSG.pCore q X)) with mul_comm := hcommR }
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Subgroup ↥(CFSG.pCore q X),
      Ω = (powMonoidHom q : ↥(CFSG.pCore q X) →* ↥(CFSG.pCore q X)).ker := ⟨_, rfl⟩
  have hmemΩ : ∀ x : ↥(CFSG.pCore q X), x ∈ Ω ↔ x ^ q = 1 := by
    intro x
    rw [hΩdef, MonoidHom.mem_ker, powMonoidHom_apply]
  have hPΩ : D.P ≤ Ω := fun x hx => (hmemΩ x).2 (D.supercritical.pow_eq_one x hx)
  have hΩcard : Nat.card Ω ≤ q ^ 2 := by
    obtain ⟨k, hk⟩ := (hRp.to_subgroup Ω).exists_card_eq
    have hel : CFSG.Open.IsElemAbelian q (Ω.map (CFSG.pCore q X).subtype) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨ω₁, -, h₁⟩ := a.2
        obtain ⟨ω₂, -, h₂⟩ := b.2
        apply Subtype.ext
        change (a : X) * b = b * a
        rw [← h₁, ← h₂, ← map_mul, ← map_mul, hcommR ω₁ ω₂]
      · rintro _ ⟨ω, hω, rfl⟩
        rw [← map_pow, (hmemΩ ω).1 hω, map_one]
    have hk' : Nat.card (Ω.map (CFSG.pCore q X).subtype) = q ^ k := by
      rw [Subgroup.card_map_of_injective (CFSG.pCore q X).subtype_injective]
      exact hk
    have h1 := le_pRank hq.one_lt le_top hel hk'
    have h2 := h.rank q hq hq2
    rw [hk]
    exact Nat.pow_le_pow_right hq.pos (h1.trans h2)
  have hPΩeq : D.P = Ω := Subgroup.eq_of_le_of_card_ge hPΩ (by rw [hcardP]; exact hΩcard)
  have hΩcard' : Nat.card Ω = q ^ 2 := by rw [← hPΩeq]; exact hcardP
  have hirr : ∀ S : Subgroup ↥(CFSG.pCore q X), S.Characteristic → S ≤ Ω → S = ⊥ ∨ S = Ω := by
    intro S hS hSΩ
    have hSP : S ≤ D.P := hPΩeq ▸ hSΩ
    rw [← hPΩeq]
    exact D.irr hΦ S hSP fun g u hu => char_apply_mem hS (MulAut.conjNormal g) hu
  obtain ⟨e, he1, hexp, a, b, ha, hb, hab⟩ := exists_independent_generators hq hRp
    (by rw [← hΩdef]; exact hΩcard') (by rw [← hΩdef]; exact hirr)
  have hΩcard'' : Nat.card
      (powMonoidHom q : ↥(CFSG.pCore q X) →* ↥(CFSG.pCore q X)).ker ≤ q ^ 2 := by
    rw [← hΩdef]
    exact hΩcard
  refine ⟨hcommR, hinvR, e, he1, ?_, ?_, ?_⟩
  · obtain ⟨φ⟩ := mulEquiv_zmod_prod hq hexp hΩcard'' ha hb hab
    exact ⟨φ⟩
  · intro he1'
    subst he1'
    rw [eq_top_iff]
    intro x _
    have hx : x ^ q = 1 := by simpa using hexp x
    have hxΩ : x ∈ Ω := (hmemΩ x).2 hx
    rw [← hPΩeq] at hxΩ
    exact hxΩ
  · intro he2
    obtain ⟨Ω₂, hΩ₂def⟩ : ∃ Ω₂ : Subgroup ↥(CFSG.pCore q X),
        Ω₂ = (powMonoidHom (q ^ 2) : ↥(CFSG.pCore q X) →* ↥(CFSG.pCore q X)).ker := ⟨_, rfl⟩
    have hmem₂ : ∀ x : ↥(CFSG.pCore q X), x ∈ Ω₂ ↔ x ^ q ^ 2 = 1 := by
      intro x
      rw [hΩ₂def, MonoidHom.mem_ker, powMonoidHom_apply]
    refine ⟨Ω₂.map (CFSG.pCore q X).subtype, ?_, Subgroup.map_subtype_le Ω₂, ?_, ?_⟩
    · refine ⟨fun n hn g => ?_⟩
      obtain ⟨ω, hω, rfl⟩ := hn
      refine ⟨MulAut.conjNormal g ω, ?_, ?_⟩
      · have h1 : ω ^ q ^ 2 = 1 := (hmem₂ ω).1 hω
        exact (hmem₂ _).2 (by rw [← map_pow, h1, map_one])
      · simp [MulAut.conjNormal_apply]
    · refine Subgroup.map_mono fun x hx => ?_
      rw [hmem₂, pow_two, pow_mul, D.supercritical.pow_eq_one x hx, one_pow]
    · obtain ⟨φ⟩ := omegaTwo_equiv hq he2 hΩcard'' ha hb hab
      exact ⟨((Ω₂.equivMapOfInjective _ (CFSG.pCore q X).subtype_injective).symm).trans
        ((MulEquiv.subgroupCongr hΩ₂def).trans φ)⟩

end CFSG.Quasithin.A36B
