module

public import CFSG.Quasithin.Background.D2Y12
public import CFSG.Quasithin.Background.D2Conj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

theorem card_sup_zpowers_of_odd {G : Type*} [Group G] [Finite G] {F : Subgroup G} {t : G}
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hF : Odd (Nat.card F))
    (hn : Subgroup.zpowers t ≤ Subgroup.normalizer (F : Set G)) :
    Nat.card ↥(F ⊔ Subgroup.zpowers t) = Nat.card F * 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdisj : F ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgF, hgt⟩
    have h1 : orderOf g ∣ Nat.card F := by
      have := orderOf_dvd_natCard (⟨g, hgF⟩ : ↥F)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf g ∣ 2 := by
      have := orderOf_dvd_natCard (⟨g, hgt⟩ : ↥(Subgroup.zpowers t))
      rwa [Subgroup.orderOf_mk, Nat.card_zpowers, hord] at this
    have h3 : orderOf g ∣ Nat.gcd (Nat.card F) 2 := Nat.dvd_gcd h1 h2
    have hcop : Nat.gcd (Nat.card F) 2 = 1 := by
      obtain ⟨k, hk⟩ := hF
      rw [hk]
      simp [Nat.gcd_comm]
    rw [hcop, Nat.dvd_one] at h3
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)
  let f : ↥F × ↥(Subgroup.zpowers t) → G := fun p => (p.1 : G) * (p.2 : G)
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a' : G)⁻¹ * a = (b' : G) * (b : G)⁻¹ := by
      have : (a : G) * b = a' * b' := h
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [this]
        _ = (b' : G) * (b : G)⁻¹ := by group
    have h2 : (a' : G)⁻¹ * a ∈ F ⊓ Subgroup.zpowers t :=
      ⟨F.mul_mem (F.inv_mem a'.2) a.2, by rw [h1]; exact Subgroup.mul_mem _ b'.2 (Subgroup.inv_mem _ b.2)⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    have ha : (a : G) = a' := by
      have := congrArg (fun y => (a' : G) * y) h2
      simpa using this
    have hb : (b : G) = b' := by
      have h3 : (b' : G) * (b : G)⁻¹ = 1 := by rw [← h1]; exact h2
      have := congrArg (fun y => y * (b : G)) h3
      exact (by simpa using this : (b' : G) = b).symm
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hrange : Set.range f = ((F ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
    ext g
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact Subgroup.mul_mem_sup a.2 b.2
    · intro hg
      rw [Subgroup.coe_mul_of_right_le_normalizer_left F (Subgroup.zpowers t) hn] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(F ⊔ Subgroup.zpowers t)
      = Nat.card ↥(Set.range f) := by rw [hrange]; rfl
    _ = Nat.card (↥F × ↥(Subgroup.zpowers t)) := Nat.card_range_of_injective hinj
    _ = Nat.card F * 2 := by rw [Nat.card_prod, Nat.card_zpowers, hord]

omit [Finite V] in
theorem card_of_dihedral {X : Subgroup (MulAut V)} {n : ℕ} [NeZero n]
    (e : Nonempty (↥X ≃* DihedralGroup n)) : Nat.card X = 2 * n := by
  obtain ⟨e⟩ := e
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

section Cyc

variable {X : Subgroup (MulAut V)}

omit [Finite V] in
theorem zpowers_le_normalizer_fittingOf {t : MulAut V} (ht : t ∈ X) :
    Subgroup.zpowers t ≤ Subgroup.normalizer (fittingOf X : Set (MulAut V)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · exact fun hf => conj_mem_fittingOf ht hf
  · intro hf
    have := conj_mem_fittingOf (X.inv_mem ht) hf
    simpa [mul_assoc] using this

theorem D2_17_cyclic (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) :
    QhatStar X = sylow2Of X ∧ D217Concl X 2 := by
  have hne : (QhatStar X).Nonempty := QhatStar_nonempty c.hyp.qhat c.hyp.le_two
  suffices h : (∃ m, Odd m ∧ Nat.card X = 2 * m) ∧ D217Concl X 2 by
    obtain ⟨⟨m, hm, hcard⟩, hc⟩ := h
    refine ⟨qhatStar_eq_sylow2Of hne fun B hB => ?_, hc⟩
    obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hB
    exact mem_sylow2Of_of_card hA2.le hA2.isElemAbelian2.isPGroup hm
      (by rw [c.cyc B hB, hcard])
  have hFodd := odd_card_fittingOf c.hyp.o2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hX1 : (Xk X 1).Nonempty
  · obtain ⟨hE, hF9, ⟨t, htX, hto, hinv, hXeq⟩, hrk⟩ := D2_25 hV c hX1
    have ht1 : t ≠ 1 := fun e => by rw [e, orderOf_one] at hto; omega
    have ht2 : t ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one t
    have hcard := card_sup_zpowers_of_odd ht2 ht1 hFodd (zpowers_le_normalizer_fittingOf htX)
    rw [← hXeq] at hcard
    exact ⟨⟨Nat.card (fittingOf X), hFodd, by rw [hcard]; ring⟩,
      Or.inr (Or.inr (Or.inl ⟨hE, hF9, ⟨t, htX, hto, hinv, hXeq⟩, hrk, rfl⟩))⟩
  · have hX1' : ∀ Y ∈ Xk X 1, False := fun Y hY => hX1 ⟨Y, hY⟩
    by_cases htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂
    · obtain ⟨hF27, hcube, hnon, ⟨t, htX, hto, hfrat, hXeq⟩, hrk⟩ := D2_17_case4 hV c hX1' htwo
      have ht1 : t ≠ 1 := fun e => by rw [e, orderOf_one] at hto; omega
      have ht2 : t ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one t
      have hcard := card_sup_zpowers_of_odd ht2 ht1 hFodd (zpowers_le_normalizer_fittingOf htX)
      rw [← hXeq] at hcard
      exact ⟨⟨Nat.card (fittingOf X), hFodd, by rw [hcard]; ring⟩,
        Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hF27, hcube, hnon, ⟨t, htX, hto, hfrat, hXeq⟩, hrk, rfl⟩)))⟩
    · push Not at htwo
      obtain ⟨A, hA⟩ := hne
      obtain ⟨t, ht, -⟩ := c.exists_tinv hA
      obtain ⟨x, hx, hx1, hinv⟩ := exists_inverted hV c ht
      have hY₀ := zpowers_mem_Yinv hV ht hx hx1 hinv
      obtain ⟨hiso, hrk⟩ := D2_27 hV c hX1' hY₀ (fun Y hY => htwo Y hY _ hY₀)
      exact ⟨⟨3, ⟨1, rfl⟩, card_of_dihedral hiso⟩,
        Or.inl ⟨hiso, by rw [hrk]; norm_num, Or.inr rfl⟩⟩

end Cyc

end CFSG.Quasithin
