module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432AutDescent

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (Real3)

theorem weaklyClosed_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {Z : Subgroup G} (h : WeaklyClosed Z) : WeaklyClosed (Z.map e.toMonoidHom) := by
  intro y hle
  obtain ⟨g, rfl⟩ := e.surjective y
  have hconj : ∀ W : Subgroup G, (W.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom =
      (W.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
    intro W
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  have hN : ∀ x : G, e x ∈ Subgroup.normalizer ((Z.map e.toMonoidHom : Subgroup H) : Set H) ↔
      x ∈ Subgroup.normalizer (Z : Set G) := by
    intro x
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    have hmem : ∀ w : G, w ∈ Z ↔ e w ∈ Z.map e.toMonoidHom := fun w =>
      (Subgroup.mem_map_iff_mem e.injective).symm
    constructor
    · intro hx w
      rw [hmem w, hmem (x * w * x⁻¹)]
      have := hx (e w)
      simpa using this
    · intro hx w'
      obtain ⟨w, rfl⟩ := e.surjective w'
      rw [← hmem w, show e x * e w * (e x)⁻¹ = e (x * w * x⁻¹) by simp, ← hmem]
      exact hx w
  rw [hconj] at hle ⊢
  have hle' : Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) := by
    intro w hw
    have : e w ∈ (Z.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hw
    exact (hN w).mp (hle this)
  rw [h g hle']

theorem ListRow.of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T] [Finite T] (e : S ≃* T)
    (h : ListRow S) : ListRow T := by
  intro z hz hwc
  obtain ⟨z', rfl⟩ := e.surjective z
  have hz' : orderOf z' = 3 := by rw [← hz]; exact (MulEquiv.orderOf_eq e z').symm
  have hwc' : WeaklyClosed (Subgroup.zpowers z') := by
    have := weaklyClosed_map_mulEquiv e.symm hwc
    rw [MonoidHom.map_zpowers] at this
    simpa using this
  rcases h z' hz' hwc' with h1 | ⟨hG, hr, hn⟩ | ⟨hJ, hr, hn⟩
  · left
    rw [← h1]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e).symm
  · right; left
    refine ⟨?_, Real3.of_mulEquiv e.symm hr, ?_⟩
    · rcases hG with ⟨p, f, hm⟩ | he'
      · exact Or.inl ⟨p, f, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e.symm hm⟩
      · obtain ⟨e'⟩ := he'
        exact Or.inr ⟨e.symm.trans e'⟩
    · intro L _ _ hq hZ ⟨f⟩
      exact hn L hq hZ ⟨f.trans e.symm⟩
  · right; right
    obtain ⟨e'⟩ := hJ
    exact ⟨⟨e.symm.trans e'⟩, Real3.of_mulEquiv e.symm hr, fun L _ _ hq hZ ⟨f⟩ =>
      hn L hq hZ ⟨f.trans e.symm⟩⟩

theorem autWeaklyClosed_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) {σ : MulAut S}
    (h : AutWeaklyClosed σ) : AutWeaklyClosed (MulAut.congr e σ) := by
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  have hρ : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have eq1 : MulAut.conj (e x) * MulAut.congr e σ * (MulAut.conj (e x))⁻¹ =
      (MulAut.congr e).toMonoidHom (MulAut.conj x * σ * (MulAut.conj x)⁻¹) := by
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, map_inv]
    rw [← KFacts.congr_mulAutConj]
  rw [eq1] at hy ⊢
  have h1 : MulAut.conj x * σ * (MulAut.conj x)⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.zpowers σ : Subgroup (MulAut S)) : Set (MulAut S)) :=
    mem_normalizer_zpowers_of_map (MulAut.congr e).toMonoidHom hρ (σ := σ) (by simpa using hy)
  have h2 := h x h1
  rw [show MulAut.congr e σ = (MulAut.congr e).toMonoidHom σ from rfl, ← MonoidHom.map_zpowers]
  exact Subgroup.mem_map_of_mem _ h2

theorem OuterRow.of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T] [Finite T] (e : S ≃* T)
    (h : OuterRow S) : OuterRow T := by
  intro h3 σ hσ hout hwc
  have hS3 : 3 ∣ Nat.card S := by rw [Nat.card_congr e.toEquiv]; exact h3
  refine h hS3 (MulAut.congr e.symm σ) ?_ ?_ ?_
  · rw [← map_pow, hσ, map_one]
  · rintro ⟨s, hs⟩
    apply hout
    refine ⟨e s, ?_⟩
    have : σ = MulAut.congr e (MulAut.congr e.symm σ) := by
      ext t; simp
    rw [this, ← hs]
    exact (KFacts.congr_mulAutConj e s).symm
  · exact autWeaklyClosed_congr e.symm hwc

theorem GoodRow.of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T] [Finite T] (e : S ≃* T)
    (h : GoodRow S) : GoodRow T :=
  ⟨ListRow.of_mulEquiv e h.1, OuterRow.of_mulEquiv e h.2⟩

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem outerRow_of_not_three_dvd_outer {S : Type} [Group S] [Finite S]
    (h : ¬ 3 ∣ Nat.card (Outer S)) : OuterRow S := by
  intro _ σ hσ hout
  exfalso
  apply hout
  have hne : Nat.card (Outer S) ≠ 0 := fun h0 => h (h0 ▸ dvd_zero 3)
  have : Finite (Outer S) := Nat.finite_of_card_ne_zero hne
  set t : Outer S := (σ : Outer S) with ht
  have ht3 : t ^ 3 = 1 := by rw [ht, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one]
  have hcop : Nat.Coprime 3 (Nat.card (Outer S)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
  have hord : orderOf t ∣ Nat.gcd 3 (Nat.card (Outer S)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht3) (orderOf_dvd_natCard t)
  rw [hcop] at hord
  have ht1 : t = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  exact (QuotientGroup.eq_one_iff σ).mp ht1

end CFSG.RankThree.PartTwo.Sec4.RonanK432
