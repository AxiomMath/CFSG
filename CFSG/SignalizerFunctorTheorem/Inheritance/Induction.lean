module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
public import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal
public import CFSG.SignalizerFunctorTheorem.Inheritance.Quotient

public section

universe u

namespace CFSG.SignalizerFunctorTheorem

theorem mem_centralizer_singleton_of_conj {H : Type*} [Group H] {a x : H}
    (h : a * x * a⁻¹ = x) : x ∈ Subgroup.centralizer ({a} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem NoFaithfulSection.exists_centralizing {G : Type*} [Group G] {A W T : Subgroup G}
    (h : NoFaithfulSection A W) (hTW : T ≤ W) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    [IsSimpleGroup T] (hnc : ∃ x y : T, x * y ≠ y * x) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ T, a * x * a⁻¹ = x := by
  have hnormal : ((⊥ : Subgroup G).subgroupOf T).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  let e : T ⧸ (⊥ : Subgroup G).subgroupOf T ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf T)).trans
      QuotientGroup.quotientBot
  obtain ⟨a, haA, ha1, hmem⟩ := h T ⊥ hTW bot_le hAT
    (fun a _ => by
      rw [(Subgroup.normalizer_eq_top_iff).mpr (inferInstance : (⊥ : Subgroup G).Normal)]
      trivial)
    e.isSimpleGroup
    (by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨e.symm x, e.symm y, fun hc => hxy (by simpa using congrArg e hc)⟩)
  refine ⟨a, haA, ha1, fun x hx => ?_⟩
  have h1 := hmem x hx
  rw [Subgroup.mem_bot] at h1
  exact (inv_mul_eq_one.mp h1).symm

theorem exists_centralizer_section_of_factor {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    {H : Type*} [Group H] [Finite H] {W A N T : Subgroup H} [N.Normal] (hNW : N ≤ W)
    (hTN : T ≤ N) (hTnorm : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T) [IsSimpleGroup T]
    (hTnc : ∃ x y : T, x * y ≠ y * x) (hA : ∀ a ∈ A, a ^ p = 1)
    (hfaith : NoFaithfulSection A W) (hXT : IsSectionOf X T) :
    ∃ a ∈ A, a ≠ 1 ∧ IsSectionOf X ↥(W ⊓ Subgroup.centralizer {a}) := by
  by_cases hAT : A ≤ Subgroup.normalizer (T : Set H)
  · obtain ⟨a, haA, ha1, hcent⟩ := hfaith.exists_centralizing (hTN.trans hNW) hAT hTnc
    refine ⟨a, haA, ha1, ?_⟩
    have hle : T ≤ W ⊓ Subgroup.centralizer {a} := fun x hx =>
      ⟨hNW (hTN hx), mem_centralizer_singleton_of_conj (hcent x hx)⟩
    exact hXT.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  · obtain ⟨a, haA, hmove⟩ := IsConcreteLE.not_le_iff_exists.mp hAT
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hmove (Subgroup.one_mem _)
    obtain ⟨φ, hφinj, hφN, hφfix⟩ := exists_diagonal hp (hA a haA) hTN hTnorm hTnc hmove
    let φ' : T →* ↥(W ⊓ Subgroup.centralizer {a}) := φ.codRestrict _ fun t =>
      ⟨hNW (hφN t), mem_centralizer_singleton_of_conj (hφfix t)⟩
    have hφ' : Function.Injective φ' := fun x y h => hφinj (congrArg Subtype.val h)
    exact ⟨a, haA, ha1, hXT.of_injective φ' hφ'⟩

theorem exists_centralizer_section {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [IsSimpleGroup X]
    (hnc : ∃ x y : X, x * y ≠ y * x) :
    ∀ (n : ℕ) {H : Type u} [Group H] [Finite H] (W A : Subgroup H) [W.Normal],
      Nat.card W = n → (∀ a ∈ A, a ^ p = 1) → Nat.Coprime p (Nat.card W) →
      NoFaithfulSection A W → IsSectionOf X W →
      ∃ a ∈ A, a ≠ 1 ∧ IsSectionOf X ↥(W ⊓ Subgroup.centralizer {a}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H _ _ W A _ hn hA hcop hfaith hXW
    have hW1 : W ≠ ⊥ := by
      rintro rfl
      have := hXW.subsingleton
      obtain ⟨x, y, hxy⟩ := hnc
      exact hxy (Subsingleton.elim _ _)
    obtain ⟨N, ⟨hNnormal, hN1, hNW⟩, hNmin⟩ :=
      (Set.toFinite {M : Subgroup H | M.Normal ∧ M ≠ ⊥ ∧ M ≤ W}).exists_minimal
        ⟨W, inferInstance, hW1, le_rfl⟩
    have hNmin' : ∀ M : Subgroup H, M.Normal → M ≤ N → M = ⊥ ∨ M = N := fun M hM hMN =>
      (em (M = ⊥)).imp id fun hM1 =>
        le_antisymm hMN (hNmin ⟨hM, hM1, hMN.trans hNW⟩ hMN)
    let π : H →* H ⧸ N := QuotientGroup.mk' N
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
    have hker : π.ker = N := QuotientGroup.ker_mk' N
    let ρ : W →* ↥(W.map π) := π.subgroupMap W
    have hρ : Function.Surjective ρ := MonoidHom.subgroupMap_surjective π W
    rcases hXW.of_hom ρ with hXker | hXquot
    ·
      have hmem : ∀ k : ρ.ker, ((k : W) : H) ∈ N := by
        intro k
        have h1 : ρ k = 1 := k.2
        have h2 : π ((k : W) : H) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      let j : ρ.ker →* N := (W.subtype.comp ρ.ker.subtype).codRestrict N hmem
      have hj : Function.Injective j := by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : N => (z : H)) h
      have hXN : IsSectionOf X N := hXker.of_injective j hj
      obtain ⟨r, S, -, hSN, hSsimple, -, hSnormal, e, -⟩ :=
        CFSG.LocalCores.minimal_normal_simple_factors hNnormal hN1 hNmin'
      obtain ⟨i, hi⟩ := IsSectionOf.of_pi hnc (hXN.trans (IsSectionOf.of_mulEquiv e))
      have := hSsimple i
      have hTnc : ∃ x y : S i, x * y ≠ y * x := by
        by_contra hcon
        push Not at hcon
        obtain ⟨x, y, hxy⟩ := hnc
        exact hxy (hi.commutative (fun a b => hcon a b) x y)
      exact exists_centralizer_section_of_factor hp hNW (hSN i)
        (fun m hm t ht => (Subgroup.normal_subgroupOf_iff (hSN i)).mp (hSnormal i) t m ht hm)
        hTnc hA hfaith hi
    ·
      have hNdvd : Nat.card N ∣ Nat.card W := Subgroup.card_dvd_of_le hNW
      have hnormal : (W.map π).Normal := Subgroup.Normal.map inferInstance π hπ
      have hlt : Nat.card (W.map π) < n := by
        have hρninj : ¬ Function.Injective ρ := by
          obtain ⟨m, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN1
          intro hinj
          have h1 : ρ ⟨m, hNW m.2⟩ = ρ 1 := by
            apply Subtype.ext
            have : π m = 1 := (QuotientGroup.eq_one_iff _).mpr m.2
            simpa [ρ] using this
          exact hm1 (Subtype.ext (congrArg (fun w : W => (w : H)) (hinj h1)))
        rw [← hn]
        have := Fintype.ofFinite W
        have := Fintype.ofFinite (W.map π)
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_lt_of_surjective_not_injective ρ hρ hρninj
      have hAQ : ∀ b ∈ A.map π, b ^ p = 1 := by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hA a ha, map_one]
      have hcopQ : Nat.Coprime p (Nat.card (W.map π)) :=
        hcop.of_dvd_right (Subgroup.card_dvd_of_surjective hρ)
      have hfaithQ : NoFaithfulSection (A.map π) (W.map π) :=
        noFaithfulSection_map hNW hA hcop hfaith
      obtain ⟨b, hbA, hb1, hbsec⟩ :=
        ih _ hlt (W.map π) (A.map π) rfl hAQ hcopQ hfaithQ hXquot
      obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp hbA
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hb1 (map_one π)
      have hfix : (W ⊓ Subgroup.centralizer {a}).map π =
          W.map π ⊓ Subgroup.centralizer {π a} :=
        map_inf_centralizer_eq hp hNW (hcop.of_dvd_right hNdvd) (hA a haA)
      rw [← hfix] at hbsec
      exact ⟨a, haA, ha1, hbsec.trans
        (IsSectionOf.of_surjective (π.subgroupMap _) (MonoidHom.subgroupMap_surjective _ _))⟩

end CFSG.SignalizerFunctorTheorem
