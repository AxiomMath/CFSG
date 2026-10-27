module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltForced

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c11_alt_relIndex_of_card {G : Type*} [Group G] [Finite G] {T X : Subgroup G}
    (hTX : T ≤ X) {a k : ℕ} (hT : Nat.card T = a) (hX : Nat.card X = a * k) :
    T.relIndex X = k := by
  have h1 := Subgroup.relIndex_mul_index hTX
  have h2 := Subgroup.card_mul_index T
  have h3 := Subgroup.card_mul_index X
  have hX0 : 0 < X.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have ha : 0 < a := by
    rw [← hT]
    exact Nat.card_pos
  rw [hT] at h2
  rw [hX] at h3
  rw [← h1] at h2
  have h4 : a * (T.relIndex X * X.index) = a * (k * X.index) := by
    rw [h2, ← h3]
    ring
  exact Nat.eq_of_mul_eq_mul_right hX0 (Nat.eq_of_mul_eq_mul_left ha h4)

private lemma s16c11_altcount_inf_stabilizer_eq {G : Type} [Group G] {V : Type} [CommGroup V]
    {ρ : G →* MulAut V} {T X : Subgroup G} {y : V}
    (hTX : T ≤ X) (h3 : T.relIndex X = 3) (hfix : ∀ t ∈ T, ρ t y = y)
    (hmov : ∃ g ∈ X, ρ g y ≠ y) :
    X ⊓ (MulAction.stabilizer (MulAut V) y).comap ρ = T := by
  set S : Subgroup G := X ⊓ (MulAction.stabilizer (MulAut V) y).comap ρ with hS
  have hTS : T ≤ S := fun t ht =>
    Subgroup.mem_inf.2 ⟨hTX ht, Subgroup.mem_comap.2 (by
      rw [MulAction.mem_stabilizer_iff]
      exact hfix t ht)⟩
  have hSX : S ≤ X := inf_le_left
  have hne : ¬ X ≤ S := by
    rintro h
    obtain ⟨g, hgX, hgy⟩ := hmov
    exact hgy (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (h hgX)).2)
  have hmul := Subgroup.relIndex_mul_relIndex T S X hTS hSX
  rw [h3] at hmul
  have h1 : S.relIndex X ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.1 h)
  have hd : S.relIndex X ∣ 3 := ⟨T.relIndex S, by rw [← hmul, mul_comm]⟩
  have h2 : S.relIndex X = 3 := ((Nat.dvd_prime Nat.prime_three).1 hd).resolve_left h1
  rw [h2] at hmul
  have h4 : T.relIndex S = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h4) hTS

private lemma s16c11_altcount_le_of_common {G : Type} [Group G] {T X X' : Subgroup G} {c : G}
    (hTX : T ≤ X) (hTX' : T ≤ X') (h3 : T.relIndex X = 3) (h3' : T.relIndex X' = 3)
    (hcX : c ∈ X) (hcX' : c ∈ X') (hcT : c ∉ T) : X ≤ X' := by
  set K : Subgroup G := X ⊓ X' with hK
  have hTK : T ≤ K := le_inf hTX hTX'
  have hKX : K ≤ X := inf_le_left
  have hcK : c ∈ K := Subgroup.mem_inf.2 ⟨hcX, hcX'⟩
  have hne : T.relIndex K ≠ 1 := by
    intro h
    exact hcT (Subgroup.relIndex_eq_one.1 h hcK)
  have hmul := Subgroup.relIndex_mul_relIndex T K X hTK hKX
  rw [h3] at hmul
  have hdvd : T.relIndex K ∣ 3 := ⟨K.relIndex X, hmul.symm⟩
  have h3K : T.relIndex K = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have hKXrel : K.relIndex X = 1 := by
    rw [h3K] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) (by simpa using hmul)
  exact (Subgroup.relIndex_eq_one.1 hKXrel).trans inf_le_right

theorem s16c11_forcedPairs_ncard_three_of_cover {G : Type} [Group G] [Finite G] {V : Type}
    [CommGroup V] {ρ : G →* MulAut V} {T₁ X₁ X₂ X₃ : Subgroup G} {y₀ a b : V}
    (hT : IsPGroup 2 ↥T₁) (hfix : ∀ t ∈ T₁, ρ t y₀ = y₀)
    (h₁ : T₁ ≤ X₁) (h₂ : T₁ ≤ X₂) (h₃ : T₁ ≤ X₃)
    (s₁ : X₁ ≤ S16C11SetStab ρ {y₀, a, b}) (s₂ : X₂ ≤ S16C11SetStab ρ {y₀, a, b})
    (s₃ : X₃ ≤ S16C11SetStab ρ {y₀, a, b})
    (i₁ : T₁.relIndex X₁ = 3) (i₂ : T₁.relIndex X₂ = 3) (i₃ : T₁.relIndex X₃ = 3)
    (m₁ : ∃ g ∈ X₁, ρ g y₀ ≠ y₀) (m₂ : ∃ g ∈ X₂, ρ g y₀ ≠ y₀) (m₃ : ∃ g ∈ X₃, ρ g y₀ ≠ y₀)
    (d₁₂ : X₁ ≠ X₂) (d₁₃ : X₁ ≠ X₃) (d₂₃ : X₂ ≠ X₃)
    (hcov : ∀ g ∈ S16C11SetStab ρ {y₀, a, b}, g ^ 3 = 1 → ρ g y₀ ≠ y₀ →
      g ∈ X₁ ∨ g ∈ X₂ ∨ g ∈ X₃) :
    (S16C11ForcedPairs ρ T₁ y₀ a b).ncard = 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : S16C11ForcedPairs ρ T₁ y₀ a b =
      ({(y₀, X₁), (y₀, X₂), (y₀, X₃)} : Set (V × Subgroup G)) := by
    ext p
    constructor
    · rintro ⟨hy, hTX, hXS, hrel, hmov⟩
      set X : Subgroup G := p.2 with hX
      have hinf : T₁ ⊓ X = T₁ := inf_eq_left.2 hTX
      have hcardX : Nat.card X = 3 * Nat.card T₁ := by
        have h := Subgroup.relIndex_mul_card (H := T₁) (K := X)
        rw [hinf, hrel] at h
        exact h.symm
      have h3dvd : 3 ∣ Nat.card X := ⟨Nat.card T₁, hcardX⟩
      obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3dvd
      let c : G := (c₀ : G)
      have hcX : c ∈ X := c₀.2
      have hc3 : c ^ 3 = 1 := by
        have h : c₀ ^ 3 = 1 := by
          simpa [hc₀] using pow_orderOf_eq_one c₀
        simpa using congrArg Subtype.val h
      have hcT : c ∉ T₁ := by
        intro hc
        let c₁ : ↥T₁ := ⟨c, hc⟩
        have hordc : orderOf c = 3 := (Subgroup.orderOf_coe c₀).trans hc₀
        have hord1 : orderOf c₁ = 3 := by
          rw [← Subgroup.orderOf_coe c₁]
          exact hordc
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥T₁)).mp hT c₁
        rw [hord1] at hk
        have h3pow : 3 ∣ 2 ^ k := by
          rw [← hk]
        have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3pow
        exact absurd h32 (by norm_num)
      have hstab_eq : X ⊓ (MulAction.stabilizer (MulAut V) y₀).comap ρ = T₁ :=
        s16c11_altcount_inf_stabilizer_eq hTX hrel hfix hmov
      have hcMov : ρ c y₀ ≠ y₀ := by
        intro hcy
        have hcStab : c ∈ X ⊓ (MulAction.stabilizer (MulAut V) y₀).comap ρ :=
          Subgroup.mem_inf.2 ⟨hcX, Subgroup.mem_comap.2 (MulAction.mem_stabilizer_iff.2 hcy)⟩
        exact hcT (hstab_eq ▸ hcStab)
      have hcS : c ∈ S16C11SetStab ρ {y₀, a, b} := hXS hcX
      rcases hcov c hcS hc3 hcMov with hcX₁ | hcX₂ | hcX₃
      · have hle : X ≤ X₁ :=
          s16c11_altcount_le_of_common hTX h₁ hrel i₁ hcX hcX₁ hcT
        have hge : X₁ ≤ X :=
          s16c11_altcount_le_of_common h₁ hTX i₁ hrel hcX₁ hcX hcT
        have hXeq : p.2 = X₁ := hX.symm.trans (le_antisymm hle hge)
        have hp : p = (y₀, X₁) := Prod.ext hy hXeq
        rw [hp]
        simp
      · have hle : X ≤ X₂ :=
          s16c11_altcount_le_of_common hTX h₂ hrel i₂ hcX hcX₂ hcT
        have hge : X₂ ≤ X :=
          s16c11_altcount_le_of_common h₂ hTX i₂ hrel hcX₂ hcX hcT
        have hXeq : p.2 = X₂ := hX.symm.trans (le_antisymm hle hge)
        have hp : p = (y₀, X₂) := Prod.ext hy hXeq
        rw [hp]
        simp
      · have hle : X ≤ X₃ :=
          s16c11_altcount_le_of_common hTX h₃ hrel i₃ hcX hcX₃ hcT
        have hge : X₃ ≤ X :=
          s16c11_altcount_le_of_common h₃ hTX i₃ hrel hcX₃ hcX hcT
        have hXeq : p.2 = X₃ := hX.symm.trans (le_antisymm hle hge)
        have hp : p = (y₀, X₃) := Prod.ext hy hXeq
        rw [hp]
        simp
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨rfl, h₁, s₁, i₁, m₁⟩
      · exact ⟨rfl, h₂, s₂, i₂, m₂⟩
      · exact ⟨rfl, h₃, s₃, i₃, m₃⟩
  rw [hsub, Set.ncard_eq_three]
  refine ⟨(y₀, X₁), (y₀, X₂), (y₀, X₃), ?_, ?_, ?_, rfl⟩
  · intro h
    exact d₁₂ (congrArg Prod.snd h)
  · intro h
    exact d₁₃ (congrArg Prod.snd h)
  · intro h
    exact d₂₃ (congrArg Prod.snd h)

theorem s16c11_alt_overgroup_of_checks {n : ℕ} (gens : List ↥(alternatingGroup (Fin n)))
    (c : ↥(alternatingGroup (Fin n))) (m e m' : ℕ)
    (hfix : S16C11AltWords gens (m + 1) = S16C11AltWords gens m)
    (hcard : (S16C11AltWords gens m).card = 2 ^ e)
    (hfix' : S16C11AltWords (gens ++ [c]) (m' + 1) = S16C11AltWords (gens ++ [c]) m')
    (hcard' : (S16C11AltWords (gens ++ [c]) m').card = 2 ^ e * 3)
    {x₀ xa xb : Fin n → ZMod 2} (h₀ : ∑ i, x₀ i = 0) (ha : ∑ i, xa i = 0) (hb : ∑ i, xb i = 0)
    (hstab : ∀ g ∈ gens ++ [c], S16C11AltTriple x₀ xa xb (g : Equiv.Perm (Fin n)))
    (hmov : ¬ S16C11AltEqv x₀ (S16C11AltPact (c : Equiv.Perm (Fin n)) x₀)) :
    S16C11AltGrp gens ≤ S16C11AltGrp (gens ++ [c]) ∧
      S16C11AltGrp (gens ++ [c]) ≤ S16C11SetStab (S16C11AltAct n)
        {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb} ∧
      (S16C11AltGrp gens).relIndex (S16C11AltGrp (gens ++ [c])) = 3 ∧
      ∃ g ∈ S16C11AltGrp (gens ++ [c]),
        S16C11AltAct n g (S16C11AltCls n x₀) ≠ S16C11AltCls n x₀ := by
  have hsub : S16C11AltGrp gens ≤ S16C11AltGrp (gens ++ [c]) := by
    refine Subgroup.closure_mono ?_
    intro g hg
    exact List.mem_append_left [c] hg
  have hstabS : S16C11AltGrp (gens ++ [c]) ≤ S16C11SetStab (S16C11AltAct n)
      {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb} := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    exact (s16c11_alt_mem_setStab_iff h₀ ha hb g).mpr (hstab g hg)
  have hcardT : Nat.card (S16C11AltGrp gens) = 2 ^ e := by
    rw [S16C11AltGrp, s16c11_alt_card_closure gens m hfix, hcard]
  have hcardX : Nat.card (S16C11AltGrp (gens ++ [c])) = 2 ^ e * 3 := by
    rw [S16C11AltGrp, s16c11_alt_card_closure (gens ++ [c]) m' hfix', hcard']
  have hrel : (S16C11AltGrp gens).relIndex (S16C11AltGrp (gens ++ [c])) = 3 :=
    s16c11_alt_relIndex_of_card hsub hcardT hcardX
  have hcX : c ∈ S16C11AltGrp (gens ++ [c]) :=
    Subgroup.subset_closure (List.mem_append_right gens (by simp))
  have hmovC : S16C11AltAct n c (S16C11AltCls n x₀) ≠ S16C11AltCls n x₀ := by
    intro h
    exact hmov ((s16c11_alt_fixed_iff c h₀).mp h)
  exact ⟨hsub, hstabS, hrel, c, hcX, hmovC⟩

theorem s16c11_alt_grp_ne_of_mem {n : ℕ} (gens₁ gens₂ : List ↥(alternatingGroup (Fin n)))
    (m : ℕ) (hfix : S16C11AltWords gens₁ (m + 1) = S16C11AltWords gens₁ m)
    {g : ↥(alternatingGroup (Fin n))} (hg : g ∈ gens₂)
    (hn : (g : Equiv.Perm (Fin n)) ∉ (S16C11AltWords gens₁ m).image Subtype.val) :
    S16C11AltGrp gens₁ ≠ S16C11AltGrp gens₂ := by
  intro hEq
  have hg2 : g ∈ S16C11AltGrp gens₂ := Subgroup.subset_closure hg
  rw [← hEq] at hg2
  have hgw : g ∈ S16C11AltWords gens₁ m :=
    (s16c11_alt_mem_closure_iff gens₁ m hfix g).mp hg2
  exact hn (Finset.mem_image_of_mem Subtype.val hgw)

theorem s16c11_alt_cover_of_check {n : ℕ}
    (gens₁ gens₂ gens₃ : List ↥(alternatingGroup (Fin n))) (m₁ m₂ m₃ : ℕ)
    {x₀ xa xb : Fin n → ZMod 2} (h₀ : ∑ i, x₀ i = 0) (ha : ∑ i, xa i = 0) (hb : ∑ i, xb i = 0)
    (h : ∀ g : Equiv.Perm (Fin n), S16C11AltTriple x₀ xa xb g → g ^ 3 = 1 →
      ¬ S16C11AltEqv x₀ (S16C11AltPact g x₀) → Equiv.Perm.sign g = 1 →
      g ∈ (S16C11AltWords gens₁ m₁).image Subtype.val ∨
        g ∈ (S16C11AltWords gens₂ m₂).image Subtype.val ∨
        g ∈ (S16C11AltWords gens₃ m₃).image Subtype.val) :
    ∀ g ∈ S16C11SetStab (S16C11AltAct n)
        {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb},
      g ^ 3 = 1 → S16C11AltAct n g (S16C11AltCls n x₀) ≠ S16C11AltCls n x₀ →
      g ∈ S16C11AltGrp gens₁ ∨ g ∈ S16C11AltGrp gens₂ ∨ g ∈ S16C11AltGrp gens₃ := by
  intro g hgS hg3 hmov
  let g' : ↥(alternatingGroup (Fin n)) := g
  have hgS' : g' ∈ S16C11SetStab (S16C11AltAct n)
      {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb} := hgS
  have htriple : S16C11AltTriple x₀ xa xb (g' : Equiv.Perm (Fin n)) :=
    (s16c11_alt_mem_setStab_iff h₀ ha hb g').mp hgS'
  have hg3' : (g' : Equiv.Perm (Fin n)) ^ 3 = 1 := by
    have h3' : g' ^ 3 = 1 := hg3
    simpa [Subgroup.coe_pow] using congrArg Subtype.val h3'
  have hnoneqv : ¬ S16C11AltEqv x₀ (S16C11AltPact (g' : Equiv.Perm (Fin n)) x₀) := by
    intro h
    exact hmov ((s16c11_alt_fixed_iff g' h₀).mpr h)
  have hsign : Equiv.Perm.sign (g' : Equiv.Perm (Fin n)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp g'.2
  rcases h (g' : Equiv.Perm (Fin n)) htriple hg3' hnoneqv hsign with hmem | hmem | hmem
  · obtain ⟨t, ht, htg⟩ := Finset.mem_image.1 hmem
    have htg' : t = g' := Subtype.ext htg
    have hmemg : g' ∈ S16C11AltGrp gens₁ := by
      rw [← htg']
      exact s16c11_alt_words_subset_closure gens₁ m₁ ht
    exact Or.inl hmemg
  · obtain ⟨t, ht, htg⟩ := Finset.mem_image.1 hmem
    have htg' : t = g' := Subtype.ext htg
    have hmemg : g' ∈ S16C11AltGrp gens₂ := by
      rw [← htg']
      exact s16c11_alt_words_subset_closure gens₂ m₂ ht
    exact Or.inr (Or.inl hmemg)
  · obtain ⟨t, ht, htg⟩ := Finset.mem_image.1 hmem
    have htg' : t = g' := Subtype.ext htg
    have hmemg : g' ∈ S16C11AltGrp gens₃ := by
      rw [← htg']
      exact s16c11_alt_words_subset_closure gens₃ m₃ ht
    exact Or.inr (Or.inr hmemg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
