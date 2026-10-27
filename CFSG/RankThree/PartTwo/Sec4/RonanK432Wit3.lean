module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCount
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

@[expose] def Wit3 {G : Type*} [Group G] (N : Subgroup G) (a : G) : Prop :=
  ∃ y ∈ N, (y * a * y⁻¹) * a = a * (y * a * y⁻¹) ∧ y * a * y⁻¹ ∉ Subgroup.zpowers a

theorem Wit3.conj {G : Type*} [Group G] {N : Subgroup G} {a : G} (h : Wit3 N a) (g : G)
    (hg : ∀ y ∈ N, g * y * g⁻¹ ∈ N) : Wit3 N (g * a * g⁻¹) := by
  obtain ⟨y, hy, hc, hn⟩ := h
  refine ⟨g * y * g⁻¹, hg y hy, ?_, ?_⟩
  · calc g * y * g⁻¹ * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * a * g⁻¹)
        = g * ((y * a * y⁻¹) * a) * g⁻¹ := by group
      _ = g * (a * (y * a * y⁻¹)) * g⁻¹ := by rw [hc]
      _ = g * a * g⁻¹ * (g * y * g⁻¹ * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹) := by group
  · intro hmem
    apply hn
    have e : g * y * g⁻¹ * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * a * y⁻¹) * g⁻¹ := by group
    rw [e] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hpow : (g * a * g⁻¹) ^ k = g * a ^ k * g⁻¹ := by
      have := conj_zpow (a := g) (b := a) (i := k)
      simpa using this
    rw [hpow] at hk
    have := congrArg (fun t => g⁻¹ * t * g) hk
    simpa [mul_assoc] using this

theorem wit3_all_of_sylow {G : Type} [Group G] [Finite G] (N : Subgroup G)
    (hN : ∀ g : G, ∀ y ∈ N, g * y * g⁻¹ ∈ N) (P : Subgroup G) (n : ℕ)
    (hP : Nat.card P = 3 ^ n) (hG : ¬ 3 ^ (n + 1) ∣ Nat.card G)
    (h : ∀ σ ∈ P, σ ≠ 1 → σ ^ 3 = 1 → Wit3 N σ) :
    ∀ a : G, a ≠ 1 → a ^ 3 = 1 → Wit3 N a := by
  intro a ha1 ha3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfacS : (Nat.card G).factorization 3 = n := by
    have h3 : 3 ^ n ∣ Nat.card G := hP ▸ Subgroup.card_subgroup_dvd_card P
    have a1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hGne).mp h3
    have b1 : ¬ n + 1 ≤ (Nat.card G).factorization 3 := fun h' =>
      hG ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hGne).mpr h')
    omega
  let Q₀ : Sylow 3 G := Sylow.ofCard P (by rw [hP, hfacS])
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hpg : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao]; simp)
  obtain ⟨R, hR⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₀ R
  have hamem : a ∈ g • Q₀ := by
    rw [hg]
    exact hR (Subgroup.mem_zpowers a)
  have hσ : g⁻¹ * a * g ∈ P := by
    have := (mem_smul_sylow_iff (P := Q₀) (g := g) (y := a)).mp hamem
    exact this
  have hσ1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    have := congrArg (fun t => g * t * g⁻¹) h1
    simpa [mul_assoc] using this
  have hσ3 : (g⁻¹ * a * g) ^ 3 = 1 := by
    have : (g⁻¹ * a * g) ^ 3 = g⁻¹ * a ^ 3 * g := by
      have := conj_pow (a := g⁻¹) (b := a) (i := 3)
      simpa using this
    rw [this, ha3]
    group
  have hw := (h _ hσ hσ1 hσ3).conj g (hN g)
  have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  rwa [e] at hw

theorem wit3_of_conj_ne {G : Type*} [Group G] {N : Subgroup G} {a y : G} (hy : y ∈ N)
    (ha : a ^ 3 = 1) (hc : (y * a * y⁻¹) * a = a * (y * a * y⁻¹)) (h1 : y * a * y⁻¹ ≠ 1)
    (h2 : y * a * y⁻¹ ≠ a) (h3 : y * a * y⁻¹ ≠ a⁻¹) : Wit3 N a := by
  refine ⟨y, hy, hc, fun hmem => ?_⟩
  rcases mem_zpowers_cases_of_pow_three ha hmem with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

theorem wit3_subgroupOf {Γ : Type*} [Group Γ] {G N : Subgroup Γ} (hNG : N ≤ G) {σ : Γ}
    (hσ : σ ∈ G) (h : Wit3 N σ) : Wit3 (N.subgroupOf G) (⟨σ, hσ⟩ : G) := by
  obtain ⟨y, hy, hc, hn⟩ := h
  refine ⟨⟨y, hNG hy⟩, Subgroup.mem_subgroupOf.mpr hy, Subtype.ext hc, fun hmem => hn ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem wit3_of_subgroupOf {Γ : Type*} [Group Γ] {G N : Subgroup Γ} {σ : G}
    (h : Wit3 (N.subgroupOf G) σ) : Wit3 N (σ : Γ) := by
  obtain ⟨y, hy, hc, hn⟩ := h
  refine ⟨(y : Γ), Subgroup.mem_subgroupOf.mp hy, congrArg Subtype.val hc, fun hmem => hn ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  simpa using hk

theorem wit3_top_of_subgroupOf {Γ : Type*} [Group Γ] {A N : Subgroup Γ} (hNA : N ≤ A) {σ : Γ}
    (hσ : σ ∈ A) (h : Wit3 N σ) : Wit3 (⊤ : Subgroup A) (⟨σ, hσ⟩ : A) := by
  obtain ⟨y, hy, hc, hn⟩ := h
  refine ⟨⟨y, hNA hy⟩, Subgroup.mem_top _, Subtype.ext hc, fun hmem => hn ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem card_subgroupOf_eq_of_le {Γ : Type*} [Group Γ] {X Y : Subgroup Γ} (h : X ≤ Y) :
    Nat.card (X.subgroupOf Y) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem wit3_all_of_sylow_sub {Γ : Type} [Group Γ] (G N P : Subgroup Γ) [Finite G]
    (hNle : N ≤ G) (hNG : ∀ g ∈ G, ∀ y ∈ N, g * y * g⁻¹ ∈ N) (hPG : P ≤ G) (n : ℕ)
    (hP : Nat.card P = 3 ^ n) (hG : ¬ 3 ^ (n + 1) ∣ Nat.card G)
    (h : ∀ σ ∈ P, σ ≠ 1 → σ ^ 3 = 1 → Wit3 N σ) :
    ∀ a ∈ G, a ≠ 1 → a ^ 3 = 1 → Wit3 N a := by
  have hP' : Nat.card (P.subgroupOf G) = 3 ^ n := by
    rw [card_subgroupOf_eq_of_le hPG, hP]
  have key := wit3_all_of_sylow (N.subgroupOf G)
    (fun g y hy => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hNG g.1 g.2 y.1 hy)
    (P.subgroupOf G) n hP' hG (fun σ hσ hσ1 hσ3 => by
      have hσ' : (σ : Γ) ∈ P := Subgroup.mem_subgroupOf.mp hσ
      have h1 : (σ : Γ) ≠ 1 := fun h' => hσ1 (Subtype.ext h')
      have h3 : (σ : Γ) ^ 3 = 1 := by simpa using congrArg Subtype.val hσ3
      exact wit3_subgroupOf hNle σ.2 (h _ hσ' h1 h3))
  intro a haG ha1 ha3
  have := key ⟨a, haG⟩ (fun h' => ha1 (by simpa using congrArg Subtype.val h'))
    (Subtype.ext (by simpa using ha3))
  exact wit3_of_subgroupOf this

theorem listRow_of_wit3 {S : Type} [Group S] [Finite S]
    (h : ∀ a : S, a ≠ 1 → a ^ 3 = 1 → Wit3 ⊤ a) : ListRow S := by
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  obtain ⟨y, -, hc, hn⟩ := h z hz1 hz3
  exact not_weaklyClosed_of_commute_conj (g := y) hc hn

theorem listRow_of_wit3_sub {Γ : Type} [Group Γ] {N A : Subgroup Γ} [Finite N] (hNA : N ≤ A)
    (h : ∀ a ∈ A, a ≠ 1 → a ^ 3 = 1 → Wit3 N a) : ListRow ↥N := by
  refine listRow_of_wit3 fun z hz1 hz3 => ?_
  have hz1' : (z : Γ) ≠ 1 := fun h' => hz1 (Subtype.ext h')
  have hz3' : (z : Γ) ^ 3 = 1 := by simpa using congrArg Subtype.val hz3
  exact wit3_top_of_subgroupOf (le_refl N) z.2 (h _ (hNA z.2) hz1' hz3')

theorem outerRow_of_wit3 {S : Type} [Group S] [Finite S] {A : Type} [Group A]
    (φ : A ≃* MulAut S) (N : Subgroup A)
    (hN : ∀ y ∈ N, φ y ∈ (MulAut.conj : S →* MulAut S).range)
    (h : ∀ a : A, a ≠ 1 → a ^ 3 = 1 → Wit3 N a) : OuterRow S := by
  intro _ σ hσ hout
  have ha3 : (φ.symm σ) ^ 3 = 1 := by
    rw [← map_pow, hσ, map_one]
  have ha1 : φ.symm σ ≠ 1 := by
    intro h1
    apply hout
    have : σ = 1 := by
      have := congrArg φ h1
      simpa using this
    rw [this]
    exact (MulAut.conj : S →* MulAut S).range.one_mem
  obtain ⟨y, hy, hc, hn⟩ := h _ ha1 ha3
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hN y hy)
  refine not_autWeaklyClosed_of_commute_conj (σ := σ) (x := x) ?_ ?_
  · rw [hx]
    have := congrArg φ hc
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at this
    exact this
  · rw [hx]
    intro hmem
    apply hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, φ.injective ?_⟩
    rw [map_zpow, map_mul, map_mul, map_inv]
    simpa using hk

theorem outerRow_of_wit3_sub {S : Type} [Group S] [Finite S] {Γ : Type} [Group Γ]
    {A N : Subgroup Γ} (hNA : N ≤ A) (φ : ↥A ≃* MulAut S)
    (hN : ∀ y : ↥A, (y : Γ) ∈ N → φ y ∈ (MulAut.conj : S →* MulAut S).range)
    (h : ∀ a ∈ A, a ≠ 1 → a ^ 3 = 1 → Wit3 N a) : OuterRow S := by
  refine outerRow_of_wit3 φ (N.subgroupOf A) (fun y hy => hN y (Subgroup.mem_subgroupOf.mp hy))
    fun a ha1 ha3 => ?_
  have h1 : (a : Γ) ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have h3 : (a : Γ) ^ 3 = 1 := by simpa using congrArg Subtype.val ha3
  exact wit3_subgroupOf hNA a.2 (h _ a.2 h1 h3)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
