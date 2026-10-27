module

public import CFSG.OddTranspositions.SixTen
public import CFSG.OddTranspositions.SixNineUnconditional
public import CFSG.OddTranspositions.FaithfulBlocks

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def FixesPerpBlocks (D : Set G) (x : G) (β : Set G) : Prop :=
  ∀ γ ∈ perp D β, (fun y => x * y * x⁻¹) '' γ = γ

@[expose] def PetersenAt (D δ : Set G) : Prop :=
  (∀ θ₁ ∈ Dalpha D δ, ∀ θ₂ ∈ Dalpha D δ, ∀ θ₃ ∈ Dalpha D δ,
      θ₂ ∈ Dalpha D θ₁ → θ₃ ∈ Dalpha D θ₁ → θ₃ ∈ Dalpha D θ₂ → False) ∧
  (∀ θ₁ ∈ Dalpha D δ, ∀ θ₂ ∈ Dalpha D δ, θ₁ ≠ θ₂ → θ₂ ∉ Dalpha D θ₁ →
      ∃! θ₃, θ₃ ∈ Dalpha D δ ∧ θ₃ ∈ Dalpha D θ₁ ∧ θ₃ ∈ Dalpha D θ₂)

theorem Dalpha_symm {θ₁ θ₂ : Set G} (h : θ₂ ∈ Dalpha D θ₁) (h₁ : θ₁ ⊆ D) :
    θ₁ ∈ Dalpha D θ₂ :=
  ⟨mem_blockClass_of_mem_blockClass h.1 (mem_blockClass_self θ₁), h₁, h.2.2.1.symm,
    fun z hz w hw => (h.2.2.2 w hw z hz).symm⟩

theorem image_mem_Dalpha_of_fix (hN : IsNormalSet D) {x : G} {ε θ : Set G}
    (hθ : θ ∈ Dalpha D ε) (hε : (fun y => x * y * x⁻¹) '' ε = ε) :
    (fun y => x * y * x⁻¹) '' θ ∈ Dalpha D ε := by
  have := Dalpha.conj hN hθ x
  rwa [hε] at this

theorem sixTen_of_petersen (hC : HypothesisC D) {x : G}
    (hpet : ∀ δ ∈ blockClass hC.alpha, PetersenAt D δ)
    (hbase : ∀ β ∈ perp D hC.alpha, FixesPerpBlocks D x β) :
    ActsTriviallyOnBlocks hC.alpha x := by
  classical
  have hN := hC.setup.normal
  have hblock := hC.isBlock_alpha
  have hsubD : ∀ θ ∈ blockClass hC.alpha, θ ⊆ D := fun θ hθ =>
    subset_of_mem_blockClass hN hblock hθ
  have main : ∀ n, ∀ δ (_ : δ ∈ blockClass hC.alpha),
      blockDist hC hC.alpha δ = n → FixesPerpBlocks D x δ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro δ hδ hdist
      have hαc := mem_blockClass_self hC.alpha
      by_cases h0 : blockDist hC hC.alpha δ = 0
      · have hδα : δ = hC.alpha := ((blockDist_eq_zero hC hαc hδ).mp h0).symm
        rw [hδα]; exact hbase _ (perp_self_mem D _)
      by_cases h1 : blockDist hC hC.alpha δ = 1
      · have hadj : (blockGraph D hC.alpha).Adj ⟨hC.alpha, hαc⟩ ⟨δ, hδ⟩ := by
          apply SimpleGraph.dist_eq_one_iff_adj.mp
          rwa [blockDist_of_mem hC hαc hδ] at h1
        exact hbase δ (mem_perp_iff.mpr (Or.inl ((blockGraph_adj_iff hN hblock).mp hadj.symm)))
      have hgt : 1 < blockDist hC hC.alpha δ := by omega
      obtain ⟨β, hβ, γ, hγ, hadjβγ, hadjγδ, hdβ, hdγ⟩ := exists_geodesic_prefix hC hδ hgt
      have hβγ : β ∈ Dalpha D γ := (blockGraph_adj_iff hN hblock).mp hadjβγ
      have hγδ : γ ∈ Dalpha D δ := (blockGraph_adj_iff hN hblock).mp hadjγδ
      have hδγ : δ ∈ Dalpha D γ := Dalpha_symm hγδ (hsubD δ hδ)
      have fixβ := ih _ (by omega) β hβ rfl
      have fixγ := ih _ (by omega) γ hγ rfl
      have hβδ : β ≠ δ := by
        rintro rfl; omega
      have hnδβ : δ ∉ Dalpha D β := by
        intro h
        have hadj : (blockGraph D hC.alpha).Adj ⟨β, hβ⟩ ⟨δ, hδ⟩ :=
          (blockGraph_adj_iff hN hblock).mpr (Dalpha_symm h (hsubD β hβ))
        have := blockDist_triangle hC hαc hβ hδ
        rw [blockDist_eq_one_of_adj hC hβ hδ hadj] at this
        omega
      obtain ⟨σ, ⟨hσγ, hσβ, hσδ⟩, -⟩ := (hpet γ hγ).2 β hβγ δ hδγ hβδ hnδβ
      have hσc : σ ∈ blockClass hC.alpha := mem_blockClass_trans hγ hσγ.1
      have hdσ : blockDist hC hC.alpha σ < blockDist hC hC.alpha δ := by
        have hadj : (blockGraph D hC.alpha).Adj ⟨β, hβ⟩ ⟨σ, hσc⟩ :=
          (blockGraph_adj_iff hN hblock).mpr (Dalpha_symm hσβ (hsubD β hβ))
        have := blockDist_triangle hC hαc hβ hσc
        rw [blockDist_eq_one_of_adj hC hβ hσc hadj] at this
        omega
      have fixσ := ih _ (by omega) σ hσc rfl
      have hxδ : (fun y => x * y * x⁻¹) '' δ = δ := fixγ δ (mem_perp_iff.mpr (Or.inl hδγ))
      intro θ hθ
      rcases mem_perp_iff.mp hθ with hθδ | rfl
      swap
      · exact hxδ
      by_cases hs : θ ∈ perp D σ
      · exact fixσ θ hs
      by_cases hg : θ ∈ perp D γ
      · exact fixγ θ hg
      have hθc : θ ∈ blockClass hC.alpha := mem_blockClass_trans hδ hθδ.1
      have hθσ : θ ≠ σ := fun h => hs (mem_perp_iff.mpr (Or.inr h))
      have hθγ : θ ≠ γ := fun h => hg (mem_perp_iff.mpr (Or.inr h))
      have hσθ : σ ∉ Dalpha D θ := fun h =>
        hs (mem_perp_iff.mpr (Or.inl (Dalpha_symm h (hsubD θ hθc))))
      have hγθ : γ ∉ Dalpha D θ := fun h =>
        hg (mem_perp_iff.mpr (Or.inl (Dalpha_symm h (hsubD θ hθc))))
      have hσδ' : σ ∈ Dalpha D δ := hσδ
      obtain ⟨hlam, hmu⟩ := hpet δ hδ
      obtain ⟨ε₁, ⟨hε₁δ, hε₁θ, hε₁σ⟩, -⟩ := hmu θ hθδ σ hσδ' hθσ hσθ
      obtain ⟨ε₂, ⟨hε₂δ, hε₂θ, hε₂γ⟩, -⟩ := hmu θ hθδ γ hγδ hθγ hγθ
      have hε₁₂ : ε₁ ≠ ε₂ := by
        rintro rfl
        exact hlam γ hγδ σ hσδ' ε₁ hε₁δ hσγ hε₂γ hε₁σ
      have hε₂₁ : ε₂ ∉ Dalpha D ε₁ := fun h => hlam θ hθδ ε₁ hε₁δ ε₂ hε₂δ hε₁θ hε₂θ h
      obtain ⟨ζ, -, huniq⟩ := hmu ε₁ hε₁δ ε₂ hε₂δ hε₁₂ hε₂₁
      have hε₁c : ε₁ ∈ blockClass hC.alpha := mem_blockClass_trans hδ hε₁δ.1
      have hε₂c : ε₂ ∈ blockClass hC.alpha := mem_blockClass_trans hδ hε₂δ.1
      have hxε₁ : (fun y => x * y * x⁻¹) '' ε₁ = ε₁ :=
        fixσ ε₁ (mem_perp_iff.mpr (Or.inl hε₁σ))
      have hxε₂ : (fun y => x * y * x⁻¹) '' ε₂ = ε₂ :=
        fixγ ε₂ (mem_perp_iff.mpr (Or.inl hε₂γ))
      have h1 := huniq θ ⟨hθδ, Dalpha_symm hε₁θ (hsubD θ hθc),
        Dalpha_symm hε₂θ (hsubD θ hθc)⟩
      have h2 := huniq ((fun y => x * y * x⁻¹) '' θ)
        ⟨image_mem_Dalpha_of_fix hN hθδ hxδ,
          image_mem_Dalpha_of_fix hN (Dalpha_symm hε₁θ (hsubD θ hθc)) hxε₁,
          image_mem_Dalpha_of_fix hN (Dalpha_symm hε₂θ (hsubD θ hθc)) hxε₂⟩
      exact h2.trans h1.symm
  intro δ hδ
  exact main _ δ hδ rfl δ (perp_self_mem D δ)

theorem image_conj_inv_image_conj (k : G) (S : Set G) :
    (fun x => k⁻¹ * x * k⁻¹⁻¹) '' ((fun x => k * x * k⁻¹) '' S) = S := by
  ext y
  simp only [Set.image_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; convert hz using 1; group
  · intro hy; exact ⟨y, hy, by group⟩

theorem image_conj_image_conj_inv (k : G) (S : Set G) :
    (fun x => k * x * k⁻¹) '' ((fun x => k⁻¹ * x * k⁻¹⁻¹) '' S) = S := by
  ext y
  simp only [Set.image_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; convert hz using 1; group
  · intro hy; exact ⟨y, hy, by group⟩

theorem PetersenAt.conj (hN : IsNormalSet D) {α : Set G} (h : PetersenAt D α) (g : G) :
    PetersenAt D ((fun x => g * x * g⁻¹) '' α) := by
  classical
  have back : ∀ {ε θ : Set G}, θ ∈ Dalpha D ((fun x => g * x * g⁻¹) '' ε) →
      (fun x => g⁻¹ * x * g⁻¹⁻¹) '' θ ∈ Dalpha D ε := by
    intro ε θ hθ
    have := Dalpha.conj hN hθ g⁻¹
    rwa [image_conj_inv_image_conj] at this
  have back' : ∀ {ε θ : Set G}, θ ∈ Dalpha D ε →
      (fun x => g⁻¹ * x * g⁻¹⁻¹) '' θ ∈ Dalpha D ((fun x => g⁻¹ * x * g⁻¹⁻¹) '' ε) :=
    fun hθ => Dalpha.conj hN hθ g⁻¹
  have fwd : ∀ {ε θ : Set G}, θ ∈ Dalpha D ((fun x => g⁻¹ * x * g⁻¹⁻¹) '' ε) →
      (fun x => g * x * g⁻¹) '' θ ∈ Dalpha D ε := by
    intro ε θ hθ
    have := Dalpha.conj hN hθ g
    rwa [image_conj_image_conj_inv] at this
  obtain ⟨hlam, hmu⟩ := h
  refine ⟨?_, ?_⟩
  · intro θ₁ h₁ θ₂ h₂ θ₃ h₃ h₁₂ h₁₃ h₂₃
    exact hlam _ (back h₁) _ (back h₂) _ (back h₃) (back' h₁₂) (back' h₁₃) (back' h₂₃)
  · intro θ₁ h₁ θ₂ h₂ hne hn
    have hne' : (fun x => g⁻¹ * x * g⁻¹⁻¹) '' θ₁ ≠ (fun x => g⁻¹ * x * g⁻¹⁻¹) '' θ₂ := by
      intro h
      apply hne
      rw [← image_conj_image_conj_inv g θ₁, h, image_conj_image_conj_inv]
    have hn' : (fun x => g⁻¹ * x * g⁻¹⁻¹) '' θ₂ ∉
        Dalpha D ((fun x => g⁻¹ * x * g⁻¹⁻¹) '' θ₁) := by
      intro h'
      apply hn
      have := fwd h'
      rwa [image_conj_image_conj_inv] at this
    obtain ⟨ζ, ⟨hζα, hζ₁, hζ₂⟩, huniq⟩ := hmu _ (back h₁) _ (back h₂) hne' hn'
    refine ⟨(fun x => g * x * g⁻¹) '' ζ, ⟨fwd (by rwa [image_conj_inv_image_conj]),
      fwd hζ₁, fwd hζ₂⟩, ?_⟩
    rintro ζ' ⟨h1, h2, h3⟩
    have : (fun x => g⁻¹ * x * g⁻¹⁻¹) '' ζ' = ζ := huniq _ ⟨back h1, back' h2, back' h3⟩
    rw [← this, image_conj_image_conj_inv]

abbrev Pair5 : Type := {s : Finset (Fin 5) // s.card = 2}

theorem pair5_triangle_free : ∀ p q r : Pair5, Disjoint p.1 q.1 → Disjoint p.1 r.1 →
    Disjoint q.1 r.1 → False := by decide

theorem pair5_mu_exists : ∀ p q : Pair5, p ≠ q → ¬ Disjoint p.1 q.1 →
    ∃ r : Pair5, Disjoint p.1 r.1 ∧ Disjoint q.1 r.1 := by decide

theorem pair5_mu_unique : ∀ p q r r' : Pair5, ¬ Disjoint p.1 q.1 → Disjoint p.1 r.1 →
    Disjoint q.1 r.1 → Disjoint p.1 r'.1 → Disjoint q.1 r'.1 → p ≠ q → r = r' := by decide

theorem petersenAt_of_model {δ : Set G} (Φ : Set G → Pair5)
    (hsurj : ∀ p, ∃ θ ∈ Dalpha D δ, Φ θ = p)
    (hinj : ∀ θ₁ ∈ Dalpha D δ, ∀ θ₂ ∈ Dalpha D δ, Φ θ₁ = Φ θ₂ → θ₁ = θ₂)
    (hadj : ∀ θ₁ ∈ Dalpha D δ, ∀ θ₂ ∈ Dalpha D δ,
      (θ₂ ∈ Dalpha D θ₁ ↔ Disjoint (Φ θ₁).1 (Φ θ₂).1)) :
    PetersenAt D δ := by
  refine ⟨?_, ?_⟩
  · intro θ₁ h₁ θ₂ h₂ θ₃ h₃ h₁₂ h₁₃ h₂₃
    exact pair5_triangle_free _ _ _ ((hadj _ h₁ _ h₂).mp h₁₂) ((hadj _ h₁ _ h₃).mp h₁₃)
      ((hadj _ h₂ _ h₃).mp h₂₃)
  · intro θ₁ h₁ θ₂ h₂ hne hn
    have hne' : Φ θ₁ ≠ Φ θ₂ := fun h => hne (hinj _ h₁ _ h₂ h)
    have hn' : ¬ Disjoint (Φ θ₁).1 (Φ θ₂).1 := fun h => hn ((hadj _ h₁ _ h₂).mpr h)
    obtain ⟨r, hr₁, hr₂⟩ := pair5_mu_exists _ _ hne' hn'
    obtain ⟨θ₃, h₃, rfl⟩ := hsurj r
    refine ⟨θ₃, ⟨h₃, (hadj _ h₁ _ h₃).mpr hr₁, (hadj _ h₂ _ h₃).mpr hr₂⟩, ?_⟩
    rintro θ ⟨hθ, hθ₁, hθ₂⟩
    exact hinj _ hθ _ h₃ (pair5_mu_unique _ _ _ _ hn' ((hadj _ h₁ _ hθ).mp hθ₁)
      ((hadj _ h₂ _ hθ).mp hθ₂) hr₁ hr₂ hne')

section S5Model

open Equiv

theorem swap_commute_fin5 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b * swap c d = swap c d * swap a b → swap a b ≠ swap c d →
    Disjoint ({a, b} : Finset (Fin 5)) {c, d} := by decide

theorem swap_disjoint_commute_fin5 : ∀ a b c d : Fin 5,
    Disjoint ({a, b} : Finset (Fin 5)) {c, d} → swap a b * swap c d = swap c d * swap a b := by
  decide

theorem exists_swap_not_commute_fin5 : ∀ a b : Fin 5, a ≠ b → ∃ c d : Fin 5, c ≠ d ∧
    swap a b * swap c d ≠ swap c d * swap a b := by decide

theorem isSwap_of_mul_self_of_sign {σ : Perm (Fin 5)} (h2 : σ * σ = 1)
    (hs : Perm.sign σ = -1) : σ.IsSwap := by
  rw [← Perm.card_support_eq_two]
  have hmem : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 := Perm.dvd_of_mem_cycleType hn
    have h2' : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    have h3 := Perm.two_le_of_mem_cycleType hn
    have := Nat.le_of_dvd two_pos (h1.trans h2')
    omega
  have hrep := Multiset.eq_replicate_of_mem hmem
  have hsum := Perm.sum_cycleType σ
  have hle : σ.support.card ≤ 5 := by simpa using σ.support.card_le_univ
  rw [Perm.sign_of_cycleType] at hs
  generalize hk : Multiset.card σ.cycleType = k at hrep hs
  rw [hrep] at hsum hs
  simp only [Multiset.sum_replicate, smul_eq_mul] at hsum hs
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact absurd hs (by decide)
  · omega
  · exact absurd hs (by decide)

theorem swap_ne_of_disjoint_fin5 : ∀ a b c d : Fin 5, a ≠ b →
    Disjoint ({a, b} : Finset (Fin 5)) {c, d} → swap a b ≠ swap c d := by decide

theorem swap_eq_of_pair_eq_fin5 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    ({a, b} : Finset (Fin 5)) = {c, d} → swap a b = swap c d := by decide

theorem swap_ne_one_fin5 : ∀ a b : Fin 5, a ≠ b → swap a b ≠ 1 := by decide

noncomputable def piG (K : Subgroup G) (π : K →* Perm (Fin 5)) (x : G) : Perm (Fin 5) :=
  haveI := Classical.dec (x ∈ K); if h : x ∈ K then π ⟨x, h⟩ else 1

section piG

variable {K : Subgroup G} {π : K →* Perm (Fin 5)}

theorem piG_mem {x : G} (hx : x ∈ K) : piG K π x = π ⟨x, hx⟩ := by
  unfold piG; exact dif_pos hx

theorem piG_coe (m : K) : piG K π m = π m := piG_mem m.2

theorem piG_one : piG K π 1 = 1 := by
  rw [piG_mem K.one_mem]; exact π.map_one

theorem piG_mul {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    piG K π (x * y) = piG K π x * piG K π y := by
  rw [piG_mem (K.mul_mem hx hy), piG_mem hx, piG_mem hy, ← map_mul]; rfl

theorem piG_inv {x : G} (hx : x ∈ K) : piG K π x⁻¹ = (piG K π x)⁻¹ := by
  rw [piG_mem (K.inv_mem hx), piG_mem hx, ← map_inv]; rfl

theorem piG_pow {x : G} (hx : x ∈ K) (n : ℕ) : piG K π (x ^ n) = piG K π x ^ n := by
  rw [piG_mem (K.pow_mem hx n), piG_mem hx, ← map_pow]
  exact congrArg π (Subtype.ext (by simp))

theorem piG_zpow {x : G} (hx : x ∈ K) (n : ℤ) : piG K π (x ^ n) = piG K π x ^ n := by
  rw [piG_mem (K.zpow_mem hx n), piG_mem hx, ← map_zpow]
  exact congrArg π (Subtype.ext (by simp))

theorem piG_conj {h x : G} (hh : h ∈ K) (hx : x ∈ K) :
    piG K π (h * x * h⁻¹) = piG K π h * piG K π x * (piG K π h)⁻¹ := by
  rw [piG_mul (K.mul_mem hh hx) (K.inv_mem hh), piG_mul hh hx, piG_inv hh]

theorem piG_commute {x y : G} (hx : x ∈ K) (hy : y ∈ K) (h : Commute x y) :
    Commute (piG K π x) (piG K π y) := by
  show piG K π x * piG K π y = piG K π y * piG K π x
  rw [← piG_mul hx hy, ← piG_mul hy hx, h.eq]

end piG

@[expose] def IsS5Model (D α : Set G) (π : Halpha D α →* Perm (Fin 5)) : Prop :=
  Function.Surjective π ∧ ∀ θ ∈ Dalpha D α, ∀ v ∈ θ, ∀ y : G,
    y ∈ θ ↔ ∃ m : Halpha D α, π m = 1 ∧ y = (m : G) * v * (m : G)⁻¹

theorem blocks_commute_of_mem (hN : IsNormalSet D) (hD : IsOddTransp D) {α : Set G}
    (hblock : IsBlock D α) {θ₁ θ₂ : Set G} (h₁ : θ₁ ∈ blockClass α) (h₂ : θ₂ ∈ blockClass α)
    (hne : θ₁ ≠ θ₂) {u v : G} (hu : u ∈ θ₁) (hv : v ∈ θ₂) (huv : Commute u v) :
    ∀ a ∈ θ₁, ∀ b ∈ θ₂, Commute a b := by
  have hθ₁ : IsBlock D θ₁ := isBlock_of_mem_blockClass hN hblock h₁
  obtain ⟨k, hk⟩ := mem_blockClass_iff'.mp (mem_blockClass_of_mem_blockClass h₁ h₂)
  have hkne : k • θ₁ ≠ θ₁ := by rw [← hk]; exact hne.symm
  intro a ha b hb
  exact commute_block_of_mem hN hD hθ₁ hkne hu (show v ∈ k • θ₁ by rw [← hk]; exact hv) huv a ha
    b (show b ∈ k • θ₁ by rw [← hk]; exact hb)

section Model

variable (hC : HypothesisC D) {π : Halpha D hC.alpha →* Perm (Fin 5)}

theorem piG_mul_self {u : G} (huD : u ∈ D) (huH : u ∈ Halpha D hC.alpha) :
    piG _ π u * piG _ π u = 1 := by
  rw [← piG_mul huH huH, hC.setup.oddT.mul_self_eq_one huD, piG_one]

theorem sign_piG_of_mem (hS : IsS5Model D hC.alpha π) {u : G}
    (hu : u ∈ DalphaStar D hC.alpha) : Perm.sign (piG _ π u) = -1 := by
  have hHu : u ∈ Halpha D hC.alpha := Subgroup.subset_closure hu
  by_contra hne
  have h1 : Perm.sign (piG _ π u) = 1 := (Int.units_eq_one_or _).resolve_right hne
  have hall : ∀ x (hx : x ∈ Subgroup.closure (DalphaStar D hC.alpha)),
      Perm.sign (piG (Halpha D hC.alpha) π x) = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem v hv =>
      obtain ⟨h, hh, rfl⟩ := hC.Halpha_transitive u hu v hv
      rw [piG_conj hh hHu, map_mul, map_mul, map_inv, mul_comm (Perm.sign (piG _ π h)),
        mul_inv_cancel_right, h1]
    | one => rw [piG_one, map_one]
    | mul x y hx hy ihx ihy => rw [piG_mul (K := Halpha D hC.alpha) hx hy, map_mul, ihx, ihy, mul_one]
    | inv x hx ihx => rw [piG_inv (K := Halpha D hC.alpha) hx, map_inv, ihx, inv_one]
  obtain ⟨k, hk⟩ := hS.1 (swap 0 1)
  have := hall k k.2
  rw [piG_coe, hk, Perm.sign_swap (by decide)] at this
  exact absurd this (by decide)

theorem piG_isSwap (hS : IsS5Model D hC.alpha π) {u : G} (hu : u ∈ DalphaStar D hC.alpha) :
    (piG _ π u).IsSwap := by
  obtain ⟨θ, hθ, huθ⟩ := hu
  exact isSwap_of_mul_self_of_sign (piG_mul_self hC (hθ.2.1 huθ)
    (Subgroup.subset_closure ⟨θ, hθ, huθ⟩)) (sign_piG_of_mem hC hS ⟨θ, hθ, huθ⟩)

theorem piG_eq_of_mem_block (hS : IsS5Model D hC.alpha π) {θ : Set G}
    (hθ : θ ∈ Dalpha D hC.alpha) {u v : G} (hu : u ∈ θ) (hv : v ∈ θ) :
    piG _ π u = piG _ π v := by
  obtain ⟨m, hm1, rfl⟩ := (hS.2 θ hθ u hu v).mp hv
  rw [piG_conj m.2 (Subgroup.subset_closure ⟨θ, hθ, hu⟩), piG_coe, hm1]
  group

theorem mem_of_piG_commute (hS : IsS5Model D hC.alpha π) {θ : Set G}
    (hθ : θ ∈ Dalpha D hC.alpha) {u x : G} (hu : u ∈ θ) (hxD : x ∈ D)
    (hxH : x ∈ Halpha D hC.alpha) (hc : Commute (piG _ π u) (piG _ π x))
    (hnc : ¬ Commute u x) : x ∈ θ := by
  have hD := hC.setup.oddT
  have huD : u ∈ D := hθ.2.1 hu
  have huH : u ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨θ, hθ, hu⟩
  have hu2 := hD.mul_self_eq_one huD
  have hx2 := hD.mul_self_eq_one hxD
  have hodd : Odd (orderOf (u * x)) := hD.odd_of_not_commute huD hxD hnc
  have hux : u * x ∈ Halpha D hC.alpha := Subgroup.mul_mem _ huH hxH
  have hpu := piG_mul_self (π := π) hC huD huH
  have hpx := piG_mul_self (π := π) hC hxD hxH
  have hy2 : piG _ π (u * x) ^ 2 = 1 := by
    rw [piG_mul huH hxH, sq]
    calc piG _ π u * piG _ π x * (piG _ π u * piG _ π x)
        = piG _ π u * (piG _ π x * piG _ π u) * piG _ π x := by group
      _ = piG _ π u * (piG _ π u * piG _ π x) * piG _ π x := by rw [hc.eq]
      _ = (piG _ π u * piG _ π u) * (piG _ π x * piG _ π x) := by group
      _ = 1 := by rw [hpu, hpx, one_mul]
  have hd1 : orderOf (piG _ π (u * x)) ∣ orderOf (u * x) :=
    orderOf_dvd_of_pow_eq_one (by rw [← piG_pow hux, pow_orderOf_eq_one, piG_one])
  have hd2 : orderOf (piG _ π (u * x)) ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have hord : orderOf (piG _ π (u * x)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact h
    · rw [h] at hd1
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨c, hc'⟩ := hd1
      omega
  have hφ1 : piG _ π (u * x) = 1 := orderOf_eq_one_iff.mp hord
  obtain ⟨j, hj⟩ := OddTransp.exists_zpow_conj_eq hu2 hx2 hodd (-1)
  have hconj : (u * x) ^ j * u * ((u * x) ^ j)⁻¹ = x := by
    rw [hj, zpow_neg_one, mul_inv_rev, hD.inv_eq hxD, hD.inv_eq huD, mul_assoc, hu2, mul_one]
  refine (hS.2 θ hθ u hu x).mpr ⟨⟨(u * x) ^ j, Subgroup.zpow_mem _ hux j⟩, ?_, hconj.symm⟩
  rw [← piG_mem (Subgroup.zpow_mem _ hux j), piG_zpow hux, hφ1, one_zpow]

theorem exists_mem_piG_eq (hS : IsS5Model D hC.alpha π) (a b : Fin 5) (hab : a ≠ b) :
    ∃ u ∈ DalphaStar D hC.alpha, piG _ π u = swap a b := by
  obtain ⟨u₀, hu₀⟩ : (DalphaStar D hC.alpha).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨k, hk⟩ := hS.1 (swap 0 1)
    have hk1 : k = 1 := by
      apply Subtype.ext
      have := k.2
      change (k : G) ∈ Subgroup.closure (DalphaStar D hC.alpha) at this
      rw [hemp, Subgroup.closure_empty, Subgroup.mem_bot] at this
      exact this
    rw [hk1, map_one] at hk
    exact swap_ne_one_fin5 0 1 (by decide) hk.symm
  obtain ⟨x, y, hxy, hsw⟩ := piG_isSwap hC hS hu₀
  obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_swap hxy hab)
  obtain ⟨k, rfl⟩ := hS.1 c
  have hu₀H : u₀ ∈ Halpha D hC.alpha := Subgroup.subset_closure hu₀
  refine ⟨(k : G) * u₀ * (k : G)⁻¹,
    (Subgroup.mem_set_normalizer_iff.mp (Halpha_le_normalizer hC.setup.normal k.2) u₀).mp hu₀, ?_⟩
  rw [piG_conj k.2 hu₀H, piG_coe, hsw, hc]

theorem eq_of_piG_eq (hS : IsS5Model D hC.alpha π) {θ₁ θ₂ : Set G}
    (h₁ : θ₁ ∈ Dalpha D hC.alpha) (h₂ : θ₂ ∈ Dalpha D hC.alpha) {u₁ u₂ : G} (hu₁ : u₁ ∈ θ₁)
    (hu₂ : u₂ ∈ θ₂) (heq : piG _ π u₁ = piG _ π u₂) : θ₁ = θ₂ := by
  classical
  have hD := hC.setup.oddT
  have hN := hC.setup.normal
  have hblock := hC.isBlock_alpha
  have hsame : ∀ y, y ∈ θ₁ → y ∈ θ₂ → θ₁ = θ₂ := fun y hy1 hy2 =>
    eq_of_mem_of_mem_blockClass hblock h₁.1 h₂.1 ⟨y, hy1, hy2⟩
  have hH : ∀ {v}, v ∈ DalphaStar D hC.alpha → v ∈ Halpha D hC.alpha :=
    fun hv => Subgroup.subset_closure hv
  have hu₁S : u₁ ∈ DalphaStar D hC.alpha := ⟨θ₁, h₁, hu₁⟩
  have hu₂S : u₂ ∈ DalphaStar D hC.alpha := ⟨θ₂, h₂, hu₂⟩
  have hu₁D : u₁ ∈ D := h₁.2.1 hu₁
  have hu₂D : u₂ ∈ D := h₂.2.1 hu₂
  have hu₁H := hH hu₁S
  have hu₂H := hH hu₂S
  by_cases hc : Commute u₁ u₂
  swap
  · exact hsame u₂ (mem_of_piG_commute hC hS h₁ hu₁ hu₂D hu₂H (by rw [heq]) hc) hu₂
  by_contra hne
  have hne12 : u₁ ≠ u₂ := fun h => hne (hsame u₂ (h ▸ hu₁) hu₂)
  obtain ⟨a, b, hab, hsw⟩ := piG_isSwap hC hS hu₁S
  obtain ⟨c, d, hcd, hnc⟩ := exists_swap_not_commute_fin5 a b hab
  obtain ⟨s, hsS, hs⟩ := exists_mem_piG_eq hC hS c d hcd
  obtain ⟨σ, hσ, hsσ⟩ := hsS
  have hsD : s ∈ D := hσ.2.1 hsσ
  have hsH : s ∈ Halpha D hC.alpha := hH ⟨σ, hσ, hsσ⟩
  have hns₁ : ¬ Commute u₁ s := fun h => hnc (by
    have := piG_commute (π := π) hu₁H hsH h
    rw [hsw, hs] at this
    exact this.eq)
  have hns₂ : ¬ Commute u₂ s := fun h => hnc (by
    have := piG_commute (π := π) hu₂H hsH h
    rw [← heq, hsw, hs] at this
    exact this.eq)
  have htri : IsTriangle D u₁ s u₂ := ⟨hu₁D, hu₂D, hsD, hne12, hc, hns₁, hns₂⟩
  have hp11 := piG_mul_self (π := π) hC hu₁D hu₁H
  have hblk := blocks_commute_of_mem hN hD hblock h₁.1 h₂.1 hne hu₁ hu₂ hc
  have tk : ∀ w, w ∈ Halpha D hC.alpha → IsTriangle D u₁ w u₂ → IsThirdKind u₁ w u₂ →
      Commute (piG _ π u₁) (piG _ π w) := by
    rintro w hwH htw ⟨n, hn, -, hord⟩
    obtain ⟨-, -, hz₁, -, -, -⟩ := htw.third_kind hD hN hn hord
    have h12 : u₁ * u₂ ∈ Halpha D hC.alpha := Subgroup.mul_mem _ hu₁H hu₂H
    have h12w : u₁ * u₂ * w ∈ Halpha D hC.alpha := Subgroup.mul_mem _ h12 hwH
    have hzH : (u₁ * u₂ * w) ^ n ∈ Halpha D hC.alpha := Subgroup.pow_mem _ h12w n
    have heH : u₁ * u₂ * (u₁ * u₂ * w) ^ n ∈ Halpha D hC.alpha := Subgroup.mul_mem _ h12 hzH
    have he : Commute (u₁ * u₂ * (u₁ * u₂ * w) ^ n) u₁ :=
      ((Commute.refl u₁).mul_left hc.symm).mul_left hz₁
    have hpw2 := piG_mul_self (π := π) hC htw.2.2.1 hwH
    have hpowodd : piG _ π w ^ n = piG _ π w := by
      obtain ⟨k, rfl⟩ := hn
      rw [pow_succ, pow_mul, sq, hpw2, one_pow, one_mul]
    have hpe : piG _ π (u₁ * u₂ * (u₁ * u₂ * w) ^ n) = piG _ π w := by
      rw [piG_mul h12 hzH, piG_pow h12w n, piG_mul h12 hwH, piG_mul hu₁H hu₂H, ← heq, hp11]
      simp only [one_mul, hpowodd]
    have := piG_commute (π := π) heH hu₁H he
    rw [hpe] at this
    exact this.symm
  have hXH : Subgroup.closure ({u₁, s} : Set G) ≤ Halpha D hC.alpha :=
    (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hu₁H, Set.singleton_subset_iff.mpr hsH⟩)
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure {u₁, s} → IsTriangle D u₁ x u₂ →
      ¬ IsThirdKind u₁ x u₂ := by
    intro x hxD hxX htx hk
    have hxH := hXH hxX
    have hxθ : x ∈ θ₁ := mem_of_piG_commute hC hS h₁ hu₁ hxD hxH (tk x hxH htx hk)
      htx.2.2.2.2.2.1
    exact htx.2.2.2.2.2.2 (hblk x hxθ u₂ hu₂).symm
  rcases IsTriangle.orderOf_cases hD hN htri with ⟨hodd, -⟩ | h4 | h3
  ·
    obtain ⟨g, hg, hgc⟩ := exists_conj_of_odd_orderOf_mul (htri.uv_mul_self hD)
      (hD.mul_self_eq_one hsD) hodd
    have hgH : g ∈ Halpha D hC.alpha := (Subgroup.closure_le _).mpr
      (Set.insert_subset_iff.mpr ⟨Subgroup.mul_mem _ hu₁H hu₂H,
        Set.singleton_subset_iff.mpr hsH⟩) hg
    have h1 : piG _ π s = 1 := by
      rw [← hgc, piG_conj hgH (Subgroup.mul_mem _ hu₁H hu₂H), piG_mul hu₁H hu₂H, ← heq, hp11]
      group
    rw [hs] at h1
    exact swap_ne_one_fin5 c d hcd h1
  ·
    have SK : SecondKindStructure u₁ s u₂ := OddTransp.secondKind_structure hD hN htri h4 hno
    obtain ⟨q, hq, hqc⟩ := SK.conj
    have hqQ := secondKind_commutator_zpowers_le hD hN htri h4 hno hq
    have hQM : conjClosure (Subgroup.closure {u₁, s}) (u₁ * u₂) ≤
        (π.ker).map (Halpha D hC.alpha).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨g, hg, rfl⟩
      have hgH := hXH hg
      have hyH : g * (u₁ * u₂) * g⁻¹ ∈ Halpha D hC.alpha :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH (Subgroup.mul_mem _ hu₁H hu₂H))
          (Subgroup.inv_mem _ hgH)
      refine ⟨⟨_, hyH⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, ← piG_mem hyH, piG_conj hgH (Subgroup.mul_mem _ hu₁H hu₂H),
        piG_mul hu₁H hu₂H, ← heq, hp11]
      group
    obtain ⟨m, hm, hmq⟩ := hQM hqQ
    apply hne
    refine hsame u₂ ((hS.2 θ₁ h₁ u₁ hu₁ u₂).mpr ⟨m, MonoidHom.mem_ker.mp hm, ?_⟩) hu₂
    rw [show (m : G) = q from hmq, hqc]
  ·
    have := tk s hsH htri h3
    rw [hsw, hs] at this
    exact hnc this.eq

theorem mem_Dalpha_iff_disjoint (hS : IsS5Model D hC.alpha π) {θ₁ θ₂ : Set G}
    (h₁ : θ₁ ∈ Dalpha D hC.alpha) (h₂ : θ₂ ∈ Dalpha D hC.alpha) {u₁ u₂ : G} (hu₁ : u₁ ∈ θ₁)
    (hu₂ : u₂ ∈ θ₂) :
    θ₂ ∈ Dalpha D θ₁ ↔ Disjoint (piG _ π u₁).support (piG _ π u₂).support := by
  have hD := hC.setup.oddT
  have hN := hC.setup.normal
  have hblock := hC.isBlock_alpha
  have hu₁H : u₁ ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨θ₁, h₁, hu₁⟩
  have hu₂H : u₂ ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨θ₂, h₂, hu₂⟩
  obtain ⟨a, b, hab, hsw₁⟩ := piG_isSwap hC hS ⟨θ₁, h₁, hu₁⟩
  obtain ⟨c, d, hcd, hsw₂⟩ := piG_isSwap hC hS ⟨θ₂, h₂, hu₂⟩
  rw [hsw₁, hsw₂, Perm.support_swap hab, Perm.support_swap hcd]
  constructor
  · intro h
    have hpc := piG_commute (π := π) hu₁H hu₂H (h.2.2.2 u₁ hu₁ u₂ hu₂)
    rw [hsw₁, hsw₂] at hpc
    refine swap_commute_fin5 a b c d hab hcd hpc.eq ?_
    intro he
    exact h.2.2.1 (eq_of_piG_eq hC hS h₁ h₂ hu₁ hu₂ (by rw [hsw₁, hsw₂, he])).symm
  · intro hdisj
    have hpc : Commute (piG _ π u₁) (piG _ π u₂) := by
      rw [hsw₁, hsw₂]; exact swap_disjoint_commute_fin5 a b c d hdisj
    have hne : θ₂ ≠ θ₁ := by
      rintro rfl
      have := piG_eq_of_mem_block (π := π) hC hS h₁ hu₁ hu₂
      rw [hsw₁, hsw₂] at this
      exact swap_ne_of_disjoint_fin5 a b c d hab hdisj this
    have hc : Commute u₁ u₂ := by
      by_contra hnc
      exact hne (eq_of_mem_of_mem_blockClass hblock h₂.1 h₁.1
        ⟨u₂, hu₂, mem_of_piG_commute hC hS h₁ hu₁ (h₂.2.1 hu₂) hu₂H hpc hnc⟩)
    exact ⟨mem_blockClass_of_mem_blockClass h₁.1 h₂.1, h₂.2.1, hne,
      blocks_commute_of_mem hN hD hblock h₁.1 h₂.1 hne.symm hu₁ hu₂ hc⟩

theorem petersenAt_of_S5 (hS : IsS5Model D hC.alpha π) : PetersenAt D hC.alpha := by
  classical
  have hblock := hC.isBlock_alpha
  let Φ : Set G → Pair5 := fun θ =>
    if h : ∃ u ∈ θ, (piG _ π u).support.card = 2 then
      ⟨(piG _ π h.choose).support, h.choose_spec.2⟩ else ⟨{0, 1}, by decide⟩
  have hΦ : ∀ θ ∈ Dalpha D hC.alpha, ∀ u ∈ θ, (Φ θ).1 = (piG _ π u).support := by
    intro θ hθ u hu
    have hex : ∃ u ∈ θ, (piG _ π u).support.card = 2 :=
      ⟨u, hu, Perm.card_support_eq_two.mpr (piG_isSwap hC hS ⟨θ, hθ, hu⟩)⟩
    dsimp only [Φ]
    rw [dif_pos hex]
    exact congrArg Perm.support (piG_eq_of_mem_block hC hS hθ hex.choose_spec.1 hu)
  refine petersenAt_of_model Φ ?_ ?_ ?_
  · rintro ⟨p, hp⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp
    obtain ⟨u, ⟨θ, hθ, hu⟩, hsw⟩ := exists_mem_piG_eq hC hS a b hab
    exact ⟨θ, hθ, Subtype.ext (by rw [hΦ θ hθ u hu, hsw, Perm.support_swap hab])⟩
  · intro θ₁ h₁ θ₂ h₂ heq
    obtain ⟨u₁, hu₁⟩ := blockClass_nonempty hblock.nonempty h₁.1
    obtain ⟨u₂, hu₂⟩ := blockClass_nonempty hblock.nonempty h₂.1
    have h := congrArg Subtype.val heq
    rw [hΦ θ₁ h₁ u₁ hu₁, hΦ θ₂ h₂ u₂ hu₂] at h
    obtain ⟨a, b, hab, hsw₁⟩ := piG_isSwap hC hS ⟨θ₁, h₁, hu₁⟩
    obtain ⟨c, d, hcd, hsw₂⟩ := piG_isSwap hC hS ⟨θ₂, h₂, hu₂⟩
    rw [hsw₁, hsw₂, Perm.support_swap hab, Perm.support_swap hcd] at h
    exact eq_of_piG_eq hC hS h₁ h₂ hu₁ hu₂
      (by rw [hsw₁, hsw₂]; exact swap_eq_of_pair_eq_fin5 a b c d hab hcd h)
  · intro θ₁ h₁ θ₂ h₂
    obtain ⟨u₁, hu₁⟩ := blockClass_nonempty hblock.nonempty h₁.1
    obtain ⟨u₂, hu₂⟩ := blockClass_nonempty hblock.nonempty h₂.1
    rw [hΦ θ₁ h₁ u₁ hu₁, hΦ θ₂ h₂ u₂ hu₂]
    exact mem_Dalpha_iff_disjoint hC hS h₁ h₂ hu₁ hu₂

end Model

theorem isS5Model_of_quotient {α : Set G} (N : Subgroup (Halpha D α)) [N.Normal]
    (e : Halpha D α ⧸ N ≃* Perm (Fin 5))
    (horb : ∀ θ ∈ Dalpha D α, ∀ v ∈ θ, ∀ y : G,
      y ∈ θ ↔ ∃ m ∈ N, y = (m : G) * v * (m : G)⁻¹) :
    IsS5Model D α ((e : Halpha D α ⧸ N →* Perm (Fin 5)).comp (QuotientGroup.mk' N)) := by
  have hker : ∀ m : Halpha D α,
      (e : Halpha D α ⧸ N →* Perm (Fin 5)).comp (QuotientGroup.mk' N) m = 1 ↔ m ∈ N := by
    intro m
    simp [QuotientGroup.eq_one_iff]
  refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective N), fun θ hθ v hv y => ?_⟩
  rw [horb θ hθ v hv y]
  simp only [hker]

end S5Model

end CFSG.OddTranspositions

