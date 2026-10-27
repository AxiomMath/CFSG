module

public import CFSG.Quasithin.Background.G11BridgeG6
public import CFSG.Quasithin.Background.G6Swap

public section

namespace CFSG.Quasithin

namespace G11

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

private theorem ofAdd_mem_coreMod {n : ℕ} {u : Fin n → ZMod 2} (hu : u ∈ permCore n) :
    Multiplicative.ofAdd u ∈ G6.coreMod n := hu

private def coreAddHom (n : ℕ) (β : G6.coreMod n →* Multiplicative M) : ↥(permCore n) →+ M where
  toFun u := Multiplicative.toAdd
    (β ⟨Multiplicative.ofAdd (u : Fin n → ZMod 2), ofAdd_mem_coreMod u.2⟩)
  map_zero' := by
    have h1 : (⟨Multiplicative.ofAdd ((0 : ↥(permCore n)) : Fin n → ZMod 2),
        ofAdd_mem_coreMod (0 : ↥(permCore n)).2⟩ : G6.coreMod n) = 1 := rfl
    show Multiplicative.toAdd (β _) = 0
    rw [h1, map_one]
    rfl
  map_add' u u' := by
    have h1 : (⟨Multiplicative.ofAdd ((u + u' : ↥(permCore n)) : Fin n → ZMod 2),
        ofAdd_mem_coreMod (u + u').2⟩ : G6.coreMod n) =
          ⟨Multiplicative.ofAdd (u : Fin n → ZMod 2), ofAdd_mem_coreMod u.2⟩ *
            ⟨Multiplicative.ofAdd (u' : Fin n → ZMod 2), ofAdd_mem_coreMod u'.2⟩ := rfl
    show Multiplicative.toAdd (β _) = _
    rw [h1, map_mul]
    rfl

private def coreLin (n : ℕ) (β : G6.coreMod n →* Multiplicative M) :
    ↥(permCore n) →ₗ[ZMod 2] M where
  toFun u := coreAddHom n β u
  map_add' := map_add (coreAddHom n β)
  map_smul' c u := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp
    · simp

private theorem coreLin_apply (n : ℕ) (β : G6.coreMod n →* Multiplicative M)
    (u : ↥(permCore n)) :
    coreLin n β u = Multiplicative.toAdd
      (β ⟨Multiplicative.ofAdd (u : Fin n → ZMod 2), ofAdd_mem_coreMod u.2⟩) := rfl

private theorem zpow_eq_one_or_self_of_mul_self {G : Type*} [Group G] {g : G} (hg : g * g = 1)
    (k : ℤ) : g ^ k = 1 ∨ g ^ k = g := by
  have hg2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← Int.mul_ediv_add_emod k 2, h0, add_zero, zpow_mul, hg2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, h1, zpow_add, zpow_mul, hg2, one_zpow, one_mul, zpow_one]

private theorem mem_zpowers_allOnes_iff {n : ℕ} (x : G6.PermMod n) :
    x ∈ Subgroup.zpowers (G6.allOnes n) ↔ x = 1 ∨ x = G6.allOnes n := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases zpow_eq_one_or_self_of_mul_self (G6.permMod_mul_self (G6.allOnes n)) k with h | h
    · exact Or.inl (hk.symm.trans h)
    · exact Or.inr (hk.symm.trans h)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

private theorem ofAdd_mem_natKer_iff {n : ℕ} (u : ↥(permCore n)) :
    (⟨Multiplicative.ofAdd (u : Fin n → ZMod 2), ofAdd_mem_coreMod u.2⟩ : G6.coreMod n) ∈
        G6.natKer n ↔ u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1) := by
  show Multiplicative.ofAdd (u : Fin n → ZMod 2) ∈ Subgroup.zpowers (G6.allOnes n) ↔ _
  rw [mem_zpowers_allOnes_iff]
  constructor
  · rintro (h | h)
    · left
      exact Subtype.ext (by simpa using h)
    · right
      have h1 : ∀ i, (u : Fin n → ZMod 2) i = 1 := fun i => congrFun h i
      refine ⟨?_, h1⟩
      have hs : ∑ i, (u : Fin n → ZMod 2) i = 0 := u.2
      simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at hs
      exact (ZMod.natCast_eq_zero_iff_even).1 hs
  · rintro (h | ⟨-, h⟩)
    · left
      rw [h]
      rfl
    · right
      exact funext h

theorem g119_natural_of_isSymNatural {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (G : Subgroup (GLV M)) {n : ℕ} (hn : 5 ≤ n)
    (h : G6.IsSymNatural (toMulSub G) (⊤ : Subgroup (Multiplicative M)) n) :
    ∃ (θ : ↥G ≃* Equiv.Perm (Fin n)) (β : ↥(permCore n) →ₗ[ZMod 2] M),
      LinearMap.range β = ⊤ ∧
      (∀ u : ↥(permCore n), β u = 0 ↔ (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) ∧
      (∀ (g : ↥G) (u u' : ↥(permCore n)),
        (u' : Fin n → ZMod 2) = permAct (θ g : Equiv.Perm (Fin n)) (u : Fin n → ZMod 2) →
          β u' = (g : GLV M) (β u)) ∧
      (∀ g : ↥G, Module.finrank (ZMod 2)
          (LinearMap.range ((g : GLV M).toLinearMap - LinearMap.id)) = 1 → (θ g).IsSwap) := by
  obtain ⟨θ₀, β₀, hequiv, hrange, hker⟩ := h
  refine ⟨(toMulSubEquiv G).trans θ₀, coreLin n β₀, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.range_eq_top]
    intro m
    have hm : Multiplicative.ofAdd m ∈ β₀.range := by
      rw [hrange]
      exact Subgroup.mem_top _
    obtain ⟨x, hx⟩ := hm
    refine ⟨⟨Multiplicative.toAdd (x : G6.PermMod n), x.2⟩, ?_⟩
    rw [coreLin_apply]
    show Multiplicative.toAdd (β₀ x) = m
    rw [hx]
    rfl
  · intro u
    have h1 : coreLin n β₀ u = 0 ↔
        (⟨Multiplicative.ofAdd (u : Fin n → ZMod 2), ofAdd_mem_coreMod u.2⟩ :
          G6.coreMod n) ∈ β₀.ker := by
      rw [MonoidHom.mem_ker, coreLin_apply]
      constructor
      · intro h
        exact Multiplicative.toAdd.injective (by simpa using h)
      · intro h
        rw [h]
        rfl
    rw [h1, hker, ofAdd_mem_natKer_iff]
  · intro g u u' hu'
    have h1 := hequiv (toMulSubEquiv G g)
      ⟨Multiplicative.ofAdd (u : Fin n → ZMod 2), ofAdd_mem_coreMod u.2⟩
    have h2 : (⟨Multiplicative.ofAdd (u' : Fin n → ZMod 2), ofAdd_mem_coreMod u'.2⟩ :
        G6.coreMod n) = G6.coreAct n (θ₀ (toMulSubEquiv G g))
          ⟨Multiplicative.ofAdd (u : Fin n → ZMod 2), ofAdd_mem_coreMod u.2⟩ := by
      apply Subtype.ext
      show Multiplicative.ofAdd (u' : Fin n → ZMod 2) = Multiplicative.ofAdd (permAct _ _)
      rw [hu']
      rfl
    rw [coreLin_apply, coreLin_apply, h2, h1]
    rfl
  · intro g hg
    have ha : linEquivMulAut (g : GLV M) ∈ toMulSub G := linEquivMulAut_mem_toMulSub.2 g.2
    have hcard : Nat.card (commV (Subgroup.zpowers (linEquivMulAut (g : GLV M)))) = 2 :=
      (card_commV_zpowers_toMulSub_eq_two_iff (g : GLV M)).2 hg
    exact G6.isSwap_of_card_commV_eq_two hn θ₀ β₀ hequiv hker.le ha hcard

theorem g119_exists_fixed_of_isSymCore {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (G : Subgroup (GLV M)) {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : G6.IsSymCore (toMulSub G) (⊤ : Subgroup (Multiplicative M)) n) :
    ∃ m : M, m ≠ 0 ∧ ∀ g ∈ G, g m = m := by
  obtain ⟨θ₀, β₀, hequiv, -, hker⟩ := h
  have hn1 : 0 < n := by omega
  have heven : Even n := by
    rcases hn with rfl | rfl
    exacts [⟨3, rfl⟩, ⟨4, rfl⟩]
  have hmem : G6.allOnes n ∈ G6.coreMod n := by
    rw [G6.mem_coreMod]
    simp only [G6.allOnes, toAdd_ofAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_eq_zero_iff_even).2 heven
  refine ⟨Multiplicative.toAdd (β₀ ⟨G6.allOnes n, hmem⟩), ?_, ?_⟩
  · intro h0
    have h1 : β₀ ⟨G6.allOnes n, hmem⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 : (⟨G6.allOnes n, hmem⟩ : G6.coreMod n) ∈ β₀.ker := h1
    rw [hker, Subgroup.mem_bot] at h2
    have h3 : G6.allOnes n = 1 := congrArg Subtype.val h2
    have h4 : (1 : ZMod 2) = 0 := congrFun (congrArg Multiplicative.toAdd h3) ⟨0, hn1⟩
    exact absurd h4 (by decide)
  · intro g hg
    have h1 := hequiv ⟨linEquivMulAut g, linEquivMulAut_mem_toMulSub.2 hg⟩ ⟨G6.allOnes n, hmem⟩
    have h2 : G6.coreAct n (θ₀ ⟨linEquivMulAut g, linEquivMulAut_mem_toMulSub.2 hg⟩)
        ⟨G6.allOnes n, hmem⟩ = ⟨G6.allOnes n, hmem⟩ := Subtype.ext rfl
    rw [h2] at h1
    exact (congrArg Multiplicative.toAdd h1).symm

theorem g119_finrank_eq_of_isLnNatural {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (G : Subgroup (GLV M)) {n : ℕ}
    (h : G6.IsLnNatural (toMulSub G) (⊤ : Subgroup (Multiplicative M)) n) :
    Module.finrank (ZMod 2) M = n ∧
      Nonempty (↥G ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨⟨e⟩, hcard, -⟩ := h
  refine ⟨?_, ⟨(toMulSubEquiv G).trans e⟩⟩
  have h1 : Nat.card (subToSubgroup (⊤ : Submodule (ZMod 2) M)) = 2 ^ n := by
    rw [OrderIso.map_top]
    exact hcard
  have h2 := (natCard_subToSubgroup_eq_iff (⊤ : Submodule (ZMod 2) M) n).1 h1
  rwa [finrank_top] at h2

end G11

end CFSG.Quasithin
