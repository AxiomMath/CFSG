module

public import CFSG.Quasithin.Background.G64PermCore
public import CFSG.Quasithin.Background.G64Conclusion
public import CFSG.Quasithin.Background.G64RankOne

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

variable {V : Type} [CommGroup V]

theorem card_symDn_mod {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (FFModel.symDn n).Mod = if Even n then 2 ^ (n - 2) else 2 ^ (n - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, Explicit.card_dnZ hn,
    Explicit.card_coreMod hn] at h
  show Nat.card (↥(G6.coreMod n) ⧸ (Subgroup.zpowers (G6.allOnes n) ⊓
    G6.coreMod n).subgroupOf (G6.coreMod n)) = _
  split_ifs at h ⊢ with he
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
      obtain ⟨r, hr⟩ := he
      exact ⟨n - 2, by omega⟩
    simp only [show m + 2 - 1 = m + 1 by omega, add_tsub_cancel_right, pow_succ] at h ⊢
    omega
  · omega

theorem sq_eq_one_of_card_two (hV2 : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hx : Nat.card (commV (Subgroup.zpowers x)) = 2) : x ^ 2 = 1 := by
  obtain ⟨w, hw, hw1⟩ := exists_ne_one_of_card_two hx
  refine sq_eq_one_of_rankOne hV2 (w := w) fun v => ?_
  exact eq_one_or_eq_of_card_two hx hw hw1 (G6.mem_commV_of_mem (Subgroup.mem_zpowers x) v)

theorem ne_one_of_card_two {x : MulAut V} (hx : Nat.card (commV (Subgroup.zpowers x)) = 2) :
    x ≠ 1 := by
  rintro rfl
  have : commV (Subgroup.zpowers (1 : MulAut V)) = ⊥ := by
    rw [eq_bot_iff, G6.commV_le_iff]
    intro y hy v
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hy
    rw [hy]
    simp
  rw [this, Subgroup.card_bot] at hx
  omega

theorem isSwap_of_symNat (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 5 ≤ n)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : Perm (Fin n) →* ↥H}
    (h : (FFModel.symDn n).RealizesVia H U Z π) {σ : Perm (Fin n)}
    (hσ : Nat.card (commV (Subgroup.zpowers ((π σ : ↥H) : MulAut V))) = 2) : σ.IsSwap := by
  have hinj := RealizesVia.injective_of_faithful' (symDn_faithful hn) h
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one] at hσ
    exact ne_one_of_card_two hσ rfl
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : π (σ ^ 2) = π 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact sq_eq_one_of_card_two hV2 hσ)
    exact hinj h1
  have hmove := RealizesVia.exists_moved (symDn_faithful hn) h hσ1
  obtain ⟨-, w, hw⟩ := isTransvecSec_of_card_two hσ hmove
  exact isSwap_of_section hV2 hn le_rfl h hσ2 hmove ⟨w, hw⟩

theorem conclusion_of_sym [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    {a : MulAut V} (h : Hyp61 G a) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2)
    {C : Subgroup V} {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hK : SymmetricNatural (conjClosure (Subgroup.zpowers a) G) ⊤ C n) : Conclusion G a := by
  classical
  set K := conjClosure (Subgroup.zpowers a) G with hKdef
  have hKV : commV K = ⊤ := commV_classK h
  have haK : a ∈ K := mem_classK
  obtain ⟨π₀, hπ₀⟩ := hK
  set π : Perm (Fin n) →* ↥K := π₀ with hπdef
  have hπ : (FFModel.symDn n).RealizesVia K ⊤ C π := hπ₀
  have hinj : Function.Injective π := RealizesVia.injective_of_faithful' (symDn_faithful hn5) hπ
  set θ : ↥K ≃* Perm (Fin n) := (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm with hθ
  have hπθ : ∀ x : ↥K, π (θ x) = x := fun x =>
    (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).apply_symm_apply x
  have hθs : ∀ σ, θ.symm σ = π σ := fun _ => rfl
  have hswap : ∀ (x : MulAut V) (hx : x ∈ K), Nat.card (commV (Subgroup.zpowers x)) = 2 →
      (θ ⟨x, hx⟩).IsSwap := by
    intro x hx hxt
    refine isSwap_of_symNat hV2 hn5 hπ ?_
    rw [hπθ]
    exact hxt
  have hsa := hswap a haK htr
  have htr' : ∀ i j : Fin n, i ≠ j → Nat.card (commV (Subgroup.zpowers (swapAut θ i j))) = 2 :=
    card_swapAut_of_isSwap θ haK hsa htr
  have htrσ : ∀ σ : Perm (Fin n), σ.IsSwap →
      Nat.card (commV (Subgroup.zpowers ((θ.symm σ : ↥K) : MulAut V))) = 2 := by
    rintro σ ⟨i, j, hij, rfl⟩
    exact htr' i j hij
  have hGK : G = K := by
    refine le_antisymm (fun g hg => ?_) (classK_le h)
    obtain ⟨k, hk, hgk⟩ := exists_eq_on_of_normalizes (by omega) θ htrσ hswap
      (g := g) fun x hx => (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure _ G hg) x).1 hx
    have : g = k := MulEquiv.ext fun v => hgk v (by rw [hKV]; trivial)
    rw [this]
    exact hk
  have hVle : Nat.card V ≤ 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := card_commV_le_of_swap θ haK hsa htr
    rw [hKV, Subgroup.card_top] at this
    simpa using this
  have hVeq := RealizesVia.card_eq hπ
  rw [Subgroup.card_top, card_symDn_mod (by omega)] at hVeq
  have hmod : ModuleType K ⊤ := by
    by_cases he : Even n
    · rw [ite_eq_left he] at hVeq
      have hC2 : Nat.card C ≤ 2 := by
        have h2 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hVeq, h2] at hVle
        exact Nat.le_of_mul_le_mul_left hVle (by positivity)
      have hCpos : 0 < Nat.card C := Nat.card_pos
      rcases (show Nat.card C = 1 ∨ Nat.card C = 2 by omega) with h1 | h1
      · right; left
        refine ⟨n, hn5, hn8, π₀, ?_⟩
        rw [← Subgroup.card_eq_one.1 h1]
        exact hπ₀
      · right; right
        have hn68 : n = 6 ∨ n = 8 := by
          obtain ⟨r, hr⟩ := he
          omega
        refine ⟨n, hn68, symmetricCore_of_card hV2 (by omega) θ htr' hKV ?_⟩
        rw [hVeq, h1, ← pow_succ]
        congr 1
        omega
    · rw [ite_eq_right he] at hVeq
      have h1 : Nat.card C = 1 := by
        have : 2 ^ (n - 1) * Nat.card C ≤ 2 ^ (n - 1) * 1 := by rw [← hVeq, mul_one]; exact hVle
        have hCpos : 0 < Nat.card C := Nat.card_pos
        have := Nat.le_of_mul_le_mul_left this (by positivity)
        omega
      right; left
      refine ⟨n, hn5, hn8, π₀, ?_⟩
      rw [← Subgroup.card_eq_one.1 h1]
      exact hπ₀
  refine conclusion_of_single h hGK hmod fun hT => ?_
  obtain ⟨T, ⟨hTG, hTp, hTi⟩, haT, hcent⟩ := hT
  rw [hGK] at hTG hTi
  have hn58 : ¬ (n = 5 ∨ n = 8) := fun hn =>
    G6.not_central_in_sylow_of_isSwap hn θ haK hsa hTG hTp hTi hcent
  rw [hGK]
  rcases (show n = 6 ∨ n = 7 by omega) with rfl | rfl
  · exact Or.inr (Or.inl ⟨θ⟩)
  · exact Or.inr (Or.inr ⟨θ⟩)

end CFSG.Quasithin.G64
