module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat2
public import CFSG.Quasithin.EmptyFaithful.S146E3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_two_ne_one {A : Type*} [Group A] (h : 2 < Nat.card A) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype A := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.1 h
  by_cases hx : x = 1
  · exact ⟨y, z, fun h => hxy (hx.trans h.symm), fun h => hxz (hx.trans h.symm), hyz⟩
  · by_cases hy : y = 1
    · exact ⟨x, z, hx, fun h => hyz (hy.trans h.symm), hxz⟩
    · exact ⟨x, y, hx, hy, hxy⟩

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {a b : G} (ha : orderOf a = 2) (hb : b ∈ Subgroup.zpowers a) :
    b = 1 ∨ b = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h : a ^ (k % 2) = a ^ k := by simpa [ha] using zpow_mod_orderOf a k
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h, h0, zpow_zero]
  · right
    rw [← h, h1, zpow_one]

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

omit [Finite G] in
theorem not_le_centralizer_W2 (hE : IsElemAbelian 2 (W 2)) :
    ¬ S ≤ Subgroup.centralizer (W 2 : Set G) := by
  intro hS
  have hn2 : 2 < n := by have := D.three_le; omega
  have hW4 : Nat.card ↥(W 2) = 4 := by
    rw [D.W_card 2 (by norm_num) hn2]
    norm_num
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne_one (A := ↥(W 2)) (by omega)
  have hord : ∀ c : ↥(W 2), c ≠ 1 → orderOf (c : G) = 2 := fun c hc =>
    orderOf_eq_prime (hE.2 c c.2) (fun h => hc (Subtype.ext h))
  have hflag : ∀ c : ↥(W 2), c ≠ 1 → ∀ x : G, x ∈ Subgroup.zpowers (c : G) ↔
      ∃ hx : x ∈ UL, Multiplicative.toAdd (D.β ⟨x, hx⟩) ∈ flagSpace n (ZMod 2) 1 := by
    intro c hc
    have hzW : Subgroup.zpowers (c : G) ≤ W 2 := Subgroup.zpowers_le.2 c.2
    refine flag_eq D.α D.β D.norm D.L_le D.rel (k := 1) (hzW.trans (D.W_le 2 (by norm_num) hn2))
      (by rw [Nat.card_zpowers, hord c hc, pow_one]) ?_
    intro s hs
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hzW) (hS hs))
  have hbz : (b : G) ∈ Subgroup.zpowers (a : G) :=
    (hflag a ha b).2 ((hflag b hb b).1 (Subgroup.mem_zpowers (b : G)))
  rcases eq_one_or_eq_of_mem_zpowers (hord a ha) hbz with h | h
  · exact hb (Subtype.ext h)
  · exact hab (Subtype.ext h.symm)

theorem relIndex_parab (hn : 1 < n) :
    S.relIndex (parab (L ⊔ S) n W 1) = 3 := by
  rw [← relIndex_Theta D (parab_le _ _ _ _), D.Theta_parab 1]
  have h := index_single (n := n) (i := 1) ⟨le_rfl, hn⟩
  rwa [← nodesNe_eq n 1] at h

theorem oTwoQuot_parab_perm (hE : IsElemAbelian 2 (W 2)) :
    Nonempty (OTwoQuot (parab (L ⊔ S) n W 1) ≃* Equiv.Perm (Fin 3)) := by
  classical
  set P := parab (L ⊔ S) n W 1 with hP
  have hn : 1 < n := by have := D.three_le; omega
  have hn2 : 2 < n := by have := D.three_le; omega
  have hPW2 : P ≤ Subgroup.normalizer (W 2 : Set G) := fun x hx =>
    (mem_parab.1 hx).2 2 (by norm_num) hn2 (by norm_num)
  have hW4 : Nat.card ↥(W 2) = 4 := by
    rw [D.W_card 2 (by norm_num) hn2]
    norm_num
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_perm_three hE hW4
  let φ : ↥P →* MulAut ↥(W 2) := (W 2).normalizerMonoidHom.comp (Subgroup.inclusion hPW2)
  have hφ : ∀ (x : ↥P) (w : ↥(W 2)),
      (((φ x) w : ↥(W 2)) : G) = (x : G) * (w : G) * (x : G)⁻¹ := fun x w =>
    (W 2).normalizerMonoidHom_apply_apply_coe (Subgroup.inclusion hPW2 x) w
  let Θ : ↥P →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp φ
  have hker : ∀ x : ↥P, Θ x = 1 → (x : G) ∈ Subgroup.centralizer (W 2 : Set G) := by
    intro x hx
    have h1 : φ x = 1 := e.injective (by simpa [Θ] using hx)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h2 := hφ x ⟨w, hw⟩
    rw [h1] at h2
    have h3 : w = (x : G) * w * (x : G)⁻¹ := h2
    calc w * (x : G) = ((x : G) * w * (x : G)⁻¹) * (x : G) := by rw [← h3]
      _ = (x : G) * w := by group
  have hk : ∀ x : ↥P, Θ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := D.isPGroup_inf_centralizer ⟨(x : G), x.2, hker x hx⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hSP : S ≤ P := D.S_le_parab 1
  have h3P : 3 ∣ Nat.card ↥P := by
    have h1 := Subgroup.relIndex_mul_card S P
    rw [inf_of_le_left hSP, relIndex_parab D hn] at h1
    exact Dvd.intro _ h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy3⟩ := exists_prime_orderOf_dvd_card' 3 h3P
  have hΘy : Θ y ≠ 1 := by
    intro h
    obtain ⟨k, hk'⟩ := hk y h
    have h1 : 3 ∣ 2 ^ k := hy3 ▸ orderOf_dvd_of_pow_eq_one hk'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1) (by norm_num)
  have hy3' : y ^ 3 = 1 := by simpa [hy3] using pow_orderOf_eq_one y
  have hΘy3 : (Θ y) ^ 3 = 1 := by
    rw [← map_pow, hy3', map_one]
  have hoy : orderOf (Θ y) = 3 := orderOf_eq_prime hΘy3 hΘy
  obtain ⟨s, hsS, hsC⟩ : ∃ s ∈ S, s ∉ Subgroup.centralizer (W 2 : Set G) := by
    by_contra hcon
    push Not at hcon
    exact not_le_centralizer_W2 D hE hcon
  have hΘs : Θ ⟨s, hSP hsS⟩ ≠ 1 := fun h => hsC (hker _ h)
  obtain ⟨a, ha⟩ := D.S2 ⟨s, hsS⟩
  have hsa : (⟨s, hSP hsS⟩ : ↥P) ^ 2 ^ a = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val ha)
  have hΘsa : (Θ ⟨s, hSP hsS⟩) ^ 2 ^ a = 1 := by rw [← map_pow, hsa, map_one]
  have h2s : 2 ∣ orderOf (Θ ⟨s, hSP hsS⟩) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hΘsa)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hΘs (orderOf_eq_one_iff.1 (by simpa using hi))
    rw [hi]
    exact dvd_pow_self 2 hi0
  set K : Subgroup (Equiv.Perm (Fin 3)) := Θ.range with hK
  have hcardK : Nat.card ↥K ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card K
    rwa [Nat.card_perm, Nat.card_fin] at this
  have h2K : 2 ∣ Nat.card ↥K := h2s.trans (Subgroup.orderOf_dvd_natCard K ⟨_, rfl⟩)
  have h3K : 3 ∣ Nat.card ↥K := by
    have := Subgroup.orderOf_dvd_natCard K (x := Θ y) ⟨_, rfl⟩
    rwa [hoy] at this
  have h6K : 6 ∣ Nat.card ↥K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2K h3K
  have hK6 : Nat.card ↥K = 6 := Nat.dvd_antisymm hcardK h6K
  have hKtop : K = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hK6, Nat.card_perm, Nat.card_fin]
    rfl
  exact nonempty_oTwoQuot_equiv_perm_three P Θ (MonoidHom.range_eq_top.1 hKtop) hk

end C

end S15223P4

end CFSG.Quasithin
