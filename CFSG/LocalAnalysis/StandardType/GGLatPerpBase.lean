module

public import CFSG.LocalAnalysis.StandardType.GGLatPerpChecks
public import CFSG.LocalAnalysis.StandardType.GGLatPerpRefl
public import CFSG.Blueprint.ChevalleyRoots

public section

namespace CFSG.StandardType.LatPerp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType.LatPerpChecks

open scoped Matrix

@[expose] def ggPerp (τ : Tag) (α : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  perp {v | IsRoot τ v} (Tag.symmetrizedCartan τ) α

theorem ggGram_eq_latGram (τ : Tag) (α β : Fin τ.rank → ℤ) :
    ggGram τ α β = latGram (Tag.symmetrizedCartan τ) α β := by
  simp only [ggGram, latGram, ggB_eq]

theorem ggCartInt_eq_cartInt (τ : Tag) (α β : Fin τ.rank → ℤ) :
    ggCartInt τ α β = cartInt (Tag.symmetrizedCartan τ) α β := by
  simp only [ggCartInt, cartInt, ggGram_eq_latGram]

theorem ggGram_eq_pair (τ : Tag) (α β : Fin τ.rank → ℤ) :
    ggGram τ α β = ggPairVec (ggMulB τ α) β := by
  simp only [ggGram, ggPairVec, ggMulB, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem ggGram_single_left (τ : Tag) (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    ggGram τ (Pi.single i 1) α = ∑ k, ggB τ i k * α k := by
  simp only [ggGram]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem lat_zmod_one_ne_zero {p : ℕ} (hp : p.Prime) : (1 : ZMod p) ≠ 0 := by
  intro h
  rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at h
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) h
  have := hp.two_le
  omega

theorem lat_zmod_two_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
  have := hp.two_le
  omega

theorem latChar_corootCoord (τ : Tag) (p : ℕ) (α β : Fin τ.rank → ℤ) :
    latChar p (corootCoord p (Tag.symmetrizedCartan τ) α) β =
      ((cartInt (Tag.symmetrizedCartan τ) α β : ℤ) : ZMod p) := by
  simp only [latChar, corootCoord, cartInt]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

theorem intCast_zmod_eq_zero_iff_of_abs_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c : ℤ} (h1 : -2 ≤ c) (h2 : c ≤ 2) : ((c : ℤ) : ZMod p) = 0 ↔ c = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hdvd
    by_contra hc
    have hle1 : p ≤ c.natAbs := by
      have := Int.natAbs_le_of_dvd_ne_zero hdvd hc
      simpa using this
    have hle2 : c.natAbs ≤ 2 := by
      have h3 : (c.natAbs : ℤ) ≤ 2 := by
        rcases Int.lt_or_le c 0 with h | h
        · rw [Int.ofNat_natAbs_of_nonpos (le_of_lt h)]; omega
        · rw [Int.natAbs_of_nonneg h]; exact h2
      exact_mod_cast h3
    have hp3 : 3 ≤ p := by
      have : 2 < p := lt_of_le_of_ne hp.two_le (by omega)
      omega
    omega
  · intro hc; rw [hc]; simp

section Cert

theorem ggRootList_mem {τ : Tag} {v : Fin τ.rank → ℤ} : v ∈ ggRootList τ ↔ IsRoot τ v := by
  rw [← List.mem_toFinset]
  exact mem_rootFinset

theorem ggPerpList_mem {τ : Tag} {α β : Fin τ.rank → ℤ} :
    β ∈ ggPerpList τ α ↔ β ∈ ggPerp τ α := by
  simp only [ggPerpList, List.mem_filter, ggPerp, perp, Set.mem_setOf_eq, ggGram_eq_latGram,
    beq_iff_eq]
  constructor
  · rintro ⟨hβ, hg⟩; exact ⟨ggRootList_mem.mp hβ, hg⟩
  · rintro ⟨hβ, hg⟩; exact ⟨ggRootList_mem.mpr hβ, hg⟩

theorem ggPerp_eq_finset (τ : Tag) (α : Fin τ.rank → ℤ) :
    ggPerp τ α = ↑(ggPerpFinset τ α) := by
  ext β
  simp only [ggPerp, perp, Set.mem_setOf_eq, Finset.mem_coe, ggPerpFinset, Finset.mem_filter,
    ggGram_eq_latGram, beq_iff_eq]
  constructor
  · rintro ⟨hβ, hg⟩; exact ⟨mem_rootFinset.mpr hβ, hg⟩
  · rintro ⟨hβ, hg⟩; exact ⟨mem_rootFinset.mp hβ, hg⟩

theorem ggCartCheck_sound {τ : Tag} (h : ggCartCheck τ = true) (j : Fin τ.rank)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    -2 ≤ cartInt (Tag.symmetrizedCartan τ) (Pi.single j 1) β ∧
      cartInt (Tag.symmetrizedCartan τ) (Pi.single j 1) β ≤ 2 ∧
      (cartInt (Tag.symmetrizedCartan τ) (Pi.single j 1) β = 0 ↔
        latGram (Tag.symmetrizedCartan τ) (Pi.single j 1) β = 0) := by
  rw [ggCartCheck] at h
  have hrow := List.all_eq_true.mp h j (List.mem_finRange j)
  rw [ggCartRow] at hrow
  have hb := List.all_eq_true.mp hrow β (ggRootList_mem.mpr hβ)
  have hc := of_decide_eq_true hb
  rw [← ggCartInt_eq_cartInt, ← ggGram_eq_latGram]
  simpa only [ggCartInt, ggGram_single_left, ← ggGram_eq_pair] using hc

end Cert

end CFSG.StandardType.LatPerp
