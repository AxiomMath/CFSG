module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKStd
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKTau
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinC
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

theorem fixesA_of_centralizes_nsbk {G : Type} [Group G] {T L I K : Subgroup G}
    {m n j : ℕ} {α : ↥K →* GL (Fin n) (ZMod 2)}
    {β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)}
    (hequi : ∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
      Multiplicative.toAdd (β v) i =
        ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u) i))
    (hV2 : ∀ a : Fin n, a.val < m → ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧
      ∃ i : Fin j, Multiplicative.toAdd (β v) i = Pi.single a 1)
    (y : ↥K) (hy : ∀ v ∈ vV T L, v * (y : G) = (y : G) * v) :
    FixesA m ((α y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  intro a ha
  obtain ⟨v, hvV, i, hi⟩ := hV2 a ha
  have hconj : (v : G) = (y : G) * (v : G) * (y : G)⁻¹ := by
    rw [← hy (v : G) hvV, mul_inv_cancel_right]
  have h := hequi y v v hconj i
  rw [hi] at h
  exact h.symm

theorem lowerBlock2_pow_nsbk {n m : ℕ} (h : n = m + 2) (g : GL (Fin n) (ZMod 2))
    (hg : FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2))) (k : ℕ) :
    FixesA m ((g ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) ∧
      lowerBlock2 h ((g ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, Units.val_one]
    exact ⟨fixesA_one m, lowerBlock2_one h⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hmul : ((g ^ (k + 1) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((g ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rw [pow_succ, Units.val_mul]
    rw [hmul]
    exact ⟨fixesA_mul ih1 hg, by rw [lowerBlock2_mul h ih1 hg, ih2, pow_succ]⟩

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}

theorem lemma35KR_of_module (hN31 : NotC31)
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hN3 : NSBModuleStructure) (h31 : Lemma31) (h32 : Lemma32) : Lemma35KR := by
  intro G _ _ T M L Mm I H K m k hd
  obtain ⟨-, -, n, hnm, hpsl⟩ := h32 G T M L Mm I H K m k hd
  obtain ⟨j, α, β, -, hsurj, hker, hbij, hequi⟩ := hN3 G T M L Mm I H K m k hd n hnm hpsl
  obtain ⟨α', β', hs', hk', hb', he', hVc, hcov, -, -⟩ :=
    exists_std_coordinates hN31 h22 h27 hd hnm α β hsurj hker hbij hequi
  have hV2 : ∀ a : Fin n, a.val < m → ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧
      ∃ i : Fin j, Multiplicative.toAdd (β' v) i = Pi.single a 1 := by
    intro a ha
    exact hcov (Pi.single a 1) (fun b hb => by
      have : b ≠ a := fun h => by subst h; omega
      simp [Pi.single_apply, this])
  have hnm' : n = m + 1 ∨ (n = 5 ∧ m = 3) := by
    rcases hnm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h1, h2⟩
    · left; omega
  refine ⟨n, j, α', β', hnm', hk', he', hV2, ?_⟩
  intro h
  have hm3 : m = 3 := by omega
  obtain ⟨x₀, hx₀R, hx₀τ⟩ :=
    nsbFiveThreeTau_holds hN31 h22 h27 h31 h32 G T M L Mm I H K m k hd n j h hm3 α' β' hs' hk'
      hb' he' hVc hV2
  obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
  have hF : ∀ x : ↥K, (x : G) ∈ pCoreOf 2 I →
      FixesA m ((α' x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro x hx
    exact fixesA_of_centralizes_nsbk he' hV2 x
      (Subgroup.mem_centralizer_iff.mp (hRC (hRlt.le hx)))
  have hD2 : ∀ x : ↥K, (x : G) ∈ pCoreOf 2 I →
      lowerBlock2 h ((α' x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
        lowerBlock2 h ((α' x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    intro x hx
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 I) ⟨(x : G), hx⟩
    have hxe : x ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
    have h1 := (lowerBlock2_pow_nsbk h (α' x) (hF x hx) (2 ^ e)).2
    rw [← map_pow, hxe, map_one, Units.val_one, lowerBlock2_one h] at h1
    exact gl2_sq_of_two_power h1.symm
  have hmulD : ∀ x y : ↥K, (x : G) ∈ pCoreOf 2 I → (y : G) ∈ pCoreOf 2 I →
      lowerBlock2 h ((α' (x * y) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        lowerBlock2 h ((α' x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          lowerBlock2 h ((α' y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro x y hx hy
    rw [map_mul, Units.val_mul, lowerBlock2_mul h (hF x hx) (hF y hy)]
  refine ⟨lowerBlock2 h ((α' x₀ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)),
    hx₀τ, hD2 x₀ hx₀R, fun x hx => ?_, x₀, hx₀R, rfl⟩
  have hxx₀ : ((x * x₀ : ↥K) : G) ∈ pCoreOf 2 I := (pCoreOf 2 I).mul_mem hx hx₀R
  have h3 := hD2 (x * x₀) hxx₀
  rw [hmulD x x₀ hx hx₀R] at h3
  rcases gl2_pair_involutions _ _ (hD2 x hx) (hD2 x₀ hx₀R) h3 with h4 | h4 | h4
  · exact Or.inl h4
  · exact absurd h4 hx₀τ
  · exact Or.inr h4

end CFSG.Quasithin.H13.Ch4.NSB
