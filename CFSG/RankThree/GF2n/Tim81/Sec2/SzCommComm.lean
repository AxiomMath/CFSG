module

public import CFSG.RankThree.GF2n.Tim81.Sec2.InvolutionModule
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzCor23
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzThreeGen
public import CFSG.RepresentationTheory.PerfectWeightStabilizerModule

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X7 CFSG.CGT.Timmesfeld75

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem finrank_three_inf_ge [Finite V] (C₁ C₂ C₃ : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) C₁ + Module.finrank (ZMod 2) C₂ + Module.finrank (ZMod 2) C₃ ≤
      2 * Module.finrank (ZMod 2) V +
        Module.finrank (ZMod 2) (C₁ ⊓ C₂ ⊓ C₃ : Submodule (ZMod 2) V) := by
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq C₁ C₂
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq (C₁ ⊓ C₂) C₃
  have hle₁ :
      Module.finrank (ZMod 2) (C₁ ⊔ C₂ : Submodule (ZMod 2) V) ≤
        Module.finrank (ZMod 2) V :=
    Submodule.finrank_le _
  have hle₂ :
      Module.finrank (ZMod 2) ((C₁ ⊓ C₂) ⊔ C₃ : Submodule (ZMod 2) V) ≤
        Module.finrank (ZMod 2) V :=
    Submodule.finrank_le _
  omega

end LinearAlgebra

section Representation

variable {G F V : Type*} [Group G] [Field F] [AddCommGroup V] [Module F V]

private theorem mem_fixedSub_closure_three (ρ : Representation F G V) (x y z : G) (w : V) :
    w ∈ fixedSub ρ (Subgroup.closure ({x, y, z} : Set G)) ↔
      ρ x w = w ∧ ρ y w = w ∧ ρ z w = w := by
  constructor
  · intro hw
    exact ⟨(mem_fixedSub.mp hw) x (Subgroup.subset_closure (by simp)),
      (mem_fixedSub.mp hw) y (Subgroup.subset_closure (by simp)),
      (mem_fixedSub.mp hw) z (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨hx, hy, hz⟩
    refine mem_fixedSub.mpr fun h hh => ?_
    refine Subgroup.closure_induction (p := fun h _ => ρ h w = w) ?_ ?_ ?_ ?_ hh
    · intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    · simp
    · intro p q _ _ hp hq
      rw [map_mul, Module.End.mul_apply, hq, hp]
    · intro p _ hp
      have h1 : ρ p⁻¹ (ρ p w) = ρ p⁻¹ w := by rw [hp]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] at h1
      exact h1.symm

private theorem fixedSub_top_eq_bot (ρ : Representation F G V) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) : fixedSub ρ (⊤ : Subgroup G) = ⊥ := by
  obtain ⟨-, hirr⟩ := (isIrreducible_iff ρ).mp (Fact.out : ρ.IsIrreducible)
  rcases hirr (fixedSub ρ ⊤) (fun g u hu => by
    rw [mem_fixedSub.mp hu g (Subgroup.mem_top g)]
    exact hu) with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := hnt
    apply hg
    ext v
    have hv : v ∈ fixedSub ρ ⊤ := by rw [h]; exact Submodule.mem_top
    have h2 : ρ g v = v := mem_fixedSub.mp hv g (Subgroup.mem_top g)
    simpa using h2

private theorem finrank_fixedSub_zpowers_conj (ρ : Representation F G V) (g x : G)
    (hinj : Function.Injective (ρ g)) :
    Module.finrank F (fixedSub ρ (Subgroup.zpowers (g * x * g⁻¹))) =
      Module.finrank F (fixedSub ρ (Subgroup.zpowers x)) := by
  rw [fixedSub_zpowers_conj ρ g x]
  exact (Submodule.equivMapOfInjective (ρ g) hinj
    (fixedSub ρ (Subgroup.zpowers x))).finrank_eq.symm

end Representation

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem three_mul_finrank_le (n : ℕ)
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (g x : ↥(suzukiGroup a K))
    (hcomm : Nat.card W ^ 4 ≤ Nat.card W *
      Nat.card (commSub ρ (CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K))) ^ 4)
    (hle : Nat.card ((commSub ρ
      (CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K))).map (ρ x - 1)) ≤ 2 ^ n) :
    3 * Module.finrank (ZMod 2) W ≤
      4 * (Module.finrank (ZMod 2) (fixedSub ρ (Subgroup.zpowers x)) + n) := by
  classical
  set U : Submodule (ZMod 2) W :=
    commSub ρ (CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K))
  have hcomm' : Nat.card W ^ 4 ≤ Nat.card W * Nat.card U ^ 4 := by simpa [U] using hcomm
  have hle' : Nat.card (U.map (ρ x - 1)) ≤ 2 ^ n := by simpa [U] using hle
  set l : ℕ := Module.finrank (ZMod 2) W with hl
  set u : ℕ := Module.finrank (ZMod 2) U with hu
  set v : ℕ := Module.finrank (ZMod 2) (U.map (ρ x - 1)) with hv
  set k : ℕ := Module.finrank (ZMod 2) (fixedSub ρ (Subgroup.zpowers x)) with hk
  have hWcard : Nat.card W = 2 ^ l := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod, hl]
  have hUcard : Nat.card U = 2 ^ u := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U), Nat.card_zmod, hu]
  have hVcard : Nat.card (U.map (ρ x - 1)) = 2 ^ v := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(U.map (ρ x - 1))),
      Nat.card_zmod, hv]
  have hlu : 3 * l ≤ 4 * u := by
    have h := hcomm'
    rw [hWcard, hUcard] at h
    rw [← pow_mul, ← pow_mul, ← pow_add] at h
    have h' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    omega
  have hvn : v ≤ n := by
    have h := hle'
    rw [hVcard] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hrn :
      v + Module.finrank (ZMod 2) (U ⊓ LinearMap.ker (ρ x - 1) : Submodule (ZMod 2) W) = u := by
    have h := CFSG.RankThree.GF2n.finrank_map_add_finrank_inf_ker (ρ x - 1) U
    rw [hv, hu]
    exact h
  have hwk_le : Module.finrank (ZMod 2)
      (U ⊓ LinearMap.ker (ρ x - 1) : Submodule (ZMod 2) W) ≤ k := by
    have hsub : U ⊓ LinearMap.ker (ρ x - 1) ≤ fixedSub ρ (Subgroup.zpowers x) := by
      rw [fixedSub_zpowers]
      exact inf_le_right
    have := Submodule.finrank_mono hsub
    simpa [hk] using this
  have huk : u ≤ k + n := by omega
  have h3 : 3 * l ≤ 4 * (k + n) := by omega
  simpa [hl, hk] using h3

private theorem finrank_le_twelve_mul (n : ℕ)
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) {x g₁ g₂ : ↥(suzukiGroup a K)}
    (hgen : Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} :
      Set ↥(suzukiGroup a K)) = ⊤)
    (h3 : 3 * Module.finrank (ZMod 2) W ≤
      4 * (Module.finrank (ZMod 2) (fixedSub ρ (Subgroup.zpowers x)) + n)) :
    Module.finrank (ZMod 2) W ≤ 12 * n := by
  classical
  set l : ℕ := Module.finrank (ZMod 2) W with hl
  set k : ℕ := Module.finrank (ZMod 2) (fixedSub ρ (Subgroup.zpowers x)) with hk
  have hky : Module.finrank (ZMod 2)
      (fixedSub ρ (Subgroup.zpowers (g₁ * x * g₁⁻¹))) = k := by
    rw [finrank_fixedSub_zpowers_conj ρ g₁ x
      (CFSG.RepresentationTheory.representation_injective ρ g₁)]
  have hkz : Module.finrank (ZMod 2)
      (fixedSub ρ (Subgroup.zpowers (g₂ * x * g₂⁻¹))) = k := by
    rw [finrank_fixedSub_zpowers_conj ρ g₂ x
      (CFSG.RepresentationTheory.representation_injective ρ g₂)]
  have hC : fixedSub ρ (Subgroup.zpowers x) ⊓
      fixedSub ρ (Subgroup.zpowers (g₁ * x * g₁⁻¹)) ⊓
      fixedSub ρ (Subgroup.zpowers (g₂ * x * g₂⁻¹)) = ⊥ := by
    have htop : fixedSub ρ (Subgroup.zpowers x) ⊓
        fixedSub ρ (Subgroup.zpowers (g₁ * x * g₁⁻¹)) ⊓
        fixedSub ρ (Subgroup.zpowers (g₂ * x * g₂⁻¹)) =
        fixedSub ρ (⊤ : Subgroup ↥(suzukiGroup a K)) := by
      ext w
      rw [Submodule.mem_inf, Submodule.mem_inf, mem_fixedSub_zpowers, mem_fixedSub_zpowers,
        mem_fixedSub_zpowers, ← hgen,
        mem_fixedSub_closure_three (ρ := ρ) (x := x) (y := g₁ * x * g₁⁻¹)
          (z := g₂ * x * g₂⁻¹)]
      simp only [and_assoc]
    rw [htop, fixedSub_top_eq_bot ρ hnt]
  have htri := finrank_three_inf_ge (V := W)
    (fixedSub ρ (Subgroup.zpowers x))
    (fixedSub ρ (Subgroup.zpowers (g₁ * x * g₁⁻¹)))
    (fixedSub ρ (Subgroup.zpowers (g₂ * x * g₂⁻¹)))
  rw [← hk, hky, hkz, hC, finrank_bot, add_zero, ← hl] at htri
  have hkl : k ≤ l := by
    have := Submodule.finrank_mono (show fixedSub ρ (Subgroup.zpowers x) ≤ ⊤ from le_top)
    simpa [hk, hl] using this
  have hcodim : l ≤ 3 * (l - k) := by omega
  have h3' : 3 * l ≤ 4 * (k + n) := by simpa [hl, hk] using h3
  have h12 : l ≤ 12 * n := by omega
  simpa [hl] using h12

theorem isSzNatural_or_two_pow_lt_card_commSub_map
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (g : ↥(suzukiGroup a K))
    {x : ↥(suzukiGroup a K)}
    (hx : x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K)) (hx1 : x ≠ 1) :
    IsSzNatural ρ ∨
      2 ^ (2 * a + 1) < Nat.card ((commSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K))).map (ρ x - 1)) := by
  classical
  by_cases hnat : IsSzNatural ρ
  · exact Or.inl hnat
  right
  set n : ℕ := 2 * a + 1 with hn
  have hx2 : x * x = 1 := by
    obtain ⟨y, hy, hxy⟩ := hx
    rw [← hxy, ← map_mul, szZ_mul_self hK hy, map_one]
  obtain ⟨g₁, g₂, hgen⟩ := exists_closure_three_conj_eq_top hK ha x hx2 hx1
  set T : Subgroup ↥(suzukiGroup a K) :=
    CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K) with hT
  set U : Submodule (ZMod 2) W := commSub ρ T with hU
  have h24 : 2 ^ (16 * n) ≤ Nat.card W := by
    rcases isSzNatural_or_le_card hK ρ hnt with h | h
    · exact absurd h hnat
    · simpa [hn] using h
  have hcomm : Nat.card W ^ 4 ≤ Nat.card W * Nat.card U ^ 4 := by
    rcases isSzNatural_or_fixed_comm_bounds (ρ := ρ) hK hnt g with h | h
    · exact absurd h hnat
    · simpa [hU, hT] using h.2
  by_contra hcon
  have hle : Nat.card (U.map (ρ x - 1)) ≤ 2 ^ n := not_lt.mp hcon
  have h3 : 3 * Module.finrank (ZMod 2) W ≤
      4 * (Module.finrank (ZMod 2) (fixedSub ρ (Subgroup.zpowers x)) + n) := by
    simpa [hU] using three_mul_finrank_le (n := n) (ρ := ρ) g x
      (by simpa [hU] using hcomm) (by simpa [hU] using hle)
  have h12 := finrank_le_twelve_mul (n := n) (ρ := ρ) hnt hgen h3
  have h16 : 16 * n ≤ Module.finrank (ZMod 2) W := by
    have h := h24
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  omega
end CFSG.RankThree.GF2n.Tim81.Sec2
