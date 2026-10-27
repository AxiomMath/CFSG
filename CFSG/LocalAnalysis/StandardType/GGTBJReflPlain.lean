module

public import CFSG.LocalAnalysis.StandardType.GGTBJReflFun

public section

namespace CFSG.StandardType

theorem exists_not_commute_reflection_plain {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    {ι : Type} [Nonempty ι] (f : ι → V → ZMod p) (v : ι → V)
    (hadd : ∀ i x y, f i (x + y) = f i x + f i y)
    (hsmul : ∀ i (c : ZMod p) x, f i (c • x) = c * f i x)
    (hfv : ∀ i, f i (v i) = 2)
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ i j, (f i (v j) ≠ 0 ∨ f j (v i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ)
    (hcard : p ^ 2 * Nat.card {w : V // ∀ i, f i w = 0} ≤ Nat.card V) :
    ∃ (i j : ι) (w : V),
      (w - f j w • v j) - f i (w - f j w • v j) • v i ≠
        (w - f i w • v i) - f j (w - f i w • v i) • v j := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let g : ι → Module.Dual (ZMod p) V := fun i =>
    { toFun := f i
      map_add' := hadd i
      map_smul' := fun c x => by simpa using hsmul i c x }
  have hg : ∀ i w, g i w = f i w := fun _ _ => rfl
  have hker : Nat.card ↥(⨅ i, LinearMap.ker (g i) : Submodule (ZMod p) V) =
      Nat.card {w : V // ∀ i, f i w = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, hg]
  have hpow : ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W],
      Nat.card W = p ^ Module.finrank (ZMod p) W := fun W _ _ _ => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := W), Nat.card_zmod]
  have hcodim : Module.finrank (ZMod p) ↥(⨅ i, LinearMap.ker (g i) : Submodule (ZMod p) V) + 2 ≤
      Module.finrank (ZMod p) V := by
    have h1 := hpow ↥(⨅ i, LinearMap.ker (g i) : Submodule (ZMod p) V)
    have h2 := hpow V
    rw [hker] at h1
    rw [h1, h2, ← pow_add, add_comm] at hcard
    have hle := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard
    omega
  obtain ⟨i, j, w, hw⟩ := exists_not_commute_reflection_fun hp2 g v hfv hconn hcodim
  exact ⟨i, j, w, hw⟩

end CFSG.StandardType

end
