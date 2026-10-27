module

public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTwist
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl

public section

namespace CFSG.StandardType.RealKGCover

open CFSG.Assembly Multiplicative SpCoord CFSG.StandardType.SlNsRootGen

section Cover

variable {p : ℕ} {H R : Type} [Group H] [Group R]

theorem centralizer_image_eq_map {φ : H →* R} (hφs : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center H) (hkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1)
    {X : Set H} (hX : ∀ x ∈ X, x ^ p = 1) :
    Subgroup.centralizer (φ '' X) = (Subgroup.centralizer X).map φ := by
  apply le_antisymm
  · intro l hl
    obtain ⟨g, rfl⟩ := hφs l
    refine Subgroup.mem_map.mpr ⟨g, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, rfl⟩
    have h1 : φ x * φ g = φ g * φ x := Subgroup.mem_centralizer_iff.mp hl (φ x) ⟨x, hx, rfl⟩
    set z := g * x * g⁻¹ * x⁻¹ with hz
    have hzker : z ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    have hzcomm : Commute z x := (Subgroup.mem_center_iff.mp (hker hzker) x).symm
    have hconj : g * x * g⁻¹ = z * x := by rw [hz]; group
    have hxp := hX x hx
    have h2 : (z * x) ^ p = 1 := by
      rw [← hconj, show g * x * g⁻¹ = MulAut.conj g x from rfl, ← map_pow, hxp, map_one]
    have hzp : z ^ p = 1 := by
      have h3 : z ^ p * x ^ p = 1 := by rw [← hzcomm.mul_pow, h2]
      rwa [hxp, mul_one] at h3
    rw [hkerp z hzker hzp, one_mul] at hconj
    calc x * g = (g * x * g⁻¹) * g := by rw [hconj]
      _ = g * x := by group
  · intro l hl
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hl
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg x hx]

theorem isComponentOf_map_centralizer {φ : H →* R} (hφs : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center H) (hkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1)
    {X : Set H} (hX : ∀ x ∈ X, x ^ p = 1) {S : Subgroup H}
    (h : IsComponentOf S (Subgroup.centralizer X)) :
    IsComponentOf (S.map φ) (Subgroup.centralizer (φ '' X)) := by
  rw [centralizer_image_eq_map hφs hker hkerp hX]
  exact isComponentOf_iff_open.mpr (CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map φ
    (fun g hg => hker (MonoidHom.mem_ker.mpr hg)) (isComponentOf_iff_open.mp h))

theorem dvd_card_map [Finite H] {φ : H →* R} (hp : p.Prime)
    (hkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) {S : Subgroup H} (hdvd : p ∣ Nat.card S) :
    p ∣ Nat.card (S.map φ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) p hdvd
  have hxH : orderOf (x : H) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hxp : (x : H) ^ p = 1 := by rw [← hxH]; exact pow_orderOf_eq_one _
  have hne : φ x ≠ 1 := by
    intro h1
    have h2 := hkerp _ (MonoidHom.mem_ker.mpr h1) hxp
    rw [h2, orderOf_one] at hxH
    exact hp.one_lt.ne hxH
  have hφx : orderOf (φ x) = p := orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) hne
  rw [← hφx]
  exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_map_of_mem φ x.2)

end Cover

section Coords

variable {s p : ℕ}

theorem coord_swap (i j : Fin s) (f : Fin s → Multiplicative (ZMod p)) :
    swapMap i j (fun k => toAdd (f k)) = fun k => toAdd (permAut (Equiv.swap i j) f k) := by
  funext k
  simp [swapMap, permAut_apply, Equiv.swap_inv]

theorem coord_neg (m : Fin s) (f : Fin s → Multiplicative (ZMod p)) :
    negMap m (fun k => toAdd (f k)) = fun k => toAdd (sgnAut m f k) := by
  funext k
  by_cases hk : k = m
  · subst hk
    simp [negMap, sgnAut_apply]
  · simp [negMap, sgnAut_apply, Function.update_of_ne hk]

theorem coord_sswap {i j : Fin s} (hij : i < j) (f : Fin s → Multiplicative (ZMod p)) :
    sswapMap i j (fun k => toAdd (f k)) =
      fun k => toAdd (omPlusRefl p (⟨(i, j), hij⟩, true) f k) := by
  rw [omPlusRefl_true_eq_conj (p := p) hij, MulAut.mul_apply, MulAut.mul_apply, sswapMap,
    coord_neg, coord_swap, coord_neg]

end Coords

theorem card_coord (p k : ℕ) [NeZero p] :
    Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
  congr 1
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)

end CFSG.StandardType.RealKGCover

end
