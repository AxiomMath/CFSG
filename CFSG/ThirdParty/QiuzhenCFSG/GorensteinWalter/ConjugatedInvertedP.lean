module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- If `g` conjugates the central involution `t` to `t₂`, then:
- a `t`-inverted subgroup `P` becomes `t₂`-inverted after conjugation by `g`;
- `C_G(t₂)` normalizes that conjugate whenever `C_G(t) ≤ N(P)`. -/
public theorem conjugate_inverted_normalizer
    {G : Type u} [Group G] (g t t2 : G) (P : Subgroup G)
    (hgt : g * t * g⁻¹ = t2)
    (ht2 : IsInvolution t2)
    (hPinvert : BenderGlauberman.IsInvertedBy t P)
    (hNP : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (P : Set G)) :
    BenderGlauberman.IsInvertedBy t2
      (P.map (MulAut.conj g).toMonoidHom) ∧
      Subgroup.centralizer ({t2} : Set G) ≤
        Subgroup.normalizer
          ((P.map (MulAut.conj g).toMonoidHom) : Set G) := by
  let Pg : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  constructor
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hm : t2 * (g * (p : G) * g⁻¹) * t2⁻¹ =
        (g * (p : G) * g⁻¹)⁻¹ := by
      calc
        t2 * (g * (p : G) * g⁻¹) * t2⁻¹ =
            (g * t * g⁻¹) * (g * (p : G) * g⁻¹) * (g * t * g⁻¹)⁻¹ := by
          rw [hgt]
        _ = g * (t * (p : G) * t⁻¹) * g⁻¹ := by group
        _ = g * (p : G)⁻¹ * g⁻¹ := by rw [hPinvert (p : G) hp]
        _ = (g * (p : G) * g⁻¹)⁻¹ := by group
    simpa [Pg, MulAut.conj_apply] using hm
  · intro z hz
    change z ∈ Subgroup.normalizer (Pg : Set G)
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    have hzcomm : z * t2 = t2 * z :=
      (Subgroup.mem_centralizer_singleton_iff.mp hz)
    have ht_eq : t = g⁻¹ * t2 * g := by
      calc
        t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * t2 * g := by rw [hgt]
    have hforward_general : ∀ w : G, w * t2 = t2 * w →
        ∀ y : G, y ∈ Pg → w * y * w⁻¹ ∈ Pg := by
      intro w hwcomm y hy
      rcases Subgroup.mem_map.mp hy with ⟨p, hp, rfl⟩
      let a : G := g⁻¹ * w * g
      have haCent : a ∈ Subgroup.centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc
          a * t = (g⁻¹ * w * g) * (g⁻¹ * t2 * g) := by rw [ht_eq]
          _ = g⁻¹ * (w * t2) * g := by group
          _ = g⁻¹ * (t2 * w) * g := by rw [hwcomm]
          _ = (g⁻¹ * t2 * g) * (g⁻¹ * w * g) := by group
          _ = t * a := by rw [← ht_eq]
      have haN : a ∈ Subgroup.normalizer (P : Set G) := hNP haCent
      have haP : a * (p : G) * a⁻¹ ∈ P :=
        ((Subgroup.mem_normalizer_iff.mp haN) (p : G)).1 hp
      have hw_eq : w = g * a * g⁻¹ := by
        dsimp [a]
        group
      have htarget : w * (g * (p : G) * g⁻¹) * w⁻¹ =
          g * (a * (p : G) * a⁻¹) * g⁻¹ := by
        calc
          w * (g * (p : G) * g⁻¹) * w⁻¹ =
              (g * a * g⁻¹) * (g * (p : G) * g⁻¹) * (g * a * g⁻¹)⁻¹ := by
            rw [hw_eq]
          _ = g * (a * (p : G) * a⁻¹) * g⁻¹ := by group
      exact Subgroup.mem_map.mpr
        ⟨a * (p : G) * a⁻¹, haP,
          by
            change (g * (a * (p : G) * a⁻¹) * g⁻¹) =
              w * (g * (p : G) * g⁻¹) * w⁻¹
            exact htarget.symm⟩
    constructor
    · intro hx
      exact hforward_general z hzcomm x hx
    · intro hx
      have ht2inv : t2⁻¹ = t2 :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht2.2)
      have hzinvcomm : z⁻¹ * t2 = t2 * z⁻¹ := by
        have h := congrArg Inv.inv hzcomm
        simpa [mul_inv_rev, ht2inv] using h.symm
      have hy := hforward_general z⁻¹ hzinvcomm (z * x * z⁻¹) hx
      simpa [mul_assoc] using hy

end CFSG.GorensteinWalter
