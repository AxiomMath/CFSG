module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- If `g` conjugates `t` to `t₂`, then conjugating a `t`-inverted
subgroup by `g` gives a `t₂`-inverted subgroup. -/
public theorem conjugated_inverted_subgroup
    {G : Type u} [Group G] (g t t2 : G) (P : Subgroup G)
    (hgt : g * t * g⁻¹ = t2)
    (hPinvert : BenderGlauberman.IsInvertedBy t P) :
    BenderGlauberman.IsInvertedBy t2
      (P.map (MulAut.conj g).toMonoidHom) := by
  intro x hx
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
  simpa [MulAut.conj_apply] using hm

end CFSG.GorensteinWalter
