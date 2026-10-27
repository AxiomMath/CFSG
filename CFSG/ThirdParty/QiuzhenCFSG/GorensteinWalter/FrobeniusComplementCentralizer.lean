module

public import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- In a Frobenius group with complement `H` and normal kernel `K`, the
centralizer of a nontrivial element of `H` is contained in `H`. -/
public theorem centralizer_mem_le_complement
    {G : Type u} [Group G] (H K : Subgroup G)
    (hcomp : H.IsComplement' K)
    (hKnormal : K.Normal)
    (hfix : ∀ h : G, h ∈ H → h ≠ 1 →
      ∀ k : G, k ∈ K → k ≠ 1 → h * k * h⁻¹ ≠ k)
    {h : G} (hh : h ∈ H) (hne : h ≠ 1) :
    Subgroup.centralizer ({h} : Set G) ≤ H := by
  intro g hg
  have hgcomm : h * g = g * h :=
    (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  have hcentral : h * g * h⁻¹ = g := by
    calc
      h * g * h⁻¹ = (g * h) * h⁻¹ := by rw [hgcomm]
      _ = g := by group
  obtain ⟨x, hx, huniq⟩ := hcomp.existsUnique g
  let a : H := x.1
  let b : K := x.2
  have hx_eq : (a : G) * (b : G) = g := hx
  let aH : H := ⟨h * (a : G) * h⁻¹,
    H.mul_mem (H.mul_mem hh (a : H).2) (H.inv_mem hh)⟩
  let bK : K := ⟨h * (b : G) * h⁻¹,
    hKnormal.conj_mem (b : G) (b : K).2 h⟩
  let y : H × K := (aH, bK)
  have hprod : (y.1 : G) * (y.2 : G) = g := by
    change (h * (a : G) * h⁻¹) * (h * (b : G) * h⁻¹) = g
    calc
      (h * (a : G) * h⁻¹) * (h * (b : G) * h⁻¹) =
          h * ((a : G) * (b : G)) * h⁻¹ := by group
      _ = h * g * h⁻¹ := by rw [hx_eq]
      _ = g := hcentral
  have hyx : y = x := huniq y (by simpa [hprod] using hprod)
  have hb_eq : h * (b : G) * h⁻¹ = (b : G) := by
    have hcong : (bK : G) = (b : G) :=
      congrArg (fun z : H × K => (z.2 : G)) hyx
    change h * (b : G) * h⁻¹ = (b : G)
    exact hcong
  by_cases hb1 : (b : G) = 1
  · have hg_eq : g = (a : G) := by
      simpa [hb1, hx_eq] using hx_eq.symm
    rw [hg_eq]
    exact (a : H).2
  · exfalso
    exact hfix h hh hne (b : G) (b : K).2 hb1 hb_eq

end CFSG.GorensteinWalter
