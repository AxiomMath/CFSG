module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Odd centers from odd quotient kernels

When restriction of an odd-kernel quotient map to a subgroup has kernel
equal to that subgroup's center, the center has odd order.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If the kernel of the quotient restriction `E → Ē` is exactly
`Z(E)` and the ambient quotient kernel `O` has odd order, then `Z(E)` has odd
order. -/
public theorem center_odd_of_quotient_restriction_ker_eq_center
    {H : Type u} [Group H] [Finite H]
    (E O : Subgroup H) [O.Normal] (hOodd : Odd (Nat.card O))
    (hker :
      let q : H →* H ⧸ O := QuotientGroup.mk' O
      let Ebar : Subgroup (H ⧸ O) := E.map q
      let f : E →* Ebar :=
        (q.comp E.subtype).codRestrict Ebar (fun x =>
          Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
      f.ker = Subgroup.center E) :
    Odd (Nat.card (Subgroup.center E)) := by
  classical
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  let f : E →* Ebar :=
    (q.comp E.subtype).codRestrict Ebar (fun x =>
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hker' : f.ker = Subgroup.center E := by
    simpa [q, Ebar, f] using hker
  have hcenterO : ∀ z : E, z ∈ Subgroup.center E → (z : H) ∈ O := by
    intro z hz
    have hzker : z ∈ f.ker := by
      rw [hker']
      exact hz
    have hfz : f z = 1 := MonoidHom.mem_ker.mp hzker
    have hqz : q z = 1 := congrArg Subtype.val hfz
    exact (QuotientGroup.eq_one_iff (N := O) (z : H)).mp hqz
  let ι : Subgroup.center E →* O := {
    toFun := fun z => ⟨(z : E), hcenterO z z.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : O => (z : H)) hxy
  exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_injective ι hι)

end CFSG.GorensteinWalter
