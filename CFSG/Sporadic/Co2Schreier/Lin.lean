module

public import CFSG.Sporadic.Co2Cert.Faithful
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Monster.B.Co2

@[expose] def co2GEquivP :
    co2G ≃* co2P :=
  (MonoidHom.ofInjective co2Rho_injective).trans (MulEquiv.subgroupCongr co2Rho_range)

theorem co2GEquivP_apply
    (g : co2G) : (co2GEquivP g : Equiv.Perm (Fin 2300)) = co2Rho g := rfl

@[expose] def linP :
    co2P →* (Co2V ≃ₗ[ZMod 2] Co2V) :=
  co2G.subtype.comp co2GEquivP.symm.toMonoidHom

theorem linP_vec
    (g : co2P) (i : Fin 2300) :
    linP g (co2Vec i) = co2Vec ((g : Equiv.Perm (Fin 2300)) i) := by
  have h : (g : Equiv.Perm (Fin 2300)) = co2Rho (co2GEquivP.symm g) := by
    rw [← co2GEquivP_apply, MulEquiv.apply_symm_apply]
  rw [h, co2Vec_rho]
  rfl

theorem linP_injective :
    Function.Injective linP := by
  intro g h hgh
  refine Subtype.ext (Equiv.ext fun i => Fin.ext (co2Vec_injective (Fin.isLt _) (Fin.isLt _) ?_))
  rw [← linP_vec, ← linP_vec, hgh]

@[expose] def xorBits (vs : Array ℕ) (m : ℕ) : ℕ :=
  (List.range vs.size).foldl (fun acc i => if m.testBit i then acc ^^^ vs[i]! else acc) 0

theorem toVecD_xorBits (vs : Array ℕ) (m : ℕ) :
    toVecD 22 (xorBits vs m) = ∑ i ∈ Finset.range vs.size,
      if m.testBit i then toVecD 22 vs[i]! else 0 := by
  rw [xorBits, foldl_xor_toVecD, toVecD_zero, zero_add]

theorem co2Vec_eq_toVecD
    {i : ℕ} (hi : i < 2300) : co2Vec i = toVecD 22 co2PackedVecs[i]! :=
  co2Vec_eq hi

end CFSG.Sporadic.Co2Schreier
