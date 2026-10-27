module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# `PSL₂` Klein-four centralizer: Huppert-normalizer endpoint

The conjugate-torus bridge specialized to `PSL₂`.  The final supply
theorem will feed the Huppert II.8.5(a) partition and II.8.3/II.8.4
normalizer data into this endpoint.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem psl2_no_kleinFour_of_torus_normalizer
    {F : Type u} [Field F] [Finite F]
    (A V : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))
    (g : BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)
    (U : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))
    (w : BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)
    (hAne : A ≠ ⊥)
    (hAodd : ∀ a : BenderSuzuki.MatrixGroups.PSL2MatrixGroup F,
      a ∈ A → Odd (orderOf a))
    (hAt : A ≤ U.map (MulAut.conj g).toMonoidHom)
    (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : BenderSuzuki.MatrixGroups.PSL2MatrixGroup F,
      x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hN : Subgroup.normalizer
      ((A.map (MulAut.conj g⁻¹).toMonoidHom :
        Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) :
        Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) =
        U ⊔ Subgroup.zpowers w)
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer
      (A : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))) :
    False :=
  no_kleinFour_centralizes_odd_cyclic_of_conjugate_torus
    A V g U w hAne hAodd hAt hUcyc hwU hwsq hwinv hN hVK hVleC

public theorem psl2_no_kleinFour_centralizes_sylow
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hodd : Odd (Nat.card F))
    (P : Sylow p (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))
    (V : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer
      ((P : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) :
        Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))) :
    False := by
  classical
  obtain ⟨Q, hQeq⟩ := psl2UpperUnipotent_isSylow (K := F) hFcard
  obtain ⟨h, hh⟩ :=
    MulAction.exists_smul_eq
      (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) P Q
  have hset : (MulAut.conj h) •
      (P : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) =
      (Q : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) := by
    rw [← Sylow.coe_smul, hh]
  have hsetU : (MulAut.conj h) •
      (P : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) =
      (psl2UpperUnipotentSubgroup F : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) := by
    rw [hset]
    exact congrArg (fun S : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) =>
      (S : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F))) hQeq
  have hPmap :
      (P : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)).map
        (MulAut.conj h).toMonoidHom = psl2UpperUnipotentSubgroup F := by
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      have hsmul : (MulAut.conj h) p ∈ (MulAut.conj h) •
          (P : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) :=
        Set.smul_mem_smul_set hp
      rwa [hsetU] at hsmul
    · intro hx
      have hx' : x ∈ (MulAut.conj h) •
          (P : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) := by
        exact hsetU.symm ▸ hx
      refine ⟨h⁻¹ * x * h, ?_, ?_⟩
      · exact (Set.mem_smul_set_iff_inv_smul_mem.mp hx')
      · simp [MulAut.conj_apply]
        group
  have hV'raw := centralizer_map_le_of_conj P V h⁻¹ hVleC
  have hV' : V.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.centralizer
        ((P.map (MulAut.conj h).toMonoidHom :
          Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) :
          Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) := by
    simpa using hV'raw
  have hV'U : V.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.centralizer
        (psl2UpperUnipotentSubgroup F : Set (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) := by
    rw [hPmap] at hV'
    exact hV'
  have hV'K : IsKleinFour (V.map (MulAut.conj h).toMonoidHom) :=
    isKleinFour_map_mulEquiv V hVK (MulAut.conj h)
  exact no_kleinFour_centralizes_psl2UpperUnipotentSubgroup hodd
    (V.map (MulAut.conj h).toMonoidHom) hV'K hV'U

end CFSG.GorensteinWalter
