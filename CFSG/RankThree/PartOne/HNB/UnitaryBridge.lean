
module

public import CFSG.RankThree.PartOne.HNB.UnitaryBridgeBase

public import Certificates.Certificate14969
import CFSG.Monster.B.Mathieu.Order

public section

namespace CFSG.RankThree.PartOne.HNB

open HNUnitaryBridge CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem nonempty_mulEquiv_psu3 {I : Type*} [Group I]
    (g : Fin 6 → I) (hgen : Subgroup.closure (Set.range g) = ⊤) (ρ : I →* Equiv.Perm (Fin 50))
    (hinj : Function.Injective ρ)
    (hρ : ∀ (k : Fin 6) (x : Fin 50), (ρ (g k) x : ℕ) = (smallPerms[(k : ℕ)]!)[(x : ℕ)]!)
    (hcard : Nat.card I = 126000) : Nonempty (I ≃* PSU3) := by
  have hg : ∀ k : Fin 6, ρ (g k) = CFSG.Monster.B.Co2.permOfArr 50 smallPerms[(k : ℕ)]! :=
    fun k => (CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep fun x => (hρ k x).symm).symm
  have hrange : ρ.range = Subgroup.closure (Set.range fun k : Fin 6 =>
      CFSG.Monster.B.Co2.permOfArr 50 smallPerms[(k : ℕ)]!) := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, ← Set.range_comp]
    exact congrArg (fun f => Subgroup.closure (Set.range f)) (funext hg)
  obtain ⟨e⟩ := Certificates.certificate14969
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans e⟩

end CFSG.RankThree.PartOne.HNB
