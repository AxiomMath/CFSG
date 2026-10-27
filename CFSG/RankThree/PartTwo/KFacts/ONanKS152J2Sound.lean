module

public import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.RankThree.Native.DerivedGenerators
public import Certificates.Data.Item434SporGenKit

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS152J2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open scoped commutatorElement

variable {n : ℕ}

theorem mem_sup_zpowers_conj {G : Type*} [Group G] {W : Subgroup G} {k r x : G}
    (hk : k ∈ Subgroup.normalizer (W : Set G)) (hx : k⁻¹ * x * k ∈ W ⊔ Subgroup.zpowers r) :
    x ∈ W ⊔ Subgroup.zpowers (k * r * k⁻¹) := by
  have hmap : (W ⊔ Subgroup.zpowers r).map (MulAut.conj k).toMonoidHom =
      W ⊔ Subgroup.zpowers (k * r * k⁻¹) := by
    have hW' : W.map (MulAut.conj k).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hk
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hW']
    rfl
  rw [← hmap]
  exact ⟨_, hx, by show k * (k⁻¹ * x * k) * k⁻¹ = x; group⟩

@[expose] def genGroup (n : ℕ) (ga gb : Array ℕ) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure ({permOfArr n ga, permOfArr n gb} : Set (Equiv.Perm (Fin n)))

end CFSG.RankThree.PartTwo.KFacts.KS152J2
