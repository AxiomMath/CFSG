module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGConfig.odd_commutator_pPrimeCoreOf_map_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (g : G)
    {d : G} (hd : d ∈ D.map (MulAut.conj g).toMonoidHom) (hd1 : d ≠ 1) :
    Odd (Nat.card ↥⁅J.map (MulAut.conj g).toMonoidHom,
      LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆) := by
  obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hd
  have hd₀1 : d₀ ≠ 1 := by
    rintro rfl
    exact hd1 (map_one _)
  have h6 := (hcfg.1.2.2.2.2.2.2.2.2.2.2 D J hcfg.2.2).2 d₀ hd₀ hd₀1
  have hcent : Subgroup.centralizer ({(MulAut.conj g).toMonoidHom d₀} : Set G) =
      (Subgroup.centralizer ({d₀} : Set G)).map (MulAut.conj g).toMonoidHom :=
    (CFSG.centralizer_singleton_map (MulAut.conj g) d₀).symm
  rw [hcent, largeEvenPPrimeCoreOf_map_conj, ← Subgroup.map_commutator,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h6

end CFSG.StandardType

end
