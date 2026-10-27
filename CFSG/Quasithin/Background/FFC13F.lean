module

public import CFSG.Quasithin.Background.FFC11B

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

theorem alt_map_conj {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    (alternatingGroup (Fin n)).map (MulAut.conj ρ).toMonoidHom = alternatingGroup (Fin n) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem y hy ρ
  · intro hx
    refine ⟨ρ⁻¹ * x * ρ, ?_, ?_⟩
    · have := (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem x hx ρ⁻¹
      simpa using this
    · show ρ * (ρ⁻¹ * x * ρ) * ρ⁻¹ = x
      group

structure AsB69DeepInputsFour : Prop where
  sp4 : AsB69NoRankTwoSp4
  a6 : AsB69NoRankTwoA6
  tripleA6 : AsB69NoRankTwoTripleA6
  g2 : AsB69NoG2

end B69

end CFSG.Quasithin
