module

public import CFSG.Quasithin.EmptyFaithful.S153YA5Std
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSplit

public section

namespace CFSG.Quasithin.YG.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

structure Cfg (H S L : Subgroup G) where
  hcs : WGen H S L
  hj : conjJoin S L = L
  h5 : IsAltType L 5
  P : A5Pi L
  hJ : P.im (thompsonJ S) = Estd
  hB : P.im (baum S) = Estd
  hS : P.im S = Dstd
  hX : P.im (L ⊔ baum S) = ⊤

theorem nonempty_cfg {H S L : Subgroup G} (hcs : WGen H S L)
    (hj : conjJoin S L = L) (h5 : IsAltType L 5) : Nonempty (Cfg H S L) := by
  obtain ⟨P⟩ := nonempty_a5pi (C56.isShort hcs) h5
  obtain ⟨P', hJ, hB, hS, hX⟩ := a5_core_std hcs hj P
  exact ⟨⟨hcs, hj, h5, P', hJ, hB, hS, hX⟩⟩

namespace Cfg

variable {H S L : Subgroup G} (C : Cfg H S L)

include C in
theorem hSN : S ≤ Subgroup.normalizer (L : Set G) := C56.S_le_normalizer C.hj

include C in
theorem hUQ : blockU L ≤ pCoreOf 2 H := C56.blockU_le_pCoreOf C.hcs C.hj

include C in
theorem hQ : H ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 H :=
  C56.inf_centralizer_eq C.hcs C.hj

end Cfg

end CFSG.Quasithin.YG.AppC
