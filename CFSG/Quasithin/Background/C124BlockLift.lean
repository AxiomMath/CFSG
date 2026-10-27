module

public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore
public import CFSG.Quasithin.Background.C124Core
public import CFSG.Quasithin.Background.C124L2PBasic
public import CFSG.Quasithin.Background.C124Z3Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure YData (X V L R : Subgroup G) (hV : IsElemAbelian 2 V) (Y : Subgroup G) : Prop where
  setup : L2P.Setup X R Y V hV ∨ Z3.Setup X R Y
  le_L : Y ≤ L
  gen : X = Y ⊔ (X ⊓ Subgroup.normalizer (baum R : Set G))
  not_cent : ¬ Y ≤ Subgroup.centralizer (V : Set G)
  closure : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal → Y ≤ N → L ≤ N
  Q_norm : pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set G)

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian E.red.2.2.1

theorem pCoreOf_L_le_Q : pCoreOf 2 L ≤ pCoreOf 2 X :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans E.hLX)
    (E.normal.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)

theorem comm_V_L_le : ⁅V, L⁆ ≤ pCoreOf 2 L := by
  have h1 : ⁅V, L⁆ ≤ V :=
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing V L E.hLN
  have h2 : ⁅V, L⁆ ≤ L := Subgroup.commutator_le.2 fun v hv l hl => by
    have hvn : v ∈ Subgroup.normalizer (L : Set G) := E.normal (E.red.1 hv)
    have := (Subgroup.mem_normalizer_iff.1 hvn l).1 hl
    simpa [commutatorElement_def] using L.mul_mem this (L.inv_mem hl)
  have hn : L ≤ Subgroup.normalizer ((pCoreOf 2 X ⊓ L : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(E.hLX.trans (le_normalizer_pCoreOf 2 X)) hl, Subgroup.le_normalizer hl⟩
  have h3 : pCoreOf 2 X ⊓ L ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hn
      ((pCoreOf_isPGroup 2 X).to_le inf_le_left)
  exact fun x hx => h3 ⟨le_pCoreOf_of_reduced E.red (h1 hx), h2 hx⟩

end EntryPlus

end CFSG.Quasithin.C124
