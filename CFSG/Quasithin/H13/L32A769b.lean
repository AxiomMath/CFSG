module

public import CFSG.Quasithin.H13.L32A769a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure Conf69 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (x : G) : Prop where
  hyp : Hyp147 G T L V
  hMod : StmtL32NModule
  h63 : Thm14_7_63
  hF : HypF98 T V L (fsuV1 T V) V (hz T V)
  h1222 : Stmt12_2_2
  h1332 : Stmt13_3_2
  h1334 : A6.Stmt13_3_4
  h64 : Remark14_7_64
  le_R1 : conjSub x (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)
  sup_eq : conjSub x (fsuU T V) ⊔ pCoreOf 2 (hz T V) = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)
  comm_le : ⁅fsuU T V, conjSub x (fsuU T V)⁆ ≤ fsuU T V ⊓ conjSub x (fsuU T V)
  U_le : fsuU T V ≤ conjSub x (hz T V)

namespace Conf69

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {x : G}
  (C : Conf69 G T L V x)
include C

theorem comm : ∀ a ∈ conjSub x (fsuU T V), ∀ b ∈ conjSub x (fsuU T V), a * b = b * a := by
  intro a ha b hb
  rw [mem_conjSub] at ha hb
  have h1 := F7.isElemAbelian_comm (isElemAbelian_fsuU_of C.hyp C.hMod) ha hb
  calc a * b = x * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * b * x) * (x⁻¹ * a * x)) * x⁻¹ := by rw [h1]
    _ = b * a := by group

omit [Finite G] C in
theorem Z_le : conjSub x (fsuV1 T V) ≤ conjSub x (fsuU T V) :=
  conjSub_mono x (inf_le_left.trans (le_conjClosure V _))

theorem card_Z : Nat.card ↥(conjSub x (fsuV1 T V)) = 2 := by
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj x).injective]
  exact C.hF.card_V₁

theorem GW_le : conjSub x (hz T V) ≤ Subgroup.normalizer (conjSub x (fsuV1 T V) : Set G) := by
  rw [conjSub_normalizer]
  exact conjSub_mono x C.hF.H_normalizes_V₁

theorem pCoreOf_eq : conjSub x (pCoreOf 2 (hz T V)) =
    centralizerMod (conjSub x (fsuV1 T V)) (conjSub x (hz T V)) (conjSub x (fsuU T V)) := by
  rw [C.hF.pCoreOf_eq_centralizerMod, conjSub_centralizerMod,
    ← fsuU_eq_conjClosure_hz C.hMod C.hyp]

theorem cent :
    fsuU T V ⊓ Subgroup.centralizer (conjSub x (fsuU T V) : Set G) = V ⊔ u0 T V ∧
      ⁅fsuU T V, conjSub x (fsuU T V)⁆ ⊔ fsuV1 T V = V ⊔ u0 T V ∧
      (fsuU T V ⊓ conjSub x (fsuU T V)) ⊔ fsuV1 T V = V ⊔ u0 T V :=
  cent_eq_of_sup_eq C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 C.h64 C.le_R1 C.sup_eq
    C.comm_le C.comm

theorem inf_QW : fsuU T V ⊓ conjSub x (pCoreOf 2 (hz T V)) = V ⊔ u0 T V := by
  rw [C.pCoreOf_eq]
  exact inf_centralizerMod_eq C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 C.h64 C.le_R1
    C.sup_eq C.comm_le C.comm Z_le C.card_Z C.U_le C.GW_le

theorem exists_comm_not_mem {u : G} (hu : u ∈ fsuU T V) (huV : u ∉ V ⊔ u0 T V) :
    ∃ w ∈ conjSub x (fsuU T V), u * w * u⁻¹ * w⁻¹ ∉ conjSub x (fsuV1 T V) :=
  L32A.exists_comm_not_mem C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 C.le_R1 C.sup_eq
    C.comm Z_le C.card_Z hu huV

end Conf69

structure Sym69 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (x x' y : G) : Prop where
  c : Conf69 G T L V x
  c' : Conf69 G T L V x'
  hU : conjSub y (fsuU T V) = conjSub x (fsuU T V)
  hW : conjSub y (conjSub x' (fsuU T V)) = fsuU T V
  hH : conjSub y (hz T V) = conjSub x (hz T V)
  hH' : conjSub y (conjSub x' (hz T V)) = hz T V
  hV1 : conjSub y (fsuV1 T V) = conjSub x (fsuV1 T V)

end CFSG.Quasithin.H13.L32A
