module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.DGroupInvariantPCommutator
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# D-group commutator control through an invariant closure

This packages the normal-closure repair needed when a self-commutator is not
known directly to be invariant under the relevant involution centralizer.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `P0 ≤ P` is its own commutator with an involution, it lies in the
odd `p`-core of a D-group whenever the involution centralizer normalizes `P`.
The proof first closes `P0` under that centralizer while remaining inside
the `p`-group `P`. -/
public theorem commutator_le_qCoreOf_via_invariant_closure
    {G : Type u} [Group G] [Finite G]
    (B P P0 : Subgroup G) (p : ℕ)
    (hD : IsDGroup B) (hp : p.Prime) (hpodd : Odd p)
    (hP0B : P0 ≤ B) (hPp : IsPGroup p P)
    {t : G} (htB : t ∈ B) (ht : IsInvolution t)
    (hDP : B ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hP0P : P0 ≤ P)
    (hP0self : ⁅P0, Subgroup.zpowers t⁆ = P0) :
    P0 ≤ qCoreOf B p := by
  classical
  let D : Subgroup G := B ⊓ Subgroup.centralizer ({t} : Set G)
  let K : Subgroup G := D ⊔ P0
  have hDK : D ≤ Subgroup.normalizer (P : Set G) := by
    simpa [D] using hDP
  have hP0K : P0 ≤ K := le_sup_right
  have hKnormP : K ≤ Subgroup.normalizer (P : Set G) :=
    sup_le hDK (hP0P.trans P.le_normalizer)
  have hKB : K ≤ B := sup_le inf_le_left hP0B
  let P0K : Subgroup K := P0.subgroupOf K
  let Rk : Subgroup K := Subgroup.normalClosure (P0K : Set K)
  let R : Subgroup G := Rk.map K.subtype
  have hP0R : P0 ≤ R := by
    intro x hx
    let xK : K := ⟨x, hP0K hx⟩
    have hxP0K : xK ∈ P0K := hx
    have hxRk : xK ∈ Rk := Subgroup.le_normalClosure hxP0K
    exact Subgroup.mem_map.mpr ⟨xK, hxRk, rfl⟩
  have hRleP : R ≤ P := by
    have : (P.subgroupOf K).Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer hKnormP
    have hRkP : Rk ≤ P.subgroupOf K := by
      apply Subgroup.normalClosure_le_normal
      intro x hx
      exact hP0P hx
    rintro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xK, hxRk, rfl⟩
    exact hRkP hxRk
  have hRleK : R ≤ K := by
    rintro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xK, hxRk, rfl⟩
    exact xK.property
  have hRsub : R.subgroupOf K = Rk := by
    ext x
    change (x : G) ∈ R ↔ x ∈ Rk
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, heq⟩
      have hyx : y = x := Subtype.ext heq
      simpa [hyx] using hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hRnormalK : (R.subgroupOf K).Normal := by
    rw [hRsub]
    infer_instance
  have hKnormR : K ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hRleK
  have hDnormR : D ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans hKnormR
  have hRp : IsPGroup p R := hPp.to_le hRleP
  have hRcore : ⁅R, Subgroup.zpowers t⁆ ≤ qCoreOf B p :=
    commutator_le_qCoreOf_of_isDGroup B R p hD hp hpodd
      (hRleK.trans hKB) hRp htB ht (by simpa [D] using hDnormR)
  rw [← hP0self]
  exact (Subgroup.commutator_mono hP0R le_rfl).trans hRcore

end CFSG.GorensteinWalter
