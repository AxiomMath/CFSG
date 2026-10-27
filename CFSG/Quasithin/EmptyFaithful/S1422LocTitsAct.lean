module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

namespace S1422Loc

section Action

variable {G : Type*} [Group G]

@[expose] def conjAutOf {P : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    MulAut ↥P where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp y.2
    rwa [inv_inv] at h⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjAutOf_apply {P : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G))
    (y : P) : (conjAutOf hg y : G) = g * y * g⁻¹ := rfl

theorem normal_subgroupOf_of_le_normalizer {P F : Subgroup G}
    (hPF : P ≤ Subgroup.normalizer (F : Set G)) : (F.subgroupOf P).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have := (Subgroup.mem_normalizer_iff.mp (hPF g.2) x).mp hx
  simpa using this

@[expose] noncomputable def quotAut {P F : Subgroup G} [(F.subgroupOf P).Normal] {g : G}
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) (hgF : g ∈ Subgroup.normalizer (F : Set G)) :
    MulAut (↥P ⧸ F.subgroupOf P) :=
  QuotientGroup.congr (F.subgroupOf P) (F.subgroupOf P) (conjAutOf hgP) (by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp hgF x).mp hx
    · intro hy
      refine ⟨(conjAutOf hgP).symm y, ?_, by simp⟩
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have hgi : g⁻¹ ∈ Subgroup.normalizer (F : Set G) := Subgroup.inv_mem _ hgF
      have := (Subgroup.mem_normalizer_iff.mp hgi (y : G)).mp hy
      show g⁻¹ * (y : G) * g ∈ F
      simpa using this)

theorem quotAut_mk {P F : Subgroup G} [(F.subgroupOf P).Normal] {g : G}
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) (hgF : g ∈ Subgroup.normalizer (F : Set G))
    (x : ↥P) : quotAut hgP hgF (QuotientGroup.mk x) = QuotientGroup.mk (conjAutOf hgP x) := by
  unfold quotAut
  exact QuotientGroup.congr_mk _ _ _ _ x

@[expose] noncomputable def quotAction {P F N : Subgroup G} [(F.subgroupOf P).Normal]
    (hNP : N ≤ Subgroup.normalizer (P : Set G)) (hNF : N ≤ Subgroup.normalizer (F : Set G)) :
    N →* MulAut (↥P ⧸ F.subgroupOf P) where
  toFun g := quotAut (hNP g.2) (hNF g.2)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    rw [quotAut_mk]
    show _ = (QuotientGroup.mk x : ↥P ⧸ F.subgroupOf P)
    congr 1
    apply Subtype.ext
    simp [conjAutOf_apply]
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    show quotAut (hNP (g * h).2) (hNF (g * h).2) (QuotientGroup.mk x) =
      quotAut (hNP g.2) (hNF g.2) (quotAut (hNP h.2) (hNF h.2) (QuotientGroup.mk x))
    rw [quotAut_mk, quotAut_mk, quotAut_mk]
    congr 1
    apply Subtype.ext
    simp [conjAutOf_apply, mul_assoc]

theorem quotAction_mk {P F N : Subgroup G} [(F.subgroupOf P).Normal]
    (hNP : N ≤ Subgroup.normalizer (P : Set G)) (hNF : N ≤ Subgroup.normalizer (F : Set G))
    (g : N) (x : ↥P) :
    quotAction hNP hNF g (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨(g : G) * x * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hNP g.2) x).mp x.2⟩ : ↥P) :=
  quotAut_mk (hNP g.2) (hNF g.2) x

end Action

end S1422Loc

end CFSG.Quasithin
