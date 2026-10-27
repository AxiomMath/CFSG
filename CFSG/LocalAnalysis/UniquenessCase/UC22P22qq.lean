module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.IVK
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qq_frattini {p : ℕ} [Fact p.Prime] {S Y M : Subgroup G} (hSY : IsSylowOf p S Y)
    (hYn : ∀ m ∈ M, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y) :
    ∀ m ∈ M, ∃ y ∈ Y, y⁻¹ * m ∈ normalizer (S : Set G) := by
  intro m hm
  have hYmap : Y.map (MulAut.conj m).toMonoidHom = Y :=
    uc22p22qi_map_eq_of_conj_mem (M := M) (K := Y) hYn hm
  set S' : Subgroup G := S.map (MulAut.conj m).toMonoidHom with hS'def
  have hS'Y : IsSylowOf p S' Y := by
    rw [isSylowOf_iff] at hSY ⊢
    obtain ⟨hle, hpg, hrel⟩ := hSY
    refine ⟨?_, hpg.of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj m).injective), ?_⟩
    · rw [← hYmap]
      exact Subgroup.map_mono hle
    · rw [← hYmap, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj m).injective]
      exact hrel
  obtain ⟨y, hy, hk⟩ := hSY.exists_mem_conj hS'Y
  refine ⟨y, hy, uc22p22qk_mem_normalizer fun s hs => ?_⟩
  have h1 : m * s * m⁻¹ ∈ S' := ⟨s, hs, rfl⟩
  have h2 := (hk _).1 h1
  simpa [mul_assoc] using h2

theorem uc22p22qq_normalizer_centralizer_le {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L P₁ : Subgroup G}
    (hL : LieModel ↥L .PSL 2 p n) (hP₁L : P₁ ≤ L) (hS : IsSylowOf p (P₁.subgroupOf L) ⊤) {x : G}
    (hxL : x ∈ normalizer (L : Set G)) (hxc : ∀ y ∈ P₁, x * y * x⁻¹ = y) :
    ∃ d ∈ centralizer (L : Set G), ∃ a ∈ P₁, x = d * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hFf, hFfin, e, hF, hFq⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hp hp2 hL
  obtain ⟨-, hSp, hSnd⟩ := isSylowOf_iff.1 hS
  let W : Sylow p ↥L := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSnd)
  have hWmem : ∀ k : ↥L, k ∈ (W : Subgroup ↥L) ↔ (k : G) ∈ P₁ := fun k => Subgroup.mem_subgroupOf
  obtain ⟨c, hstd, -⟩ := L2Borel.exists_isStd hp hFq e W
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := L2Borel.two_ne_zero_of_odd_card hodd
  let α : MulAut ↥L := UC6.conjOn L hxL
  have hfix : ∀ k : ↥L, (k : G) ∈ P₁ → α k = k := by
    intro k hk
    apply Subtype.ext
    change x * (k : G) * x⁻¹ = k
    exact hxc _ hk
  have hstab : α ∈ MulAction.stabilizer (MulAut ↥L) (W : Subgroup ↥L) := by
    rw [L2Borel.mem_stabilizer_iff_forall]
    intro k
    constructor
    · intro hk
      have hk2 : α k = k := α.injective (hfix _ ((hWmem _).1 hk))
      rw [← hk2]
      exact hk
    · intro hk
      rw [hfix _ ((hWmem _).1 hk)]
      exact hk
  have htriv : ∀ t, α (L2Borel.wt (L2Borel.eConj e c) t) = L2Borel.wt (L2Borel.eConj e c) t := fun t =>
    hfix _ ((hWmem _).1 (hstd.wt_mem t))
  obtain ⟨b, hb⟩ := L2Borel.trivial_action hstd h2 hstab htriv
  set w : ↥L := L2Borel.wt (L2Borel.eConj e c) b with hw
  have hwP₁ : (w : G) ∈ P₁ := (hWmem _).1 (hstd.wt_mem b)
  have hd : (w : G)⁻¹ * x ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hα : α ⟨l, hl⟩ = MulAut.conj w ⟨l, hl⟩ := by rw [hb]
    have h1 : x * l * x⁻¹ = (w : G) * l * (w : G)⁻¹ := congrArg Subtype.val hα
    calc l * ((w : G)⁻¹ * x) = (w : G)⁻¹ * ((w : G) * l * (w : G)⁻¹) * x := by group
      _ = (w : G)⁻¹ * (x * l * x⁻¹) * x := by rw [h1]
      _ = (w : G)⁻¹ * x * l := by group
  have hcomm : (w : G) * ((w : G)⁻¹ * x) = ((w : G)⁻¹ * x) * (w : G) :=
    Subgroup.mem_centralizer_iff.1 hd (w : G) w.2
  exact ⟨(w : G)⁻¹ * x, hd, (w : G), hwP₁, by rw [← hcomm]; group⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
