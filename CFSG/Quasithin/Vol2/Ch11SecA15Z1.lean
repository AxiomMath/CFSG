module

public import CFSG.Quasithin.Vol2.Ch11SecA15Block
public import CFSG.Quasithin.Vol2.Ch11SecA15Coc2
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch11SecA15Kill
public import CFSG.Quasithin.Vol2.Ch11SecA15Kind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

variable {G : Type} [Group G]

theorem blockZ_comm {L : Subgroup G} (hS : IsShort2 L) :
    ∀ a ∈ blockZ L, ∀ a' ∈ blockZ L, a * a' = a' * a := by
  intro a ha a' ha'
  have hQ : blockU L ≤ pCoreOf 2 L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  exact Subgroup.mem_centralizer_iff.mp (hS.2.2.1.1 ha'.1).2 a (hQ ha.1)

theorem blockZ_commute_L {L : Subgroup G} : ∀ l ∈ L, ∀ a ∈ blockZ L, l * a = a * l :=
  fun l hl _ ha => Subgroup.mem_centralizer_iff.mp ha.2 l hl

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem commute_of_mem_centerOf_ROf (h : Hyp11 G T L I n) {z : G}
    (hz : z ∈ centerOf (ROf T L V₁)) {k : G} (hk : k ∈ pCoreOf 2 L) : k * z = z * k :=
  Subgroup.mem_centralizer_iff.mp hz.2 k (pCoreOf_le_ROf h hk)

omit [Finite G] in
theorem mem_pCoreOf_of_mem_pCore {k : ↥L} (hk : k ∈ CFSG.pCore 2 ↥L) : (k : G) ∈ pCoreOf 2 L :=
  (CFSG.mem_openPCoreOf_iff k).mpr hk

theorem exists_blockU_of_sl3Block (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hB : IsSL3Block L) {z : G} (hz : z ∈ centerOf (ROf T L V₁)) :
    ∃ u₀ ∈ blockU L, u₀⁻¹ * z ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hS, m, F, _, _, hF, α, hα, hker, β, hβs, hβker, hβ⟩ := hB
  have hm := (kindSL3_of_modO2Surj hG2 h1102 h hF ⟨hα, hker⟩).2
  have hn : 2 ≤ n := h.one_lt
  have hz0 := centerOf_ROf_le_pCoreOf_msG0 h hz
  let e : Multiplicative (Fin 3 → F) ≃* Multiplicative (Fin 1 → Fin 3 → F) :=
    (AddEquiv.funUnique (Fin 1) (Fin 3 → F)).symm.toMultiplicative
  have he : ∀ (x : Multiplicative (Fin 3 → F)) (i : Fin 1),
      Multiplicative.toAdd (e x) i = Multiplicative.toAdd x := fun _ _ => rfl
  obtain ⟨u₀, hu₀, hw⟩ := exists_commutator_mem_ker_of_cocycle hF (by omega) α hα
    (e.toMonoidHom.comp β) (e.surjective.comp hβs)
    (fun l u v huv i => by
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, he]
      exact hβ l u v huv)
    (L_le_normalizer_blockU L) (commutator_mem_blockU h hz0)
    (fun l hl => commute_of_mem_centerOf_ROf h hz
      (mem_pCoreOf_of_mem_pCore (hker ▸ (MonoidHom.mem_ker.mpr hl))))
  refine ⟨u₀, hu₀, mem_centralizer_of_perfect h.fsu.faithful.1.2.1.2.1 (blockZ_comm hS)
    blockZ_commute_L fun l hl => ?_⟩
  obtain ⟨w, hw1, hweq⟩ := hw l hl
  rw [← hweq]
  have h1 : β w = 1 := e.injective (by simpa using hw1)
  have h2 : w ∈ β.ker := h1
  rw [hβker, Subgroup.mem_subgroupOf] at h2
  exact h2

end CFSG.Quasithin.Vol2.Ch11.SecA
