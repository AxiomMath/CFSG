module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem conjSubgroup_inv_eq_conjSub (V : Subgroup G) (a : G) :
    conjSubgroup V a⁻¹ = conjSub a V := by
  unfold conjSubgroup conjSub
  rw [inv_inv]

theorem conjSub_conjClosure_of_mem {V H : Subgroup G} {h : G} (hh : h ∈ H) :
    conjSub h (conjClosure V H) = conjClosure V H :=
  F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V H hh)

theorem conjSub_pCoreOf_of_mem [Finite G] {H : Subgroup G} {h : G} (hh : h ∈ H) :
    conjSub h (pCoreOf 2 H) = pCoreOf 2 H :=
  F7.conjSub_eq_of_mem_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh)

theorem le_centralizer_conjSub_conjClosure {V H : Subgroup G} (g : G)
    (h : ∀ k ∈ H, V ≤ Subgroup.centralizer (conjSub (g * k) V : Set G)) :
    V ≤ Subgroup.centralizer (conjSub g (conjClosure V H) : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  rw [conjClosure, conjSub_closure, Subgroup.closure_le]
  rintro _ ⟨y, ⟨k, hk, z, hz, rfl⟩, rfl⟩
  have hmem : g * (k * z * k⁻¹) * g⁻¹ ∈ conjSub (g * k) V := by
    have := mul_mem_conjSub (g := g * k) hz
    simpa [mul_assoc] using this
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.mp (h k hk hv)) _ hmem).symm

theorem conjSub_le_wClos_zero {V X : Subgroup G} (a : G) (h : conjSub a V ≤ X) :
    conjSub a V ≤ E3.wClos V 0 X := by
  have hmem : conjSub a V ∈ E3.gammaSet V 0 X := by
    refine ⟨h, a⁻¹, ?_, ?_⟩
    · rw [conjSubgroup_inv_eq_conjSub]
    · rw [conjSubgroup_inv_eq_conjSub]
      exact E3.mQuot_self _
  exact le_iSup₂_of_le (conjSub a V) hmem le_rfl

end S152Fin

end CFSG.Quasithin
