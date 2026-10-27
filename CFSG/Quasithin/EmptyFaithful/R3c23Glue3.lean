module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
public import CFSG.Quasithin.EmptyFaithful.S151S4F

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_centralizer_of_isTwoReducedIn {H V : Subgroup G} (hV : IsTwoReducedIn H V) :
    pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) := by
  refine hV.2.2.2 (pCoreOf 2 H) (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) ?_
  intro d hd
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [this]
  exact Subgroup.one_mem _

theorem inf_centralizer_eq_pCore {H L V : Subgroup G} (hV : IsTwoReducedIn H V)
    (hLH : L ∈ cComp H) {n : ℕ} (hLn : IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L))
    (hquasi : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLnV : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    (Subgroup.centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L := by
  have hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    (S151S4.pCoreOf_le_of_isSubnormal (subnormal_of_mem_cComp hLH)).trans
      (pCoreOf_le_centralizer_of_isTwoReducedIn hV)
  have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    S151S4.center_eq_bot_of_isPSL2 hLn
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hpcK : ∀ x : ↥L, π x = 1 → (x : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have h1 : x ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff x).mp hx
    exact hO2L ⟨x, by assumption, rfl⟩
  have hker : π.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
    apply le_antisymm
    · intro x hx
      exact hpcK x hx
    · intro x hx
      have hKnorm : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer ((le_of_mem_cComp hLH).trans (hV.2.1.trans
          (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V)))
      have hmn : (((Subgroup.centralizer (V : Set G)).subgroupOf L).map π).Normal :=
        hKnorm.map π hπs
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hquasi hmn with h | h
      · exfalso
        apply hLnV
        intro l hl
        have hmem : π ⟨l, hl⟩ ∈ ((Subgroup.centralizer (V : Set G)).subgroupOf L).map π :=
          h ▸ Subgroup.mem_top _
        obtain ⟨y, hy, hyl⟩ := hmem
        have h1 : π (y⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hyl, inv_mul_cancel]
        have h2 := hpcK _ h1
        have hyC : (y : G) ∈ Subgroup.centralizer (V : Set G) := Subgroup.mem_subgroupOf.mp hy
        have hl' : l = (y : G) * ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
        rw [hl']
        exact (Subgroup.centralizer (V : Set G)).mul_mem hyC h2
      · rw [hcenter] at h
        have hx' : π x ∈ ((Subgroup.centralizer (V : Set G)).subgroupOf L).map π := ⟨x, hx, rfl⟩
        exact Subgroup.mem_bot.mp (h hx')
  rw [← hker, hπ, QuotientGroup.ker_mk']


theorem lin2Cover_autI {H L V : Subgroup G} (hVe : IsElemAbelian 2 V) (hV : IsTwoReducedIn H V)
    (hLH : L ∈ cComp H) {n : ℕ} (hn : 1 < n) (hLn : IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L))
    (hquasi : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLnV : ¬ L ≤ Subgroup.centralizer (V : Set G)) : Lin2Cover ↥(autI hVe L) := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hLH).trans hV.2.1
  let φ : ↥L →* MulAut (IntMod V hVe) := (convI hVe).comp (Subgroup.inclusion hLN)
  have hrange : φ.range = autI hVe L := by
    ext ψ
    rw [MonoidHom.mem_range, mem_autI]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLN x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 ↥L := by
    rw [← inf_centralizer_eq_pCore hV hLH hLn hquasi hLnV]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact convI_eq_one_iff hVe (Subgroup.inclusion hLN x)
  obtain ⟨F, hF, hFin, -, hcard, ⟨e₂⟩⟩ := S151S4.exists_equiv_sl2 hLn
  let e₁ : ↥(autI hVe L) ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
    ((MulEquiv.subgroupCongr hrange.symm).trans (QuotientGroup.quotientKerEquivRange φ).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  exact ⟨F, hF, hFin, n, hn, hcard,
    ⟨e₁.trans (e₂.trans (specialLinearGroupEquivStatedSL 2 F))⟩⟩

omit [Finite G] in
theorem not_thompsonJ_le_centralizer {H T L V : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hLH : L ≤ H) (hJ : ⁅L, thompsonJ T⁆ = L)
    (hLnV : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
  intro hJC
  apply hLnV
  rw [← hJ]
  refine Subgroup.commutator_le.2 fun l hl j hj => ?_
  have hlN : l ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V (hHN (hLH hl))
  have h1 : l * j * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp hlN j).mp (hJC hj)
    exact this
  have h2 : ⁅l, j⁆ = (l * j * l⁻¹) * j⁻¹ := commutatorElement_def l j
  rw [h2]
  exact mul_mem h1 (inv_mem (hJC hj))

theorem isFFModule_autI {H T V : Subgroup G} (hVe : IsElemAbelian 2 V) (hVH : V ≤ H)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : IsFFModule (autI hVe H) := by
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h)
  exact (B2_7_of_not_le hVe hVH hHN hJH).1

end R3c23

end CFSG.Quasithin
