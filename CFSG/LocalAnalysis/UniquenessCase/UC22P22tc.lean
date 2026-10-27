module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tcU
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASLift
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASEF
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenGen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC
open CFSG.Quasithin (IsSylowIn conjSubgroup twoResidual)
open CFSG.Quasithin.E3 (wClos cClos sParam)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Thm111)
open CFSG.LocalAnalysis.WeakClosure81 (InFSqAS HasUniqueMaxOver)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22tc_exists_isE_not_le {V H T M₀ : Subgroup G} {i j : ℕ} (hV : IsElemAbelian 2 V)
    (hT : IsSylowIn 2 T H) (hF : InFSqAS j H) (hTM : T ≤ M₀) (hHM : ¬ H ≤ M₀)
    (hA : ∃ A ∈ CFSG.Quasithin.E3.gammaSet V i T, ¬ A ≤ pCoreOf 2 H) :
    ∃ A ∈ CFSG.Quasithin.E3.gammaSet V i T,
      ∃ K : Subgroup G, CFSG.Quasithin.E1.IsE j H T A K ∧ ¬ K ≤ M₀ := by
  classical
  let Ω : Set (Subgroup G) :=
    {A | A ≤ H ∧ ∃ g : G, A ≤ conjSubgroup V g ∧
      CFSG.Quasithin.E3.mQuot (conjSubgroup V g) A = i}
  have hΩ : CFSG.Quasithin.E1.IsInvColl H Ω := by
    refine ⟨fun A hA => hA.1, ?_, ?_⟩
    · rintro A ⟨-, g, hAg, -⟩
      exact CFSG.Open.IsElemAbelian.mono
        (CFSG.LocalAnalysis.WeakClosure81.isElemAbelian_conjSubgroup' hV g) hAg
    · rintro A ⟨hAH, g, hAg, hm⟩ h hh
      have hB : CFSG.Quasithin.A1b.conjSub h A = conjSubgroup A h⁻¹ := by
        ext x
        simp [CFSG.Quasithin.A1b.mem_conjSub_iff, CFSG.Quasithin.mem_conjSubgroup_iff]
      rw [hB]
      refine ⟨CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_le_of_le hAH (H.inv_mem hh),
        g * h⁻¹, ?_, ?_⟩
      · rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup V g h⁻¹]
        exact Subgroup.map_mono hAg
      · rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup V g h⁻¹,
          CFSG.Quasithin.E3.mQuot_conjSubgroup (conjSubgroup V g) A h⁻¹]
        exact hm
  obtain ⟨A₀, ⟨hA₀T, hA₀g⟩, hA₀O⟩ := hA
  obtain ⟨A, ⟨-, g, hAg, hm⟩, hAT, K, hK, hKM⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_isE_not_le_of_inFSqAS hT hF hTM hHM hΩ
      ⟨A₀, ⟨hA₀T.trans hT.le, hA₀g⟩, hA₀O⟩
  exact ⟨A, ⟨hAT, g, hAg, hm⟩, K, hK, hKM⟩

theorem uc22p22tc_dich {V H S : Subgroup G} (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H)
    {i j : ℕ} (hF : InFSqAS j H) (hij : i + j < sParam hV) :
    H ≤ normalizer (wClos V i S : Set G) ∨ ⁅cClos V (i + j) S, twoResidual H⁆ = ⊥ := by
  by_cases hHN : H ≤ normalizer (wClos V i S : Set G)
  · exact Or.inl hHN
  right
  set J := H ⊓ centralizer (cClos V (i + j) S : Set G) with hJ
  have hSJ : S ≤ normalizer (J : Set G) :=
    CFSG.Quasithin.A1a.le_normalizer_inf (hS.le.trans Subgroup.le_normalizer)
      (CFSG.Quasithin.A1a.le_normalizer_centralizer
        (Subgroup.le_normalizer.trans
          (CFSG.Quasithin.E3.normalizer_le_normalizer_cClos (V := V) (i := i + j) S)))
  suffices hres : twoResidual H ≤ J by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hres.trans inf_le_right)
  by_cases hHM : H ≤ J ⊔ S
  · exact CFSG.Quasithin.RonanE111.twoResidual_le_of_le_sup_two hSJ hS.isPGroup hHM
  · exfalso
    obtain ⟨A, hA, K, hK, hKM⟩ := uc22p22tc_exists_isE_not_le hV hS hF le_sup_right hHM
      (PartTwo.TwelveEighteen.exists_gammaSet_not_le_pCoreOf hS hHN)
    have hcomm := CFSG.Quasithin.E3.e3_19_comm hV hS hij hA hK
    apply hKM
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    rw [← CFSG.Quasithin.sup_twoResidual_eq hSK]
    refine sup_le (inf_le_left.trans le_sup_right) (le_sup_of_le_left (le_inf ?_ ?_))
    · exact (CFSG.Quasithin.twoResidual_le K).trans hK.1
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

@[expose] def F229AS (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, InFSqAS c.n (c.L0 ⊔ D.T)

@[expose] def InE229 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch,
    CFSG.Quasithin.E1.InE c.n (⊤ : Subgroup (Bar2 (c.L0 ⊔ D.T)))

theorem uc22p22tc_exists_hasUniqueMaxOver_bar {H T N : Subgroup G} (hT : IsSylowIn 2 T H)
    (hNH : N < H) (hTN : T ≤ N) (hmax : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ N) :
    ∃ T' : Subgroup (Bar2 H), CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ ∧ HasUniqueMaxOver T' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup ↥H := CFSG.pCore 2 ↥H with hY
  set π : ↥H →* ↥H ⧸ Y := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  have hT'syl : IsSylowIn 2 T' ⊤ := by
    have := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff hT.le le_rfl).mpr hT
    rwa [Subgroup.subgroupOf_self] at this
  have hYT : Y ≤ T' := by
    intro y hy
    have : (y : G) ∈ pCoreOf 2 H := ⟨y, hy, rfl⟩
    exact CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn hT this
  have hTt : IsSylowIn 2 (T'.map π) ⊤ :=
    CFSG.Quasithin.E1.isSylowIn_two_map_top hπs hT'syl
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  have hT'N' : T' ≤ N' := fun x hx => hTN hx
  have hYN' : Y ≤ N' := hYT.trans hT'N'
  refine ⟨T'.map π, CFSG.ABGLocalTools.isSylowOf_iff.mpr hTt, N'.map π, ?_, ?_⟩
  · rw [lt_top_iff_ne_top]
    intro htop
    have h2 : (N'.map π).comap π = N' ⊔ π.ker := Subgroup.comap_map_eq π N'
    rw [htop, Subgroup.comap_top, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hYN'] at h2
    have hHN : H ≤ N := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥H) ∈ N' := by rw [← h2]; exact Subgroup.mem_top _
      exact hx'
    exact absurd hHN (not_le_of_gt hNH)
  · intro X hTX hXtop
    set X₁ : Subgroup ↥H := X.comap π with hX₁
    have hTX₁ : T' ≤ X₁ := Subgroup.map_le_iff_le_comap.mp hTX
    have hX₁top : X₁ < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply ne_of_lt hXtop
      have h3 : X.comap π = (⊤ : Subgroup (↥H ⧸ Y)).comap π := by rw [← hX₁, h, Subgroup.comap_top]
      exact Subgroup.comap_injective hπs h3
    set X₂ : Subgroup G := X₁.map H.subtype with hX₂
    have hTX₂ : T ≤ X₂ := fun t ht =>
      ⟨⟨t, hT.le ht⟩, hTX₁ (show (⟨t, hT.le ht⟩ : ↥H) ∈ T' from ht), rfl⟩
    have hX₂H : X₂ < H := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le X₁) fun h => ?_
      apply ne_of_lt hX₁top
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ X₂ := by rw [h]; exact x.2
      obtain ⟨x', hx', hxx'⟩ := hx
      have h4 : x' = x := Subtype.ext hxx'
      rw [← h4]
      exact hx'
    have hX₂N : X₂ ≤ N := hmax X₂ hTX₂ hX₂H
    have hX₁N' : X₁ ≤ N' := fun x hx => hX₂N ⟨x, hx, rfl⟩
    calc X = X₁.map π := (Subgroup.map_comap_eq_self_of_surjective hπs X).symm
      _ ≤ N'.map π := Subgroup.map_mono hX₁N'

theorem f229AS_of_uniqueMax (D : Data G) (Ch : Choice2011 G) (hU : UniqueMaxL0T D Ch)
    (hE : InE229 D Ch) : F229AS D Ch := by
  intro h1930 c
  obtain ⟨N, hTN, hNH, hmax⟩ := hU h1930 c
  exact CFSG.LocalAnalysis.WeakClosure81.inFAS_top_of_inE c.n (hE h1930 c)
    (uc22p22tc_exists_hasUniqueMaxOver_bar (uc22p22ta_isSylowIn D le_sup_right) hNH hTN hmax)
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
