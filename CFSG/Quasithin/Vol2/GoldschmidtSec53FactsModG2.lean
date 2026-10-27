module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Ctr
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamPkg
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParG2
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data

public section

namespace CFSG.Quasithin.H13.Sec53F.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.Rk2
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.Sec53F
open scoped Pointwise

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem trans_center {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (i : Fin Tag.G2.rank)
    {a a' : ↥(adjointGroup Tag.G2 K)}
    (ha : a ∈ centerOf (perfectCore
      ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K))))
    (ha' : a' ∈ centerOf (perfectCore
      ((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K))))
    (h1 : a ≠ 1) (h1' : a' ≠ 1) :
    ∃ m ∈ (parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K),
      m * a * m⁻¹ = a' := by
  have hPC : parabolicSubgroup Tag.G2 K {i} ≤ adjointGroup Tag.G2 K :=
    parabolicSubgroup_le_adjointGroup _ _ _
  obtain ⟨hx, hxc⟩ := (mem_centerOf_perfectCore_subgroupOf hPC a).mp ha
  obtain ⟨hx', hxc'⟩ := (mem_centerOf_perfectCore_subgroupOf hPC a').mp ha'
  rcases fin_two_cases i with rfl | rfl
  · exact absurd (Subtype.ext (center_zero hK hf hx hxc)) h1
  · obtain ⟨t, ht⟩ := center_one hK hf hx hxc
    obtain ⟨t', ht'⟩ := center_one hK hf hx' hxc'
    have ht0 : t ≠ 0 := fun h0 => h1 (Subtype.ext (by rw [ht, h0, gX_zero]; rfl))
    have ht0' : t' ≠ 0 := fun h0 => h1' (Subtype.ext (by rw [ht', h0, gX_zero]; rfl))
    obtain ⟨τ, hτ⟩ := exists_torus_conj ht0 ht0'
    refine ⟨⟨torusElt Tag.G2 K i0 τ, torusElt_mem_adjointGroup i0 τ⟩, ?_, Subtype.ext ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (borelGroup_le_parabolicSubgroup _
        (torusGroup_le_borelGroup (torusElt_mem_torusGroup i0 τ)))
    · show torusElt Tag.G2 K i0 τ * (a : ModGL Tag.G2 K) * (torusElt Tag.G2 K i0 τ)⁻¹ = a'
      rw [ht, ht', hτ]

theorem posUnipotent_le_perfectCore_idx {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (i : Fin Tag.G2.rank) :
    posUnipotent Tag.G2 K ≤ perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
  rcases fin_two_cases i with rfl | rfl
  · exact posUnipotent_le_perfectCore_zero (four_le_card_of hK hf)
  · exact posUnipotent_le_perfectCore_one (four_le_card_of hK hf)

theorem g2_noNormal {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ∀ R : Subgroup ↥(adjointGroup Tag.G2 K), R.Normal → IsPGroup 2 ↥R → R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  intro R hR h2
  have h4 := four_le_card_of hK hf
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K (by omega)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq R with h | h
  · rw [center_adjointGroup_eq_bot] at h
    exact le_bot_iff.mp h
  · exfalso
    subst h
    apply (rank2Pkg_g2 hK hf).not_isSolvable_perfectCore 0
    have hp : IsPGroup 2 ↥(perfectCore
        ((parabolicSubgroup Tag.G2 K {g2Index 0}).subgroupOf (adjointGroup Tag.G2 K))) :=
      IsPGroup.to_le h2 le_top
    have := hp.isNilpotent
    infer_instance

theorem g2_yamStd {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    Yam.YamStd ↥(adjointGroup Tag.G2 K) (posUnipotentSub Tag.G2 K)
      ((parabolicSubgroup Tag.G2 K {g2Index 0}).subgroupOf (adjointGroup Tag.G2 K))
      ((parabolicSubgroup Tag.G2 K {g2Index 1}).subgroupOf (adjointGroup Tag.G2 K)) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  exact (rank2Pkg_g2 hK hf).yamStd g2_sylow (g2_noNormal hK hf)

theorem g2_lieFactsOf {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    Yam.LieFactsOf (posUnipotentSub Tag.G2 K)
      ((parabolicSubgroup Tag.G2 K {g2Index 0}).subgroupOf (adjointGroup Tag.G2 K))
      ((parabolicSubgroup Tag.G2 K {g2Index 1}).subgroupOf (adjointGroup Tag.G2 K)) := by
  have hPC : ∀ j, parabolicSubgroup Tag.G2 K {g2Index j} ≤ adjointGroup Tag.G2 K :=
    fun j => parabolicSubgroup_le_adjointGroup _ _ _
  obtain ⟨hcov, hinj, -⟩ := exceptional_ordinary_minimal_Borel_intersections Tag.G2 K
  have hne : parabolicSubgroup Tag.G2 K {g2Index 0} ≠ parabolicSubgroup Tag.G2 K {g2Index 1} :=
    fun h => absurd (g2Index_injective (hinj h)) (by decide)
  have hcov' : ∀ j, borelGroup Tag.G2 K ⋖ parabolicSubgroup Tag.G2 K {g2Index j} :=
    fun j => (hcov _ (hPC j)).2 ⟨_, rfl⟩
  have hB := inf_eq_of_covBy (hcov' 0) (hcov' 1) hne
  refine ⟨⟨(rank2Pkg_g2 hK hf).res.2.2.2.1, fun a ha a' ha' h1 h1' => ?_,
    fun a ha a' ha' h1 h1' => ?_⟩, fun c hc => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact trans_center hK hf _ ha ha' h1 h1'
  · exact trans_center hK hf _ ha ha' h1 h1'
  · have hcB : (c : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
      rw [← hB]
      exact ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hc).1,
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hc).2⟩
    rw [normalizer_subgroupOf_eq' posUnipotent_le_adjointGroup, Subgroup.mem_subgroupOf,
      (borel_self_normalizers Tag.G2 K).1]
    exact hcB
  · exact (mem_perfectCore_subgroupOf (hPC 0) x).mpr
      (posUnipotent_le_perfectCore_idx hK hf _ (Subgroup.mem_subgroupOf.mp hx))
  · exact (mem_perfectCore_subgroupOf (hPC 1) x).mpr
      (posUnipotent_le_perfectCore_idx hK hf _ (Subgroup.mem_subgroupOf.mp hx))

theorem lieModelFacts_g2 : LieModelFacts .G2 0 :=
  Yam.lieModelFacts_of_std fun Y _ f hpar hY => by
    obtain ⟨-, hX⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hY (by decide)
    obtain ⟨hf, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
    have : Finite (ModGL Tag.G2 K) := finite_modGL
    exact ⟨_, inferInstance, inferInstance, _, _, _, g2_yamStd hK hf, g2_lieFactsOf hK hf, ⟨e⟩⟩

end CFSG.Quasithin.H13.Sec53F.G2
