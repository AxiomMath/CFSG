module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNKer
public import CFSG.GroupTheory.PGL2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

theorem starOfSylThree_holds : StarOfSylThreeStmt := by
  intro G _ _ V N hP g hg hVg x hx hord
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨S, hS, hxS⟩ := exists_isSylowIn_ge 3
    ((zpowers_le (G := G) (H := N)).mpr (mem_inf.mp hx).1) hzp
  obtain ⟨p, -, -, -, -, -, hcap⟩ := hP S hS
  have hmem : x ∈ S ⊓ conjSubgroup (normalizer (V : Set G)) g := by
    refine mem_inf.mpr ⟨hxS (mem_zpowers x), ?_⟩
    rw [CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_normalizer]
    exact (mem_inf.mp hx).2
  rw [hcap g hg hVg, mem_bot] at hmem
  rw [hmem, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem nfReduction7_holds : NFAbstract → NFPGL27 → ∀ (G : Type) [Group G] [Finite G], W3Lem914N7 G := by
  intro hW hF G _ _ V T N L hyp hTN hNM hN hL hTL hψ hφ hstar
  obtain ⟨Z, _, ψ, hψs, hψk, hcomp⟩ := hψ
  obtain ⟨A, _, φ, hφs, hφk, hA⟩ := hφ
  have hLN : L ≤ N := by rw [hN]; exact le_sup_right
  have hNL : N ≤ normalizer (L : Set G) := by rw [hN]; exact sup_le hTL Subgroup.le_normalizer
  have hLn : (L.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  have hNinf : N ≤ N ⊓ normalizer (L : Set G) := le_inf le_rfl hNL
  let π : ↥N →* A := φ.comp (Subgroup.inclusion hNinf)
  have : Finite A := Finite.of_surjective φ hφs
  have hπs : Function.Surjective π := by
    intro a
    obtain ⟨y, rfl⟩ := hφs a
    exact ⟨⟨y, (mem_inf.mp y.2).1⟩, rfl⟩
  have hπk : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L) :=
    fun x => hφk (Subgroup.inclusion hNinf x)
  have hT2 : IsPGroup 2 T := hyp.sylow.isPGroup
  have hker : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N := fun x =>
    (hπk x).trans (NF914.mem_centSection_iff_mem_pCoreOf hLN hNL hTN hT2 hN.symm ψ hψs hψk
      hcomp.1 π hπs hπk (dvd_of_eq (CFSG.GroupTheory.card_of_isPGL2_seven hA)) x)
  refine hW G V T N L hyp hTN hNM hLN hLn hstar A π hπs hker ?_
  refine hF A hA ((L.subgroupOf N).map π) ((T.subgroupOf N).map π) (hLn.map π hπs) ?_ ?_ ?_
  ·
    intro hbot
    have := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
    have hψL : (L.subgroupOf N).map ψ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨l, hl, rfl⟩
      have h1 : π l ∈ (L.subgroupOf N).map π := mem_map_of_mem π hl
      rw [hbot, mem_bot] at h1
      exact (hψk l).mpr ((hker l).mp h1)
    exact (nontrivial_iff_ne_bot _).mp inferInstance hψL
  ·
    have hLperf : ⁅L, L⁆ = L := by
      have h := CFSG.Quasithin.perfectCore_perfect (L ⊔ pCoreOf 2 N)
      rw [← hL] at h
      exact h
    have hL'perf : ⁅L.subgroupOf N, L.subgroupOf N⁆ = L.subgroupOf N := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLN, hLperf]
    rw [← Subgroup.map_commutator, hL'perf]
  ·
    have hT2' : IsPGroup 2 (T.subgroupOf N) := hT2.of_equiv (subgroupOfEquivOfLe hTN).symm
    refine ⟨le_top, hT2'.map π, fun hd => hyp.sylow.not_dvd_relIndex ?_⟩
    rw [Subgroup.relIndex_top_right] at hd
    have h1 : 2 ∣ T.relIndex N := hd.trans (Subgroup.index_map_dvd _ hπs)
    rw [← Subgroup.relIndex_mul_relIndex T N (normalizer (V : Set G)) hTN hNM]
    exact h1.mul_right _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
