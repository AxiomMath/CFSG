module

public import CFSG.Quasithin.Background.RonanE114QPair
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Cov
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Core

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

theorem exists_quot_subgroupOf {M : Type} [Group M] [Finite M] {Γ P V : Subgroup M}
    (hPΓ : P ≤ Γ) (hV : IsPGroup 2 V) {Y Y' : Type} [Group Y] [Group Y'] (eY : Y ≃* Y')
    (g : ↥(perfectCore P) →* Y) (hs : Function.Surjective g)
    (hk : ∀ x, g x = 1 → (x : M) ∈ V) :
    ∃ φ : ↥(perfectCore (P.subgroupOf Γ)) →* Y', Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  have hfin : Finite ↥Γ := Finite.of_injective _ Γ.subtype_injective
  have h : (perfectCore (P.subgroupOf Γ)).map Γ.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPΓ]
  let eP : ↥(perfectCore (P.subgroupOf Γ)) ≃* ↥(perfectCore P) :=
    ((perfectCore (P.subgroupOf Γ)).equivMapOfInjective Γ.subtype Γ.subtype_injective).trans
      (MulEquiv.subgroupCongr h)
  set ψ : ↥(perfectCore P) →* Y' := eY.toMonoidHom.comp g with hψ
  have hψs : Function.Surjective ψ := eY.surjective.comp hs
  have hψk : IsPGroup 2 ψ.ker := by
    intro x
    have hx : g x.1 = 1 := by
      have h2 : ψ x.1 = 1 := x.2
      exact (map_eq_one_iff eY eY.injective).mp h2
    obtain ⟨k, hk'⟩ := hV ⟨((x.1 : ↥(perfectCore P)) : M), hk _ hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : ((x.1 : ↥(perfectCore P)) : M) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk'
    simpa using h1
  exact ⟨ψ.comp eP.toMonoidHom, hψs.comp eP.surjective, isPGroup_ker_comp ψ eP hψk⟩

section Ree

open CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem hasQuotPair_2F4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    HasQuotPair ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) (2 * a + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ‹CharP K F4.prime›
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨-, hcov, hn₀, hn₁, hgen, hi₀, hi₁⟩ := F4.largeRee_named_covers a K hK
  have hne : Nat.card K + 1 ≠ Nat.card K ^ 2 + 1 := by
    intro h
    have h1 : Nat.card K = Nat.card K ^ 2 := Nat.add_right_cancel h
    nlinarith
  have hinv := D4.invariant_of_unequal_covers hcov (by rw [hi₀, hi₁]; exact hne)
  have hcases : ∀ j : Fin F4.fixedOrbitCount, j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
    decide
  have hPΓ : ∀ j, F4.reeLocalParabolic K a j ≤ F4.reeGamma K a := fun j => inf_le_left
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hs₀ := isSimpleGroup_rankOneGroupOne ha hK
  have hs₁ := isSimpleGroup_rankOneGroupTwo ha hK
  haveI := hs₀.1
  haveI := hs₁.1
  obtain ⟨⟨g₀, hg₀, hk₀⟩, hM₀⟩ := F4.levi_hom ha hK ⟨0, by decide⟩
    (M := rankOneGroupOne K a) h0eq hs₀.2
  obtain ⟨⟨g₁, hg₁, hk₁⟩, hM₁⟩ := F4.levi_hom ha hK ⟨1, by decide⟩
    (M := rankOneGroupTwo K a) h1eq hs₁.2
  refine ⟨Fin F4.fixedOrbitCount,
    fun j => (F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a), ?_, ?_, ?_⟩
  · intro α hα j
    rcases hcases j with rfl | rfl
    · exact (hinv α hα).1
    · exact (hinv α hα).2
  ·
    suffices h : (⨆ j, perfectCore ((F4.reeLocalParabolic K a j).subgroupOf
        (F4.reeGamma K a))) = ⊤ by rw [h, top_sup_eq]
    rw [eq_top_iff, ← Subgroup.map_le_map_iff_of_injective (F4.reeGamma K a).subtype_injective,
      Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_iSup]
    have h2 : ∀ j, (perfectCore ((F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a))).map
        (F4.reeGamma K a).subtype = perfectCore (F4.reeLocalParabolic K a j) := fun j => by
      rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le (hPΓ j)]
    simp only [h2]
    rw [large_Ree_simple_pair_generation a K hK, h0eq, h1eq]
    exact sup_le (le_iSup_of_le ⟨0, by decide⟩ hM₀) (le_iSup_of_le ⟨1, by decide⟩ hM₁)
  · intro j
    rcases hcases j with rfl | rfl
    · obtain ⟨φ, hφs, hφk⟩ := exists_quot_subgroupOf (hPΓ ⟨0, by decide⟩)
        (F4.isPGroup_rad ha hK ⟨0, by decide⟩) (rankOneEquivSL K a hK).symm g₀ hg₀ hk₀
      exact ⟨_, inferInstance, φ, Rk1.sl2 hK hK4, hφs, hφk⟩
    · obtain ⟨φ, hφs, hφk⟩ := exists_quot_subgroupOf (hPΓ ⟨1, by decide⟩)
        (F4.isPGroup_rad ha hK ⟨1, by decide⟩) (rankOneEquivSuzuki K a ha hK) g₁ hg₁ hk₁
      exact ⟨_, inferInstance, φ, Rk1.suzuki ha hK, hφs, hφk⟩

end Ree

section Main

open CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {G : Type} [Group G] [Finite G]

theorem inEFor_of_is2F4 {L T : Subgroup G} (hLn : L.Normal) (hT : IsSylowIn 2 T ⊤)
    (hLT : L ⊔ T = ⊤) {n : ℕ} (h2F4 : CFSG.Quasithin.Is2F4 n ↥L) : E1.InEFor n ⊤ T := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model h2F4
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have := hasQuotPair_2F4 ha hK'
  rw [hfa]
  exact inEFor_of_hasQuotPair hLn hT hLT e (F4.largeRee_named_covers a K hK').1
    (hasQuotPair_2F4 ha hK')

theorem nParam_le_of_is2F4 {T : Subgroup G} {n : ℕ} (hLn : (CFSG.generalizedFitting G).Normal)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (h2F4 : CFSG.Quasithin.Is2F4 n ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK, -⟩ := exists_mulEquiv_largeRee_model h2F4
  exact (E1.nParam_le_iff (by omega)).mpr
    ((E1.inE_iff_inEFor hT).mpr (inEFor_of_is2F4 hLn hT hFT h2F4))

end Main

end CFSG.Quasithin.RonanE114
