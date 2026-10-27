module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagGraphRest
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wi
import CFSG.LocalAnalysis.UniquenessCase.UCKP3Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticTwo
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (exceptionalAut exceptionalAut_structure)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_mk rhoL_mk_coe)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_typeKernel_of_classPres {θ : MulAut (StatedProj (StatedSp 2 K))}
    (hθ : uc22pdiag_ClassPres (StatedProj (StatedSp 2 K)) θ) : θ ∈ typeKernel K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₀, hV₀⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hB : normalizer ((V₀ : Subgroup (StatedProj (StatedSp 2 K))) : Set (StatedProj (StatedSp 2 K))) =
      projBorel 2 K := by
    rw [hV₀]
    exact normalizer_projUnipotent 2 (by norm_num)
  have hN : normalizer ((V₀ : Subgroup (StatedProj (StatedSp 2 K))) : Set (StatedProj (StatedSp 2 K))) ≤
      projStabilizer 2 K (flag 2 K 1) := by
    rw [hB]
    exact Subgroup.map_mono (borelSubgroup_le_stabilizer_flag (by norm_num))
  obtain ⟨g, hg⟩ := hθ V₀ (projStabilizer 2 K (flag 2 K 1))
    (isCoatom_projStabilizer_flag (by norm_num) (by norm_num)) hN
  have hX : projStabilizer 2 K (flag 2 K 1) ∈ pointParabolics K :=
    ⟨flag 2 K 1, finrank_flag (by norm_num), rfl⟩
  obtain ⟨hall, -, -, hinn⟩ := type_kernel (K := K) 2
  have hgX : (projStabilizer 2 K (flag 2 K 1)).map (MulAut.conj g).toMonoidHom ∈ pointParabolics K := by
    have h1 := mem_typeKernel.1 (hinn ⟨g, rfl⟩)
    rw [← h1]
    exact ⟨_, hX, rfl⟩
  obtain ⟨-, -, hdisj, -⟩ := extremal_parabolics (K := K) 2 rfl
  obtain ⟨-, -, hpres | ⟨hXY, -⟩⟩ := hall θ
  · exact mem_typeKernel.2 hpres.1
  · have h2 : (projStabilizer 2 K (flag 2 K 1)).map θ.toMonoidHom ∈ planeParabolics K := by
      rw [← hXY]
      exact ⟨_, hX, rfl⟩
    rw [hg] at h2
    exact absurd h2 (Set.disjoint_left.1 hdisj hgX)

theorem mem_range_conj_of_mem_typeKernel {n : ℕ} (hn : Odd n) (hK : Nat.card K = 2 ^ n)
    {θ : MulAut (StatedProj (StatedSp 2 K))} (hθ : θ ∈ typeKernel K) {a : ℕ} (ha : θ ^ 2 ^ a = 1) :
    θ ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data hn.pos hK
  obtain ⟨hγ, -, -, -, -, -, hE, -⟩ := exceptionalAut_structure hn.pos hFr hord hzp
  rw [(kernel_generation (K := K)).1, hE, ← SetLike.mem_coe, Subgroup.normal_mul] at hθ
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hθ
  have hy' : y ∈ inner (StatedProj (StatedSp 2 K)) := hy
  have hz' : z ∈ Subgroup.zpowers (exceptionalAut K ^ 2) := hz
  have hγn : (exceptionalAut K ^ 2) ^ n = 1 := by rw [← pow_mul, ← hγ, pow_orderOf_eq_one]
  have hzn : z ^ n = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers hz').trans (orderOf_dvd_of_pow_eq_one hγn))
  have h1 : (QuotientGroup.mk (y * z) : MulAut (StatedProj (StatedSp 2 K)) ⧸
      inner (StatedProj (StatedSp 2 K))) ^ n = 1 := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy', one_mul, ← QuotientGroup.mk_pow, hzn,
      QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk (y * z) : MulAut (StatedProj (StatedSp 2 K)) ⧸
      inner (StatedProj (StatedSp 2 K))) ^ 2 ^ a = 1 := by
    rw [← QuotientGroup.mk_pow, ha, QuotientGroup.mk_one]
  exact (QuotientGroup.eq_one_iff _).1
    ((pow_eq_one_iff_of_coprime (hn.coprime_two_right.pow_right a)).1 ⟨h1, h2⟩)

end Model

section Main

theorem not_isInnDiagFieldAut_of_not_inner_sp4 {S : Type} [Group S] {n : ℕ} (hS : IsSp4 S n) (hn : Odd n)
    {θ : MulAut S} {a : ℕ} (ha : θ ^ 2 ^ a = 1) (hθ : θ ∉ (MulAut.conj : S →* MulAut S).range) :
    ¬ CFSG.ASVolI.ChA.IsInnDiagFieldAut S θ := by
  intro h
  obtain ⟨⟨-, -, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  have hn3 : 2 < n := by
    obtain ⟨k, rfl⟩ := hn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd (by norm_num) hne
    · omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Finite (StatedProj (StatedSp 2 K)) := CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp 2 K
  haveI : Finite S := Finite.of_equiv _ e.symm.toEquiv
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num) (Or.inl (Or.inr h4))
  haveI : IsSimpleGroup S := e.isSimpleGroup
  have hcp : uc22pdiag_ClassPres S θ :=
    uc22pdiag_classPres_of_innDiagField (fun V => (uc22pdiag_twoClasses_Sp4 hS V).twoCoatoms)
      (uc22pdiag_dvd_Sp4 hS hn3) h
  have hcp' : uc22pdiag_ClassPres (StatedProj (StatedSp 2 K)) (MulAut.congr e θ) :=
    uc22pdiag_ClassPres_of_congr e.symm _ (by rwa [P22w.congr_symm_congr])
  have ha' : MulAut.congr e θ ^ 2 ^ a = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨y, hy⟩ := mem_range_conj_of_mem_typeKernel hn hK (mem_typeKernel_of_classPres hcp') ha'
  refine hθ ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [P22w.congr_conj, MulEquiv.apply_symm_apply, hy]

theorem exists_quot_not_isInnDiagFieldAut_sp4 {X : Type} [Group X] {n : ℕ} (hX : IsSp4 X n) (hn : Odd n)
    {α : MulAut X} {a : ℕ} (ha : α ^ 2 ^ a = 1) (hα : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ θ : MulAut (X ⧸ center X), (∀ x : X, θ (QuotientGroup.mk x) = QuotientGroup.mk (α x)) ∧
      ¬ CFSG.ASVolI.ChA.IsInnDiagFieldAut (X ⧸ center X) θ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨e₀, he₀⟩ :=
    UCK.exists_mulEquiv_of_center_eq_bot (CFSG.QuasithinUnique.Lin2.Five.center_eq_bot_of_equiv e)
  refine ⟨MulAut.congr e₀ α, fun x => ?_, ?_⟩
  · rw [← he₀, ← he₀]
    simp
  · rw [uc22p22wi_isInnDiagFieldAut_congr]
    exact not_isInnDiagFieldAut_of_not_inner_sp4 hX hn ha hα

theorem actsNontrivOnDiagram_of_not_inner_sp4 {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
    (hX : IsSp4 (Bar2 L) n) (hn : Odd n) {t : G} (htN : t ∈ normalizer (L : Set G)) {a : ℕ}
    (ht : t ^ 2 ^ a = 1) (hout : rhoL L ⟨t, htN⟩ ∉ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range) :
    ActsNontrivOnDiagram L t := by
  have ha : rhoL L ⟨t, htN⟩ ^ 2 ^ a = 1 := by
    have h1 : (⟨t, htN⟩ : ↥(normalizer (L : Set G))) ^ 2 ^ a = 1 := Subtype.ext (by simpa using ht)
    rw [← map_pow, h1, map_one]
  obtain ⟨θ, hθ, hnot⟩ := exists_quot_not_isInnDiagFieldAut_sp4 hX hn ha hout
  have hind : InducedQuot L t θ := by
    intro l l' hl
    have hl' : Subgroup.normalizerMonoidHom L ⟨t, htN⟩ l = l' :=
      Subtype.ext ((rhoL_mk_coe L ⟨t, htN⟩ l).trans hl.symm)
    rw [hθ, rhoL_mk, hl']
  exact ⟨htN, θ, hind, hnot⟩

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
