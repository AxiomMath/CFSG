module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGPresentation
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import CFSG.LocalAnalysis.StandardType.GGRankOneModel
import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
import CFSG.LocalAnalysis.StandardType.GGRankOneTags
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg

private theorem exists_sl2_range_rankOne {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective φ ∧
      φ.range = CFSG.LieType.CurtisTits.rankOne D.rootGroup i := by
  unfold GGRankOneModel at hM
  obtain ⟨x, C, O, hE, -⟩ := hM
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  refine ⟨φ, hφinj, ?_⟩
  apply le_antisymm
  · rintro y ⟨M, rfl⟩
    have hM' : M ∈ Subgroup.closure
        (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
          Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) := by
      rw [CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top]
      exact Subgroup.mem_top M
    have hs : (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
        Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ := by
      rintro x (hx | hx)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Upper c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφu c]
        exact Subgroup.mem_sup_left
          (((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Lower c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφl c]
        exact Subgroup.mem_sup_right
          (((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
    exact Subgroup.mem_comap.mp
      (Subgroup.mem_closure.mp hM'
        ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ) hs)
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ φ.range
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, by rw [hφu c, hc]⟩
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Lower c, by rw [hφl c, hc]⟩

theorem ggRankOneIn_isQuasisimple_of_kgPos
    (hKG : GGSecFiveKGPosInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    (hXs : GGSplitLie p X) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r) := by
  obtain ⟨t, n, f, ψ, hadm, h3, hker, -, htag, hpf, htb⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := htb
  have hW := ggTag_weylMatrix htag hadm
  have hpresε : GGCoxeterPres p (ggAutomizer X Bs)
      (coxeterMatrix (ggU t n f).D.isFiniteType) ε := ⟨hW.1, hεrefl⟩
  obtain ⟨w, i, hw⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top X Bs) hpresε hW.2 hrA hr
  have hlevi : ggRankOneIn X Bs ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) :
      ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = (ggRootLevi (ggU t n f).D (Pi.single i 1)).map ψ := by
    have h := hεlevi 1 i
    simp only [one_mul, inv_one, mul_one, map_one, Module.End.one_apply] at h
    exact h
  have hr' : ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
      ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
        MulAut ↥Bs) * ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)⁻¹ = r := by
    rw [hw, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨g, -, -, hg⟩ := exists_ggRankOneIn_conj_of_mem_ggAutomizer (ε w).2
    ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
      MulAut ↥Bs)
  rw [hr', hlevi] at hg
  obtain ⟨φ, hφinj, hφrange⟩ := exists_sl2_range_rankOne (ggRankOneModel_of_tag htag hadm h3) i
  have hθinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp (ψ.comp φ)) :=
    (MulAut.conj g).injective.comp (PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker)
  have hθrange : ((MulAut.conj g).toMonoidHom.comp (ψ.comp φ)).range = ggRankOneIn X Bs r := by
    rw [← hg, ← MonoidHom.map_range, ← MonoidHom.map_range ψ φ, hφrange]
    rfl
  have hf2 : 2 ≤ f := by
    have hf1 : 1 ≤ f := hadm.2.1
    by_contra hlt
    obtain rfl : f = 1 := by omega
    have hp1 : p ∣ 1 := by simpa using hpf
    exact (ggRouteCfg_prime hcfg).1.one_lt.ne' (Nat.dvd_one.mp hp1)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hSL : CFSG.Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4).commutator_eq_top,
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩
  rw [← hθrange]
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hθinj).symm hSL

end CFSG.StandardType

end
