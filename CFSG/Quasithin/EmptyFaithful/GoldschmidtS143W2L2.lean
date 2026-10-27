module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Gen
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFixedBasis
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.Quasithin.EmptyFaithful.Insp7NumP

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.K1 CFSG.GorensteinWalter
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

namespace S143

namespace InspW2

theorem numFactW_oddL2 : NumFactW Insp7.OddL2Fam := by
  intro L _ _ hq hF z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard h4 hC3
  obtain ⟨p, hFM, hmodel⟩ := hF
  have hp : p.Prime := hFM.1
  have hp2 : p ≠ 2 := Insp7.fm_ne_two hFM
  obtain ⟨K, _, _, _, e, hq1, hchar, hq5⟩ := psl2_model_data hp2 hmodel
  have hKp : Fintype.card K = p := by rw [hq1, pow_one]
  have hp5 : 5 ≤ p := hKp ▸ hq5
  have hZ : Subgroup.center L = ⊥ := by
    have h1 : (Subgroup.center L).map e.toMonoidHom = Subgroup.center PSL(2, K) :=
      Subgroup.map_center_eq e
    rw [psl2_center_eq_bot K] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hez1 : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
  have hez2 : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
  obtain ⟨a, ha⟩ := Insp7.exists_two_pow_card_centralizer_psl2 hFM hKp hchar hp5 hez1 hez2
  have hcardL : Nat.card (Subgroup.centralizer ({z} : Set L)) = 2 ^ a := by
    rw [← ha, ← Insp7.map_centralizer_singleton_mulEquiv e z]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv)
  have hcl : ∀ l : L, l * z = z * l → l ^ (2 ^ a) = 1 := by
    intro l hl
    have hmem : l ∈ Subgroup.centralizer ({z} : Set L) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hl
    have h := pow_card_eq_one' (G := ↥(Subgroup.centralizer ({z} : Set L))) (x := ⟨l, hmem⟩)
    rw [hcardL] at h
    exact congrArg Subtype.val h
  have hpow : ∀ c : Gc, c ∈ Subgroup.centralizer ({ž} : Set Gc) → c ^ (2 ^ (a + 1)) = 1 := by
    intro c hc
    have hcc : c * ž = ž * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hρc : ρ c * MulAut.conj z = MulAut.conj z * ρ c := by
      rw [← hž, ← map_mul, ← map_mul, hcc]
    obtain ⟨g, hg⟩ := Insp7.sq_inner_psl2 hp hp2 hKp hp5 (transAut e (ρ c))
    refine Insp7.pow_eq_one_of_sq_inner hZ ρ hρ z a hcl c hρc (e.symm g) ?_
    ext x
    apply e.injective
    have h1 := congrArg (fun m : MulAut PSL(2, K) => m (e x)) hg
    simp only [MulAut.mul_apply, transAut_apply, MulAut.conj_apply] at h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  have hC2 : IsPGroup 2 (Subgroup.centralizer ({ž} : Set Gc)) := fun g =>
    ⟨a + 1, Subtype.ext (hpow g.1 g.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hC2
  rw [hm] at hC3
  have h3 : 3 ∣ 2 ^ m := ⟨Nat.card Ŝ, by rw [hC3]⟩
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem numFactW_psl32 : NumFactW (fun L _ => StatedClassicalModel L .PSL 3 2 1) :=
  numFactW_of_union (G' := Insp7.OddL2Fam) (H := Insp7.OddL2Fam)
    (fun _ _ h => Or.inl ⟨7, ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩,
      CFSG.QuasithinUnique.Id2519.psl2_seven_of_psl3_two h⟩) numFactW_oddL2 numFactW_oddL2

end InspW2

end S143

end CFSG.Quasithin
