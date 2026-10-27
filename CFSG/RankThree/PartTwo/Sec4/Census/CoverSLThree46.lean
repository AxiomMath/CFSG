module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem card_scalars_dvd_three {K : Type} [Field K] [Finite K] {p f : ℕ}
    {H : Subgroup (GL (Fin 3) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL 3 K) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU 3 (p ^ f) K)) :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf H) ∣ 3 :=
  SectionRank.OddCover.card_scalars_dvd (by norm_num) H fun x c hc => by
    have hdet := SectionRank.OddCover.det_eq_one_of_linUni hH x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])

theorem nonempty_mulEquiv_of_odd_splitting {X H : Type} [Group X] [Finite X]
    [Group.IsPerfect X] [Group H] [Finite H] {D : Subgroup H} [D.Normal]
    (hodd : Odd (Nat.card (Subgroup.center X))) (hZ : Subgroup.center X ≠ ⊥)
    (e : X ⧸ Subgroup.center X ≃* H ⧸ D) (hD : Nat.card D ∣ 3)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : H →* E, ∀ g, π (s g) = g) :
    Nonempty (X ≃* H) := by
  obtain ⟨φ, hφ, -, hmap⟩ := QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting hodd e hsplit
  have hdvd : Nat.card (Subgroup.center X) ∣ 3 := by
    rw [← hmap]
    exact (Subgroup.card_map_dvd D φ).trans hD
  have h3 : Nat.card (Subgroup.center X) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left
      fun h1 => hZ (Subgroup.card_eq_one.mp h1)
  exact ⟨(MulEquiv.ofBijective φ (QuasithinUnique.Ch1.bijective_of_scalar_cover e h3 hD hφ).2).symm⟩

theorem five_le_of_pow_mod_three {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (h3 : p ^ e % 3 ≠ 0) : 5 ≤ p := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 (Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega)))
  have h2 := hp.two_le
  rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
  · exact absurd h hp2
  · exact absurd h hp3
  · exact absurd (h ▸ hp) (by norm_num)
  · exact h

theorem sq_mod_three_ne_two (p : ℕ) : p ^ 2 % 3 ≠ 2 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt p (show 0 < 3 by norm_num)
  interval_cases (p % 3) <;> norm_num

theorem false_of_isQuasisimple_projSU_three_two {X : Type} [Group X] (hq : IsQuasisimple X)
    (f : X ⧸ Subgroup.center X ≃* projSU 3 2 1) : False := by
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have := Sec13.isSolvable_projSU_two
  have hsolv : Group.IsSolvable (X ⧸ Subgroup.center X) :=
    Group.isSolvable_of_surjective (f := f.symm.toMonoidHom) f.symm.surjective
  obtain ⟨x, y, hxy⟩ := hq.2.2
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

theorem statedSL_three_exists_section {K : Type} [Field K] [Finite K] (hK : 5 ≤ Nat.card K)
    {E : Type} [Group E] {π : E →* StatedSL 3 K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ s : StatedSL 3 K →* E, ∀ g, π (s g) = g := by
  set ε := specialLinearGroupEquivStatedSL 3 K with hε
  set π' : E →* Matrix.SpecialLinearGroup (Fin 3) K := ε.symm.toMonoidHom.comp π with hπ'
  have hker : π'.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπ', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  obtain ⟨s', hs'⟩ := LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
    (m := 2) le_rfl hK (π := π') (ε.symm.surjective.comp hπ) (hker ▸ hcen)
  refine ⟨s'.comp ε.symm.toMonoidHom, fun g => ε.symm.injective ?_⟩
  have h := hs' (ε.symm g)
  rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact h

section Cover

theorem isSLThreeEpsAt_of_linear {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hodd : Odd (Nat.card (Subgroup.center X))) (hZ : Subgroup.center X ≠ ⊥) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (h1 : p ^ e % 3 = 1)
    (f : X ⧸ Subgroup.center X ≃* projSL 3 (GaloisField p e)) : IsSLThreeEpsAt X (p ^ e) := by
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have e' : X ⧸ Subgroup.center X ≃* StatedProj (StatedSL 3 (GaloisField p e)) :=
    f.trans ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL 3 _))).symm
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSL 3 (GaloisField p e)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : StatedSL 3 (GaloisField p e) →* E, ∀ g, π (s g) = g := by
    intro E _ _ π hπ hC hoddπ
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨s, hs, -⟩ :=
        SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated (n := 3)
          (by norm_num) hπ hC hoddπ
      exact ⟨s, hs⟩
    · have hp5 := five_le_of_pow_mod_three Fact.out hp2 he (by omega)
      refine statedSL_three_exists_section ?_ hπ hC
      rw [hK]
      exact hp5.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_odd_splitting hodd hZ e'
    (card_scalars_dvd_three (Or.inl ⟨hK, rfl⟩)) hsplit
  exact ⟨GaloisField p e, inferInstance, inferInstance, Or.inl ⟨hK, ⟨φ⟩⟩⟩

theorem isSLThreeEpsAt_of_unitary {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hodd : Odd (Nat.card (Subgroup.center X))) (hZ : Subgroup.center X ≠ ⊥) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (hb : p = 2 ∨ e ≤ 2) (h2 : p ^ e % 3 = 2)
    (h21 : ¬(p = 2 ∧ e = 1)) (f : X ⧸ Subgroup.center X ≃* projSU 3 p e) :
    IsSLThreeEpsAt X (p ^ e) := by
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have e' : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 (p ^ e) (GaloisField p (2 * e))) :=
    f.trans (statedSUEquivProjSU 3 p e).symm
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* StatedSU 3 (p ^ e) (GaloisField p (2 * e))),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : StatedSU 3 (p ^ e) (GaloisField p (2 * e)) →* E, ∀ g, π (s g) = g := by
    by_cases hp2 : p = 2
    · subst hp2
      have he2 : 2 ≤ e := by omega
      intro E _ _ π hπ hC hoddπ
      obtain ⟨s, hs, -⟩ :=
        SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting hK he2 hπ hC
          hoddπ
      exact ⟨s, hs⟩
    · have hp : p.Prime := Fact.out
      have he1 : e = 1 := by
        rcases (show e = 1 ∨ e = 2 by omega) with h | h
        · exact h
        · exact absurd (h ▸ h2) (sq_mod_three_ne_two p)
      subst he1
      have hK' : Nat.card (GaloisField p (2 * 1)) = p ^ 2 := by rw [hK, pow_one]
      have hsplitq : ∀ q : ℕ, q = p → ∀ (E : Type) [Group E] [Finite E]
          (π : E →* StatedSU 3 q (GaloisField p (2 * 1))), Function.Surjective π →
          π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
          ∃ s : StatedSU 3 q (GaloisField p (2 * 1)) →* E, ∀ g, π (s g) = g := by
        rintro q rfl E _ _ π hπ hC hoddπ
        obtain ⟨⟨s, hs, -⟩, -⟩ :=
          SectionRank.OddCover.prime_classical_three_central_odd_extension_splitting hp hp2
            (Or.inr ⟨rfl, hK', rfl⟩) π hπ hC hoddπ
        exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
      exact hsplitq (p ^ 1) (pow_one p)
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_odd_splitting hodd hZ e'
    (card_scalars_dvd_three (Or.inr ⟨hK, rfl⟩)) hsplit
  exact ⟨GaloisField p (2 * e), inferInstance, inferInstance, Or.inr ⟨hK, ⟨φ⟩⟩⟩

theorem coverSLThree46 : CoverSLThree46 := by
  intro X _ _ hq hZ3 hZ p e _ he hb hpi
  have : Group.IsPerfect X := hq.1
  have hodd : Odd (Nat.card (Subgroup.center X)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  rcases hpi with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
  · exact isSLThreeEpsAt_of_linear hodd hZ he h1 f
  · by_cases h21 : p = 2 ∧ e = 1
    · obtain ⟨rfl, rfl⟩ := h21
      exact (false_of_isQuasisimple_projSU_three_two hq f).elim
    · exact isSLThreeEpsAt_of_unitary hodd hZ he hb h2 h21 f

end Cover

end CFSG.RankThree.PartTwo.Sec4.Census
