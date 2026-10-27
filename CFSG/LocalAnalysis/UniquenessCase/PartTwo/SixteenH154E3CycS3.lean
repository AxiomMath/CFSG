module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ChiD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_card_two_eq {M : Type*} [Group M] {A : Subgroup M}
    (hA : Nat.card A = 2) {a b : M} (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
  have hay : (⟨a, ha⟩ : ↥A) = y := hyuniq ⟨a, ha⟩ (by simpa using ha1)
  have hby : (⟨b, hb⟩ : ↥A) = y := hyuniq ⟨b, hb⟩ (by simpa using hb1)
  exact Subtype.ext_iff.mp (hay.trans hby.symm)

private theorem s16h_e3_prime_ne_two (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) {p : ℕ} (hp : p.Prime)
    (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n) :
    p ≠ 2 := by
  intro hp2
  apply hχ
  intro n _ hnN l hl
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 2 := hLp.2.trans hp2
  by_cases hl1 : l = 1
  · rw [hl1]; group
  have hconj : n * l * n⁻¹ ∈ lBar V₀ V hV L := (Subgroup.mem_normalizer_iff.1 hnN l).1 hl
  have hconj1 : n * l * n⁻¹ ≠ 1 := by
    intro h
    apply hl1
    have h2 := congrArg (fun x => n⁻¹ * x * n) h
    simpa [mul_assoc] using h2
  have heq : n * l * n⁻¹ = l := s16h_e3_card_two_eq hcard hconj hl hconj1 hl1
  calc n * l = (n * l * n⁻¹) * n := by group
    _ = l * n := by rw [heq]

theorem s16h_e3_cyclic_unique_of_s_ge_three (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hs : 3 ≤ s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n) :
    (∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) ∧
    (∀ x ∈ D.M, ∀ y ∈ D.M,
      conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ≠
        conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y →
      ∀ w ∈ v1Sub D.M V₀ V h.hyp151.isElemAbelian L ⊔
        ⨆ X ∈ {X | X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y}, X,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) := by
  have hV := h.hyp151.isElemAbelian
  have hp2 : p ≠ 2 := s16h_e3_prime_ne_two D hV hp hLp hχ
  have hσ3 : ∃ q ∈ D.sig, 3 ≤ CFSG.Open.pRank q D.M := by
    obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    exact ⟨q, hq, S.hSig.three_le q hq⟩
  have hU2 : s16h_CondU2 D V₀ V L hV :=
    s16h_condU2_of_chi_ne D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112 S.hThin S.hCyc
      S.h127 hσ h hc hp hp2 hLp hχ
  refine ⟨s16h_unique₁_of_condU2 D S.h61 h hσ3 hU2 (by omega), ?_⟩
  intro x hx y hy hxy w hw hw1
  by_cases hw0 : w ∈ V₀
  · exact s16h_v0_good D S.h61 h.hyp16 hσ3 w hw0 hw1
  · have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
        h.hyp151.hyp125.pairFacts.le_normalizer₀
    have hne : barSub V₀ V hV (conjSubgroup L x) ≠ barSub V₀ V hV (conjSubgroup L y) := by
      intro heq
      apply hxy
      rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx),
        ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hy)]
      unfold wSub wTil
      rw [heq]
    have hwx : w ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))) :=
      s16h_le_preTil_fixV_of_ne D h.hyp151 hx
        (S := {X : Subgroup G | X ∈ wConj D.M V₀ V hV L ∧
          X ≠ conjSubgroup (wSub V₀ V hV L) x ∧ X ≠ conjSubgroup (wSub V₀ V hV L) y})
        (fun X hX => ⟨hX.1, hX.2.1⟩) hw
    have hwy : w ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L y))) :=
      s16h_le_preTil_fixV_of_ne D h.hyp151 hy
        (S := {X : Subgroup G | X ∈ wConj D.M V₀ V hV L ∧
          X ≠ conjSubgroup (wSub V₀ V hV L) x ∧ X ≠ conjSubgroup (wSub V₀ V hV L) y})
        (fun X hX => ⟨hX.1, hX.2.2⟩) hw
    exact hU2 x hx y hy hne w ⟨hwx, hwy⟩ hw0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
