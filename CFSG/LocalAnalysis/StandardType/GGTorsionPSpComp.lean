module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionPSpComp

private theorem tps_conj_data {m : ℕ} {K : Type} [Field K] [Finite K]
    {p : ℕ} {δ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (h2 : (2 : K) = 0)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) = ⊥)
    (hδp : δ ^ p = 1)
    (hδ : δ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m)) :
    ∃ x : CFSG.Open.StatedSp m K,
      δ = MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x) ∧
        x ^ p = 1 := by
  obtain ⟨A, hA⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hδ
  obtain ⟨x, hx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hδx : δ = MulAut.conj
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x) :=
    hA.symm.trans hx
  refine ⟨x, hδx, ?_⟩
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ
    (by rw [← hδx]; exact hδp)

private theorem tps_card_quot_center_a6 {R F : Type} [Group R] [Field F] [Finite F]
    (hK2 : Nat.card F = 2) (e : ↥(commutator ↥(CFSG.Open.StatedSp 2 F)) ≃* R) :
    Nat.card (R ⧸ Subgroup.center R) = 360 := by
  let eR : R ≃* alternatingGroup (Fin 6) :=
    e.symm.trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK2)
  have hZ : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eR z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro a
      obtain ⟨y, rfl⟩ := eR.surjective a
      rw [← map_mul, ← map_mul, hz]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact eR.injective (by simpa using hz')
  calc Nat.card (R ⧸ Subgroup.center R) = Nat.card (R ⧸ (⊥ : Subgroup R)) := by rw [hZ]
    _ = Nat.card R := Nat.card_congr (QuotientGroup.quotientBot (G := R)).toEquiv
    _ = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr eR.toEquiv
    _ = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num

theorem ggTorsion_psp_components {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {δ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))} (hδp : δ ^ p = 1)
    (hδ : δ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m))
    {J : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))}
    (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    (∃ (t : CFSG.Open.StatedLieTag) (n' f : ℕ),
        CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) t n' 2 f) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rwa [← Nat.card_eq_fintype_card]
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨x, hδx, hxp⟩ := tps_conj_data h2 hZ hδp hδ
  subst hδx
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x)) =
      ggAutFixedSubgroup (MulAut.conj
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x)) :=
    Subgroup.ext fun _ => Iff.rfl
  have hJo : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x))) := by
    rw [hfix]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  obtain ⟨-, hcomp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
      (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      hp hp2 Nat.prime_two hn hK hm hp2 (fun h => h.elim) x hxp
  obtain ⟨X, inst, hXfin, ⟨hXL, -⟩, hfac, f, hf, hker⟩ := hcomp J hJo
  letI := inst
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hXL.perfect f hf hker
  let eY := e.symm
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hA6
  ·
    obtain ⟨a, j, E, hEf, hEfin, ha, hj, -, hEc, h4, ⟨eX⟩⟩ := hSL
    letI := hEf
    letI := hEfin
    have hnj : 1 ≤ n * j := Nat.mul_pos hn hj
    have hcard : Nat.card E = 2 ^ (n * j) := by
      rw [Nat.card_eq_fintype_card, hEc, hK, ← pow_mul]
    have hne22 : (a, 2 ^ (n * j)) ≠ (2, 2) := by
      intro hh
      obtain ⟨h1, h2'⟩ := Prod.mk.inj hh
      have hle := h4 h1
      rw [Fintype.card_eq_nat_card, hcard, h2'] at hle
      norm_num at hle
    have hne23 : (a, 2 ^ (n * j)) ≠ (2, 3) := by
      intro hh
      obtain ⟨-, h3⟩ := Prod.mk.inj hh
      have hdvd : 2 ∣ 2 ^ (n * j) := dvd_pow_self 2 (by omega)
      rw [h3] at hdvd
      norm_num at hdvd
    obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl a eX
    exact Or.inl ⟨CFSG.Open.StatedLieTag.PSL, a, n * j,
      ⟨⟨Nat.prime_two, hnj, ha, hne22, hne23⟩, E, inferInstance, inferInstance, hcard,
        ⟨eY.trans eZ⟩⟩⟩
  ·
    obtain ⟨a, j, q', E, hEf, hEfin, ha, hj, -, hq', hEc, hne, ⟨eX⟩⟩ := hSU
    letI := hEf
    letI := hEfin
    obtain rfl : q' = 2 ^ (n * j) := by rw [hq', hK, ← pow_mul]
    have hE : Nat.card E = (2 ^ (n * j)) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hEc]
    have hnj : 1 ≤ n * j := Nat.mul_pos hn hj
    have hcen := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (F := E) (p := 2) (f := n * j) hE ha hne).2
    obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eX
    exact Or.inl ⟨CFSG.Open.StatedLieTag.PSU, a, n * j,
      ⟨⟨Nat.prime_two, hnj, ha, hne⟩, E, inferInstance, inferInstance, hE,
        ⟨eY.trans (e₁.trans (QuotientGroup.quotientMulEquivOfEq hcen))⟩⟩⟩
  ·
    obtain ⟨-, -, s, hs, hne, ⟨eX⟩⟩ := hSp
    have hne' : ¬(s = 2 ∧ Nat.card K = 2) := fun h => hne (by rw [h.1, h.2])
    obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
      (s := s) hs hne' inferInstance eX
    exact Or.inl ⟨CFSG.Open.StatedLieTag.PSp, s, n,
      ⟨⟨Nat.prime_two, hn, hs, fun h => hne (by rw [hK]; exact h)⟩, K, inferInstance,
        inferInstance, hK, ⟨eY.trans eZ⟩⟩⟩
  ·
    obtain ⟨-, -, hK2, ⟨eX⟩⟩ := hA6
    exact Or.inr (by
      rw [← Nat.card_congr e.toEquiv]
      exact tps_card_quot_center_a6 hK2 eX.symm)

end TorsionPSpComp

end CFSG.StandardType
