module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeALift
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear Matrix

section Cfg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}

theorem GGTypeANbrCfg.exists_lift_K (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∃ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
  have hNc := hN
  obtain ⟨hcfg, hOp, hInn, hNoTr, hmod, hpq, hn, hsc, hnbr, hmodK, hW, hAll⟩ := hN
  have hp : p.Prime := GGTypeANbrCfg.prime hNc
  have hf1 : 1 ≤ f := GGTypeANbrCfg.one_le_f hNc
  have hf : 2 ≤ f := by
    by_contra hlt
    have hf' : f = 1 := by omega
    rw [hf'] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  have hn2 : 2 ≤ n := by have := GGTypeANbrCfg.three_le hNc; omega
  have hnf : ¬ (n = 2 ∧ f = 2) := by
    rintro ⟨h1, -⟩
    omega
  have hperf : commutator K = ⊤ := (hInn.2 y K hnbr).1
  exact exists_slLift_of_classicalModel hn2 hf hnf hperf hmodK

theorem GGTypeANbrCfg.not_y_comm_L (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ¬ ∀ l ∈ L, y * l = l * y := by
  intro hcomm
  have hNc := hN
  have hp : p.Prime := GGTypeANbrCfg.prime hNc
  have hyzx : y ∈ Subgroup.zpowers x :=
    GGTypeANbrCfg.mem_zpowers_x_of_comm_L hNc y (GGTypeANbrCfg.y_mem hNc) hcomm
  obtain ⟨hcfg, -, -, -, htypeA⟩ := hN
  obtain ⟨hmod, hpq, hn, hsc, hnbr, hmodK, hW, hAll⟩ := htypeA
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hnbr.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_zpowers _
    · exact hyzx
  have hcardD : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hxne : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxpow : x ^ p = 1 := GGTypeANbrCfg.exponent hNc x (GGTypeANbrCfg.x_mem hNc)
  have hxord : orderOf x = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxpow hxne
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
  rw [hcardD, hcardx] at hle
  nlinarith [hp.two_le]

section Certs

theorem exists_mem_ggInducedPairs_of_innerDiagOn (hMp : GGInnerDiagMpInput) {Bs X : Subgroup G}
    (hn : 2 ≤ n) (hadm : StatedLieAdmissible .PSL (n + 1) 2 f) (hmark : GGInnerDiagOn Bs X)
    {φ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hrange : φ.range = X) :
    ∀ b ∈ Bs, ∃ A : GL (Fin (n + 1)) (GaloisField 2 f), (b, A) ∈ LinFusion.ggInducedPairs φ := by
  let ψ : (ggU .PSL (n + 1) f).K →* G := φ
  have hrk : 2 ≤ (ggU .PSL (n + 1) f).D.rank := by
    show 2 ≤ n
    exact hn
  have hkerψ : ψ.ker ≤ Subgroup.center (ggU .PSL (n + 1) f).K := hker
  have hrangeψ : ψ.range = X := hrange
  have hQ : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSL (n + 1) f).D ψ b := by
    have hmk := hMp G .PSL (n + 1) f ψ hadm hrk hkerψ X hrangeψ _ hmark
    exact largeEvenMarking_elim_const
      (Q := ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSL (n + 1) f).D ψ b)
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h b hb => h.2 b (h.1.1 hb) (h.1.2 b hb)) hmk)
  intro b hb
  exact LinFusion.exists_mem_ggInducedPairs hn ψ hkerψ (hQ b⁻¹ (Bs.inv_mem hb))

end Certs

end Cfg

end CFSG.StandardType

end
