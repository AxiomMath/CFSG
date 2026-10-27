module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepToral
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWitt

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.TableCRes
open CFSG.Open (StatedLieTag)

section Genuine


theorem rckPSULiftHyp_of_compConfig {X : Type} [Group X] [Finite X] {n g : ℕ}
    {ψ : (ggU .PSU n (g + 1)).K →* X} {p : ℕ} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (h : RCKCompConfig .PSU n (g + 1) ψ p G₀ A B₁ D J L K e)
    (hID : ∀ a ∈ A, GGPsiInnerDiag (ggU .PSU n (g + 1)).D ψ a) :
    PSULiftHyp n g ψ p A := by
  unfold RCKCompConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, heD, he1, hKcomp, hJK, hOddK⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := hGG.1.1
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K := hGG.2.1.2
  have hcard4 : p ^ 4 ≤ Nat.card A := le_trans hp4 (Subgroup.card_le_of_le hB1A)
  have hN : p ∣ 2 ^ (g + 1) + 1 → p ^ (n - 3) ≤ Nat.card A := by
    intro hpq
    rcases Nat.lt_or_ge n 4 with hn | hn
    · have hn3 : n = 3 := by have := hadm.2.2.1; omega
      rw [hn3]
      simp
      exact Nat.card_pos
    · have hc : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 :=
        card_galoisField_two_mul 2 (g + 1) (Nat.le_add_left 1 g)
      have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (g + 1)
          (GaloisField 2 (2 * (g + 1))) :=
        ⟨Nat.prime_two, by omega, by rw [hc, ← pow_mul, mul_comm]⟩
      have hψ'mem : ∀ x : (ggU .PSU n (g + 1)).K, ψ x ∈ A ⊔ G₀ := fun x => by
        have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
        rw [hrange] at hx
        exact Subgroup.mem_sup_right hx
      let ψ' : (ggU .PSU n (g + 1)).K →* ↥(A ⊔ G₀) := ψ.codRestrict (A ⊔ G₀) hψ'mem
      have hker' : ψ'.ker ≤ Subgroup.center ↥(Unitary.SU (PSUσ g) n) := by
        intro x hx
        have h1 : ψ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        exact hker (MonoidHom.mem_ker.mpr h1)
      obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hc n
      have hframe : SURep.GGFrameKer (SURep.ggFrameU hc ψ' P hP) :=
        SURep.ggFrameKer_ggFrameU hc ψ' P hP hadm.2.2.1 hadm.2.2.2 hker'
      have hrank : n - 3 ≤ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
        SURep.sub_three_le_twoLocalRankU hUF hp hp2 hpq hn hframe
      exact (Nat.pow_le_pow_right hp.pos hrank).trans hrank2
  have hnorm : A ≤ Subgroup.normalizer (ψ.range : Set X) := by
    rw [hrange]
    exact hAnorm
  have hfaith : A ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ := by
    rw [hrange]
    exact hAc
  refine ⟨hadm, hker, hp, hp2, hnorm, ?_, hAel, hcard4, hfaith, hN⟩
  intro b hb
  exact hID b hb

end Genuine

end CFSG.StandardType.RCKRP
