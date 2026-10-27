module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTableP
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUB
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUC

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

private theorem qtwoDB23_unitary_model {R : Type} [Group R] {m : ℕ} {lab : LargeEvenLabel}
    (hm : 1 ≤ m) (hlab : GGHasLabel lab R)
    (hU : lab = ⟨.twA, m - 1, 1⟩ ∨ (lab = ⟨.twA, m, 1⟩ ∧ 3 ∣ m + 1)) :
    ∃ (s : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 4 ∧ Nonempty (R ≃* LargeEvenProj (LargeEvenSUGroup (Fin s) K 2)) ∧
      (s = m ∨ (s = m + 1 ∧ 3 ∣ m + 1)) := by
  rcases hU with h | ⟨h, h3⟩
  · subst h
    unfold GGHasLabel at hlab
    simp only [LargeEvenRawDatum] at hlab
    obtain ⟨K, hfield, hfin, hcard, hQ⟩ := hlab
    have hQ' : Nonempty (R ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) K 2)) := by
      have hQ'' := hQ
      rw [show m - 1 + 1 = m by omega] at hQ''
      exact hQ''
    exact ⟨m, K, hfield, hfin, by norm_num at hcard ⊢; omega, hQ', Or.inl rfl⟩
  · subst h
    unfold GGHasLabel at hlab
    simp only [LargeEvenRawDatum] at hlab
    obtain ⟨K, hfield, hfin, hcard, hQ⟩ := hlab
    exact ⟨m + 1, K, hfield, hfin, by norm_num at hcard ⊢; omega, hQ, Or.inr ⟨rfl, h3⟩⟩


theorem ggQTwoDUnit_not_unitary (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {N : Subgroup G} (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hU : lab = ⟨.twA, m - 1, 1⟩ ∨ (lab = ⟨.twA, m, 1⟩ ∧ 3 ∣ m + 1)) : False := by
  obtain ⟨s, K, hKfield, hKfin, hcardK, hQ, hs⟩ :=
    qtwoDB23_unitary_model (by omega) hlab hU
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨θ⟩ := hQ
  have hBsN : Bs ≤ Subgroup.normalizer (N : Set G) :=
    ggQTwoDUnit_normalizer_N (by omega) hbase b'.2 hN hJ₁
  obtain ⟨-, hcardA, hA, hAinn, hsc⟩ := qtwoDB36_gamma (by omega) hbase hcoords hdel hN hJ₁ hJ₂ hBsN
  let ψN : ↥N →* LargeEvenProj (LargeEvenSUGroup (Fin s) K 2) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥N))
  have hψ : Function.Surjective ψN := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψN.ker ≤ Subgroup.center ↥N := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥N) y) = 1 :=
      θ.injective (hy.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff y).mp h1
  have hs7 : 7 ≤ s := by rcases hs with h | ⟨h, -⟩ <;> omega
  have hcard : 3 ^ (s / 3 + 2) ≤ Nat.card (ggGamma N hBsN).range := by
    rw [hcardA]
    exact Nat.pow_le_pow_right (by norm_num) (by rcases hs with h | ⟨h, -⟩ <;> omega)
  have haut := qtwoDB36_aut_card hcardK hs7 hψ hker (qtwoDB36_perfect hN) hA hAinn hcard hsc
  obtain ⟨Θ, hΘ, -⟩ := qtwoDB36_weyl_embed (by omega) hbase hcoords hdel hN hJ₁ hJ₂ hBsN
  have hdvd := Subgroup.card_dvd_of_injective Θ hΘ
  rw [haut, qtwoDB36_card_dEvenStab (by omega) c] at hdvd
  obtain ⟨h1, h2⟩ := qtwoDB36_not_dvd hm
  rcases hs with rfl | ⟨rfl, -⟩
  · exact h1 hdvd
  · exact h2 hdvd

end CFSG.StandardType.QTwo

end
