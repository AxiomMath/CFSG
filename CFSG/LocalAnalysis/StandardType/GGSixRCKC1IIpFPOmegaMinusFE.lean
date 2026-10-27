module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Spin.Action
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightProj

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition

private lemma rckIIp_component_model_PSL_or_PSU (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomeι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomeJ n F bq cq).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomeQ n F bq cq))}
    {ε e : Matrix (fepomeι n) (fepomeι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomeG n F bq cq) (fepomeA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomeJ n F bq cq) S ε,
      glBlockCentralizer (fepomeJ n F bq cq) S ε⁆)
    (he : IsPrimIdemIn (fepomeA n F S) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (fepomeA n F S) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (fepomeA n F S) e)) :
    ∃ (t' : CFSG.Open.StatedLieTag) (m' f' : ℕ), f < f' ∧
      (t' = .PSL ∨ t' = .PSU) ∧
      CFSG.Open.StatedClassicalModel (↥J' ⧸ Subgroup.center ↥J') t' m' 2 f' := by
  classical
  have hf : 1 ≤ f := by
    have : Fintype F := Fintype.ofFinite F
    have h2 : 2 ≤ Fintype.card F :=
      Fintype.one_lt_card_iff.mpr (exists_pair_ne F)
    have h2' : 2 ≤ Nat.card F := by rwa [Nat.card_eq_fintype_card]
    by_contra h
    have h0 : f = 0 := by omega
    subst f
    rw [pow_zero] at hc
    omega
  rcases hdeg with ⟨hself, hd4⟩ | ⟨hne, hd2⟩
  · obtain ⟨K, hKfield, hKalg, hKfinite, π, hπsurj, hπker, hπdeg⟩ :=
      exists_blockField hS hodd he
    obtain ⟨l, hl, hl2, τ, hτcompat, hτ2, hτne⟩ :=
      fepome_selfDual_hermitian n hirr hn f hc S hSU hS hodd hε he heε hself hd4 K π
        hπsurj hπker hπdeg
    rcases fepome_selfDual_model n hirr hn f hc hf S hSU hS hodd hε hJε he heε hself hd4
        l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne with ⟨m', hm'3, hmod⟩ | hmod
    · refine ⟨.PSU, m', l * f, ?_, Or.inr rfl, hmod⟩
      have hl1 : 1 < l := by omega
      have hf0 : 0 < f := by omega
      simpa using Nat.mul_lt_mul_of_pos_right hl1 hf0
    · refine ⟨.PSL, 2, l * f, ?_, Or.inl rfl, hmod⟩
      have hl1 : 1 < l := by omega
      have hf0 : 0 < f := by omega
      simpa using Nat.mul_lt_mul_of_pos_right hl1 hf0
  · obtain ⟨K, hKfield, hKalg, hKfinite, π, hπsurj, hπker, hπdeg⟩ :=
      exists_blockField hS hodd he
    obtain ⟨m', hm'2, hmod⟩ :=
      fepome_dualPair_model n hirr hn f hc hf S hSU hS hodd hε hJε he heε hne hd2 K π
        hπsurj hπker hπdeg
    refine ⟨.PSL, m', blockDegree (fepomeA n F S) e * f, ?_, Or.inl rfl, hmod⟩
    have hd1 : 1 < blockDegree (fepomeA n F S) e := by omega
    have hf0 : 0 < f := by omega
    simpa using Nat.mul_lt_mul_of_pos_right hd1 hf0

theorem rckIIp_POmegaMinus_fieldExt
    {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (φ : (ggU .POmegaMinus n f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {J' : Subgroup (ggU .POmegaMinus n f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε :
          Subgroup (ggU .POmegaMinus n f).K),
        (glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε :
          Subgroup (ggU .POmegaMinus n f).K)⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega : f ≠ 0)
  obtain ⟨t', m', f', hlt, ht', hmod⟩ :=
    rckIIp_component_model_PSL_or_PSU n (minusCoeffs_irr 2 f) hn f hc S hSU hS hodd hε hJe he
      heε hdeg
  have hperf : _root_.commutator ↥J' = ⊤ := hJe.2.2.1
  obtain ⟨ξ⟩ := fepome_quotientCenter φ hφk hperf
  have hmod' : CFSG.Open.StatedClassicalModel
      (↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) t' m' 2 f' :=
    fepome_statedClassicalModel_congr ξ t' m' 2 f' hmod
  exact CFSG.StandardType.RCKC1.rckIIp_false_of_alt_eight_statedClassicalModel
    ht' (by omega) hmod' hA8

end CFSG.StandardType.RCKC1
