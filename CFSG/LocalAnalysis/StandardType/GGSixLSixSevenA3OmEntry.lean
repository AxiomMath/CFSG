module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmModel
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmNumerics
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCases

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCOrthComm (matrixDerivedEquiv)

section Group

theorem mem_of_exists_mem_centralizer_of_not_dvd {G : Type*} [Group G] [Finite G]
    {R : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcen : ¬ p ∣ Nat.card (Subgroup.centralizer (R : Set G))) {b : G} (hbp : b ^ p = 1)
    (hb : ∃ g ∈ R, b * g ∈ Subgroup.centralizer (R : Set G)) : b ∈ R := by
  obtain ⟨g, hg, hc⟩ := hb
  have hgc : Commute (b * g) g := (Subgroup.mem_centralizer_iff.mp hc g hg).symm
  have hcg : Commute (b * g) g⁻¹ := hgc.inv_right
  have hb' : b = (b * g) * g⁻¹ := by group
  have hpow : (b * g) ^ p = g ^ p := by
    have h1 : 1 = (b * g) ^ p * (g ^ p)⁻¹ := by
      conv_lhs => rw [← hbp, hb']
      rw [hcg.mul_pow, inv_pow]
    rwa [eq_comm, mul_inv_eq_one] at h1
  have hord : orderOf (b * g) ∣ Nat.card (Subgroup.centralizer (R : Set G)) := by
    have h := orderOf_dvd_natCard (⟨b * g, hc⟩ : Subgroup.centralizer (R : Set G))
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime p (orderOf (b * g)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hcen (h.trans hord)
  have hcR : b * g ∈ R := by
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm, hpow]
    exact R.pow_mem (R.pow_mem hg _) _
  rw [hb']
  exact R.mul_mem hcR (R.inv_mem hg)

end Group

section Model


theorem exists_conj_le_of_model_bstar {G : Type} [Group G] [Finite G] {U : Type} [Group U]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U}
    {t : StatedLieTag} {n f : ℕ} {ψ : U →* G} (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {d : ℕ} {Q : QuadraticForm (GaloisField 2 f) (Fin d → GaloisField 2 f)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 f) (Fin d → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hψ : Function.Injective ψ) (π : U →* matrixDerived Q) (hπ : Function.Bijective π)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hA : GGSixLSevenA3Case J) (hBB : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) :
    ∃ g ∈ ggG0 p B x L D J, D.map (MulAut.conj g).toMonoidHom ≤ J := by
  classical
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : ψ.range = ggG0 p B x L D J := hctx.2.2.2.2.1.1
  have hcen : ¬ p ∣ Nat.card (Subgroup.centralizer (ψ.range : Set G)) := by
    rw [hrange]
    exact not_dvd_card_centralizer_ggG0_of_stdSub hp hctx.sstar hctx.stdType hctx.stdSub
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : ↥(orthDerived Q) →* G :=
    ψ.comp (πe.symm.toMonoidHom.comp (matrixDerivedEquiv Q).symm.toMonoidHom) with hφ
  have hφinj : Function.Injective φ :=
    hψ.comp (πe.symm.injective.comp (matrixDerivedEquiv Q).symm.injective)
  have hφr : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨matrixDerivedEquiv Q (πe u), by simp [hφ]⟩
  have hG₀ : φ.range = ggG0 p B x L D J := hφr.trans hrange
  have hBs := hctx.bstar
  have hBφ : Bs ≤ φ.range := by
    intro b hb
    rw [hφr]
    exact mem_of_exists_mem_centralizer_of_not_dvd hp hcen (hBs.2.1.2 b hb) (hdiag b hb)
  have hJc : IsComponentOf J (ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G)) :=
    hctx.j_isComponentOf_inf
  have hq : CFSG.Assembly.IsQuasisimple J := hJc.2.2
  obtain ⟨v, hv, hconj⟩ := CoordOm.exists_mem_normalizer_conj_le_of_model hp2 hnd hT hφinj hBφ
    hBs.2.1 hctx.pow_four_le_card_bstar
    (fun g hg hgp => hBs.2.2.2 g (Subgroup.mem_inf.mp hg).2 hgp) hctx.d_le_bstar hctx.card_d
    (by rw [hG₀]; exact hJc) hBB (card_dvd_of_a3Case hq hA)
    (eq_one_of_central_pow_of_a3Case hp hp2 hq hA)
  refine ⟨v⁻¹, ?_, ?_⟩
  · rw [← hG₀]
    exact φ.range.inv_mem (Subgroup.mem_inf.mp hv).1
  · rintro _ ⟨e, he, rfl⟩
    have h := hconj e he
    simpa [MulAut.conj_apply] using h

@[expose] def GGSixLSixSevenA3BstarInput (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    GGSixLSevenA3Case J → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

theorem ggSixLSixSevenConjA3At_POmegaPlus_of_bstar (h : GGSixLSixSevenA3BstarInput .POmegaPlus) :
    GGSixLSixSevenConjA3At .POmegaPlus := by
  intro G _ _ p B Bs x L D J n f
  have hBB := h G p B Bs x L D J n f
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn] at hBB ⊢
    intro ψ hctx hC2 hodd hcomp hA
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hker⟩ := hctx.2.2.2.2.1
    have hψinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
        ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
      exact hker
    obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 f) hn
    exact exists_conj_le_of_model_bstar hctx hnd hT hψinj (AutOm.spinModelPlus hn)
      ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩
      (fun b hb => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb))
      hA (hBB ψ hctx hC2 hodd hcomp hA)
  · intro ψ hctx _ _ _ _
    exact absurd hctx.2.2.2.1.1.2.2 (by omega)

end Model

end CFSG.StandardType
