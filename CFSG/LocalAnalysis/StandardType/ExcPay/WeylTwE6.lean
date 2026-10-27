module

public import CFSG.LocalAnalysis.StandardType.ExcPay.Defs

import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
import CFSG.LieType.Chevalley.C2E6FirstResidueLevi
import CFSG.RankThree.Classical2.TwistedE6RationalOrder
import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTRank
import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
import CFSG.LocalAnalysis.StandardType.GGFinModelRat
import CFSG.RankThree.PartOne.Q1327T.Item7D4W

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem excPayW6_le_of_commutator_index_eq_three_pow {M : Type*} [Group M]
    {R C E : Subgroup M} (hC : ⁅R, R⁆ = C) {k : ℕ}
    (hidx : (C.subgroupOf R).index = 3 ^ k) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ 3)
    (hER : E ≤ R) (hE : ∀ x ∈ E, x ^ ℓ = 1) : E ≤ C := by
  let N : Subgroup ↥R := C.subgroupOf R
  have : N.Normal := by
    have hNcomm : N = _root_.commutator ↥R := by
      change C.subgroupOf R = _root_.commutator ↥R
      rw [← hC, ← Subgroup.map_subtype_commutator R]
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    rw [hNcomm, commutator_def]
    exact Subgroup.commutator_normal (⊤ : Subgroup ↥R) ⊤
  intro x hx
  have hxR : x ∈ R := hER hx
  let y : ↥R := ⟨x, hxR⟩
  let q : ↥R →* ↥R ⧸ N := QuotientGroup.mk' N
  have h1 : (q y) ^ (3 ^ k) = 1 := by
    rw [← hidx, ← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ N.index)).2 (Subgroup.pow_index_mem N y)
  have hyp : y ^ ℓ = 1 := Subtype.ext (hE x hx)
  have h2 : (q y) ^ ℓ = 1 := by
    rw [← map_pow, hyp, map_one]
  have hcop : Nat.Coprime (3 ^ k) ℓ := Nat.Coprime.pow_left k hℓ.symm
  have hdvd : orderOf (q y) ∣ Nat.gcd (3 ^ k) ℓ :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hdvd
  have hy : y ∈ N := (QuotientGroup.eq_one_iff y).1 (orderOf_eq_one_iff.1 hdvd)
  simpa using Subgroup.mem_subgroupOf.mp hy


private lemma excPayW6_simple_weyl_comm {p f : ℕ} {ht : GGExcFive .twistedE6}
    (hplus : p ∣ 2 ^ f + 1) (M : GGDatumModel .twistedE6 f p ht)
    (k : Fin (langTag .twistedE6).rank) :
    (show WeylGroup TwistTag.E6.tag from M.w) * weylTwist TwistTag.E6
        (simple TwistTag.E6.tag k) =
      simple TwistTag.E6.tag k * (show WeylGroup TwistTag.E6.tag from M.w) := by
  let t : TwistTag := TwistTag.E6
  let k' : Fin t.tag.rank := k
  let w : WeylGroup t.tag := M.w
  have hcongr : ∀ u : Fin (langTag .twistedE6).rank → ℤ,
      permLattice ((finCongr (rank_eq_langTag f ht)).permCongr
        (1 : Equiv.Perm (Fin ((ggU (absTag .twistedE6) 6 f).D.rank)))) u = u := by
    intro u
    rw [show (1 : Equiv.Perm (Fin ((ggU (absTag .twistedE6) 6 f).D.rank))) = Equiv.refl _
      from Equiv.Perm.one_def]
    rw [Equiv.permCongr_refl]
    rfl
  have hw_smul : ∀ u : Fin t.tag.rank → ℤ,
      w • permLattice t.perm u = eps p f • u := by
    intro u
    have h := M.hw u
    rw [piB_twistedE6_of_dvd f hplus, hcongr u] at h
    exact h
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin t.tag.rank → ℤ)
  intro u
  have hd : weylTwist t (simple t.tag k') • u =
      permLattice t.perm (simple t.tag k' • permLattice t.perm.symm u) :=
    weylTwist_smul t (simple t.tag k') u
  have hwρ : w • u = eps p f • permLattice t.perm.symm u := by
    have h := hw_smul (permLattice t.perm.symm u)
    rwa [permLattice_permLattice_symm] at h
  calc (w * weylTwist t (simple t.tag k')) • u
      = w • (weylTwist t (simple t.tag k') • u) := by rw [mul_smul]
    _ = w • (permLattice t.perm (simple t.tag k' • permLattice t.perm.symm u)) := by
        rw [hd]
    _ = eps p f • (simple t.tag k' • permLattice t.perm.symm u) := by rw [hw_smul]
    _ = simple t.tag k' • (eps p f • permLattice t.perm.symm u) := by rw [smul_comm]
    _ = simple t.tag k' • (w • u) := by rw [hwρ]
    _ = (simple t.tag k' * w) • u := by rw [mul_smul]

private lemma excPayW6_simple_comm {p f : ℕ} {ht : GGExcFive .twistedE6}
    (hplus : p ∣ 2 ^ f + 1) (M : GGDatumModel .twistedE6 f p ht)
    (k : Fin (langTag .twistedE6).rank) :
    M.D.n * canonicalRep (coxeterSystem (langTag .twistedE6)) GGL
        (weylTwist TwistTag.E6 (simple (langTag .twistedE6) k)) =
      canonicalRep (coxeterSystem (langTag .twistedE6)) GGL
        (simple (langTag .twistedE6) k) * M.D.n := by
  let t : TwistTag := TwistTag.E6
  let k' : Fin t.tag.rank := k
  let w : WeylGroup t.tag := M.w
  have hw_comm : w * weylTwist t (simple t.tag k') = simple t.tag k' * w :=
    excPayW6_simple_weyl_comm hplus M k
  have hcomm_t : canonicalRep (coxeterSystem t.tag) GGL w *
      canonicalRep (coxeterSystem t.tag) GGL (weylTwist t (simple t.tag k')) =
      canonicalRep (coxeterSystem t.tag) GGL (simple t.tag k') *
        canonicalRep (coxeterSystem t.tag) GGL w := by
    calc canonicalRep (coxeterSystem t.tag) GGL w *
          canonicalRep (coxeterSystem t.tag) GGL (weylTwist t (simple t.tag k'))
        = canonicalRep (coxeterSystem t.tag) GGL
            (w * weylTwist t (simple t.tag k')) :=
          (CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (τ := t.tag)
            (w := w) (v := weylTwist t (simple t.tag k'))).symm
      _ = canonicalRep (coxeterSystem t.tag) GGL (simple t.tag k' * w) :=
          congrArg (canonicalRep (coxeterSystem t.tag) GGL) hw_comm
      _ = canonicalRep (coxeterSystem t.tag) GGL (simple t.tag k') *
            canonicalRep (coxeterSystem t.tag) GGL w :=
          CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (τ := t.tag)
            (w := simple t.tag k') (v := w)
  have hn : M.D.n = canonicalRep (coxeterSystem t.tag) GGL w := M.hn
  rw [hn]
  exact hcomm_t

theorem canonicalRep_simple_mem_model_TwE6 {p f : ℕ} {ht : GGExcFive .twistedE6}
    (hplus : p ∣ 2 ^ f + 1) (M : GGDatumModel .twistedE6 f p ht)
    (k : Fin (langTag .twistedE6).rank) :
    canonicalRep (coxeterSystem (langTag .twistedE6)) GGL (simple (langTag .twistedE6) k) ∈
      M.D.model := by
  have hmem_adj : canonicalRep (coxeterSystem (langTag .twistedE6)) GGL
      (simple (langTag .twistedE6) k) ∈ adjointGroup (langTag .twistedE6) GGL :=
    canonicalRep_mem_adjointGroup (coxeterSystem (langTag .twistedE6)) GGL
      (simple (langTag .twistedE6) k)
  have hcomm := excPayW6_simple_comm hplus M k
  have hΦ_fix : M.D.Φ (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL
      (simple (langTag .twistedE6) k)) =
      canonicalRep (coxeterSystem (langTag .twistedE6)) GGL
        (weylTwist TwistTag.E6 (simple (langTag .twistedE6) k)) := by
    rw [M.hΦ]
    exact twistHom_canonicalRep TwistTag.E6 GGL (ggFrobT f)
      (simple (langTag .twistedE6) k)
  rw [LangDatum.mem_model]
  refine ⟨hmem_adj, ?_⟩
  rw [hΦ_fix, mul_inv_eq_iff_eq_mul]
  exact hcomm

private lemma excPayW6_commutator_index_setup {p f : ℕ} {ht : GGExcFive .twistedE6} (hf : 1 ≤ f)
    (M : GGDatumModel .twistedE6 f p ht) :
    ∃ (C : Subgroup (ModGL (langTag .twistedE6) GGL)) (k : ℕ),
      ⁅M.D.fix, M.D.fix⁆ = C ∧ (C.subgroupOf M.D.fix).index = 3 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * f)
  let : Algebra F GGL := (ggRatEmb (2 * f)).toAlgebra
  have : IsScalarTower (ZMod 2) F GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : Algebra.IsAlgebraic F GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F) (A := GGL)
  have : IsAlgClosure F GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hcardF : Nat.card F = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega : 2 * f ≠ 0), ← pow_mul, Nat.mul_comm]
  let σ : F →+* F := (iterateFrobeniusEquiv F 2 f).toRingHom
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := fun c => iterateFrobeniusEquiv_def F 2 f c
  obtain ⟨-, -, hder, ⟨k, hidx⟩, -, -, -⟩ :=
    (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf F hcardF σ hσ
      GGL (ggFrobT f) (ggFrobT_apply f))
  let C : Subgroup (ModGL (langTag .twistedE6) GGL) :=
    (graphFixedRootGroup TwistTag.E6 F σ).map (baseChangeGL (algebraMap F GGL))
  have hfix : CFSG.Blueprint.twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) = M.D.fix := by
    rw [ggFixGp_eq_fix M.D M.hΦ]
    rfl
  refine ⟨C, k, ?_, ?_⟩
  · rw [← hfix]
    exact hder
  · rw [← hfix]
    exact hidx

theorem mem_Γ_of_mem_model_TwE6 {p f : ℕ} {ht : GGExcFive .twistedE6} (hf : 1 ≤ f)
    (M : GGDatumModel .twistedE6 f p ht) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ 3)
    {z : ModGL (langTag .twistedE6) GGL} (hz : z ∈ M.D.model) (hzℓ : z ^ ℓ = 1) :
    z ∈ M.D.Γ := by
  classical
  obtain ⟨C, k, hC, hidx'⟩ := excPayW6_commutator_index_setup hf M
  have hcz : (MulAut.conj M.D.g0).toMonoidHom z ∈ M.D.fix := by
    have hmem : (MulAut.conj M.D.g0).toMonoidHom z ∈
        M.D.model.map (MulAut.conj M.D.g0).toMonoidHom := ⟨z, hz, rfl⟩
    rwa [LangDatum.map_conj_model] at hmem
  have hczℓ : ((MulAut.conj M.D.g0).toMonoidHom z) ^ ℓ = 1 := by
    rw [← map_pow, hzℓ, map_one]
  let E : Subgroup (ModGL (langTag .twistedE6) GGL) :=
    Subgroup.zpowers ((MulAut.conj M.D.g0).toMonoidHom z)
  have hER : E ≤ M.D.fix := Subgroup.zpowers_le.2 hcz
  have hE : ∀ x ∈ E, x ^ ℓ = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hg : ((MulAut.conj M.D.g0).toMonoidHom z) ^ (ℓ : ℤ) = 1 := by
      rw [zpow_natCast, hczℓ]
    calc (((MulAut.conj M.D.g0).toMonoidHom z) ^ m) ^ ℓ
        = (((MulAut.conj M.D.g0).toMonoidHom z) ^ m) ^ (ℓ : ℤ) := by rw [zpow_natCast]
      _ = ((MulAut.conj M.D.g0).toMonoidHom z) ^ (m * (ℓ : ℤ)) := by rw [← zpow_mul]
      _ = (((MulAut.conj M.D.g0).toMonoidHom z) ^ (ℓ : ℤ)) ^ m := by rw [zpow_mul']
      _ = (1 : ModGL (langTag .twistedE6) GGL) ^ m := by rw [hg]
      _ = 1 := one_zpow m
  have hEsub : E ≤ C :=
    excPayW6_le_of_commutator_index_eq_three_pow hC hidx' hℓ hER hE
  have hΓ : M.D.Γ.map (MulAut.conj M.D.g0).toMonoidHom = ⁅M.D.fix, M.D.fix⁆ :=
    LangDatum.map_conj_Γ M.D
  have hmem : (MulAut.conj M.D.g0).toMonoidHom z ∈
      M.D.Γ.map (MulAut.conj M.D.g0).toMonoidHom := by
    rw [hΓ, hC]
    exact hEsub (Subgroup.mem_zpowers _)
  exact (Subgroup.mem_map_iff_mem (f := (MulAut.conj M.D.g0).toMonoidHom)
    (MulAut.conj M.D.g0).injective).1 hmem

theorem canonicalRep_simple_mem_Γ_TwE6 {p f : ℕ} {ht : GGExcFive .twistedE6} (hf : 1 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) (M : GGDatumModel .twistedE6 f p ht)
    (k : Fin (langTag .twistedE6).rank) :
    canonicalRep (coxeterSystem (langTag .twistedE6)) GGL (simple (langTag .twistedE6) k) ∈
      M.D.Γ := by
  have hsquare : canonicalRep (coxeterSystem (langTag .twistedE6)) GGL
      (simple (langTag .twistedE6) k) ^ 2 = 1 := by
    rw [pow_two,
      ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo
        (τ := langTag .twistedE6) (w := simple (langTag .twistedE6) k)
        (v := simple (langTag .twistedE6) k),
      (coxeterSystem (langTag .twistedE6)).simple_mul_simple_self, canonicalRep_one]
  exact mem_Γ_of_mem_model_TwE6 hf M (ℓ := 2) (by decide)
    (canonicalRep_simple_mem_model_TwE6 hplus M k) hsquare

end CFSG.StandardType.ExcPay
