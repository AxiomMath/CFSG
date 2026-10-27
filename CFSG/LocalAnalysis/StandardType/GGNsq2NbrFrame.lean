module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSQ2CellsDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate10010
public import Certificates.Certificate10011
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotActs
import CFSG.LocalAnalysis.StandardType.GGNsq2Hopf
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg Matrix

theorem ggNsq2Member_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {X : Subgroup G} (hcentX : Nat.card ↥(B ⊓ Subgroup.centralizer (X : Set G)) = p)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hdvd : p ∣ 2 ^ 1 + 1) {n : ℕ} (hn : n = 4 ∨ n = 6)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ 1)))
    (hperf : commutator ↥X = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1))) (LargeEvenGUSet (Fin n) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
      (f : ↥(Subgroup.normalizer (X : Set G)) →* Q) (ψ : Su K 2 1 n →* Q),
      NsQuot.Datum p (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X) ∧
      ψ.range = NsQuot.img (Subgroup.normalizer (X : Set G)) f X ∧
      GGNSLocalHyp p (NsQuot.img (Subgroup.normalizer (X : Set G)) f B)
        (NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) K 1 n ψ ∧
      GGActsDiagonally (p := 2) (f := 1) ψ
        (NsQuot.img (Subgroup.normalizer (X : Set G)) f Bs) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hBsExp : ∀ b ∈ Bs, b ^ p = 1 := hconf.2.1.2.1.2
  have hBBs : B ≤ Bs := hconf.2.1.1
  obtain ⟨Q, _, _, f, hD⟩ := exists_quotient_datum hp hodd hBsN hBsExp
  have hperfX : Group.IsPerfect ↥X := ⟨hperf⟩
  obtain ⟨η, hη⟩ := hD.exists_eta θ
  have hmax : ∀ l : ↥X, l ∈ Subgroup.center ↥X → (∃ k : ℕ, l ^ (2 ^ k) = 1) →
      (l : G) ∈ twoCentral X := fun l hc hk => mem_twoCentral_of_center hc hk
  have hηsurj := hD.eta_surjective hη
  have hηker := hD.eta_ker_le_center hη
  have hηcop := hD.eta_ker_coprime_four hη hmax
  have : Group.IsPerfect ↥(NsQuot.img _ f X) := Group.IsPerfect.ofSurjective hD.fL_surjective
  obtain ⟨ψ, hψsurj, hψη⟩ := exists_cover_u2 hK hn η hηsurj inferInstance hηker hηcop
  let ee : Su K 2 1 n ≃* ↥(LargeEvenSUGroup (Fin n) K (2 ^ 1)) :=
    MulEquiv.subgroupCongr (su_eq_largeEven hK)
  let ψ₀ : Su K 2 1 n →* ↥(NsQuot.img _ f X) := ψ.comp ee.toMonoidHom
  have hψ₀surj : Function.Surjective ψ₀ := hψsurj.comp ee.surjective
  have hψ₀η : ∀ s, η (ψ₀ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK) s) := fun s => hψη (ee s)
  have hψ₀ker : ψ₀.ker ≤ Subgroup.center (Su K 2 1 n) := by
    intro s hs
    have h1 : η (ψ₀ s) = 1 := by rw [MonoidHom.mem_ker.1 hs, map_one]
    rw [hψ₀η s] at h1
    have hz : (ee s) ∈ (LargeEvenScalars (Fin n) K).subgroupOf
        (LargeEvenSUGroup (Fin n) K (2 ^ 1)) := (QuotientGroup.eq_one_iff _).1 h1
    have hz' : ((ee s : ↥(LargeEvenSUGroup (Fin n) K (2 ^ 1))) : GL (Fin n) K) ∈
        Subgroup.center (GL (Fin n) K) := by
      have h3 := Subgroup.mem_subgroupOf.1 hz
      rwa [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hz' (y : GL (Fin n) K)
  have hacts : GGActsUnitarily (p := 2) (f := 1) ((NsQuot.img _ f X).subtype.comp ψ₀)
      (NsQuot.img _ f Bs) := by
    intro bq hbq
    obtain ⟨bn, hbnB, rfl⟩ := NsQuot.mem_img.1 hbq
    obtain ⟨φ, hφI, hInd⟩ := hbs (bn : G) hbnB
    have hnorm := hD.f_mem_normalizer_img hBsN hbnB
    have hbY : ∀ y ∈ NsQuot.img _ f X, f bn * y * (f bn)⁻¹ ∈ NsQuot.img _ f X := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 hnorm y).1 hy
    exact ggNSq2_acts_quot hK (by omega) η hηker ψ₀ hψ₀η hbY hφI
      (hD.eta_induces hη hBsN hbnB hInd)
  have hlocal := NsQuot.ggNSLocalHyp_of_quot hcfg hD hperfX hcentX hK
    (by omega) (by omega) hdvd hψ₀ker hψ₀surj hacts
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds hlocal
  have h' := hlocal.comp_conj c
  have hrange : (((NsQuot.img _ f X).subtype.comp ψ₀).comp (MulAut.conj c).toMonoidHom).range =
      NsQuot.img _ f X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ₀surj, Subgroup.map_top,
      Subgroup.range_subtype]
  exact ⟨Q, inferInstance, inferInstance, f,
    ((NsQuot.img _ f X).subtype.comp ψ₀).comp (MulAut.conj c).toMonoidHom, hD, hrange, h', hc⟩

theorem ggNsq2Nbr_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G}
    {X : Subgroup G} (hnbr : GGNbr p B x D J y X) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hdvd : p ∣ 2 ^ 1 + 1) {n : ℕ} (hn : n = 4 ∨ n = 6)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ 1)))
    (hperf : commutator ↥X = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1))) (LargeEvenGUSet (Fin n) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
      (f : ↥(Subgroup.normalizer (X : Set G)) →* Q) (ψ : Su K 2 1 n →* Q),
      NsQuot.Datum p (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X) ∧
      ψ.ker ≤ Subgroup.center (Su K 2 1 n) ∧
      ψ.range = NsQuot.img (Subgroup.normalizer (X : Set G)) f X ∧
      ∀ (b : G) (hb : b ∈ Bs), ∃ g : GL (Fin n) K, ggIsDiagMat g ∧
        GGInducesUnitary (p := 2) (f := 1) ψ (f ⟨b, hBsN hb⟩) g := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  obtain ⟨Q, _, _, f, ψ, hD, hrange, h', hc⟩ := ggNsq2Member_frame hcfg
    (ggNSPosPD_routeCfg_cent_K hp hnbr) hK hdvd hn θ hperf hBsN hbs
  refine ⟨Q, inferInstance, inferInstance, f, ψ, hD, h'.ker, hrange, fun b hb => ?_⟩
  obtain ⟨g, hgd, hgi⟩ := hc (f ⟨b, hBsN hb⟩) (NsQuot.mem_img.2 ⟨⟨b, hBsN hb⟩, hb, rfl⟩)
  exact ⟨g, hgd, hgi⟩

end CFSG.StandardType

end
