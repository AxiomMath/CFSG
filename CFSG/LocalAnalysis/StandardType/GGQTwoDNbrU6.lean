module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrUnit
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
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Steinberg Matrix

variable {G : Type} [Group G] [Finite G]

section


theorem qtwoDNbr_u6_toral {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G}
    {X : Subgroup G} (hnbr : GGNbr 3 B x D J y X) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥X = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card ↥Bs ≤ 3 ^ 5 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hBsExp : ∀ b ∈ Bs, b ^ 3 = 1 := hconf.2.1.2.1.2
  have hBBs : B ≤ Bs := hconf.2.1.1
  obtain ⟨Q, _, _, f, hD⟩ := exists_quotient_datum hp hodd hBsN hBsExp
  have hperfX : Group.IsPerfect ↥X := ⟨hperf⟩
  obtain ⟨η, hη⟩ := hD.exists_eta θ
  have hmax : ∀ l : ↥X, l ∈ Subgroup.center ↥X → (∃ k : ℕ, l ^ (2 ^ k) = 1) →
      (l : G) ∈ twoCentral X := fun l hc hk => mem_twoCentral_of_center hc hk
  have hηsurj := hD.eta_surjective hη
  have hηker := hD.eta_ker_le_center hη
  have hηcop := hD.eta_ker_coprime_four hη hmax
  haveI : Group.IsPerfect ↥(NsQuot.img _ f X) := Group.IsPerfect.ofSurjective hD.fL_surjective
  obtain ⟨ψ, hψsurj, hψη⟩ := exists_cover_u2 hK (Or.inr rfl) η hηsurj inferInstance hηker hηcop
  let ee : Su K 2 1 6 ≃* ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    MulEquiv.subgroupCongr (su_eq_largeEven hK)
  let ψ₀ : Su K 2 1 6 →* ↥(NsQuot.img _ f X) := ψ.comp ee.toMonoidHom
  have hψ₀surj : Function.Surjective ψ₀ := hψsurj.comp ee.surjective
  have hψ₀η : ∀ s, η (ψ₀ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK) s) := fun s => hψη (ee s)
  have hψ₀ker : ψ₀.ker ≤ Subgroup.center (Su K 2 1 6) := by
    intro s hs
    have h1 : η (ψ₀ s) = 1 := by rw [MonoidHom.mem_ker.1 hs, map_one]
    rw [hψ₀η s] at h1
    have hz : (ee s) ∈ (LargeEvenScalars (Fin 6) K).subgroupOf
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := (QuotientGroup.eq_one_iff _).1 h1
    have hz' : ((ee s : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) ∈
        Subgroup.center (GL (Fin 6) K) := by
      have h3 := Subgroup.mem_subgroupOf.1 hz
      rwa [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hz' (y : GL (Fin 6) K)
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
  have hlocal := NsQuot.ggNSLocalHyp_of_quot hcfg hD hperfX (ggNSPosPD_routeCfg_cent_K hp hnbr)
    hK (by omega) (by omega) (by norm_num) hψ₀ker hψ₀surj hacts
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds hlocal
  have h' := hlocal.comp_conj c
  have hrange : (((NsQuot.img _ f X).subtype.comp ψ₀).comp (MulAut.conj c).toMonoidHom).range =
      NsQuot.img _ f X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ₀surj,
      Subgroup.map_top, Subgroup.range_subtype]
  have htor := ggNSDiag_toral_bound h' hc
  rw [hrange, hD.card_img le_rfl, hD.cent hperfX le_rfl] at htor
  exact htor

theorem qtwoDNbr_u6_cover {Bs X : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥X = ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥X)))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ∃ ψ : Su K 2 1 6 →* G, ψ.ker ≤ Subgroup.center (Su K 2 1 6) ∧ ψ.range = X ∧
      GGActsUnitarily (p := 2) (f := 1) ψ Bs := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hperfX : Group.IsPerfect ↥X := ⟨hperf⟩
  let η : ↥X →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hηsurj : Function.Surjective η := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηkereq : η.ker = Subgroup.center ↥X := by
    ext z
    rw [MonoidHom.mem_ker]
    change θ (QuotientGroup.mk z) = 1 ↔ z ∈ Subgroup.center ↥X
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hηker : η.ker ≤ Subgroup.center ↥X := hηkereq.le
  have hηcop : Nat.Coprime (Nat.card η.ker) 4 := by
    rw [hηkereq]
    have h2 : Nat.Coprime (Nat.card (Subgroup.center ↥X)) 2 := hodd.coprime_two_right
    simpa using h2.pow_right 2
  obtain ⟨ψ, hψsurj, hψη⟩ := exists_cover_u2 hK (Or.inr rfl) η hηsurj hperfX hηker hηcop
  let ee : Su K 2 1 6 ≃* ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    MulEquiv.subgroupCongr (su_eq_largeEven hK)
  let ψ₀ : Su K 2 1 6 →* ↥X := ψ.comp ee.toMonoidHom
  have hψ₀surj : Function.Surjective ψ₀ := hψsurj.comp ee.surjective
  have hψ₀η : ∀ s, η (ψ₀ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK) s) := fun s => hψη (ee s)
  have hψ₀ker : ψ₀.ker ≤ Subgroup.center (Su K 2 1 6) := by
    intro s hs
    have h1 : η (ψ₀ s) = 1 := by rw [MonoidHom.mem_ker.1 hs, map_one]
    rw [hψ₀η s] at h1
    have hz : (ee s) ∈ (LargeEvenScalars (Fin 6) K).subgroupOf
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := (QuotientGroup.eq_one_iff _).1 h1
    have hz' : ((ee s : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) ∈
        Subgroup.center (GL (Fin 6) K) := by
      have h3 := Subgroup.mem_subgroupOf.1 hz
      rwa [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hz' (y : GL (Fin 6) K)
  refine ⟨X.subtype.comp ψ₀, ?_, ?_, ?_⟩
  · intro s hs
    apply hψ₀ker
    rw [MonoidHom.mem_ker] at hs ⊢
    exact Subtype.ext hs
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ₀surj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro b hb
    obtain ⟨φ, hφI, hInd⟩ := hbs b hb
    have hbY : ∀ y ∈ X, b * y * b⁻¹ ∈ X := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 (hBsN hb) y).1 hy
    exact ggNSq2_acts_quot hK (by omega) η hηker ψ₀ hψ₀η hbY hφI hInd


theorem qtwoDNbr_u6 (hC : GGSecFiveNSCornerInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) {m : ℕ} (hm : 7 ≤ m) (hcard : Nat.card ↥Bs = 3 ^ m)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 ^ 2)
    (hFix : QTwoDFixBound Bs X m)
    (hmark : GGInnerDiagOnLabel (fun p lab =>
      ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X) :
    QTwoDL1Chart 3 B Bs X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨K, hKf, hKfin, lab, m', θ, hK, -, hmrank, hSide, -, hperf, -, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  haveI : CharP K 2 := charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn, hr5⟩ := hSide
  change n = 1 at hn
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK
  have htor := qtwoDNbr_u6_toral hcfg hnbr hK' θ hperf hBsN hbs
  have h9 : 9 ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    have h7 : 3 ^ 7 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hcard] at htor
    have h57 : 3 ^ 5 * 9 ≤ 3 ^ 5 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
      calc 3 ^ 5 * 9 = 3 ^ 7 := by norm_num
        _ ≤ 3 ^ m := h7
        _ ≤ _ := htor
    exact Nat.le_of_mul_le_mul_left h57 (by norm_num)
  have hBBs : B ≤ Bs := hconf.2.1.1
  have hlt : B < Bs := by
    refine lt_of_le_of_ne hBBs fun hBeq => ?_
    have h3 := ggNSPosPD_routeCfg_cent_K (ggRouteCfg_prime hcfg).1 hnbr
    rw [hBeq] at h3
    omega
  have hodd := hconf.odd_card_center_of_B_lt_Bs hlt hBsN
  obtain ⟨ψ, hker, hrange, hacts⟩ := qtwoDNbr_u6_cover hK' θ hperf hodd hbs hBsN
  exact qtwoDNbr_unit_of_cover hC hcfg hnbr hcard hFix hK' (by norm_num) hker hrange
    (by norm_num) hacts

end

end CFSG.StandardType.QTwo

end
