module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSQ2CellsDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotCover
import CFSG.LocalAnalysis.StandardType.GGNsq2Hopf
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotActs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlock
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransport
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.CoprimeKernel CFSG.Blueprint
  CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

open NsQuot

private theorem ggNsq2Cover_ker_qps {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {Y : Type} [Group Y]
    {η : Y →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {ψ₀ : Su K 2 1 6 →* Y}
    (hψ₀η : ∀ s, η (ψ₀ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK) s)) :
    ψ₀.ker ≤ Subgroup.center (Su K 2 1 6) := by
  intro s hs
  have h1 : η (ψ₀ s) = 1 := by rw [MonoidHom.mem_ker.1 hs, map_one]
  rw [hψ₀η s] at h1
  have hz : (MulEquiv.subgroupCongr (su_eq_largeEven hK) s) ∈
      (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    (QuotientGroup.eq_one_iff _).1 h1
  have hz' : ((MulEquiv.subgroupCongr (su_eq_largeEven hK) s :
      ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) ∈
      Subgroup.center (GL (Fin 6) K) := by
    have h3 := Subgroup.mem_subgroupOf.1 hz
    rwa [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.1 hz' (y : GL (Fin 6) K)

private theorem ggNsq2Marking_qps {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {X : Subgroup G}
    (h5 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      commutator ↥X = ⊤ ∧ Nat.card K = (2 ^ 1) ^ 2 ∧ p ∣ 2 ^ 1 + 1 ∧
      Bs ≤ Subgroup.normalizer (X : Set G) ∧
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hf, hfin, lab, m, θ, hK, h4m, hmrank, hlab, hdvd, hperf, hlab2, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore h5 (fun p lab hl => hl.1)
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hrow, hn1, hr5⟩ := hlab
  change n = 1 at hn1
  change rank = 5 at hr5
  change m = rank + 1 at hmrank
  subst hn1
  subst hr5
  have hm6 : m = 6 := by omega
  subst hm6
  have hchar : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hK
  exact ⟨K, hf, hfin, hchar, θ, hperf, hK, hdvd, hBsN, hbs⟩

private theorem ggNsq2QuotDatum_qps
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hcentX : Nat.card ↥(B ⊓ Subgroup.centralizer (X : Set G)) = p)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hdvd : p ∣ 2 ^ 1 + 1)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥X = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : ↥(Subgroup.normalizer (X : Set G)) →* Q)
      (ψ₀ : Su K 2 1 6 →* ↥(img _ f X)),
      Datum p (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X) ∧
      Function.Surjective ψ₀ ∧
      GGNSLocalHyp p (img _ f B) (img _ f Bs) K 1 6 ((img _ f X).subtype.comp ψ₀) := by
  classical
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hBsExp : ∀ b ∈ Bs, b ^ p = 1 := hcfg.1.1.2.1.2.1.2
  obtain ⟨Q, _, _, f, hD⟩ := exists_quotient_datum hp hodd hBsN hBsExp
  obtain ⟨η, hη⟩ := hD.exists_eta θ
  have hηsurj := hD.eta_surjective hη
  have hηker := hD.eta_ker_le_center hη
  have hηcop := hD.eta_ker_coprime_four hη (fun l hc hk => mem_twoCentral_of_center hc hk)
  have : Group.IsPerfect ↥X := ⟨hperf⟩
  have : Group.IsPerfect ↥(img _ f X) := Group.IsPerfect.ofSurjective hD.fL_surjective
  obtain ⟨ψ, hψsurj, hψη⟩ := exists_cover_u62 hK η hηsurj inferInstance hηker hηcop
  let ee : Su K 2 1 6 ≃* ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    MulEquiv.subgroupCongr (su_eq_largeEven hK)
  let ψ₀ : Su K 2 1 6 →* ↥(img _ f X) := ψ.comp ee.toMonoidHom
  have hψ₀surj : Function.Surjective ψ₀ := hψsurj.comp ee.surjective
  have hψ₀η : ∀ s, η (ψ₀ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK) s) := fun s => hψη (ee s)
  have hψ₀ker : ψ₀.ker ≤ Subgroup.center (Su K 2 1 6) := ggNsq2Cover_ker_qps hK hψ₀η
  have hacts : GGActsUnitarily (p := 2) (f := 1) ((img _ f X).subtype.comp ψ₀) (img _ f Bs) := by
    intro bq hbq
    obtain ⟨bn, hbnB, rfl⟩ := mem_img.1 hbq
    obtain ⟨φ, hφI, hInd⟩ := hbs (bn : G) hbnB
    have hnorm := hD.f_mem_normalizer_img hBsN hbnB
    have hbY : ∀ y ∈ img _ f X, f bn * y * (f bn)⁻¹ ∈ img _ f X := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 hnorm y).1 hy
    exact ggNSq2_acts_quot hK (by norm_num) η hηker ψ₀ hψ₀η hbY hφI
      (hD.eta_induces hη hBsN hbnB hInd)
  refine ⟨Q, inferInstance, inferInstance, f, ψ₀, hD, hψ₀surj, ?_⟩
  exact NsQuot.ggNSLocalHyp_of_quot hcfg hD ⟨hperf⟩ hcentX hK (by norm_num) (by norm_num) hdvd
    hψ₀ker hψ₀surj hacts

private theorem ggNsq2PosPackage_qps {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {X N : Subgroup G} {Q : Type} [Group Q] [Finite Q] {f : ↥N →* Q}
    {K : Type} [Field K] [Finite K] [CharP K 2] {ψ₀ : Su K 2 1 6 →* ↥(img N f X)}
    (hlocal : GGNSLocalHyp p (img N f B) (img N f Bs) K 1 6 ((img N f X).subtype.comp ψ₀))
    (hψ₀surj : Function.Surjective ψ₀) :
    ∃ (ψ : Su K 2 1 6 →* Q),
      GGNSLocalHyp p (img N f B) (img N f Bs) K 1 6 ψ ∧ ψ.range = img N f X ∧
      GGActsDiagonally (p := 2) (f := 1) ψ (img N f Bs) ∧
      ∃ ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (img N f X) (img N f Bs)),
        (∀ (σ : Equiv.Perm (Fin 6)) (s : ↥(img N f Bs)),
          ((((ε σ : ↥(ggAutomizer (img N f X) (img N f Bs))) : MulAut ↥(img N f Bs)) s :
            ↥(img N f Bs)) : Q) = ψ (ggPermSU σ⁻¹) * (s : Q) * (ψ (ggPermSU σ⁻¹))⁻¹) ∧
        (∀ a b : Fin 6, a ≠ b → GGIsReflection p
          ((ε (Equiv.swap a b) : ↥(ggAutomizer (img N f X) (img N f Bs))) :
            MulAut ↥(img N f Bs))) ∧
        ∀ a b : Fin 6, a ≠ b →
          ggRankOneIn (img N f X) (img N f Bs)
            ((ε (Equiv.swap a b) : ↥(ggAutomizer (img N f X) (img N f Bs))) :
              MulAut ↥(img N f Bs)) = (ggSuPairBlock K 2 1 6 a b).map ψ := by
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds hlocal
  let ψ : Su K 2 1 6 →* Q := ((img N f X).subtype.comp ψ₀).comp (MulAut.conj c).toMonoidHom
  have h' : GGNSLocalHyp p (img N f B) (img N f Bs) K 1 6 ψ := hlocal.comp_conj c
  have hrange : ψ.range = img N f X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ₀surj,
      Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨ψ, h', hrange, hc, ?_⟩
  rw [← hrange]
  obtain ⟨ε, hε, hrefl⟩ := ggNSDiag_automizer_perm h' hc
  exact ⟨ε, hε, hrefl, fun a b hab =>
    ggNSDiag_rankOne_block h' hc a b hab _ (fun s => by
      have := hε (Equiv.swap a b) s
      rwa [Equiv.swap_inv] at this)⟩

theorem ggNsq2Member_quotient_position
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hcentX : Nat.card ↥(B ⊓ Subgroup.centralizer (X : Set G)) = p)
    (h5 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X) :
    p = 3 ∧ Group.IsPerfect ↥X ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (Q : Type) (_ : Group Q)
        (_ : Finite Q) (f : ↥(Subgroup.normalizer (X : Set G)) →* Q) (ψ : Su K 2 1 6 →* Q),
        Datum p (Subgroup.normalizer (X : Set G)) f X Bs (twoCentral X) ∧ Nat.card K = 4 ∧
        GGNSLocalHyp p (img _ f B) (img _ f Bs) K 1 6 ψ ∧ ψ.range = img _ f X ∧
        GGActsDiagonally (p := 2) (f := 1) ψ (img _ f Bs) ∧
        ∃ ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (img _ f X) (img _ f Bs)),
          (∀ (σ : Equiv.Perm (Fin 6)) (s : ↥(img _ f Bs)),
            ((((ε σ : ↥(ggAutomizer (img _ f X) (img _ f Bs))) : MulAut ↥(img _ f Bs)) s :
              ↥(img _ f Bs)) : Q) = ψ (ggPermSU σ⁻¹) * (s : Q) * (ψ (ggPermSU σ⁻¹))⁻¹) ∧
          (∀ a b : Fin 6, a ≠ b → GGIsReflection p
            ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) :
              MulAut ↥(img _ f Bs))) ∧
          ∀ a b : Fin 6, a ≠ b →
            ggRankOneIn (img _ f X) (img _ f Bs)
              ((ε (Equiv.swap a b) : ↥(ggAutomizer (img _ f X) (img _ f Bs))) :
                MulAut ↥(img _ f Bs)) = (ggSuPairBlock K 2 1 6 a b).map ψ := by
  classical
  obtain ⟨K, hKf, hKfin, hKchar, θ, hperf, hK, hdvd, hBsN, hbs⟩ := ggNsq2Marking_qps h5
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (ggRouteCfg_prime hcfg).1 Nat.prime_three).1
    (by simpa using hdvd)
  obtain ⟨Q, hQ, hQfin, f, ψ₀, hD, hψ₀surj, hlocal⟩ :=
    ggNsq2QuotDatum_qps hcfg hcentX hK hdvd θ hperf hBsN hbs
  obtain ⟨ψ, h', hrange, hc, hε⟩ := ggNsq2PosPackage_qps hlocal hψ₀surj
  exact ⟨hp3, ⟨hperf⟩, hBsN, K, hKf, hKfin, hKchar, Q, hQ, hQfin, f, ψ,
    hD, hK4, h', hrange, hc, hε⟩

end CFSG.StandardType

end
