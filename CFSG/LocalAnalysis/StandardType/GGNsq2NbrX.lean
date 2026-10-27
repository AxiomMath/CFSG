module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrFrame
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrBlock
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrTransport
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotCover
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg Matrix

open scoped commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G]

theorem twoCentral_le_pPrimeCoreOf {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (X : Subgroup G) :
    twoCentral X ≤ LargeEvenPPrimeCoreOf p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Z' : Subgroup ↥X := (twoCentral X).subgroupOf X
  have hZ'n : Z'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : (n : G) ∈ twoCentral X := hn
    have h2 := twoCentral_central h1 (g : G) g.2
    show ((g * n * g⁻¹ : ↥X) : G) ∈ twoCentral X
    have h3 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [h2, mul_inv_cancel_right]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h3]
    exact h1
  have hZ'p : IsPGroup 2 ↥Z' := by
    intro z
    obtain ⟨k, hk⟩ := twoCentral_two (show ((z : ↥X) : G) ∈ twoCentral X from z.2)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hk
  have hcop : Nat.Coprime p (Nat.card ↥Z') := by
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).1 hZ'p
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hodd)
  have hle : Z' ≤ CFSG.pPrimeCore p ↥X := le_sSup ⟨hZ'n, hcop⟩
  intro z hz
  have hzX : z ∈ X := twoCentral_le X hz
  exact ⟨⟨z, hzX⟩, hle (show (⟨z, hzX⟩ : ↥X) ∈ Z' from hz), rfl⟩

end Aux

section Comm

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]

theorem NsQuot.Datum.commutator_le_of_img_centralizes {p : ℕ} {N : Subgroup G} {f : ↥N →* Q}
    {L Bs Z : Subgroup G} (hD : NsQuot.Datum p N f L Bs Z) {x : G} (hx : x ∈ N)
    (hcen : NsQuot.img N f L ≤ Subgroup.centralizer ({f ⟨x, hx⟩} : Set Q)) :
    (⁅L, Subgroup.zpowers x⁆ : Subgroup G) ≤ Z := by
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
  have hg₁N : g₁ ∈ N := hD.LN hg₁
  have hxk : x ^ k ∈ N := zpow_mem hx k
  have hfk : f ⟨x ^ k, hxk⟩ = (f ⟨x, hx⟩) ^ k := by
    rw [← map_zpow]
    rfl
  have hcom : Commute (f ⟨g₁, hg₁N⟩) (f ⟨x ^ k, hxk⟩) := by
    rw [hfk]
    refine Commute.zpow_right ?_ k
    have h := hcen (NsQuot.mem_img.2 ⟨⟨g₁, hg₁N⟩, hg₁, rfl⟩)
    exact (Subgroup.mem_centralizer_singleton_iff.1 h)
  have hcN : ⁅g₁, x ^ k⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hg₁N hxk) (N.inv_mem hg₁N)) (N.inv_mem hxk)
  have h1 : f (⟨⁅g₁, x ^ k⁆, hcN⟩ : ↥N) = 1 := by
    have : (⟨⁅g₁, x ^ k⁆, hcN⟩ : ↥N) = ⁅(⟨g₁, hg₁N⟩ : ↥N), (⟨x ^ k, hxk⟩ : ↥N)⁆ := rfl
    rw [this, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hcom.eq
  exact (hD.mem_ker_iff _).1 h1

end Comm

theorem ggNsq2Nbr_X
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G}
    {X : Subgroup G} (hnbr : GGNbr p B x D J y X) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hdvd : p ∣ 2 ^ 1 + 1) {n : ℕ} (hn : n = 4 ∨ n = 6)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ 1)))
    (hperf : commutator ↥X = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ 1))) (LargeEvenGUSet (Fin n) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G))) :
    n = 6 ∧ ∃ a : ℕ, 4 ≤ a ∧ a ≤ 5 ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* Su K 2 1 a ⧸ Subgroup.center (Su K 2 1 a)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hx : x ∈ Bs := hconf.2.1.1 (hconf.1.2.2.2.2.2.2.1).2.1
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := hBsN hx
  obtain ⟨Q, _, _, f, ψ, hD, hker, hrange, hdiag⟩ :=
    ggNsq2Nbr_frame hcfg hnbr hK hdvd hn θ hperf hBsN hbs
  obtain ⟨J', hJ', ⟨e₁⟩⟩ := hD.exists_isComponentOf_img hxN hxN hJ
  rw [← hrange] at hJ'
  obtain ⟨g, hg, hgi⟩ := hdiag x hx
  obtain ⟨a, ha2, han, ha4, haN, ⟨e₂⟩⟩ :=
    exists_isComponent_block_iso (f := 1) hK hp hdvd hker hg hgi hJ'
  have ha4' : 4 ≤ a := ha4 rfl
  have hnot : a ≠ n := by
    intro han'
    have hcen := haN han'
    rw [hrange] at hcen
    have hle := hD.commutator_le_of_img_centralizes hxN hcen
    exact hnbr.2.2.2 (hle.trans (twoCentral_le_pPrimeCoreOf hp hodd X))
  refine ⟨?_, a, ha4', ?_, ⟨e₁.symm.trans e₂⟩⟩
  · omega
  · omega

theorem not_ggInnerDiagOnLabel_unitary_four_two_of_ggNbr
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {y : G} {X : Subgroup G} (hnbr : GGNbr p B x D J y X) :
    ¬ GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) p Bs X := by
  classical
  intro hmark
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hf, hfin, lab, m, θ, hK, h4m, hmrank, hSide, hdvd, hperf, hlab, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn1, hr3⟩ := hSide
  change n = 1 at hn1
  change rank = 3 at hr3
  change m = rank + 1 at hmrank
  subst hn1
  have hm4 : m = 4 := by omega
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
  have hJX : J ≤ X := le_of_ggNbr hLB hconf.1 hconf.2.2 hpJ hnbr
  have hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hconf hnbr hJX
  obtain ⟨hm6, -⟩ :=
    ggNsq2Nbr_X hcfg hnbr hK hdvd (Or.inl hm4) θ hperf hBsN hbs hcomp
  omega

end CFSG.StandardType

end
