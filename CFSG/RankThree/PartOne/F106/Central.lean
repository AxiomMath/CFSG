module

public import CFSG.RankThree.PartOne.F106.Defs
public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.F106.Large
import CFSG.RankThree.PartOne.F106.Shape
import CFSG.RankThree.PartOne.F106.Transport
import CFSG.RankThree.PartOne.F106.ZeroStar
import CFSG.RankThree.PartOne.K156.Full
import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingPrimeCut
public import CFSG.RankThree.PartOne.N143.SectionGroup

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.N143 (SectionListBound)
open scoped commutatorElement

theorem central_false (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (hCVD : CoreVanishingDichotomy) (hI : InSec10Seven) (hSLB : SectionListBound)
    (hRank : EvenLieFiveRank) (hQD : EvenLieNoQD32) {G : Type} [Group G] [Finite G]
    {A L : Subgroup G} {c : G} {q : ℕ} {D R : Subgroup G} {e : G} {K : Subgroup G}
    (hsucc : FiveSuccessorData A L c q D R e K)
    (hcent : ⁅thetaQuotientCentralizer 5 A L, D⁆ = ⊥) : False := by
  have hcrit := hsucc.critical
  have h := hcrit.setup
  have hp : Nat.Prime 5 := by norm_num
  have hq := hcrit.q_prime
  have hq2 := hcrit.q_ne_two
  have hq5 := hcrit.q_ne_five
  obtain ⟨-, -, -, -, -, -, hAe, hAcard, -, -⟩ := id h
  have hAL := hcrit.A_normalizes
  have hLD : L ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf Subgroup.le_normalizer hcrit.D_le_L hcrit.D_char
  have hAD : A ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf hAL hcrit.D_le_L hcrit.D_char
  have hRAD : R ⊔ A ≤ normalizer (D : Set G) := sup_le (hcrit.R_le_L.trans hLD) hAD
  have hEA : thetaQuotientCentralizer 5 A L ≤ A := inf_le_left
  have hBA : A ⊓ centralizer (R : Set G) ≤ A := inf_le_left
  have hrel : (A ⊓ centralizer (R : Set G)).relIndex A = 5 := by
    rw [hcrit.kernel_R]
    have h1 := Subgroup.relIndex_mul_card (thetaQuotientCentralizer 5 A L) A
    rw [inf_eq_left.mpr hEA, hcrit.E_card, hAcard] at h1
    have h3 : (thetaQuotientCentralizer 5 A L).relIndex A * 25 = 125 := by simpa using h1
    omega
  obtain ⟨a, b₀, -, -, -, -, hA₀A, hA₀elem, hA₀card, hfac, -⟩ :=
    exists_plane_of_index_prime_subgroup hp hAe hAcard hBA hrel
  have hset : MinTwoActionSetting 5 q (zpowers a ⊔ zpowers b₀) D R :=
    minTwoActionSetting_of_plane hp hq (by norm_num) hq2 hq5 hA₀elem hA₀card hA₀A hfac hRAD
      hcrit.D_exponent hcrit.D_class hcrit.R_two hcrit.R_invariant hcrit.R_comm hcrit.R_ne_bot
      hcrit.R_acts hcrit.relative_minimal
  have hE : e ∈ thetaQuotientCentralizer 5 A L := hsucc.e_mem
  have hDfix : D ≤ L ⊓ centralizer ({e} : Set G) := fun d hdD => by
    refine ⟨hcrit.D_le_L hdD, ?_⟩
    have heD : e ∈ centralizer (D : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcent hE
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp heD d hdD)
  have hPnorm : ∀ g ∈ L ⊓ centralizer ({e} : Set G), ∀ x ∈ fiveResidual L e,
      g * x * g⁻¹ ∈ fiveResidual L e := by
    intro g hg x hx
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹,
      (inferInstance : (perfectResidual ↥(L ⊓ centralizer ({e} : Set G))).Normal).conj_mem x' hx'
        ⟨g, hg⟩, ?_⟩
    simp
  have hDRP : ⁅D, R⁆ ≤ fiveResidual L e := by
    refine Subgroup.commutator_le.mpr fun d hdD r hr => ?_
    rw [commutatorElement_def]
    exact (fiveResidual L e).mul_mem (hPnorm d (hDfix hdD) r (hsucc.R_le_P hr))
      ((fiveResidual L e).inv_mem (hsucc.R_le_P hr))
  have hPK : fiveResidual L e ≤ K := hsucc.P_le.trans inf_le_right
  obtain ⟨K', hK', hKK'⟩ := exists_zeroStar_above_of_zero hS h hsucc.K_mem.1
  have hKleK' : K ≤ K' := K156.le_of_sectionTenRel_of_quasisimple hp hsucc.K_quasisimple hKK'
  have hRK' : R ≤ K' := (hsucc.R_le_P.trans hPK).trans hKleK'
  have hDRK' : ⁅D, R⁆ ≤ K' := (hDRP.trans hPK).trans hKleK'
  obtain ⟨Xg, _, _, φ, hφs, hφk, hXs, hXn, hXlie, hXlist⟩ :=
    zeroStar_simple_quotient hS hTwo hI hSLB h hK'
  rcases five_shape hTwo hset hcrit.fixed_rank with
    ⟨-, -, hDe, hDcard, hDR, hDC, r, -, hr2, hr3⟩ |
      ⟨Y, hYD, hRY, hYR, hA₀Y, ⟨a₁, ha₁, r₁, hr₁, hnt⟩, ψ, hψs, hψk⟩
  ·
    have hDK' : D ≤ K' := by
      rw [← hDR]
      exact hDRK'
    by_cases hq7 : 7 < q
    · exact false_of_large_prime hCVD h (by norm_num) hq hq7 (by norm_num) hDe hDcard hr2 hr3
    · have hq37 : q = 3 ∨ q = 7 := by
        have h2 := hq.two_le
        have : q ≤ 7 := by omega
        interval_cases q <;> first | omega | (exfalso; norm_num at hq)
      have : Fact q.Prime := ⟨hq⟩
      have hDe' : CFSG.IsElementaryAbelian q ↥(D.subgroupOf K') := by
        have := hDe
        exact IsElementaryAbelian.subgroupOf hDK'
      have hDcard' : Nat.card ↥(D.subgroupOf K') = q ^ 5 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK').toEquiv]
        exact hDcard
      have hdis : Disjoint (D.subgroupOf K') φ.ker := by
        rw [Subgroup.disjoint_def]
        intro x hxD hxk
        have hxc := hφk hxk
        have hxC : (x : G) ∈ centralizer (R : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro r hr
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨r, hRK' hr⟩)
        have h1 : (x : G) ∈ D ⊓ centralizer (R : Set G) := ⟨hxD, hxC⟩
        rw [hDC, Subgroup.mem_bot] at h1
        exact Subtype.ext h1
      have hD'e : CFSG.IsElementaryAbelian q ↥((D.subgroupOf K').map φ) := by
        have := hDe'
        exact IsElementaryAbelian.map φ
      have hD'card : Nat.card ↥((D.subgroupOf K').map φ) = q ^ 5 := by
        rw [N143.card_map_of_disjoint_ker φ hdis]
        exact hDcard'
      exact hRank Xg hXs hXn hXlie hXlist q hq37 _ hD'e hD'card
  ·
    have hYK' : Y ≤ K' := by
      rw [← hYR]
      exact (Subgroup.commutator_mono hYD le_rfl).trans hDRK'
    have hYexp : ∀ y ∈ Y, y ^ q = 1 := fun y hy => hcrit.D_exponent y (hYD hy)
    have hYcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1 := by
      intro a ha b hb c hc
      have h1 : ⁅⁅a, b⁆, c⁆ ∈ ⁅⁅D, D⁆, D⁆ :=
        Subgroup.commutator_mem_commutator
          (Subgroup.commutator_mem_commutator (hYD ha) (hYD hb)) (hYD hc)
      rw [hcrit.D_class, Subgroup.mem_bot] at h1
      exact h1
    have hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : G) ∈ centralizer (Y : Set G) := by
      intro r
      rw [← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hr => hr.2, fun hr => ⟨r.2, hr⟩⟩
    obtain ⟨ψ', hψ's, hψ'c⟩ :=
      exists_hom_img φ hq hq2 hYK' hRK' hYexp hcrit.R_two hRY hφk ψ hψs hψc
    have : CFSG.IsElementaryAbelian 5 A := hAe
    have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hAe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hKne : K ≠ ⊥ := by
      intro hbot
      obtain ⟨x, y, hxy⟩ := hsucc.K_quasisimple.2.2
      obtain ⟨kx, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨ky, rfl⟩ := QuotientGroup.mk_surjective y
      have h1 : kx = 1 := Subtype.ext (by simpa [hbot] using kx.2)
      have h2 : ky = 1 := Subtype.ext (by simpa [hbot] using ky.2)
      exact hxy (by rw [h1, h2])
    have hAK' : A ≤ normalizer (K' : Set G) :=
      le_normalizer_of_perfect_le hp hAc ((sectionTenZeroStar_subset 5 A).2.2.1 hK'.2) hKne
        hsucc.K_quasisimple.1 hKleK' hsucc.A_normalizes_K
    have hker : φ.ker = center ↥K' := by
      refine le_antisymm hφk ?_
      have hn : ((center ↥K').map φ).Normal := Subgroup.Normal.map inferInstance φ hφs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((center ↥K').map φ) with h0 | h0
      · intro x hx
        have h1 : φ x ∈ (center ↥K').map φ := Subgroup.mem_map_of_mem φ hx
        rw [h0, Subgroup.mem_bot] at h1
        exact h1
      · exfalso
        obtain ⟨u, v, huv⟩ := hXn
        have hu : u ∈ (center ↥K').map φ := h0 ▸ Subgroup.mem_top u
        obtain ⟨cu, hcu, rfl⟩ := hu
        obtain ⟨kv, rfl⟩ := hφs v
        exact huv (by rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcu kv])
    have ha₁A : a₁ ∈ A := hA₀A ha₁
    have ha₁K' : a₁ ∈ normalizer (K' : Set G) := hAK' ha₁A
    obtain ⟨α, hα⟩ := exists_aut_conj φ hφs hker ha₁K'
    have hα5 : α ^ 5 = 1 :=
      aut_conj_pow_eq_one φ hφs ha₁K' hα (elemPow_eq_one_of_isElementaryAbelian (p := 5) a₁ ha₁A)
    have hR₁ : a₁ ∈ normalizer (R : Set G) := hset.R_inv ha₁
    have hr₁K : r₁ ∈ K' := hRK' hr₁
    have hr₁' : φ ⟨r₁, hr₁K⟩ ∈ img φ R := mem_img_of_mem φ hr₁K hr₁
    have hmem : a₁ * r₁ * a₁⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hR₁ r₁).mp hr₁
    have hs : a₁ * r₁ * a₁⁻¹ * r₁⁻¹ ∈ R := R.mul_mem hmem (R.inv_mem hr₁)
    have hmemK : a₁ * r₁ * a₁⁻¹ ∈ K' := hRK' hmem
    have hsK : a₁ * r₁ * a₁⁻¹ * r₁⁻¹ ∈ K' := hRK' hs
    have hαr : α (φ ⟨r₁, hr₁K⟩) = φ ⟨a₁ * r₁ * a₁⁻¹, hmemK⟩ := hα _ _ rfl
    have hsub : (⟨a₁ * r₁ * a₁⁻¹ * r₁⁻¹, hsK⟩ : ↥K') =
        ⟨a₁ * r₁ * a₁⁻¹, hmemK⟩ * ⟨r₁, hr₁K⟩⁻¹ := Subtype.ext rfl
    have hnt' : α (φ ⟨r₁, hr₁K⟩) * (φ ⟨r₁, hr₁K⟩)⁻¹ ∉
        centralizer ((img φ Y : Subgroup Xg) : Set Xg) := by
      intro hc
      rw [hαr, ← map_inv, ← map_mul, ← hsub] at hc
      exact hnt (centralizes_of_img φ hq hq2 hYK' hRK' hYexp hcrit.R_two hRY hφk hs hc)
    exact hQD Xg hXs hXn hXlie hXlist q hq hq2 hq5 α hα5 (img φ Y) (img φ R) (img_exp φ hYexp)
      (img_class φ hYcl) (img_isPGroup φ hcrit.R_two) (img_le_normalizer φ hRY)
      (fun y hy => aut_conj_mem_img φ ha₁K' hα (hA₀Y ha₁) hy)
      (fun r hr => aut_conj_mem_img φ ha₁K' hα hR₁ hr) ⟨_, hr₁', hnt'⟩ ψ' hψ's hψ'c

end CFSG.RankThree.PartOne.F106
