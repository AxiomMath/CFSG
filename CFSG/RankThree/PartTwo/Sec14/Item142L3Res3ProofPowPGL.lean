module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofPowCore
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofPowAut
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypes

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup)
open scoped commutatorElement

namespace L3PGLPow

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PartTwo.Sec14.L3PGL (sigmaOf) in
theorem sigma_comm_of_pgl {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hPGLA : Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A)) (hx : ∃ x ∈ A, Sec4.InducesTypeOn L x 3) :
    ∀ r₁ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ r₂ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ (h₁ : r₁ ∈ Subgroup.normalizer (L : Set G)) (h₂ : r₂ ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L h₁ * sigmaOf L h₂ = sigmaOf L h₂ * sigmaOf L h₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨x, hxA, hx⟩ := hx
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hq2 := L3PGL.two_lt_of_model hqs hK hq e
  obtain ⟨s, hs, hsZ, hs3, hysZ, -, hσ'⟩ :=
    L3PGL.plane_model h hPGLA hxA hxN hK hq e hyH hy3 hact
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hconj : ∀ (g : GL (Fin 3) K) (hg : g ∈ glPi π 3 (p ^ f) K) (i j : ℤ),
      ProjGenLinGroup.mk g = ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j →
      ∃ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        MulAut.congr e (sigmaOf L haN) = Res8Hess.conjM' hπ hg := by
    intro g hg i j hgij
    obtain ⟨a, haA, haN, hz⟩ := hσ' i j
    refine ⟨a, haA, haN, ?_⟩
    ext m
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, Res8Hess.coe_conjM',
      hz, hgij, MulEquiv.apply_symm_apply]
  obtain ⟨a₁, ha₁A, ha₁N, h₁⟩ := hconj s hsH 1 0 (by simp)
  obtain ⟨a₂, ha₂A, ha₂N, h₂⟩ := hconj y hyH 0 1 (by simp)
  have hcommA : ∀ (r : G) (_ : r ∈ Subgroup.centralizer (A : Set G))
      (hrN : r ∈ Subgroup.normalizer (L : Set G)) (a : G) (_ : a ∈ A)
      (haN : a ∈ Subgroup.normalizer (L : Set G)),
      Commute (MulAut.congr e (sigmaOf L hrN)) (MulAut.congr e (sigmaOf L haN)) := by
    intro r hrA hrN a haA haN
    have h1 : sigmaOf L hrN * sigmaOf L haN = sigmaOf L haN * sigmaOf L hrN := by
      rw [sigmaOf, sigmaOf, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 2
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hrA a haA).symm)
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, h1]
  intro r₁ hr₁ r₂ hr₂ hr₁N hr₂N
  have hr₁A : r₁ ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr₁
  have hr₂A : r₂ ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr₂
  have h1s := hcommA r₁ hr₁A hr₁N a₁ ha₁A ha₁N
  have h1y := hcommA r₁ hr₁A hr₁N a₂ ha₂A ha₂N
  have h2s := hcommA r₂ hr₂A hr₂N a₁ ha₁A ha₁N
  have h2y := hcommA r₂ hr₂A hr₂N a₂ ha₂A ha₂N
  rw [h₁] at h1s h2s
  rw [h₂] at h1y h2y
  have hcR : ⁅r₁, r₂⁆ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)
  have hcN : ⁅r₁, r₂⁆ ∈ Subgroup.normalizer (L : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hr₁N hr₂N) (inv_mem hr₁N)) (inv_mem hr₂N)
  set n := orderOf ⁅r₁, r₂⁆ with hn
  have hn3 : ¬ 3 ∣ n := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Subgroup.orderOf_dvd_natCard _ hcR))
  have hζ : ⁅MulAut.congr e (sigmaOf L hr₁N), MulAut.congr e (sigmaOf L hr₂N)⁆ =
      MulAut.congr e (sigmaOf L hcN) := by
    rw [sigmaOf_commutator hr₁N hr₂N hcN, map_commutatorElement]
  have hζn : ⁅MulAut.congr e (sigmaOf L hr₁N), MulAut.congr e (sigmaOf L hr₂N)⁆ ^ n = 1 := by
    rw [hζ, ← map_pow]
    have h1 : (⟨⁅r₁, r₂⁆, hcN⟩ : Subgroup.normalizer (L : Set G)) ^ n = 1 :=
      Subtype.ext (by simp [hn, pow_orderOf_eq_one])
    rw [sigmaOf, ← map_pow, ← map_pow, h1, map_one, map_one, map_one]
  have hcomm := comm_of_commute_plane hπ hK hq hq2 hyH hy3 hs hsH hsZ hs3 hysZ h1s h1y h2s h2y
    hn3 hζn
  apply (MulAut.congr e).injective
  rw [map_mul, map_mul]
  exact hcomm

end L3PGLPow

theorem step142TypesL3PGLPow_proof :
    Step142TypesL3PGLPow := by
  intro G _ _ A c L h Q hQ hK _ hPGL _ hx _ _
  have hD := h.toSec13Data
  have : (ker142 A (lB A) c).Normal := ker142_normal hD.isElemAbelian.1 hD.mem_A
  have d : L3PGLPow.Pow142 A c L :=
    ⟨h, hK, L3PGL.le_k_of_ker (step142PGLKer_of_res3 KFacts.kpSz) h hK hPGL hx⟩
  obtain ⟨hlist, -⟩ := L3PGL.list_bar h hPGL hx
  exact d.typesOne_of_list_comm hQ hlist (L3PGLPow.sigma_comm_of_pgl h hPGL hx)

theorem step142TypesL3PGL_proof :
    Step142TypesL3PGL :=
  step142TypesL3PGL_of step142TypesL3PGLPow_proof

end CFSG.RankThree.PartTwo.Sec14
