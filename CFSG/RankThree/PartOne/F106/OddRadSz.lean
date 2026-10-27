module

public import CFSG.RankThree.PartOne.F106.OddRadGen
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.RankThree.PartOne.F106.OddRadAt

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Ree
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

theorem eqLocus_mulAut_conj {G : Type*} [Group G] (g : G) :
    ((MulAut.conj g : MulAut G) : G →* G).eqLocus (MonoidHom.id G) = Subgroup.centralizer {g} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  show (MulAut.conj g) x = x ↔ _
  rw [MulAut.conj_apply]
  constructor
  · intro h
    exact ((mul_inv_eq_iff_eq_mul.1 h).symm)
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem mulAut_congr_conj {G : Type*} [Group G] (h : G) (β : MulAut G) :
    MulAut.congr (MulAut.conj h) β = MulAut.conj h * β * (MulAut.conj h)⁻¹ := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply]

theorem oddRadConcl_suzukiGroup {a : ℕ} {K : Type} [Field K]
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : MulAut (suzukiGroup a K))
    (hβ : orderOf β = 5) : OddRadConcl (suzukiGroup a K) β := by
  classical
  have hfin : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  by_cases hβI : β ∈ inner (suzukiGroup a K)
  · obtain ⟨g, rfl⟩ := hβI
    have hinj := KE.suzuki_conj_injective ha hK
    have hgo : orderOf g = 5 := by rw [← hβ, orderOf_injective _ hinj g]
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hgo
      exact absurd hgo (by norm_num)
    have hgodd : Odd (orderOf g) := by rw [hgo]; decide
    unfold OddRadConcl
    rw [eqLocus_mulAut_conj]
    exact odd_card_radical_perfectResidual_of_odd_card
      ((CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).2 g hg1
        hgodd).1
  · obtain ⟨σ, h, b, k, _, _, -, -, hk, hconj, ⟨eH⟩⟩ :=
      KE.suzukiPrimeFieldCosetDescent a ha K hK 5 (by norm_num) (by norm_num) β hβ hβI
    rw [← oddRadConcl_congr (MulAut.conj h) β, mulAut_congr_conj, hconj]
    show Odd (Nat.card ↥(solvableRadical ↥(perfectResidual
      ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _)))))
    rw [card_solvableRadical_perfectResidual_eq eH]
    by_cases hb1 : 1 ≤ b
    · obtain ⟨hfinS, -, hsimple⟩ := suzuki_simple hb1 hk
      rw [radical_perfectResidual_eq_bot_of_isSimpleGroup (suzuki_perfect hb1 hk).2,
        Subgroup.card_bot]
      exact odd_one
    · obtain rfl : b = 0 := by omega
      have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
      have hcard := (suzuki_two_normal_five_complement_core_trivial hk2).1
      have hfinS : Finite (suzukiGroup 0 k) := finite_suzukiGroup hk
      have hsolv : Group.IsSolvable (suzukiGroup 0 k) :=
        CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)
      rw [radical_perfectResidual_eq_bot_of_isSolvable hsolv, Subgroup.card_bot]
      exact odd_one

theorem oddRadAt_smallModel_twistedB2 :
    OddRadAt (SmallModel .twistedB2) := by
  rintro T _ _ _ ⟨n, f, _, hmodel, -⟩ β hβ
  rcases hmodel with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, hS⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hS
    exact oddRadConcl_of_mulEquiv e
      (fun β' hβ' => oddRadConcl_suzukiGroup ha (by rw [hK, hf]) β' hβ') β hβ

end CFSG.RankThree.PartOne.F106
