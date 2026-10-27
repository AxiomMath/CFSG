module

public import CFSG.RankThree.PartOne.S11.Sec11One
public import CFSG.RankThree.PartOne.S11b.Sec11Algebra
public import CFSG.RankThree.PartOne.S12.KF128Rank1
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S11.PlaneData

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Sec11Indeed

variable {G : Type} [Group G] [Finite G]

structure Sit (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) : Prop where
  setup : SteinbergBM.SectionTenSetup G p A
  c_mem : c ∈ A
  c_ne_one : c ≠ 1
  L_mem : L ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) c
  fail : ∀ K ∈ sectionTenZeroStar p A ∩ sectionTenOne p A, ¬ A ⊓ L ≤ K
  a_mem : a ∈ A
  d_mem : d ∈ A
  d_ne_one : d ≠ 1
  A_eq : A = zpowers a ⊔ zpowers c ⊔ zpowers d
  d_gen : zpowers d = A ⊓ L
  a_field : InducesFieldAut p a L
  even : CFSG.Blueprint.EvenLieType (L ⧸ Subgroup.center L)
  p_ndvd : ¬ p ∣ Nat.card (Subgroup.center L)

structure WitnessAt (A : Subgroup G) (c f : G) (R : Subgroup G) : Prop where
  le_cent : R ≤ centralizer ({f} : Set G)
  ne_bot : R ≠ ⊥
  two : IsPGroup 2 R
  norm : A ≤ normalizer (R : Set G)
  comm : R = ⁅R, zpowers c⁆

@[expose] def ThreeClaim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G),
    Sit p A c L a d → CFSG.pRank p ↥L = 1

@[expose] def FourClaim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G),
    Sit p A c L a d → ∀ f : G, f ∈ zpowers a ⊔ zpowers c → f ≠ 1 → ∀ R : Subgroup G,
      WitnessAt A c f R →
      ∃ K ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) f,
        inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤ K ∧ A ⊓ L ≤ K ∧
        ⁅R, K⁆ = K ∧ InducesFieldAut p c K

@[expose] def FiveClaim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G),
    Sit p A c L a d → CFSG.pRank p ↥L = 1 → ∃ R : Subgroup G, WitnessAt A c a R

structure Transvection (p : ℕ) (A K : Subgroup G) (d u v : G) : Prop where
  mem : u ∈ K
  pElt : ∃ k : ℕ, orderOf u = p ^ k
  cent_d : u * d * u⁻¹ = d
  moves : u * v * u⁻¹ ≠ v
  comm_mem : ∀ e ∈ A, u * e * u⁻¹ * e⁻¹ ∈ zpowers d

@[expose] def FinalClaim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G),
    Sit p A c L a d → ∀ (K : Subgroup G) (x y : G),
      K ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) a →
      inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) ≤ K → A ⊓ L ≤ K →
      A ⊓ K = zpowers d → InducesFieldAut p c K → CFSG.pRank p ↥L = 1 →
      Transvection p A K d x c → Transvection p A L d y a →
      ∃ (T Q W : Subgroup G) (x' y' z : G), Q ≤ T ∧ W ≤ Q ∧ x' ∈ T ∧ y' ∈ T ∧ z ∈ Q ∧
        (∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q) ∧ (∀ w ∈ W, ∀ t ∈ T, t * w = w * t) ∧
        y'⁻¹ * x'⁻¹ * y' * x' ∈ Q ∧ (∀ q ∈ Q, q⁻¹ * x'⁻¹ * q * x' ∈ W) ∧
        (∀ q ∈ Q, q⁻¹ * y'⁻¹ * q * y' ∈ W) ∧ x' ^ p * y' ^ p = 1 ∧
        p ∣ Monoid.exponent Q ∧ orderOf (x' * y' * z) = p * Monoid.exponent Q

end Sec11Indeed

open Sec11Indeed in
theorem sec11OneIndeed_of_steps (hS : SchreierFor InCatalog) (h107 : InSec10Seven)
    (h112 : InSec11Two) (hKF : KF128Rank1) (h113 : ThreeClaim) (h114 : FourClaim) (h115 : FiveClaim)
    (hfin : FinalClaim) : Sec11OneIndeed := by
  intro G _ _ p A h L hL
  by_contra hnot
  have hfail : ∀ K ∈ sectionTenZeroStar p A ∩ sectionTenOne p A, ¬ A ⊓ L ≤ K :=
    fun K hK hle => hnot ⟨K, hK, hle⟩
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p A).2.2.1 hL.1.2)
  have hLsit : L ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) c := ⟨hL, hLc⟩
  obtain ⟨hEven, hndvd, a, d, haA, hdA, hd1, hAeq, hdL, hfa⟩ := h112 G p A h c hcA hc1 L hLsit
  have sit : Sit p A c L a d :=
    ⟨h, hcA, hc1, hLsit, hfail, haA, hdA, hd1, hAeq, hdL, hfa, hEven, hndvd⟩
  have h3 := h113 G p A c L a d sit
  obtain ⟨R, hR⟩ := h115 G p A c L a d sit h3
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hfa.2.1 (Subgroup.mem_sup_left L.one_mem)
  have haac : a ∈ zpowers a ⊔ zpowers c := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  obtain ⟨K, hK, hCLK, hALK, -, hcK⟩ := h114 G p A c L a d sit a haac ha1 R hR
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hdLmem : d ∈ L := (Subgroup.mem_inf.mp (hdL ▸ Subgroup.mem_zpowers d)).2
  obtain ⟨hqL, hAL, -⟩ := moving_maximal_data_at hS h hL.1 hcA hc1 hLc
  have hevL : evenRank ↥L ≤ 3 :=
    (Sec9A.evenRank_subgroup_le L).trans (sectionTenSetup_evenRank_eq h).le
  obtain ⟨-, S, hSL, hS1, hS2, hAS, -⟩ := hL.1.1
  obtain ⟨y, hyL, hyp, hyd, hya, hye⟩ := hKF G p L A a d hp hp5 hqL hEven hevL h3.le hndvd hAe hAL
    haA hdA hdLmem hd1 hfa ⟨S, hSL, hS1, hS2, hAS haA, hAS hdA⟩
  obtain ⟨hqK, hAK, -⟩ := moving_maximal_data_at hS h hK.1.1 haA ha1 hK.2
  have hEvenK := h107 G p A h K hK.1.1
  have hndvdK := (h112 G p A h a haA ha1 K hK).2.1
  have hevK : evenRank ↥K ≤ 3 :=
    (Sec9A.evenRank_subgroup_le K).trans (sectionTenSetup_evenRank_eq h).le
  have hdK : d ∈ K := hALK (Subgroup.mem_inf.mpr ⟨hdA, hdLmem⟩)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, d', -, hd'A, hd'1, -, hd'K, -⟩ := h112 G p A h a haA ha1 K hK
  have hAKd : A ⊓ K = zpowers d := by
    have hordd : orderOf d = p :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) d hdA) hd1
    have hordd' : orderOf d' = p :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) d' hd'A) hd'1
    rw [← hd'K]
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ?_) ?_
    · rw [hd'K]
      exact Subgroup.mem_inf.mpr ⟨hdA, hdK⟩
    · rw [Nat.card_zpowers, Nat.card_zpowers, hordd, hordd']
  have hAeqK : A = zpowers c ⊔ zpowers a ⊔ zpowers d := by
    rw [sup_comm (zpowers c) (zpowers a)]
    exact sit.A_eq
  have sitK : Sit p A a K c d :=
    ⟨h, haA, ha1, hK, fun K' hK' hle => hfail K' hK' ((le_inf inf_le_left hALK).trans hle), hcA, hdA,
      hd1, hAeqK, hAKd.symm, hcK, hEvenK, hndvdK⟩
  have hrK : CFSG.pRank p ↥K ≤ 1 := (h113 G p A a K c d sitK).le
  obtain ⟨-, SK, hSKK, hSK1, hSK2, hASK, -⟩ := hK.1.1.1
  obtain ⟨x, hxK, hxp, hxd, hxc, hxe⟩ := hKF G p K A c d hp hp5 hqK hEvenK hevK hrK hndvdK hAe hAK
    hcA hdA hdK hd1 hcK ⟨SK, hSKK, hSK1, hSK2, hASK hcA, hASK hdA⟩
  obtain ⟨T, Q, W, x', y', z, hQT, hWQ, hx', hy', hz, hQc, hWz, hc, hQx, hQy, hxy, hexp, hord⟩ :=
    hfin G p A c L a d sit K x y hK hCLK hALK hAKd hcK h3 ⟨hxK, hxp, hxd, hxc, hxe⟩
      ⟨hyL, hyp, hyd, hya, hye⟩
  exact Sec11Algebra.false_of_subgroup_relations hp hp5 T Q W hQT hWQ x' y' z hx' hy' hz hQc hWz
    hc hQx hQy hxy hexp hord

end CFSG.RankThree.PartOne
