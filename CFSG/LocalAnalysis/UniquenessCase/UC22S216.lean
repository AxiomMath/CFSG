module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsSixInf
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10Spor
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.UC22S216Spor
import CFSG.LocalAnalysis.UniquenessCase.UC22S216Inn
import CFSG.LocalAnalysis.UniquenessCase.UC22S216J1
import CFSG.LocalAnalysis.UniquenessCase.UC22S216J1Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

private theorem uc22s216_center_barInf_eq_bot {M L : Subgroup G} (hL : L ∈ calC M) :
    center (BarInf L) = ⊥ := by
  obtain ⟨hsimp, a, b, hab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (BarInf L)) with h | h
  · exact h
  · have hb : b ∈ center (BarInf L) := by
      rw [h]
      exact mem_top b
    exact absurd ((mem_center_iff.mp hb) a) hab

theorem uc22s216_eq_J1_of_isSpor {D : Data G} {Ch : Choice2011 G} (h3 : S21_3 D Ch)
    (h5 : S21_5 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hK : F10.K105Spor)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {s : TauCeti.SporadicName} (hs : IsSpor (BarInf L) s) : s = .J1 := by
  by_contra hsJ
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hBN : c.B0 ≤ normalizer (L : Set G) := h5 hH c₀ L hL
  have hthin := uc22s216_not_thin8_of_isSpor hrank hL hsJ hs
  obtain ⟨-, hBab, -, -, -, -, -, -, -, hBT, -, -⟩ := c.hB0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBo : Odd (Nat.card ↥c.B0) := by
    by_contra h
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 2 h
    have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 b.2
    rw [Subgroup.orderOf_coe, hb] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  obtain ⟨S, Bφ, hS, hBφab, hBφo, hperm, hact⟩ := uc22s216_exists_inner_permutes
    (uc22s216_center_barInf_eq_bot hL)
    (fun σ hσ => uc22s216_mem_range_conj_of_isSpor hout hL hs hσ)
    (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hBN hBT hBab hBo
  haveI := hBφab
  have hB3 : IsPGroup 3 ↥Bφ :=
    F10.isPGroup_three_of_permutes_spor hK hsJ hs hS inferInstance hBφo hperm
  obtain ⟨p, hp, hpd, hp3⟩ := uc22p20o_prime_sub_one_ne_three (hn3 hH c)
  have hpB : p ∣ Nat.card ↥c.B0 := by
    have hpi : p ∈ piSet c.B0 := by rw [c.hpi]; exact ⟨hp, hpd⟩
    exact hpi.2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) p hpB
  rw [← Subgroup.orderOf_coe] at hb
  obtain ⟨x, hx, hbx, hxo⟩ := hact (b : G) b.2
  have hx1 : x = 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hB3.exists_card_eq
    have h1 : orderOf x ∣ 3 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard Bφ hx
    have hcop : Nat.Coprime (3 ^ k) p :=
      ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)).pow_left k
    have h := Nat.dvd_gcd h1 (hb ▸ hxo)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  have h1 : inducedBarInfAutHom L ⟨b, hBN b.2⟩ = 1 := by rw [hbx, hx1, map_one]
  have hb1 : (b : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    exact hp.one_lt.ne hb
  exact hthin (h3 hH c₀ L hL ⟨b, b.2, hb1,
    uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN b.2) h1⟩)

theorem s21_6Inf_of_k105Spor {D : Data G} {Ch : Choice2011 G} (h3 : S21_3 D Ch)
    (h5 : S21_5 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hK : F10.K105Spor)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2) :
    S21_6Inf D Ch := by
  rintro hH c L hL ⟨s, hs⟩
  obtain rfl := uc22s216_eq_J1_of_isSpor h3 h5 hn3 hK hrank hout hH c hL hs
  have hJ : IsJ1 (BarInf L) := hs
  refine ⟨uc22s216_isJ1_bar2_of_isJ1_barInf hL hJ, ?_⟩
  have hBN : c.B ≤ normalizer (L : Set G) := h5 hH c L hL
  obtain ⟨-, hBab, -, -, -, -, -, -, -, hBT, -, -⟩ := c.hB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBo : Odd (Nat.card ↥c.B) := by
    by_contra h
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B) 2 h
    have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB b.2
    rw [Subgroup.orderOf_coe, hb] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  obtain ⟨S, Bφ, hS, hBφab, hBφo, hperm, hact⟩ := uc22s216_exists_inner_permutes
    (uc22s216_center_barInf_eq_bot hL)
    (fun σ hσ => uc22s216_mem_range_conj_of_isSpor hout hL hs hσ)
    (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hBN hBT hBab hBo
  haveI := hBφab
  by_cases h7 : 7 ∈ piSet c.B
  · exact Or.inr h7
  left
  have hcent : ∀ b ∈ c.B, (orderOf b).Coprime 3 → CentralizesBar b L := by
    intro b hb hb3
    obtain ⟨x, hx, hbx, hxo⟩ := hact b hb
    have hx1 : x = 1 := by
      by_contra hx1
      obtain ⟨q, hq, hqx⟩ := Nat.exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
      have hqb : q ∣ orderOf b := hqx.trans hxo
      rcases uc22s216_prime_eq_three_or_seven_of_permutes_J1 hJ hS inferInstance hBφo hperm hq
        (hqx.trans (Subgroup.orderOf_dvd_natCard Bφ hx)) with rfl | rfl
      · have h := Nat.dvd_gcd hqb (dvd_refl 3)
        rw [Nat.Coprime.gcd_eq_one hb3] at h
        norm_num at h
      · exact h7 ⟨by norm_num, hqb.trans (Subgroup.orderOf_dvd_natCard c.B hb)⟩
    exact uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN hb)
      (by rw [hbx, hx1, map_one])
  let K : Subgroup G :=
    { carrier := {x | CentralizesBar x L}
      mul_mem' := uc22p21d_centralizesBar_mul
      one_mem' := uc22p21d_centralizesBar_one L
      inv_mem' := fun hx => uc22p21d_centralizesBar_of_mem_zpowers hx (inv_mem (mem_zpowers _)) }
  have hOK : CFSG.Quasithin.opResidual 3 c.B ≤ K := by
    rw [CFSG.Quasithin.opResidual, Subgroup.closure_le]
    exact fun x hx => hcent x hx.1 hx.2
  rw [Subgroup.commutator_le]
  intro g hg l hl
  have hgK : CentralizesBar g L := hOK hg
  rw [commutatorElement_def]
  exact hgK.2 l hl

end CFSG.LocalAnalysis.UniquenessCase.UC22
