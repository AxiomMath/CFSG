module

public import CFSG.RankThree.PartOne.KFOUT3.Transport
public import CFSG.RankThree.PartOne.N143.JGood

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem A_le_normalizer_J {p : ℕ} {A : Subgroup G} {c : G} {J : Subgroup G} (h : JGood p A c J) :
    A ≤ Subgroup.normalizer (J : Set G) := fun a ha =>
  h.mem_normalizer_of_scalar (Subgroup.le_normalizer ha) ⟨1, fun x hx => by
    rw [pow_one]
    exact mul_inv_eq_iff_eq_mul.2 (Sec12Three.mul_comm_of_mem_A h.hyp ha hx)⟩

theorem Tof_le_J {p : ℕ} {A : Subgroup G} {c : G} {J : Subgroup G} (h : JGood p A c J) :
    Tof A J ≤ J := by
  rw [Tof, Subgroup.commutator_le]
  intro a ha w hw
  have h1 : a * w * a⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.1 (A_le_normalizer_J h ha) w).1 hw.1
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw.1)

theorem exists_model_of_JGood {p : ℕ} {A : Subgroup G} {c : G} {J : Subgroup G}
    (h : JGood p A c J) {f : ℕ} (hpf : p ∣ 2 ^ f - 1)
    (hmodel : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ ζ : Kˣ, orderOf ζ = p ∧
      ∃ ι : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K,
        (∀ (t : G) (ht : t ∈ Tof A J), ι (QuotientGroup.mk ⟨t, Tof_le_J h ht⟩) ∈ Tbar p K) ∧
        ∀ s ∈ Tbar p K, ∃ (t : G) (ht : t ∈ Tof A J),
          ι (QuotientGroup.mk ⟨t, Tof_le_J h ht⟩) = s := by
  classical
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e0⟩⟩ := hmodel
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hdvd : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hpf
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζ' : IsPrimitiveRoot ζ p := by
    have := IsPrimitiveRoot.orderOf ζ
    rwa [hζ] at this
  let e1 : (↥J ⧸ Subgroup.center ↥J) ≃* PSL3 K :=
    e0.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
  let ε₀ : ↥J →* PSL3 K := e1.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J))
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥J)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.generic.center_pPrime
  have hε₀ : IsCentralPQuot p ε₀ := isCentralPQuot_center e1 hcop
  let T : Subgroup ↥J := (Tof A J).subgroupOf J
  have hTmem : ∀ t ∈ T, ((t : ↥J) : G) ∈ Tof A J := fun t ht => ht
  have hTexp : ∀ t ∈ T, t ^ p = 1 := by
    intro t ht
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact Sec12Three.pow_eq_one_of_mem_A h.hyp (Tof_le A J (hTmem t ht))
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    apply Subtype.ext
    exact Sec12Three.mul_comm_of_mem_A h.hyp (Tof_le A J (hTmem s hs)) (Tof_le A J (hTmem t ht))
  have hTcard : p ^ 2 ≤ Nat.card T := by
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Tof_le_J h)).toEquiv
    rw [this, h.card_Tof]
  obtain ⟨κ, hκ1, hκ2⟩ := exists_torus_transport hp h5 ⟨ζ, hζ'⟩ ε₀ hε₀ T hTexp hTcomm hTcard
  refine ⟨K, hKf, hKfin, hchar, hK, ζ, hζ, e1.trans (MulAut.conj κ), ?_, ?_⟩
  · intro t ht
    exact hκ1 ⟨t, Tof_le_J h ht⟩ ht
  · intro s hs
    obtain ⟨t, ht, hts⟩ := hκ2 s hs
    exact ⟨(t : G), ht, hts⟩

end CFSG.RankThree.PartOne.KFOUT3
