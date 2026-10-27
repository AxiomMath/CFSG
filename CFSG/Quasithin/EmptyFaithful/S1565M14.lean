module

public import CFSG.Quasithin.EmptyFaithful.S1565M4
public import CFSG.Quasithin.EmptyFaithful.S1565L9
public import CFSG.Quasithin.EmptyFaithful.S1565M2
public import CFSG.Quasithin.EmptyFaithful.S1565M3

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Natfree

variable {W : Type} [CommGroup W]

theorem natfree_sl3_of_two_le {L : Subgroup (MulAut W)} {V C : Subgroup W} {n' : ℕ} (hn' : 2 ≤ n')
    (h : BinaryNaturalSL L V (V ⊓ C) 3 n') (S : Sylow 2 ↥L) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ V, ((b : MulAut W) u) * u⁻¹ ∈ V ⊓ C → u ∈ V ⊓ C := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨ω, hω1, hodd⟩ := exists_unit_odd_order_ne_one hK hn'
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    obtain ⟨c, hc⟩ := hodd
    have : orderOf ω ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    have h4 : orderOf ω = 1 := by omega
    exact hω1 (orderOf_eq_one_iff.mp h4)
  obtain ⟨b, hb, hbr, hnf⟩ :=
    natural_sl3_borel_element ω hω1 hω2 (orderOf ω) (pow_orderOf_eq_one ω) hπ S
  exact ⟨b, hb, orderOf ω, hodd, hbr, hnf⟩

theorem natfree_sp4_of_two_le {L : Subgroup (MulAut W)} {V C : Subgroup W} {n' : ℕ} (hn' : 2 ≤ n')
    (h : BinaryNaturalSp4 L V (V ⊓ C) n') (S : Sylow 2 ↥L) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ V, ((b : MulAut W) u) * u⁻¹ ∈ V ⊓ C → u ∈ V ⊓ C := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨ω, hω1, hodd⟩ := exists_unit_odd_order_ne_one hK hn'
  obtain ⟨b, hb, hbr, hnf⟩ :=
    natural_sp4_borel_element ω hω1 (orderOf ω) (pow_orderOf_eq_one ω) hπ S
  exact ⟨b, hb, orderOf ω, hodd, hbr, hnf⟩

@[expose] def TypesFourShapeNatW (L : Subgroup (MulAut W)) : Prop :=
  TypesFourShapeNat L ∨ (∃ n', 2 ≤ n' ∧ BinaryNaturalSL L ⊤ (⊤ ⊓ fixV L) 3 n') ∨
    (∃ n', 2 ≤ n' ∧ BinaryNaturalSp4 L ⊤ (⊤ ⊓ fixV L) n')

theorem typesFour_good_natW {L Q : Subgroup (MulAut W)}
    (S : Sylow 2 ↥L)
    (hS : ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), (b : MulAut W) ∈ Q)
    (h : TypesFourShapeNatW L) :
    ∃ a₀ ∈ Q, ∃ m : ℕ, Odd m ∧ a₀ ^ m = 1 ∧ ∀ w : W, a₀ w * w⁻¹ ∈ fixV L → w ∈ fixV L := by
  rcases h with h | ⟨n', hn', h⟩ | ⟨n', hn', h⟩
  · exact typesFour_good_nat S hS h
  · have key := natfree_sl3_of_two_le hn' h S
    obtain ⟨b, hbN, r, hr, hbr, hnf⟩ := key
    refine ⟨(b : MulAut W), hS b hbN, r, hr, ?_, ?_⟩
    · have := congrArg Subtype.val hbr
      simpa using this
    · intro w hw
      exact (hnf w trivial ⟨trivial, hw⟩).2
  · have key := natfree_sp4_of_two_le hn' h S
    obtain ⟨b, hbN, r, hr, hbr, hnf⟩ := key
    refine ⟨(b : MulAut W), hS b hbN, r, hr, ?_, ?_⟩
    · have := congrArg Subtype.val hbr
      simpa using this
    · intro w hw
      exact (hnf w trivial ⟨trivial, hw⟩).2

end Natfree

section Core

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem typesFour_core_natW (hF : HypF918 T V L V₁ Vp H K)
    (M I : Subgroup G) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) (hK0 : conjClosure K T = K)
    (hkerchar : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (hshape : haveI := factElem hF hIU; TypesFourShapeNatW (autIH V₁ I H K)) :
    TypesFourEltConcl hF M I hIU := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFI := factElem hF hIU
  obtain ⟨S, hS⟩ := exists_sylow_borel_acting_two hF M I hIU hnt hkerchar hB
  set φ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  set Q : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H))) :=
    ((H ⊓ M).subgroupOf H).map φ with hQ
  have hSQ : ∀ b ∈ Subgroup.normalizer
      ((S : Subgroup ↥(autIH V₁ I H K)) : Set ↥(autIH V₁ I H K)),
      (b : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Q := by
    intro b hb
    obtain ⟨k, hkM, hkb⟩ := hS b hb
    rw [← hkb, toAutI_coe]
    exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr ⟨hKH k.2, hkM⟩, rfl⟩
  obtain ⟨a₀, ha₀, m, hodd, hpow, hgood⟩ := typesFour_good_natW S hSQ hshape
  obtain ⟨t₀, ht₀mem, rfl⟩ := ha₀
  have ht₀M : (t₀ : G) ∈ M := (Subgroup.mem_subgroupOf.mp ht₀mem).2
  have hKK : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK0]
  refine ⟨t₀, ht₀M, m, hodd, hpow, ?_⟩
  rw [hKK]
  exact hgood

end Core

section Inputs

attribute [local instance] commGroupOfFact

end Inputs

end CFSG.Quasithin
