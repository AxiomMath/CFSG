module

public import CFSG.Quasithin.Recognition.AS14216QO2Core
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotJ2
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.AS14216

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem isQ8D8_facts {Q : Subgroup G} (hq : IsQ8D8 ↥Q) :
    Nat.card Q = 32 ∧ ∃ z ∈ Q, z ≠ 1 ∧ (∀ q ∈ Q, z * q = q * z) ∧
      (∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z) ∧ ∃ q ∈ Q, q * q = z := by
  classical
  refine ⟨hq.1, ?_⟩
  obtain ⟨z, hzc, hz1, -, hcen, hsq⟩ := CFSG.Quasithin.H13.isQ8D8_central_facts hq
  refine ⟨z, z.2, fun h => hz1 (Subtype.ext h), fun q hq' => ?_, fun c hc hcq => ?_, ?_⟩
  · have := Subgroup.mem_center_iff.mp hzc ⟨q, hq'⟩
    exact (congrArg Subtype.val this).symm
  · have hcc : (⟨c, hc⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      exact Subtype.ext (hcq q q.2).symm
    rcases hcen _ hcc with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · by_contra hno
    push Not at hno
    have hsq1 : ∀ x : ↥Q, x * x = 1 := fun x => by
      rcases hsq x with h | h
      · exact h
      · exact absurd (congrArg Subtype.val h) (hno x x.2)
    have hinv : ∀ x : ↥Q, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq1 x)
    have hcomm : ∀ x y : ↥Q, x * y = y * x := fun x y => by
      calc x * y = (x * y)⁻¹ := (hinv _).symm
        _ = y * x := by rw [mul_inv_rev, hinv, hinv]
    have h12 : ∀ x : ↥Q, x = 1 ∨ x = z := fun x =>
      hcen x (Subgroup.mem_center_iff.mpr fun y => hcomm y x)
    have hle : Nat.card ↥Q ≤ Nat.card Bool := by
      refine Nat.card_le_card_of_injective (fun x : ↥Q => decide (x = 1)) ?_
      intro x y hxy
      rcases h12 x with rfl | rfl <;> rcases h12 y with rfl | rfl <;> simp_all
    rw [hq.1, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
    omega

theorem pCoreOf_le_pCoreOf_of_isQ8D8 {X K1 : Subgroup G} (hKX : K1 ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K1 : Set G)) (hct : CharTwo X)
    (hq : IsQ8D8 ↥(pCoreOf 2 X)) (h5 : 5 ∣ Nat.card K1) : pCoreOf 2 X ≤ pCoreOf 2 K1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Q := pCoreOf 2 X with hQdef
  have hQX : Q ≤ X := pCoreOf_le 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 X
  obtain ⟨hQ32, z, hzQ, hz1, hzc, hcen, hsq⟩ := isQ8D8_facts hq
  obtain ⟨k0, hk0⟩ := exists_prime_orderOf_dvd_card' (G := ↥K1) 5 h5
  set k : G := (k0 : G) with hkdef
  have hk : orderOf k = 5 := by rw [hkdef, Subgroup.orderOf_coe, hk0]
  have hkK : k ∈ K1 := k0.2
  have hkQ : k ∈ Subgroup.normalizer (Q : Set G) := hXQ (hKX hkK)
  have hkK1 : k ∈ Subgroup.normalizer (K1 : Set G) := Subgroup.le_normalizer hkK
  set W := Q ⊓ K1 with hW
  have hkW : k ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [hW, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hkQ g,
      Subgroup.mem_normalizer_iff.mp hkK1 g]
  have hcomm : ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W := by
    intro q hq'
    refine Subgroup.mem_inf.mpr ⟨Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hkQ q).mp hq')
      (Q.inv_mem hq'), ?_⟩
    have h1 : q * k⁻¹ * q⁻¹ ∈ K1 :=
      (Subgroup.mem_normalizer_iff.mp (hXK (hQX hq')) _).mp (K1.inv_mem hkK)
    have := K1.mul_mem hkK h1
    simpa [mul_assoc] using this
  have hnc : ¬ ∀ q ∈ Q, k * q = q * k := by
    intro h
    have hkC : k ∈ X ⊓ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_inf.mpr ⟨hKX hkK, Subgroup.mem_centralizer_iff.mpr fun q hq' => (h q hq').symm⟩
    have hkQ' : k ∈ Q := hct hkC
    have hd : orderOf k ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hkQ'
    rw [hk, hQ32] at hd
    norm_num at hd
  have hWQ : W = Q := eq_of_orderOf_five hQ32 inf_le_left hkQ hkW hk hcomm hnc hzQ hz1 hzc hcen hsq
  have hQK : Q ≤ K1 := hWQ ▸ (inf_le_right : Q ⊓ K1 ≤ K1)
  exact le_pCoreOf_of_le_normalizer 2 hQK (hKX.trans hXQ) (pCoreOf_isPGroup 2 X)

variable {T M H K1 : Subgroup G}

end CFSG.Quasithin.AS14216
