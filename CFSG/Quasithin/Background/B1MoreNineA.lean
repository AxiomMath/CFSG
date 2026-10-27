module

public import CFSG.Quasithin.Background.B1MoreSevenA
public import CFSG.Quasithin.Background.D2Fitting
public import CFSG.Quasithin.Background.B1Solvable

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace B19Aux

section Involution

variable {Γ : Type*} [Group Γ]

theorem comm_conj_inv (a x : Γ) (ha : a ^ 2 = 1) :
    a * (x * a * x⁻¹ * a⁻¹) * a⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by
  have h : a * a = 1 := by rw [← pow_two]; exact ha
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h
  rw [ha']
  calc a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ * (a * a) := by group
    _ = a * x * a * x⁻¹ := by rw [h, mul_one]
    _ = (x * a * x⁻¹ * a)⁻¹ := by simp [mul_assoc, ha']

theorem comm_comm_self (a x : Γ) (ha : a ^ 2 = 1) :
    (x * a * x⁻¹ * a⁻¹) * a * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹ = (x * a * x⁻¹ * a⁻¹) ^ 2 := by
  have h := comm_conj_inv a x ha
  set y := x * a * x⁻¹ * a⁻¹ with hy
  have e : y * a * y⁻¹ * a⁻¹ = y * (a * y * a⁻¹)⁻¹ := by group
  rw [e, h, inv_inv, pow_two]

theorem commutator_le_commutator_commutator {X A : Subgroup Γ}
    (hodd : ∀ x ∈ X, Odd (orderOf x)) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) : ⁅X, A⁆ ≤ ⁅⁅X, A⁆, A⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hyX : x * a * x⁻¹ * a⁻¹ ∈ X := by
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact X.mul_mem hx (hAX a ha x⁻¹ (X.inv_mem hx))
  have hy1 : x * a * x⁻¹ * a⁻¹ ∈ ⁅X, A⁆ := Subgroup.commutator_mem_commutator hx ha
  have hy2 : (x * a * x⁻¹ * a⁻¹) ^ 2 ∈ ⁅⁅X, A⁆, A⁆ := by
    have h : (x * a * x⁻¹ * a⁻¹) * a * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹ ∈ ⁅⁅X, A⁆, A⁆ :=
      Subgroup.commutator_mem_commutator hy1 ha
    rwa [comm_comm_self a x (hA2 a ha)] at h
  have hcop : Nat.Coprime 2 (orderOf (x * a * x⁻¹ * a⁻¹)) :=
    Nat.coprime_two_left.2 (hodd _ hyX)
  exact (Subgroup.zpowers_le.2 hy2) (A4.mem_zpowers_pow_of_coprime hcop)

theorem odd_card_of_forall_odd_orderOf [Finite Γ] {K : Subgroup Γ}
    (h : ∀ x ∈ K, Odd (orderOf x)) : Odd (Nat.card K) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card K := by
    rcases Nat.even_or_odd (Nat.card K) with h' | h'
    · exact even_iff_two_dvd.1 h'
    · exact absurd h' hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := h y y.2
  rw [Subgroup.orderOf_coe, hy] at this
  exact absurd this (by decide)

end Involution

section Fitting

variable {V : Type*} [CommGroup V]

theorem odd_orderOf_of_mem_fittingOf [Finite V] {G : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 G = ⊥) : ∀ x ∈ fittingOf G, Odd (orderOf x) := by
  intro x hx
  by_contra hev
  have h2 : 2 ∣ orderOf x := by
    rcases Nat.even_or_odd (orderOf x) with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hev
  have : Group.IsNilpotent ↥(fittingOf G) := fittingOf_nilpotent G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : 2 ∣ Nat.card ↥(fittingOf G) := by
    refine h2.trans ?_
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(fittingOf G))
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hyp : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; simp)
  obtain ⟨P, hP⟩ := hyp.exists_le_sylow
  have hyP : y ∈ (P : Subgroup ↥(fittingOf G)) := hP (Subgroup.mem_zpowers y)
  have hPn : (P : Subgroup ↥(fittingOf G)).Normal := inferInstance
  have : (P : Subgroup ↥(fittingOf G)).Characteristic := Sylow.characteristic_of_normal P hPn
  let N : Subgroup (MulAut V) := (P : Subgroup ↥(fittingOf G)).map (fittingOf G).subtype
  have hNG : N ≤ G := (Subgroup.map_subtype_le _).trans (fittingOf_le G)
  have hGnorm : G ≤ Subgroup.normalizer (fittingOf G : Set (MulAut V)) :=
    le_normalizer_of_conj fun g hg f hf => conj_mem_fittingOf hg hf
  have hnormN : G ≤ Subgroup.normalizer (N : Set (MulAut V)) := fun g hg =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := fittingOf G) _
      (hGnorm hg)
  have hpN : IsPGroup 2 ↥N := P.isPGroup'.map (fittingOf G).subtype
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNG hnormN hpN
  rw [hO2] at hle
  have hy1 : ((y : ↥(fittingOf G)) : MulAut V) ∈ N := Subgroup.mem_map_of_mem _ hyP
  have hy0 : y = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle hy1))
  rw [hy0, orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem fittingOf_conj {G : Subgroup (MulAut V)} {g f : MulAut V} (hg : g ∈ G)
    (hf : f ∈ fittingOf G) : g * f * g⁻¹ ∈ fittingOf G :=
  conj_mem_fittingOf hg hf

end Fitting

end B19Aux

end CFSG.Quasithin
