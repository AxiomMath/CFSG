module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch11SecDO22
public import CFSG.Quasithin.Vol2.Ch11SecO10R

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem isA7Order_of {X : Type} [Group X] [Finite X]
    (hX : IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 7))) : IsA7Order X :=
  card_of_central_quot hX (MonoidHom.id X) Function.surjective_id fun x hx => by
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
    rw [hx]
    exact Subgroup.one_mem _

theorem not_five_dvd_ker {K : Subgroup G} (f : ↥K →* Perm (Fin 7))
    (hf : f.range = alternatingGroup (Fin 7))
    (hK : IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7))) :
    ¬ 5 ∣ Nat.card f.ker := by
  intro h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card K := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hf, nat_card_alternatingGroup, Nat.card_fin] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  have hO2 : IsPGroup 2 (CFSG.pCore 2 ↥K) := by
    rw [← SecD.pCoreOf_subgroupOf]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_of_injective K.subtype
      K.subtype_injective
  obtain ⟨m, hm⟩ := hO2.exists_card_eq
  rw [hm] at h2
  have h3 : ¬ 5 ∣ 2 ^ m := fun h =>
    absurd (Nat.prime_five.dvd_of_dvd_pow h) (by norm_num)
  have h7 : (7 : ℕ).factorial / 2 = 2520 := by decide
  rw [h7] at h1
  rcases isA7Order_of hK with hc | hc <;> rw [hc] at h2 <;> generalize 2 ^ m = M at h2 h3
  · have : Nat.card f.ker = M := by omega
    exact h3 (this ▸ h5)
  · have : Nat.card f.ker = 3 * M := by omega
    rw [this] at h5
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5 with h | h
    · exact absurd h (by norm_num)
    · exact h3 h

theorem exists_five_lOf {K L₁ : Subgroup G} (hLK : L₁ ≤ K) (f : ↥K →* Perm (Fin 7))
    (hf : f.range = alternatingGroup (Fin 7))
    (hK : IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7)))
    {K₀ : Type} [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = 2 ^ 2)
    (e₁ : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K₀) :
    ∃ y : G, ∃ hy : y ∈ L₁, orderOf y = 5 ∧ f ⟨y, hLK hy⟩ ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ : Nat.card (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) = 60 := by
    rw [Nat.card_congr e₁.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK₀]
    norm_num
  have h5 : 5 ∣ Nat.card L₁ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L₁), hQ]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L₁) 5 h5
  have hy' : orderOf (y : G) = 5 := (orderOf_injective L₁.subtype L₁.subtype_injective y).trans hy
  refine ⟨y, y.2, hy', fun h1 => not_five_dvd_ker f hf hK ?_⟩
  have hmem : (⟨(y : G), hLK y.2⟩ : ↥K) ∈ f.ker := h1
  have h3 : orderOf (⟨⟨(y : G), hLK y.2⟩, hmem⟩ : f.ker) = 5 :=
    (orderOf_injective f.ker.subtype f.ker.subtype_injective _).symm.trans
      ((orderOf_injective K.subtype K.subtype_injective _).symm.trans hy')
  rw [← h3]
  exact orderOf_dvd_natCard _

end CFSG.Quasithin.Vol2.Ch11.O10
