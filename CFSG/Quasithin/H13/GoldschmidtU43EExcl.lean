module

public import CFSG.Quasithin.H13.GoldschmidtU43ESylG
public import CFSG.Quasithin.H13.GoldschmidtU43BK2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

theorem card_map_of_trivial_ker {A B : Type} [Group A] [Group B] (φ : A →* B) (P : Subgroup A)
    (h : ∀ p ∈ P, φ p = 1 → p = 1) : Nat.card (P.map φ) = Nat.card P := by
  have hinj : Function.Injective (φ.domRestrict P) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    have hp1 : φ (p : A) = 1 := hp
    have := h _ p.2 hp1
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  rw [← MonoidHom.domRestrict_range]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)
include S

abbrev E1 : Subgroup G := Eg z S.t S.w S.a

abbrev K1 : Subgroup G := Subgroup.normalizer (S.E1 : Set G)

theorem card_K1 : Nat.card S.K1 = 5760 := S.e.swap.card_normalizer_Eg S.e.ha

theorem card_E1 : Nat.card S.E1 = 16 := S.e.swap.card_Eg S.e.ha

theorem card_PK (PK : Sylow 3 ↥S.K1) : Nat.card PK = 9 :=
  card_sylow_three_of_card S.card_K1 PK

theorem exists_conj_Tg (h9 : Nat.card S.Mg = 9) (PK : Sylow 3 ↥S.K1) :
    ∃ g : G, ∀ x : G, x ∈ (PK : Subgroup ↥S.K1).map S.K1.subtype ↔ g⁻¹ * x * g ∈ S.Tg := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hP₀⟩ := S.exists_sylow_Tg h9
  set T' : Subgroup G := (PK : Subgroup ↥S.K1).map S.K1.subtype with hT'
  have hT'card : Nat.card T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective S.K1.subtype_injective]
    exact S.card_PK PK
  have hT'3 : IsPGroup 3 T' := PK.isPGroup'.map _
  obtain ⟨P₁, hP₁⟩ := hT'3.exists_le_sylow
  have hP₀card : Nat.card (P₀ : Subgroup G) = 9 := by
    rw [hP₀]
    exact S.card_Tg
  have hP₁card : Nat.card (P₁ : Subgroup G) = 9 := by
    rw [Sylow.card_eq_multiplicity P₁, ← Sylow.card_eq_multiplicity P₀]
    exact hP₀card
  have hTP : T' = (P₁ : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hP₁ (by rw [hP₁card, hT'card])
  obtain ⟨g, hg⟩ := exists_conj_sylow P₀ P₁
  refine ⟨g, fun x => ?_⟩
  rw [← hP₀, hTP]
  exact hg x

end JWSetup

end CFSG.Quasithin.H13.U43
