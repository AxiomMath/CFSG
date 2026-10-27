module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm8

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

@[expose] noncomputable def preimageNbar (P : Subgroup S.Nbar) : Subgroup G :=
  (P.comap S.piN).map S.Ng.subtype

theorem mem_preimageNbar {P : Subgroup S.Nbar} {x : G} :
    x ∈ S.preimageNbar P ↔ ∃ h : x ∈ S.Ng, S.piN ⟨x, h⟩ ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem Mg_le_preimageNbar (P : Subgroup S.Nbar) : S.Mg ≤ S.preimageNbar P := by
  intro m hm
  refine S.mem_preimageNbar.mpr ⟨S.Mg_le_Ng hm, ?_⟩
  have : S.piN ⟨m, S.Mg_le_Ng hm⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hm
  rw [this]
  exact one_mem _

theorem preimageNbar_le_Ng (P : Subgroup S.Nbar) : S.preimageNbar P ≤ S.Ng := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem card_Ng : Nat.card S.Ng = 81 * Nat.card S.Nbar := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.Mg.subgroupOf S.Ng)
  have h2 : Nat.card (S.Mg.subgroupOf S.Ng) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.Mg_le_Ng).toEquiv, S.card_Mg_eq_81]
  rw [h2] at h
  rw [h, mul_comm]

theorem card_preimageNbar (P : Subgroup S.Nbar) :
    Nat.card (S.preimageNbar P) = 81 * Nat.card P := by
  have h1 : Nat.card (P.comap S.piN) * (P.comap S.piN).index = Nat.card S.Ng :=
    Subgroup.card_mul_index _
  have h2 : (P.comap S.piN).index = P.index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h3 : Nat.card P * P.index = Nat.card S.Nbar := Subgroup.card_mul_index _
  have h4 : Nat.card (S.preimageNbar P) = Nat.card (P.comap S.piN) := by
    rw [preimageNbar, Subgroup.card_map_of_injective S.Ng.subtype_injective]
  rw [h4]
  rw [h2, S.card_Ng] at h1
  have hpos : 0 < P.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have : Nat.card (P.comap S.piN) * P.index = 81 * Nat.card P * P.index := by
    rw [h1]
    calc 81 * Nat.card S.Nbar = 81 * (Nat.card P * P.index) := by rw [h3]
      _ = 81 * Nat.card P * P.index := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end JWSetup

end CFSG.Quasithin.H13.U43
