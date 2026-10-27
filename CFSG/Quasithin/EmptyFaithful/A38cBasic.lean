module

public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

section Quot

variable {G : Type} [Group G] {L : Subgroup G}

noncomputable def quotPCoreMulEquiv {Q : Type*} [Group Q] (α : ↥L →* Q)
    (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥L) :
    ↥L ⧸ CFSG.pCore 2 ↥L ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective α hα)

theorem card_quot_pCore_of_surjective {Q : Type*} [Group Q] (α : ↥L →* Q)
    (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card Q :=
  Nat.card_congr (quotPCoreMulEquiv α hα hk).toEquiv

theorem card_quotPCore_of_isAltType {m : ℕ} (hm : 2 ≤ m) (h : IsAltType L m) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = m.factorial / 2 := by
  obtain ⟨α, hα, hk, -⟩ := h
  rw [card_quot_pCore_of_surjective α hα hk, card_alt m hm]

theorem card_quotPCore_of_isAltBlockTypeWith {m : ℕ} (hm : 2 ≤ m)
    {α : ↥L →* alternatingGroup (Fin m)} (h : IsAltBlockTypeWith L m α) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = m.factorial / 2 := by
  obtain ⟨hα, hk, -⟩ := h
  rw [card_quot_pCore_of_surjective α hα hk, card_alt m hm]

theorem card_quotPCore_of_isExcA7Block (h : IsExcA7Block L) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 := by
  obtain ⟨-, ⟨α, hα, hk⟩, -⟩ := h
  rw [card_quot_pCore_of_surjective α hα hk, card_alt 7 (by norm_num)]
  decide

theorem card_quotPCore_of_isSp4Block (h : IsSp4Block L) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 979200 := by
  obtain ⟨-, F, _, _, hF, α, hα, hk, -⟩ := h
  have : Finite F := inferInstance
  have hF' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  rw [card_quot_pCore_of_surjective α hα hk, card_Sp4_pow hF']
  norm_num

theorem card_quotPCore_of_isG2Block (h : IsG2Block L) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 :=
  CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three h.2.1

theorem card_quotPCore_of_isHatA6Block (h : IsHatA6Block L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h.2.1
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [Nat.card_congr e.toEquiv, hZ, card_alt 6 (by norm_num)] at h1
  rw [h1]
  decide

theorem card_quotPCore_of_isLin2Type {n : ℕ} (h : IsLin2Type L n) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨F, _, _, hF, α, hα, hk, -⟩ := h
  have : Finite F := inferInstance
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [card_quot_pCore_of_surjective α hα hk, card_SL_two_pow hF']

end Quot

theorem bijective_of_surjective_hom_of_simple {Γ Q : Type*} [Group Γ] [Group Q]
    [IsSimpleGroup Γ] [Nontrivial Q] (π : Γ →* Q) (hπ : Function.Surjective π) :
    Function.Bijective π := by
  refine ⟨(MonoidHom.ker_eq_bot_iff π).mp ?_, hπ⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    obtain ⟨g, rfl⟩ := hπ x
    exact hx (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g))

theorem card_eq_of_surjective_hom_of_simple {Γ Q : Type*} [Group Γ] [Group Q]
    [IsSimpleGroup Γ] [Nontrivial Q] (π : Γ →* Q) (hπ : Function.Surjective π) :
    Nat.card Γ = Nat.card Q :=
  Nat.card_congr (Equiv.ofBijective π (bijective_of_surjective_hom_of_simple π hπ))

end CFSG.Quasithin
