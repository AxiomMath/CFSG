module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiD
public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1CE
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WIsoHhat

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 CFSG.ClassicalInvolution.Sp62Rec
open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Solomon73 CFSG.Open
open scoped Pointwise


theorem exists_thetaW : ∃ Θ : ↥Wsub ≃* ↥Hhat,
    (Θ ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ : StatedSp 3 (ZMod 2)) = alpha ∧
    (∀ a (ha : a ∈ Wsub), a ∈ DW ↔ (Θ ⟨a, ha⟩ : StatedSp 3 (ZMod 2)) ∈ S0) ∧
    (∀ a (ha : a ∈ Wsub), a ∈ SW ↔ (Θ ⟨a, ha⟩ : StatedSp 3 (ZMod 2)) ∈ A0) := by
  obtain ⟨Θ0, hΘ0⟩ := exists_iso_Wsub_Hhat
  have hH : Nat.card ↥Hhat = 23040 := card_Hhat
  set P : Subgroup ↥Hhat := (DW.subgroupOf Wsub).map Θ0.toMonoidHom with hPdef
  have hPcard : Nat.card P = 512 := by
    rw [hPdef, Subgroup.card_map_of_injective Θ0.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe DW_le_Wsub).toEquiv, card_DW]
  have hS0card : Nat.card (S0.subgroupOf Hhat) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Hhat).toEquiv, card_S0]
  have hidx : ∀ K : Subgroup ↥Hhat, Nat.card K = 512 → ¬ 2 ∣ K.index := by
    intro K hK
    have h := Subgroup.card_mul_index K
    rw [hK, hH] at h
    have h45 : K.index = 45 := by omega
    rw [h45]
    norm_num
  let SP : Sylow 2 ↥Hhat := IsPGroup.toSylow (IsPGroup.of_card (n := 9)
    (by rw [hPcard]; norm_num)) (hidx P hPcard)
  let S1 : Sylow 2 ↥Hhat := IsPGroup.toSylow (IsPGroup.of_card (n := 9)
    (by rw [hS0card]; norm_num)) (hidx _ hS0card)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥Hhat) SP S1
  have hS1 : (S1 : Subgroup ↥Hhat) = MulAut.conj c • (P : Subgroup ↥Hhat) :=
    (congrArg (fun X : Sylow 2 ↥Hhat => (X : Subgroup ↥Hhat)) hc).symm.trans
      Sylow.coe_subgroup_smul
  set Θ : ↥Wsub ≃* ↥Hhat := Θ0.trans (MulAut.conj c) with hΘ
  have hΘapp : ∀ a : ↥Wsub, Θ a = c * Θ0 a * c⁻¹ := fun a => rfl
  have hD : ∀ a (ha : a ∈ Wsub), a ∈ DW ↔ (Θ ⟨a, ha⟩ : StatedSp 3 (ZMod 2)) ∈ S0 := by
    intro a ha
    have key : Θ ⟨a, ha⟩ ∈ (S1 : Subgroup ↥Hhat) ↔ Θ0 ⟨a, ha⟩ ∈ P := by
      rw [hS1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hΘapp]
      show c⁻¹ * (c * Θ0 ⟨a, ha⟩ * c⁻¹) * c⁻¹⁻¹ ∈ P ↔ _
      rw [show c⁻¹ * (c * Θ0 ⟨a, ha⟩ * c⁻¹) * c⁻¹⁻¹ = Θ0 ⟨a, ha⟩ by group]
    have hS1coe : (S1 : Subgroup ↥Hhat) = S0.subgroupOf Hhat := rfl
    rw [hS1coe, Subgroup.mem_subgroupOf] at key
    rw [key, hPdef, Subgroup.mem_map]
    constructor
    · intro haD
      exact ⟨⟨a, ha⟩, haD, rfl⟩
    · rintro ⟨b, hb, hbe⟩
      obtain rfl : b = ⟨a, ha⟩ := Θ0.injective hbe
      exact hb
  refine ⟨Θ, ?_, hD, ?_⟩
  ·
    rw [hΘapp]
    show ((c * Θ0 ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ * c⁻¹ : ↥Hhat) : StatedSp 3 (ZMod 2)) = alpha
    rw [hΘ0]
    have hcα : (c : StatedSp 3 (ZMod 2)) * alpha = alpha * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Hhat_le_centralizer_alpha c.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcα, mul_assoc, mul_inv_cancel, mul_one]
  ·
    set B : Subgroup (StatedSp 3 (ZMod 2)) :=
      ((SW.subgroupOf Wsub).map Θ.toMonoidHom).map Hhat.subtype with hBdef
    have hBS0 : B ≤ S0 := by
      rintro _ ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact (hD a a.2).mp (SW_le_DW ha)
    have hBE : IsE64 B := by
      refine ⟨?_, ?_, ?_⟩
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
        have hab : a * b = b * a := Subtype.ext (SW_comm ha hb)
        show ((Θ a : ↥Hhat) : StatedSp 3 (ZMod 2)) * Θ b = Θ b * Θ a
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        have haa : a * a = 1 := by
          obtain ⟨x, hx⟩ := mem_SW_iff.mp ha
          apply Subtype.ext
          have hx' : (a : Wr 6) = cSp x := hx
          rw [Subgroup.coe_mul, Subgroup.coe_one, hx', cSp_mul_self]
        show ((Θ a : ↥Hhat) : StatedSp 3 (ZMod 2)) * Θ a = 1
        rw [← Subgroup.coe_mul, ← map_mul, haa, map_one]
        rfl
      · rw [hBdef, Subgroup.card_map_of_injective Hhat.subtype_injective,
          Subgroup.card_map_of_injective Θ.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe SW_le_Wsub).toEquiv, card_SW]
    have hBA : B = A0 := eq_A0_of_isE64 B hBS0 hBE
    intro a ha
    rw [← hBA]
    constructor
    · intro haS
      exact ⟨Θ ⟨a, ha⟩, ⟨⟨a, ha⟩, haS, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨b, hb, rfl⟩, hye⟩
      obtain rfl : b = ⟨a, ha⟩ := Θ.injective (Subtype.ext hye)
      exact hb

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
