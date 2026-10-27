module

public import CFSG.Quasithin.Background.C126A5Core4
public import CFSG.Quasithin.Background.C126Glue
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Background.GoldschmidtE23FourY0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {G : Type} [Group G] [Finite G]

theorem twoResidual_le_of_isSubnormal {L P : Subgroup G} (h : IsSubnormal L P)
    (hidx : ∃ n : ℕ, L.relIndex P = 2 ^ n) : twoResidual P ≤ L := by
  revert hidx
  induction h with
  | refl H => exact fun _ => twoResidual_le H
  | @step H M K hHM hN hMK ih =>
    rintro ⟨n, hn⟩
    have hMKle : M ≤ K := A4.subnormal_le hMK
    have hmul : H.relIndex M * M.relIndex K = H.relIndex K :=
      Subgroup.relIndex_mul_relIndex H M K hHM hMKle
    have h1 : M.relIndex K ∣ 2 ^ n := hn ▸ hmul ▸ dvd_mul_left _ _
    have h2 : H.relIndex M ∣ 2 ^ n := hn ▸ hmul ▸ dvd_mul_right _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hK : twoResidual K ≤ M := ih ⟨j, hj⟩
    have hMN : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hN
    have hMH : twoResidual M ≤ H := twoResidual_le_of_isTwoQuotient hHM hMN fun y hy =>
      ⟨i, B6.pow_mem_of_relIndex_eq_two_pow hMN hi y hy⟩
    exact (twoResidual_twoResidual K).symm.le.trans
      ((C126.A5.twoResidual_mono hK).trans hMH)

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V}

theorem isShort2_and_isAltType_three_Y (h129 : ASC129Statement G)
    (s : C126.A5.Setting H T M V Y hV)
    (hPU : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    IsShort2 Y ∧ IsAltType Y 3 := by
  classical
  have hsq : IsSQTKIn (Y ⊔ baum T) := C1GN.isSQTKTC_iff_sqtkGroup.1 s.sqtk_P₃
  have hcgs : cgsIn (Y ⊔ baum T) (baum T) ≤ baum T := by
    refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC0 => iSup_le fun hchar => ?_
    have hSN : baum T ≤ Subgroup.normalizer (C : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_of_characteristic hCS hchar)
    have hTN : T ≤ Subgroup.normalizer (C : Set G) :=
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)).trans
        (normalizer_le_of_characteristic hCS hchar)
    rcases s.sandwich_P₃ (le_inf le_sup_right hSN) inf_le_left with h | h
    · exact h.le
    · exfalso
      have hP : Y ⊔ baum T ≤ Subgroup.normalizer (C : Set G) := h ▸ inf_le_right
      refine hPU C hCS hC0 hchar ?_
      rw [← s.P₃_sup_T]
      exact sup_le hP hTN
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 (Y ⊔ baum T) (baum T) (baum T) hsq s.charTwo_P₃
    s.sylow_S hcgs le_sup_right
  obtain ⟨i, hi⟩ : ∃ i, ¬ Lb i ≤ baum T := by
    by_contra hall
    push Not at hall
    refine not_lt_of_ge (fun p hp => ?_) s.S_lt_P₃
    obtain ⟨m, hm, x, hx, rfl⟩ := hprod p hp
    refine (baum T).mul_mem hm (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact hall j (hx j)
  obtain ⟨hchi, -, -⟩ := hLb i
  have hA3 : IsAltType (Lb i) 3 :=
    C1Pack.isAltType_three_of_isBlock2_of_solvable hchi.1 s.isSolvable_P₃
  have hLY : Lb i ≤ Y := by
    have := C126.le_twoResidual_of_short hchi.1.2.1 hchi.1.1
    rwa [s.twoResidual_P₃] at this
  have hcardL : ∃ b : ℕ, Nat.card ↥(Lb i) = 3 * 2 ^ b := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Lb i))).exists_card_eq
    refine ⟨b, ?_⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(Lb i)),
      C2Six.natCard_pCore_quotient_of_isAltType_three hA3, hb]
  have hcardP : ∃ a : ℕ, Nat.card ↥(Y ⊔ baum T) = 3 * 2 ^ a := by
    obtain ⟨a, ha⟩ := (s.hT.2.1.to_le s.S_le_T).exists_card_eq
    refine ⟨a, ?_⟩
    have h1 := Subgroup.relIndex_mul_card (baum T) (Y ⊔ baum T)
    rw [inf_eq_left.2 le_sup_right, s.relIndex_S_P₃, ha] at h1
    exact h1.symm
  have hidx : ∃ n : ℕ, (Lb i).relIndex (Y ⊔ baum T) = 2 ^ n := by
    obtain ⟨b, hb⟩ := hcardL
    obtain ⟨a, ha⟩ := hcardP
    have h1 := Subgroup.relIndex_mul_card (Lb i) (Y ⊔ baum T)
    rw [inf_eq_left.2 hchi.1.2.1, hb, ha] at h1
    have h2 : (Lb i).relIndex (Y ⊔ baum T) * 2 ^ b = 2 ^ a := by
      have : 3 * ((Lb i).relIndex (Y ⊔ baum T) * 2 ^ b) = 3 * 2 ^ a := by
        rw [← h1]
        ring
      omega
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ h2)
    exact ⟨n, hn⟩
  have hYL : Y ≤ Lb i := by
    have := twoResidual_le_of_isSubnormal (IsBlock2.isSubnormal hchi.1) hidx
    rwa [s.twoResidual_P₃] at this
  have hEq : Y = Lb i := le_antisymm hYL hLY
  rw [hEq]
  exact ⟨hchi.1.1, hA3⟩

end E2

end CFSG.Quasithin
