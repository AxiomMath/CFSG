module

public import CFSG.Quasithin.Background.RonanH143NF2
public import CFSG.Quasithin.Background.RonanH143E2
public import CFSG.Quasithin.Background.RonanH143Ind
public import CFSG.Quasithin.Background.RonanH143Nat
public import CFSG.Quasithin.Background.RonanH143F4e
public import CFSG.Quasithin.Background.RonanH143ConjC

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf

theorem NQ_ne_fixO : NQ ≠ fixO := by
  intro h
  have h1 : nqPerm 4 ∈ NQ := ⟨4, rfl⟩
  rw [h, mem_fixO_iff] at h1
  obtain ⟨t, ht⟩ := h1
  have key : ∀ s : Fin 16, nqPerm 4 ≠ koPerm s := by decide +kernel
  exact key t ht

theorem MY_le_self (Γ : Subgroup P24) {α : Type*} [MulAction P24 α] (Y : α) : MY Γ Y ≤ Γ :=
  inf_le_left

theorem part2a_L :
    ∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
      ConjIsoModel (perfectCore (MY mog22 Qstd)) NQ (Multiplicative (Fin 2 → K))
        ((natSub 2 K (CFSG.Open.StatedSL 2 K) : Subgroup (MulAut (Multiplicative (Fin 2 → K)))) :
          Set (MulAut (Multiplicative (Fin 2 → K)))) :=
  ⟨F4, inferInstance, by rw [Nat.card_eq_fintype_card]; exact F4.card, conjIsoModel_NQ⟩

theorem std_L {T₀ : Subgroup P24}
    (hT : T₀ ⊓ mog22 = PO) : H143Concl 0 1 Ostd Sstd Bstd T₀ mog22 := by
  have hM : MY mog22 Qstd ⊓ mog22 = MY mog22 Qstd := inf_eq_left.2 (MY_le_self _ _)
  unfold H143Concl
  rw [Sstd_erase, ← Hstd_eq, M22g_zero_one, KY_Q_L, inf_eq_left.2 NQ_le_mog22, hM]
  refine ⟨⟨by rw [KY_H_L]; exact NQ_ne_fixO, fun A => ?_, fun h => absurd rfl h⟩,
    ⟨part2a_L, fun h => absurd rfl h⟩, ⟨fun _ => conjSymNatural_H_L, fun h => absurd rfl h⟩⟩
  rw [hT, KY_H_L]
  exact isE2k_four_PO_iff A

theorem std_L2 {T₀ : Subgroup P24}
    (hT : T₀ ⊓ mog22plus = P2) : H143Concl 0 1 Ostd Sstd Bstd T₀ mog22plus := by
  have hT' : T₀ ⊓ mog22 = PO := by
    have h : T₀ ⊓ mog22 = (T₀ ⊓ mog22plus) ⊓ mog22 := by
      rw [inf_assoc, inf_eq_right.2 mog22_le_mog22plus]
    rw [h, hT, P2_inf_mog22]
  have hne : mog22plus ≠ mog22 := fun h => ePerm_notMem_mog22 (h ▸ ePerm_mem_mog22plus)
  unfold H143Concl
  rw [Sstd_erase, ← Hstd_eq, M22g_zero_one, KY_Q_L2, NQ2_inf_mog22, MY_plus_inf_mog22]
  refine ⟨⟨by rw [KY_H_L2]; exact NQ_ne_fixO, fun A => ?_, fun _ A => ?_⟩,
    ⟨part2a_L, fun _ => ⟨⟨piQ mog22plus, piQ_range_top_L2, ?_⟩, ?_, ?_⟩⟩,
    ⟨fun h => absurd h hne, fun _ => conjSymNatural_H_L2⟩⟩
  · rw [hT', KY_H_L2]
    exact isE2k_four_PO_iff A
  · rw [hT]
    exact isE2k_five_P2_iff A
  · rw [ker_piQ_L2]
  · exact card_NQ2
  · simpa only [KY_Q_L2] using indecomposable_Q_L2

theorem main {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S)
    (hBS : B ∈ S) (haB : a ∈ B) (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O)
    (hTS : ∀ g ∈ T₀, g • S = S) (hL : M22g a b ≤ Γ) (hΓ : Γ ≤ M2ab a b)
    (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ) : H143Concl a b O S B T₀ Γ := by
  obtain ⟨c, hc, hca, hO', hS', hB', hcases⟩ :=
    normal_form hab hO haO hbO hS hBS haB hbB hTO hTS hL hΓ hSyl
  refine H143Concl_of_conj hc ?_
  rw [hO', hS', hB']
  have key : H143Concl 0 1 Ostd Sstd Bstd (conjSubg c T₀) (conjSubg c Γ) := by
    rcases hcases with ⟨hΓc, hTc⟩ | ⟨hΓc, hTc⟩
    · rw [hΓc]
      exact std_L hTc
    · rw [hΓc]
      exact std_L2 hTc
  rcases hca with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
    exact key
  · rw [h0, h1]
    exact H143Concl_swap key

end CFSG.Quasithin.RonanH143
