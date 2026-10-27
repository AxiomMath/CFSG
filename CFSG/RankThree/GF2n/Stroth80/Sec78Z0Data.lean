module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_Z0_data (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t) :
    Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) = Nat.card Q * Nat.card Z ∧
      IsOppDecomp (hc.CN t) Z0 (LB M Q B) (LB M Q (conjSubgroup r B))
        (LB M Q B ⊓ hc.CN t) (LB M Q (conjSubgroup r B) ⊓ hc.CN t) ∧
      LB M Q B ⊓ LB M Q (conjSubgroup r B) = Z0 := by
  obtain ⟨-, hcard, hcomm, hopp⟩ := h51 G M Q Z B hc n t hs hnat r hr.mem
    hr.plane (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t)
    (Rt M (LB M Q B) t) rfl rfl rfl rfl rfl
  have hQI : Q ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
    le_inf sec39_Q_le_LB sec39_Q_le_LB
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]
    exact le_sup_right
  have hIZ : LB M Q B ⊓ LB M Q (conjSubgroup r B) = Z0 := by
    apply le_antisymm
    · intro x hx
      refine (hZ0 x).mpr ⟨le_Rt (M := M) (LB M Q B) hs.mem hx.1, fun ρ hρ => ?_⟩
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hcomm ρ hρ x hx)
    · intro z hz
      obtain ⟨-, -, -, -, -, hinf, -, -, h9, h10⟩ := hopp
      have hzN := hZN hz
      have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
      have hzA1 : z ∈ LB M Q B ⊓ hc.CN t :=
        (h9 z hzN).mpr fun l hl => by
          rw [← commutatorElement_inv]
          exact hQI (Q.inv_mem (hZ0.comm_mem hz (hLR hl)))
      have hzA2 : z ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t :=
        (h10 z hzN).mpr fun l hl => by
          rw [← commutatorElement_inv]
          exact hQI (Q.inv_mem (hZ0.comm_mem hz (hL'R hl)))
      rw [← hinf]
      exact ⟨hzA1, hzA2⟩
  refine ⟨by rw [hcard], ?_, hIZ⟩
  rw [hIZ] at hopp
  exact hopp

theorem sec7ctr_Z0_le_LB (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t) :
    Z0 ≤ LB M Q B := by
  obtain ⟨-, -, hIZ⟩ := sec7ctr_Z0_data h51 hc hs hnat hr hZ0 hZN
  rw [← hIZ]
  exact inf_le_left

theorem sec7ctr_Z0_le_LC (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t) :
    Z0 ≤ LB M Q (conjSubgroup r B) := by
  obtain ⟨-, -, hIZ⟩ := sec7ctr_Z0_data h51 hc hs hnat hr hZ0 hZN
  rw [← hIZ]
  exact inf_le_right

theorem sec7ctr_card_Z0 (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t) :
    Nat.card Z0 = Nat.card Q * Nat.card Z := by
  obtain ⟨hcard, -, hIZ⟩ := sec7ctr_Z0_data h51 hc hs hnat hr hZ0 hZN
  rw [← hIZ]
  exact hcard

theorem sec7ctr_Z0_le_conj_LB (hc : Ctx M Q Z B) {t : G}
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZL : Z0 ≤ LB M Q B)
    {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) : Z0 ≤ conjSubgroup ρ (LB M Q B) := by
  have hnorm : ∀ σ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, σ * y * σ⁻¹ ∈ Q := fun σ hσ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hσ)) y).mp hy
  intro z hz
  rw [mem_conjSubgroup]
  have hρi : ρ⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hρ
  have h1 : ρ⁻¹ * z * ρ⁻¹⁻¹ ∈ Z0 :=
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hnorm hρi) z).mp hz
  rw [inv_inv] at h1
  exact hZL h1

end CFSG.RankThree.GF2n.Stroth80
