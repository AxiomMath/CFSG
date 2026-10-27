module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem commW_zpowers_cj (g x : Perm (Fin 5)) :
    commW orth (Subgroup.zpowers (g * x * g⁻¹)) ⊤ = mp g (commW orth (Subgroup.zpowers x) ⊤) := by
  rw [← cj_zpowers, commW_cj_top]

theorem That_le (D : Subgroup (Perm (Fin 5))) : That D ≤ D := by
  unfold That
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

theorem cenW_commW_zStd : cenW (commW orth (Subgroup.zpowers zStd) ⊤) = S5That := by
  ext g
  rw [mem_cenW, mem_S5That_iff]
  have h : ∀ g : Perm (Fin 5), (∀ w ∈ commF zStd, orth.act g w = w) ↔ g ∈ S5ThatF := by
    unfold commF zStd; decide +kernel
  rw [← h g]
  exact forall_congr' fun w => imp_congr_left (mem_commW_zpowers_iff zStd w)

theorem cenW_commW_z {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) : cenW (commW orth (Subgroup.zpowers z) ⊤) = That D := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [isCentInv_cj_std_iff.mp hz, commW_zpowers_cj, cenW_mp, cenW_commW_zStd, ← That_std,
    cj_That]

theorem act_conj_comm (g d : Perm (Fin 5)) (w : orth.W) :
    orth.act (g * d * g⁻¹) (orth.act g w) * (orth.act g w)⁻¹ =
      orth.act g (orth.act d w * w⁻¹) := by
  have h1 : orth.act (g * d * g⁻¹) (orth.act g w) = orth.act g (orth.act d w) := by
    rw [← act_mul_apply, ← act_mul_apply]; congr 1; group
  rw [h1, map_mul, map_inv]

theorem trivOn_conj (g d : Perm (Fin 5)) (P : Subgroup orth.W) :
    (∀ w : orth.W, orth.act (g * d * g⁻¹) w * w⁻¹ ∈ mp g P) ↔
      ∀ w : orth.W, orth.act d w * w⁻¹ ∈ P := by
  constructor
  · intro h w
    have h1 := h (orth.act g w)
    rw [act_conj_comm, mem_mp, act_inv_act] at h1
    exact h1
  · intro h w
    have e := act_conj_comm g d (orth.act g⁻¹ w)
    rw [act_act_inv] at e
    rw [e]
    exact ⟨_, h _, rfl⟩

theorem trivOn_commW_z_iff {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {z : Perm (Fin 5)} (hz : IsCentInv D z) {d : Perm (Fin 5)} (hd : d ∈ D) :
    (∀ w : orth.W, orth.act d w * w⁻¹ ∈ commW orth (Subgroup.zpowers z) ⊤) ↔ d ∈ That D := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  obtain ⟨d0, rfl⟩ : ∃ d0, d = g * d0 * g⁻¹ := ⟨g⁻¹ * d * g, by group⟩
  have hd0 : d0 ∈ S5Syl := mem_cj_conj.mp hd
  rw [isCentInv_cj_std_iff.mp hz, commW_zpowers_cj, trivOn_conj, ← cj_That, That_std,
    mem_cj_conj]
  have h : ∀ d ∈ S5SylF, (∀ w : orth.W, orth.act d w * w⁻¹ ∈ commF zStd) ↔ d ∈ S5ThatF := by
    unfold commF zStd; decide +kernel
  rw [mem_S5That_iff, ← h d0 ((mem_S5Syl_iff d0).mp hd0)]
  exact forall_congr' fun w => by rw [mem_commW_zpowers_iff]

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
