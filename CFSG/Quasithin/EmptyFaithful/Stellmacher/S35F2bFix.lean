module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2bSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2bDef
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin5

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2b

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

@[expose] def ellO (p : Fin 5) : Subgroup orth.W := Subgroup.zpowers (vp p)

theorem mem_ellO {p : Fin 5} {w : orth.W} : w ∈ ellO p ↔ w = 1 ∨ w = vp p :=
  mem_zpowers_iff_of_mul_self (vp_mul_self p)

theorem card_ellO (p : Fin 5) : Nat.card (ellO p) = 2 := card_zpowers_vp p

theorem key_fix4 : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup → ∀ w : orth.W,
    (orth.act (swap a c * swap c b * swap b d) w * w⁻¹ = 1 ∨
      orth.act (swap a c * swap c b * swap b d) w * w⁻¹ = vp p) →
    (w = 1 ∨ w = ep a b ∨ w = ep c d ∨ w = vp p) := by
  decide +kernel

theorem cyc_comm : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup →
    (swap a c * swap c b * swap b d) * (swap a b * swap c d) =
      (swap a b * swap c d) * (swap a c * swap c b * swap b d) := by
  decide +kernel

variable {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
  (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
  (hdec : z = swap a b * swap c d)

include hD hz h hdec

theorem fixQ_orth : fixQ orth D (ellO p) = commW orth (Subgroup.zpowers z) ⊤ := by
  ext w
  rw [← commW_That_eq_commW_z hD hz h hdec, mem_commW_That_iff hD hz h hdec]
  constructor
  · intro hw
    have hg : (swap a c * swap c b * swap b d) ∈ D := by
      rw [mem_sylow_iff_comm hD hz, hdec]; exact cyc_comm a b c d p h
    exact key_fix4 a b c d p h w (mem_ellO.mp (hw _ hg))
  · intro hw x hx
    rw [mem_ellO]
    rcases hw with rfl | rfl | rfl | rfl
    · left; simp
    · by_cases hxT : x ∈ That D
      · left; rw [(act_ep_ab_iff hD hz h hdec hx).mpr hxT]; exact mul_inv_cancel _
      · right; exact act_ep_ab_mul_inv hD hz h hdec hx hxT
    · by_cases hxT : x ∈ That D
      · left; rw [(act_ep_cd_iff hD hz h hdec hx).mpr hxT]; exact mul_inv_cancel _
      · right; exact act_ep_cd_mul_inv hD hz h hdec hx hxT
    · left
      rw [act_vp, isFixPt_p hD hz h hdec x hx]; exact mul_inv_cancel _

theorem card_fixQ_orth : Nat.card (fixQ orth D (ellO p)) = 2 * Nat.card (ellO p) := by
  rw [fixQ_orth hD hz h hdec, card_commW_z hD hz, card_ellO]

omit hD hz h hdec

end CFSG.Quasithin.F53.Stellmacher.S35.F2b
