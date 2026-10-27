module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Refl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem zd_prod_shift (k : Fin 5) : L.z (D.delta (2 + k)) * L.z (D.delta (0 + k)) = D.x := by
  open Fin.NatCast Fin.CommRing in
  have hk : ((k.val : ℕ) : Fin 5) = k := Fin.cast_val_eq_self k
  have e : ∀ j : Fin 5, (D.x ^ k.val)⁻¹ * L.z (D.delta j) * D.x ^ k.val =
      L.z (D.delta (j + k)) := by
    intro j
    have := D.zd_conj_pow k.val j
    rwa [hk] at this
  have hxk : D.x * D.x ^ k.val = D.x ^ k.val * D.x :=
    (Commute.pow_right (Commute.refl D.x) k.val).eq
  have hxdef : D.x = L.z (D.delta 2) * L.z (D.delta 0) := rfl
  rw [← e 2, ← e 0]
  calc (D.x ^ k.val)⁻¹ * L.z (D.delta 2) * D.x ^ k.val *
        ((D.x ^ k.val)⁻¹ * L.z (D.delta 0) * D.x ^ k.val)
      = (D.x ^ k.val)⁻¹ * (L.z (D.delta 2) * L.z (D.delta 0)) * D.x ^ k.val := by group
    _ = (D.x ^ k.val)⁻¹ * (D.x * D.x ^ k.val) := by rw [← hxdef]; group
    _ = (D.x ^ k.val)⁻¹ * (D.x ^ k.val * D.x) := by rw [hxk]
    _ = D.x := by group

open Fin.NatCast Fin.CommRing in
@[expose] def shift (k : Fin 5) : D10Set L α where
  P i := D.P (i + k)
  val := D.val
  start i := D.start (i + k)
  inj := by
    intro i j hij
    have := D.inj hij
    simpa using this
  dih := by
    have hr : (Set.range fun i : Fin 5 => L.z ((D.P (i + k)).vert 4)) =
        Set.range fun i : Fin 5 => L.z ((D.P i).vert 4) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i + k, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨i - k, by simp⟩
    rw [hr]
    exact D.dih
  conj := by
    intro i
    show (L.z (D.delta (2 + k)) * L.z (D.delta (0 + k)))⁻¹ * L.z (D.delta (i + k)) *
      (L.z (D.delta (2 + k)) * L.z (D.delta (0 + k))) = L.z (D.delta (i + 1 + k))
    rw [D.zd_prod_shift k, add_right_comm]
    exact D.conj (i + k)

variable {D}

theorem shift_delta (k i : Fin 5) : (D.shift k).delta i = D.delta (i + k) := rfl

theorem shift_x (k : Fin 5) : (D.shift k).x = D.x := D.zd_prod_shift k

end D10Set

end CFSG.Quasithin.Fan86
