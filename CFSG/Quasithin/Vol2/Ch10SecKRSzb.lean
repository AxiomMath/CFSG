module

public import CFSG.Quasithin.Vol2.Ch10SecC9S4c
public import CFSG.Quasithin.Vol2.Ch10SecKRSm
public import CFSG.Quasithin.Vol2.Ch10SecQ9H4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.VI_le_of (c : Conf T L I t w J) {X : Subgroup G}
    (hJX : J ≤ Subgroup.normalizer (X : Set G))
    (hX : fsuUL T L I ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) ≤ X) :
    VI T L I J w ≤ X := by
  refine conjClosure_le fun h hh z hz => ?_
  have hset : ((J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) : Subgroup G) : Set G) =
      (J : Set G) * ((T ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left J _ c.Tw_le_normalizer
  have hh' : h ∈ ((J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) : Subgroup G) : Set G) := hh
  rw [hset] at hh'
  obtain ⟨j, hj, τ, hτ, rfl⟩ := Set.mem_mul.mp hh'
  have hτz : τ * z * τ⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hz.2 τ hτ, mul_inv_cancel_right]
  rw [show j * τ * z * (j * τ)⁻¹ = j * (τ * z * τ⁻¹) * j⁻¹ by group, hτz]
  exact (Subgroup.mem_normalizer_iff.mp (hJX hj) z).mp (hX hz)

theorem Conf.u_mem_fsuUL (c : Conf T L I t w J) : t * w * t⁻¹ ∈ fsuUL T L I := by
  have h1 := c.claim.1
  rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L c.ht),
    SecA.mem_conjugate_iff] at h1
  exact h1

theorem Conf.u_ne_one (c : Conf T L I t w J) : t * w * t⁻¹ ≠ 1 := fun h => c.w_ne_one (by
  calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
    _ = 1 := by rw [h]; group)

theorem Conf.u_mem_fix (c : Conf T L I t w J)
    (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    t * w * t⁻¹ ∈ fsuUL T L I ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) :=
  ⟨Conf.u_mem_fsuUL c, Subgroup.mem_centralizer_iff.mpr fun _ hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (Conf.Tw_le_centralizer_u c hTw h37 h38 hs)⟩

theorem Conf.u_mem_VI (c : Conf T L I t w J)
    (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    t * w * t⁻¹ ∈ VI T L I J w :=
  le_conjClosure _ _ (Conf.u_mem_fix c hTw h37 h38)

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
