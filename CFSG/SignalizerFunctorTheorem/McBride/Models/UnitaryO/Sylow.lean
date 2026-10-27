module

public import CFSG.Open.Catalog
import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Assembly
import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryO.GL3

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryO

theorem isMulCommutative_sylow_psu3 {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (R : Sylow r (PSU3 2 p)) : IsMulCommutative (R : Subgroup (PSU3 2 p)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hK : ¬ r ∣ Nat.card (GaloisField 2 (2 * p)) := by
    rw [GaloisField.card 2 (2 * p) (by have := hp.pos; omega)]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
    omega
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective (projSU3_surjective hp.one_le) r R
  rw [Sylow.coe_mapSurjective]
  have : IsMulCommutative ((S : Subgroup (SU3 hp.one_le)).map (SU3 hp.one_le).subtype) :=
    isMulCommutative_of_isPGroup_gl3 hr h5 hK (S.isPGroup'.map _)
  have : IsMulCommutative (S : Subgroup (SU3 hp.one_le)) :=
    .of_setLike_mul_comm fun a ha b hb => Subtype.ext
      (setLike_mul_comm (s := (S : Subgroup (SU3 hp.one_le)).map (SU3 hp.one_le).subtype)
        ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  infer_instance

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryO
