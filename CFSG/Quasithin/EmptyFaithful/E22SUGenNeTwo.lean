module

public import CFSG.Quasithin.EmptyFaithful.E22SUGen
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.Quasithin.E22S

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank (StatedSU)

variable {K : Type} [Field K]

theorem iSup_suStab_eq_top_of_ne_two [Finite K] {q : ℕ} (hq : q ≠ 2) (hK : Nat.card K = q ^ 2) :
    (⨆ k : Fin 3, suStab K q k) = ⊤ := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := su3_exists_prime_pow hK
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have h3 := exists_norm_ne_one hK hq
  have hall := su3_iSup_stabilizer_eq_top hσ h3
  let e : SUid (unitaryInvolution K p f) 3 ≃* StatedSU 3 (p ^ f) K :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)
  have hmap : ∀ k : Fin 3, (MulAction.stabilizer (SUid (unitaryInvolution K p f) 3)
      (Pi.single k (1 : K) : Fin 3 → K)).map e.toMonoidHom = suStab K (p ^ f) k := by
    intro k
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_suStab.mpr (MulAction.mem_stabilizer_iff.mp hy)
    · intro hx
      exact ⟨e.symm x, MulAction.mem_stabilizer_iff.mpr (mem_suStab.mp hx),
        e.apply_symm_apply x⟩
  rw [← iSup_congr hmap, ← Subgroup.map_iSup, hall, Subgroup.map_top_of_surjective _ e.surjective]

end CFSG.Quasithin.E22S
