module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Tr
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Gen

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.LieType.BorelTits

theorem wd_nil : wd [] = 1 := rfl

theorem rkIdx_of_cards {W : Type} [CommGroup W] [Finite W] (U : Subgroup W) {a b : ℕ}
    (hW : Nat.card W = 2 ^ b) (hU : Nat.card U = 2 ^ a) : rkIdx U = b - a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := rk_add_rkIdx U
  unfold rk at h
  rw [hW, hU, padicValNat.prime_pow, padicValNat.prime_pow] at h
  omega

theorem pCoreOf_map_injective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (P : Subgroup G) :
    pCoreOf 2 (P.map f) = (pCoreOf 2 P).map f := by
  unfold pCoreOf
  let φ : ↥P ≃* ↥(P.map f) := P.equivMapOfInjective f hf
  rw [← map_pCore_mulEquiv 2 φ, Subgroup.map_map, Subgroup.map_map]
  congr 1

section Conj

variable {W : Type} [CommGroup W]

theorem cg_apply_self (c a : MulAut W) : cg c a = c * a * c⁻¹ := by
  ext x
  simp [cg, MulAut.congr_apply]

theorem map_cg_of_mem {X : Subgroup (MulAut W)} {k : MulAut W} (hk : k ∈ X) :
    X.map (cg k) = X := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [cg_apply_self]
    exact mul_mem (mul_mem hk hx) (inv_mem hk)
  · intro hy
    refine ⟨k⁻¹ * y * k, mul_mem (mul_mem (inv_mem hk) hy) hk, ?_⟩
    rw [cg_apply_self]
    group

end Conj

end CFSG.Quasithin.H13.U3.GC137.S2
