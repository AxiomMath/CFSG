module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5F48Tor
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5System
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigExt

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.Quasithin.H13.F48Rig CFSG.Quasithin.H13.F431.F48Rig
  CFSG.QuasithinUnique CFSG.Open CFSG.LieType.Universal.Unitary CFSG.GH74.BNPair
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Cartan

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 2)) [hζ : Fact ((ζ : F) ≠ 0)]

theorem exists_cartan_un5_quot :
    ∃ h ∈ (un5System hF ζ).B ⊓ (un5System hF ζ).N, ∀ y ∈ (un5System hF ζ).U,
      h * y * h⁻¹ = y → y = 1 := by
  obtain ⟨h0, hh0, hc0⟩ := exists_cartan_un5 hF ζ
  refine ⟨un5Proj h0, ⟨⟨h0, hh0.1, rfl⟩, ⟨h0, hh0.2, rfl⟩⟩, ?_⟩
  rintro _ ⟨u, hu0, rfl⟩ hc
  have hu : u ∈ unU hF 5 := hu0
  have hnorm : h0 * u * h0⁻¹ ∈ unU hF 5 := by
    obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
    have : Fact ((ζ' : F) ≠ 0) := ⟨hζ'⟩
    exact (Subgroup.mem_normalizer_iff.1
      (borel_le_normalizer_posUnipotent (un5_isCTGroupDatum hF ζ') hh0.1) u).1 hu
  have hker : h0 * u * h0⁻¹ * u⁻¹ ∈ (un5Proj (F := F) (f := 2)).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc, mul_inv_cancel]
  have hmemU : h0 * u * h0⁻¹ * u⁻¹ ∈ unU hF 5 :=
    (unU hF 5).mul_mem hnorm ((unU hF 5).inv_mem hu)
  have h1 : h0 * u * h0⁻¹ * u⁻¹ = 1 :=
    Subgroup.mem_bot.1 ((un5_U_inf_ker hF).le ⟨hmemU, hker⟩)
  have h2 : h0 * u * h0⁻¹ = u := mul_inv_eq_one.1 h1
  rw [hc0 u hu h2, map_one]

end Cartan

end CFSG.Quasithin.H13.F431.Un
