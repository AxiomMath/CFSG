module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier

public section

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.CentralExt

namespace CFSG.Quasithin.ASInputs

namespace C10KH

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem comm_mul_center_left {x b k : G} (hk : k ∈ Subgroup.center G) : ⁅x * k, b⁆ = ⁅x, b⁆ := by
  have hkb : k * b = b * k := (Subgroup.mem_center_iff.mp hk b).symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * k * b * (k⁻¹ * x⁻¹) * b⁻¹ = x * (k * b) * k⁻¹ * x⁻¹ * b⁻¹ := by group
    _ = x * (b * k) * k⁻¹ * x⁻¹ * b⁻¹ := by rw [hkb]
    _ = x * b * x⁻¹ * b⁻¹ := by group

theorem comm_mul_center_right {x y k : G} (hk : k ∈ Subgroup.center G) : ⁅x, y * k⁆ = ⁅x, y⁆ := by
  have hkx : k * x⁻¹ = x⁻¹ * k := (Subgroup.mem_center_iff.mp hk x⁻¹).symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * (y * k) * x⁻¹ * (k⁻¹ * y⁻¹) = x * y * (k * x⁻¹) * k⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * k) * k⁻¹ * y⁻¹ := by rw [hkx]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem injective_of_section {L S : Type*} [Group L] [Group S] (φ : L →* S)
    (hperf : commutator L = ⊤) (hker : φ.ker ≤ Subgroup.center L) (σ : S →* L)
    (hσ : ∀ g, φ (σ g) = g) : Function.Injective φ := by
  have hk : ∀ l : L, (σ (φ l))⁻¹ * l ∈ φ.ker := fun l => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
  have hcomm : commutator L ≤ σ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have e : ⁅a, b⁆ = ⁅σ (φ a), σ (φ b)⁆ := by
      calc ⁅a, b⁆ = ⁅σ (φ a) * ((σ (φ a))⁻¹ * a), σ (φ b) * ((σ (φ b))⁻¹ * b)⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅σ (φ a), σ (φ b)⁆ := by
            rw [comm_mul_center_left (hker (hk a)), comm_mul_center_right (hker (hk b))]
    rw [e, ← map_commutatorElement]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have htop : σ.range = ⊤ := top_le_iff.mp (hperf ▸ hcomm)
  intro x y hxy
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp (htop ▸ Subgroup.mem_top x)
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp (htop ▸ Subgroup.mem_top y)
  rw [hσ, hσ] at hxy
  rw [hxy]

end C10KH


theorem as_I_1_3_Sp4_holds : AS_I_1_3_Sp4 := by
  intro e he F _ _ hF L _ _ φ hφ hperf hker
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have : Group.IsPerfect (StatedSp 2 F) := SpClosed.isPerfect_statedSp 2 F hF4
  set Z := SymplecticHigher.spScalars 2 F
  have hZc : Z ≤ Subgroup.center (StatedSp 2 F) := SymplecticHigher.spScalars_le_center
  obtain ⟨σ, hσ⟩ := CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
    (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc)
    (SpClosed.psp_two_cover_trivial hF (by omega) le_rfl (fun _ => he))
    (fun E _ _ π hπ hcen hc => SpClosed.sp_exists_section_of_coprime E π hπ hcen hc) L φ hφ hker
  exact C10KH.injective_of_section φ hperf hker σ hσ

end CFSG.Quasithin.ASInputs
