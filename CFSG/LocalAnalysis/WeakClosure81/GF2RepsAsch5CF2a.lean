module

public import CFSG.Quasithin.Background.A3Structure38Facts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin

theorem isSolvable_quotient_of_outSolvable {K : Type} [Group K] (F : Subgroup K) [F.Normal]
    (hC : Subgroup.centralizer (F : Set K) ≤ F) (hout : OutSolvable ↥F) :
    Group.IsSolvable (K ⧸ F) := by
  obtain ⟨n, hn⟩ := hout
  have hle : derivedSeries K n ≤ F := by
    intro k hk
    have h1 : (MulAut.conjNormal : K →* MulAut ↥F) k ∈ derivedSeries (MulAut ↥F) n :=
      (map_derivedSeries_le_derivedSeries _ n) (Subgroup.mem_map_of_mem _ hk)
    obtain ⟨f, hf⟩ := hn h1
    have hmem : (f : K)⁻¹ * k ∈ Subgroup.centralizer (F : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg (fun φ : MulAut ↥F => ((φ ⟨x, hx⟩ : ↥F) : K)) hf
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulAut.conj_apply, MulAut.conjNormal_apply,
        Subgroup.coe_mul, InvMemClass.coe_inv] at h2
      calc x * ((f : K)⁻¹ * k) = (f : K)⁻¹ * (f * x * (f : K)⁻¹) * f * ((f : K)⁻¹ * k) := by group
        _ = (f : K)⁻¹ * (k * x * k⁻¹) * f * ((f : K)⁻¹ * k) := by rw [h2]
        _ = ((f : K)⁻¹ * k) * x := by group
    have h3 : (f : K)⁻¹ * k ∈ F := hC hmem
    have hk' : k = (f : K) * ((f : K)⁻¹ * k) := by group
    rw [hk']
    exact F.mul_mem f.2 h3
  refine ⟨⟨n, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective F) n, eq_bot_iff]
  rintro _ ⟨k, hk, rfl⟩
  simpa using (QuotientGroup.eq_one_iff k).mpr (hle hk)

end CFSG.LocalAnalysis.WeakClosure81
