module

public import CFSG.Quasithin.H13.L32NKGSp6Wit
public import CFSG.Quasithin.H13.L32NKGSp6Darboux
public import CFSG.Quasithin.H13.L32NKGSp6Transport

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

theorem kgSp6Order12096_of_checks
    (h1 : countCheck 64 1451520 = true) (h2 : normCheck 64 s0 n0List = true)
    (h3 : witCheck 64 KGCert.g22Elems n0List 6047 = true) : KGCert.KGSp6Order12096 := by
  intro V _ _ _ B hBalt hBnd hdim Γ hΓB hcard
  obtain ⟨b, hb⟩ := exists_darboux B hBalt hBnd hdim
  have hΓ₀card : Nat.card (Γ.map (phi b)) = 12096 := by
    rw [Subgroup.card_map_of_injective (phi_injective b), hcard]
  have hΓ₀ : Γ.map (phi b) ≤ SpU := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact isIso_toMatrix b B hb (hΓB γ hγ)
  obtain ⟨c, hcSp, hP0⟩ := exists_conj_sub h1 hΓ₀ hΓ₀card
  have hΓ₁card : Nat.card ((Γ.map (phi b)).map (MulAut.conj c).toMonoidHom) = 12096 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hΓ₀card]
  have hΓ₁ : (Γ.map (phi b)).map (MulAut.conj c).toMonoidHom ≤ SpU := by
    rintro _ ⟨x, hx, rfl⟩
    exact SpU.mul_mem (SpU.mul_mem hcSp (hΓ₀ hx)) (SpU.inv_mem hcSp)
  have hG := eq_Gsub h2 h3 hΓ₁ hΓ₁card hP0
  obtain ⟨e, he⟩ := phi_surjective b c⁻¹
  refine ⟨b.map e, fun M => ?_⟩
  have hconj : ∀ γ : V ≃ₗ[ZMod 2] V, LinearMap.toMatrix (b.map e) (b.map e)
      (γ : V →ₗ[ZMod 2] V) = ((MulAut.conj c (phi b γ) : Mat6ˣ) : Mat6) := by
    intro γ
    rw [toMatrix_map, map_mul, map_mul, map_inv, he, inv_inv, MulAut.conj_apply]
  constructor
  · intro hM
    obtain ⟨u, hu⟩ := isUnit_of_isIso (KGCert.g22Mats_isometry M hM)
    have huG : u ∈ Gsub := by
      rw [mem_Gsub, hu]
      exact hM
    rw [← hG] at huG
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγu⟩ := huG
    refine ⟨γ, hγ, ?_⟩
    rw [hconj]
    exact (congrArg Units.val hγu).trans hu
  · rintro ⟨γ, hγ, rfl⟩
    rw [hconj]
    have hmem : MulAut.conj c (phi b γ) ∈ (Γ.map (phi b)).map (MulAut.conj c).toMonoidHom :=
      ⟨phi b γ, ⟨γ, hγ, rfl⟩, rfl⟩
    rw [hG] at hmem
    exact hmem

end CFSG.Quasithin.H13.KGSp6
