module

public import CFSG.Quasithin.EmptyFaithful.S143ND
public import CFSG.Quasithin.EmptyFaithful.S143NC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section Defs

variable {G : Type} [Group G]

@[expose] def tdOf (T : Subgroup G) (δ : G) : Subgroup G := T ⊓ Subgroup.centralizer ({δ} : Set G)

@[expose] def sdOf (T M : Subgroup G) (δ : G) : Subgroup G :=
  (rOf T M ⊔ qOf T) ⊓ Subgroup.centralizer ({δ} : Set G)

end Defs

section TD

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2)
  (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X))

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb

theorem isSylowTwoOf_tdOf_ch :
    IsSylowTwoOf (tdOf T δ) (mcOf T ⊓ Subgroup.centralizer ({δ} : Set G)) := by
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hT : IsSylowTwoOf T (mcOf T) := sylow_G1_of_hyp c.h1281
  have hN := oTwoUpper_mcOf_le_centralizer hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb
  have h := isSylowTwoOf_inf_of_pow_mem (X := mcOf T) (N := oTwoUpper (mcOf T))
    (C := mcOf T ⊓ Subgroup.centralizer ({δ} : Set G)) (T := T) hT
    (le_normalizer_oTwoUpper (mcOf T)) (le_inf (oTwoUpper_le _) hN) inf_le_left
    (fun w hw => exists_pow_mem_oTwoUpper (mcOf T) hw)
  have e : T ⊓ (mcOf T ⊓ Subgroup.centralizer ({δ} : Set G)) = tdOf T δ := by
    rw [← inf_assoc, inf_eq_left.mpr hTH]
    rfl
  rwa [e] at h

omit hemb in
theorem center_td_le {w : G} (hwT : w ∈ T) (hwδ : w * δ = δ * w)
    (hcen : ∀ u ∈ tdOf T δ, w * u = u * w) :
    w = 1 ∨ w = z ∨ w = δ ∨ w = z * δ := by
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hUT : ∀ u ∈ uOfL22 T M, u ∈ tdOf T δ := by
    intro u hu
    refine ⟨qOf_le_T_of_hyp c.h1281 (uOfL22_le_qOf c hu), Subgroup.mem_centralizer_iff.mpr
      fun h' hh' => ?_⟩
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact (Subgroup.mem_centralizer_iff.mp hδD.2 u hu).symm
  have hwQ : w ∈ qOf T :=
    c.mem_qOf_of_centralizes_uOfL22 (hTH hwT) fun u hu => (hcen u (hUT u hu)).symm
  have hwD : w ∈ dOf T M := ⟨hwQ, Subgroup.mem_centralizer_iff.mpr fun u hu => (hcen u (hUT u hu)).symm⟩
  exact centralizer_D_delta hS htT htRQ hM hP hVl hC1 hδD hδ hδA hwD hwδ

omit hemb in
theorem mem_mcOf_of_normalizer_td
    (hnc : ∀ x : G, x * z * x⁻¹ ≠ δ) (hnc' : ∀ x : G, x * z * x⁻¹ ≠ z * δ)
    {w : G} (hwδ : w ∈ Subgroup.centralizer ({δ} : Set G))
    (hwN : w ∈ Subgroup.normalizer (tdOf T δ : Set G)) : w ∈ mcOf T := by
  have hz := hS.z_mem
  have hz1 := hS.z_ne
  have hzTc := quasithinOmegaOneCenter_le_center T hz
  have hzT : z ∈ T := hzTc.1
  have hzcen : ∀ u ∈ T, u * z = z * u := fun u hu => Subgroup.mem_centralizer_iff.mp hzTc.2 u hu
  have hzδ : z * δ = δ * z := z_comm_dOf hS hδD
  have hzd : z ∈ tdOf T δ := ⟨hzT, Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact hzδ.symm⟩
  have hwδ' : w * δ = δ * w := (Subgroup.mem_centralizer_iff.mp hwδ δ rfl).symm
  have hwδ'' : w⁻¹ * δ * w = δ := by
    calc w⁻¹ * δ * w = w⁻¹ * (δ * w) := by group
      _ = w⁻¹ * (w * δ) := by rw [hwδ']
      _ = δ := by group
  have hw'd : w * z * w⁻¹ ∈ tdOf T δ := (Subgroup.mem_normalizer_iff.mp hwN z).mp hzd
  have hw'δ : (w * z * w⁻¹) * δ = δ * (w * z * w⁻¹) := by
    calc (w * z * w⁻¹) * δ = w * z * (w⁻¹ * δ * w) * w⁻¹ := by group
      _ = w * (z * δ) * w⁻¹ := by rw [hwδ'']; group
      _ = w * (δ * z) * w⁻¹ := by rw [hzδ]
      _ = (w * δ * w⁻¹) * (w * z * w⁻¹) := by group
      _ = δ * (w * z * w⁻¹) := by rw [hwδ']; group
  have hw'cen : ∀ u ∈ tdOf T δ, (w * z * w⁻¹) * u = u * (w * z * w⁻¹) := by
    intro u hu
    have hu' : w⁻¹ * u * w ∈ tdOf T δ := by
      refine (Subgroup.mem_normalizer_iff.mp hwN (w⁻¹ * u * w)).mpr ?_
      have : w * (w⁻¹ * u * w) * w⁻¹ = u := by group
      rw [this]; exact hu
    have h1 := hzcen _ hu'.1
    calc (w * z * w⁻¹) * u = w * (z * (w⁻¹ * u * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * u * w) * z) * w⁻¹ := by rw [h1]
      _ = u * (w * z * w⁻¹) := by group
  have hcases := center_td_le hS htT htRQ hM hP hVl hC1 hδD hδ hδA hw'd.1 hw'δ hw'cen
  have hwz : w * z * w⁻¹ = z := by
    rcases hcases with e | e | e | e
    · exact absurd (by
        have := congrArg (fun q => w⁻¹ * q * w) e
        simpa [mul_assoc] using this) hz1
    · exact e
    · exact absurd e (hnc w)
    · exact absurd e (hnc' w)
  have hwzc : w * z = z * w := by
    calc w * z = (w * z * w⁻¹) * w := by group
      _ = z * w := by rw [hwz]
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  rcases c.mem_Z_cases hz hz1 hu with rfl | rfl
  · simp
  · exact hwzc.symm

theorem isSylowTwoOf_tdOf_gd
    (hnc : ∀ x : G, x * z * x⁻¹ ≠ δ) (hnc' : ∀ x : G, x * z * x⁻¹ ≠ z * δ) :
    IsSylowTwoOf (tdOf T δ) (Subgroup.centralizer ({δ} : Set G)) :=
  isSylowTwoOf_of_normalizer_le (isSylowTwoOf_tdOf_ch hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb)
    inf_le_right fun _ hw hwN =>
      ⟨mem_mcOf_of_normalizer_td hS htT htRQ hM hP hVl hC1 hδD hδ hδA hnc hnc' hw hwN, hw⟩

end TD

end S143

end CFSG.Quasithin
