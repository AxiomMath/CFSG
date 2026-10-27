module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerTorus

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Chevalley.ExceptionalCover
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

namespace TwE6Per

theorem rhoPerm_nd0 : rhoPerm (nd 0) = nd 5 := by decide

theorem rhoPerm_nd2 : rhoPerm (nd 2) = nd 4 := by decide

theorem rhoPerm_nd3 : rhoPerm (nd 3) = nd 3 := by decide


variable {k : Type} [Field k] (θ : k →+* k)

theorem isSymU_uOne (hθ : ∀ c, θ (θ c) = c) {μ : kˣ} (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) :
    IsSymU θ (uOne μ) := by
  have h := isSymU_mulSingle_pair θ hθ (c := nd 0) (by decide) μ
  rwa [rhoPerm_nd0, hθμ] at h

theorem isSymU_uTwo (hθ : ∀ c, θ (θ c) = c) {μ : kˣ} (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) :
    IsSymU θ (uTwo μ) := by
  have h := isSymU_mulSingle_pair θ hθ (c := nd 2) (by decide) μ
  rwa [rhoPerm_nd2, hθμ] at h

theorem chiHom_pair (c a b : Fin (Tag.rank .E6)) (μ : kˣ) :
    chiHom c (Pi.mulSingle a μ * Pi.mulSingle b μ⁻¹) =
      μ ^ (-Tag.cartan .E6 a c) * μ⁻¹ ^ (-Tag.cartan .E6 b c) := by
  rw [map_mul, chiHom_mulSingle, chiHom_mulSingle]

theorem conj_pair_torusHom {c : Fin (Tag.rank .E6)} (hdc : Tag.cartan .E6 (rhoPerm c) c = 0)
    {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) {v : Fin (Tag.rank .E6) → kˣ}
    (hv : u * Pi.mulSingle c (chiHom c u) *
      Pi.mulSingle (rhoPerm c) (Units.map (θ : k →* k) (chiHom c u)) = v) :
    e6Data_valid.nm k c * e6Data_valid.nm k (rhoPerm c) * torusHom k u *
      (e6Data_valid.nm k c * e6Data_valid.nm k (rhoPerm c))⁻¹ = torusHom k v := by
  rw [conj_torusHom_pair θ hdc hu, ← torusHom_mulSingle, ← torusHom_mulSingle, ← map_mul,
    ← map_mul, ← mul_assoc, hv]

variable {θ}

theorem units_map_zpow (μ : kˣ) (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) (m : ℤ) :
    Units.map (θ : k →* k) (μ ^ m) = μ ^ (-m) := by
  rw [map_zpow, hθμ, inv_zpow', zpow_neg]

theorem chiHom_uOne_nd0 (μ : kˣ) : chiHom (nd 0) (uOne μ) = μ ^ (-2 : ℤ) := by
  rw [uOne, chiHom_pair, show Tag.cartan .E6 (nd 0) (nd 0) = 2 by decide,
    show Tag.cartan .E6 (nd 5) (nd 0) = 0 by decide]
  simp

theorem chiHom_uTwo_nd0 (μ : kˣ) : chiHom (nd 0) (uTwo μ) = μ ^ (1 : ℤ) := by
  rw [uTwo, chiHom_pair, show Tag.cartan .E6 (nd 2) (nd 0) = -1 by decide,
    show Tag.cartan .E6 (nd 4) (nd 0) = 0 by decide]
  simp

theorem chiHom_uTwo_nd2 (μ : kˣ) : chiHom (nd 2) (uTwo μ) = μ ^ (-2 : ℤ) := by
  rw [uTwo, chiHom_pair, show Tag.cartan .E6 (nd 2) (nd 2) = 2 by decide,
    show Tag.cartan .E6 (nd 4) (nd 2) = 0 by decide]
  simp

theorem chiHom_uOne_nd2 (μ : kˣ) : chiHom (nd 2) (uOne μ) = μ ^ (1 : ℤ) := by
  rw [uOne, chiHom_pair, show Tag.cartan .E6 (nd 0) (nd 2) = -1 by decide,
    show Tag.cartan .E6 (nd 5) (nd 2) = 0 by decide]
  simp

theorem conj_N1_t1 (hθ : ∀ c, θ (θ c) = c) {μ : kˣ} (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) :
    e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) * torusHom k (uOne μ) *
      (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5))⁻¹ = (torusHom k (uOne μ))⁻¹ := by
  have h := conj_pair_torusHom θ (c := nd 0) (by decide) (isSymU_uOne θ hθ hθμ)
    (v := (uOne μ)⁻¹) (by
      rw [chiHom_uOne_nd0, units_map_zpow μ hθμ, rhoPerm_nd0, uOne]
      funext a
      fin_cases a <;> simp [Fin.ext_iff] <;> group)
  rw [rhoPerm_nd0] at h
  rw [h, map_inv]

theorem conj_N1_t2 (hθ : ∀ c, θ (θ c) = c) {μ : kˣ} (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) :
    e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) * torusHom k (uTwo μ) *
      (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5))⁻¹ =
        torusHom k (uTwo μ) * torusHom k (uOne μ) := by
  have h := conj_pair_torusHom θ (c := nd 0) (by decide) (isSymU_uTwo θ hθ hθμ)
    (v := uTwo μ * uOne μ) (by
      rw [chiHom_uTwo_nd0, units_map_zpow μ hθμ, rhoPerm_nd0, uOne, uTwo]
      funext a
      fin_cases a <;> simp [Fin.ext_iff])
  rw [rhoPerm_nd0] at h
  rw [h, map_mul]

theorem conj_N2_t2 (hθ : ∀ c, θ (θ c) = c) {μ : kˣ} (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) :
    e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) * torusHom k (uTwo μ) *
      (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹ = (torusHom k (uTwo μ))⁻¹ := by
  have h := conj_pair_torusHom θ (c := nd 2) (by decide) (isSymU_uTwo θ hθ hθμ)
    (v := (uTwo μ)⁻¹) (by
      rw [chiHom_uTwo_nd2, units_map_zpow μ hθμ, rhoPerm_nd2, uTwo]
      funext a
      fin_cases a <;> simp [Fin.ext_iff] <;> group)
  rw [rhoPerm_nd2] at h
  rw [h, map_inv]

theorem conj_N2_t1 (hθ : ∀ c, θ (θ c) = c) {μ : kˣ} (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) :
    e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) * torusHom k (uOne μ) *
      (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹ =
        torusHom k (uOne μ) * torusHom k (uTwo μ) := by
  have h := conj_pair_torusHom θ (c := nd 2) (by decide) (isSymU_uOne θ hθ hθμ)
    (v := uOne μ * uTwo μ) (by
      rw [chiHom_uOne_nd2, units_map_zpow μ hθμ, rhoPerm_nd2, uOne, uTwo]
      funext a
      fin_cases a <;> simp [Fin.ext_iff])
  rw [rhoPerm_nd2] at h
  rw [h, map_mul]

end TwE6Per

end CFSG.StandardType
