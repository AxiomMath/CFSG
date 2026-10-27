module

public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.S15221

open Equiv Equiv.Perm CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type*} [Group G]

section Pi

variable (K : Subgroup G) (e : OTwoQuot K ≃* alternatingGroup (Fin 8)) (g0 : Perm (Fin 8))

@[expose] def piK : ↥K →* Perm (Fin 8) :=
  (MulAut.conj g0).toMonoidHom.comp ((alternatingGroup (Fin 8)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))))

theorem piK_apply (x : ↥K) :
    piK K e g0 x =
      g0 * ((e (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : Perm (Fin 8)) * g0⁻¹ := rfl

theorem piK_eq_one_iff {x : ↥K} : piK K e g0 x = 1 ↔ x ∈ CFSG.Open.pCore 2 ↥K := by
  rw [piK_apply, mul_inv_eq_one, mul_eq_left]
  constructor
  · intro h
    have h1 : e (QuotientGroup.mk x) = 1 := Subtype.ext h
    exact (QuotientGroup.eq_one_iff x).mp (e.injective (h1.trans (map_one e).symm))
  · intro h
    have : (QuotientGroup.mk x : OTwoQuot K) = 1 := (QuotientGroup.eq_one_iff x).mpr h
    rw [this, map_one]
    rfl

theorem piK_mem_alternating (hg0 : g0 ∈ alternatingGroup (Fin 8)) (x : ↥K) :
    piK K e g0 x ∈ alternatingGroup (Fin 8) := by
  rw [piK_apply]
  exact (alternatingGroup (Fin 8)).mul_mem ((alternatingGroup (Fin 8)).mul_mem hg0
    (e (QuotientGroup.mk x)).2) ((alternatingGroup (Fin 8)).inv_mem hg0)

theorem exists_piK_eq (hg0 : g0 ∈ alternatingGroup (Fin 8)) {c : Perm (Fin 8)}
    (hc : c ∈ alternatingGroup (Fin 8)) : ∃ x : ↥K, piK K e g0 x = c := by
  have hc' : g0⁻¹ * c * g0 ∈ alternatingGroup (Fin 8) :=
    (alternatingGroup (Fin 8)).mul_mem ((alternatingGroup (Fin 8)).mul_mem
      ((alternatingGroup (Fin 8)).inv_mem hg0) hc) hg0
  obtain ⟨q, hq⟩ := e.surjective ⟨g0⁻¹ * c * g0, hc'⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨x, ?_⟩
  rw [piK_apply, hq]
  group

theorem piK_conj_eq_one {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {w : G} (hw : w ∈ K)
    (hw' : g * w * g⁻¹ ∈ K) (h : piK K e g0 ⟨w, hw⟩ = 1) : piK K e g0 ⟨g * w * g⁻¹, hw'⟩ = 1 := by
  rw [piK_eq_one_iff] at h ⊢
  have hmem : w ∈ pCoreOf 2 K := ⟨⟨w, hw⟩, h, rfl⟩
  have h2 : g * w * g⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K hg) w).mp hmem
  obtain ⟨y, hy, hyw⟩ := h2
  have : y = ⟨g * w * g⁻¹, hw'⟩ := Subtype.ext hyw
  rwa [this] at hy

theorem comm_conj_aux {Γ : Type*} [Group Γ] (π : ↥K →* Γ) {g : G}
    (hker : ∀ (w : G) (hw : w ∈ K) (hw' : g * w * g⁻¹ ∈ K), π ⟨w, hw⟩ = 1 →
      π ⟨g * w * g⁻¹, hw'⟩ = 1)
    {x z : G} (hx : x ∈ K) (hz : z ∈ K) (hx' : g * x * g⁻¹ ∈ K) (hz' : g * z * g⁻¹ ∈ K)
    (hxz : π ⟨x, hx⟩ * π ⟨z, hz⟩ = π ⟨z, hz⟩ * π ⟨x, hx⟩) :
    π ⟨g * x * g⁻¹, hx'⟩ * π ⟨g * z * g⁻¹, hz'⟩ = π ⟨g * z * g⁻¹, hz'⟩ * π ⟨g * x * g⁻¹, hx'⟩ := by
  set X : ↥K := ⟨x, hx⟩
  set Z : ↥K := ⟨z, hz⟩
  set X' : ↥K := ⟨g * x * g⁻¹, hx'⟩
  set Z' : ↥K := ⟨g * z * g⁻¹, hz'⟩
  have hw : x * z * x⁻¹ * z⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hx hz) (K.inv_mem hx)) (K.inv_mem hz)
  have hw' : g * (x * z * x⁻¹ * z⁻¹) * g⁻¹ ∈ K := by
    have : g * (x * z * x⁻¹ * z⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * z * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * z * g⁻¹)⁻¹ := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx' hz') (K.inv_mem hx')) (K.inv_mem hz')
  have h1 : π ⟨x * z * x⁻¹ * z⁻¹, hw⟩ = 1 := by
    have : (⟨x * z * x⁻¹ * z⁻¹, hw⟩ : ↥K) = X * Z * X⁻¹ * Z⁻¹ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hxz]
    group
  have h2 := hker _ hw hw' h1
  have h3 : (⟨g * (x * z * x⁻¹ * z⁻¹) * g⁻¹, hw'⟩ : ↥K) = X' * Z' * X'⁻¹ * Z'⁻¹ :=
    Subtype.ext (by
      show g * (x * z * x⁻¹ * z⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * z * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * z * g⁻¹)⁻¹
      group)
  rw [h3, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  calc π X' * π Z' = (π X' * π Z' * (π X')⁻¹ * (π Z')⁻¹) * (π Z' * π X') := by group
    _ = π Z' * π X' := by rw [h2, one_mul]

theorem piK_congr {x y : G} (hx : x ∈ K) (hy : y ∈ K) (h : x = y) :
    piK K e g0 ⟨x, hx⟩ = piK K e g0 ⟨y, hy⟩ := by
  subst h
  rfl

end Pi

end CFSG.Quasithin.S15221
