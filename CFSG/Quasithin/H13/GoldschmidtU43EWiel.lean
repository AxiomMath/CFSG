module

public import CFSG.Quasithin.H13.GoldschmidtU43EMg
public import CFSG.Quasithin.H13.GoldschmidtU43DOrb
public import CFSG.Quasithin.H13.GoldschmidtU43DUz

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem card_inf_centralizer_conj (K : Subgroup G) {g : G} (hg : ∀ x, x ∈ K ↔ g * x * g⁻¹ ∈ K)
    (y : G) : Nat.card ↥(K ⊓ Subgroup.centralizer ({g * y * g⁻¹} : Set G)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({y} : Set G)) := by
  have hmap : (K ⊓ Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      K ⊓ Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwK, hwc⟩ := Subgroup.mem_inf.mp hw
      have hwc' := Subgroup.mem_centralizer_singleton_iff.mp hwc
      refine ⟨(hg w).1 hwK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      show g * w * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * w * g⁻¹)
      calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
        _ = g * (y * w) * g⁻¹ := by rw [hwc']
        _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group
    · rintro ⟨hxK, hxc⟩
      have hxc' := Subgroup.mem_centralizer_singleton_iff.mp hxc
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      refine ⟨g⁻¹ * x * g, Subgroup.mem_inf.mpr ⟨(hg _).2 (by rw [e]; exact hxK),
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, e⟩
      calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [hxc']
        _ = y * (g⁻¹ * x * g) := by group
  rw [← hmap]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_Hz_conj (z k : G) : Nat.card ↥(Hz (k * z * k⁻¹)) = Nat.card ↥(Hz z) := by
  rw [Hz_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj k).injective

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

theorem conj_v_u_H : S.v⁻¹ * S.u * S.v = S.u * zK z := by
  have h := S.jw.r13
  rw [S.ui] at h
  calc S.v⁻¹ * S.u * S.v = (S.u * S.v * S.u) * S.u * S.v := by rw [h]
    _ = S.u * S.v * (S.u * S.u) * S.v := by group
    _ = S.u * (S.v * S.v) := by rw [S.uu]; group
    _ = S.u * zK z := by rw [S.vv]

theorem u_mul_σ₁ : S.u * S.σ₁ = S.σ₂ * S.u := by
  unfold σ₂
  rw [S.ui]
  calc S.u * S.σ₁ = S.u * S.σ₁ * (S.u * S.u) := by rw [S.uu, mul_one]
    _ = S.u * S.σ₁ * S.u * S.u := by group

theorem u_mul_σ₂ : S.u * S.σ₂ = S.σ₁ * S.u := by
  unfold σ₂
  group

theorem u_comm_σ₁σ₂ : S.u * (S.σ₁ * S.σ₂) = (S.σ₁ * S.σ₂) * S.u := by
  calc S.u * (S.σ₁ * S.σ₂) = (S.u * S.σ₁) * S.σ₂ := by group
    _ = S.σ₂ * (S.u * S.σ₂) := by rw [S.u_mul_σ₁]; group
    _ = S.σ₂ * (S.σ₁ * S.u) := by rw [S.u_mul_σ₂]
    _ = (S.σ₂ * S.σ₁) * S.u := by group
    _ = (S.σ₁ * S.σ₂) * S.u := by rw [S.σ₁σ₂_comm]

theorem u_sq : (S.u : G) * S.u = 1 := congrArg Subtype.val S.uu

theorem u_comm_z : Commute z (S.u : G) := (z_comm_H S.u).symm

theorem u_normalizer_Tg : (S.u : G) ∈ Subgroup.normalizer (S.Tg : Set G) :=
  S.normalizer_Tg S.hu

theorem v_normalizer_Tg : (S.v : G) ∈ Subgroup.normalizer (S.Tg : Set G) :=
  S.normalizer_Tg S.hv

variable [Finite G]

theorem normalizer_Mg_iff {g : G} (hg : g ∈ Subgroup.normalizer (S.Tg : Set G))
    (x : G) : x ∈ S.Mg ↔ g * x * g⁻¹ ∈ S.Mg := by
  constructor
  · exact S.conj_mem_Mg hg
  · intro h
    have := S.conj_mem_Mg ((Subgroup.normalizer (S.Tg : Set G)).inv_mem hg) h
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem u_ne_one : (S.u : G) ≠ 1 := by
  intro h
  apply S.act_u_ne_one
  have : S.u = 1 := Subtype.ext h
  rw [this, map_one]

theorem u_ne_z : (S.u : G) ≠ z := by
  intro h
  apply S.act_u_ne_one
  have : S.u = zK z := Subtype.ext h
  rw [this, S.act_zK]

theorem exists_conj_u : ∃ k : G, k * z * k⁻¹ = (S.u : G) := by
  obtain ⟨k, -, hk⟩ := S.e.swap.exists_conj_to_z S.e.ha S.huE S.u_ne_one
  exact ⟨k, hk⟩

theorem card_Hz_u : Nat.card ↥(Hz (S.u : G)) = 1152 := by
  obtain ⟨k, hk⟩ := S.exists_conj_u
  rw [← hk, card_Hz_conj]
  exact S.hyp.card_H

end JWSetup

end CFSG.Quasithin.H13.U43
