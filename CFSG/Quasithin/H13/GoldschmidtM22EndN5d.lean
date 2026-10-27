module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4c

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

omit [Finite G] in
include hk P in
theorem inter_conj_eq_Z (a : ↥(HH T)) (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V)
    (hg : P.ψ ⟨g, hk.g_mem⟩ * P.ψ a ≠ P.ψ a * P.ψ ⟨g, hk.g_mem⟩) {k : G} (hkH : k ∈ HH T)
    (hkN : k ∉ Subgroup.normalizer (V : Set G)) :
    V ⊓ conjSubgroup V k = quasithinOmegaOneCenter T := by
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  have hτ2 : (P.ψ a).support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hτ
  have hk' : P.ψ ⟨k, hkH⟩ * P.ψ a ≠ P.ψ a * P.ψ ⟨k, hkH⟩ := fun hc =>
    hkN ((hNa ⟨k, hkH⟩).mpr hc)
  rcases perm3_coset_cover _ _ (P.ψ ⟨k, hkH⟩) hτ2 hg with h1 | h2 | h3
  · exact absurd h1 hk'
  · have : conjSubgroup V k = conjSubgroup V g :=
      P.conjSubgroup_eq_of_comm a haV haC ⟨k, hkH⟩ ⟨g, hk.g_mem⟩
        (by simpa [map_mul, map_inv] using h2)
    rw [this]
    exact hk.inter_eq
  · have : conjSubgroup V k = conjSubgroup V ((g : G) * (a : G)) :=
      P.conjSubgroup_eq_of_comm a haV haC ⟨k, hkH⟩ (⟨g, hk.g_mem⟩ * a)
        (by simpa [map_mul, map_inv] using h3)
    rw [this]
    have hVa : conjSubgroup V (a : G) = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer haV)
    calc V ⊓ conjSubgroup V ((g : G) * (a : G))
        = conjSubgroup V (a : G) ⊓ conjSubgroup (conjSubgroup V g) (a : G) := by
          rw [hVa, conjSubgroup_conjSubgroup]
      _ = conjSubgroup (V ⊓ conjSubgroup V g) (a : G) :=
          (CFSG.QuasithinUnique.C5.conjSubgroup_inf _ _ _).symm
      _ = conjSubgroup (quasithinOmegaOneCenter T) (a : G) := by rw [hk.inter_eq]
      _ = quasithinOmegaOneCenter T :=
          conjSubgroup_eq_iff_mem_normalizer.mpr (HH_le_normalizer_Z T a.2)

omit [Finite G] in
include hk P in
theorem V1_inf_conj (a : ↥(HH T)) (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V)
    (hg : P.ψ ⟨g, hk.g_mem⟩ * P.ψ a ≠ P.ψ a * P.ψ ⟨g, hk.g_mem⟩) :
    conjSubgroup V g ⊓ conjSubgroup V ((g : G) * (a : G)) = quasithinOmegaOneCenter T := by
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  have hτ2 : (P.ψ a).support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hτ
  have hkH : (g : G) * (a : G) * (g : G)⁻¹ ∈ HH T :=
    (HH T).mul_mem ((HH T).mul_mem hk.g_mem a.2) ((HH T).inv_mem hk.g_mem)
  have hkN : (g : G) * (a : G) * (g : G)⁻¹ ∉ Subgroup.normalizer (V : Set G) := by
    intro hN
    have hc := (hNa ⟨(g : G) * (a : G) * (g : G)⁻¹, hkH⟩).mp hN
    have e : (⟨(g : G) * (a : G) * (g : G)⁻¹, hkH⟩ : ↥(HH T)) =
        ⟨g, hk.g_mem⟩ * a * ⟨g, hk.g_mem⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hc
    exact (perm3_noncomm_conj _ _ hτ2 hg).2 hc
  have h1 := inter_conj_eq_Z hk P a haV haC hg hkH hkN
  have h2 := congrArg (fun A => conjSubgroup A (g : G)) h1
  simp only [CFSG.QuasithinUnique.C5.conjSubgroup_inf, conjSubgroup_conjSubgroup] at h2
  have hk3 : (g : G) * (a : G) * (g : G)⁻¹ * (g : G) = (g : G) * (a : G) := by group
  rw [hk3, conjSubgroup_eq_iff_mem_normalizer.mpr (HH_le_normalizer_Z T hk.g_mem)] at h2
  exact h2

include hk P h hZ in
theorem comm_a_mem_V0 (a : ↥(HH T)) (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V)
    (hg : P.ψ ⟨g, hk.g_mem⟩ * P.ψ a ≠ P.ψ a * P.ψ ⟨g, hk.g_mem⟩) (ha2 : (a : G) ^ 2 = 1)
    (h6211 : Stmt6_2_11) {c : G} (hcD : c ∈ D)
    (hac : (a : G) * c * (a : G)⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T) :
    c ∈ V ⊓ CHU T L V := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hk.exists_mul_V0_V1 h hZ h6211 c hcD
  have huV : u ∈ V := (Subgroup.mem_inf.mp hu).1
  have huH : u ∈ HH T := V_le_HH h hZ huV
  have hwVg : w ∈ conjSubgroup V g := (Subgroup.mem_inf.mp hw).1
  have hau : (a : G) * u * (a : G)⁻¹ = u := by
    have := B2F.isElemAbelian_comm h.toHyp611.isElemAbelian haV huV
    rw [this]
    group
  have hy : (a : G) * w * (a : G)⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T := by
    have e1 : (a : G) * (u * w) * (a : G)⁻¹ * (u * w)⁻¹ =
        u * ((a : G) * w * (a : G)⁻¹ * w⁻¹) * u⁻¹ := by
      calc (a : G) * (u * w) * (a : G)⁻¹ * (u * w)⁻¹
          = ((a : G) * u * (a : G)⁻¹) * ((a : G) * w * (a : G)⁻¹) * w⁻¹ * u⁻¹ := by group
        _ = u * ((a : G) * w * (a : G)⁻¹) * w⁻¹ * u⁻¹ := by rw [hau]
        _ = u * ((a : G) * w * (a : G)⁻¹ * w⁻¹) * u⁻¹ := by group
    rw [e1] at hac
    have hzc := Z_central T ((HH T).inv_mem huH) hac
    have e2 : (a : G) * w * (a : G)⁻¹ * w⁻¹ =
        u⁻¹ * (u * ((a : G) * w * (a : G)⁻¹ * w⁻¹) * u⁻¹) * u := by group
    rw [e2, hzc, inv_mul_cancel_right]
    exact hac
  have hZVg : quasithinOmegaOneCenter T ≤ conjSubgroup V g := hk.inter_eq ▸ inf_le_right
  have haa : (a : G) * (a : G) = 1 := by rw [← pow_two]; exact ha2
  have hw' : (a : G) * w * (a : G)⁻¹ ∈ conjSubgroup V g ⊓ conjSubgroup V ((g : G) * (a : G)) := by
    refine ⟨?_, ?_⟩
    · have e3 : (a : G) * w * (a : G)⁻¹ = ((a : G) * w * (a : G)⁻¹ * w⁻¹) * w := by group
      rw [e3]
      exact (conjSubgroup V g).mul_mem (hZVg hy) hwVg
    · have hgw : (g : G) * w * (g : G)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hwVg
      refine mem_conjSubgroup_iff.mpr ?_
      have e4 : ((g : G) * (a : G)) * ((a : G) * w * (a : G)⁻¹) * ((g : G) * (a : G))⁻¹ =
          (g : G) * w * (g : G)⁻¹ := by
        calc ((g : G) * (a : G)) * ((a : G) * w * (a : G)⁻¹) * ((g : G) * (a : G))⁻¹
            = (g : G) * ((a : G) * (a : G)) * w * ((a : G) * (a : G))⁻¹ * (g : G)⁻¹ := by group
          _ = (g : G) * w * (g : G)⁻¹ := by rw [haa]; group
      rw [e4]
      exact hgw
  rw [V1_inf_conj hk P a haV haC hg] at hw'
  have hwZ : w ∈ quasithinOmegaOneCenter T := by
    have hzc := Z_central T ((HH T).inv_mem a.2) hw'
    have e5 : w = (a : G)⁻¹ * ((a : G) * w * (a : G)⁻¹) * (a : G) := by group
    rw [e5, hzc, inv_mul_cancel_right]
    exact hw'
  exact (V ⊓ CHU T L V).mul_mem hu (hk.Z_le_V0 h hZ hwZ)

end KData

end CFSG.Quasithin.H13.GM22
