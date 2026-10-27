module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_n19_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y hxy
  exact IntMod.val_injective
    (mul_inv_eq_one.1 (Subgroup.mem_bot.1 ((mkTil_eq_iff ⊥ V hV x y).1 hxy)))

private theorem s16c167_n19_imgTil_inj {V U U' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : U ≤ V) (hU' : U' ≤ V) (h : imgTil ⊥ V hV U = imgTil ⊥ V hV U') : U = U' := by
  have hmkTil_inj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
    s16c167_n19_mkTil_bot_injective hV
  have hmain : (intSub V hV U).map (mkTil (⊥ : Subgroup G) V hV) =
      (intSub V hV U').map (mkTil (⊥ : Subgroup G) V hV) := h
  have h1 : intSub V hV U = intSub V hV U' := by
    have hc := congrArg (Subgroup.comap (mkTil (⊥ : Subgroup G) V hV)) hmain
    rw [Subgroup.comap_map_eq_self_of_injective hmkTil_inj,
      Subgroup.comap_map_eq_self_of_injective hmkTil_inj] at hc
    exact hc
  have h2 : (U.subgroupOf V).map V.subtype = (U'.subgroupOf V).map V.subtype := by
    simpa only [intSub] using congrArg (Subgroup.map V.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hU, Subgroup.map_subgroupOf_eq_of_le hU'] at h2

private theorem s16c167_n19_conjSubgroup_centralizer_singleton {g u m : G}
    (hm : m = g * u * g⁻¹) :
    conjSubgroup (Subgroup.centralizer ({m} : Set G)) g =
      Subgroup.centralizer ({u} : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : g * (x * u) * g⁻¹ = g * (u * x) * g⁻¹ := by
      calc g * (x * u) * g⁻¹ = (g * x * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by rw [← hm]; exact h
        _ = g * (u * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro h
    rw [hm]
    calc (g * x * g⁻¹) * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [h]
      _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group

theorem s16c167_unique_of_tilde (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : D.M ≤ normalizer (V : Set G)) {g : G} {Δ : Set (Subgroup G)}
    (hΔV : ∀ I ∈ Δ, I ≤ V) {Δt : Set (Subgroup (Vtil (⊥ : Subgroup G) V hV))}
    (hΔt : ∀ I ∈ Δ, imgTil ⊥ V hV I ∈ Δt) (hU : Uniq19 (Mbar D.M ⊥ V hV) Δt) :
    Unique19 D V g Δ := by
  intro u hu z hz hnu hnz I hI hIu hIz
  obtain ⟨J, hJΔ, rfl⟩ := hI
  set m : G := g * u * g⁻¹ with hm
  set n : G := g * z * g⁻¹ with hn
  have hmM : m ∈ D.M := by rw [hm]; exact mem_conjSubgroup_iff.1 hu.2
  have hnM : n ∈ D.M := by rw [hn]; exact mem_conjSubgroup_iff.1 hz.2
  have hmV : m ∈ normalizer (V : Set G) := hM hmM
  have hnV : n ∈ normalizer (V : Set G) := hM hnM
  have hm_stab : m ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot hmV
  have hn_stab : n ∈ stabTil (⊥ : Subgroup G) V := s16c167_mem_stabTil_bot hnV
  have hm2 : m ^ 2 = 1 := by
    rw [pow_two, hm]
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [← pow_two, hV.2 u hu.1]; group
  have hn2 : n ^ 2 = 1 := by
    rw [pow_two, hn]
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [← pow_two, hV.2 z hz.1]; group
  have huz : u * z = z * u :=
    congrArg Subtype.val (hV.1.is_comm.comm ⟨u, hu.1⟩ ⟨z, hz.1⟩)
  have hmn : m * n = n * m := by
    rw [hm, hn]
    calc (g * u * g⁻¹) * (g * z * g⁻¹) = g * (u * z) * g⁻¹ := by group
      _ = g * (z * u) * g⁻¹ := by rw [huz]
      _ = (g * z * g⁻¹) * (g * u * g⁻¹) := by group
  have hCm : conjSubgroup (Subgroup.centralizer ({m} : Set G)) g =
      Subgroup.centralizer ({u} : Set G) := s16c167_n19_conjSubgroup_centralizer_singleton hm
  have hCn : conjSubgroup (Subgroup.centralizer ({n} : Set G)) g =
      Subgroup.centralizer ({z} : Set G) := s16c167_n19_conjSubgroup_centralizer_singleton hn
  set t₁ : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨m, hm_stab⟩ with ht₁
  set t₂ : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨n, hn_stab⟩ with ht₂
  have ht₁_mem : t₁ ∈ Mbar D.M (⊥ : Subgroup G) V hV := by
    rw [ht₁]; exact actTil_mem_barSub (⊥ : Subgroup G) V hV hmM hm_stab
  have ht₂_mem : t₂ ∈ Mbar D.M (⊥ : Subgroup G) V hV := by
    rw [ht₂]; exact actTil_mem_barSub (⊥ : Subgroup G) V hV hnM hn_stab
  have ht₁2 : t₁ * t₁ = 1 := by
    have hmul : (⟨m, hm_stab⟩ : stabTil (⊥ : Subgroup G) V) * ⟨m, hm_stab⟩ = 1 := by
      ext
      show m * m = 1
      rw [← pow_two]; exact hm2
    rw [ht₁, ← map_mul, hmul, map_one]
  have ht₂2 : t₂ * t₂ = 1 := by
    have hmul : (⟨n, hn_stab⟩ : stabTil (⊥ : Subgroup G) V) * ⟨n, hn_stab⟩ = 1 := by
      ext
      show n * n = 1
      rw [← pow_two]; exact hn2
    rw [ht₂, ← map_mul, hmul, map_one]
  have ht₁₂ : t₁ * t₂ = t₂ * t₁ := by
    have hmul : (⟨m, hm_stab⟩ : stabTil (⊥ : Subgroup G) V) * ⟨n, hn_stab⟩ =
        (⟨n, hn_stab⟩ : stabTil (⊥ : Subgroup G) V) * ⟨m, hm_stab⟩ := by
      ext
      show m * n = n * m
      exact hmn
    rw [ht₁, ht₂, ← map_mul, ← map_mul, hmul]
  have hfix₁ : fixV (Subgroup.zpowers t₁) =
      imgTil (⊥ : Subgroup G) V hV (V ⊓ Subgroup.centralizer ({m} : Set G)) := by
    rw [ht₁]; exact s16c167_fixV_actTil hV hm_stab
  have hfix₂ : fixV (Subgroup.zpowers t₂) =
      imgTil (⊥ : Subgroup G) V hV (V ⊓ Subgroup.centralizer ({n} : Set G)) := by
    rw [ht₂]; exact s16c167_fixV_actTil hV hn_stab
  have ht₁ne : t₁ ≠ 1 := by
    intro h1
    apply hnu
    rw [← hCm]
    apply E3.conjSubgroup_mono_left g
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨m, hm_stab⟩).1
      (by rw [← ht₁]; exact h1) v hv
    rw [Subgroup.mem_bot] at h2
    have h3 : m * v * m⁻¹ = v := mul_inv_eq_one.1 h2
    calc v * m = (m * v * m⁻¹) * m := by rw [h3]
      _ = m * v := by group
  have ht₂ne : t₂ ≠ 1 := by
    intro h1
    apply hnz
    rw [← hCn]
    apply E3.conjSubgroup_mono_left g
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨n, hn_stab⟩).1
      (by rw [← ht₂]; exact h1) v hv
    rw [Subgroup.mem_bot] at h2
    have h3 : n * v * n⁻¹ = v := mul_inv_eq_one.1 h2
    calc v * n = (n * v * n⁻¹) * n := by rw [h3]
      _ = n * v := by group
  have hJV : J ≤ V := hΔV J hJΔ
  have hJm : J ≤ Subgroup.centralizer ({m} : Set G) := by
    rw [← E3.conjSubgroup_le_conjSubgroup_iff g, hCm]
    exact hIu
  have hJn : J ≤ Subgroup.centralizer ({n} : Set G) := by
    rw [← E3.conjSubgroup_le_conjSubgroup_iff g, hCn]
    exact hIz
  have hle₁ : imgTil (⊥ : Subgroup G) V hV J ≤ fixV (Subgroup.zpowers t₁) := by
    rw [hfix₁]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V (le_inf hJV hJm))
  have hle₂ : imgTil (⊥ : Subgroup G) V hV J ≤ fixV (Subgroup.zpowers t₂) := by
    rw [hfix₂]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V (le_inf hJV hJn))
  have hkey : t₁ = t₂ :=
    hU t₁ ht₁_mem t₂ ht₂_mem ht₁2 ht₂2 ht₁₂ ht₁ne ht₂ne
      (imgTil (⊥ : Subgroup G) V hV J) (hΔt J hJΔ) hle₁ hle₂
  have hfix_eq : imgTil (⊥ : Subgroup G) V hV (V ⊓ Subgroup.centralizer ({m} : Set G)) =
      imgTil (⊥ : Subgroup G) V hV (V ⊓ Subgroup.centralizer ({n} : Set G)) := by
    rw [← hfix₁, ← hfix₂, hkey]
  have hinf_eq : V ⊓ Subgroup.centralizer ({m} : Set G) =
      V ⊓ Subgroup.centralizer ({n} : Set G) :=
    s16c167_n19_imgTil_inj hV inf_le_left inf_le_left hfix_eq
  calc conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)
      = conjSubgroup V g ⊓ conjSubgroup (Subgroup.centralizer ({m} : Set G)) g := by
          rw [hCm]
    _ = conjSubgroup (V ⊓ Subgroup.centralizer ({m} : Set G)) g := by
          rw [E3.conjSubgroup_inf]
    _ = conjSubgroup (V ⊓ Subgroup.centralizer ({n} : Set G)) g := by rw [hinf_eq]
    _ = conjSubgroup V g ⊓ conjSubgroup (Subgroup.centralizer ({n} : Set G)) g := by
          rw [E3.conjSubgroup_inf]
    _ = conjSubgroup V g ⊓ Subgroup.centralizer ({z} : Set G) := by rw [hCn]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
