module

public import CFSG.Quasithin.SteinbergBQDegreeThreeAutomizer
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module

theorem derivedSeries_eq_top_of_isPerfect {G : Type*} [Group G] [Group.IsPerfect G] (n : ℕ) :
    derivedSeries G n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero G
  | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem map_perfectResidual_comap_eq {G X : Type*} [Group G] [Group X] [Finite G] (π : G →* X)
    (hπ : Function.Surjective π) {B : Subgroup X} (hB : ⁅B, B⁆ = B) :
    ((CFSG.perfectResidual (B.comap π)).map (B.comap π).subtype).map π = B := by
  have : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr hB
  let f : B.comap π →* B := (π.comp (B.comap π).subtype).codRestrict B fun b => b.2
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨g, rfl⟩ := hπ b
    exact ⟨⟨g, hb⟩, rfl⟩
  obtain ⟨n, hn, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := B.comap π)
  have hmap : (CFSG.perfectResidual (B.comap π)).map f = ⊤ := by
    rw [hn, map_derivedSeries_eq hf, derivedSeries_eq_top_of_isPerfect]
  have hcomp : π.comp (B.comap π).subtype = B.subtype.comp f := rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hmap, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem exists_normal_sylow_of_central_kernel {G X : Type*} [Group G] [Group X] [Finite G]
    (π : G →* X) (hπ : Function.Surjective π) (hD : π.ker ≤ center G) {N : Subgroup X} {ℓ : ℕ}
    [Fact ℓ.Prime] (hN : IsPGroup ℓ N) :
    ∃ P : Sylow ℓ (N.comap π), (P : Subgroup (N.comap π)).Characteristic ∧
      ∀ n ∈ N, ∃ q ∈ (P : Subgroup (N.comap π)), π q = n := by
  classical
  let f : N.comap π →* N := (π.comp (N.comap π).subtype).codRestrict N fun m => m.2
  have hf : Function.Surjective f := by
    rintro ⟨n, hn⟩
    obtain ⟨g, rfl⟩ := hπ n
    exact ⟨⟨g, hn⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (N.comap π)) := inferInstance
  have hmax := (P.mapSurjective hf).is_maximal' (hN.to_subgroup ⊤) le_top
  have hPN : ∀ n ∈ N, ∃ q ∈ (P : Subgroup (N.comap π)), π q = n := by
    intro n hn
    have h1 : (⟨n, hn⟩ : N) ∈ ((P.mapSurjective hf : Sylow ℓ N) : Subgroup N) := by
      rw [← hmax]
      exact mem_top _
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨q, hq, hqn⟩ := h1
    exact ⟨q, hq, congrArg Subtype.val hqn⟩
  have hnorm : (P : Subgroup (N.comap π)).Normal := by
    refine ⟨fun q hq m => ?_⟩
    obtain ⟨q', hq', hq'm⟩ := hPN (π m) m.2
    have hd : ((q'⁻¹ * m : N.comap π) : G) ∈ π.ker := by
      rw [MonoidHom.mem_ker, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hq'm,
        inv_mul_cancel]
    have hc := Subgroup.mem_center_iff.mp (hD hd)
    have e : m * q * m⁻¹ = q' * q * q'⁻¹ := by
      apply Subtype.ext
      have hm : (m : G) = q' * ((q'⁻¹ * m : N.comap π) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      set d : G := ((q'⁻¹ * m : N.comap π) : G)
      have hdq : (q : G) * d = d * q := hc q
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hm]
      calc (q' : G) * d * q * ((q' : G) * d)⁻¹ = q' * (d * q) * d⁻¹ * (q' : G)⁻¹ := by group
        _ = q' * ((q : G) * d) * d⁻¹ * (q' : G)⁻¹ := by rw [hdq]
        _ = q' * q * (q' : G)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hq' hq) (inv_mem hq')
  exact ⟨P, Sylow.characteristic_of_normal P hnorm, hPN⟩

theorem commute_of_normal_coprime_of_finrank_three {k V : Type*} [Field k] {p : ℕ}
    [Fact p.Prime] [CharP k p] [AddCommGroup V] [Module k V] (hV : finrank k V = 3)
    {Γ : Type*} [Group Γ] [Finite Γ] (θ : Γ →* LinearMap.GeneralLinearGroup k V)
    (hθ : Function.Injective θ) (D : Subgroup Γ) [D.Normal] (hD : D ≤ center Γ)
    {B N : Subgroup (Γ ⧸ D)} (hB : ⁅B, B⁆ = B) (hNB : N ≤ B) (hNn : (N.subgroupOf B).Normal)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hN : IsPGroup ℓ N) :
    ∀ b ∈ B, ∀ n ∈ N, b * n = n * b := by
  classical
  set π : Γ →* Γ ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker ≤ center Γ := by rw [hπ, QuotientGroup.ker_mk']; exact hD
  obtain ⟨P₀, hchar, hPN⟩ := exists_normal_sylow_of_central_kernel π hπs hker hN
  set P : Subgroup Γ := (P₀ : Subgroup (N.comap π)).map (N.comap π).subtype with hPdef
  have hBN : B ≤ normalizer (N : Set (Γ ⧸ D)) :=
    (normal_subgroupOf_iff_le_normalizer hNB).mp hNn
  have hBP : B.comap π ≤ normalizer (P : Set Γ) :=
    ((comap_mono hBN).trans (le_normalizer_comap π)).trans
      (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  set H : Subgroup Γ := (CFSG.perfectResidual (B.comap π)).map (B.comap π).subtype with hHdef
  have hHB : H.map π = B := map_perfectResidual_comap_eq π hπs hB
  have hHperf : ⁅H, H⁆ = H := by
    have h1 : Group.IsPerfect (CFSG.perfectResidual (B.comap π)) :=
      (CFSG.perfect_residual_characterization (G := B.comap π)).2.2.1
    rw [Subgroup.isPerfect_iff] at h1
    rw [hHdef, ← Subgroup.map_commutator, h1]
  have hHle : H ≤ normalizer (P : Set Γ) := (map_subtype_le _).trans hBP
  have : Finite (P.map θ) := Finite.of_surjective _ (θ.subgroupMap_surjective P)
  have hPp : IsPGroup ℓ (P.map θ) := (P₀.isPGroup'.map _).map θ
  have hHθ : H.map θ ≤ normalizer ((P.map θ : Subgroup _) : Set _) :=
    (map_mono hHle).trans (le_normalizer_map θ)
  have hHθperf : ⁅H.map θ, H.map θ⁆ = H.map θ := by rw [← Subgroup.map_commutator, hHperf]
  have hcent := (SteinbergBQ.degree_three_coprime_automizer_solvable hV hℓp (P.map θ) hPp).2.2
    (H.map θ) hHθ hHθperf
  intro b hb n hn
  rw [← hHB] at hb
  obtain ⟨h, hh, rfl⟩ := hb
  obtain ⟨q, hq, rfl⟩ := hPN n hn
  have hqP : (q : Γ) ∈ P := ⟨q, hq, rfl⟩
  have hc := mem_centralizer_iff.mp (hcent ⟨h, hh, rfl⟩) (θ q) ⟨q, hqP, rfl⟩
  rw [← map_mul, ← map_mul] at hc
  rw [← map_mul, ← map_mul, hθ hc]

theorem degree_three_scalar_quotient_normal_coprime_prime_subgroup_central {k : Type*} [Field k]
    [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] {Γ : Subgroup (GL (Fin 3) k)}
    (D : Subgroup Γ) [D.Normal]
    (hD : ∀ d ∈ D, ∃ c : kˣ, (d : GL (Fin 3) k) = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    {B N : Subgroup (Γ ⧸ D)} (hB : ⁅B, B⁆ = B) (hNB : N ≤ B) (hNn : (N.subgroupOf B).Normal)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hN : IsPGroup ℓ N) :
    N.subgroupOf B ≤ center B := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite (GL (Fin 3) k) := Finite.of_injective _ Units.val_injective
  have hDc : D ≤ center Γ := by
    intro d hd
    obtain ⟨c, hc⟩ := hD d hd
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (Matrix.GeneralLinearGroup.scalar_commute c (g : GL (Fin 3) k)).symm
  have hcomm := commute_of_normal_coprime_of_finrank_three (Module.finrank_fin_fun k)
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin 3) k ≃* _).toMonoidHom.comp Γ.subtype)
    (Matrix.GeneralLinearGroup.toLin.injective.comp Γ.subtype_injective) D hDc hB hNB hNn hℓp hN
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro b
  exact Subtype.ext (hcomm b b.2 x (mem_subgroupOf.mp hx))

end CFSG.Quasithin.H13.NQCat
