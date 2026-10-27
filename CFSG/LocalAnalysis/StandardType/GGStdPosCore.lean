module

public import CFSG.LocalAnalysis.StandardType.GGStdPosAct
public import CFSG.LocalAnalysis.StandardType.GGStdPosUnip
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

theorem ggStdPos_centralizer_eq {K G : Type*} [Group K] [Group G]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (htr : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, ∀ x' ∈ D.rootGroup γ, x ≠ 1 → x' ≠ 1 →
      ∃ t ∈ ggTorus D, t * x * t⁻¹ = x')
    (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) (S : Set G)
    (hS : ∀ s ∈ S, ∀ γ ∈ D.roots, ∃ h ∈ ggTorus D, ∀ z ∈ D.rootGroup γ,
      s * ψ z * s⁻¹ = ψ (h * z * h⁻¹)) :
    (Subgroup.centralizer S).comap ψ =
      ((Subgroup.centralizer S).comap ψ ⊓ Subgroup.normalizer (ggTorus D : Set K)) ⊔
        ⨆ β ∈ {β | β ∈ D.roots ∧ D.rootGroup β ≤ (Subgroup.centralizer S).comap ψ},
          D.rootGroup β := by
  refine le_antisymm (fun k hk => ?_) (sup_le inf_le_left (iSup₂_le fun β hβ => hβ.2))
  have memC : ∀ g : K, g ∈ (Subgroup.centralizer S).comap ψ ↔ ∀ s ∈ S, s * ψ g * s⁻¹ = ψ g :=
    fun g => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      exact forall₂_congr fun s _ =>
        ⟨fun h => by rw [h, mul_inv_cancel_right], fun h => mul_inv_eq_iff_eq_mul.mp h⟩
  have hZT : Subgroup.center K ≤ ⨆ i, H i :=
    (LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU).le.trans
      (LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU)
  have hcen : ∀ {a b : K}, ψ a = ψ b → ∃ z ∈ Subgroup.center K, b = a * z := fun {a b} h =>
    ⟨a⁻¹ * b, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]), by group⟩
  have hUC := ggStdPos_posUnipotent_inf_le hct hext hBU htr ψ hker S hS
  obtain ⟨⟨w, b, u⟩, ⟨⟨hb, hu⟩, hkbu⟩, -⟩ := existsUnique_bruhat_normalForm hct hext hBU k
  simp only at hb hu hkbu
  have hb' := hb
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb'
  obtain ⟨t, htT, v, hv, rfl⟩ := hb'
  have hnw := nrep_mem_weylN hct w
  have huC : u ∈ (Subgroup.centralizer S).comap ψ := by
    refine (memC u).mpr fun s hsS => ?_
    have hs := hS s hsS
    obtain ⟨t₁, ht₁, ht₁T⟩ :=
      ggStdPos_exists_conj_eq hct hext hBU hker hs (actsAs_of_mem_iSup hct htT)
    obtain ⟨v₁, hv₁, hv₁e⟩ := ggStdPos_conj_mem_map_iSup hs (fun γ hγ => hγ.1) hv
    obtain ⟨m, hm, hmT⟩ := ggStdPos_exists_conj_eq hct hext hBU hker hs (actsAs_nrep hct w)
    obtain ⟨u₁, hu₁, hu₁e⟩ := ggStdPos_conj_mem_map_iSup hs (fun γ hγ => hγ.1) hu
    have ht₁' : t₁ ∈ ⨆ i, H i := by
      simpa using mul_mem htT ht₁T
    set b₂ := t₁ * v₁ * (nrep hct w * ((nrep hct w)⁻¹ * m) * (nrep hct w)⁻¹) with hb₂
    have hb₂B : b₂ ∈ borel D H := mul_mem (mul_mem (iSup_le_borel ht₁')
      (posUnipotent_le_borel hv₁)) (iSup_le_borel (conj_mem_iSup_of_mem_weylN hct hnw hmT))
    have e1 : ψ k = ψ (b₂ * nrep hct w * u₁) := by
      rw [← (memC k).mp hk s hsS, hkbu]
      calc s * ψ (t * v * nrep hct w * u) * s⁻¹ = (s * ψ t * s⁻¹) * (s * ψ v * s⁻¹) *
            (s * ψ (nrep hct w) * s⁻¹) * (s * ψ u * s⁻¹) := by
            rw [map_mul, map_mul, map_mul]
            group
        _ = ψ (b₂ * nrep hct w * u₁) := by
            rw [ht₁, hv₁e, hm, hu₁e, hb₂, ← map_mul, ← map_mul, ← map_mul]
            congr 1
            group
    obtain ⟨z, hz, hze⟩ := hcen e1
    have hzB : z⁻¹ ∈ borel D H := iSup_le_borel (hZT (inv_mem hz))
    have e2 : t * v * nrep hct w * u = b₂ * z⁻¹ * nrep hct w * u₁ := by
      have hc := Subgroup.mem_center_iff.mp (inv_mem hz) (nrep hct w * u₁)
      calc t * v * nrep hct w * u = b₂ * nrep hct w * u₁ * z⁻¹ := by
            rw [← hkbu, hze]
            group
        _ = b₂ * (nrep hct w * u₁ * z⁻¹) := by group
        _ = b₂ * (z⁻¹ * (nrep hct w * u₁)) := by rw [hc]
        _ = b₂ * z⁻¹ * nrep hct w * u₁ := by group
    have hu₁u := (eq_of_mul_nrep_mul_eq hct hBU hb (mul_mem hb₂B hzB) hu hu₁ e2).2
    rw [hu₁e, hu₁u]
  set v' := t * v * t⁻¹ with hv'
  set m₀ := t * nrep hct w with hm₀
  have hv'U : v' ∈ posUnipotent D := (Subgroup.mem_normalizer_iff.mp
    (borel_le_normalizer_posUnipotent hct (iSup_le_borel htT)) v).mp hv
  have hm₀N : m₀ ∈ weylN n H := mul_mem (iSup_le_weylN htT) hnw
  have hm₀A : ActsAs D m₀ w := by
    simpa only [one_mul] using (actsAs_of_mem_iSup hct htT).mul (actsAs_nrep hct w)
  have hbn : t * v * nrep hct w = v' * m₀ := by rw [hv', hm₀]; group
  have hbnC : v' * m₀ ∈ (Subgroup.centralizer S).comap ψ := by
    rw [← hbn, show t * v * nrep hct w = k * u⁻¹ by rw [hkbu]; group]
    exact mul_mem hk (inv_mem huC)
  have hv'C : v' ∈ (Subgroup.centralizer S).comap ψ := by
    refine (memC v').mpr fun s hsS => ?_
    have hs := hS s hsS
    obtain ⟨v₁, hv₁, hv₁e⟩ := ggStdPos_conj_mem_map_iSup hs (fun γ hγ => hγ.1) hv'U
    obtain ⟨m₁, hm₁, hm₁T⟩ := ggStdPos_exists_conj_eq hct hext hBU hker hs hm₀A
    have e1 : ψ (v' * m₀) = ψ (v₁ * m₁) := by
      rw [← (memC _).mp hbnC s hsS, map_mul ψ v' m₀, map_mul ψ v₁ m₁, ← hv₁e, ← hm₁]
      group
    obtain ⟨z, hz, hze⟩ := hcen e1
    have hT : v'⁻¹ * v₁ ∈ ⨆ i, H i := by
      have e2 : v'⁻¹ * v₁ = m₀ * (z * (m₀⁻¹ * m₁)⁻¹) * m₀⁻¹ := by
        calc v'⁻¹ * v₁ = m₀ * ((v' * m₀)⁻¹ * (v₁ * m₁)) * (m₀⁻¹ * m₁)⁻¹ * m₀⁻¹ := by group
          _ = m₀ * (z * (m₀⁻¹ * m₁)⁻¹) * m₀⁻¹ := by
              rw [show (v' * m₀)⁻¹ * (v₁ * m₁) = z by rw [hze]; group, mul_assoc m₀ z]
      rw [e2]
      exact conj_mem_iSup_of_mem_weylN hct hm₀N (mul_mem (hZT hz) (inv_mem hm₁T))
    have h1 : v'⁻¹ * v₁ ∈ (⨆ i, H i) ⊓ posUnipotent D :=
      Subgroup.mem_inf.mpr ⟨hT, mul_mem (inv_mem hv'U) hv₁⟩
    rw [show posUnipotent D = ⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ from rfl,
      hext.torus_inf_posPart, Subgroup.mem_bot] at h1
    rw [hv₁e, ← inv_mul_eq_one.mp h1]
  have hm₀C : m₀ ∈ (Subgroup.centralizer S).comap ψ := by
    simpa using mul_mem (inv_mem hv'C) hbnC
  have hm₀T : m₀ ∈ Subgroup.normalizer (ggTorus D : Set K) := by
    rw [ggStdPos_ggTorus_eq hct hext hBU]
    exact weylN_le_normalizer hct hm₀N
  rw [hkbu, hbn]
  refine mul_mem (mul_mem (le_sup_right (a := (Subgroup.centralizer S).comap ψ ⊓
    Subgroup.normalizer (ggTorus D : Set K)) (hUC ⟨hv'U, hv'C⟩))
      (le_sup_left (b := ⨆ β ∈ {β | β ∈ D.roots ∧
        D.rootGroup β ≤ (Subgroup.centralizer S).comap ψ}, D.rootGroup β) ⟨hm₀C, hm₀T⟩))
    (le_sup_right (a := (Subgroup.centralizer S).comap ψ ⊓
      Subgroup.normalizer (ggTorus D : Set K))
      (hUC ⟨inversionUnipotent_le_posUnipotent w hu, huC⟩))

end CFSG.StandardType

end
