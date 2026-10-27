module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16k_realizesVia_map {W W' : Type} [CommGroup W] [CommGroup W'] {D : FFModel}
    {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')} {U Z : Subgroup W}
    {π : D.Gam →* ↥H} (hR : D.RealizesVia H U Z π) (ρ : W →* W') (hker : ρ.ker ≤ Z)
    (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    D.RealizesVia H' (U.map ρ) (Z.map ρ) (θ.comp π) := by
  obtain ⟨hsurj, hZU, hkersec, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hR
  let ψ : ↥U →* ↥(U.map ρ) := ρ.subgroupMap U
  have hψ : Function.Surjective ψ := ρ.subgroupMap_surjective U
  have hker' : ψ.ker ≤ β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [hβk u]
    exact hker (by rw [MonoidHom.mem_ker]; exact congrArg Subtype.val hu)
  let β' : ↥(U.map ρ) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    MonoidHom.liftOfSurjective ψ hψ ⟨β, hker'⟩
  have hβ' : ∀ u : ↥U, β' (ψ u) = β u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ (Function.rightInverse_surjInv hψ) ⟨β, hker'⟩ u
  refine ⟨hθ.comp hsurj, Subgroup.map_mono hZU, hkersec, ?_, ?_, hsec, hkerinv, β', ?_, ?_, ?_⟩
  · rintro h' u' ⟨u, hu, rfl⟩
    obtain ⟨h, rfl⟩ := hθ h'
    rw [← hequiv h u]
    exact Subgroup.mem_map_of_mem ρ (hHU h u hu)
  · rintro h' z' ⟨z, hz, rfl⟩
    obtain ⟨h, rfl⟩ := hθ h'
    rw [← hequiv h z]
    exact Subgroup.mem_map_of_mem ρ (hHZ h z hz)
  · intro y
    obtain ⟨u, rfl⟩ := hβs y
    exact ⟨ψ u, hβ' u⟩
  · intro u'
    obtain ⟨u, rfl⟩ := hψ u'
    rw [hβ' u, hβk u]
    constructor
    · intro hu
      exact Subgroup.mem_map_of_mem ρ hu
    · intro hu
      obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.1 hu
      have hzu' : ρ z = ρ (u : W) := hzu
      have hmem : z⁻¹ * (u : W) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzu']
        exact inv_mul_cancel (ρ (u : W))
      have hZu : z⁻¹ * (u : W) ∈ Z := hker hmem
      have h1 : z * (z⁻¹ * (u : W)) ∈ Z := mul_mem hz hZu
      have h2 : z * (z⁻¹ * (u : W)) = (u : W) := by group
      rwa [h2] at h1
  · intro γ u' m hu' hm hbu
    obtain ⟨u, rfl⟩ := hψ u'
    rw [hβ' u] at hbu
    have hu₀ : ((π γ : ↥H) : MulAut W) (u : W) ∈ U := hHU (π γ) u u.2
    have key : (⟨((θ.comp π γ : ↥H') : MulAut W') ((ψ u : W')), hu'⟩ : ↥(U.map ρ)) =
        ψ ⟨((π γ : ↥H) : MulAut W) (u : W), hu₀⟩ :=
      Subtype.ext (hequiv (π γ) (u : W)).symm
    rw [key, hβ' ⟨_, hu₀⟩]
    exact hβe γ u m hu₀ hm hbu

theorem s16k_realizes_map {W W' : Type} [CommGroup W] [CommGroup W'] {D : FFModel}
    {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')} {U Z : Subgroup W}
    (hR : D.Realizes H U Z) (ρ : W →* W') (hker : ρ.ker ≤ Z)
    (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    D.Realizes H' (U.map ρ) (Z.map ρ) := by
  obtain ⟨π, hπ⟩ := hR
  exact ⟨θ.comp π, s16k_realizesVia_map hπ ρ hker θ hθ hequiv⟩

theorem s16k_sumOfNat_map {W W' : Type} [CommGroup W] [CommGroup W']
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {N' : Subgroup (MulAut W') → Subgroup W' → Subgroup W' → Prop}
    {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')} {U Z : Subgroup W} {k : ℕ}
    (hS : SumOfNat N H U Z k) (ρ : W →* W') (hker : ρ.ker ≤ Z)
    (hN : ∀ I : Subgroup W, Z ≤ I → N H I Z → N' H' (I.map ρ) (Z.map ρ)) :
    SumOfNat N' H' (U.map ρ) (Z.map ρ) k := by
  obtain ⟨I, hZI, hind, hsup, hNI⟩ := hS
  refine ⟨fun i => (I i).map ρ, fun i => Subgroup.map_mono (hZI i), ?_, ?_,
    fun i => hN (I i) (hZI i) (hNI i)⟩
  · intro i x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxi, hxrest⟩ := hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hxi
    have hle : Z.map ρ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), (I j).map ρ
        ≤ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j).map ρ := by
      apply sup_le
      · exact Subgroup.map_mono le_sup_left
      · apply iSup_le
        intro j
        apply iSup_le
        intro hj
        refine Subgroup.map_mono (le_trans ?_ le_sup_right)
        exact le_iSup₂ (f := fun (j' : Fin k) (_ : j' ≠ i) => I j') j hj
    obtain ⟨b, hb, hbρ⟩ := Subgroup.mem_map.1 (hle hxrest)
    have hmem : a * b⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbρ]
      exact mul_inv_cancel (ρ a)
    have hZ : a * b⁻¹ ∈ Z := hker hmem
    have haB : a ∈ Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
      have h1 : (a * b⁻¹) * b ∈ Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j :=
        mul_mem (Subgroup.mem_sup_left hZ) hb
      have h2 : (a * b⁻¹) * b = a := by group
      rwa [h2] at h1
    exact Subgroup.mem_map_of_mem ρ (hind i ⟨ha, haB⟩)
  · rw [← Subgroup.map_iSup ρ I, ← Subgroup.map_sup, hsup]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
