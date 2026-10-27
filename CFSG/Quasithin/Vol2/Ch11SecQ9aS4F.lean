module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartE
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4C
public import CFSG.Quasithin.Vol2.KGNatSp4Levi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Open (pCoreOf)

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem psiSp_mem (π : ↥(StatedSp 2 K) →* ↥H) (g A : StatedSp 2 K) : psiSp π g A ∈ H :=
  (π (g * A * g⁻¹)).2

theorem psiSp_mul (π : ↥(StatedSp 2 K) →* ↥H) (g x : StatedSp 2 K) :
    psiSp π (g * x) = (psiSp π g).comp (MulAut.conj x).toMonoidHom := by
  ext A
  rw [MonoidHom.comp_apply, psiSp_apply, psiSp_apply]
  congr 3
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_psiSp_eq (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {x : MulAut W} (hx : x ∈ H) : ∃ A, psiSp π g A = x := by
  obtain ⟨B, hB⟩ : ∃ B : ↥(StatedSp 2 K), π B = ⟨x, hx⟩ := hf.onto ⟨x, hx⟩
  exact ⟨g⁻¹ * B * g, by rw [psiSp_apply, show g * (g⁻¹ * B * g) * g⁻¹ = B by group, hB]⟩

variable [Finite K]

theorem eq_map_psiSp_of_sylow {P : Subgroup (MulAut W)} {g : StatedSp 2 K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W)) :
    P = (unipotent 2 K).map (psiSp π g) := by
  ext x
  rw [hg, ← Usp_eq_unipotent]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

omit [Finite K] in
theorem inf_normalizer_eq_sp (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) :
    H ⊓ Subgroup.normalizer
        (((unipotent 2 K).map (psiSp π g) : Subgroup (MulAut W)) : Set (MulAut W)) =
      (borelSubgroup 2 K).map (psiSp π g) := by
  have hψ := psiSp_injective hf g
  ext x
  constructor
  · rintro ⟨hxH, hxN⟩
    obtain ⟨A, rfl⟩ := exists_psiSp_eq hf g hxH
    refine ⟨A, ?_, rfl⟩
    rw [← normalizer_unipotent]
    exact (map_mem_normalizer_iff _ hψ).mp hxN
  · rintro ⟨A, hA, rfl⟩
    refine ⟨psiSp_mem π g A, (map_mem_normalizer_iff _ hψ).mpr ?_⟩
    rw [normalizer_unipotent]
    exact hA

omit [Finite K] in
theorem sylow_conj_mul_sp {P : Subgroup (MulAut W)} {g x : StatedSp 2 K}
    (hg : ∀ y : MulAut W, y ∈ P ↔ ∃ u ∈ Usp K, y = ((π (g * u * g⁻¹) : ↥H) : MulAut W))
    (hx : x ∈ Usp K) :
    ∀ y : MulAut W, y ∈ P ↔
      ∃ u ∈ Usp K, y = ((π ((g * x) * u * (g * x)⁻¹) : ↥H) : MulAut W) := by
  intro y
  rw [hg]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨x⁻¹ * u * x, (Usp K).mul_mem ((Usp K).mul_mem ((Usp K).inv_mem hx) hu) hx, ?_⟩
    rw [show g * x * (x⁻¹ * u * x) * (g * x)⁻¹ = g * u * g⁻¹ by group]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨x * u * x⁻¹, (Usp K).mul_mem ((Usp K).mul_mem hx hu) ((Usp K).inv_mem hx), ?_⟩
    rw [show g * (x * u * x⁻¹) * g⁻¹ = g * x * u * (g * x)⁻¹ by group]

theorem exists_eq_map_torus_sp [CharP K 2] (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) {D : Subgroup (MulAut W)}
    (hD : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf D ((borelSubgroup 2 K).map (psiSp π g))) :
    ∃ x ∈ unipotent 2 K, D = (torus 2 K).map (psiSp π (g * x)) := by
  have hψ := psiSp_injective hf g
  obtain ⟨hDle, hDodd, k, hk⟩ := hD
  have hDeq : (D.comap (psiSp π g)).map (psiSp π g) = D :=
    Subgroup.map_comap_eq_self (hDle.trans (Subgroup.map_le_range _ _))
  have hD0 : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf (D.comap (psiSp π g))
      (borelSubgroup 2 K) := by
    refine ⟨?_, ?_, k, ?_⟩
    · have := Subgroup.comap_mono (f := psiSp π g) hDle
      rwa [Subgroup.comap_map_eq_self_of_injective hψ] at this
    · rw [← Subgroup.card_map_of_injective hψ, hDeq]
      exact hDodd
    · rw [← Subgroup.relIndex_map_map_of_injective _ _ hψ, hDeq]
      exact hk
  obtain ⟨x, hx, hxD⟩ := exists_conj_torus_of_isHall_sp hD0
  refine ⟨x, hx, ?_⟩
  rw [← hDeq, hxD, Subgroup.map_map, psiSp_mul]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
