module

public import CFSG.Quasithin.AppendixH.H16.ConjNat
public import CFSG.Quasithin.AppendixH.H16.Concl161Mod
public import CFSG.Quasithin.AppendixH.H16.SextetO23

public section

open scoped Pointwise

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24
  CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Open

theorem h161_group
    (τ : S24) :
    IsO23 (conjSubg τ sxGen) (conjSubg τ sxN) ∧
      ∃ π : ↥(conjSubg τ sxGen) →* ↥(CFSG.Open.StatedSp 2 (ZMod 2)), Function.Surjective π ∧
        π.ker = (conjSubg τ sxN).subgroupOf (conjSubg τ sxGen) := by
  refine ⟨isO23_conjSubg τ isO23_sxGen, ?_⟩
  let φ : ↥sxGen ≃* ↥(conjSubg τ sxGen) :=
    Subgroup.equivMapOfInjective sxGen (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective
  have hφ : ∀ y : ↥sxGen, ((φ y : ↥(conjSubg τ sxGen)) : S24) = τ * (y : S24) * τ⁻¹ := fun y => rfl
  have hφs : ∀ g : ↥(conjSubg τ sxGen), (((φ.symm g : ↥sxGen)) : S24) = τ⁻¹ * (g : S24) * τ := by
    intro g
    have h := hφ (φ.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    group
  refine ⟨sxPi.comp φ.symm.toMonoidHom, sxPi_surjective.comp φ.symm.surjective, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
  have h1 : sxPi (φ.symm g) = 1 ↔ φ.symm g ∈ sxPi.ker := (MonoidHom.mem_ker).symm
  rw [show (φ.symm.toMonoidHom g) = φ.symm g from rfl, h1, sxPi_ker, Subgroup.mem_subgroupOf,
    hφs, mem_conjSubg_iff]

theorem h161_of_coords
    {V : Type*} [CommGroup V]
    (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoC11 AutPerm le_rfl γ (e v))
    {S : Finset (Finset (Fin 24))} (hS : IsSextet S) :
    ∃ V₁₀ : Subgroup V,
      (IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g S))) ⊥ (fixV (rImg ρ (KY M24g S))) ∧
        rk ↥(fixV (rImg ρ (KY M24g S))) = 4 ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g S))) (fixV (rImg ρ (KY M24g S))) V₁₀ ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g S))) V₁₀ ⊤ ∧
        V₁₀ = CFSG.Quasithin.commV (rImg ρ (perfectCore (MY M24g S))) ∧ rkIdx V₁₀ = 1) ∧
      (∃ N : Subgroup S24, IsO23 (MY M24g S) N ∧
        (∃ π : ↥(MY M24g S) →* ↥(CFSG.Open.StatedSp 2 (ZMod 2)), Function.Surjective π ∧
          π.ker = N.subgroupOf (MY M24g S)) ∧
        (∀ g : ↥M24g, (g : S24) ∈ MY M24g S →
          ((∀ x ∈ fixV (rImg ρ (KY M24g S)), ρ g x = x) ↔ (g : S24) ∈ N)) ∧
        InducesOn (rImg ρ (MY M24g S)) (fixV (rImg ρ (KY M24g S))) ⊥
          (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
          (natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2)))) ∧
      FullTranspAxis (rImg ρ (MY M24g S)) (rImg ρ (KY M24g S)) (fixV (rImg ρ (KY M24g S))) V₁₀ := by
  obtain ⟨τ, hτ, rfl⟩ := exists_smul_stdSextet hS
  have hMY : MY M24g (τ • stdSextet) = conjSubg τ sxGen := by
    rw [MY_smul_of_mem hτ, MY_stdSextet_eq]
  have hKY : KY M24g (τ • stdSextet) = conjSubg τ sxKS := by
    rw [KY, hMY, pCoreOf_conjSubg, pCoreOf_two_sxGen]
  have hPC : perfectCore (MY M24g (τ • stdSextet)) = conjSubg τ sxP0 := by
    rw [hMY, perfectCore_conjSubg, perfectCore_sxGen]
  let τ' : ↥M24g := ⟨τ, hτ⟩
  let e' : V ≃* W11 := (ρ τ'⁻¹).trans e
  have hcongr : ∀ γ : ↥M24g, CFSG.Quasithin.H.congrHom e' (ρ γ) =
      rhoC11 AutPerm le_rfl (τ'⁻¹ * γ * τ') :=
    congrHom_twist ρ (rhoC11 AutPerm le_rfl) e he τ'
  have hτinv : ((τ' : S24))⁻¹ = τ⁻¹ := rfl
  have hG : (rImg ρ (MY M24g (τ • stdSextet))).map (CFSG.Quasithin.H.congrHom e') =
      imgCd sxGen := by
    have h := map_congrHom_rImg ρ (rhoC11 AutPerm le_rfl) e' τ' hcongr
      (A := MY M24g (τ • stdSextet)) inf_le_left
    rw [h, hτinv, hMY, conjSubg_inv_conjSubg]
    rfl
  have hK : (rImg ρ (KY M24g (τ • stdSextet))).map (CFSG.Quasithin.H.congrHom e') =
      imgCd sxKS := by
    have h := map_congrHom_rImg ρ (rhoC11 AutPerm le_rfl) e' τ' hcongr
      (A := KY M24g (τ • stdSextet)) ((pCoreOf_le_subgroup 2 _).trans inf_le_left)
    rw [h, hτinv, hKY, conjSubg_inv_conjSubg]
    rfl
  have hP : (rImg ρ (perfectCore (MY M24g (τ • stdSextet)))).map (CFSG.Quasithin.H.congrHom e') =
      imgCd sxP0 := by
    have h := map_congrHom_rImg ρ (rhoC11 AutPerm le_rfl) e' τ' hcongr
      (A := perfectCore (MY M24g (τ • stdSextet))) ((perfectCore_le_subgroup _).trans inf_le_left)
    rw [h, hτinv, hPC, conjSubg_inv_conjSubg]
    rfl
  obtain ⟨V₁₀, h1, hind, h3⟩ := h161_transport e' _ _ _ hG hK hP
  have hFix : (fixV (rImg ρ (KY M24g (τ • stdSextet)))).map e'.toMonoidHom = US := by
    have h := CFSG.Quasithin.H.fixV_map_congrHom e' (rImg ρ (KY M24g (τ • stdSextet)))
    rw [hK, fixV_imgCd_sxKS] at h
    exact h.symm
  have hgroup : ∀ M : Subgroup S24, M = conjSubg τ sxGen →
      ∃ N : Subgroup S24, IsO23 M N ∧
        (∃ π : ↥M →* ↥(CFSG.Open.StatedSp 2 (ZMod 2)), Function.Surjective π ∧
          π.ker = N.subgroupOf M) ∧
        (∀ g : ↥M24g, (g : S24) ∈ M →
          ((∀ x ∈ fixV (rImg ρ (KY M24g (τ • stdSextet))), ρ g x = x) ↔ (g : S24) ∈ N)) := by
    intro M hM
    subst hM
    refine ⟨conjSubg τ sxN, (h161_group τ).1, (h161_group τ).2, ?_⟩
    intro g hg
    have hgG : τ⁻¹ * (g : S24) * τ ∈ sxGen := (mem_conjSubg_iff τ sxGen g).1 hg
    let g' : ↥AutPerm := ⟨τ⁻¹ * (g : S24) * τ, sxGen_le_AutPerm hgG⟩
    have hcg : CFSG.Quasithin.H.congrHom e' (ρ g) = rhoC11 AutPerm le_rfl g' := hcongr g
    rw [mem_conjSubg_iff]
    refine Iff.trans ?_ (fixes_US_iff_mem_sxN g' hgG)
    have happ : ∀ x : V, (rhoC11 AutPerm le_rfl g') (e' x) = e' (ρ g x) := by
      intro x
      have h := CFSG.Quasithin.H.congrHom_apply e' (ρ g) (e' x)
      have hxx : e'.symm (e' x) = x := e'.symm_apply_apply x
      erw [hxx] at h
      rw [← hcg]
      exact h
    constructor
    · intro hfix u hu
      rw [← hFix] at hu
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
      show (rhoC11 AutPerm le_rfl g') (e' x) = e' x
      rw [happ, hfix x hx]
    · intro h x hx
      have hx' : e'.toMonoidHom x ∈ US := by
        rw [← hFix]
        exact Subgroup.mem_map_of_mem _ hx
      have h2 : (rhoC11 AutPerm le_rfl g') (e' x) = e' x := h _ hx'
      rw [happ] at h2
      exact e'.injective h2
  obtain ⟨N, hN1, hN2, hN3⟩ := hgroup _ hMY
  exact ⟨V₁₀, h1, ⟨N, hN1, hN2, hN3, hind⟩, h3⟩

end CFSG.ASVolI.H16
