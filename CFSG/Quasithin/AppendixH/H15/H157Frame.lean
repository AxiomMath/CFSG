module

public import CFSG.Quasithin.AppendixH.H15.H157Frat
public import CFSG.Quasithin.Background.H153Conj

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24 CFSG.ASVolI.ChH CFSG.Monster.Code

theorem conjSubg_zpowers_eq {y c : S24} (hcy : c * y * c⁻¹ = tP) (h : S24) :
    conjSubg (h * c) (Subgroup.zpowers y) = (Subgroup.zpowers tP).map (cjS h).toMonoidHom := by
  unfold conjSubg
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  congr 1
  change MulAut.conj (h * c) y = cjS h tP
  rw [MulAut.conj_apply, cjS_apply]
  rw [show (h * c) * y * (h * c)⁻¹ = h * (c * y * c⁻¹) * h⁻¹ by group, hcy]

theorem normN_conj_eq {h : S24} (hh : h ∈ M24g) {y c : S24} (hcy : c * y * c⁻¹ = tP) :
    M24g ⊓ Subgroup.normalizer ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24) =
      Nt.map (cjS h).toMonoidHom := by
  rw [conjSubg_zpowers_eq hcy h]
  rw [← Subgroup.map_normalizer_eq_of_bijective (Subgroup.zpowers tP) (cjS h).bijective]
  have hM : M24g.map (cjS h).toMonoidHom = M24g := AutPerm_map_cj hh
  rw [← hM, ← Subgroup.map_inf _ _ _ (cjS h).injective]
  unfold Nt
  rfl

theorem KY_smul_S0 {h : S24} (hh : h ∈ M24g) :
    KY M24g (h • S0) = KSp.map (cjS h).toMonoidHom := by
  rw [KY_conj hh, show KY M24g S0 = KSp by unfold KY; exact pCoreOf_MY0]

theorem frame_inf {h y c : S24} (hh : h ∈ M24g) (hcy : c * y * c⁻¹ = tP) :
    (M24g ⊓ Subgroup.normalizer
        ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊓
      KY M24g (h • S0) = ⊥ := by
  rw [normN_conj_eq hh hcy, KY_smul_S0 hh, ← Subgroup.map_inf _ _ _ (cjS h).injective,
    Nt_inf_KSp, Subgroup.map_bot]

theorem frame_sup {h y c : S24} (hh : h ∈ M24g) (hcy : c * y * c⁻¹ = tP) :
    (M24g ⊓ Subgroup.normalizer
        ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊔
      KY M24g (h • S0) = MY M24g (h • S0) := by
  rw [normN_conj_eq hh hcy, KY_smul_S0 hh, ← Subgroup.map_sup, Nt_sup_KSp, MY_conj hh]

theorem exists_pi_coord_map (h : S24) {G N : Subgroup S24} {p : Fin 6 → Fin 24}
    (hpi : ∃ π : ↥G →* Equiv.Perm (Fin 6), Function.Surjective π ∧ π.ker = N.subgroupOf G ∧
      ∀ (n : ↥G) (j : Fin 6), (n : S24) (p j) = p (π n j)) :
    ∃ π : ↥(G.map (cjS h).toMonoidHom) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = (N.map (cjS h).toMonoidHom).subgroupOf (G.map (cjS h).toMonoidHom) ∧
      ∀ (n : ↥(G.map (cjS h).toMonoidHom)) (j : Fin 6),
        (n : S24) (h (p j)) = h (p (π n j)) := by
  obtain ⟨π₀, hs, hk, hc⟩ := hpi
  let ψ : ↥(G.map (cjS h).toMonoidHom) ≃* ↥G :=
    (G.equivMapOfInjective (cjS h).toMonoidHom (cjS h).injective).symm
  have hψ : ∀ x : ↥(G.map (cjS h).toMonoidHom),
      ((ψ x : ↥G) : S24) = (cjS h).symm (x : S24) := by
    intro x
    have h1 : ((G.equivMapOfInjective (cjS h).toMonoidHom (cjS h).injective (ψ x) :
        ↥(G.map (cjS h).toMonoidHom)) : S24) = (cjS h) ((ψ x : ↥G) : S24) :=
      Subgroup.coe_equivMapOfInjective_apply G (cjS h).toMonoidHom (cjS h).injective _
    have h2 : G.equivMapOfInjective (cjS h).toMonoidHom (cjS h).injective (ψ x) = x :=
      (G.equivMapOfInjective (cjS h).toMonoidHom (cjS h).injective).apply_symm_apply x
    rw [h2] at h1
    rw [h1]
    exact ((cjS h).symm_apply_apply _).symm
  refine ⟨π₀.comp ψ.toMonoidHom, hs.comp ψ.surjective, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : (π₀.comp ψ.toMonoidHom) x = 1 ↔ ψ x ∈ π₀.ker := Iff.rfl
    rw [h1, hk, Subgroup.mem_subgroupOf, hψ]
    constructor
    · intro hx
      exact ⟨_, hx, (cjS h).apply_symm_apply _⟩
    · rintro ⟨y, hy, hyx⟩
      have : (cjS h).symm (x : S24) = y := by rw [← hyx]; exact (cjS h).symm_apply_apply y
      rw [this]
      exact hy
  · intro n j
    have hn : (n : S24) = (cjS h) ((ψ n : ↥G) : S24) := by
      have h1 := (cjS h).apply_symm_apply (n : S24)
      rw [← hψ n] at h1
      exact h1.symm
    rw [hn, cjS_apply]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
      hc]
    rfl

theorem frame_pi {h y c : S24} (hh : h ∈ M24g) (hcy : c * y * c⁻¹ = tP) :
    ∃ π : ↥(M24g ⊓ Subgroup.normalizer
        ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24)) →*
        Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = (conjSubg (h * c) (Subgroup.zpowers y)).subgroupOf
        (M24g ⊓ Subgroup.normalizer
          ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ∧
      ∃ coordinates : Fin 6 ↪ Fin 24,
        (∀ point : Fin 24, ((h * c) * y * (h * c)⁻¹) point = point ↔
          ∃ index : Fin 6, coordinates index = point) ∧
        ∀ (acting : ↥(M24g ⊓ Subgroup.normalizer
            ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24))) (index : Fin 6),
          (acting : S24) (coordinates index) = coordinates (π acting index) := by
  obtain ⟨π₀, hs, hk, hc⟩ := exists_pi_Nt
  obtain ⟨π, hπs, hπk, hπp⟩ :=
    exists_pi_coord_map h (G := Nt) (N := Subgroup.zpowers tP) (p := fixPt) ⟨π₀, hs, hk, hc⟩
  rw [normN_conj_eq hh hcy, conjSubg_zpowers_eq hcy h]
  refine ⟨π, hπs, hπk, ?_⟩
  have hg : (h * c) * y * (h * c)⁻¹ = h * tP * h⁻¹ := by
    rw [show (h * c) * y * (h * c)⁻¹ = h * (c * y * c⁻¹) * h⁻¹ by group, hcy]
  refine ⟨⟨fun j => h (fixPt j), ?_⟩, ?_, ?_⟩
  · intro a b hab
    exact fixPt_injective (h.injective hab)
  · intro point
    rw [hg]
    constructor
    · intro hp
      have hp' : h (tP (h⁻¹ point)) = point := by
        rwa [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hp
      have h1 : tP (h⁻¹ point) = h⁻¹ point := by
        have := congrArg (fun x => h.symm x) hp'
        simpa [Equiv.Perm.inv_def] using this
      have h2 : h⁻¹ point ∈ tFix := (mem_tFix_iff (h⁻¹ point)).2 h1
      obtain ⟨j, hj⟩ := (mem_tFix_iff_exists).1 h2
      refine ⟨j, ?_⟩
      change h (fixPt j) = point
      rw [hj, Equiv.Perm.inv_def]
      exact Equiv.apply_symm_apply h point
    · rintro ⟨j, hj⟩
      have hj' : h (fixPt j) = point := hj
      rw [← hj']
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
        (mem_tFix_iff (fixPt j)).1 (fixPt_mem_tFix j)]
  · intro acting index
    exact hπp acting index

end CFSG.ASVolI.AppH.H157
