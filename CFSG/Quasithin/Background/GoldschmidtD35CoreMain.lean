module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreConj
public import CFSG.Quasithin.Background.GoldschmidtD35CoreOff3
public import CFSG.Quasithin.Background.GoldschmidtD35CoreReal

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin Equiv
open scoped Matrix LinearAlgebra.Projectivization

theorem d35ValCore_holds : D35ValCore := by
  intro K _ _ Γ hval α E F hE hF hrel
  classical
  obtain ⟨pt, hO⟩ := exists_isSixOrbit (threeQuaternaryData_of_valentiner hval)
  obtain ⟨a, b, hab, hEab⟩ := exists_fixTwo_of_offender hval hO hE
  obtain ⟨c, d, hcd, hFcd⟩ := exists_fixTwo_of_offender hval hO hF
  set e := actEquiv hval hO with he
  have hQE : ∀ (G : Subgroup Γ) (x : alternatingGroup (Fin 6))
      (p : alternatingGroup (Fin 6) → Prop),
      (∀ z, p z ↔ ∃ γ ∈ G, actHom hO γ = z) →
      (p x ↔ e.symm x ∈ G.map (QuotientGroup.mk' (Subgroup.center Γ))) := by
    intro G x p hp
    obtain ⟨q, rfl⟩ := e.surjective x
    obtain ⟨γ₀, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulEquiv.symm_apply_apply, hp]
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨γ, hγ, ?_⟩
      exact e.injective (by rw [← h]; rfl)
    · rintro ⟨γ, hγ, h⟩
      exact ⟨γ, hγ, ((actEquiv_mk hval hO γ).symm).trans (congrArg e h)⟩
  let α'' : MulAut (alternatingGroup (Fin 6)) := e.symm.trans (α.trans e)
  have hα''_apply : ∀ x, α'' x = e (α (e.symm x)) := fun x => rfl
  have hiff : ∀ x, FixTwo a b x ↔ FixTwo c d (α'' x) := by
    intro x
    rw [hQE E x _ hEab, hα''_apply, hQE F _ _ hFcd, MulEquiv.symm_apply_apply, ← hrel]
    constructor
    · exact fun h => Subgroup.mem_map_of_mem _ h
    · rintro ⟨q, hq, hqα⟩
      exact α.injective hqα ▸ hq
  obtain ⟨σ, hσ⟩ := exists_perm_of_fixTwo α'' hab hcd hiff
  obtain ⟨n, hn⟩ := hO.exists_induces hval.1 (Module.finrank_fin_fun K)
    (threeQuaternaryData_of_valentiner hval).irreducible σ
  obtain ⟨β, Φ, hβperm, hΦ⟩ := exists_conj_aut hval hO hn
  refine ⟨β, Φ, fun γ => ?_, hΦ⟩
  apply e.injective
  have h1 : e (QuotientGroup.mk' (Subgroup.center Γ) (β γ)) = actHom hO (β γ) :=
    actEquiv_mk hval hO _
  have h2 : e (α (QuotientGroup.mk' (Subgroup.center Γ) γ)) = α'' (actHom hO γ) := by
    rw [hα''_apply]
    congr 2
    rw [← actEquiv_mk hval hO, MulEquiv.symm_apply_apply]
    rfl
  rw [h1, h2]
  apply Subtype.ext
  rw [hσ, coe_actHom, hβperm]
  rfl

end CFSG.Quasithin.D35Core
