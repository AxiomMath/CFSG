module

public import CFSG.Quasithin.Vol2.GoldschmidtP778A5E2

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1.LiftS5
open scoped commutatorElement

section Ambient

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isTwoClosed_of_isPGroup {R : Subgroup G} (hR : IsPGroup 2 R) : IsTwoClosed R := by
  refine ⟨R, ⟨le_rfl, hR, ?_⟩, ?_⟩
  · rw [Subgroup.relIndex_self]
    exact fun h => by omega
  · rw [Subgroup.subgroupOf_self]
    infer_instance

theorem isE_one_top_of_card_le_two {H T A : Subgroup G} (ψ : ↥H →* Perm (Fin 5))
    (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (hker : IsPGroup 2 ψ.ker)
    (hT : IsSylowIn 2 T H) (hAT : A ≤ T) (hV : (A.subgroupOf H).map ψ ≠ ⊥)
    (hV2 : Nat.card ↥((A.subgroupOf H).map ψ) ≤ 2) : IsE 1 H T A H := by
  have hTH : T ≤ H := hT.le
  set φ := ψ.rangeRestrict with hφdef
  set f' : ↥ψ.range →* Perm (Fin 5) := ψ.range.subtype with hf'def
  have hf' : Function.Injective f' := Subgroup.subtype_injective _
  have hA5' : alternatingGroup (Fin 5) ≤ f'.range := by
    rw [hf'def, Subgroup.range_subtype]; exact hA5
  have hφs : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ψ
  have hkerφ : φ.ker = ψ.ker := MonoidHom.ker_rangeRestrict ψ
  have hker2 : IsPGroup 2 φ.ker := hkerφ ▸ hker
  have hsolv : Group.IsSolvable ↥φ.ker := by
    have : Group.IsNilpotent ↥φ.ker := hker2.isNilpotent
    infer_instance
  have hpc : CFSG.Open.pCore 2 ↥ψ.range = ⊥ := by
    refine le_bot_iff.mp ((A3.le_solvableRadical inferInstance ?_).trans
      (solvableRadical_eq_bot f' hf' hA5').le)
    have : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥ψ.range) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).isNilpotent
    infer_instance
  have hZ : IsTwoClosed ((CFSG.Open.pCore 2 ↥ψ.range).comap φ) := by
    rw [hpc, MonoidHom.comap_bot]
    exact isTwoClosed_of_isPGroup hker2
  have hSyl' : IsSylowIn 2 ((T ⊓ H).subgroupOf H) (⊤ : Subgroup ↥H) := by
    have := (isSylowIn_subgroupOf_iff (p := 2) (inf_le_right : T ⊓ H ≤ H) le_rfl).mpr
      (by rw [inf_eq_left.mpr hTH]; exact hT)
    rwa [Subgroup.subgroupOf_self] at this
  have hSp : IsPGroup 2 ↥((T ⊓ H).subgroupOf H) := hSyl'.isPGroup
  have hBS : A.subgroupOf H ≤ (T ⊓ H).subgroupOf H :=
    Subgroup.subgroupOf_mono _ (le_inf hAT (hAT.trans hTH))
  have hkerS : φ.ker ≤ (T ⊓ H).subgroupOf H :=
    hSyl'.le_of_normal le_top inferInstance hker2
  have hmin : ∀ M : Subgroup ↥H, (T ⊓ H).subgroupOf H ≤ M → M ⊔ φ.ker = ⊤ → M = ⊤ := by
    intro M hM hMk
    rw [sup_eq_left.mpr (hkerS.trans hM)] at hMk
    exact hMk
  have hres := twoResidual_eq_perfectCore_of_surjective φ hφs hSyl' hmin
    (twoResidual_top_eq_perfectCore f' hf' hA5')
  have hB' : (A.subgroupOf H).map φ ≠ ⊥ := by
    intro h
    apply hV
    have : (A.subgroupOf H).map ψ = ((A.subgroupOf H).map φ).map f' := by
      rw [Subgroup.map_map]; rfl
    rw [this, h, Subgroup.map_bot]
  have hE2 : ETwo ↥H ((T ⊓ H).subgroupOf H) (A.subgroupOf H) :=
    eTwo_of_surjective φ hφs hZ hSp hBS hres
      (eTwo_of_embedding f' hf' hA5' _ hB')
  refine ⟨le_rfl, le_inf (tauOf_le H T A) ((tauOf_le H T A).trans hTH),
    by rw [inf_eq_left.mpr hTH]; exact hT, Or.inr ⟨hE2, ?_⟩⟩
  rw [← card_barRad_eq_of_surjective φ hφs hsolv]
  have hradbot : CFSG.solvableRadical ↥ψ.range = ⊥ := solvableRadical_eq_bot f' hf' hA5'
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical ↥ψ.range)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hradbot]
  have hmapeq : ((A.subgroupOf H).map φ).map f' = (A.subgroupOf H).map ψ := by
    rw [Subgroup.map_map]; rfl
  have h1 : Nat.card ↥(((A.subgroupOf H).map φ).map f') = Nat.card ↥((A.subgroupOf H).map φ) :=
    Subgroup.card_map_of_injective hf'
  rw [hmapeq] at h1
  unfold barRad
  rw [Subgroup.card_map_of_injective hinj, ← h1]
  exact hV2

end Ambient

end CFSG.Quasithin.E1.ThinA5
