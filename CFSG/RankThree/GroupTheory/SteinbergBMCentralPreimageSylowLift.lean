module

public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG

variable {M : Type*} [Group M]

theorem central_preimage_two_group_characteristic_sylow_lift [Finite M] {E : Type*} [Group E]
    (f : M →* E) (hf : Function.Surjective f) (hZ : f.ker ≤ center M) (hE : IsPGroup 2 E) :
    ∃ P : Sylow 2 M, (∀ Q : Sylow 2 M, Q = P) ∧ (P : Subgroup M).Characteristic ∧
      (P : Subgroup M).map f = ⊤ ∧
      (P : Subgroup M) ⊓ f.ker = inSubgroup (pCore 2) f.ker ∧
      inSubgroup (pPrimeCore 2) f.ker ⊓ (P : Subgroup M) = ⊥ ∧
      inSubgroup (pPrimeCore 2) f.ker ⊔ (P : Subgroup M) = ⊤ ∧
      (∀ x ∈ inSubgroup (pPrimeCore 2) f.ker, ∀ y ∈ (P : Subgroup M), x * y = y * x) ∧
      ∀ σ : MulAut M, (P : Subgroup M).map σ.toMonoidHom = P := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := inferInstance
  have hcentral : ∀ z ∈ f.ker, ∀ m : M, m * z = z * m := fun z hz => mem_center_iff.mp (hZ hz)
  have hPE : (P : Subgroup M).map f = ⊤ := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤) (hE.of_equiv topEquiv.symm) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hZP : f.ker ⊔ (P : Subgroup M) = ⊤ := by
    refine eq_top_iff.mpr fun m _ => ?_
    obtain ⟨q, hq, hfq⟩ : f m ∈ (P : Subgroup M).map f := by rw [hPE]; exact mem_top _
    have hm : m = (m * q⁻¹) * q := by group
    rw [hm]
    refine mul_mem_sup (MonoidHom.mem_ker.mpr ?_) hq
    rw [map_mul, map_inv, hfq, mul_inv_cancel]
  have hPn : (P : Subgroup M).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hZP]
    refine sup_le (fun z hz => centralizer_le_normalizer _ ?_) le_normalizer
    rw [mem_centralizer_iff]
    intro m _
    exact hcentral z hz m
  have huniq : ∀ Q : Sylow 2 M, Q = P := fun Q =>
    (Sylow.unique_of_normal P hPn).uniq Q |>.trans ((Sylow.unique_of_normal P hPn).uniq P).symm
  have hchar : (P : Subgroup M).Characteristic := Sylow.characteristic_of_normal P hPn
  have h2P : ∀ Q : Subgroup M, IsPGroup 2 Q → Q ≤ P := fun Q hQ => by
    obtain ⟨R, hR⟩ := hQ.exists_le_sylow
    rwa [huniq R] at hR
  have hO2 : inSubgroup (pCore 2) f.ker ≤ P :=
    h2P _ ((CFSG.pCore_isPGroup (p := 2) (G := f.ker)).map f.ker.subtype)
  have hPZ : (P : Subgroup M) ⊓ f.ker = inSubgroup (pCore 2) f.ker := by
    refine le_antisymm (le_inSubgroup_pCore_of_normal (P.isPGroup'.to_le inf_le_left) inf_le_right
      fun z hz => centralizer_le_normalizer _ ?_) (le_inf hO2 (map_subtype_le _))
    rw [mem_centralizer_iff]
    intro m _
    exact hcentral z hz m
  have hZo2 : Nat.Coprime 2 (Nat.card (inSubgroup (pPrimeCore 2) f.ker)) := by
    rw [inSubgroup, card_map_of_injective f.ker.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 2) (G := f.ker)
  have hinf : inSubgroup (pPrimeCore 2) f.ker ⊓ (P : Subgroup M) = ⊥ := by
    refine disjoint_iff.mp (disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk]
    exact (Nat.Coprime.pow_left k hZo2).symm
  have hZle : f.ker ≤ inSubgroup (pCore 2) f.ker ⊔ inSubgroup (pPrimeCore 2) f.ker := by
    have hab : Group.IsNilpotent f.ker := by
      have : IsMulCommutative f.ker := ⟨⟨fun x y => Subtype.ext (hcentral y y.2 x)⟩⟩
      infer_instance
    have h := map_mono (f := f.ker.subtype)
      (CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (p := 2) hab)
    rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
  have hsup : inSubgroup (pPrimeCore 2) f.ker ⊔ (P : Subgroup M) = ⊤ := by
    rw [eq_top_iff, ← hZP]
    refine sup_le (hZle.trans (sup_le (hO2.trans le_sup_right) le_sup_left)) le_sup_right
  refine ⟨P, huniq, hchar, hPE, hPZ, hinf, hsup, fun x hx y _ => ?_,
    fun σ => characteristic_iff_map_eq.mp hchar σ⟩
  exact (hcentral x (map_subtype_le _ hx) y).symm

theorem central_preimage_two_group_characteristic_sylow_lift_comap {V W : Type*} [Group V]
    [Group W] [Finite V] (f₀ : V →* W) (hker : f₀.ker ≤ center V) {E : Subgroup W}
    (hE : IsPGroup 2 E) (hEf : E ≤ f₀.range) :
    let M := E.comap f₀
    let g : M →* E := (f₀.comp M.subtype).codRestrict E fun x => x.2
    Function.Surjective g ∧ g.ker.map M.subtype = f₀.ker ∧ g.ker ≤ center M ∧
      ∃ P : Sylow 2 M, (∀ Q : Sylow 2 M, Q = P) ∧
        ∀ σ : MulAut V, M.map σ.toMonoidHom = M →
          ((P : Subgroup M).map M.subtype).map σ.toMonoidHom = (P : Subgroup M).map M.subtype := by
  intro M g
  have hg : ∀ x : M, (g x : W) = f₀ x := fun _ => rfl
  have hsurj : Function.Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := hEf hw
    exact ⟨⟨v, hw⟩, rfl⟩
  have hkerg : g.ker.map M.subtype = f₀.ker := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    · intro hv
      have hvM : v ∈ M := by
        change f₀ v ∈ E
        rw [MonoidHom.mem_ker.mp hv]
        exact one_mem E
      exact ⟨⟨v, hvM⟩, MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp hv)), rfl⟩
  have hcen : g.ker ≤ center M := by
    intro x hx
    have hxv : (x : V) ∈ f₀.ker := by rw [← hkerg]; exact mem_map_of_mem _ hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hker hxv) y)
  obtain ⟨P, huniq, hchar, -⟩ :=
    central_preimage_two_group_characteristic_sylow_lift g hsurj hcen
      (hE.of_equiv (MulEquiv.refl _))
  refine ⟨hsurj, hkerg, hcen, P, huniq, fun σ hσ => ?_⟩
  let τ : MulAut M := (σ.subgroupMap M).trans (MulEquiv.subgroupCongr hσ)
  have hτ : ∀ x : M, ((τ x : M) : V) = σ x := fun _ => rfl
  have hPτ := characteristic_iff_map_eq.mp hchar τ
  calc ((P : Subgroup M).map M.subtype).map σ.toMonoidHom =
        ((P : Subgroup M).map τ.toMonoidHom).map M.subtype := by
          rw [map_map, map_map]
          rfl
    _ = (P : Subgroup M).map M.subtype := by rw [hPτ]

end CFSG.RankThree.GroupTheory.SteinbergBM
