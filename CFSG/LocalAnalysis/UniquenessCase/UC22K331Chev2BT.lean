module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
import CFSG.GH74.Exceptional.LinearFourTwoSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

theorem k331At_of_solvBorel {L : Type} [Group L] [Finite L]
    (hBT : ∀ T : Subgroup L, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → ∀ H : Subgroup L, T ≤ H →
      Group.IsSolvable H → H ≤ Subgroup.normalizer (T : Set L)) : K331At L := by
  intro T hT K hK hTK
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hK
  obtain ⟨S, hS⟩ := ((hT.of_le le_sup_right le_top).inf_of_le_normalizer le_sup_left
    (sup_le Subgroup.le_normalizer hTK)).exists_sylow_eq_subgroupOf
  have hSmem : ∀ k : K, k ∈ (S : Subgroup K) ↔ (k : L) ∈ T := fun k => by
    rw [hS, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, k.2⟩⟩
  set R : Subgroup K := CFSG.pCore 2 K
  set π : K →* Bar2 K := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hRS : R ≤ S := CFSG.pCore_isPGroup.le_sylow_of_normal S
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup (Bar2 K), P = (S : Subgroup K).map π := ⟨_, rfl⟩
  have hPmem : ∀ k : K, π k ∈ P ↔ k ∈ (S : Subgroup K) := fun k => by
    rw [hPdef, ← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.2 hRS]
  have hPp : IsPGroup 2 P := hPdef ▸ S.isPGroup'.map π
  have hPi : ¬ 2 ∣ P.index := fun h =>
    S.not_dvd_index (h.trans (hPdef ▸ Subgroup.index_map_dvd _ hπ))
  obtain ⟨hsolv, hnle⟩ :=
    CFSG.GH74.Exceptional.normalizer_centralizer_sylow_of_alt_eight e hPp hPi
  set NC := Subgroup.normalizer (Subgroup.centralizer (P : Set (Bar2 K)) : Set (Bar2 K))
  have hY0 : Group.IsSolvable (NC.comap π) := by
    let ι := (NC.comap π).subtype
    have hRp : IsPGroup 2 (R.comap ι) :=
      CFSG.pCore_isPGroup.comap_of_injective ι (Subgroup.subtype_injective _)
    have : Group.IsNilpotent (R.comap ι) := hRp.isNilpotent
    have : Group.IsSolvable NC := hsolv
    refine Group.isSolvable_of_ker_le_range (R.comap ι).subtype (π.subgroupComap NC)
      fun x hx => ?_
    rw [Subgroup.range_subtype, Subgroup.mem_comap]
    have h1 : π (x : K) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hx)
    exact (QuotientGroup.eq_one_iff _).1 h1
  set Y : Subgroup L := (NC.comap π).map K.subtype
  have hYsolv : Group.IsSolvable Y :=
    Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective (NC.comap π))
  have hTY : T ≤ Subgroup.normalizer (Y : Set L) := by
    intro t ht
    let α : K ≃* K := Subgroup.normalizerMonoidHom (H := K) ⟨t, hTK ht⟩
    have hα : ∀ k : K, (α k : L) = t * k * t⁻¹ := fun k => rfl
    let β : Bar2 K ≃* Bar2 K :=
      QuotientGroup.congr R R α (Subgroup.characteristic_iff_map_eq.1 inferInstance α)
    have hβ : ∀ k : K, β (π k) = π (α k) := fun k => rfl
    have hPβ : P = P.comap (β : Bar2 K →* Bar2 K) := by
      ext x
      obtain ⟨k, rfl⟩ := hπ x
      rw [Subgroup.mem_comap]
      change π k ∈ P ↔ β (π k) ∈ P
      rw [hβ, hPmem, hPmem, hSmem, hSmem, hα]
      exact Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht) k
    have hNβ : NC = NC.comap (β : Bar2 K →* Bar2 K) := by
      have h := CFSG.GH74.Exceptional.normalizer_centralizer_comap_mulEquiv β P
      rw [← hPβ] at h
      exact h
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨α k, ?_, rfl⟩
    rw [Subgroup.mem_comap] at hk ⊢
    rw [hNβ, Subgroup.mem_comap] at hk
    exact hk
  have : Group.IsNilpotent T := hT.isPGroup.isNilpotent
  have hYT := hBT T hT (Y ⊔ T) le_sup_right
    (CFSG.SignalizerFunctor.Helpers.solvable_sup_of_normalizing Y T hTY hYsolv inferInstance)
  refine hnle fun x hx => ?_
  obtain ⟨k, rfl⟩ := hπ x
  have hkT : (k : L) ∈ Subgroup.normalizer (T : Set L) :=
    hYT (le_sup_left (a := Y) (Subgroup.mem_map_of_mem K.subtype (show k ∈ NC.comap π from hx)))
  refine Subgroup.mem_normalizer_iff.2 fun h => ?_
  obtain ⟨j, rfl⟩ := hπ h
  rw [← map_inv, ← map_mul, ← map_mul, hPmem, hPmem, hSmem, hSmem]
  exact Subgroup.mem_normalizer_iff.1 hkT j

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
