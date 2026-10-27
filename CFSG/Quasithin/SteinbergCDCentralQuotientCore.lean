module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup

theorem central_quotients_preserve_prime_core_quasisimplicity {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (Z : Subgroup G) (hZ : Z ≤ center G) :
    haveI : Z.Normal := normal_of_le_center hZ
    pCore p (G ⧸ Z) = (pCore p G).map (QuotientGroup.mk' Z) ∧
      (pCore p G).map (QuotientGroup.mk' Z) = (pCore p G ⊔ Z).map (QuotientGroup.mk' Z) ∧
      (Group.IsPerfect G →
        (IsQuasisimple (G ⧸ pCore p G) ↔ IsQuasisimple ((G ⧸ Z) ⧸ pCore p (G ⧸ Z)))) := by
  have : Z.Normal := normal_of_le_center hZ
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' Z with hπ
  have hle : (pCore p G).map π ≤ pCore p (G ⧸ Z) :=
    le_sSup ⟨pCore_normal.map π (QuotientGroup.mk'_surjective Z), pCore_isPGroup.map π⟩
  have hge : pCore p (G ⧸ Z) ≤ (pCore p G).map π := by
    set A := (pCore p (G ⧸ Z)).comap π with hA
    have hAn : A.Normal := pCore_normal.comap π
    let f : A →* G ⧸ Z := π.comp A.subtype
    have hfrange : f.range = pCore p (G ⧸ Z) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hA,
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]
    have hfker : f.ker ≤ center A := by
      intro a ha
      rw [mem_center_iff]
      intro b
      have haZ : (a : G) ∈ Z := (QuotientGroup.eq_one_iff (a : G)).mp (MonoidHom.mem_ker.mp ha)
      exact Subtype.ext (mem_center_iff.mp (hZ haZ) b)
    have hrp : IsPGroup p f.range := hfrange ▸ pCore_isPGroup
    have : Group.IsNilpotent f.range := hrp.isNilpotent
    have hAnil : Group.IsNilpotent A :=
      Subgroup.isNilpotent_of_ker_le_center f.rangeRestrict (by rwa [MonoidHom.ker_rangeRestrict])
    obtain ⟨S⟩ : Nonempty (Sylow p A) := inferInstance
    have hSn : (S : Subgroup A).Normal := hAnil.sylow_normal p S
    have hSO : (S : Subgroup A) ≤ pCore p A := le_sSup ⟨hSn, S.isPGroup'⟩
    have hSmap : (S : Subgroup A).map f.rangeRestrict = ⊤ := by
      let S' := S.mapSurjective f.rangeRestrict_surjective
      have h1 : (S' : Subgroup f.range) = ⊤ := (S'.is_maximal' (hrp.to_subgroup ⊤) le_top).symm
      exact h1
    have hOA : (pCore p A).map A.subtype ≤ pCore p G :=
      le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map A.subtype⟩
    intro x hx
    rw [← hfrange] at hx
    have hx' : (⟨x, hx⟩ : f.range) ∈ (S : Subgroup A).map f.rangeRestrict := by
      rw [hSmap]
      exact mem_top _
    obtain ⟨a, haS, ha⟩ := hx'
    have hax : f a = x := congrArg Subtype.val ha
    exact ⟨a, hOA ⟨a, hSO haS, rfl⟩, hax⟩
  have hcore : pCore p (G ⧸ Z) = (pCore p G).map π := le_antisymm hge hle
  have hZbot : Z.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hsup : (pCore p G).map π = (pCore p G ⊔ Z).map π := by
    rw [Subgroup.map_sup, hZbot, sup_bot_eq]
  refine ⟨hcore, hsup, fun hG => ?_⟩
  have hmap : pCore p G ≤ (pCore p (G ⧸ Z)).comap π := map_le_iff_le_comap.mp hle
  let φ := QuotientGroup.map (pCore p G) (pCore p (G ⧸ Z)) π hmap
  have hφ : Function.Surjective φ :=
    QuotientGroup.map_surjective_of_surjective _ _ π
      ((QuotientGroup.mk_surjective).comp (QuotientGroup.mk'_surjective Z)) hmap
  have hker : φ.ker ≤ center (G ⧸ pCore p G) := by
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h := MonoidHom.mem_ker.mp hy
    change ((π g : G ⧸ Z) : (G ⧸ Z) ⧸ pCore p (G ⧸ Z)) = 1 at h
    have hg : π g ∈ pCore p (G ⧸ Z) := (QuotientGroup.eq_one_iff _).mp h
    rw [hcore] at hg
    obtain ⟨c, hc, hcg⟩ := hg
    have hz : c⁻¹ * g ∈ Z := QuotientGroup.eq.mp hcg
    have hy' : (g : G ⧸ pCore p G) = ((c⁻¹ * g : G) : G ⧸ pCore p G) := by
      rw [QuotientGroup.eq]
      have h1 := pCore_normal.conj_mem c⁻¹ (inv_mem hc) g⁻¹
      have e : g⁻¹ * (c⁻¹ * g) = g⁻¹ * c⁻¹ * g⁻¹⁻¹ := by group
      rw [e]
      exact h1
    rw [hy', mem_center_iff]
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp (hZ hz) w]
  have hGq : Group.IsPerfect (G ⧸ pCore p G) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore p G))
  exact CFSG.LocalCores.isQuasisimple_iff_of_surjective hGq φ hφ hker

end CFSG.Quasithin.SteinbergCD
