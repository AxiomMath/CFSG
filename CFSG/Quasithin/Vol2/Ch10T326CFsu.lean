module

public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem map_centralizer_equiv (σ : G ≃* G) (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).map σ.toMonoidHom =
      Subgroup.centralizer ((X.map σ.toMonoidHom : Subgroup G) : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have h1 := congrArg σ (h w hw)
    simpa using h1
  · intro h w hw
    have h1 := h (σ.toMonoidHom w) ⟨w, hw, rfl⟩
    apply σ.injective
    simpa using h1

theorem map_conjClosure (σ : G ≃* G) (Z H : Subgroup G) :
    (conjClosure Z H).map σ.toMonoidHom =
      conjClosure (Z.map σ.toMonoidHom) (H.map σ.toMonoidHom) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine conjClosure_le fun h hh z hz => ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact mem_conjClosure (Subgroup.mem_map_of_mem σ.toMonoidHom hh)
      (Subgroup.mem_map_of_mem σ.toMonoidHom hz)
  · refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨h', hh', rfl⟩ := hh
    obtain ⟨z', hz', rfl⟩ := hz
    have e : σ.toMonoidHom h' * σ.toMonoidHom z' * (σ.toMonoidHom h')⁻¹ =
        σ.toMonoidHom (h' * z' * h'⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map_of_mem σ.toMonoidHom (mem_conjClosure hh' hz')

theorem map_subgroupOf_equivMap (σ : G ≃* G) (C H : Subgroup G) :
    (C.subgroupOf H).map (H.equivMapOfInjective σ.toMonoidHom σ.injective :
        ↥H →* ↥(H.map σ.toMonoidHom)) =
      (C.map σ.toMonoidHom).subgroupOf (H.map σ.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(w : G), Subgroup.mem_subgroupOf.mp hw, rfl⟩
  · rintro ⟨c, hc, hcy⟩
    have hcH : c ∈ H := by
      obtain ⟨h', hh', hh'y⟩ := y.2
      have h1 : σ.toMonoidHom h' = σ.toMonoidHom c := hh'y.trans hcy.symm
      rw [← (σ.injective : Function.Injective σ.toMonoidHom) h1]
      exact hh'
    exact ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hc, Subtype.ext hcy⟩

theorem isXSectionIso_map {X C J K : Subgroup G} (σ : G ≃* G) (h : IsXSectionIso X C J K) :
    IsXSectionIso (X.map σ.toMonoidHom) (C.map σ.toMonoidHom) (J.map σ.toMonoidHom)
      (K.map σ.toMonoidHom) := by
  obtain ⟨hJn, hKn, e, he⟩ := h
  obtain ⟨eJ, heJ⟩ : ∃ f, f = J.equivMapOfInjective σ.toMonoidHom σ.injective := ⟨_, rfl⟩
  obtain ⟨eK, heK⟩ : ∃ f, f = K.equivMapOfInjective σ.toMonoidHom σ.injective := ⟨_, rfl⟩
  have hJ : (C.subgroupOf J).map (eJ : ↥J →* ↥(J.map σ.toMonoidHom)) =
      (C.map σ.toMonoidHom).subgroupOf (J.map σ.toMonoidHom) := by
    rw [heJ]
    exact map_subgroupOf_equivMap σ C J
  have hK : (C.subgroupOf K).map (eK : ↥K →* ↥(K.map σ.toMonoidHom)) =
      (C.map σ.toMonoidHom).subgroupOf (K.map σ.toMonoidHom) := by
    rw [heK]
    exact map_subgroupOf_equivMap σ C K
  have hJn' : ((C.map σ.toMonoidHom).subgroupOf (J.map σ.toMonoidHom)).Normal :=
    hJ ▸ hJn.map (eJ : ↥J →* ↥(J.map σ.toMonoidHom)) eJ.surjective
  have hKn' : ((C.map σ.toMonoidHom).subgroupOf (K.map σ.toMonoidHom)).Normal :=
    hK ▸ hKn.map (eK : ↥K →* ↥(K.map σ.toMonoidHom)) eK.surjective
  have hvJ : ∀ j : ↥J, ((eJ j : ↥(J.map σ.toMonoidHom)) : G) = σ.toMonoidHom (j : G) :=
      fun j => by
    rw [heJ]
    rfl
  have hvK : ∀ k : ↥K, ((eK k : ↥(K.map σ.toMonoidHom)) : G) = σ.toMonoidHom (k : G) :=
      fun k => by
    rw [heK]
    rfl
  refine ⟨hJn', hKn', ((QuotientGroup.congr _ _ eJ hJ).symm.trans e).trans
    (QuotientGroup.congr _ _ eK hK), ?_⟩
  intro x' hx' j' k' hj' hk' hjk
  obtain ⟨x, hx, rfl⟩ := hx'
  obtain ⟨j, rfl⟩ := eJ.surjective j'
  obtain ⟨k, rfl⟩ := eK.surjective k'
  have hsJ : ∀ j : ↥J, (QuotientGroup.congr _ _ eJ hJ).symm
      ((eJ j : ↥(J.map σ.toMonoidHom)) : ↥(J.map σ.toMonoidHom) ⧸
        (C.map σ.toMonoidHom).subgroupOf (J.map σ.toMonoidHom)) =
      ((j : ↥J) : ↥J ⧸ C.subgroupOf J) := fun j => by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have hcK : ∀ k : ↥K, QuotientGroup.congr _ _ eK hK ((k : ↥K) : ↥K ⧸ C.subgroupOf K) =
      ((eK k : ↥(K.map σ.toMonoidHom)) : ↥(K.map σ.toMonoidHom) ⧸
        (C.map σ.toMonoidHom).subgroupOf (K.map σ.toMonoidHom)) := fun k => rfl
  simp only [MulEquiv.trans_apply] at hjk ⊢
  rw [hsJ, ← hcK] at hjk
  have hjk' := (QuotientGroup.congr _ _ eK hK).injective hjk
  have hj : x * (j : G) * x⁻¹ ∈ J := by
    have h1 := hj'
    rw [hvJ, ← map_inv, ← map_mul, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem (σ.injective : Function.Injective σ.toMonoidHom)).mp h1
  have hk : x * (k : G) * x⁻¹ ∈ K := by
    have h1 := hk'
    rw [hvK, ← map_inv, ← map_mul, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem (σ.injective : Function.Injective σ.toMonoidHom)).mp h1
  have h2 := he x hx j k hj hk hjk'
  have eJ' : (⟨σ.toMonoidHom x * ((eJ j : ↥(J.map σ.toMonoidHom)) : G) * (σ.toMonoidHom x)⁻¹,
      hj'⟩ : ↥(J.map σ.toMonoidHom)) = eJ ⟨x * (j : G) * x⁻¹, hj⟩ := by
    apply Subtype.ext
    show σ.toMonoidHom x * ((eJ j : ↥(J.map σ.toMonoidHom)) : G) * (σ.toMonoidHom x)⁻¹ =
      ((eJ ⟨x * (j : G) * x⁻¹, hj⟩ : ↥(J.map σ.toMonoidHom)) : G)
    rw [hvJ, hvJ]
    simp
  have eK' : (⟨σ.toMonoidHom x * ((eK k : ↥(K.map σ.toMonoidHom)) : G) * (σ.toMonoidHom x)⁻¹,
      hk'⟩ : ↥(K.map σ.toMonoidHom)) = eK ⟨x * (k : G) * x⁻¹, hk⟩ := by
    apply Subtype.ext
    show σ.toMonoidHom x * ((eK k : ↥(K.map σ.toMonoidHom)) : G) * (σ.toMonoidHom x)⁻¹ =
      ((eK ⟨x * (k : G) * x⁻¹, hk⟩ : ↥(K.map σ.toMonoidHom)) : G)
    rw [hvK, hvK]
    simp
  rw [eJ', eK', hsJ, h2]
  rfl

end CFSG.Quasithin.Vol2.Ch10
