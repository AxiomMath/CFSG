module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Plain
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocFinal2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique U42F431
  CFSG.Quasithin.LieSetting CFSG.Quasithin.H13 CFSG.LieType.BorelTits

theorem u42LocalCent_holds :
    U42LocalCent := by
  intro G _ _ _ _ M₁ M₂ iso _ hcz _ hN2
  let φ1 : ↥P1 →* G := M₁.subtype.comp (isoP1 iso).toMonoidHom
  let φ2 : ↥P2 →* G := M₂.subtype.comp (isoP2 iso).toMonoidHom
  have hφ2mem : ∀ p, φ2 p ∈ M₂ := fun p => (isoP2 iso p).2
  have hrange2 : ∀ g ∈ M₂, g ∈ φ2.range := fun g hg => ⟨(isoP2 iso).symm ⟨g, hg⟩, by simp [φ2]⟩
  have hV2 : (Subgroup.map φ2 (Vsub.subgroupOf P2) : Subgroup G) =
      centerOf (pCoreOf 2 M₂) := by
    have h1 : CFSG.Open.pCore 2 ↥P2 = Vsub.subgroupOf P2 := by
      have h2 := pCoreOf_P2
      have h3 : (CFSG.Open.pCore 2 ↥P2).map P2.subtype = Vsub := h2
      rw [← h3]
      exact (Subgroup.comap_map_eq_self_of_injective P2.subtype_injective _).symm
    have h4 : pCoreOf 2 M₂ = Subgroup.map φ2 (Vsub.subgroupOf P2) := by
      change (CFSG.Open.pCore 2 ↥M₂).map M₂.subtype = _
      rw [← map_pCore_mulEquiv 2 (isoP2 iso), h1, Subgroup.map_map]
    have hab : ∀ a ∈ Subgroup.map φ2 (Vsub.subgroupOf P2),
        ∀ b ∈ Subgroup.map φ2 (Vsub.subgroupOf P2), a * b = b * a := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg φ2 (Subtype.ext (Vsub_comm hx hy))
    apply le_antisymm
    · intro x hx
      rw [h4]
      exact ⟨hx, Subgroup.mem_centralizer_iff.2 fun h hh => hab h hh x hx⟩
    · intro x hx
      rw [h4] at hx
      exact hx.1
  let C : Ctx G :=
    { φ1 := φ1
      φ2 := φ2
      inj1 := M₁.subtype_injective.comp (isoP1 iso).injective
      inj2 := M₂.subtype_injective.comp (isoP2 iso).injective
      agree := fun b h1 h2 => by
        have e1 := congrArg Subtype.val (isoB_comm1 iso ⟨b, h1, h2⟩)
        have e2 := congrArg Subtype.val (isoB_comm2 iso ⟨b, h1, h2⟩)
        exact e1.symm.trans e2
      cent := fun g hg => by
        have hgz : g ∈ Subgroup.centralizer ({((isoP1 iso ⟨xY, xY_mem_P1⟩ : ↥M₁) : G)} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.2 hg
        exact ⟨(isoP1 iso).symm ⟨g, hcz hgz⟩, by simp [φ1]⟩
      norm := fun g hg => by
        rw [hV2] at hg
        exact hrange2 g (hN2 ▸ hg) }
  obtain ⟨m, hmP, hm⟩ := exists_P2_conj_tPrime
  intro g hg
  have hφtY : ((isoP2 iso ⟨tY, tY_mem_P2⟩ : ↥M₂) : G) = C.Φ2 tY :=
    (C.Φ2_of_mem tY_mem_P2).symm
  have hΦ : C.Φ2 tY = C.Φ2 m * C.tG * (C.Φ2 m)⁻¹ := by
    rw [← hm, C.Φ2_conj hmP (Vsub_le_P2 tPrime_mem_Vsub)]
    rfl
  have hc : (C.Φ2 m)⁻¹ * g * C.Φ2 m ∈ Subgroup.centralizer ({C.tG} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hg
    rw [hφtY, hΦ] at h1
    calc (C.Φ2 m)⁻¹ * g * C.Φ2 m * C.tG
        = (C.Φ2 m)⁻¹ * (g * (C.Φ2 m * C.tG * (C.Φ2 m)⁻¹)) * C.Φ2 m := by group
      _ = (C.Φ2 m)⁻¹ * ((C.Φ2 m * C.tG * (C.Φ2 m)⁻¹) * g) * C.Φ2 m := by rw [h1]
      _ = C.tG * ((C.Φ2 m)⁻¹ * g * C.Φ2 m) := by group
  obtain ⟨p, hp⟩ := C.centralizer_tG_le_range hc
  have hmM : C.Φ2 m ∈ M₂ := by
    rw [C.Φ2_of_mem hmP]
    exact hφ2mem _
  have hg' : g = C.Φ2 m * C.φ2 p * (C.Φ2 m)⁻¹ := by
    rw [hp]
    group
  rw [hg']
  exact M₂.mul_mem (M₂.mul_mem hmM (hφ2mem p)) (M₂.inv_mem hmM)

end CFSG.Quasithin.H13.F431.U42
