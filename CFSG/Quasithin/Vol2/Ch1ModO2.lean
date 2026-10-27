
module

public import CFSG.Quasithin.Vol2.Ch1Quotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def modO2Image (H L : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

theorem modO2Image_bijOn (H : Subgroup G) :
    Set.BijOn (modO2Image H) (cComp H) (cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) := by
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  exact (cComp_quotient_bijOn (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)).comp
    (cComp_subgroupOf_bijOn H)

theorem modO2Image_mem_cComp {H L : Subgroup G} (hL : L ∈ cComp H) :
    modO2Image H L ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  (modO2Image_bijOn H).mapsTo hL

theorem modO2Image_injOn (H : Subgroup G) : Set.InjOn (modO2Image H) (cComp H) :=
  (modO2Image_bijOn H).injOn

theorem exists_cComp_modO2Image_eq {H : Subgroup G}
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : K ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) :
    ∃ L ∈ cComp H, modO2Image H L = K :=
  (modO2Image_bijOn H).surjOn hK

theorem exists_modO2_surjection {H L : Subgroup G} (hL : L ∈ cComp H) :
    ∃ ψ : ↥L →* ↥(modO2Image H L), Function.Surjective ψ ∧ ψ.ker = CFSG.pCore 2 ↥L := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set N := CFSG.pCore 2 ↥H with hN
  let φ : ↥L →* (↥H ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.inclusion hLH)
  have hrange : φ.range = modO2Image H L := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = CFSG.pCore 2 ↥L := by
    apply le_antisymm
    ·
      have hkp : IsPGroup 2 φ.ker := by
        intro x
        have hx : Subgroup.inclusion hLH (x : ↥L) ∈ N := by
          have := x.2
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at this
          exact this
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
        refine ⟨k, Subtype.ext ?_⟩
        have h1 : (Subgroup.inclusion hLH (x : ↥L)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
        rw [← map_pow] at h1
        exact (Subgroup.inclusion_injective hLH) (by simpa using h1)
      exact le_sSup ⟨inferInstance, hkp⟩
    ·
      intro x hx
      have hxG : (x : G) ∈ pCoreOf 2 L := by
        exact ⟨x, hx, rfl⟩
      have hxH : (x : G) ∈ pCoreOf 2 H :=
        A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL) hxG
      have hxH' : (x : G) ∈ (CFSG.pCore 2 ↥H).map H.subtype := by
        exact hxH
      obtain ⟨y, hy, hyx⟩ := hxH'
      have hy' : y = Subgroup.inclusion hLH x := Subtype.ext hyx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, ← hy']
      exact hy
  refine ⟨((MulEquiv.subgroupCongr hrange).toMonoidHom).comp φ.rangeRestrict, ?_, ?_⟩
  · exact (MulEquiv.subgroupCongr hrange).surjective.comp φ.rangeRestrict_surjective
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hrange).injective,
      MonoidHom.ker_rangeRestrict, hker]

theorem modO2_mulEquiv {H L : Subgroup G} (hL : L ∈ cComp H) :
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(modO2Image H L)) := by
  obtain ⟨ψ, hsurj, hker⟩ := exists_modO2_surjection hL
  have hnorm : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩

end CFSG.Quasithin
