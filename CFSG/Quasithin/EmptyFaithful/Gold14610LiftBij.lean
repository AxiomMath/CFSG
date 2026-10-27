module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

variable {G : Type} [Group G] [Finite G]

theorem imgMod3_bijOn (I : Subgroup G) (hs : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥I)) :
    Set.BijOn (imgMod3 I) (cComp I) (cComp (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))) :=
  (cComp_quotient_bijOn (CFSG.pPrimeCore 3 ↥I) hs).comp (cComp_subgroupOf_bijOn I)

omit [Finite G] in
theorem map_conj_eq_self {I : Subgroup G} {g : G} (hg : g ∈ I) :
    I.map (MulAut.conj g).toMonoidHom = I := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using I.mul_mem (I.mul_mem hg hy) (I.inv_mem hg)
  · intro hx
    exact ⟨g⁻¹ * x * g, I.mul_mem (I.mul_mem (I.inv_mem hg) hx) hg, by simp [mul_assoc]⟩

omit [Finite G] in
theorem imgMod3_map_conj {I K : Subgroup G} {g : G} (hg : g ∈ I)
    (hn : (imgMod3 I K).Normal) :
    imgMod3 I (K.map (MulAut.conj g).toMonoidHom) = imgMod3 I K := by
  set b : ↥I := ⟨g, hg⟩ with hb
  have key : ∀ a : ↥I, ((b * a * b⁻¹ : ↥I) : G) = g * a * g⁻¹ := fun a => rfl
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha)
    have hk' : b⁻¹ * a * b ∈ K.subgroupOf I := by
      rw [Subgroup.mem_subgroupOf]
      have h1 : g * k * g⁻¹ = (a : G) := hka
      have : ((b⁻¹ * a * b : ↥I) : G) = k := by
        simp [hb, ← h1, mul_assoc]
      rw [this]
      exact hk
    have h2 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) (b⁻¹ * a * b) ∈ imgMod3 I K :=
      ⟨_, hk', rfl⟩
    have h3 := hn.conj_mem _ h2 (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) b)
    simpa [map_mul, map_inv, mul_assoc] using h3
  · intro hu
    have h1 := hn.conj_mem u hu ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) b)⁻¹)
    obtain ⟨a, ha, hau⟩ := h1
    refine Subgroup.mem_map.mpr ⟨b * a * b⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, key]
      exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have : (a : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) = (b : ↥I ⧸ CFSG.pPrimeCore 3 ↥I)⁻¹ * u * b := by
        simpa using hau
      rw [this]
      group

theorem le_normalizer_of_imgMod3_normal {I K : Subgroup G}
    (hs : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥I)) (hK : K ∈ cComp I)
    (hn : (imgMod3 I K).Normal) : I ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  have hK' : K.map (MulAut.conj g).toMonoidHom ∈ cComp I := by
    have h := cComp_map_mulEquiv (MulAut.conj g) hK
    rwa [map_conj_eq_self hg] at h
  have heq : K.map (MulAut.conj g).toMonoidHom = K :=
    (imgMod3_bijOn I hs).injOn hK' hK (imgMod3_map_conj hg hn)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [heq] at h1
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h2 : y = x := by
      have : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using this
    rw [h2] at hy
    exact hy

end Gold14610

end CFSG.Quasithin
