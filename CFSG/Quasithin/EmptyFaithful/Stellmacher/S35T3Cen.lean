module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Cen (β : Geo H M) (K : Subgroup G)
    (hK : stab β ≤ Subgroup.normalizer (K : Set G)) : Subgroup G where
  carrier := {g | g ∈ stab β ∧ ∀ w ∈ K, ⁅w, g⁆ ∈ Vn β}
  one_mem' := ⟨one_mem _, fun w _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨mul_mem ha hb, fun w hw => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (Std.Vn_normal β ha) _).mp (hcb w hw)
    have h2 := mul_mem (hca w hw) h1
    convert h2 using 1
    simp only [commutatorElement_def]
    group
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨inv_mem ha, fun w hw => ?_⟩
    have hw' : a⁻¹ * w * a ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hK (inv_mem ha)) _).mp hw
    have h := inv_mem (hca _ hw')
    convert h using 1
    simp only [commutatorElement_def]
    group

omit [Finite G] in
theorem Cen_normal (β : Geo H M) (K : Subgroup G)
    (hK : stab β ≤ Subgroup.normalizer (K : Set G)) :
    stab β ≤ Subgroup.normalizer (Cen β K hK : Set G) := by
  have key : ∀ s ∈ stab β, ∀ c ∈ Cen β K hK, s * c * s⁻¹ ∈ Cen β K hK := by
    rintro s hs c ⟨hc, hcw⟩
    refine ⟨mul_mem (mul_mem hs hc) (inv_mem hs), fun w hw => ?_⟩
    have hw' : s⁻¹ * w * s ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hK (inv_mem hs)) _).mp hw
    have h := (Subgroup.mem_normalizer_iff.mp (Std.Vn_normal β hs) _).mp (hcw _ hw')
    convert h using 1
    simp only [commutatorElement_def]
    group
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key s hs c hc, fun hc => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ hc
  simpa [mul_assoc] using this

omit [Finite G] in
theorem conj_mem_of_Cen {β : Geo H M} {K : Subgroup G}
    {hK : stab β ≤ Subgroup.normalizer (K : Set G)} {c x : G} (hc : c ∈ Cen β K hK)
    {P : Subgroup G} (hVP : Vn β ≤ P) (hPK : P ≤ K) (hx : x ∈ P) : c * x * c⁻¹ ∈ P := by
  have h := hc.2 x (hPK hx)
  have e : c * x * c⁻¹ = (⁅x, c⁆)⁻¹ * x := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (inv_mem (hVP h)) hx

@[expose] def Pz (β : Geo H M) (K : Subgroup G) (δ : Geo H M) : Subgroup G :=
  K ⊓ (Vn δ ⊔ Vn β)

omit [Finite G] in
theorem Vn_le_Pz (β δ : Geo H M) {K : Subgroup G} (hVK : Vn β ≤ K) : Vn β ≤ Pz β K δ :=
  le_inf hVK le_sup_right

omit [Finite G] in
theorem Pz_smul_le {β : Geo H M} {K : Subgroup G}
    {hK : stab β ≤ Subgroup.normalizer (K : Set G)} (hVK : Vn β ≤ K) (g : ↥(H ⊔ M))
    (hg : (g : G) ∈ Cen β K hK) (δ : Geo H M) : Pz β K (g • δ) ≤ Pz β K δ := by
  intro x hx
  have hgβ : g • β = β := smul_eq_of_mem_stab hg.1
  have hle : Vn (g • δ) ⊔ Vn β ≤ conjSub (g : G) (Vn δ ⊔ Vn β) := by
    refine sup_le ?_ ?_
    · rw [Vn_smul]
      exact conjSub_mono _ le_sup_left
    · have := Vn_smul g β
      rw [hgβ] at this
      exact this.le.trans (conjSub_mono _ le_sup_right)
  have hxK : x ∈ K := hx.1
  have hy1 : (g : G)⁻¹ * x * g ∈ Vn δ ⊔ Vn β := by
    have hx' : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ ∈ conjSub (g : G) (Vn δ ⊔ Vn β) := by
      have : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x := by group
      rw [this]; exact hle hx.2
    exact conj_mem_conjSub_iff.mp hx'
  have hy2 : (g : G)⁻¹ * x * g ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hK (inv_mem hg.1)) _).mp hxK
  have hyP : (g : G)⁻¹ * x * g ∈ Pz β K δ := ⟨hy2, hy1⟩
  have := conj_mem_of_Cen hg (Vn_le_Pz β δ hVK) inf_le_left hyP
  have e : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x := by group
  rwa [e] at this

omit [Finite G] in
theorem Pz_smul {β : Geo H M} {K : Subgroup G}
    {hK : stab β ≤ Subgroup.normalizer (K : Set G)} (hVK : Vn β ≤ K) (g : ↥(H ⊔ M))
    (hg : (g : G) ∈ Cen β K hK) (δ : Geo H M) : Pz β K (g • δ) = Pz β K δ := by
  refine le_antisymm (Pz_smul_le hVK g hg δ) ?_
  have hg' : ((g⁻¹ : ↥(H ⊔ M)) : G) ∈ Cen β K hK := by
    simpa using inv_mem hg
  have := Pz_smul_le hVK g⁻¹ hg' (g • δ)
  simpa using this

end S35.T3

end F53.Stellmacher

end CFSG.Quasithin
