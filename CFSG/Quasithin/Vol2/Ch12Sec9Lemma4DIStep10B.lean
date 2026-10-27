module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIGrp
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIEnv
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep7

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

open scoped IsMulCommutative

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem conj_fix_V1 {V₁ : Subgroup G} (hV₁2 : Nat.card V₁ = 2) {k : G}
    (hk : k ∈ Subgroup.normalizer (V₁ : Set G)) {v : G} (hv : v ∈ V₁) : k * v * k⁻¹ = v := by
  by_cases hv1 : v = 1
  · subst hv1
    simp
  obtain ⟨x, y, hxy, hall⟩ := Nat.card_eq_two_iff.1 hV₁2
  have hmem : ∀ z : ↥V₁, z = x ∨ z = y := fun z => by
    have hz : z ∈ ({x, y} : Set ↥V₁) := by
      rw [hall]
      exact Set.mem_univ z
    simpa using hz
  set e1 : ↥V₁ := ⟨1, V₁.one_mem⟩ with he1
  set ev : ↥V₁ := ⟨v, hv⟩ with hev
  have he : e1 ≠ ev := fun h => hv1 (congrArg Subtype.val h).symm
  have hclaim : ∀ z : ↥V₁, z = e1 ∨ z = ev := by
    intro z
    rcases hmem e1 with h1 | h1 <;> rcases hmem ev with h2 | h2 <;> rcases hmem z with h3 | h3 <;>
      simp_all
  have hu : k * v * k⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 hk v).1 hv
  rcases hclaim ⟨k * v * k⁻¹, hu⟩ with h | h
  · exfalso
    have h' : k * v * k⁻¹ = 1 := congrArg Subtype.val h
    apply hv1
    calc v = k⁻¹ * (k * v * k⁻¹) * k := by group
      _ = 1 := by rw [h']; group
  · exact congrArg Subtype.val h

theorem DIEnv.DI_inf_V1 (E : DIEnv T L V V₁ V₂ K₁ g D) :
    E.I ⊓ wcSub T L V V₁ ⊓ V₁ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hvI : v ∈ E.I := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hv).1).1
  have hvV : v ∈ V₁ := (Subgroup.mem_inf.1 hv).2
  set w : Additive ↥E.I := Additive.ofMul ⟨v, hvI⟩ with hw
  have hfix : ∀ γ : (Additive ↥E.I) ≃ₗ[ZMod 2] (Additive ↥E.I), γ w = w := by
    intro γ
    obtain ⟨x, hx⟩ := E.kap.surjective γ
    obtain ⟨k, hkK, hkN, hk⟩ := (L128A.HatU.mem_img D).1 x.2
    have hxe : x = ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hkK hkN⟩ := Subtype.ext hk.symm
    rw [← hx, hxe]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [E.action hkN (E.hKI hkK) (E.hK₁H hkK) (L128A.HatU.rho_mem_img D hkK hkN) w]
    exact conj_fix_V1 (card_V₁ E.hs) (E.hK₁H hkK) hvV
  have hw0 : w = 0 := by
    by_contra hne
    obtain ⟨γ, hγ⟩ := fixed_vector_GL (by rw [E.hM]; norm_num) hne
    exact hγ (hfix γ)
  have h1 : (Additive.toMul w : ↥E.I) = 1 := by
    rw [hw0]
    rfl
  have hv1 : v = 1 := congrArg Subtype.val h1
  rw [hv1]
  exact Subgroup.one_mem _

end Env

end CFSG.Quasithin.H13.C1294
