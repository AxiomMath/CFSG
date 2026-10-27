module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep5

open scoped IsMulCommutative

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

section Env

variable {G : Type} [Group G] [Finite G]

structure DIEnv (T L V V₁ V₂ K₁ : Subgroup G) (g : G) (D : HatModelU (u128 V V₁)) where
  hcx : Cx1291 G T L V 4
  hs : Setting1282One G T L V 4 V₁ V₂
  hLK : lOne L V₁ ≤ K₁
  hgP : g ∈ p128 T L V
  hgN : g ∉ Subgroup.normalizer (V₁ : Set G)
  hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G)
  hK₁U : K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G)
  hker : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
    D.ρ ⟨k, hkN⟩ = 1 ↔ k ∈ pCoreOf 2 K₁
  himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2
  hTΩ : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
    D.ρ ⟨t, htU⟩ ∈ D.img K₁
  I : Subgroup G
  [comm : IsMulCommutative ↥I]
  [mod : Module (ZMod 2) (Additive ↥I)]
  hIZ : I ≤ zU128 V V₁
  hTI : T ≤ Subgroup.normalizer (I : Set G)
  hKI : K₁ ≤ Subgroup.normalizer (I : Set G)
  hI16 : Nat.card I = 16
  kap : ↥(D.img K₁) ≃* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I)
  hact : ∀ x : G, ∀ (hxU : x ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hxI : x ∈ Subgroup.normalizer (I : Set G)) (hxH : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxΩ : D.ρ ⟨x, hxU⟩ ∈ D.img K₁),
    linAct (V := I) ⟨x, hxI⟩ = kap ⟨D.ρ ⟨x, hxU⟩, hxΩ⟩
  S : Submodule (ZMod 2) D.V
  hS3 : Module.finrank (ZMod 2) S = 3
  hSV : ∀ v ∈ V, D.π v ∈ S
  hSπ : ∀ s ∈ S, ∃ v ∈ V, D.π v = s
  fp : Submodule (ZMod 2) (Additive ↥I)
  fl : Submodule (ZMod 2) (Additive ↥I)
  fPl : Submodule (ZMod 2) (Additive ↥I)
  hM : Module.finrank (ZMod 2) (Additive ↥I) = 4
  hp : Module.finrank (ZMod 2) fp = 1
  hℓ : Module.finrank (ZMod 2) fl = 2
  hPl : Module.finrank (ZMod 2) fPl = 3
  hpℓ : fp < fl
  hℓPl : fl < fPl
  a : G
  haV₂ : a ∈ V₂
  haV₁ : a ∉ V₁
  hY₁ : kmapOf (D.img K₁) kap (stabS (Submodule.span (ZMod 2) {D.π a})) = stabS fl
  hY₂ : kmapOf (D.img K₁) kap (stabS S) = stabS fp ∨ kmapOf (D.img K₁) kap (stabS S) = stabS fPl
  hD0 : kmapOf (D.img K₁) kap (D.img (CFSG.conjugate (zU128 V V₁) g)) =
    pCoreOf 2 (kmapOf (D.img K₁) kap (stabS S)) ⊓ pCoreOf 2 (stabS fl)
  hDg4 : Nat.card ↥(D.img (CFSG.conjugate (zU128 V V₁) g)) = 4
  y₀ : G
  hy₀ : y₀ ∈ L ⊓ Subgroup.centralizer (V₂ : Set G)
  hy₀3 : orderOf y₀ = 3

attribute [instance] DIEnv.comm DIEnv.mod

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem DIEnv.action (E : DIEnv T L V V₁ V₂ K₁ g D) {x : G}
    (hxU : x ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hxI : x ∈ Subgroup.normalizer (E.I : Set G)) (hxH : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxΩ : D.ρ ⟨x, hxU⟩ ∈ D.img K₁) (v : Additive ↥E.I) :
    ((Additive.toMul (E.kap ⟨D.ρ ⟨x, hxU⟩, hxΩ⟩ v) : ↥E.I) : G) =
      x * ((Additive.toMul v : ↥E.I) : G) * x⁻¹ := by
  rw [← E.hact x hxU hxI hxH hxΩ]
  exact coe_linAct ⟨x, hxI⟩ v

theorem y0_conj_mem {T L V V₁ V₂ : Subgroup G} (hcx : Cx1291 G T L V 4)
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    {y₀ : G} (hy₀ : y₀ ∈ L ⊓ Subgroup.centralizer (V₂ : Set G)) :
    g * y₀ * g⁻¹ ∈ L ⊓ Subgroup.centralizer (V₂ : Set G) ∧
      g⁻¹ * y₀ * g ∈ L ⊓ Subgroup.centralizer (V₂ : Set G) := by
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hcx.hyp.hyp.normalizes
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    (sup_le Subgroup.le_normalizer hTN) hgP.1
  have hgV₂ : g ∈ Subgroup.normalizer (V₂ : Set G) := p128_le_normalizer_V₂ hs hgP
  have hL := Subgroup.mem_inf.1 hy₀
  have key : ∀ h : G, h ∈ Subgroup.normalizer (L : Set G) → h ∈ Subgroup.normalizer (V₂ : Set G) →
      ∀ x ∈ L ⊓ Subgroup.centralizer (V₂ : Set G), h * x * h⁻¹ ∈ L ⊓ Subgroup.centralizer (V₂ : Set G) := by
    intro h hhL hhV x hx
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hhL x).1 (Subgroup.mem_inf.1 hx).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : h⁻¹ * v * h ∈ V₂ := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hhV) v).1 hv
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 _ hw
    calc v * (h * x * h⁻¹) = h * ((h⁻¹ * v * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * v * h)) * h⁻¹ := by rw [hc]
      _ = h * x * h⁻¹ * v := by group
  refine ⟨key g hgL hgV₂ y₀ hy₀, ?_⟩
  have h := key g⁻¹ (Subgroup.inv_mem _ hgL) (Subgroup.inv_mem _ hgV₂) y₀ hy₀
  rwa [inv_inv] at h

theorem comm_mem_of_relIndex_two {H K : Subgroup G} (hHK : H ≤ K) (h2 : H.relIndex K = 2)
    {y : G} (hyK : ∀ x ∈ K, y * x * y⁻¹ ∈ K) (hyH : ∀ x ∈ H, y * x * y⁻¹ ∈ H)
    (hyH' : ∀ x ∈ H, y⁻¹ * x * y ∈ H) {j : G} (hjK : j ∈ K) (hjH : j ∉ H) :
    y * j * y⁻¹ * j⁻¹ ∈ H := by
  obtain ⟨a, haK, ha⟩ := Subgroup.relIndex_eq_two_iff.1 h2
  have hmemOut : ∀ b ∈ K, b ∉ H → b * a ∈ H := by
    intro b hb hbH
    rcases ha b hb with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact h1
    · exact absurd h2 hbH
  set j' : G := y * j * y⁻¹ with hj'
  have hj'K : j' ∈ K := hyK j hjK
  have hj'H : j' ∉ H := by
    intro h
    apply hjH
    have := hyH' j' h
    rw [hj'] at this
    simpa [mul_assoc] using this
  have h1 : j' * a ∈ H := hmemOut j' hj'K hj'H
  have h2' : j * a ∈ H := hmemOut j hjK hjH
  have h3 : j' * a * (j * a)⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem h2')
  have e : y * j * y⁻¹ * j⁻¹ = j' * a * (j * a)⁻¹ := by
    rw [hj']; group
  rw [e]
  exact h3

end Env

end CFSG.Quasithin.H13.C1294
