module

public import CFSG.Quasithin.EmptyFaithful.S146F9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Fusion

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {R₁ R₂ : Subgroup G}

theorem e9_fusion (S : Setting146 G T M) (hH : IsHTM T M H) (hR₁ : R₁ ≤ H) (hR₂ : R₂ ≤ H)
    (hTrans : ∀ u u' : G, (u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂) → u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H R₁ ∨ u' ∈ uHi T M H R₂) → u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T)
    (hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H R₁ → w ∉ uHi T M H R₂ →
      ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
        Nat.card T ≤ 2 * Nat.card S')
    {u : G} (hu : u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2)
    (h4 : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u)
    {y g : G} (hyK : y ∈ uK T M H) (hg : g⁻¹ * u * g = y) : ∃ c ∈ H, c⁻¹ * u * c = y := by
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have huG : u ∈ mcOf T := by
    rcases hu with hu | hu
    · exact S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure (hR₁) hu)
    · exact S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure (hR₂) hu)
  by_cases hyU : y ∈ uHi T M H R₁ ∨ y ∈ uHi T M H R₂
  · by_cases hyZ : y ∈ quasithinOmegaOneCenter T
    · exfalso
      by_cases hy1 : y = 1
      · apply huZ
        have hu1 : u = 1 := by
          rw [hy1] at hg
          calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
            _ = 1 := by rw [hg]; group
        rw [hu1]
        exact (quasithinOmegaOneCenter T).one_mem
      · exact h4.2 g y hyZ hy1 (by rw [← hg]; group)
    · obtain ⟨c, hcH, hc⟩ := hTrans u y hu huZ hyU hyZ
      have hζ : (c * u * c⁻¹ * y⁻¹)⁻¹ ∈ quasithinOmegaOneCenter T :=
        (quasithinOmegaOneCenter T).inv_mem hc
      obtain ⟨t₁, ht₁T, ht₁⟩ := S.exists_conj_eq_mul_Z huG h1.2 hζ
      refine ⟨(c * t₁)⁻¹, H.inv_mem (H.mul_mem hcH (hTH ht₁T)), ?_⟩
      have hcz : c * (c * u * c⁻¹ * y⁻¹)⁻¹ = (c * u * c⁻¹ * y⁻¹)⁻¹ * c :=
        S146T.comm_Z (hHG hcH) hζ
      calc ((c * t₁)⁻¹)⁻¹ * u * (c * t₁)⁻¹ = c * (t₁ * u * t₁⁻¹) * c⁻¹ := by group
        _ = c * ((c * u * c⁻¹ * y⁻¹)⁻¹ * u) * c⁻¹ := by rw [ht₁]
        _ = (c * (c * u * c⁻¹ * y⁻¹)⁻¹) * u * c⁻¹ := by group
        _ = ((c * u * c⁻¹ * y⁻¹)⁻¹ * c) * u * c⁻¹ := by rw [hcz]
        _ = y := by group
  · exfalso
    obtain ⟨S', hS'le, hS'2, hS'card⟩ :=
      hSing y hyK (fun h' => hyU (Or.inl h')) (fun h' => hyU (Or.inr h'))
    have hu' : u = g * y * g⁻¹ := by rw [← hg]; group
    set X : Subgroup G := S'.map (MulAut.conj g).toMonoidHom with hX
    have hXle : X ≤ Subgroup.centralizer ({u} : Set G) := by
      rintro _ ⟨s, hs, rfl⟩
      show _ ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have hys : y * s = s * y := Subgroup.mem_centralizer_iff.mp (hS'le hs).2 y rfl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hu']
      calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
        _ = g * (s * y) * g⁻¹ := by rw [hys]
        _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
    have hX2 : IsPGroup 2 X := by
      refine isPGroup_two_of_forall fun c hc => ?_
      obtain ⟨s, hs, rfl⟩ := hc
      obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hS'2 hs
      refine ⟨k, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hk]
      group
    have hXcard : Nat.card X = Nat.card S' :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hle := card_le_twoPart hXle hX2
    have hsyl := h4.1.card_eq
    have hT4 : Nat.card T = 4 * Nat.card (tU T u) := by
      have e := Subgroup.relIndex_mul_card (H := tU T u) (K := T)
      have hle : tU T u ≤ T := inf_le_left
      rw [inf_eq_left.mpr hle, h1.1] at e
      exact e.symm
    have hpos : 0 < Nat.card (tU T u) := Nat.card_pos
    omega

end Fusion

section Four

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {R₁ R₂ : Subgroup G}

theorem e9_transitive_on_conj (S : Setting146 G T M) (hH : IsHTM T M H) (hR₁ : R₁ ≤ H)
    (hR₂ : R₂ ≤ H)
    (hTrans : ∀ u u' : G, (u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂) → u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H R₁ ∨ u' ∈ uHi T M H R₂) → u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T)
    (hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H R₁ → w ∉ uHi T M H R₂ →
      ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
        Nat.card T ≤ 2 * Nat.card S')
    {u : G} (huK : u ∈ uK T M H) (hu : u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2)
    (h4 : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u) :
    ∀ Y₁ ∈ conjugatesOf (uK T M H), ∀ Y₂ ∈ conjugatesOf (uK T M H), u ∈ Y₁ → u ∈ Y₂ →
      ∃ c ∈ Subgroup.centralizer ({u} : Set G), conjSubgroup Y₁ c = Y₂ := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
    S145.le_normalizer_commutator hHU Subgroup.le_normalizer
  refine (conjClass_inter_eq_iff_centralizer_transitive huK).mp ?_
  ext y
  constructor
  · rintro ⟨⟨g, hg⟩, hyK⟩
    obtain ⟨c, hcH, hcy⟩ := e9_fusion S hH hR₁ hR₂ hTrans hSing hu huZ h1 h4 hyK hg
    exact ⟨c, hHN hcH, hcy⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) u).mp huK
    simpa using this

theorem e9_not_centralizer_le_mcOf (S : Setting146 G T M) (hH : IsHTM T M H) (hR₁ : R₁ ≤ H)
    (hR₂ : R₂ ≤ H)
    (hTrans : ∀ u u' : G, (u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂) → u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H R₁ ∨ u' ∈ uHi T M H R₂) → u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T)
    (hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H R₁ → w ∉ uHi T M H R₂ →
      ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
        Nat.card T ≤ 2 * Nat.card S')
    {u : G} (huK : u ∈ uK T M H) (hu : u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2)
    (h4 : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u)
    (hUK : ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
      ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥) :
    ¬ Subgroup.centralizer ({u} : Set G) ≤ mcOf T := by
  intro hC
  obtain ⟨g', hug', hnc⟩ := hUK
  have htrans := e9_transitive_on_conj S hH hR₁ hR₂ hTrans hSing huK hu huZ h1 h4
  obtain ⟨c, hc, hcY⟩ := htrans (conjSubgroup (uK T M H) 1) ⟨1, rfl⟩ (conjSubgroup (uK T M H) g')
    ⟨g', rfl⟩ (by rw [conjSubgroup_one]; exact huK) hug'
  rw [conjSubgroup_one] at hcY
  have hcG : c ∈ mcOf T := hC hc
  have hUKle : uK T M H ≤ uOfL22 T M := by
    have h₁ : uK T M H ≤ conjClosure (VZ T M) H :=
      S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _)
    exact h₁.trans (conjClosure_mono le_rfl (S.le_mcOf hH))
  have hconj : conjSubgroup (uK T M H) c ≤ uOfL22 T M := by
    intro x hx
    have hx' : c * x * c⁻¹ ∈ uK T M H := mem_conjSubgroup_iff.mp hx
    have hN : c⁻¹ ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
      le_normalizer_conjClosure (VZ T M) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
        (Subgroup.inv_mem _ hcG)
    have := (Subgroup.mem_normalizer_iff.mp hN _).mp (hUKle hx')
    simpa [mul_assoc] using this
  apply hnc
  rw [← hcY]
  refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
  have hcomm := S.abelian.is_comm.comm ⟨a, hUKle ha⟩ ⟨b, hconj hb⟩
  have hab : a * b = b * a := congrArg Subtype.val hcomm
  rw [Subgroup.mem_bot, commutatorElement_def, hab]
  group

end Four

end CFSG.Quasithin
