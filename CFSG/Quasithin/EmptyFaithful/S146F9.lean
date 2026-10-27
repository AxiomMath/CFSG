module

public import CFSG.Quasithin.EmptyFaithful.S146F8
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Prelim

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem Setting146.exists_conj_eq_mul_Z (S : Setting146 G T M) {u : G} (hu : u ∈ mcOf T)
    (h1 : (tU T u).relIndex (tZero T u) = 2) {ζ : G} (hζ : ζ ∈ quasithinOmegaOneCenter T) :
    ∃ t₀ ∈ T, t₀ * u * t₀⁻¹ = ζ * u := by
  by_cases hζ1 : ζ = 1
  · exact ⟨1, T.one_mem, by simp [hζ1]⟩
  · have hnle : ¬ tZero T u ≤ tU T u := fun hle => by
      have h11 := Subgroup.relIndex_eq_one.mpr hle
      rw [h11] at h1
      omega
    obtain ⟨t₀, ht₀, ht₀U⟩ : ∃ t₀ ∈ tZero T u, t₀ ∉ tU T u := by
      by_contra hcon
      push Not at hcon
      exact hnle fun x hx => hcon x hx
    obtain ⟨ht₀T, hc⟩ := (S146T.mem_tZero_iff hu).mp ht₀
    have hne : ⁅t₀, u⁆ ≠ 1 := by
      intro h1'
      apply ht₀U
      refine ⟨ht₀T, ?_⟩
      show t₀ ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (S146T.comm_eq_one_iff.mp h1')
    have heq : ⁅t₀, u⁆ = ζ := S.Z_eq_of_iff hc hζ ⟨fun h' => absurd h' hne, fun h' => absurd h' hζ1⟩
    refine ⟨t₀, ht₀T, ?_⟩
    rw [← heq]
    simp only [commutatorElement_def]
    group

end Prelim

@[expose] def Input14617Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → p = 3 → IsOFourPlusOn T M H →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        ∀ u u' : G, (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) → u ∉ quasithinOmegaOneCenter T →
          (u' ∈ uHi T M H H₁ ∨ u' ∈ uHi T M H H₂) → u' ∉ quasithinOmegaOneCenter T →
            ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T

@[expose] def Input14617Singular : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → p = 3 → IsOFourPlusOn T M H →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        ∀ w ∈ uK T M H, w ∉ uHi T M H H₁ → w ∉ uHi T M H H₂ →
          ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
            Nat.card T ≤ 2 * Nat.card S'

@[expose] def Input14617UK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 → IsOFourPlusOn T M H →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        (Case13One T M H p H₁ ∨ Case13One T M H p H₂) →
          ∀ u : G, (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) → u ∉ quasithinOmegaOneCenter T →
            T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u → IsInvU T M H u →
              ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
                ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥

section Fusion

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.fusion (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hTrans : ∀ u u' : G, (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) → u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H H₁ ∨ u' ∈ uHi T M H H₂) → u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T)
    (hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H H₁ → w ∉ uHi T M H H₂ →
      ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
        Nat.card T ≤ 2 * Nat.card S')
    {u : G} (hu : u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2)
    (h4 : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u)
    {y g : G} (hyK : y ∈ uK T M H) (hg : g⁻¹ * u * g = y) : ∃ c ∈ H, c⁻¹ * u * c = y := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have huG : u ∈ mcOf T := by
    rcases hu with hu | hu
    · exact S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure (h.le₁.trans h.le) hu)
    · exact S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure (h.le₂.trans h.le) hu)
  by_cases hyU : y ∈ uHi T M H H₁ ∨ y ∈ uHi T M H H₂
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

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.transitive_on_conj (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hTrans : ∀ u u' : G, (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) → u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H H₁ ∨ u' ∈ uHi T M H H₂) → u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T)
    (hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H H₁ → w ∉ uHi T M H H₂ →
      ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
        Nat.card T ≤ 2 * Nat.card S')
    {u : G} (huK : u ∈ uK T M H) (hu : u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2)
    (h4 : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u) :
    ∀ Y₁ ∈ conjugatesOf (uK T M H), ∀ Y₂ ∈ conjugatesOf (uK T M H), u ∈ Y₁ → u ∈ Y₂ →
      ∃ c ∈ Subgroup.centralizer ({u} : Set G), conjSubgroup Y₁ c = Y₂ := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
    S145.le_normalizer_commutator hHU Subgroup.le_normalizer
  refine (conjClass_inter_eq_iff_centralizer_transitive huK).mp ?_
  ext y
  constructor
  · rintro ⟨⟨g, hg⟩, hyK⟩
    obtain ⟨c, hcH, hcy⟩ := h.fusion S hred hTrans hSing hu huZ h1 h4 hyK hg
    exact ⟨c, hHN hcH, hcy⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) u).mp huK
    simpa using this

theorem IsDec12.not_centralizer_le_mcOf (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hTrans : ∀ u u' : G, (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) → u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H H₁ ∨ u' ∈ uHi T M H H₂) → u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T)
    (hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H H₁ → w ∉ uHi T M H H₂ →
      ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
        Nat.card T ≤ 2 * Nat.card S')
    {u : G} (huK : u ∈ uK T M H) (hu : u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2)
    (h4 : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u)
    (hUK : ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
      ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥) :
    ¬ Subgroup.centralizer ({u} : Set G) ≤ mcOf T := by
  intro hC
  obtain ⟨g', hug', hnc⟩ := hUK
  have hH : IsHTM T M H := hred.isHTM
  have htrans := h.transitive_on_conj S hred hTrans hSing huK hu huZ h1 h4
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

theorem IsDec12.not_centralizer_le_M (S : Setting146 G T M) (h2 : Stage1461Two) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (h : IsDec12 T M H p H₀ H₁ H₂ t) {u : G}
    (hu : u ∈ uHi T M H H₁) : ¬ Subgroup.centralizer ({u} : Set G) ≤ M := by
  intro hCM
  have hH : IsHTM T M H := hred.isHTM
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hdec3 : IsDec12 T M H 3 H₀ H₂ H₁ t⁻¹ := hp3 ▸ h.swap
  obtain ⟨z, hz2, hzQ, hzodd, -⟩ := hdec3.exists_odd_three
  have hzK : z ∈ oTwoUpper H₂ := mem_oTwoUpper_of_odd hz2 hzodd
  have hK2 : oTwoUpper H₂ ≤ Subgroup.centralizer ({u} : Set G) := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ⟨1, ?_⟩
    have hc : u * x * u⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T :=
      h.cent₁ (Subgroup.commutator_mem_commutator hu hx)
    set c := u * x * u⁻¹ * x⁻¹ with hcdef
    have hcx : x * c = c * x := S146T.comm_Z (hHG (h.le₂.trans h.le hx)) hc
    have hc2 : c * c = 1 := by
      have := S146T.Z_sq hc
      simpa [pow_two] using this
    have e1 : u * x = c * x * u := by rw [hcdef]; group
    show x ^ 2 ^ 1 ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hx2 : x ^ 2 ^ 1 = x * x := by rw [pow_one, pow_two]
    rw [hx2]
    calc w * (x * x) = (w * x) * x := by group
      _ = (c * x * w) * x := by rw [e1]
      _ = c * x * (w * x) := by group
      _ = c * x * (c * x * w) := by rw [e1]
      _ = c * (x * c) * x * w := by group
      _ = c * (c * x) * x * w := by rw [hcx]
      _ = (c * c) * (x * x) * w := by group
      _ = x * x * w := by rw [hc2]; group
  have hzM : z ∈ M := hCM (hK2 hzK)
  have hzP : z ∈ oTwoPIn p H :=
    (((oTwoUpper_mono (h.le₂.trans h.le)).trans (hred.oTwoUpper_le_pq hT2)).trans hred.le_oTwoPIn) hzK
  have hint : z ∈ oTwoPIn p H ⊓ M := ⟨hzP, hzM⟩
  rw [h2 G T M S H hH p hred.prime hred.odd] at hint
  exact hzQ hint

end Four


section Assembly

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem Setting146.inH_centralizer (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {u : G}
    (hu : u ∈ conjClosure (VZ T M) H) (hu1 : u ≠ 1) :
    InH (tU T u) (Subgroup.centralizer ({u} : Set G)) := by
  refine ⟨inf_le_right, ?_⟩
  have hsq : u ^ 2 = 1 := isElemAbelian_pow_eq_one (S.lemma_14_5_15_two hH) hu
  have hz : IsPGroup 2 (Subgroup.zpowers u) := by
    refine isPGroup_two_of_forall fun c hc => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]
  have hu1C : u ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
  have hle : Subgroup.zpowers u ≤ Subgroup.centralizer ({u} : Set G) := Subgroup.zpowers_le.mpr hu1C
  have hnorm : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    intro c hc
    have hcw : ∀ w ∈ Subgroup.zpowers u, c * w * c⁻¹ = w := by
      intro w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hcu : Commute u c := Subgroup.mem_centralizer_iff.mp hc u rfl
      have h' : Commute c (u ^ n) := (hcu.zpow_left n).symm
      rw [h'.eq]
      group
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [hcw w hw]
      exact hw
    · intro hw
      have h1 := hcw _ hw
      have h2 : c * (c * w * c⁻¹) = c * w := by
        calc c * (c * w * c⁻¹) = (c * (c * w * c⁻¹) * c⁻¹) * c := by group
          _ = (c * w * c⁻¹) * c := by rw [h1]
          _ = c * w := by group
      have e2 : c * w * c⁻¹ = w := mul_left_cancel h2
      rw [e2] at hw
      exact hw
  have hP : Subgroup.zpowers u ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 hle hnorm hz
  intro hbot
  apply hu1
  have := hP (Subgroup.mem_zpowers u)
  rw [hbot] at this
  simpa using this

end Assembly


section Four2

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.isI_of_inputs (S : Setting146 G T M) (h2 : Stage1461Two) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hTrans : ∀ u u' : G, (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) → u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H H₁ ∨ u' ∈ uHi T M H H₂) → u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T)
    (hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H H₁ → w ∉ uHi T M H H₂ →
      ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
        Nat.card T ≤ 2 * Nat.card S')
    {u : G} (huK : u ∈ uK T M H) (hu : u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (h1 : (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2)
    (h4 : IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ (g z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u)
    (hUK : ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
      ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥) :
    IsI T M u (Subgroup.centralizer ({u} : Set G)) := by
  have hH : IsHTM T M H := hred.isHTM
  have huU : u ∈ conjClosure (VZ T M) H := by
    rcases hu with hu | hu
    · exact uHi_le_conjClosure (h.le₁.trans h.le) hu
    · exact uHi_le_conjClosure (h.le₂.trans h.le) hu
  have hu1 : u ≠ 1 := fun h' => huZ (h' ▸ (quasithinOmegaOneCenter T).one_mem)
  refine ⟨S.inH_centralizer hH huU hu1, h.not_centralizer_le_mcOf S hred hTrans hSing huK hu huZ h1 h4 hUK, ?_⟩
  rcases hu with hu | hu
  · exact h.not_centralizer_le_M S h2 hred hp3 hu
  · exact h.swap.not_centralizer_le_M S h2 hred hp3 hu

theorem input14617Four_of (h2 : Stage1461Two) (h4 : Stage1463Four) (iTrans : Input14617Trans)
    (iSing : Input14617Singular) (iUK : Input14617UK) : Input14617Four := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hcase u huK hu huZ huT hInv
  have hp3 : p = 3 := hcase.elim (fun c => c.1) (fun c => c.1)
  have hOF : IsOFourPlusOn T M H := hcase.elim (fun c => c.2.1) (fun c => c.2.1)
  have hH : IsHTM T M H := hred.isHTM
  have h1 := stage1463_one_proof G T M S H hH u hInv
  have h4' := h4 G T M S H hH u hInv
  exact hdec.isI_of_inputs S h2 hred hp3
    (fun u u' hu huZ hu' hu'Z => iTrans G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec u u' hu huZ hu' hu'Z)
    (fun w hw hw1 hw2 => iSing G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec w hw hw1 hw2)
    huK hu huZ ⟨h1.1, h1.2.1⟩ ⟨h4'.2.1, h4'.2.2⟩
    (iUK G T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec hcase u hu huZ huT hInv)

end Four2


end CFSG.Quasithin
