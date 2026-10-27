module

public import CFSG.Quasithin.EmptyFaithful.S152YB
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.S152Y

open CFSG.QuasithinUnique CFSG.Quasithin

set_option maxRecDepth 100000 in
theorem card_SL3 : Fintype.card SL3 = 168 := by decide +kernel

theorem factorization_two_pow_mul (k n : ℕ) (hn : ¬ 2 ∣ n) : (2 ^ k * n).factorization 2 = k := by
  have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hn0]
  simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hn]

section Bridge

variable {G : Type} [Group G] [Finite G]

structure GVData (K V S : Subgroup G) (y : G) : Prop where
  card : Nat.card V = 4
  S_le : S ≤ K
  S_norm : ∀ s ∈ S, s ∈ Subgroup.normalizer (V : Set G)
  y_mem : y ∈ K
  y_norm : y ∈ Subgroup.normalizer (V : Set G)
  y_fpf : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1

structure GCoord (K X : Subgroup G) (α : ↥K →* SL3) (β : ↥X →* Multiplicative Vec3) : Prop where
  normalizes : K ≤ Subgroup.normalizer (X : Set G)
  equiv : ∀ (a : ↥K) (u v : ↥X), (v : G) = a * u * a⁻¹ →
    Multiplicative.toAdd (β v) = mulV (α a) (Multiplicative.toAdd (β u))

@[expose] def conjAct (K X : Subgroup G) (h : K ≤ Subgroup.normalizer (X : Set G)) : ↥K →* MulAut ↥X :=
  X.normalizerMonoidHom.comp (Subgroup.inclusion h)

omit [Finite G] in
theorem conjAct_coe (K X : Subgroup G) (h : K ≤ Subgroup.normalizer (X : Set G)) (k : ↥K) (x : ↥X) :
    ((conjAct K X h k x : ↥X) : G) = k * x * (k : G)⁻¹ := rfl

omit [Finite G] in
theorem GCoord.natCoord {K X : Subgroup G} {α : ↥K →* SL3} {β : ↥X →* Multiplicative Vec3}
    (h : GCoord K X α β) : NatCoord (conjAct K X h.normalizes) α β :=
  fun k x => h.equiv k x _ (conjAct_coe K X h.normalizes k x)

omit [Finite G] in
theorem closure_orbit_eq {K X V : Subgroup G} (h : K ≤ Subgroup.normalizer (X : Set G)) (hVX : V ≤ X) :
    Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x} =
      (Subgroup.closure (orbitSet (conjAct K X h) (V.subgroupOf X))).map X.subtype := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, z, hz, rfl⟩
    refine ⟨conjAct K X h ⟨k, hk⟩ ⟨z, hVX hz⟩, ⟨⟨k, hk⟩, ⟨z, hVX hz⟩, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, v, hv, rfl⟩, rfl⟩
    exact ⟨k, k.2, v, hv, rfl⟩

omit [Finite G] in
theorem card_closure_orbit_eq {K X V : Subgroup G} (h : K ≤ Subgroup.normalizer (X : Set G)) (hVX : V ≤ X) :
    Nat.card (Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x}) =
      Nat.card (Subgroup.closure (orbitSet (conjAct K X h) (V.subgroupOf X))) := by
  rw [closure_orbit_eq h hVX]
  exact Subgroup.card_map_of_injective X.subtype_injective

omit [Finite G] in
theorem GVData.vdata {K X V S : Subgroup G} {y : G} (hV : GVData K V S y)
    (h : K ≤ Subgroup.normalizer (X : Set G)) (hVX : V ≤ X) :
    VData (conjAct K X h) (V.subgroupOf X) (S.subgroupOf K) ⟨y, hV.y_mem⟩ where
  card := by
    rw [← hV.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv
  S_le := by
    intro s hs x
    have hsK : (s : G) ∈ S := hs
    show ((conjAct K X h s x : ↥X) : G) ∈ V ↔ (x : G) ∈ V
    rw [conjAct_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hV.S_norm _ hsK) x).symm
  y_mem := by
    intro x
    show ((conjAct K X h ⟨y, hV.y_mem⟩ x : ↥X) : G) ∈ V ↔ (x : G) ∈ V
    rw [conjAct_coe]
    exact (Subgroup.mem_normalizer_iff.mp hV.y_norm x).symm
  y_fpf := by
    intro v hv hfix
    have hvV : (v : G) ∈ V := hv
    have : (y : G) * v * (y : G)⁻¹ = v := congrArg Subtype.val hfix
    exact Subtype.ext (hV.y_fpf _ hvV this)

theorem card_map_sylow {K S : Subgroup G} (hS : IsSylowTwoOf S K) {α : ↥K →* SL3}
    (hα : Function.Surjective α) : Nat.card ((S.subgroupOf K).map α) = 8 := by
  have hP := Sylow.mapSurjective hα (A4.toSylow hS)
  have h1 : ((Sylow.mapSurjective hα (A4.toSylow hS) : Sylow 2 SL3) : Subgroup SL3) =
      (S.subgroupOf K).map α := rfl
  rw [← h1, Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, card_SL3]
  have : (168 : ℕ) = 2 ^ 3 * 21 := by norm_num
  rw [this]
  have h21 : ¬ 2 ∣ 21 := by norm_num
  rw [factorization_two_pow_mul 3 21 h21]
  norm_num

theorem g_afl2 {K W V S : Subgroup G} {y : G} {α : ↥K →* SL3} {β₀ β₁ : ↥W →* Multiplicative Vec3}
    (hWsq : ∀ a ∈ W, a * a = 1) (h₀ : GCoord K W α β₀) (h₁ : GCoord K W α β₁)
    (hjoint : ∀ x, β₀ x = 1 → β₁ x = 1 → x = 1) (hV : GVData K V S y) (hVW : V ≤ W)
    (hS8 : Nat.card ((S.subgroupOf K).map α) = 8) :
    Nat.card (Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x}) ≤ 8 := by
  classical
  have : Fintype ↥W := Fintype.ofFinite _
  rw [card_closure_orbit_eq h₀.normalizes hVW]
  have h₁' : NatCoord (conjAct K W h₀.normalizes) α β₁ := by
    intro k x
    exact h₁.equiv k x _ (conjAct_coe K W h₀.normalizes k x)
  exact afl2 h₀.natCoord h₁' hjoint (fun x => Subtype.ext (hWsq x x.2))
    (hV.vdata h₀.normalizes hVW) hS8

theorem g_afl1 {K W V S : Subgroup G} {y : G} {α : ↥K →* SL3} {β : ↥W →* Multiplicative Vec3}
    (hWsq : ∀ a ∈ W, a * a = 1) (h : GCoord K W α β) (hα : Function.Surjective α)
    (hker : ∀ a b c : ↥W, β a = 1 → β b = 1 → β c = 1 → a = b ∨ a = c ∨ b = c)
    (hkerfix : ∀ (k : ↥K) (x : ↥W), β x = 1 → (k : G) * x * (k : G)⁻¹ = x)
    (htriv : ∀ k : ↥K, α k = 1 → ∀ x ∈ W, (k : G) * x * (k : G)⁻¹ = x)
    (hV : GVData K V S y) (hVW : V ≤ W) (hS8 : Nat.card ((S.subgroupOf K).map α) = 8) :
    Nat.card (Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x}) ≤ 8 := by
  classical
  have : Fintype ↥W := Fintype.ofFinite _
  rw [card_closure_orbit_eq h.normalizes hVW]
  exact afl1 h.natCoord hα (fun x => Subtype.ext (hWsq x x.2)) hker
    (fun k x hx => Subtype.ext (hkerfix k x hx))
    (fun k hk => MulEquiv.ext fun x => Subtype.ext (htriv k hk x x.2))
    (hV.vdata h.normalizes hVW) hS8

end Bridge

end CFSG.Quasithin.S152Y
