module

public import CFSG.Quasithin.EmptyFaithful.SzF53MZa
public import CFSG.Quasithin.Background.B2FactorizationR2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

structure Dict5 (X S Z : Subgroup G) where
  ψ : ↥X →* Perm (Fin 5)
  φ : orth.W →* G
  surj : Function.Surjective ψ
  ker_iff : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 X
  map_S : (S.subgroupOf X).map ψ = S5Syl
  inj : Function.Injective φ
  range_eq : φ.range = Z
  act_eq : ∀ (x : ↥X) (u : orth.W), φ (orth.act (ψ x) u) = (x : G) * φ u * (x : G)⁻¹
  S_le : S ≤ X
  Q_le : pCoreOf 2 X ≤ S

theorem nonempty_dict5 [Finite G] {X S Z : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) (hS : IsSylowTwoOf S X)
    (hZ : IsOrthSec X ⊥ Z) : Nonempty (Dict5 X S Z) := by
  have hQ : cSecIn X ⊥ Z = pCoreOf 2 X := IsModelSec.cSecIn_eq_pCoreOf hZ hq
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := hZ
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ := hsd.exists_normalized hθs hθk hS
  let ℓ : ↥Z ⧸ (⊥ : Subgroup G).subgroupOf Z →* G :=
    QuotientGroup.lift ((⊥ : Subgroup G).subgroupOf Z) Z.subtype (by
      intro z hz
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hz
      exact hz)
  have hℓ : ∀ z : ↥Z, ℓ (QuotientGroup.mk z) = (z : G) := fun z => rfl
  have hℓinj : Function.Injective ℓ := by
    intro a b hab
    obtain ⟨z₁, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨z₂, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hℓ, hℓ] at hab
    rw [Subtype.ext hab]
  refine ⟨⟨Ψ, ℓ.comp β', hΨs, fun x => ?_, hPS, fun a b h => hsd'.inj (hℓinj h), ?_, ?_,
    hS.1, pCoreOf_le_of_isSylowTwoOf hS⟩⟩
  · rw [← MonoidHom.mem_ker, hkΨ, hQ, Subgroup.mem_subgroupOf]
  · ext g
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (β' w)
      show ℓ (β' w) ∈ Z
      rw [← hz, hℓ]
      exact z.2
    · intro hg
      obtain ⟨w, hw⟩ := hsd'.surj (QuotientGroup.mk (⟨g, hg⟩ : ↥Z))
      exact ⟨w, by show ℓ (β' w) = g; rw [hw, hℓ]⟩
  · intro x u
    obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (β' u)
    obtain ⟨hkx, h1⟩ := hsd'.equiv x u z hz.symm
    show ℓ (β' (orth.act (Ψ x) u)) = _
    rw [h1, hℓ]
    show (x : G) * (z : G) * (x : G)⁻¹ = (x : G) * ℓ (β' u) * (x : G)⁻¹
    rw [← hz, hℓ]

theorem act_inv_mem (V : Subgroup orth.W) (σ : Perm (Fin 5)) (h : ∀ y ∈ V, orth.act σ y ∈ V) :
    ∀ y ∈ V, orth.act σ⁻¹ y ∈ V := by
  have hle : V.map (orth.act σ).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (orth.act σ).injective])
  intro y hy
  rw [← heq] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  rw [show (orth.act σ).toMonoidHom v = orth.act σ v from rfl, act_inv_act]
  exact hv

namespace Dict5

variable {X S Z : Subgroup G} (D : Dict5 X S Z)

@[expose] def bar (K : Subgroup G) : Subgroup (Perm (Fin 5)) := (K.subgroupOf X).map D.ψ

theorem mem_bar_iff {K : Subgroup G} (σ : Perm (Fin 5)) :
    σ ∈ D.bar K ↔ ∃ x : ↥X, (x : G) ∈ K ∧ D.ψ x = σ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem bar_S : D.bar S = S5Syl := D.map_S

theorem ker_eq : D.ψ.ker = (pCoreOf 2 X).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, D.ker_iff, Subgroup.mem_subgroupOf]

theorem φ_mem (u : orth.W) : D.φ u ∈ Z := D.range_eq.le ⟨u, rfl⟩

theorem map_φ_top : (⊤ : Subgroup orth.W).map D.φ = Z := by
  rw [← MonoidHom.range_eq_map]
  exact D.range_eq

theorem card_map_φ (V : Subgroup orth.W) : Nat.card (V.map D.φ) = Nat.card V :=
  Subgroup.card_map_of_injective D.inj

theorem map_φ_le (V : Subgroup orth.W) : V.map D.φ ≤ Z := by
  exact (Subgroup.map_mono le_top).trans D.map_φ_top.le

theorem map_comap_φ {U : Subgroup G} (hU : U ≤ Z) : (U.comap D.φ).map D.φ = U := by
  rw [Subgroup.map_comap_eq, D.range_eq]
  exact inf_eq_right.mpr hU

theorem mem_iff_of_Q_le {K : Subgroup G} (hQK : pCoreOf 2 X ≤ K) (x : ↥X) :
    (x : G) ∈ K ↔ D.ψ x ∈ D.bar K := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h1 : ((y⁻¹ * x : ↥X) : G) ∈ pCoreOf 2 X :=
      (D.ker_iff _).mp (by rw [map_mul, map_inv, hyx, inv_mul_cancel])
    have h2 : (x : G) = (y : G) * ((y⁻¹ * x : ↥X) : G) := by
      simp
    rw [h2]
    exact K.mul_mem (Subgroup.mem_subgroupOf.mp hy) (hQK h1)

theorem mem_S_iff (x : ↥X) : (x : G) ∈ S ↔ D.ψ x ∈ S5Syl := by
  rw [← D.bar_S]
  exact D.mem_iff_of_Q_le D.Q_le x

theorem bar_eq_of_iff {K : Subgroup G} {P : Subgroup (Perm (Fin 5))}
    (h : ∀ x : ↥X, (x : G) ∈ K ↔ D.ψ x ∈ P) : D.bar K = P := by
  ext σ
  rw [D.mem_bar_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mp hx
  · intro hσ
    obtain ⟨x, rfl⟩ := D.surj σ
    exact ⟨x, (h x).mpr hσ, rfl⟩

theorem card_bar {K : Subgroup G} (hK : K ≤ X) :
    Nat.card (D.bar K) = (pCoreOf 2 X ⊓ K).relIndex K := by
  unfold bar
  rw [← Subgroup.relIndex_ker, D.ker_eq, Subgroup.relIndex_subgroupOf hK,
    Subgroup.inf_relIndex_right]

theorem ψ_mem_S5Syl {s : G} (hs : s ∈ S) : D.ψ ⟨s, D.S_le hs⟩ ∈ S5Syl :=
  (D.mem_S_iff ⟨s, D.S_le hs⟩).mp hs

theorem mem_fixW_bar_iff {K : Subgroup G} (hK : K ≤ X) (w : orth.W) :
    w ∈ fixW orth (D.bar K) ↔ ∀ k ∈ K, k * D.φ w = D.φ w * k := by
  constructor
  · intro h k hk
    have h1 := h (D.ψ ⟨k, hK hk⟩) ⟨⟨k, hK hk⟩, hk, rfl⟩
    have h2 := congrArg D.φ h1
    rw [D.act_eq] at h2
    calc k * D.φ w = (k * D.φ w * k⁻¹) * k := by group
      _ = D.φ w * k := by rw [h2]
  · rintro h _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ K := hy
    apply D.inj
    rw [D.act_eq y w]
    calc (y : G) * D.φ w * (y : G)⁻¹ = (D.φ w * (y : G)) * (y : G)⁻¹ := by rw [h _ hy']
      _ = D.φ w := by group

theorem map_fixW {K : Subgroup G} (hK : K ≤ X) :
    (fixW orth (D.bar K)).map D.φ = Z ⊓ Subgroup.centralizer (K : Set G) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨D.φ_mem w, Subgroup.mem_centralizer_iff.mpr fun k hk =>
      (D.mem_fixW_bar_iff hK w).mp hw k hk⟩
  · rintro ⟨hz, hc⟩
    have hz' : g ∈ D.φ.range := D.range_eq.ge hz
    obtain ⟨w, rfl⟩ := hz'
    exact ⟨w, (D.mem_fixW_bar_iff hK w).mpr fun k hk =>
      (Subgroup.mem_centralizer_iff.mp hc k hk), rfl⟩

theorem map_commW {K : Subgroup G} (hK : K ≤ X) (U : Subgroup orth.W) :
    (commW orth (D.bar K) U).map D.φ = ⁅U.map D.φ, K⁆ := by
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr ?_
    unfold commW
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨b, ⟨y, hy, rfl⟩, u, hu, rfl⟩
    have hy' : (y : G) ∈ K := hy
    have h1 := Subgroup.commutator_mem_commutator hy' (Subgroup.mem_map_of_mem D.φ hu)
    rw [Subgroup.commutator_comm] at h1
    show D.φ (orth.act (D.ψ y) u * u⁻¹) ∈ ⁅U.map D.φ, K⁆
    rw [map_mul, map_inv, D.act_eq y u]
    rw [commutatorElement_def] at h1
    exact h1
  · rw [Subgroup.commutator_le]
    rintro _ ⟨u, hu, rfl⟩ k hk
    have hkX : k ∈ X := hK hk
    let b := D.ψ ⟨k, hkX⟩
    have hb : b ∈ D.bar K := ⟨⟨k, hkX⟩, hk, rfl⟩
    have hc : orth.act b u * u⁻¹ ∈ commW orth (D.bar K) U :=
      Subgroup.subset_closure ⟨b, hb, u, hu, rfl⟩
    refine Subgroup.mem_map.mpr ⟨_, Subgroup.inv_mem _ hc, ?_⟩
    rw [map_inv, map_mul, map_inv, D.act_eq ⟨k, hkX⟩ u, commutatorElement_def]
    group

theorem map_commW_top {K : Subgroup G} (hK : K ≤ X) :
    (commW orth (D.bar K) ⊤).map D.φ = ⁅Z, K⁆ := by
  rw [D.map_commW hK, D.map_φ_top]

include D in
theorem commutator_le {K : Subgroup G} (hK : K ≤ X) : ⁅Z, K⁆ ≤ Z := by
  rw [← D.map_commW_top hK]
  exact D.map_φ_le _

theorem invariant_iff {K : Subgroup G} (hK : K ≤ X) {U : Subgroup G} (hU : U ≤ Z) :
    (∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) ↔ IsInvSub orth (D.bar K) (U.comap D.φ) := by
  constructor
  · rintro h _ ⟨y, hy, rfl⟩ u hu
    show D.φ (orth.act (D.ψ y) u) ∈ U
    rw [D.act_eq]
    exact h y hy _ hu
  · intro h k hk u hu
    have hu' : u ∈ D.φ.range := D.range_eq.ge (hU hu)
    obtain ⟨w, rfl⟩ := hu'
    have hkX : k ∈ X := hK hk
    have := h (D.ψ ⟨k, hkX⟩) ⟨⟨k, hkX⟩, hk, rfl⟩ w hu
    have h2 := (Subgroup.mem_comap.mp this)
    rwa [D.act_eq] at h2

theorem mem_centralizer_map_iff (V : Subgroup orth.W) (x : ↥X) :
    (x : G) ∈ Subgroup.centralizer (V.map D.φ : Set G) ↔ ∀ w ∈ V, orth.act (D.ψ x) w = w := by
  constructor
  · intro h w hw
    apply D.inj
    rw [D.act_eq]
    have := Subgroup.mem_centralizer_iff.mp h (D.φ w) (Subgroup.mem_map_of_mem D.φ hw)
    calc (x : G) * D.φ w * (x : G)⁻¹ = (D.φ w * (x : G)) * (x : G)⁻¹ := by rw [this]
      _ = D.φ w := by group
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    have h1 := congrArg D.φ (h w hw)
    rw [D.act_eq] at h1
    calc D.φ w * (x : G) = ((x : G) * D.φ w * (x : G)⁻¹) * x := by rw [h1]
      _ = (x : G) * D.φ w := by group

theorem mem_normalizer_map_iff (V : Subgroup orth.W) (x : ↥X) :
    (x : G) ∈ Subgroup.normalizer (V.map D.φ : Set G) ↔ ∀ w ∈ V, orth.act (D.ψ x) w ∈ V := by
  constructor
  · intro h w hw
    have h1 := (Subgroup.mem_normalizer_iff.mp h (D.φ w)).mp (Subgroup.mem_map_of_mem D.φ hw)
    rw [← D.act_eq] at h1
    obtain ⟨w', hw', hw'e⟩ := h1
    rwa [← D.inj hw'e]
  · intro h
    have hinv := act_inv_mem V _ h
    have key : ∀ (y : ↥X), (∀ w ∈ V, orth.act (D.ψ y) w ∈ V) →
        ∀ g ∈ V.map D.φ, (y : G) * g * (y : G)⁻¹ ∈ V.map D.φ := by
      rintro y hy _ ⟨w, hw, rfl⟩
      rw [← D.act_eq]
      exact ⟨_, hy w hw, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨key x h g, fun hg => ?_⟩
    have h2 := key x⁻¹ (by rw [map_inv]; exact hinv) _ hg
    simpa [mul_assoc] using h2

theorem relIndex_centralizer_eq (s : ↥X) :
    (Z ⊓ Subgroup.centralizer ({(s : G)} : Set G)).relIndex Z = idx orth (D.ψ s) := by
  have h1 : (fixW orth (Subgroup.zpowers (D.ψ s))).map D.φ =
      Z ⊓ Subgroup.centralizer ({(s : G)} : Set G) := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h := congrArg D.φ ((mem_fixW_zpowers orth).mp hw)
      rw [D.act_eq] at h
      refine ⟨D.φ_mem w, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      rw [Set.mem_singleton_iff] at hk
      subst hk
      calc (s : G) * D.φ w = ((s : G) * D.φ w * (s : G)⁻¹) * s := by group
        _ = D.φ w * s := by rw [h]
    · rintro ⟨hz, hc⟩
      have hz' : g ∈ D.φ.range := D.range_eq.ge hz
      obtain ⟨w, rfl⟩ := hz'
      refine ⟨w, (mem_fixW_zpowers orth).mpr ?_, rfl⟩
      apply D.inj
      rw [D.act_eq]
      have := Subgroup.mem_centralizer_iff.mp hc s rfl
      calc (s : G) * D.φ w * (s : G)⁻¹ = (D.φ w * s) * (s : G)⁻¹ := by rw [this]
        _ = D.φ w := by group
  unfold idx
  have e := Subgroup.relIndex_map_map_of_injective
    (fixW orth (Subgroup.zpowers (D.ψ s))) ⊤ D.inj
  rw [D.map_φ_top, Subgroup.relIndex_top_right] at e
  rw [← h1, e]

end Dict5

end CFSG.Quasithin.F53.Stellmacher.S43
