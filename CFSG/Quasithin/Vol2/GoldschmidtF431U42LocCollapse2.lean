module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocCollapse

public section

namespace CFSG.Quasithin.H13.F431.U42

theorem collapse' {G : Type} [Group G] [Finite G] (H N X Q : Subgroup G) (hNH : N ≤ H)
    (hNc : ∀ n ∈ N, ∀ h ∈ H, n * h = h * n) (hN2 : Nat.card N = 2) (hNX : N ≤ X) (hNQ : N ≤ Q)
    (hQH : Q ≤ H) (hQp : IsPGroup 2 Q)
    (hQm : ∀ Q' : Subgroup G, Q' ≤ H → IsPGroup 2 Q' → Q ≤ Q' → Q' = Q)
    (u a b : G) (huH : u ∈ H) (haH : a ∈ H) (hbH : b ∈ H) (hu : u * u = 1) (huN : u ∉ N)
    (huQ : u ∈ Q) (huc : ∀ q ∈ Q, q * u * q⁻¹ * u⁻¹ ∈ N)
    (hU1 : ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ N → h ∈ X)
    (hU3 : ∀ h ∈ H, h * u * h⁻¹ ∈ Q → h * u * h⁻¹ * u⁻¹ ∈ N)
    (ha : a * a = 1) (hb : b * b = 1)
    (hUa : ∀ h ∈ H, h * a * h⁻¹ * a⁻¹ ∈ N → h ∈ X)
    (hUb : ∀ h ∈ H, h * b * h⁻¹ * b⁻¹ ∈ N → h ∈ X)
    (hUab : ∀ h ∈ H, h * (a * b) * h⁻¹ * (a * b)⁻¹ ∈ N → h ∈ X)
    (hX1 : ∀ K : Subgroup G, K ≤ X ⊓ H → (∀ e ∈ X ⊓ H, ∀ k ∈ K, e * k * e⁻¹ ∈ K) → N ≤ K →
      ¬ 4 ∣ Nat.card K → K = N) :
    ∀ h ∈ H, h ∈ X := by
  have hN2' : Nat.card (N.subgroupOf H) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hN2
  have hQp' : IsPGroup 2 (Q.subgroupOf H) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hQm' : ∀ Q' : Subgroup H, IsPGroup 2 Q' → Q.subgroupOf H ≤ Q' → Q' = Q.subgroupOf H := by
    intro Q' hQ'p hQQ'
    have h1 : IsPGroup 2 (Q'.map H.subtype) := hQ'p.map _
    have h2 : Q ≤ Q'.map H.subtype := fun q hq => ⟨⟨q, hQH hq⟩, hQQ' hq, rfl⟩
    have h3 := hQm (Q'.map H.subtype) (Subgroup.map_subtype_le Q') h1 h2
    ext x
    constructor
    · intro hx
      have hx' : (x : G) ∈ Q'.map H.subtype := ⟨x, hx, rfl⟩
      rw [h3] at hx'
      exact hx'
    · exact fun hx => hQQ' hx
  have hX1' : ∀ K : Subgroup H, K ≤ X.subgroupOf H →
      (∀ e ∈ X.subgroupOf H, ∀ k ∈ K, e * k * e⁻¹ ∈ K) → N.subgroupOf H ≤ K →
      ¬ 4 ∣ Nat.card K → K = N.subgroupOf H := by
    intro K hKX hKn hNK h4
    have hK0 : K.map H.subtype = N := by
      refine hX1 (K.map H.subtype) ?_ ?_ ?_ ?_
      · rintro _ ⟨k, hk, rfl⟩
        exact ⟨hKX hk, k.2⟩
      · rintro e ⟨heX, heH⟩ _ ⟨k, hk, rfl⟩
        exact ⟨_, hKn ⟨e, heH⟩ heX k hk, rfl⟩
      · intro n hn
        exact ⟨⟨n, hNH hn⟩, hNK hn, rfl⟩
      · rwa [Subgroup.card_map_of_injective H.subtype_injective]
    calc K = (K.map H.subtype).comap H.subtype :=
          (Subgroup.comap_map_eq_self_of_injective H.subtype_injective K).symm
      _ = N.subgroupOf H := by rw [hK0]; rfl
  have key := collapse (N.subgroupOf H) (X.subgroupOf H) (Q.subgroupOf H)
    (fun n hn => Subgroup.mem_center_iff.2 fun g => Subtype.ext (hNc n hn g g.2).symm) hN2'
    (fun n hn => hNX hn) (fun n hn => hNQ hn) hQp' hQm' ⟨u, huH⟩ ⟨a, haH⟩ ⟨b, hbH⟩
    (Subtype.ext hu) huN huQ (fun q hq => huc q hq) (fun h => hU1 h h.2) (fun h => hU3 h h.2)
    (Subtype.ext ha) (Subtype.ext hb) (fun h => hUa h h.2) (fun h => hUb h h.2)
    (fun h => hUab h h.2) hX1'
  exact fun h hh => key ⟨h, hh⟩

end CFSG.Quasithin.H13.F431.U42
