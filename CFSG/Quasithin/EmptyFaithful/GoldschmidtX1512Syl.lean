module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace X1512

theorem sylow_top_iff {X : Type*} [Group X] {Q : Subgroup X} :
    IsSylowTwoOf Q ⊤ ↔ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index := by
  unfold IsSylowTwoOf
  rw [show (Q.subgroupOf ⊤).index = Q.index from Subgroup.relIndex_top_right Q]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨le_top, h.1, h.2⟩⟩

theorem sylow_subgroupOf_top {G : Type*} [Group G] {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf (T.subgroupOf H) (⊤ : Subgroup ↥H) := by
  rw [sylow_top_iff]
  refine ⟨?_, ?_⟩
  · have e : ↥(T.subgroupOf H) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hT.1
    exact hT.2.1.of_injective e.toMonoidHom e.injective
  · have e : (T.subgroupOf H).index = T.relIndex H := rfl
    rw [e]
    exact hT.2.2

theorem sylow_subgroupOf_of_le {G : Type*} [Group G] {K H S : Subgroup G} (hS : IsSylowTwoOf S H)
    (hHK : H ≤ K) : IsSylowTwoOf (S.subgroupOf K) (H.subgroupOf K) := by
  refine ⟨fun x hx => hS.1 hx, ?_, ?_⟩
  · have e : ↥(S.subgroupOf K) ≃* ↥S := Subgroup.subgroupOfEquivOfLe (hS.1.trans hHK)
    exact hS.2.1.of_injective e.toMonoidHom e.injective
  · have h := hS.2.2
    show ¬ 2 ∣ (S.subgroupOf K).relIndex (H.subgroupOf K)
    rw [Subgroup.relIndex_subgroupOf hHK]
    exact h

theorem sylow_map_top {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map f) ⊤ := by
  obtain ⟨hp, hi⟩ := sylow_top_iff.mp hS
  rw [sylow_top_iff]
  exact ⟨hp.map f, fun hd => hi (hd.trans (Subgroup.index_map_dvd S hf))⟩

theorem sylow_map_of_map_eq_top {X Y : Type*} [Group X] [Group Y] {φ : X →* Y}
    {H₁ T : Subgroup X} (hH : H₁.map φ = ⊤) (hT : IsSylowTwoOf T H₁) :
    IsSylowTwoOf (T.map φ) ⊤ := by
  have hsurj : Function.Surjective (φ.comp H₁.subtype) := by
    intro y
    have : y ∈ H₁.map φ := by rw [hH]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have h := sylow_map_top (φ.comp H₁.subtype) hsurj (sylow_subgroupOf_top hT)
  have e2 : (T.subgroupOf H₁).map (φ.comp H₁.subtype) = T.map φ := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hT.1]
  rwa [e2] at h

theorem card_sylow_perm {n : ℕ} (hn : n = 3 ∨ n = 5) {D : Subgroup (Equiv.Perm (Fin n))}
    (hD : IsSylowTwoOf D ⊤) : Nat.card D = if n = 3 then 2 else 8 := by
  obtain ⟨hp, hi⟩ := sylow_top_iff.mp hD
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h1 := Subgroup.card_mul_index D
  rw [hk, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  rcases hn with rfl | rfl
  · have h6 : 2 ^ k * D.index = 6 := by simpa [Nat.factorial] using h1
    have hk2 : k < 2 := by
      by_contra h
      have : 4 ∣ 2 ^ k := by
        have := pow_dvd_pow 2 (not_lt.mp h)
        simpa using this
      have : 4 ∣ 6 := h6 ▸ Dvd.dvd.mul_right this _
      omega
    interval_cases k <;> simp at h6 hk ⊢ <;> omega
  · have h120 : 2 ^ k * D.index = 120 := by simpa [Nat.factorial] using h1
    have hk4 : k < 4 := by
      by_contra h
      have : 16 ∣ 2 ^ k := by
        have := pow_dvd_pow 2 (not_lt.mp h)
        simpa using this
      have : 16 ∣ 120 := h120 ▸ Dvd.dvd.mul_right this _
      omega
    interval_cases k <;> simp at h120 hk ⊢ <;> omega

theorem isElemAbelian_map_subgroupOf {G Y : Type*} [Group G] [Group Y] {K A : Subgroup G}
    (f : ↥K →* Y) (hA : IsElemAbelian 2 A) : IsElemAbelian 2 ((A.subgroupOf K).map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    refine Subtype.ext ?_
    show (a : Y) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm hA (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy))
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hA.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]

end X1512

end CFSG.Quasithin
