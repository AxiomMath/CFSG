module

public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Sporadic.Co1.Module.PairsCheck

public section

namespace CFSG.Sporadic.Co1.Module.Pairs

open CFSG.Blueprint MulAction

section Generic

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def stabEquiv (K : Subgroup G) (w : X) :
    ↥(K ⊓ MulAction.stabilizer G w) ≃ ↥(MulAction.stabilizer (↥K) w) where
  toFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  invFun g := ⟨g.1.1, g.1.2, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ncard_orbit_mul_card_inf_stabilizer (K : Subgroup G) (w : X) :
    (MulAction.orbit K w).ncard * Nat.card ↥(K ⊓ MulAction.stabilizer G w) = Nat.card ↥K := by
  have h := Subgroup.index_mul_card (MulAction.stabilizer (↥K) w)
  rw [MulAction.index_stabilizer] at h
  rw [Nat.card_congr (stabEquiv K w)]
  exact h

theorem orbit_eq_of_forall {K : Subgroup G} {w : X} {T : Set X} (hw : w ∈ T)
    (htrans : ∀ t ∈ T, ∃ g ∈ K, g • w = t) (hinv : ∀ g ∈ K, ∀ t ∈ T, g • t ∈ T) :
    MulAction.orbit K w = T := by
  ext t
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact hinv g hg w hw
  · intro ht
    obtain ⟨g, hg, rfl⟩ := htrans t ht
    exact ⟨⟨g, hg⟩, rfl⟩

theorem ncard_mul_card_inf_stabilizer {K : Subgroup G} {w : X} {T : Set X} (hw : w ∈ T)
    (htrans : ∀ t ∈ T, ∃ g ∈ K, g • w = t) (hinv : ∀ g ∈ K, ∀ t ∈ T, g • t ∈ T) :
    T.ncard * Nat.card ↥(K ⊓ MulAction.stabilizer G w) = Nat.card ↥K := by
  rw [← orbit_eq_of_forall hw htrans hinv]
  exact ncard_orbit_mul_card_inf_stabilizer K w

theorem card_inf_stabilizer_smul₂ (g : G) (x y : X) :
    Nat.card ↥(MulAction.stabilizer G (g • x) ⊓ MulAction.stabilizer G (g • y)) =
      Nat.card ↥(MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_inf_stabilizer_smul₃ (g : G) (x w y : X) :
    Nat.card ↥(MulAction.stabilizer G (g • x) ⊓ MulAction.stabilizer G (g • w) ⊓
        MulAction.stabilizer G (g • y)) =
      Nat.card ↥(MulAction.stabilizer G x ⊓ MulAction.stabilizer G w ⊓
        MulAction.stabilizer G y) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end Generic

theorem card_stabilizer_v₂ :
    Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 v₂) = 42305421312000 := by
  have h := Subgroup.index_mul_card (MulAction.stabilizer NativeSporadic.Co1 v₂)
  rw [MulAction.index_stabilizer] at h
  have h1 : (MulAction.orbit NativeSporadic.Co1 v₂).ncard = 98280 := co1_orbit_ncard_v₂
  rw [h1, CFSG.Sporadic.Co1.card_Co1] at h
  omega

theorem tyOrbC_smul_mem (g : NativeSporadic.Co1) {j : ℕ} {z : Vec24} (hz : z ∈ tyOrbC j) :
    g • z ∈ tyOrbC j := by
  match j with
  | 0 =>
    rw [tyOrbC, Set.mem_singleton_iff] at hz ⊢
    rw [hz]; exact smul_zero g
  | 1 => exact orbit_smul_mem g hz
  | 2 => exact orbit_smul_mem g hz
  | j + 3 => exact orbit_smul_mem g hz

theorem cls_smul_mem {j : ℕ} {g : NativeSporadic.Co1} (hg : g • v₂ = v₂) {y : Vec24}
    (hy : y ∈ cls j) : g • y ∈ cls j := by
  refine ⟨orbit_smul_mem g hy.1, ?_⟩
  have : v₂ + g • y = g • (v₂ + y) := by rw [smul_add, hg]
  rw [this]
  exact tyOrbC_smul_mem g hy.2

theorem cls_card_stab
    {j : ℕ} (hj : j < 4) {y : Vec24} (hy : y ∈ cls j) :
    (cls j).ncard * Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 v₂ ⊓
      MulAction.stabilizer NativeSporadic.Co1 y) = 42305421312000 := by
  rw [← card_stabilizer_v₂]
  refine ncard_mul_card_inf_stabilizer (K := MulAction.stabilizer NativeSporadic.Co1 v₂) hy
    (fun t ht => ?_) (fun g hg t ht => cls_smul_mem hg ht)
  obtain ⟨g, hg1, hg2⟩ := cls_trans hj hy ht
  exact ⟨g, hg1, hg2⟩

theorem pair_one
    (x : Vec24) (hx : x ∈ MulAction.orbit NativeSporadic.Co1 v₂) :
    ∃ y ∈ MulAction.orbit NativeSporadic.Co1 v₂, x + y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      3 ^ 6 * 11 ∣ Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 x ⊓
        MulAction.stabilizer NativeSporadic.Co1 y) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨y₀, hy₀⟩ : (cls 3).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [cls_ncard (by norm_num)]; decide)
  refine ⟨g • y₀, orbit_smul_mem g hy₀.1, ?_, ?_⟩
  · rw [← smul_add]
    exact orbit_smul_mem g hy₀.2
  · rw [card_inf_stabilizer_smul₂]
    have h := cls_card_stab (j := 3) (by norm_num) hy₀
    rw [cls_ncard (by norm_num)] at h
    have h3 : dat.subSizes[3]! = 4600 := by decide
    rw [h3] at h
    have hc : Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 v₂ ⊓
        MulAction.stabilizer NativeSporadic.Co1 y₀) = 9196830720 := by omega
    rw [hc]; norm_num

theorem pair_two
    (x : Vec24) (hx : x ∈ MulAction.orbit NativeSporadic.Co1 v₂) :
    ∃ y ∈ MulAction.orbit NativeSporadic.Co1 v₄, x + y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      2 ^ 18 ∣ Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 x ⊓
        MulAction.stabilizer NativeSporadic.Co1 y) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨z₀, hz₀⟩ : (cls 1).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [cls_ncard (by norm_num)]; decide)
  have hy₀ : v₂ + z₀ ∈ MulAction.orbit NativeSporadic.Co1 v₄ := hz₀.2
  refine ⟨g • (v₂ + z₀), orbit_smul_mem g hy₀, ?_, ?_⟩
  · rw [← smul_add, ← add_assoc, vec_add_self, zero_add]
    exact orbit_smul_mem g hz₀.1
  · rw [card_inf_stabilizer_smul₂]
    have hstab : MulAction.stabilizer NativeSporadic.Co1 v₂ ⊓
        MulAction.stabilizer NativeSporadic.Co1 (v₂ + z₀) =
        MulAction.stabilizer NativeSporadic.Co1 v₂ ⊓
          MulAction.stabilizer NativeSporadic.Co1 z₀ := by
      ext k
      simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [smul_add, h1] at h2
        exact add_left_cancel h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [smul_add, h1, h2]
    rw [hstab]
    have h := cls_card_stab (j := 1) (by norm_num) hz₀
    rw [cls_ncard (by norm_num)] at h
    have h1 : dat.subSizes[1]! = 46575 := by decide
    rw [h1] at h
    have hc : Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 v₂ ⊓
        MulAction.stabilizer NativeSporadic.Co1 z₀) = 908328960 := by omega
    rw [hc]; norm_num

theorem pair_three
    (x : Vec24) (hx : x ∈ MulAction.orbit NativeSporadic.Co1 v₂) :
    ∃ y ∈ MulAction.orbit NativeSporadic.Co1 v₄,
      x + y ∈ MulAction.orbit NativeSporadic.Co1 v₄ := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨y₀, hy₀, hy₀'⟩ := exists_type4_adjacent
  refine ⟨g • y₀, orbit_smul_mem g hy₀, ?_⟩
  rw [← smul_add]
  exact orbit_smul_mem g hy₀'

theorem pair_to_v₂ {x y : Vec24} (hx : x ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hy : y ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hxy : x + y ∈ MulAction.orbit NativeSporadic.Co1 v₃) :
    ∃ g : NativeSporadic.Co1, g • x = v₂ ∧ g • y ∈ cls 2 := by
  obtain ⟨h, rfl⟩ := hx
  refine ⟨h⁻¹, inv_smul_smul h v₂, orbit_smul_mem _ hy, ?_⟩
  have : v₂ + h⁻¹ • y = h⁻¹ • (h • v₂ + y) := by
    rw [smul_add, inv_smul_smul]
  rw [this]
  exact orbit_smul_mem _ hxy

theorem pair_four
    {x y x' y' : Vec24} (hx : x ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hy : y ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hxy : x + y ∈ MulAction.orbit NativeSporadic.Co1 v₃)
    (hx' : x' ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hy' : y' ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hxy' : x' + y' ∈ MulAction.orbit NativeSporadic.Co1 v₃) :
    ∃ g : NativeSporadic.Co1, g • x = x' ∧ g • y = y' := by
  obtain ⟨a, ha1, ha2⟩ := pair_to_v₂ hx hy hxy
  obtain ⟨b, hb1, hb2⟩ := pair_to_v₂ hx' hy' hxy'
  obtain ⟨k, hk1, hk2⟩ := cls_trans (j := 2) (by norm_num) ha2 hb2
  refine ⟨b⁻¹ * k * a, ?_, ?_⟩
  · rw [mul_smul, mul_smul, ha1, hk1, ← hb1, inv_smul_smul]
  · rw [mul_smul, mul_smul, hk2, inv_smul_smul]

theorem pair_five
    {x y : Vec24} (hx : x ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hy : y ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hxy : x + y ∈ MulAction.orbit NativeSporadic.Co1 v₃) :
    Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 x ⊓
      MulAction.stabilizer NativeSporadic.Co1 y) = 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11 := by
  obtain ⟨g, hg1, hg2⟩ := pair_to_v₂ hx hy hxy
  rw [← card_inf_stabilizer_smul₂ g, hg1]
  have h := cls_card_stab (j := 2) (by norm_num) hg2
  rw [cls_ncard (by norm_num)] at h
  have h2 : dat.subSizes[2]! = 47104 := by decide
  rw [h2] at h
  omega

theorem pair_six
    {x y w : Vec24} (hx : x ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hy : y ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hxy : x + y ∈ MulAction.orbit NativeSporadic.Co1 v₃)
    (hw : w ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hxw : x + w ∈ MulAction.orbit NativeSporadic.Co1 v₂)
    (hwy : w + y ∈ MulAction.orbit NativeSporadic.Co1 v₂) :
    Nat.card ↥(MulAction.stabilizer NativeSporadic.Co1 x ⊓
      MulAction.stabilizer NativeSporadic.Co1 w ⊓ MulAction.stabilizer NativeSporadic.Co1 y) =
        2 ^ 7 * 3 ^ 6 * 5 * 7 := by
  obtain ⟨x₀, y₀, w₀, K, hx₀, hy₀, hxy₀, hK, hw₀, htrans, hcard⟩ := mcl_facts
  obtain ⟨g, hgx, hgy⟩ := pair_four hx hy hxy hx₀ hy₀ hxy₀
  have hw' : g • w ∈ adjSet x₀ y₀ := by
    refine ⟨orbit_smul_mem g hw, ?_, ?_⟩
    · rw [← hgx, ← smul_add]; exact orbit_smul_mem g hxw
    · rw [← hgy, ← smul_add]; exact orbit_smul_mem g hwy
  rw [← card_inf_stabilizer_smul₃ g, hgx, hgy, inf_right_comm]
  have h5 := pair_five hx₀ hy₀ hxy₀
  have htr : ∀ t ∈ adjSet x₀ y₀, ∃ k ∈ MulAction.stabilizer NativeSporadic.Co1 x₀ ⊓
      MulAction.stabilizer NativeSporadic.Co1 y₀, k • (g • w) = t := by
    intro t ht
    obtain ⟨a, haK, ha⟩ := htrans t ht
    obtain ⟨b, hbK, hb⟩ := htrans _ hw'
    exact ⟨a * b⁻¹, hK (K.mul_mem haK (K.inv_mem hbK)), by
      rw [mul_smul, ← hb, inv_smul_smul, ha]⟩
  have hmain := ncard_mul_card_inf_stabilizer
    (K := MulAction.stabilizer NativeSporadic.Co1 x₀ ⊓ MulAction.stabilizer NativeSporadic.Co1 y₀)
    hw' htr (fun k hk t ht => adjSet_smul_mem hk.1 hk.2 ht)
  rw [hcard, h5] at hmain
  omega

theorem co1Orbit_zero :
    CFSG.Monster.GMS.co1Orbit 0 = MulAction.orbit NativeSporadic.Co1 v₂ := rfl

theorem co1Orbit_one :
    CFSG.Monster.GMS.co1Orbit 1 = MulAction.orbit NativeSporadic.Co1 v₃ := rfl

theorem co1Orbit_two :
    CFSG.Monster.GMS.co1Orbit 2 = MulAction.orbit NativeSporadic.Co1 v₄ := rfl

theorem co1Stab_eq (v : Vec24) :
    CFSG.Monster.GMS.co1Stab v = MulAction.stabilizer NativeSporadic.Co1 v := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  rfl

theorem co1Act_eq (g : NativeSporadic.Co1) (v : Vec24) :
    CFSG.Monster.GMS.co1Act g v = g • v := rfl

end CFSG.Sporadic.Co1.Module.Pairs

namespace CFSG.Monster.GMS

open CFSG.Sporadic.Co1.Module.Pairs

theorem co1PairFacts :
    Co1PairFacts := by
  unfold Co1PairFacts
  simp only [co1Orbit_zero, co1Orbit_one, co1Orbit_two, co1Stab_eq, co1Act_eq]
  refine ⟨pair_one, pair_two, pair_three, ?_, ?_, ?_⟩
  · intro x y x' y' hx hy hxy hx' hy' hxy'
    exact pair_four hx hy hxy hx' hy' hxy'
  · intro x y hx hy hxy
    exact pair_five hx hy hxy
  · intro x y w hx hy hxy hw hxw hwy
    exact pair_six hx hy hxy hw hxw hwy

end CFSG.Monster.GMS
