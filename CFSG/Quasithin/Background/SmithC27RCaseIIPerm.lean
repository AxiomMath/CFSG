module

public import CFSG.Quasithin.Background.SmithC27AltSetup
public import CFSG.Quasithin.Background.SmithC27RLieBasic
public import CFSG.LieType.SteinbergBROddSylowNormalizers

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.QuasithinUnique Equiv Equiv.Perm MulAction

section Generic

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def IsRadSig (P : Subgroup (Perm α)) : Prop :=
  ∀ Y : Subgroup (Perm α), IsPGroup 2 Y →
    Subgroup.normalizer (P : Set (Perm α)) ≤ Subgroup.normalizer (Y : Set (Perm α)) → Y ≤ P

omit [Fintype α] [DecidableEq α] in
theorem mem_orbit_subgroup_iff {P : Subgroup (Perm α)} {x y : α} :
    y ∈ orbit ↥P x ↔ ∃ g ∈ P, g x = y := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

omit [Fintype α] [DecidableEq α] in
theorem mem_fixedPoints_subgroup_iff {P : Subgroup (Perm α)} {x : α} :
    x ∈ fixedPoints ↥P α ↔ ∀ g ∈ P, g x = x :=
  ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

omit [Fintype α] [DecidableEq α] in
theorem conj_mem_of_mem_normalizer {P : Subgroup (Perm α)} {m : Perm α}
    (hm : m ∈ Subgroup.normalizer (P : Set (Perm α))) {g : Perm α} (hg : g ∈ P) :
    m * g * m⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.1 hm g).1 hg

omit [Fintype α] [DecidableEq α] in
theorem apply_mem_orbit_iff {P : Subgroup (Perm α)} {m : Perm α}
    (hm : m ∈ Subgroup.normalizer (P : Set (Perm α))) {x y : α} :
    m y ∈ orbit ↥P (m x) ↔ y ∈ orbit ↥P x := by
  rw [mem_orbit_subgroup_iff, mem_orbit_subgroup_iff]
  constructor
  · rintro ⟨g, hg, hgy⟩
    refine ⟨m⁻¹ * g * m, ?_, ?_⟩
    · have h := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hm) hg
      simpa using h
    · simp [Perm.mul_apply, hgy]
  · rintro ⟨g, hg, rfl⟩
    exact ⟨m * g * m⁻¹, conj_mem_of_mem_normalizer hm hg, by simp [Perm.mul_apply]⟩

omit [Fintype α] [DecidableEq α] in
theorem orbit_apply_eq_image {P : Subgroup (Perm α)} {m : Perm α}
    (hm : m ∈ Subgroup.normalizer (P : Set (Perm α))) (x : α) :
    orbit ↥P (m x) = (m : α → α) '' orbit ↥P x := by
  ext y
  constructor
  · intro hy
    refine ⟨m⁻¹ y, ?_, by simp⟩
    rw [← apply_mem_orbit_iff hm]
    simpa using hy
  · rintro ⟨w, hw, rfl⟩
    exact (apply_mem_orbit_iff hm).2 hw

omit [Fintype α] [DecidableEq α] in
theorem card_orbit_apply {P : Subgroup (Perm α)} {m : Perm α}
    (hm : m ∈ Subgroup.normalizer (P : Set (Perm α))) (x : α) :
    Nat.card (orbit ↥P (m x)) = Nat.card (orbit ↥P x) := by
  rw [orbit_apply_eq_image hm, Nat.card_image_of_injective m.injective]

omit [Fintype α] [DecidableEq α] in
theorem apply_mem_fixedPoints_iff {P : Subgroup (Perm α)} {m : Perm α}
    (hm : m ∈ Subgroup.normalizer (P : Set (Perm α))) {x : α} :
    m x ∈ fixedPoints ↥P α ↔ x ∈ fixedPoints ↥P α := by
  rw [mem_fixedPoints_subgroup_iff, mem_fixedPoints_subgroup_iff]
  constructor
  · intro h g hg
    have h1 := h _ (conj_mem_of_mem_normalizer hm hg)
    simpa [Perm.mul_apply] using h1
  · intro h g hg
    have h1 := h _ (conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hm) hg)
    have h2 : m⁻¹ (g (m x)) = x := by simpa [Perm.mul_apply] using h1
    calc g (m x) = m (m⁻¹ (g (m x))) := by simp
      _ = m x := by rw [h2]

omit [Fintype α] [DecidableEq α] in
theorem mem_normalizer_zpowers_of_commute {h m : Perm α} (hc : m * h * m⁻¹ = h) :
    m ∈ Subgroup.normalizer ((Subgroup.zpowers h : Subgroup (Perm α)) : Set (Perm α)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp only; rw [← conj_zpow, hc]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : m * h ^ k * m⁻¹ = h ^ k := by rw [← conj_zpow, hc]
    have h2 : m * y * m⁻¹ = m * h ^ k * m⁻¹ := by
      simp only at hk
      rw [h1, hk]
    exact (mul_left_cancel (mul_right_cancel h2)).symm

omit [Fintype α] in
theorem IsRadSig.swap_mem {P : Subgroup (Perm α)} (hrad : IsRadSig P) {a b : α}
    (hN : ∀ m ∈ Subgroup.normalizer (P : Set (Perm α)),
      (m a = a ∧ m b = b) ∨ (m a = b ∧ m b = a)) :
    swap a b ∈ P := by
  have hY : IsPGroup 2 (Subgroup.zpowers (swap a b)) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, pow_two, swap_mul_self])
  refine hrad _ hY (fun m hm => mem_normalizer_zpowers_of_commute ?_) (Subgroup.mem_zpowers _)
  rw [← swap_apply_apply]
  rcases hN m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, swap_comm]

omit [Fintype α] [DecidableEq α] in
theorem exists_pairing {P : Subgroup (Perm α)} (h2 : ∀ x : α, Nat.card (orbit ↥P x) = 2) :
    ∃ z : Perm α, z * z = 1 ∧ (∀ x, z x ≠ x) ∧ (∀ g ∈ P, ∀ x, g x = x ∨ g x = z x) ∧
      Subgroup.normalizer (P : Set (Perm α)) ≤ Subgroup.centralizer {z} := by
  have hex : ∀ x : α, ∃ y : α, y ≠ x ∧ orbit ↥P x = {x, y} := by
    intro x
    obtain ⟨a, b, hab, he⟩ := Set.ncard_eq_two.1 (by rw [← Nat.card_coe_set_eq]; exact h2 x)
    have hx : x ∈ orbit ↥P x := mem_orbit_self (M := ↥P) x
    rw [he] at hx
    rcases hx with rfl | rfl
    · exact ⟨b, hab.symm, he⟩
    · exact ⟨a, hab, by rw [he, Set.pair_comm]⟩
  choose f hf1 hf2 using hex
  have hmem : ∀ x : α, f x ∈ orbit ↥P x := fun x => by
    rw [hf2 x]
    exact Or.inr rfl
  have hff : ∀ x : α, f (f x) = x := by
    intro x
    have h1 : orbit ↥P (f x) = orbit ↥P x := orbit_eq_iff.2 (hmem x)
    have h2 : f (f x) ∈ orbit ↥P x := by rw [← h1]; exact hmem (f x)
    rw [hf2 x] at h2
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd (h2.symm ▸ rfl : f (f x) = f x) (hf1 (f x))
  let z : Perm α := Function.Involutive.toPerm f hff
  have hz : ∀ x, z x = f x := fun _ => rfl
  refine ⟨z, Equiv.ext fun x => by simp [Perm.mul_apply, hz, hff], fun x => by
    rw [hz]; exact hf1 x, fun g hg x => ?_, fun m hm => ?_⟩
  · have h1 : g x ∈ orbit ↥P x := mem_orbit_subgroup_iff.2 ⟨g, hg, rfl⟩
    rw [hf2 x] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [hz]; exact h1)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    refine Equiv.ext fun x => ?_
    show m (z x) = z (m x)
    rw [hz, hz]
    have h1 : f (m x) ∈ orbit ↥P (m x) := hmem (m x)
    rw [orbit_apply_eq_image hm, hf2 x] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    rcases hw with rfl | rfl
    · exact absurd hwe.symm (hf1 (m w))
    · exact hwe

omit [DecidableEq α] in
theorem exists_sylow_le_of_not_two_dvd_index {C : Subgroup (Perm α)} (h : ¬ 2 ∣ C.index) :
    ∃ T : Subgroup (Perm α), IsSylowTwoOf T ⊤ ∧ T ≤ C := by
  obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup (Perm α)) ≤ C)
    (IsPGroup.of_card (n := 0) (by simp))
  refine ⟨T, ⟨le_top, hT.2.1, fun h2 => ?_⟩, hT.1⟩
  have e := Subgroup.relIndex_mul_relIndex T C ⊤ hT.1 le_top
  rw [Subgroup.relIndex_top_right] at e
  have h2' : 2 ∣ T.relIndex C * C.index := by
    rw [e]
    exact h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2' with h3 | h3
  · exact hT.2.2 h3
  · exact h h3

theorem two_dvd_card_support_of_mul_self {z : Perm α} (hz : z * z = 1) :
    2 ∣ z.support.card := by
  have h1 : z.cycleType.sum = z.support.card := Perm.sum_cycleType z
  rw [cycleType_of_mul_self hz, Multiset.sum_replicate, smul_eq_mul] at h1
  exact ⟨z.support.card / 2, by omega⟩

theorem card_centralizer_of_mul_self {z : Perm α} (hz : z * z = 1) :
    Nat.card (Subgroup.centralizer {z}) =
      (Fintype.card α - z.support.card).factorial * 2 ^ (z.support.card / 2) *
        (z.support.card / 2).factorial := by
  have hct := cycleType_of_mul_self hz
  have heven := two_dvd_card_support_of_mul_self hz
  rw [Perm.nat_card_centralizer, hct, Multiset.sum_replicate, Multiset.prod_replicate,
    smul_eq_mul, Nat.div_mul_cancel heven]
  congr 1
  rcases Nat.eq_zero_or_pos (z.support.card / 2) with h0 | hpos
  · rw [h0]
    simp
  · have hne : z.support.card / 2 ≠ 0 := by omega
    simp [Multiset.toFinset_replicate, hne]

omit [DecidableEq α] in
theorem exists_pairing_of_le_two {P : Subgroup (Perm α)}
    (h2 : ∀ x : α, Nat.card (orbit ↥P x) ≤ 2) :
    ∃ z : Perm α, z * z = 1 ∧ (∀ g ∈ P, ∀ x, g x = x ∨ g x = z x) ∧
      Subgroup.normalizer (P : Set (Perm α)) ≤ Subgroup.centralizer {z} := by
  have hex : ∀ x : α, ∃ y : α, orbit ↥P x = {x, y} := by
    intro x
    have hx : x ∈ orbit ↥P x := mem_orbit_self (M := ↥P) x
    have hpos : 0 < (orbit ↥P x).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨x, hx⟩
    have hle : (orbit ↥P x).ncard ≤ 2 := by rw [← Nat.card_coe_set_eq]; exact h2 x
    rcases (by omega : (orbit ↥P x).ncard = 1 ∨ (orbit ↥P x).ncard = 2) with h1 | h1
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
      rw [ha] at hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨x, by rw [ha, hx, Set.pair_eq_singleton]⟩
    · obtain ⟨a, b, -, he⟩ := Set.ncard_eq_two.1 h1
      rw [he] at hx
      rcases hx with rfl | rfl
      · exact ⟨b, he⟩
      · exact ⟨a, by rw [he, Set.pair_comm]⟩
  choose f hf using hex
  have hmem : ∀ x : α, f x ∈ orbit ↥P x := fun x => by
    rw [hf x]
    exact Or.inr rfl
  have hff : ∀ x : α, f (f x) = x := by
    intro x
    have h1 : orbit ↥P (f x) = orbit ↥P x := orbit_eq_iff.2 (hmem x)
    have h2 : x ∈ orbit ↥P (f x) := by
      rw [h1]
      exact mem_orbit_self (M := ↥P) x
    have h3 : f (f x) ∈ orbit ↥P x := by
      rw [← h1]
      exact hmem (f x)
    rw [hf x] at h3
    rcases h3 with h3 | h3
    · exact h3
    · rw [hf (f x), h3, Set.pair_eq_singleton, Set.mem_singleton_iff] at h2
      rw [h3]
      exact h2.symm
  let z : Perm α := Function.Involutive.toPerm f hff
  have hz : ∀ x, z x = f x := fun _ => rfl
  refine ⟨z, Equiv.ext fun x => by simp [Perm.mul_apply, hz, hff], fun g hg x => ?_, fun m hm => ?_⟩
  · have h1 : g x ∈ orbit ↥P x := mem_orbit_subgroup_iff.2 ⟨g, hg, rfl⟩
    rw [hf x] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [hz]; exact h1)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    refine Equiv.ext fun x => ?_
    show m (z x) = z (m x)
    rw [hz, hz]
    have h1 : f (m x) ∈ orbit ↥P (m x) := hmem (m x)
    have h2 : orbit ↥P (m x) = {m x, m (f x)} := by
      rw [orbit_apply_eq_image hm, hf x, Set.image_pair]
    rw [h2] at h1
    rcases h1 with h1 | h1
    ·
      have h3 : orbit ↥P (m x) = {m x} := by
        rw [hf (m x), h1, Set.pair_eq_singleton]
      have h4 : m (f x) ∈ orbit ↥P (m x) := by
        rw [h2]
        exact Or.inr rfl
      rw [h3, Set.mem_singleton_iff] at h4
      rw [h4, h1]
    · exact h1.symm

omit [Fintype α] [DecidableEq α] in
theorem mul_self_of_mem_swapGroupOf {z : Perm α} {hz : z * z = 1} {g : Perm α}
    (hg : g ∈ swapGroupOf z hz) : g * g = 1 := by
  have hzz := apply_apply_of_mul_self hz
  refine Equiv.ext fun x => ?_
  show g (g x) = x
  rcases hg x with h | h
  · rw [h, h]
  · rcases hg (z x) with h' | h'
    · have h4 : z x = x := g.injective (h'.trans h.symm)
      rw [h, h']
      exact h4
    · rw [h, h', hzz]

omit [Fintype α] [DecidableEq α] in
theorem isPGroup_swapGroupOf {z : Perm α} (hz : z * z = 1) : IsPGroup 2 (swapGroupOf z hz) :=
  fun g => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact mul_self_of_mem_swapGroupOf g.2)⟩

omit [DecidableEq α] in
theorem exists_sylow_le_normalizer_of_card {P : Subgroup (Perm α)} (hP : IsPGroup 2 P) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card (Perm α)) (hk' : ¬ 2 ^ (k + 1) ∣ Nat.card (Perm α))
    (hcard : 2 ^ k ≤ 2 * Nat.card P) :
    ∃ T : Subgroup (Perm α), IsSylowTwoOf T ⊤ ∧
      T ≤ Subgroup.normalizer (P : Set (Perm α)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hPT⟩ := A4.exists_isSylowTwoOf_ge (le_top : P ≤ ⊤) hP
  refine ⟨T, hT, ?_⟩
  obtain ⟨j, hj⟩ := hT.2.1.exists_card_eq
  have hTi := Subgroup.card_mul_index T
  have hodd : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at this
  have hjk : j = k := by
    apply le_antisymm
    · by_contra hlt
      apply hk'
      rw [← hTi, hj]
      exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (by omega)) _
    · have h1 : 2 ^ k ∣ 2 ^ j * T.index := by rw [← hj, hTi]; exact hk
      have h2 : Nat.Coprime (2 ^ k) T.index :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
      have h3 := h2.dvd_of_dvd_mul_right h1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3
  have hPc : Nat.card ↥(P.subgroupOf T) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv
  have hPi := Subgroup.card_mul_index (P.subgroupOf T)
  rw [hPc, hj, hjk] at hPi
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hi : (P.subgroupOf T).index ≤ 2 := by
    by_contra hgt
    have : Nat.card P * 3 ≤ Nat.card P * (P.subgroupOf T).index :=
      Nat.mul_le_mul_left _ (not_le.1 hgt)
    omega
  have hi0 : (P.subgroupOf T).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hPi
    exact absurd hPi.symm (by positivity)
  rcases (by omega : (P.subgroupOf T).index = 1 ∨ (P.subgroupOf T).index = 2) with h1 | h1
  · rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact h1.trans (Subgroup.le_normalizer)
  · have := Subgroup.normal_of_index_eq_two h1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPT).1 this

end Generic

theorem card_perm_fin_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem mem_orbit_of_mem_orbit {β : Type*} {P : Subgroup (Perm β)} {x y : β}
    (h : y ∈ orbit ↥P x) :
    orbit ↥P y = orbit ↥P x :=
  orbit_eq_iff.2 h

theorem exists_sylow_le_normalizer_six {P : Subgroup (Perm (Fin 6))} (hP : IsPGroup 2 P)
    (hrad : IsRadSig P) :
    ∃ T : Subgroup (Perm (Fin 6)), IsSylowTwoOf T ⊤ ∧
      T ≤ Subgroup.normalizer (P : Set (Perm (Fin 6))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_perm_fin_six
  have hle6 : ∀ x : Fin 6, Nat.card (orbit ↥P x) ≤ 6 := fun x => by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_card _).trans (by simp)
  have horb : ∀ x : Fin 6, Nat.card (orbit ↥P x) ≤ 2 ∨ Nat.card (orbit ↥P x) = 4 := by
    intro x
    obtain ⟨k, hk⟩ := hP.card_orbit x
    have h6 := hle6 x
    rw [hk] at h6 ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk3
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h8
      omega
    interval_cases k <;> norm_num
  by_cases h4 : ∃ x : Fin 6, Nat.card (orbit ↥P x) = 4
  · obtain ⟨x₀, hx₀⟩ := h4
    set Θ := orbit ↥P x₀ with hΘdef
    have hΘ : ∀ y, y ∈ Θ ↔ Nat.card (orbit ↥P y) = 4 := by
      intro y
      constructor
      · intro hy
        rw [mem_orbit_of_mem_orbit hy]
        exact hx₀
      · intro hy
        by_contra hyΘ
        have hsub : orbit ↥P y ⊆ Θᶜ := by
          intro w hw hwΘ
          apply hyΘ
          have h1 : orbit ↥P w = orbit ↥P y := mem_orbit_of_mem_orbit hw
          have h2 : orbit ↥P w = Θ := mem_orbit_of_mem_orbit hwΘ
          rw [← h2, h1]
          exact mem_orbit_self (M := ↥P) y
        have hc : Θᶜ.ncard = 2 := by
          rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq,
            hx₀]
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [hc, ← Nat.card_coe_set_eq, hy] at this
        omega
    have hc : Θᶜ.ncard = 2 := by
      rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hx₀]
    obtain ⟨e, f, hef, hEF⟩ := Set.ncard_eq_two.1 hc
    have heΘ : e ∉ Θ := by
      have : e ∈ Θᶜ := by rw [hEF]; exact Or.inl rfl
      exact this
    have hfΘ : f ∉ Θ := by
      have : f ∈ Θᶜ := by rw [hEF]; exact Or.inr rfl
      exact this
    have hout : ∀ y, y ∉ Θ → y = e ∨ y = f := by
      intro y hy
      have : y ∈ Θᶜ := hy
      rw [hEF] at this
      exact this
    have hsw : swap e f ∈ P := by
      refine hrad.swap_mem fun m hm => ?_
      have hme : m e ∉ Θ := by
        rw [hΘ, card_orbit_apply hm, ← hΘ]
        exact heΘ
      have hmf : m f ∉ Θ := by
        rw [hΘ, card_orbit_apply hm, ← hΘ]
        exact hfΘ
      have hne : m e ≠ m f := fun h => hef (m.injective h)
      rcases hout _ hme with h1 | h1 <;> rcases hout _ hmf with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hne
    have hx₀e : x₀ ≠ e := fun h => heΘ (h ▸ mem_orbit_self (M := ↥P) x₀)
    have hx₀f : x₀ ≠ f := fun h => hfΘ (h ▸ mem_orbit_self (M := ↥P) x₀)
    have hstab : 2 ≤ Nat.card (stabilizer ↥P x₀) := by
      have hmem : (⟨swap e f, hsw⟩ : ↥P) ∈ stabilizer ↥P x₀ := by
        show swap e f x₀ = x₀
        exact swap_apply_of_ne_of_ne hx₀e hx₀f
      have hne : (⟨⟨swap e f, hsw⟩, hmem⟩ : ↥(stabilizer ↥P x₀)) ≠ 1 := by
        intro h
        have h1 := congrArg (fun g : ↥(stabilizer ↥P x₀) => ((g : ↥P) : Perm (Fin 6)) e) h
        simp only [swap_apply_left] at h1
        exact hef.symm h1
      have : Nontrivial ↥(stabilizer ↥P x₀) := ⟨⟨_, 1, hne⟩⟩
      exact Finite.one_lt_card
    have h8 : 8 ≤ Nat.card P := by
      have hos := Subgroup.card_mul_index (stabilizer ↥P x₀)
      rw [index_stabilizer, ← Nat.card_coe_set_eq, ← hΘdef, hx₀] at hos
      omega
    exact exists_sylow_le_normalizer_of_card hP (k := 4) (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num) (by omega)
  · push Not at h4
    have hle2 : ∀ x : Fin 6, Nat.card (orbit ↥P x) ≤ 2 := fun x =>
      (horb x).resolve_right (h4 x)
    obtain ⟨z, hz, hPz, hNz⟩ := exists_pairing_of_le_two hle2
    have hPeq : P = swapGroupOf z hz := le_antisymm (fun g hg => hPz g hg)
      (hrad _ (isPGroup_swapGroupOf hz) (by rw [normalizer_swapGroupOf]; exact hNz))
    rw [hPeq, normalizer_swapGroupOf]
    apply exists_sylow_le_of_not_two_dvd_index
    have key : Nat.card (Subgroup.centralizer {z}) * (Subgroup.centralizer {z}).index = 720 := by
      rw [Subgroup.card_mul_index, hcard]
    rw [card_centralizer_of_mul_self hz, Fintype.card_fin] at key
    obtain ⟨t, ht⟩ := two_dvd_card_support_of_mul_self hz
    have hs6 : z.support.card ≤ 6 := (Finset.card_le_univ _).trans (by simp)
    rw [ht] at key
    have ht3 : t ≤ 3 := by omega
    generalize (Subgroup.centralizer {z}).index = i at key ⊢
    interval_cases t <;> norm_num [Nat.factorial] at key <;> omega

theorem normalizer_sylow_alt {n : ℕ} (hn : n = 6 ∨ n = 8)
    (U : Sylow 2 ↥(alternatingGroup (Fin n))) :
    Subgroup.normalizer ((U : Subgroup ↥(alternatingGroup (Fin n))) :
      Set ↥(alternatingGroup (Fin n))) = U := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hnab : ∃ a b : ↥(alternatingGroup (Fin n)), a * b ≠ b * a := by
    rcases hn with rfl | rfl
    · refine ⟨⟨swap 0 1 * swap 0 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
        ⟨swap 1 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩, ?_⟩
      intro h
      have := congrArg Subtype.val h
      revert this
      decide
    · refine ⟨⟨swap 0 1 * swap 0 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
        ⟨swap 1 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩, ?_⟩
      intro h
      have := congrArg Subtype.val h
      revert this
      decide
  exact (CFSG.LieType.small_alternating_and_binary_linear_odd_Sylow_normalizers_are_trivial
    ↥(alternatingGroup (Fin n)) hs hnab U 1 (by simp)
    (by rw [show ((1 : MulAut ↥(alternatingGroup (Fin n))).toMonoidHom) = MonoidHom.id _ from rfl,
      Subgroup.map_id])
    (Or.inl ⟨n, by omega, ⟨MulEquiv.refl _⟩⟩)).1

theorem inf_normalizer_le_of_sylow_alt {n : ℕ} (hn : n = 6 ∨ n = 8)
    {S : Subgroup (Perm (Fin n))} (hS : IsSylowTwoOf S (alternatingGroup (Fin n))) :
    alternatingGroup (Fin n) ⊓ Subgroup.normalizer (S : Set (Perm (Fin n))) ≤ S := by
  have h1 := isSylowTwoOf_subgroupOf hS le_rfl
  rw [Subgroup.subgroupOf_self] at h1
  obtain ⟨U, hU⟩ := exists_sylow_two_coe_eq h1
  have hN := normalizer_sylow_alt hn U
  rw [hU] at hN
  rintro x ⟨hxA, hxN⟩
  have hx : (⟨x, hxA⟩ : ↥(alternatingGroup (Fin n))) ∈
      Subgroup.normalizer ((S.subgroupOf (alternatingGroup (Fin n)) : Subgroup _) :
        Set ↥(alternatingGroup (Fin n))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hxN (y : Perm (Fin n))
  rw [hN] at hx
  exact hx

end CFSG.Quasithin.SmithC27

