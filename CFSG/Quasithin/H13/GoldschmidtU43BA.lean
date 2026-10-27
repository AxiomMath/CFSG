module

public import CFSG.Quasithin.H13.GoldschmidtU43BPhi2
public import CFSG.Quasithin.H13.GoldschmidtU43BTwo

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable {z t w a : G}

@[expose] noncomputable def tauV (s : Swap z t w) : V4 := Multiplicative.toAdd (s.hyp.θ ⟨t, s.ht.1⟩)

@[expose] noncomputable def alphaV (s : Swap z t w) (ha : Good z t a) : V4 :=
  Multiplicative.toAdd (s.hyp.θ ⟨a, ha.mem.1⟩)

theorem linePair_ta [Finite G] (s : Swap z t w) (ha : Good z t a) :
    LinePair (s.tauV) (s.alphaV ha) := by
  have h := s.hyp
  have haz : a ≠ z := fun e => ha.notV (e ▸ z_mem_Vg z t)
  have ha1 : a ≠ 1 := fun e => ha.notV (e ▸ one_mem _)
  refine ⟨h.q_θ_eq_zero s.ht.1 s.ht.2.1, h.q_θ_eq_zero ha.mem.1 ha.sq, ?_, ?_, ?_, ?_⟩
  · have := h.comm_eq ⟨t, s.ht.1⟩ ⟨a, ha.mem.1⟩
    have hc : t * a * t⁻¹ * a⁻¹ = 1 := by
      have e : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp ha.mem.2
      calc t * a * t⁻¹ * a⁻¹ = (t * a) * (a * t)⁻¹ := by group
        _ = 1 := by rw [e]; group
    have h2 : zp z (bq (Multiplicative.toAdd (h.θ ⟨t, s.ht.1⟩))
        (Multiplicative.toAdd (h.θ ⟨a, ha.mem.1⟩))) = zp z 0 := by
      rw [zp_zero, ← this]
      exact hc
    exact zp_injective h.z_ne_one h2
  · intro h0
    exact h.θ_ne_one s.ht.1 s.ht.2.2.1 s.ht.2.2.2
      (Multiplicative.toAdd.injective (by simpa [tauV] using h0))
  · intro h0
    exact h.θ_ne_one ha.mem.1 ha1 haz
      (Multiplicative.toAdd.injective (by simpa [alphaV] using h0))
  · intro hτα
    have hθ : h.θ ⟨a, ha.mem.1⟩ = h.θ ⟨t, s.ht.1⟩ :=
      Multiplicative.toAdd.injective hτα.symm
    rcases h.eq_of_θ_eq ha.mem.1 s.ht.1 hθ with e | e
    · exact ha.notV (by rw [e]; exact t_mem_Vg z t)
    · exact ha.notV (by rw [e]; exact zt_mem_Vg z t)

@[expose] def A0 (s : Swap z t w) (ha : Good z t a) : Set G :=
  {x | ∃ hx : x ∈ Uz z, Aset s.tauV (s.alphaV ha) (Multiplicative.toAdd (s.hyp.θ ⟨x, hx⟩))}

theorem mem_A0_iff [Finite G] (s : Swap z t w) (ha : Good z t a) (x : G) :
    x ∈ A0 s ha ↔ ∃ v ∈ Vg z t, ∃ i : ZMod 2, x = v * zp a i := by
  have h := s.hyp
  have hp := s.cm
  constructor
  · rintro ⟨hx, hA⟩
    have key : ∀ y : G, ∀ hy : y ∈ Uz z, h.θ ⟨x, hx⟩ = h.θ ⟨y, hy⟩ →
        x = y ∨ x = z * y := by
      intro y hy hθ
      by_cases hxy : x = y
      · exact Or.inl hxy
      · right
        have h1 : h.θ (⟨x, hx⟩ * ⟨y, hy⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, hθ]
          exact mul_inv_cancel _
        rcases (h.θ_eq_one_iff _).1 h1 with h2 | h2
        · exact absurd (mul_inv_eq_one.mp (by simpa using h2)) hxy
        · have : x * y⁻¹ = z := by simpa using h2
          calc x = (x * y⁻¹) * y := by group
            _ = z * y := by rw [this]
    rcases hA with e | e | e | e
    · rcases key 1 (one_mem _) (by
        have : h.θ ⟨x, hx⟩ = 1 := Multiplicative.toAdd.injective (by simpa using e)
        rw [this]; exact (map_one h.θ).symm) with e' | e'
      · exact ⟨1, one_mem _, 0, by rw [e']; simp [zp_zero]⟩
      · exact ⟨z, z_mem_Vg z t, 0, by rw [e']; simp [zp_zero]⟩
    · rcases key t s.ht.1 (by
        have : h.θ ⟨x, hx⟩ = h.θ ⟨t, s.ht.1⟩ :=
          Multiplicative.toAdd.injective (by simpa [tauV] using e)
        exact this) with e' | e'
      · exact ⟨t, t_mem_Vg z t, 0, by rw [e']; simp [zp_zero]⟩
      · exact ⟨z * t, zt_mem_Vg z t, 0, by rw [e']; simp [zp_zero]⟩
    · rcases key a ha.mem.1 (by
        have : h.θ ⟨x, hx⟩ = h.θ ⟨a, ha.mem.1⟩ :=
          Multiplicative.toAdd.injective (by simpa [alphaV] using e)
        exact this) with e' | e'
      · exact ⟨1, one_mem _, 1, by rw [e']; simp [zp_one]⟩
      · exact ⟨z, z_mem_Vg z t, 1, by rw [e']; simp [zp_one]⟩
    · have hta : t * a ∈ Uz z := mul_mem s.ht.1 ha.mem.1
      rcases key (t * a) hta (by
        have : h.θ ⟨x, hx⟩ = h.θ ⟨t * a, hta⟩ := by
          have e2 : h.θ ⟨t * a, hta⟩ = h.θ ⟨t, s.ht.1⟩ * h.θ ⟨a, ha.mem.1⟩ := by
            rw [← map_mul]; rfl
          rw [e2]
          apply Multiplicative.toAdd.injective
          rw [toAdd_mul]
          simpa [tauV, alphaV] using e
        exact this) with e' | e'
      · exact ⟨t, t_mem_Vg z t, 1, by rw [e']; simp [zp_one]⟩
      · exact ⟨z * t, zt_mem_Vg z t, 1, by rw [e']; simp [zp_one, mul_assoc]⟩
  · rintro ⟨v, hv, i, rfl⟩
    have hvU : v ∈ Uz z := s.Vg_le_U hv
    have hai : zp a i ∈ Uz z := by
      rcases zmod_two_cases i with rfl | rfl
      · rw [zp_zero]; exact one_mem _
      · rw [zp_one]; exact ha.mem.1
    refine ⟨mul_mem hvU hai, ?_⟩
    have hθv : h.θ ⟨v * zp a i, mul_mem hvU hai⟩ = h.θ ⟨v, hvU⟩ * h.θ ⟨zp a i, hai⟩ := by
      rw [← map_mul]; rfl
    rw [hθv, toAdd_mul]
    rcases s.theta_V hv with e1 | e1 <;> rcases zmod_two_cases i with rfl | rfl
    · left
      have : h.θ ⟨zp a 0, hai⟩ = 1 := by
        have : (⟨zp a 0, hai⟩ : ↥(Uz z)) = 1 := Subtype.ext (zp_zero a)
        rw [this, map_one]
      rw [this, toAdd_one, e1]; simp
    · rw [show h.θ ⟨zp a 1, hai⟩ = h.θ ⟨a, ha.mem.1⟩ from by simp only [zp_one]]
      right; right; left
      rw [e1]; simp [alphaV]
    · have : h.θ ⟨zp a 0, hai⟩ = 1 := by
        have : (⟨zp a 0, hai⟩ : ↥(Uz z)) = 1 := Subtype.ext (zp_zero a)
        rw [this, map_one]
      right; left
      rw [this, toAdd_one, e1]; simp [tauV]
    · rw [show h.θ ⟨zp a 1, hai⟩ = h.θ ⟨a, ha.mem.1⟩ from by simp only [zp_one]]
      right; right; right
      rw [e1]; simp [alphaV, tauV]


theorem A0_le_E [Finite G] (s : Swap z t w) (ha : Good z t a) {x : G} (hx : x ∈ A0 s ha) :
    x ∈ Eg z t w a := by
  obtain ⟨v, hv, i, rfl⟩ := (s.mem_A0_iff ha x).1 hx
  exact (s.mem_Eg_iff ha _).2 ⟨v, hv, i, 0, by simp [zp_zero]⟩

theorem E_inf_U_le_A0 [Finite G] (s : Swap z t w) (ha : Good z t a) {x : G}
    (hxE : x ∈ Eg z t w a) (hxU : x ∈ Uz z) : x ∈ A0 s ha := by
  obtain ⟨v, hv, i, j, rfl⟩ := (s.mem_Eg_iff ha x).1 hxE
  have hvU : v ∈ Uz z := s.Vg_le_U hv
  have hai : zp a i ∈ Uz z := by
    rcases zmod_two_cases i with rfl | rfl
    · rw [zp_zero]; exact one_mem _
    · rw [zp_one]; exact ha.mem.1
  rcases zmod_two_cases j with rfl | rfl
  · exact (s.mem_A0_iff ha _).2 ⟨v, hv, i, by simp [zp_zero]⟩
  · exfalso
    rw [zp_one] at hxU
    have hmU : w⁻¹ * a * w ∈ Uz z := by
      have e : w⁻¹ * a * w = (v * zp a i)⁻¹ * (v * zp a i * (w⁻¹ * a * w)) := by group
      rw [e]
      exact mul_mem ((Uz z).inv_mem (mul_mem hvU hai)) hxU
    apply s.m_notV ha
    refine (s.mem_N1_inf_N2 _).1 ⟨⟨hmU, (s.m_mem_B ha).2⟩, m_mem_N2 ha⟩

theorem ncard_A0_le [Finite G] (s : Swap z t w) (ha : Good z t a) : (A0 s ha).ncard ≤ 8 := by
  classical
  let f : ↥(Vg z t) × ZMod 2 → G := fun p => (p.1 : G) * zp a p.2
  have hsub : A0 s ha ⊆ Set.range f := by
    intro x hx
    obtain ⟨v, hv, i, rfl⟩ := (s.mem_A0_iff ha x).1 hx
    exact ⟨(⟨v, hv⟩, i), rfl⟩
  calc (A0 s ha).ncard ≤ (Set.range f).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (↥(Vg z t) × ZMod 2) := by
        rw [← Set.image_univ]
        calc (f '' Set.univ).ncard ≤ (Set.univ : Set (↥(Vg z t) × ZMod 2)).ncard :=
              Set.ncard_image_le (Set.toFinite _)
          _ = Nat.card (↥(Vg z t) × ZMod 2) := Set.ncard_univ _
    _ = 8 := by rw [Nat.card_prod, s.card_Vg]; simp


theorem t_mem_A0 [Finite G] (s : Swap z t w) (ha : Good z t a) : t ∈ A0 s ha :=
  (s.mem_A0_iff ha t).2 ⟨t, t_mem_Vg z t, 0, by simp [zp_zero]⟩

theorem a_mem_A0 [Finite G] (s : Swap z t w) (ha : Good z t a) : a ∈ A0 s ha :=
  (s.mem_A0_iff ha a).2 ⟨1, one_mem _, 1, by simp [zp_one]⟩

theorem bq_eq_zero_of_commute (s : Swap z t w) {x u : G} (hx : x ∈ Uz z) (hu : u ∈ Uz z)
    (hc : u * x = x * u) :
    bq (Multiplicative.toAdd (s.hyp.θ ⟨x, hx⟩)) (Multiplicative.toAdd (s.hyp.θ ⟨u, hu⟩)) = 0 := by
  have h := s.hyp
  have := h.comm_eq ⟨x, hx⟩ ⟨u, hu⟩
  have h1 : x * u * x⁻¹ * u⁻¹ = 1 := by
    calc x * u * x⁻¹ * u⁻¹ = (x * u) * (u * x)⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have h2 : zp z (bq (Multiplicative.toAdd (h.θ ⟨x, hx⟩))
      (Multiplicative.toAdd (h.θ ⟨u, hu⟩))) = zp z 0 := by
    rw [zp_zero, ← this]
    exact h1
  exact zp_injective h.z_ne_one h2

theorem centralizer_A0 [Finite G] (s : Swap z t w) (ha : Good z t a) :
    Hz z ⊓ Subgroup.centralizer (A0 s ha) = Eg z t w a := by
  have h := s.hyp
  have hlp := s.linePair_ta ha
  have hEX : Eg z t w a ≤ Hz z ⊓ Subgroup.centralizer (A0 s ha) := by
    intro x hx
    exact ⟨(s.Eg_le_B ha hx).1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (s.Eg_comm_sq ha (s.A0_le_E ha hy) hx).1⟩
  refine (Subgroup.eq_of_le_of_card_ge hEX ?_).symm
  rw [s.card_Eg ha]
  have hXH : Hz z ⊓ Subgroup.centralizer (A0 s ha) ≤ Hz z := inf_le_left
  have h1 : Nat.card (((Hz z ⊓ Subgroup.centralizer (A0 s ha)).subgroupOf (Hz z)).map h.act)
      ≤ 2 := by
    set S := ((Hz z ⊓ Subgroup.centralizer (A0 s ha)).subgroupOf (Hz z)).map h.act with hS
    have hsub : (S : Set (MulAut (Multiplicative V4))) ⊆ FixA s.tauV (s.alphaV ha) := by
      intro g hg
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg
      have hcX : (c : G) ∈ Hz z ⊓ Subgroup.centralizer (A0 s ha) := hc
      have hcc := Subgroup.mem_centralizer_iff.mp hcX.2
      refine ⟨h.act_mem_Oq c, ?_, ?_⟩
      · have e : conjU c ⟨t, s.ht.1⟩ = ⟨t, s.ht.1⟩ := by
          apply Subtype.ext
          rw [coe_conjU]
          have := hcc t (s.t_mem_A0 ha)
          calc (c : G) * t * (c : G)⁻¹ = (t * (c : G)) * (c : G)⁻¹ := by rw [← this]
            _ = t := by group
        show Multiplicative.toAdd ((h.act c) (Multiplicative.ofAdd s.tauV)) = s.tauV
        have e2 : Multiplicative.ofAdd s.tauV = h.θ ⟨t, s.ht.1⟩ := by simp [tauV]
        rw [e2, h.act_θ, e]
        rfl
      · have e : conjU c ⟨a, ha.mem.1⟩ = ⟨a, ha.mem.1⟩ := by
          apply Subtype.ext
          rw [coe_conjU]
          have := hcc a (s.a_mem_A0 ha)
          calc (c : G) * a * (c : G)⁻¹ = (a * (c : G)) * (c : G)⁻¹ := by rw [← this]
            _ = a := by group
        show Multiplicative.toAdd ((h.act c) (Multiplicative.ofAdd (s.alphaV ha))) =
          s.alphaV ha
        have e2 : Multiplicative.ofAdd (s.alphaV ha) = h.θ ⟨a, ha.mem.1⟩ := by simp [alphaV]
        rw [e2, h.act_θ, e]
        rfl
    rw [show Nat.card ↥S = Set.ncard (S : Set (MulAut (Multiplicative V4))) from
      Nat.card_coe_set_eq _]
    calc Set.ncard (S : Set (MulAut (Multiplicative V4)))
        ≤ Set.ncard (FixA s.tauV (s.alphaV ha)) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (FixA s.tauV (s.alphaV ha)) := (Nat.card_coe_set_eq _).symm
      _ ≤ 2 := card_FixA_le hlp
  have h2 : Nat.card ↥((Hz z ⊓ Subgroup.centralizer (A0 s ha)) ⊓ Uz z) ≤ 8 := by
    have hsub : (((Hz z ⊓ Subgroup.centralizer (A0 s ha)) ⊓ Uz z : Subgroup G) : Set G) ⊆
        A0 s ha := by
      intro x hx
      have hxU : x ∈ Uz z := hx.2
      have hcc := Subgroup.mem_centralizer_iff.mp hx.1.2
      refine ⟨hxU, perp_line _ _ hlp _ ?_ ?_⟩
      · exact s.bq_eq_zero_of_commute hxU s.ht.1 (hcc t (s.t_mem_A0 ha))
      · exact s.bq_eq_zero_of_commute hxU ha.mem.1 (hcc a (s.a_mem_A0 ha))
    rw [show Nat.card ↥((Hz z ⊓ Subgroup.centralizer (A0 s ha)) ⊓ Uz z) =
      Set.ncard (((Hz z ⊓ Subgroup.centralizer (A0 s ha)) ⊓ Uz z : Subgroup G) : Set G) from
      Nat.card_coe_set_eq _]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (s.ncard_A0_le ha)
  exact (h.card_le_of_act _ hXH h1 h2).trans (by norm_num)

end Swap

end CFSG.Quasithin.H13.U43
