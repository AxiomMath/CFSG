module

public import CFSG.Quasithin.Recognition.Stroth.MoufangApartment

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem aptRoot_le_fixingSubgroup {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) {s r : ℤ} (h1 : s ≤ r) (h2 : r ≤ s + (n : ℤ)) :
    aptRoot D Γ n t s ≤ fixingSubgroup D ({apt t r} : Set V) := by
  intro g hg
  refine (mem_fixingSubgroup_iff D).mpr fun x hx => ?_
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have h := aptRoot_fix ht hg hn (r := r - s) (by omega) (by omega)
  rwa [show s + (r - s) = r by ring] at h

theorem aptRoot_le_star {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) {s r : ℤ}
    (h1 : s + 1 ≤ r) (h2 : r ≤ s + (n : ℤ) - 1) :
    aptRoot D Γ n t s ≤ fixingSubgroup D (Γ.neighborSet (apt t r)) := by
  intro g hg
  refine (mem_fixingSubgroup_iff D).mpr fun y hy => ?_
  exact aptRoot_smul_of_adj hg (i := r - s) (by omega) (by omega) (w := y)
    (by rwa [show s + (r - s) = r by ring])

theorem iSup_aptRoot_le_fixing {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) {a b : ℤ} (hab : a < b) {r : ℤ}
    (h1 : ∀ s : ℤ, a < s → s ≤ b → s ≤ r) (h2 : ∀ s : ℤ, a < s → s ≤ b → r ≤ s + (n : ℤ)) :
    (⨆ s ∈ Set.Ioc a b, aptRoot D Γ n t s) ≤ fixingSubgroup D ({apt t r} : Set V) :=
  iSup_le fun s => iSup_le fun hs =>
    aptRoot_le_fixingSubgroup ht hn (h1 s hs.1 hs.2) (h2 s hs.1 hs.2)

theorem iSup_aptRoot_le_star {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) {a b : ℤ}
    {r : ℤ} (h1 : ∀ s : ℤ, a < s → s ≤ b → s + 1 ≤ r)
    (h2 : ∀ s : ℤ, a < s → s ≤ b → r ≤ s + (n : ℤ) - 1) :
    (⨆ s ∈ Set.Ioc a b, aptRoot D Γ n t s) ≤ fixingSubgroup D (Γ.neighborSet (apt t r)) :=
  iSup_le fun s => iSup_le fun hs => aptRoot_le_star ht (h1 s hs.1 hs.2) (h2 s hs.1 hs.2)

theorem smul_apt_eq_of_window_right {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {g : D} {a : ℤ}
    (h : ∀ r : ℤ, a ≤ r → r ≤ a + (n : ℤ) + 1 → g • apt t r = apt t r) :
    ∀ r : ℤ, a + (n : ℤ) + 1 ≤ r → r ≤ a + 2 * (n : ℤ) → g • apt t r = apt t r := by
  intro r h1 h2
  have h2end : g • apt t (a + (n : ℤ) + 1 + (n : ℤ) - 1) =
      apt t (a + (n : ℤ) + 1 + (n : ℤ) - 1) := by
    rw [show a + (n : ℤ) + 1 + (n : ℤ) - 1 = a + 2 * (n : ℤ) * 1 by ring, apt_add_two_mul]
    exact h a (by omega) (by omega)
  have hk0 : 0 ≤ r - (a + (n : ℤ) + 1) := by omega
  have hk : (r - (a + (n : ℤ) + 1)).toNat ≤ n - 1 := by
    have h3 : ((r - (a + (n : ℤ) + 1)).toNat : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hk0]
      rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
      omega
    exact_mod_cast h3
  have hfix := fix_of_smul_ends ht hn hP hT (a := a + (n : ℤ) + 1)
    (h (a + (n : ℤ) + 1) (by omega) (by omega)) h2end hk
  rwa [show a + (n : ℤ) + 1 + ((r - (a + (n : ℤ) + 1)).toNat : ℤ) = r by
    rw [Int.toNat_of_nonneg hk0]; ring] at hfix

theorem smul_apt_eq_of_window {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 1 ≤ n)
    {g : D} {a : ℤ} (h : ∀ r : ℤ, a ≤ r → r ≤ a + 2 * (n : ℤ) → g • apt t r = apt t r) (r : ℤ) :
    g • apt t r = apt t r := by
  have hpos : (0 : ℤ) < 2 * (n : ℤ) := by
    have h2 : (0 : ℕ) < 2 * n := by omega
    exact_mod_cast h2
  set s : ℤ := (r - a) % (2 * (n : ℤ)) with hs
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact Int.emod_nonneg _ hpos.ne'
  have hslt : s < 2 * (n : ℤ) := by
    rw [hs]
    exact Int.emod_lt_of_pos _ hpos
  have hdec : s + 2 * (n : ℤ) * ((r - a) / (2 * (n : ℤ))) = r - a := by
    rw [hs]
    exact Int.emod_add_mul_ediv _ _
  have hr : r = (a + s) + 2 * (n : ℤ) * ((r - a) / (2 * (n : ℤ))) := by
    conv_lhs => rw [show r = a + (r - a) by ring]
    conv_lhs => rw [show r = a + (r - a) by ring, ← hdec]
    ring
  have h1 : apt t r = apt t (a + s) := by
    rw [hr]
    exact apt_add_two_mul (t := t) (a + s) ((r - a) / (2 * (n : ℤ)))
  rw [h1]
  exact h (a + s) (by omega) (by omega)

theorem eq_one_of_fix_window {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {g : D} {i j : ℤ} (hij : i < j)
    (hjn : j < i + (n : ℤ))
    (hwin : ∀ r : ℤ, i ≤ r → r ≤ i + (n : ℤ) + 1 → g • apt t r = apt t r)
    (h0 : ∀ y : V, Γ.Adj (apt t j) y → g • y = y)
    (h1 : ∀ y : V, Γ.Adj (apt t (j + 1)) y → g • y = y) : g = 1 := by
  have hright := smul_apt_eq_of_window_right ht hn hP hT hwin
  have hwindow : ∀ r : ℤ, i ≤ r → r ≤ i + 2 * (n : ℤ) → g • apt t r = apt t r := by
    intro r h1 h2
    by_cases h3 : r ≤ i + (n : ℤ) + 1
    · exact hwin r h1 h3
    · exact hright r (by omega) h2
  have hfix : ∀ r : ℤ, g • apt t r = apt t r := smul_apt_eq_of_window ht (by omega) hwindow
  exact eq_one_of_fix_apartment_stars ht hn hP hT hfix (c := j) h0 h1

theorem commutator_mem_iSup {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n)
    {i j : ℤ} (hij : i < j) (hjn : j < i + (n : ℤ)) {u v : D}
    (hu : u ∈ aptRoot D Γ n t i) (hv : v ∈ aptRoot D Γ n t j) :
    u * v * u⁻¹ * v⁻¹ ∈ ⨆ k ∈ Set.Ioo i j, aptRoot D Γ n t k := by
  have huf : ∀ r : ℤ, i ≤ r → r ≤ i + (n : ℤ) → u • apt t r = apt t r := by
    intro r h1 h2
    have h := aptRoot_fix ht hu hn (r := r - i) (by omega) (by omega)
    rwa [show i + (r - i) = r by ring] at h
  have hvf : ∀ r : ℤ, j ≤ r → r ≤ j + (n : ℤ) → v • apt t r = apt t r := by
    intro r h1 h2
    have h := aptRoot_fix ht hv hn (r := r - j) (by omega) (by omega)
    rwa [show j + (r - j) = r by ring] at h
  have hus : ∀ r : ℤ, i + 1 ≤ r → r ≤ i + (n : ℤ) - 1 → ∀ y : V, Γ.Adj (apt t r) y →
      u • y = y := by
    intro r h1 h2 y hy
    exact aptRoot_smul_of_adj hu (i := r - i) (by omega) (by omega) (w := y)
      (by rwa [show i + (r - i) = r by ring])
  have hvs : ∀ r : ℤ, j + 1 ≤ r → r ≤ j + (n : ℤ) - 1 → ∀ y : V, Γ.Adj (apt t r) y →
      v • y = y := by
    intro r h1 h2 y hy
    exact aptRoot_smul_of_adj hv (i := r - j) (by omega) (by omega) (w := y)
      (by rwa [show j + (r - j) = r by ring])
  have hwf : ∀ r : ℤ, j ≤ r → r ≤ i + (n : ℤ) → (u * v * u⁻¹ * v⁻¹) • apt t r = apt t r := by
    intro r h1 h2
    have hu' : u ∈ MulAction.stabilizer D (apt t r) := huf r (by omega) (by omega)
    have hv' : v ∈ MulAction.stabilizer D (apt t r) := hvf r h1 (by omega)
    exact MulAction.mem_stabilizer_iff.mp
      (mul_mem (mul_mem (mul_mem hu' hv') (inv_mem hu')) (inv_mem hv'))
  have hws : ∀ r : ℤ, j ≤ r → r ≤ i + (n : ℤ) → ∀ y : V, Γ.Adj (apt t r) y →
      (u * v * u⁻¹ * v⁻¹) • y = y := by
    intro r h1 h2 y hy
    by_cases hr : r = i + (n : ℤ)
    · have hy' : Γ.Adj (apt t (i + (n : ℤ))) y := hr ▸ hy
      exact commutator_smul_eq_right (huf _ (by omega) le_rfl) (hvs _ (by omega) (by omega)) hy'
    · exact commutator_smul_eq (hus r (by omega) (by omega)) (hvf r h1 (by omega)) hy
  have hwj : ∀ y : V, Γ.Adj (apt t j) y → (u * v * u⁻¹ * v⁻¹) • y = y :=
    hws j le_rfl (by omega)
  have hwj1 : ∀ y : V, Γ.Adj (apt t (j + 1)) y → (u * v * u⁻¹ * v⁻¹) • y = y :=
    hws (j + 1) (by omega) (by omega)
  have hw_in : (u * v * u⁻¹ * v⁻¹) • apt t (i + (n : ℤ) + 1) = apt t (i + (n : ℤ) + 1) :=
    hws (i + (n : ℤ)) (by omega) le_rfl _ (by simpa using apt_adj ht (i + (n : ℤ)))
  have hw_jm : (u * v * u⁻¹ * v⁻¹) • apt t (j - 1) = apt t (j - 1) := by
    have h2 : Γ.Adj (apt t j) (apt t (j - 1)) := by
      have h := (apt_adj ht (j - 1)).symm
      rwa [show j - 1 + 1 = j by ring] at h
    exact hwj _ h2
  rcases eq_or_lt_of_le (by omega : i + 1 ≤ j) with hji | hji
  ·
    have hw_i : (u * v * u⁻¹ * v⁻¹) • apt t i = apt t i := by
      refine hwj (apt t i) ?_
      have h := (apt_adj ht i).symm
      rwa [← hji]
    have hwin : ∀ r : ℤ, i ≤ r → r ≤ i + (n : ℤ) + 1 →
        (u * v * u⁻¹ * v⁻¹) • apt t r = apt t r := by
      intro r h1 h2
      by_cases h3 : r ≤ j - 1
      · have hri : r = i := by omega
        rw [hri]
        exact hw_i
      · by_cases h4 : r ≤ i + (n : ℤ)
        · exact hwf r (by omega) h4
        · have hri : r = i + (n : ℤ) + 1 := by omega
          rw [hri]
          exact hw_in
    have hone : u * v * u⁻¹ * v⁻¹ = 1 := eq_one_of_fix_window ht hn hP hT hij hjn hwin hwj hwj1
    rw [hone]
    exact Subgroup.one_mem _
  ·
    have hb : i < j - 1 := by omega
    have hIoc : Set.Ioc i (j - 1) = Set.Ioo i j := by
      ext k
      simp only [Set.mem_Ioc, Set.mem_Ioo]
      omega
    have hmem : (⨆ s ∈ Set.Ioc i (j - 1), aptRoot D Γ n t s) =
        ⨆ k ∈ Set.Ioo i j, aptRoot D Γ n t k := by rw [hIoc]
    have hnb : ∀ s : ℤ, i ≤ s → s + 2 ≤ (j - 1) + 1 →
        (u * v * u⁻¹ * v⁻¹) • apt t s ≠ (u * v * u⁻¹ * v⁻¹) • apt t (s + 2) := by
      intro s h1 h2 heq
      have h2' : apt t s = apt t (s + 2) := by
        have := congrArg (fun x => (u * v * u⁻¹ * v⁻¹)⁻¹ • x) heq
        simpa using this
      exact apt_ne_two (by omega : 2 ≤ n) ht s h2'
    obtain ⟨y, hy, hyb, hyz⟩ := exists_smul_apt_path (b := j - 1) ht hn hM hb (by omega)
      (fun s => (u * v * u⁻¹ * v⁻¹) • apt t s) hw_jm
      (by rw [show j - 1 + 1 = j from by ring]; exact hwf j le_rfl (by omega))
      (fun s _ _ =>
        (GraphAction.adj_smul (Γ := Γ) (u * v * u⁻¹ * v⁻¹) (apt t s) (apt t (s+1))).mpr
          (apt_adj ht s))
      hnb
    rw [hmem] at hy
    have hyfix : ∀ r : ℤ, j - 1 ≤ r → r ≤ i + (n : ℤ) + 1 → y • apt t r = apt t r := by
      intro r h1 h2
      have hle : (⨆ s ∈ Set.Ioc i (j - 1), aptRoot D Γ n t s) ≤
          fixingSubgroup D ({apt t r} : Set V) :=
        iSup_aptRoot_le_fixing (t := t) (a := i) (b := j - 1) (r := r) ht hn hb
          (fun s hs1 hs2 => by omega) (fun s hs1 hs2 => by omega)
      rw [hmem] at hle
      exact (mem_fixingSubgroup_iff D).mp (hle hy) _ (Set.mem_singleton _)
    have hystar : ∀ r : ℤ, j ≤ r → r ≤ j + 1 → ∀ y' : V, Γ.Adj (apt t r) y' → y • y' = y' := by
      intro r h1 h2 y' hy'
      have hle : (⨆ s ∈ Set.Ioc i (j - 1), aptRoot D Γ n t s) ≤
          fixingSubgroup D (Γ.neighborSet (apt t r)) :=
        iSup_aptRoot_le_star (t := t) (a := i) (b := j - 1) (r := r) ht
          (fun s hs1 hs2 => by omega) (fun s hs1 hs2 => by omega)
      rw [hmem] at hle
      exact (mem_fixingSubgroup_iff D).mp (hle hy) _ hy'
    have hyinv : y⁻¹ • apt t (j - 1) = apt t (j - 1) := by
      calc y⁻¹ • apt t (j - 1) = y⁻¹ • (y • apt t (j - 1)) := by rw [hyb]
        _ = apt t (j - 1) := inv_smul_smul y _
    have hgwin : ∀ r : ℤ, i ≤ r → r ≤ i + (n : ℤ) + 1 →
        (y⁻¹ * (u * v * u⁻¹ * v⁻¹)) • apt t r = apt t r := by
      intro r h1 h2
      rw [mul_smul]
      by_cases h3 : r ≤ j - 1
      · rcases eq_or_lt_of_le h3 with h4 | h4
        · rw [h4, hw_jm, hyinv]
        · rw [show (u * v * u⁻¹ * v⁻¹) • apt t r = y • apt t r from
            (hyz r h1 (by omega)).symm, ← mul_smul, inv_mul_cancel, one_smul]
      · have hwr : (u * v * u⁻¹ * v⁻¹) • apt t r = apt t r := by
          by_cases h4 : r ≤ i + (n : ℤ)
          · exact hwf r (by omega) h4
          · have hri : r = i + (n : ℤ) + 1 := by omega
            rw [hri]
            exact hw_in
        rw [hwr]
        exact inv_smul_eq_iff.mpr (hyfix r (by omega) h2).symm
    have hg0 : ∀ y' : V, Γ.Adj (apt t j) y' → (y⁻¹ * (u * v * u⁻¹ * v⁻¹)) • y' = y' := by
      intro y' hy'
      rw [mul_smul, hwj y' hy']
      exact inv_smul_eq_iff.mpr (hystar j le_rfl (by omega) y' hy').symm
    have hg1 : ∀ y' : V, Γ.Adj (apt t (j + 1)) y' →
        (y⁻¹ * (u * v * u⁻¹ * v⁻¹)) • y' = y' := by
      intro y' hy'
      rw [mul_smul, hwj1 y' hy']
      exact inv_smul_eq_iff.mpr (hystar (j + 1) (by omega) (by omega) y' hy').symm
    have hgone : y⁻¹ * (u * v * u⁻¹ * v⁻¹) = 1 :=
      eq_one_of_fix_window ht hn hP hT hij hjn hgwin hg0 hg1
    have hw_eq : u * v * u⁻¹ * v⁻¹ = y := by
      have h := congrArg (fun z => y * z) hgone
      simpa [mul_assoc] using h
    rw [hw_eq]
    exact hy

end CFSG.Quasithin.Stroth
