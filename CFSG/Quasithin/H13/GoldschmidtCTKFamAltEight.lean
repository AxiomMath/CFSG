module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.CTK.AltEight

open Equiv MulAction

variable {V : Subgroup (Perm (Fin 8))}

theorem ncard_orbit_dvd (p : Fin 8) : (orbit V p).ncard ∣ Nat.card V := by
  rw [← MulAction.index_stabilizer V p]
  exact Dvd.intro_left _ (Subgroup.card_mul_index _)

theorem mem_orbit_iff' {p q : Fin 8} : q ∈ orbit V p ↔ ∃ v ∈ V, v p = q := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    exact ⟨v, hv, h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨⟨v, hv⟩, h⟩

theorem image_orbit {x : Perm (Fin 8)} (h1 : ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (h2 : ∀ v ∈ V, x⁻¹ * v * x ∈ V) (p : Fin 8) : x '' orbit V p = orbit V (x p) := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨v, hv, rfl⟩ := mem_orbit_iff'.1 ha
    exact mem_orbit_iff'.2 ⟨x * v * x⁻¹, h1 v hv, by simp⟩
  · intro hq
    obtain ⟨w, hw, rfl⟩ := mem_orbit_iff'.1 hq
    exact ⟨(x⁻¹ * w * x) p, mem_orbit_iff'.2 ⟨_, h2 w hw, rfl⟩, by simp⟩

theorem image_pow_orbit {x : Perm (Fin 8)} (h1 : ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (h2 : ∀ v ∈ V, x⁻¹ * v * x ∈ V) (p : Fin 8) (i : ℕ) :
    (x ^ i) '' orbit V p = orbit V ((x ^ i) p) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : ((x ^ (i + 1) : Perm (Fin 8)) : Fin 8 → Fin 8) = x ∘ (x ^ i : Perm (Fin 8)) := by
      ext a
      simp [pow_succ', Perm.mul_apply]
    rw [this, Set.image_comp, ih, image_orbit h1 h2]
    simp

theorem card_le_six_of_fixes (q : Fin 5 → Fin 8) (hq : Function.Injective q)
    (hfix : ∀ v ∈ V, ∀ i, v (q i) = q i) : Nat.card V ≤ 6 := by
  classical
  let P : Fin 8 → Prop := fun a => a ∉ Set.range q
  have hc : Fintype.card {a // P a} = 3 := by
    have h1 := Fintype.card_subtype_compl (fun a => a ∈ Set.range q)
    have h2 : Fintype.card (Set.range q) = 5 := by
      rw [Set.card_range_of_injective hq]
      simp
    have h3 : Fintype.card {a // a ∈ Set.range q} = 5 := h2
    simp only [Fintype.card_fin] at h1
    rw [h3] at h1
    exact h1
  let f : V → {g : Perm (Fin 8) // ∀ a, ¬ P a → g a = a} := fun v =>
    ⟨v, fun a ha => by
      obtain ⟨i, rfl⟩ := not_not.1 ha
      exact hfix v v.2 i⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (by simpa [f] using h)
  calc Nat.card V ≤ Nat.card {g : Perm (Fin 8) // ∀ a, ¬ P a → g a = a} :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card (Perm {a // P a}) := (Nat.card_congr (Perm.subtypeEquivSubtypePerm P)).symm
    _ = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, hc]
        rfl


theorem false_of_five {x : Perm (Fin 8)} (hx : orderOf x = 5) (hV : Nat.card V = 16)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (h1 : ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (h2 : ∀ v ∈ V, x⁻¹ * v * x ∈ V) : False := by
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ p := by
    by_contra h
    push Not at h
    have : x = 1 := Equiv.ext h
    rw [this, orderOf_one] at hx
    omega
  have hpow : ∀ n : ℕ, x ^ n = x ^ (n % 5) := fun n => by
    rw [← hx, pow_mod_orderOf]
  have hfix : ∀ k, 0 < k → k < 5 → (x ^ k) p = p → x p = p := by
    intro k hk0 hk5 h
    have hm : ∀ m : ℕ, (x ^ (k * m)) p = p := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [mul_add, mul_one, pow_add, Perm.mul_apply, h, ih]
    interval_cases k
    · simpa using h
    · have := hm 3
      rwa [hpow, show 2 * 3 % 5 = 1 by norm_num, pow_one] at this
    · have := hm 2
      rwa [hpow, show 3 * 2 % 5 = 1 by norm_num, pow_one] at this
    · have := hm 4
      rwa [hpow, show 4 * 4 % 5 = 1 by norm_num, pow_one] at this
  have aux : ∀ i k : ℕ, i + k < 5 → (x ^ i) p = (x ^ (i + k)) p → k = 0 := by
    intro i k hik h
    by_contra hk
    have h' : (x ^ k) p = p := by
      have : (x ^ (i + k)) p = (x ^ i) ((x ^ k) p) := by rw [pow_add, Perm.mul_apply]
      rw [this] at h
      exact ((x ^ i).injective h).symm
    exact hp (hfix k (Nat.pos_of_ne_zero hk) (by omega) h')
  let q : Fin 5 → Fin 8 := fun i => (x ^ (i : ℕ)) p
  have hq : Function.Injective q := by
    intro i j hij
    rcases le_total (i : ℕ) j with hle | hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have := aux i k (by omega) (by simpa [q, hk] using hij)
      exact Fin.ext (by omega)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have := aux j k (by omega) (by simpa [q, hk] using hij.symm)
      exact Fin.ext (by omega)
  have hkey : ∀ k, 0 < k → k < 5 → (x ^ k) p ∈ orbit V p → x p ∈ orbit V p := by
    intro k hk0 hk5 hk
    have hst : ∀ r ∈ orbit V p, (x ^ k) r ∈ orbit V p := by
      intro r hr
      have : (x ^ k) r ∈ (x ^ k) '' orbit V p := ⟨r, hr, rfl⟩
      rw [image_pow_orbit h1 h2, MulAction.orbit_eq_iff.2 hk] at this
      exact this
    have hm : ∀ m : ℕ, (x ^ (k * m)) p ∈ orbit V p := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [mul_add, mul_one, add_comm, pow_add, Perm.mul_apply]
        exact hst _ ih
    interval_cases k
    · simpa using hk
    · have := hm 3
      rwa [hpow, show 2 * 3 % 5 = 1 by norm_num, pow_one] at this
    · have := hm 2
      rwa [hpow, show 3 * 2 % 5 = 1 by norm_num, pow_one] at this
    · have := hm 4
      rwa [hpow, show 4 * 4 % 5 = 1 by norm_num, pow_one] at this
  by_cases hA : x p ∈ orbit V p
  · have hstable : ∀ i : ℕ, (x ^ i) p ∈ orbit V p := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : (x ^ (i + 1)) p = x ((x ^ i) p) := by rw [pow_succ', Perm.mul_apply]
        rw [e]
        have hmem : x ((x ^ i) p) ∈ x '' orbit V p := ⟨_, ih, rfl⟩
        rwa [image_orbit h1 h2, MulAction.orbit_eq_iff.2 hA] at hmem
    have hsub : Set.range q ⊆ orbit V p := by
      rintro _ ⟨i, rfl⟩
      exact hstable i
    have h5 : 5 ≤ (orbit V p).ncard := by
      have hr : (Set.range q).ncard = 5 := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hq, Set.ncard_univ]
        simp
      rw [← hr]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have h8 : (orbit V p).ncard ≤ 8 := by
      calc (orbit V p).ncard ≤ (Set.univ : Set (Fin 8)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
        _ = 8 := by simp
    have hd := ncard_orbit_dvd (V := V) p
    rw [hV] at hd
    have hc8 : (orbit V p).ncard = 8 := by
      generalize (orbit V p).ncard = c at h5 h8 hd
      interval_cases c <;> simp_all
    have horb : orbit V p = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [hc8]; simp) (Set.toFinite _)
    have hstab : MulAction.stabilizer V p = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have hap : (a : Perm (Fin 8)) p = p := ha
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      apply Equiv.ext
      intro r
      have hr : r ∈ orbit V p := by rw [horb]; trivial
      obtain ⟨v, hv, rfl⟩ := mem_orbit_iff'.1 hr
      have hav := hcomm a a.2 v hv
      show (a : Perm (Fin 8)) (v p) = v p
      calc (a : Perm (Fin 8)) (v p) = ((a : Perm (Fin 8)) * v) p := rfl
        _ = (v * (a : Perm (Fin 8))) p := by rw [hav]
        _ = v ((a : Perm (Fin 8)) p) := rfl
        _ = v p := by rw [hap]
    have := Subgroup.card_mul_index (MulAction.stabilizer V p)
    rw [MulAction.index_stabilizer, hc8, hstab, Subgroup.card_bot, hV] at this
    omega
  · by_cases hB : (orbit V p).ncard = 1
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hB
      have hpa : p = a := by
        have : p ∈ orbit V p := mem_orbit_self p
        rw [ha] at this
        exact this
      subst hpa
      have hfixall : ∀ v ∈ V, ∀ i : Fin 5, v (q i) = q i := by
        intro v hv i
        have hm : v (q i) ∈ orbit V (q i) := mem_orbit_iff'.2 ⟨v, hv, rfl⟩
        have e : orbit V (q i) = {q i} := by
          have := image_pow_orbit h1 h2 p (i : ℕ)
          rw [ha, Set.image_singleton] at this
          exact this.symm
        rw [e] at hm
        exact hm
      have := card_le_six_of_fixes q hq hfixall
      omega
    · have hpos : 0 < (orbit V p).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]
        exact ⟨p, mem_orbit_self p⟩
      have h2le : 2 ≤ (orbit V p).ncard := by omega
      let c : Fin 5 × ↥(orbit V p) → Fin 8 := fun ia => (x ^ (ia.1 : ℕ)) (ia.2 : Fin 8)
      have key : ∀ (i j : ℕ) (a b : Fin 8), i ≤ j → j < 5 → a ∈ orbit V p → b ∈ orbit V p →
          (x ^ i) a = (x ^ j) b → i = j := by
        intro i j a b hij hj ha hb hab
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
        have hab' : a = (x ^ k) b := by
          rw [pow_add, Perm.mul_apply] at hab
          exact (x ^ i).injective hab
        have ha2 : a ∈ orbit V ((x ^ k) p) := by
          rw [← image_pow_orbit h1 h2, hab']
          exact ⟨b, hb, rfl⟩
        obtain ⟨v, hv, hva⟩ := mem_orbit_iff'.1 ha
        obtain ⟨w, hw, hwa⟩ := mem_orbit_iff'.1 ha2
        have hkp : (x ^ k) p ∈ orbit V p :=
          mem_orbit_iff'.2 ⟨w⁻¹ * v, V.mul_mem (V.inv_mem hw) hv, by
            rw [Perm.mul_apply, hva, ← hwa]
            simp⟩
        by_contra hne
        have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
        exact hA (hkey k hk0 (by omega) hkp)
      have hc : Function.Injective c := by
        rintro ⟨i, ⟨a, ha⟩⟩ ⟨j, ⟨b, hb⟩⟩ hab
        simp only [c] at hab
        have hij : (i : ℕ) = j := by
          rcases le_total (i : ℕ) j with hle | hle
          · exact key i j a b hle j.2 ha hb hab
          · exact (key j i b a hle i.2 hb ha hab.symm).symm
        have hij' : i = j := Fin.ext hij
        subst hij'
        have : a = b := (x ^ (i : ℕ)).injective hab
        subst this
        rfl
      have := Nat.card_le_card_of_injective c hc
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin,
        Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at this
      omega


end CFSG.Quasithin.H13.CTK.AltEight
