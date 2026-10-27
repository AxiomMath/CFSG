module

public import Certificates.Certificate7097
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Base

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.A7Fano
open CFSG.QuasithinUnique.L246.C123 (A7)
open scoped Pointwise

section Recognition

variable {A U U' : Type*} [Group A] [Group U] [Group U']

theorem exists_mulEquiv_of_stabilizer_eq (ρ : A →* MulAut U) (ρ' : A →* MulAut U')
    (h2 : ∀ u : U, u * u = 1) (h2' : ∀ u : U', u * u = 1) {u0 : U} {u0' : U'} (hu0 : u0 ≠ 1)
    (hu0' : u0' ≠ 1) (htr : ∀ u : U, u ≠ 1 → ∃ g, ρ g u0 = u)
    (htr' : ∀ u : U', u ≠ 1 → ∃ g, ρ' g u0' = u) (hstab : ∀ g : A, ρ g u0 = u0 ↔ ρ' g u0' = u0')
    (hfix : ∀ v w : U', v ≠ 1 → w ≠ 1 → v ≠ w → ∀ x : U', x ≠ 1 →
      (∀ g : A, ρ' g v = v → ρ' g w = w → ρ' g x = x) → x = v ∨ x = w ∨ x = v * w) :
    ∃ φ : U ≃* U', φ u0 = u0' ∧ ∀ (g : A) (u : U), φ (ρ g u) = ρ' g (φ u) := by
  classical
  have hkey : ∀ g h : A, ρ g u0 = ρ h u0 ↔ ρ' g u0' = ρ' h u0' := by
    intro g h
    have e1 : ρ g u0 = ρ h u0 ↔ ρ (h⁻¹ * g) u0 = u0 := by
      rw [map_mul, MulAut.mul_apply]
      constructor
      · intro hgh
        rw [hgh, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      · intro hgh
        have := congrArg (ρ h) hgh
        rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
    have e2 : ρ' g u0' = ρ' h u0' ↔ ρ' (h⁻¹ * g) u0' = u0' := by
      rw [map_mul, MulAut.mul_apply]
      constructor
      · intro hgh
        rw [hgh, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      · intro hgh
        have := congrArg (ρ' h) hgh
        rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
    rw [e1, e2, hstab]
  let f : U → U' := fun u => if hu : u = 1 then 1 else ρ' (htr u hu).choose u0'
  have hf : ∀ g : A, f (ρ g u0) = ρ' g u0' := by
    intro g
    have hne : ρ g u0 ≠ 1 := fun h => hu0 (by
      have := congrArg (ρ g⁻¹) h
      rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_one] at this)
    simp only [f, hne, ↓reduceDIte]
    exact (hkey _ _).mp (htr _ hne).choose_spec
  have hf1 : f 1 = 1 := by simp [f]
  have hfne : ∀ u : U, u ≠ 1 → f u ≠ 1 := by
    intro u hu h
    obtain ⟨g, rfl⟩ := htr u hu
    rw [hf] at h
    apply hu0'
    have := congrArg (ρ' g⁻¹) h
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_one] at this
  have hinj : Function.Injective f := by
    intro u v huv
    by_cases hu : u = 1
    · by_cases hv : v = 1
      · rw [hu, hv]
      · rw [hu, hf1] at huv
        exact absurd huv.symm (hfne v hv)
    · by_cases hv : v = 1
      · rw [hv, hf1] at huv
        exact absurd huv (hfne u hu)
      · obtain ⟨g, rfl⟩ := htr u hu
        obtain ⟨h, rfl⟩ := htr v hv
        rw [hf, hf] at huv
        exact (hkey g h).mpr huv
  have hequiv : ∀ (g : A) (u : U), f (ρ g u) = ρ' g (f u) := by
    intro g u
    by_cases hu : u = 1
    · rw [hu, map_one, hf1, map_one]
    · obtain ⟨h, rfl⟩ := htr u hu
      rw [← MulAut.mul_apply, ← map_mul, hf, hf, map_mul, MulAut.mul_apply]
  have hmul : ∀ u v : U, f (u * v) = f u * f v := by
    intro u v
    by_cases hu : u = 1
    · rw [hu, one_mul, hf1, one_mul]
    by_cases hv : v = 1
    · rw [hv, mul_one, hf1, mul_one]
    by_cases huv : u = v
    · rw [huv, h2, hf1, h2']
    have huv1 : u * v ≠ 1 := fun h => huv (by
      have : u * v = v * v := by rw [h, h2]
      exact mul_right_cancel this)
    have hfx := hfix (f u) (f v) (hfne u hu) (hfne v hv) (fun h => huv (hinj h)) (f (u * v))
      (hfne _ huv1) (by
        intro g hgu hgv
        have hu' : ρ g u = u := hinj (by rw [hequiv, hgu])
        have hv' : ρ g v = v := hinj (by rw [hequiv, hgv])
        rw [← hequiv, map_mul, hu', hv'])
    rcases hfx with h | h | h
    · exfalso
      have := hinj h
      apply hv
      calc v = u⁻¹ * (u * v) := by group
        _ = 1 := by rw [this, inv_mul_cancel]
    · exfalso
      have := hinj h
      apply hu
      calc u = (u * v) * v⁻¹ := by group
        _ = 1 := by rw [this, mul_inv_cancel]
    · exact h
  have hsurj : Function.Surjective f := by
    intro w
    by_cases hw : w = 1
    · exact ⟨1, by rw [hw, hf1]⟩
    · obtain ⟨g, rfl⟩ := htr' w hw
      exact ⟨ρ g u0, hf g⟩
  refine ⟨MulEquiv.ofBijective (MonoidHom.mk' f hmul) ⟨hinj, hsurj⟩, ?_, fun g u => hequiv g u⟩
  change f u0 = u0'
  have := hf 1
  rwa [map_one, MulAut.one_apply, map_one, MulAut.one_apply] at this

end Recognition

@[expose] def fanoStab (P : Finset (Finset (Fin 7))) : Subgroup A7 :=
  (MulAction.stabilizer (Perm (Fin 7)) P).comap (alternatingGroup (Fin 7)).subtype

theorem mem_fanoStab {P : Finset (Finset (Fin 7))} {g : A7} :
    g ∈ fanoStab P ↔ (g : Perm (Fin 7)) • P = P := Iff.rfl

@[expose] def cyc7A : A7 :=
  ⟨cyc7, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def dbl7A : A7 :=
  ⟨dbl7, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem card_fanoStab {P : Finset (Finset (Fin 7))} (hP : (stabSet P).card = 168) :
    Nat.card (fanoStab P) = 168 := by
  have e : Nat.card (fanoStab P) =
      Nat.card {g : Perm (Fin 7) // Perm.sign g = 1 ∧ g • P = P} :=
    Nat.card_congr
      { toFun := fun g => ⟨((g : A7) : Perm (Fin 7)),
          Equiv.Perm.mem_alternatingGroup.mp (g : A7).2, g.2⟩
        invFun := fun g => ⟨⟨g.1, Equiv.Perm.mem_alternatingGroup.mpr g.2.1⟩, g.2.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hP]
  rfl

theorem card_fanoStab_fano1 : Nat.card (fanoStab fano1) = 168 :=
  card_fanoStab Certificates.certificate7097.2.1

theorem card_fanoStab_fano2 : Nat.card (fanoStab fano2) = 168 :=
  card_fanoStab Certificates.certificate7097.2.2.1

theorem reps1_facts :
    (∀ i, Perm.sign (reps1 i) = 1) ∧ (∀ i j, i ≠ j → ((reps1 i)⁻¹ * reps1 j) • fano1 ≠ fano1) ∧
      ∀ j : Fin 15, j ≠ 0 → fixCount fano1 reps1 j ≤ 3 :=
  ⟨Certificates.certificate7097.2.2.2.1, Certificates.certificate7097.2.2.2.2.1,
    Certificates.certificate7097.2.2.2.2.2.1⟩

theorem normCount_eq {σ : Perm (Fin 7)}
    (hσ : σ.cycleType = {3}) : normCount σ = 72 :=
  Certificates.certificate7097.2.2.2.2.2.2 σ hσ

theorem le_or_le_of_subset_union {X : Type*} [Group X] {S S₁ S₂ : Subgroup X}
    (h : ∀ g ∈ S, g ∈ S₁ ∨ g ∈ S₂) : S ≤ S₁ ∨ S ≤ S₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨a, haS, ha1⟩ := Set.not_subset.mp h1
  obtain ⟨b, hbS, hb2⟩ := Set.not_subset.mp h2
  have ha2 : a ∈ S₂ := (h a haS).resolve_left ha1
  have hb1 : b ∈ S₁ := (h b hbS).resolve_right hb2
  rcases h (a * b) (S.mul_mem haS hbS) with hab | hab
  · apply ha1
    have := S₁.mul_mem hab (S₁.inv_mem hb1)
    rwa [mul_inv_cancel_right] at this
  · apply hb2
    have := S₂.mul_mem (S₂.inv_mem ha2) hab
    rwa [inv_mul_cancel_left] at this

theorem eq_fanoStab_of_card {S : Subgroup A7}
    (hS : Nat.card S = 168) (hc : cyc7A ∈ S) (hd : dbl7A ∈ S) :
    S = fanoStab fano1 ∨ S = fanoStab fano2 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsub : ∀ g ∈ S, g ∈ fanoStab fano1 ∨ g ∈ fanoStab fano2 := by
    intro g hg
    rcases Certificates.certificate7097.1 (g : Perm (Fin 7))
      (Equiv.Perm.mem_alternatingGroup.mp g.2) with h1 | h2 | ⟨i, j, hw5, hw1⟩
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso
      set w : A7 := g * cyc7A ^ (i : ℕ) * dbl7A ^ (j : ℕ) with hw
      have hwS : w ∈ S := S.mul_mem (S.mul_mem hg (S.pow_mem hc _)) (S.pow_mem hd _)
      have hwo : orderOf w = 5 := by
        refine orderOf_eq_prime (Subtype.ext ?_) (fun h => hw1 ?_)
        · simpa [hw, cyc7A, dbl7A] using hw5
        · have := congrArg Subtype.val h
          simpa [hw, cyc7A, dbl7A] using this
      have hdvd := Subgroup.orderOf_dvd_natCard S hwS
      rw [hwo, hS] at hdvd
      norm_num at hdvd
  rcases le_or_le_of_subset_union hsub with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [card_fanoStab_fano1, hS]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [card_fanoStab_fano2, hS]))

section Stab

variable {A U : Type*} [Group A] [Group U]

@[expose] def vecStab (ρ : A →* MulAut U) (u : U) : Subgroup A where
  carrier := {g | ρ g u = u}
  mul_mem' {a b} ha hb := by
    change ρ (a * b) u = u
    rw [map_mul, MulAut.mul_apply]
    change ρ b u = u at hb
    change ρ a u = u at ha
    rw [hb, ha]
  one_mem' := by
    change ρ 1 u = u
    rw [map_one, MulAut.one_apply]
  inv_mem' {a} ha := by
    change ρ a u = u at ha
    change ρ a⁻¹ u = u
    calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [ha]
      _ = u := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem mem_vecStab {ρ : A →* MulAut U} {u : U} {g : A} : g ∈ vecStab ρ u ↔ ρ g u = u := Iff.rfl

theorem inv_apply_apply (ρ : A →* MulAut U) (g : A) (u : U) : ρ g⁻¹ (ρ g u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem apply_inv_apply (ρ : A →* MulAut U) (g : A) (u : U) : ρ g (ρ g⁻¹ u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem card_vecStab_mul [Finite A] [Finite U] (ρ : A →* MulAut U) (hU : Nat.card U = 16)
    {u0 : U} (hu0 : u0 ≠ 1) (htr : ∀ u : U, u ≠ 1 → ∃ g, ρ g u0 = u) :
    Nat.card (vecStab ρ u0) * 15 = Nat.card A := by
  classical
  let _ : MulAction A U := MulAction.compHom U ρ
  have hst : MulAction.stabilizer A u0 = vecStab ρ u0 := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_vecStab]
    rfl
  have horb : MulAction.orbit A u0 = {u | u ≠ 1} := by
    ext u
    constructor
    · rintro ⟨g, rfl⟩
      intro h
      apply hu0
      have := congrArg (ρ g⁻¹) h
      change ρ g⁻¹ (ρ g u0) = ρ g⁻¹ 1 at this
      rwa [inv_apply_apply, map_one] at this
    · intro hu
      obtain ⟨g, hg⟩ := htr u hu
      exact ⟨g, hg⟩
  have hidx := MulAction.index_stabilizer A u0
  rw [horb, hst] at hidx
  have h15 : ({u | u ≠ 1} : Set U).ncard = 15 := by
    have h1 : ({u | u ≠ 1} : Set U) = (({1} : Set U))ᶜ := by
      ext u
      simp
    rw [h1, Set.ncard_compl, Set.ncard_singleton, hU]
  rw [h15] at hidx
  rw [← hidx]
  exact Subgroup.card_mul_index _

end Stab

section A7Module

variable {U : Type*} [Group U] [Finite U]

theorem dbl7A_conj : dbl7A⁻¹ * cyc7A * dbl7A = cyc7A ^ 4 :=
  Subtype.ext (show dbl7⁻¹ * cyc7 * dbl7 = cyc7 ^ 4 by decide)

theorem exists_fixed_cyc7 (ρ : A7 →* MulAut U) (hinj : Function.Injective ρ)
    (hU : Nat.card U = 16) :
    ∃ u0 : U, u0 ≠ 1 ∧ ρ cyc7A u0 = u0 ∧ ρ dbl7A u0 = u0 ∧
      ∀ u : U, ρ cyc7A u = u → u = 1 ∨ u = u0 := by
  classical
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let C : Subgroup U :=
    { carrier := {u | ρ cyc7A u = u}
      mul_mem' := fun {a b} ha hb => by
        change ρ cyc7A (a * b) = a * b
        rw [map_mul]
        change ρ cyc7A a = a at ha
        change ρ cyc7A b = b at hb
        rw [ha, hb]
      one_mem' := map_one _
      inv_mem' := fun {a} ha => by
        change ρ cyc7A a = a at ha
        change ρ cyc7A a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hC : ∀ u : U, u ∈ C ↔ ρ cyc7A u = u := fun u => Iff.rfl
  have hc7 : orderOf cyc7A = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by decide) (by decide)
  let _ : MulAction (Subgroup.zpowers cyc7A) U :=
    MulAction.compHom U (ρ.comp (Subgroup.zpowers cyc7A).subtype)
  have hP : IsPGroup 7 (Subgroup.zpowers cyc7A) := by
    have : Nat.card (Subgroup.zpowers cyc7A) = 7 ^ 1 := by rw [Nat.card_zpowers, hc7, pow_one]
    exact IsPGroup.of_card this
  have hmod := hP.card_modEq_card_fixedPoints U
  have hfix : MulAction.fixedPoints (Subgroup.zpowers cyc7A) U = (C : Set U) := by
    ext u
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, hC]
    constructor
    · intro h
      exact h ⟨cyc7A, Subgroup.mem_zpowers _⟩
    · intro h g
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      change ρ (cyc7A ^ k) u = u
      have hf : u ∈ MulAction.fixedBy U (ρ cyc7A) := h
      have := MulAction.mem_fixedBy_zpow hf k
      rw [MulAction.mem_fixedBy, MulAut.smul_def] at this
      rw [map_zpow]
      exact this
  rw [hfix, Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hmod
  have hCcard : Nat.card C ∣ 16 := hU ▸ Subgroup.card_subgroup_dvd_card C
  have hC2 : Nat.card C = 2 := by
    have hmod' : 16 % 7 = Nat.card C % 7 := by rw [← hU]; exact hmod
    have hle : Nat.card C ≤ 16 := Nat.le_of_dvd (by norm_num) hCcard
    have h16 : Nat.card C ≠ 16 := by
      intro h16
      have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [h16, hU])
      have h1 : ρ cyc7A = 1 := by
        ext u
        have : u ∈ C := htop ▸ Subgroup.mem_top u
        exact this
      have := hinj (h1.trans (map_one ρ).symm)
      exact absurd this (by decide)
    interval_cases h : Nat.card C <;> omega
  obtain ⟨⟨u0, hu0C⟩, hu01, hu0u⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC2
  have hu0 : u0 ≠ 1 := fun h => hu01 (Subtype.ext h)
  have honly : ∀ u : U, ρ cyc7A u = u → u = 1 ∨ u = u0 := by
    intro u hu
    by_cases h1 : u = 1
    · exact Or.inl h1
    · right
      have := hu0u ⟨u, hu⟩ (fun h => h1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  refine ⟨u0, hu0, hu0C, ?_, honly⟩
  have hc4 : ρ (cyc7A ^ 4) u0 = u0 := by
    rw [map_pow]
    have : ∀ k : ℕ, (ρ cyc7A ^ k) u0 = u0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hu0C, ih]
    exact this 4
  have hd : ρ cyc7A (ρ dbl7A u0) = ρ dbl7A u0 := by
    have e : cyc7A * dbl7A = dbl7A * cyc7A ^ 4 := by
      rw [← dbl7A_conj]
      group
    rw [← MulAut.mul_apply, ← map_mul, e, map_mul, MulAut.mul_apply, hc4]
  rcases honly _ hd with h | h
  · exfalso
    apply hu0
    have := congrArg (ρ dbl7A⁻¹) h
    rwa [inv_apply_apply, map_one] at this
  · exact h

theorem vecStab_eq_fanoStab (ρ : A7 →* MulAut U)
    (hU : Nat.card U = 16) {u0 : U} (hu0 : u0 ≠ 1) (hc : ρ cyc7A u0 = u0) (hd : ρ dbl7A u0 = u0)
    (htr : ∀ u : U, u ≠ 1 → ∃ g, ρ g u0 = u) :
    vecStab ρ u0 = fanoStab fano1 ∨ vecStab ρ u0 = fanoStab fano2 := by
  have h := card_vecStab_mul ρ hU hu0 htr
  rw [CFSG.QuasithinUnique.L246.C123.card_A7] at h
  exact eq_fanoStab_of_card (by omega) hc hd

end A7Module

section Third

variable {U : Type*} [Group U] [Finite U]

theorem mem_of_fixed_of_stab_eq (ρ : A7 →* MulAut U) (hU : Nat.card U = 16)
    (h2 : ∀ u : U, u * u = 1) {u0 : U} (hu0 : u0 ≠ 1) (htr : ∀ u : U, u ≠ 1 → ∃ g, ρ g u0 = u)
    {P : Finset (Finset (Fin 7))} {r : Fin 15 → Perm (Fin 7)} (hr : ∀ i, Perm.sign (r i) = 1)
    (hr0 : r 0 = 1) (hrinj : ∀ i j, i ≠ j → ((r i)⁻¹ * r j) • P ≠ P)
    (hcount : ∀ j : Fin 15, j ≠ 0 → fixCount P r j ≤ 3)
    (hstab : ∀ g : A7, ρ g u0 = u0 ↔ (g : Perm (Fin 7)) • P = P) :
    ∀ v w : U, v ≠ 1 → w ≠ 1 → v ≠ w → ∀ x : U, x ≠ 1 →
      (∀ g : A7, ρ g v = v → ρ g w = w → ρ g x = x) → x = v ∨ x = w ∨ x = v * w := by
  classical
  let rA : Fin 15 → A7 := fun i => ⟨r i, Equiv.Perm.mem_alternatingGroup.mpr (hr i)⟩
  let e : Fin 15 → U := fun i => ρ (rA i) u0
  have he0 : e 0 = u0 := by
    have : rA 0 = 1 := Subtype.ext hr0
    simp only [e, this, map_one, MulAut.one_apply]
  have hfixe : ∀ (g : A7) (j : Fin 15), ρ g (e j) = e j ↔
      ((r j)⁻¹ * (g : Perm (Fin 7)) * r j) • P = P := by
    intro g j
    have e1 : ρ g (e j) = e j ↔ ρ ((rA j)⁻¹ * g * rA j) u0 = u0 := by
      simp only [e, map_mul, MulAut.mul_apply]
      constructor
      · intro h
        rw [h, inv_apply_apply]
      · intro h
        have := congrArg (ρ (rA j)) h
        rwa [apply_inv_apply] at this
    rw [e1, hstab]
    rfl
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    apply hrinj i j hne
    have h1 : ρ ((rA i)⁻¹ * rA j) u0 = u0 := by
      rw [map_mul, MulAut.mul_apply]
      change ρ (rA i)⁻¹ (e j) = u0
      rw [← hij]
      exact inv_apply_apply ρ (rA i) u0
    have h2 := (hstab _).mp h1
    simpa [rA] using h2
  have hne1 : ∀ i, e i ≠ 1 := by
    intro i h
    apply hu0
    have := congrArg (ρ (rA i)⁻¹) h
    rwa [inv_apply_apply, map_one] at this
  have := Fintype.ofFinite U
  have hcover : ∀ u : U, u ≠ 1 → ∃ i, e i = u := by
    have hcard : Fintype.card {u : U // u ≠ 1} = 15 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hU]
    let f : Fin 15 → {u : U // u ≠ 1} := fun i => ⟨e i, hne1 i⟩
    have hf : Function.Injective f := fun i j h => hinj (congrArg Subtype.val h)
    have hbij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by rw [hcard]; simp⟩
    intro u hu
    obtain ⟨i, hi⟩ := hbij.2 ⟨u, hu⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hmemI : ∀ j : Fin 15, ∀ i : Fin 15, (∀ g : A7, ρ g u0 = u0 → ρ g (e j) = e j →
      ρ g (e i) = e i) →
      i ∈ Finset.univ.filter fun i : Fin 15 =>
        ∀ g ∈ (stabSet P).filter fun g => ((r j)⁻¹ * g * r j) • P = P,
          ((r i)⁻¹ * g * r i) • P = P := by
    intro j i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun g hg => ?_⟩
    rw [Finset.mem_filter] at hg
    obtain ⟨hgS, hgj⟩ := hg
    simp only [stabSet, Finset.mem_filter, Finset.mem_univ, true_and] at hgS
    let gA : A7 := ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hgS.1⟩
    exact (hfixe gA i).mp (hi gA ((hstab gA).mpr hgS.2) ((hfixe gA j).mpr hgj))
  intro v w hv hw hvw x hx hfx
  obtain ⟨g, rfl⟩ := htr v hv
  set w' := ρ g⁻¹ w with hw'
  set x' := ρ g⁻¹ x with hx'
  have hww : w = ρ g w' := by rw [hw', apply_inv_apply]
  have hxx : x = ρ g x' := by rw [hx', apply_inv_apply]
  have hw'1 : w' ≠ 1 := fun h => hw (by rw [hww, h, map_one])
  have hx'1 : x' ≠ 1 := fun h => hx (by rw [hxx, h, map_one])
  have hw'u : w' ≠ u0 := fun h => hvw (by rw [hww, h])
  have hfx' : ∀ h : A7, ρ h u0 = u0 → ρ h w' = w' → ρ h x' = x' := by
    intro h hhu hhw
    have hc := hfx (g * h * g⁻¹)
      (by rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, inv_apply_apply, hhu])
      (by rw [hww, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, inv_apply_apply, hhw])
    rw [hxx, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, inv_apply_apply] at hc
    have := congrArg (ρ g⁻¹) hc
    rwa [inv_apply_apply, inv_apply_apply] at this
  obtain ⟨j, hj⟩ := hcover w' hw'1
  have hj0 : j ≠ 0 := fun h => hw'u (by rw [← hj, h, he0])
  have huw1 : u0 * w' ≠ 1 := fun h => hw'u (by
    have := congrArg (u0 * ·) h
    simp only [← mul_assoc, h2, one_mul, mul_one] at this
    exact this)
  obtain ⟨k, hk⟩ := hcover (u0 * w') huw1
  obtain ⟨i, hi⟩ := hcover x' hx'1
  set Fj := Finset.univ.filter fun i : Fin 15 =>
    ∀ g ∈ (stabSet P).filter fun g => ((r j)⁻¹ * g * r j) • P = P,
      ((r i)⁻¹ * g * r i) • P = P with hFj
  have hFcard : Fj.card ≤ 3 := hcount j hj0
  have h0F : (0 : Fin 15) ∈ Fj := hmemI j 0 (fun h hu _ => by rw [he0]; exact hu)
  have hjF : j ∈ Fj := hmemI j j (fun h _ hw => hw)
  have hkF : k ∈ Fj := hmemI j k (fun h hu hw => by
    rw [hk, map_mul, hu, ← hj, hw])
  have hiF : i ∈ Fj := hmemI j i (fun h hu hw => by
    rw [hi]
    exact hfx' h hu (by rw [← hj]; exact hw))
  have h0k : (0 : Fin 15) ≠ k := fun h => by
    apply hw'1
    have := hk
    rw [← h, he0] at this
    have e2 := congrArg (u0⁻¹ * ·) this
    simp only [inv_mul_cancel_left] at e2
    rw [← e2, inv_mul_cancel]
  have hjk : j ≠ k := fun h => by
    apply hu0
    have := hk
    rw [← h, hj] at this
    have e2 := congrArg (· * w'⁻¹) this
    simp only [mul_inv_cancel_right, mul_inv_cancel] at e2
    exact e2.symm
  have hi3 : i = 0 ∨ i = j ∨ i = k := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hi0, hij, hik⟩ := hcon
    have h3 : ({0, j, k} : Finset (Fin 15)).card = 3 :=
      Finset.card_eq_three.mpr ⟨0, j, k, hj0.symm, h0k, hjk, rfl⟩
    have hi' : i ∉ ({0, j, k} : Finset (Fin 15)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hi0, hij, hik⟩
    have h4 : (insert i ({0, j, k} : Finset (Fin 15))).card = 4 := by
      rw [Finset.card_insert_of_notMem hi', h3]
    have hsub : insert i ({0, j, k} : Finset (Fin 15)) ⊆ Fj := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact hiF
      · exact h0F
      · exact hjF
      · exact hkF
    have := Finset.card_le_card hsub
    omega
  rcases hi3 with rfl | rfl | rfl
  · left
    rw [hxx, ← hi, he0]
  · right; left
    rw [hxx, ← hi, hj, ← hww]
  · right; right
    rw [hxx, ← hi, hk, map_mul, ← hww]

end Third

end CFSG.Quasithin.H13
