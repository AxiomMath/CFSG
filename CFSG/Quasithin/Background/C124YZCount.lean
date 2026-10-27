module

public import CFSG.Quasithin.Background.C124YZModel

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Quasithin Equiv Equiv.Perm

section Count

variable {m : ℕ} (B : Subgroup (Perm (Fin m)))

abbrev OrbQ : Type := MulAction.orbitRel.Quotient ↥B (Fin m)

noncomputable instance instFintypeOrbQ : Fintype (OrbQ B) := Fintype.ofFinite _

theorem nat_le_two_pow_pred {n : ℕ} (h : 1 ≤ n) : n ≤ 2 ^ (n - 1) := by
  have := Nat.lt_two_pow_self (n := n - 1)
  omega

theorem lt_two_pow_pred {n : ℕ} (h : 3 ≤ n) : n < 2 ^ (n - 1) := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : k + 1 - 1 = (k - 1) + 1 := by omega
    rw [this, pow_succ]
    omega

theorem mk_out_orbit (c : OrbQ B) : (Quotient.out c : Fin m) ∈ c.orbit :=
  MulAction.orbitRel.Quotient.mem_orbit.2 (Quotient.out_eq' c)

theorem exists_smul_out (z : Fin m) :
    ∃ a : ↥B, (a : Perm (Fin m)) z = Quotient.out (Quotient.mk'' z : OrbQ B) := by
  have h : (Quotient.mk'' (Quotient.out (Quotient.mk'' z : OrbQ B)) : OrbQ B) = Quotient.mk'' z :=
    Quotient.out_eq' _
  have h2 := Quotient.eq''.1 h
  rw [MulAction.orbitRel_apply] at h2
  obtain ⟨a, ha⟩ := h2
  exact ⟨a, by simpa [Subgroup.smul_def, Perm.smul_def] using ha⟩

theorem card_le_prod_orbit (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ ∏ c : OrbQ B, Nat.card c.orbit := by
  classical
  let ψ : ↥B → ((c : OrbQ B) → ↥c.orbit) := fun b c =>
    ⟨(b : Perm (Fin m)) (Quotient.out c),
      MulAction.orbitRel.Quotient.mapsTo_smul_orbit b c (mk_out_orbit B c)⟩
  have hψ : Function.Injective ψ := by
    intro b b' h
    have hb : ∀ c, (b : Perm (Fin m)) (Quotient.out c) = (b' : Perm (Fin m)) (Quotient.out c) :=
      fun c => congrArg Subtype.val (congrFun h c)
    apply Subtype.ext
    refine Equiv.ext fun z => ?_
    obtain ⟨a, ha⟩ := exists_smul_out B z
    have h1 := hb (Quotient.mk'' z)
    rw [← ha] at h1
    have e1 : (b : Perm (Fin m)) ((a : Perm (Fin m)) z) =
        (a : Perm (Fin m)) ((b : Perm (Fin m)) z) := by
      have := hcomm b b.2 a a.2
      exact congrArg (fun f : Perm (Fin m) => f z) this
    have e2 : (b' : Perm (Fin m)) ((a : Perm (Fin m)) z) =
        (a : Perm (Fin m)) ((b' : Perm (Fin m)) z) := by
      have := hcomm b' b'.2 a a.2
      exact congrArg (fun f : Perm (Fin m) => f z) this
    rw [e1, e2] at h1
    exact (a : Perm (Fin m)).injective h1
  calc Nat.card B ≤ Nat.card ((c : OrbQ B) → ↥c.orbit) := Nat.card_le_card_of_injective ψ hψ
    _ = ∏ c : OrbQ B, Nat.card c.orbit := Nat.card_pi

theorem sum_card_orbit : ∑ c : OrbQ B, Nat.card c.orbit = m := by
  have h := Nat.card_congr (MulAction.selfEquivSigmaOrbits' ↥B (Fin m))
  rw [Nat.card_sigma] at h
  simpa using h.symm

theorem one_le_card_orbit (c : OrbQ B) : 1 ≤ Nat.card c.orbit := by
  have := c.nonempty_orbit.to_subtype
  exact Nat.card_pos

theorem prod_card_orbit_le :
    ∏ c : OrbQ B, Nat.card c.orbit ≤ 2 ^ (m - Fintype.card (OrbQ B)) := by
  calc ∏ c : OrbQ B, Nat.card c.orbit
      ≤ ∏ c : OrbQ B, 2 ^ (Nat.card c.orbit - 1) :=
        Finset.prod_le_prod fun c _ => nat_le_two_pow_pred (one_le_card_orbit B c)
    _ = 2 ^ ∑ c : OrbQ B, (Nat.card c.orbit - 1) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = 2 ^ (m - Fintype.card (OrbQ B)) := by
      congr 1
      have h := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (OrbQ B)))
        (f := fun c => Nat.card c.orbit) (g := fun _ => 1) (fun c _ => one_le_card_orbit B c)
      rw [h, sum_card_orbit]
      simp

theorem toAdd_eq_of_mem_fixAct {x : ↥(G6.coreMod m)} (hx : x ∈ fixAct (G6.coreAct m) B)
    (b : ↥B) (i : Fin m) :
    Multiplicative.toAdd (x : G6.PermMod m) ((b : Perm (Fin m)) i) =
      Multiplicative.toAdd (x : G6.PermMod m) i := by
  have h := congrArg (fun y : ↥(G6.coreMod m) =>
    Multiplicative.toAdd (y : G6.PermMod m) ((b : Perm (Fin m)) i)) (hx b b.2)
  simp only [G6.coreAct_coe, G6.permAct_apply] at h
  rw [show (b : Perm (Fin m))⁻¹ ((b : Perm (Fin m)) i) = i from
    (b : Perm (Fin m)).symm_apply_apply i] at h
  exact h.symm

theorem card_fixAct_core_le (hB : IsPGroup 2 B) (hodd : Odd m) :
    Nat.card (fixAct (G6.coreAct m) B) ≤ 2 ^ (Fintype.card (OrbQ B) - 1) := by
  classical
  obtain ⟨p, hp⟩ := exists_fixed_of_odd hB (by simpa using hodd)
  set c₀ : OrbQ B := Quotient.mk'' p with hc₀
  let Φ : fixAct (G6.coreAct m) B → ({c : OrbQ B // c ≠ c₀} → ZMod 2) :=
    fun x c => Multiplicative.toAdd (x.1 : G6.PermMod m) (Quotient.out c.1)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have hoff : ∀ i, i ≠ p → Multiplicative.toAdd (x.1 : G6.PermMod m) i =
        Multiplicative.toAdd (y.1 : G6.PermMod m) i := by
      intro i hi
      have hc : (Quotient.mk'' i : OrbQ B) ≠ c₀ := by
        intro h
        have h2 := Quotient.eq''.1 h
        rw [MulAction.orbitRel_apply] at h2
        obtain ⟨a, ha⟩ := h2
        apply hi
        rw [← ha]
        simpa [Subgroup.smul_def, Perm.smul_def] using hp a a.2
      obtain ⟨a, ha⟩ := exists_smul_out B i
      have h1 := toAdd_eq_of_mem_fixAct B x.2 a i
      have h2 := toAdd_eq_of_mem_fixAct B y.2 a i
      rw [ha] at h1 h2
      have h3 := congrFun hxy ⟨Quotient.mk'' i, hc⟩
      simp only [Φ] at h3
      rw [h1.symm, h2.symm]
      exact h3
    refine Subtype.ext (Subtype.ext (Multiplicative.toAdd.injective (funext fun i => ?_)))
    by_cases hi : i = p
    · subst hi
      have hx0 := G6.mem_coreMod.1 x.1.2
      have hy0 := G6.mem_coreMod.1 y.1.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hx0 hy0
      have hs : ∑ j ∈ Finset.univ.erase i, Multiplicative.toAdd (x.1 : G6.PermMod m) j =
          ∑ j ∈ Finset.univ.erase i, Multiplicative.toAdd (y.1 : G6.PermMod m) j :=
        Finset.sum_congr rfl fun j hj => hoff j (Finset.ne_of_mem_erase hj)
      rw [hs] at hx0
      exact add_right_cancel (hx0.trans hy0.symm)
    · exact hoff i hi
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, Nat.card_zmod] at hcard
  have hr : Nat.card {c : OrbQ B // c ≠ c₀} = Fintype.card (OrbQ B) - 1 := by
    rw [Nat.card_eq_fintype_card]
    have := Fintype.card_subtype_compl (fun c : OrbQ B => c = c₀)
    rw [Fintype.card_subtype_eq] at this
    exact this
  rw [hr] at hcard
  exact hcard

theorem card_coreMod {n : ℕ} (hn : 1 ≤ n) : Nat.card (G6.coreMod n) = 2 ^ (n - 1) := by
  let coordSum : G6.PermMod n →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
      map_one' := by simp
      map_mul' := fun x y => by simp [Finset.sum_add_distrib] }
  have hker : coordSum.ker = G6.coreMod n := by
    ext x
    rw [MonoidHom.mem_ker, G6.mem_coreMod]
    exact ofAdd_eq_one
  have hsurj : Function.Surjective coordSum := by
    intro c
    refine ⟨Multiplicative.ofAdd (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c)), ?_⟩
    change Multiplicative.ofAdd (∑ i, (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c) :
      Fin n → ZMod 2) i) = c
    rw [Finset.sum_pi_single']
    simp only [Finset.mem_univ, ↓reduceIte, ofAdd_toAdd]
  have h := Subgroup.card_ker_mul_card_range coordSum
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker] at h
  have h1 : Nat.card (G6.PermMod n) = 2 ^ n := by
    change Nat.card (Fin n → ZMod 2) = 2 ^ n
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  rw [h1, h2] at h
  have h3 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem isPGroup_two_of_sq {B : Subgroup (Perm (Fin m))} (hB : ∀ b ∈ B, b * b = 1) :
    IsPGroup 2 B := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hB g g.2)⟩

theorem one_le_card_orbQ (hodd : Odd m) : 1 ≤ Fintype.card (OrbQ B) :=
  Fintype.card_pos_iff.2 ⟨Quotient.mk'' ⟨0, hodd.pos⟩⟩

theorem card_orbQ_le : Fintype.card (OrbQ B) ≤ m := by
  calc Fintype.card (OrbQ B) = ∑ _c : OrbQ B, 1 := by simp
    _ ≤ ∑ c : OrbQ B, Nat.card c.orbit := Finset.sum_le_sum fun c _ => one_le_card_orbit B c
    _ = m := sum_card_orbit B

theorem card_mul_card_fixAct_le (hsq : ∀ b ∈ B, b * b = 1)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hodd : Odd m) :
    Nat.card B * Nat.card (fixAct (G6.coreAct m) B) ≤ Nat.card (G6.coreMod m) := by
  have h1 := card_le_prod_orbit B hcomm
  have h2 := prod_card_orbit_le B
  have h3 := card_fixAct_core_le B (isPGroup_two_of_sq hsq) hodd
  have h4 := one_le_card_orbQ B hodd
  have h5 := card_orbQ_le B
  rw [card_coreMod hodd.pos]
  calc Nat.card B * Nat.card (fixAct (G6.coreAct m) B)
      ≤ 2 ^ (m - Fintype.card (OrbQ B)) * 2 ^ (Fintype.card (OrbQ B) - 1) :=
        Nat.mul_le_mul (h1.trans h2) h3
    _ = 2 ^ (m - 1) := by
      rw [← pow_add]
      congr 1
      omega

end Count

end CFSG.Quasithin.C124.YZ
