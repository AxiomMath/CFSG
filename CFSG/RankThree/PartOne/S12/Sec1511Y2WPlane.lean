module

public import CFSG.RankThree.PartOne.S12.Sec1511Y2W
public import CFSG.RankThree.PartOne.S12.Sec1511Y2WLin

public section

namespace CFSG.RankThree.PartOne

open CFSG

open scoped IsMulCommutative

namespace Sec1511

theorem perm4_data : ∃ a₀ b₀ s₀ : Equiv.Perm (Fin 4),
    (∃ q : Equiv.Perm (Fin 4), q ^ 2 = a₀) ∧ (∃ q : Equiv.Perm (Fin 4), q ^ 2 = b₀) ∧
    (∃ q : Equiv.Perm (Fin 4), q ^ 2 = s₀) ∧ a₀ * a₀ = 1 ∧ b₀ * b₀ = 1 ∧ a₀ * b₀ = b₀ * a₀ ∧
    a₀ ≠ 1 ∧ s₀ * a₀ = b₀ * s₀ ∧ s₀ * b₀ = a₀ * (b₀ * s₀) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 1 2 * Equiv.swap 2 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem exists_klein_triple {X : Type*} [Group X] {W₀ T : Subgroup X} (hTW : T ≤ W₀)
    (e : ↥W₀ ≃* Equiv.Perm (Fin 4)) (hT : 8 < Nat.card ↥T) :
    ∃ xa xb xs : X, xa ∈ T ∧ xb ∈ T ∧ xs ∈ T ∧ xa * xa = 1 ∧ xb * xb = 1 ∧ xa * xb = xb * xa ∧
      xa ≠ 1 ∧ xs * xa = xb * xs ∧ xs * xb = xa * (xb * xs) := by
  classical
  set T₀ : Subgroup ↥W₀ := T.subgroupOf W₀ with hT₀
  have hcardT₀ : Nat.card ↥T₀ = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv
  have hW24 : Nat.card ↥W₀ = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hmul := T₀.card_mul_index
  rw [hcardT₀, hW24] at hmul
  have hidx : T₀.index = 1 ∨ T₀.index = 2 := by
    have h3 : T₀.index < 3 := by
      by_contra h
      have h' : 3 ≤ T₀.index := not_lt.1 h
      nlinarith
    have h0 : T₀.index ≠ 0 := by
      intro h
      rw [h] at hmul
      omega
    omega
  have hsq : ∀ q : ↥W₀, q ^ 2 ∈ T₀ := by
    rcases hidx with h | h
    · intro q
      rw [Subgroup.index_eq_one.1 h]
      exact Subgroup.mem_top _
    · exact Subgroup.sq_mem_of_index_two h
  have hmem : ∀ q : Equiv.Perm (Fin 4), ((e.symm (q ^ 2) : ↥W₀) : X) ∈ T := by
    intro q
    have h := hsq (e.symm q)
    rw [← map_pow e.symm q 2] at h
    exact Subgroup.mem_subgroupOf.1 h
  obtain ⟨a₀, b₀, s₀, ⟨qa, hqa⟩, ⟨qb, hqb⟩, ⟨qs, hqs⟩, ha2, hb2, hab, ha1, hsa, hsb⟩ := perm4_data
  have hmul' : ∀ x y : Equiv.Perm (Fin 4), ((e.symm x : ↥W₀) : X) * ((e.symm y : ↥W₀) : X) =
      ((e.symm (x * y) : ↥W₀) : X) := fun x y => by rw [map_mul]; rfl
  refine ⟨(e.symm a₀ : X), (e.symm b₀ : X), (e.symm s₀ : X), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hmem qa
    rw [hqa] at h
    exact h
  · have h := hmem qb
    rw [hqb] at h
    exact h
  · have h := hmem qs
    rw [hqs] at h
    exact h
  · rw [hmul', ha2, map_one]
    rfl
  · rw [hmul', hb2, map_one]
    rfl
  · rw [hmul', hmul', hab]
  · intro h
    apply ha1
    have h1 : (e.symm a₀ : ↥W₀) = 1 := Subtype.ext h
    have h2 : a₀ = 1 := by
      have := congrArg e h1
      simpa using this
    exact h2
  · rw [hmul', hmul', hsa]
  · rw [hmul', hmul', hmul', hsb]

theorem no_A4_stab_plane {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E : Type} [Group E] [Finite E]
    [IsElementaryAbelian p E] (hEcard : Nat.card E = p ^ 3) (B : Subgroup E)
    (hB : Nat.card ↥B = p ^ 2) (xa xb xs : MulAut E) (haB : xa ∈ autStab B)
    (hbB : xb ∈ autStab B) (hsB : xs ∈ autStab B) (ha2 : xa * xa = 1) (hb2 : xb * xb = 1)
    (hab : xa * xb = xb * xa) (ha1 : xa ≠ 1) (hsa : xs * xa = xb * xs)
    (hsb : xs * xb = xa * (xb * xs)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Additive E) := inferInstanceAs (Finite E)
  have : Module.Finite (ZMod p) (Additive E) := Module.Finite.of_finite
  let lin : MulAut E → (Additive E ≃ₗ[ZMod p] Additive E) := fun x =>
    { MulEquiv.toAdditive x with
      map_smul' := fun c v => ZMod.map_smul (MulEquiv.toAdditive x) c v }
  have lin_mul : ∀ x y v, lin (x * y) v = lin x (lin y v) := fun x y v => rfl
  have lin_one : ∀ v, lin 1 v = v := fun v => rfl
  have hrel : ∀ x y : MulAut E, x = y → ∀ v, lin x v = lin y v := fun x y h v => by rw [h]
  have hdim : Module.finrank (ZMod p) (Additive E) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    rw [Nat.card_zmod, show Nat.card (Additive E) = Nat.card E from rfl, hEcard] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let H : Submodule (ZMod p) (Additive E) :=
    AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup B)
  have hmemH : ∀ v : Additive E, v ∈ H ↔ Additive.toMul v ∈ B := fun v => Iff.rfl
  have hHdim : Module.finrank (ZMod p) H = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := H)
    have hc : Nat.card H = Nat.card B :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun x => Iff.rfl))
    rw [Nat.card_zmod, hc, hB] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  have hinv : ∀ x ∈ autStab B, ∀ v ∈ H, lin x v ∈ H := fun x hx v hv =>
    (hmemH _).2 ((hx _).1 ((hmemH v).1 hv))
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  refine no_invariant_plane h2 h3 hdim H hHdim (lin xa) (lin xb) (lin xs) ?_ ?_ ?_ ?_ ?_ ?_
    (hinv xa haB) (hinv xb hbB) (hinv xs hsB)
  · intro v
    rw [← lin_mul, ha2, lin_one]
  · intro v
    rw [← lin_mul, hb2, lin_one]
  · intro v
    have h := hrel _ _ hab v
    simpa only [lin_mul] using h
  · by_contra hcon
    have hfix : ∀ w, lin xa w = w := fun w => not_not.1 fun h => hcon ⟨w, h⟩
    apply ha1
    refine MulEquiv.ext fun y => ?_
    have h : Additive.ofMul (xa y) = Additive.ofMul y := hfix (Additive.ofMul y)
    exact Additive.ofMul.injective h
  · intro v
    have h := hrel _ _ hsa v
    simpa only [lin_mul] using h
  · intro v
    have h := hrel _ _ hsb v
    simpa only [lin_mul] using h

theorem kfW4Plane : KFW4Plane := by
  intro p hp hp5 E _ _ hE hEcard W₀ hW B hB
  by_contra hlt
  have hlt' : 8 < Nat.card ↥(W₀ ⊓ autStab B) := not_le.1 hlt
  obtain ⟨e⟩ := hW
  obtain ⟨xa, xb, xs, hxa, hxb, hxs, ha2, hb2, hab, ha1, hsa, hsb⟩ :=
    exists_klein_triple (inf_le_left : W₀ ⊓ autStab B ≤ W₀) e hlt'
  have := hE
  exact no_A4_stab_plane hp hp5 hEcard B hB xa xb xs hxa.2 hxb.2 hxs.2 ha2 hb2 hab ha1 hsa hsb

end Sec1511

end CFSG.RankThree.PartOne
