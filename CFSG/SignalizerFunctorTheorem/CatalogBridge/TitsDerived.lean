module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsHeis

public noncomputable section

open CFSG.LieType.Simplicity.TitsBits CFSG.SectionRank.TitsOrder CFSG.LieType.Ree
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Simplicity
open CFSG.SectionRank.TitsGen
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def letterCount (j : ℕ) (w : List ℤ) : ℕ :=
  (w.map fun l => if l.natAbs = j then 1 else 0).sum

theorem letterCount_cons (j : ℕ) (l : ℤ) (w : List ℤ) :
    letterCount j (l :: w) = (if l.natAbs = j then 1 else 0) + letterCount j w := by
  simp [letterCount]

theorem letterCount_nil (j : ℕ) : letterCount j [] = 0 := rfl

theorem comm_pow_aux {A : Type*} [CommMonoid A] (x y z : A) (p q r p' q' r' : ℕ) :
    x ^ p * y ^ q * z ^ r * (x ^ p' * y ^ q' * z ^ r') =
      x ^ (p + p') * y ^ (q + q') * z ^ (r + r') := by
  rw [pow_add, pow_add, pow_add]
  simp only [mul_assoc, mul_left_comm]

theorem heisA_even : ∀ j < 4, Even (letterCount 2 (heisA.getD j [])) ∧
    Even (letterCount 3 (heisA.getD j [])) ∧ Even (letterCount 4 (heisA.getD j [])) := by
  decide

theorem heisX_even : ∀ i < 16, Even (letterCount 2 (heisX.getD i [])) ∧
    Even (letterCount 3 (heisX.getD i [])) ∧ Even (letterCount 4 (heisX.getD i [])) := by
  decide


section Squares

variable {K : Type} [Field K] [CharP K ReeTag.F4.prime]

theorem titsZ1_mul_self : titsZ1 K * titsZ1 K = 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [titsZ1_eq_evalG, ← evalG_append, ← evalG_nil, evalG_eq_evalG_iff]
  decide +kernel

theorem titsZ2_mul_self : titsZ2 K * titsZ2 K = 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [titsZ2_eq_evalG, ← evalG_append, ← evalG_nil, evalG_eq_evalG_iff]
  decide +kernel

end Squares

section Parity

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem gWordG_mem_commutator
    (h0 : g0 K ∈ commutator (reeFixed ReeTag.F4 K 0))
    (h1 : g1 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0))
    (h2 : z1 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0))
    (h3 : z2 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0))
    (w : List ℤ) (hw : ∀ l ∈ w, GoodLetter l) (e2 : Even (letterCount 2 w))
    (e3 : Even (letterCount 3 w)) (e4 : Even (letterCount 4 w)) :
    gWordG K w ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  have hker : ∀ x : reeFixed ReeTag.F4 K 0, x ∈ commutator (reeFixed ReeTag.F4 K 0) ↔
      (Abelianization.of x) = 1 := fun x => by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of]
  have ha : Abelianization.of (g0 K) = 1 := (hker _).1 h0
  have hb2 : Abelianization.of (g1 K) ^ 2 = 1 := by rw [← map_pow]; exact (hker _).1 h1
  have hc2 : Abelianization.of (z1 K) ^ 2 = 1 := by rw [← map_pow]; exact (hker _).1 h2
  have hd2 : Abelianization.of (z2 K) ^ 2 = 1 := by rw [← map_pow]; exact (hker _).1 h3
  have hbi : (Abelianization.of (g1 K))⁻¹ = Abelianization.of (g1 K) :=
    inv_eq_of_mul_eq_one_right (by rwa [← sq])
  have hci : (Abelianization.of (z1 K))⁻¹ = Abelianization.of (z1 K) :=
    inv_eq_of_mul_eq_one_right (by rwa [← sq])
  have hdi : (Abelianization.of (z2 K))⁻¹ = Abelianization.of (z2 K) :=
    inv_eq_of_mul_eq_one_right (by rwa [← sq])
  have hlet : ∀ l : ℤ, GoodLetter l → Abelianization.of (gEltG K l) =
      Abelianization.of (g1 K) ^ (if l.natAbs = 2 then 1 else 0) *
        Abelianization.of (z1 K) ^ (if l.natAbs = 3 then 1 else 0) *
        Abelianization.of (z2 K) ^ (if l.natAbs = 4 then 1 else 0) := by
    intro l ⟨hl0, hl4⟩
    have : l = -4 ∨ l = -3 ∨ l = -2 ∨ l = -1 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gEltG, genG, ha, hbi, hci, hdi]
  have hword : ∀ w : List ℤ, (∀ l ∈ w, GoodLetter l) → Abelianization.of (gWordG K w) =
      Abelianization.of (g1 K) ^ letterCount 2 w * Abelianization.of (z1 K) ^ letterCount 3 w *
        Abelianization.of (z2 K) ^ letterCount 4 w := by
    intro w
    induction w with
    | nil => intro _; simp [gWordG_nil, letterCount_nil]
    | cons l w ih =>
      intro hw
      rw [gWordG_cons, map_mul, hlet l (hw l (List.mem_cons_self ..)),
        ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')), letterCount_cons,
        letterCount_cons, letterCount_cons]
      exact comm_pow_aux _ _ _ _ _ _ _ _ _
  rw [hker, hword w hw]
  obtain ⟨m2, hm2⟩ := e2
  obtain ⟨m3, hm3⟩ := e3
  obtain ⟨m4, hm4⟩ := e4
  rw [hm2, hm3, hm4, ← two_mul, ← two_mul, ← two_mul, pow_mul, pow_mul, pow_mul, hb2, hc2, hd2]
  simp

theorem g0_mem_commutator : g0 K ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  refine mem_commutator_of_conj_mem (x := z1 K) ?_
  have h : z1 K * g0 K * (z1 K)⁻¹ = ⁅(z1 K * z2 K) * g1 K * (z1 K * z2 K)⁻¹, g1 K⁆ :=
    Subtype.ext tits_R2.symm
  rw [h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem g1_sq_mem_commutator : g1 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  refine mem_commutator_of_conj_mem (x := z2 K) ?_
  have h : z2 K * g1 K ^ 2 * (z2 K)⁻¹ =
      ⁅z1 K * g1 K * (z1 K)⁻¹, (z2 K * z1 K) * g0 K * (z2 K * z1 K)⁻¹⁆ :=
    Subtype.ext tits_R1.symm
  rw [h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem gens_mem_commutator :
    g0 K ∈ commutator (reeFixed ReeTag.F4 K 0) ∧
      g1 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0) ∧
      z1 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0) ∧
      z2 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  refine ⟨g0_mem_commutator, g1_sq_mem_commutator, ?_, ?_⟩
  · have : z1 K ^ 2 = 1 := by
      rw [pow_two]
      exact Subtype.ext titsZ1_mul_self
    rw [this]
    exact one_mem _
  · have : z2 K ^ 2 = 1 := by
      rw [pow_two]
      exact Subtype.ext titsZ2_mul_self
    rw [this]
    exact one_mem _

theorem gWordG_mem_commutator_of_even (w : List ℤ) (hw : ∀ l ∈ w, GoodLetter l)
    (e2 : Even (letterCount 2 w)) (e3 : Even (letterCount 3 w)) (e4 : Even (letterCount 4 w)) :
    gWordG K w ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := gens_mem_commutator (K := K)
  exact gWordG_mem_commutator h0 h1 h2 h3 w hw e2 e3 e4

end Parity

section Heis

variable {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem heisAG_mem_commutator {j : ℕ} (hj : j < 4) :
    heisAG k j ∈ commutator (reeFixed ReeTag.F4 k 0) := by
  obtain ⟨e2, e3, e4⟩ := heisA_even j hj
  have hmem : heisA.getD j [] ∈ heisA := by
    rw [List.getD_eq_getElem _ _ (by simpa [heisA] using hj)]
    exact List.getElem_mem _
  exact gWordG_mem_commutator_of_even _ (heis_letters _ (List.mem_append_left _ hmem)) e2 e3 e4

theorem heisXG_mem_commutator {i : ℕ} (hi : i < 16) :
    heisXG k i ∈ commutator (reeFixed ReeTag.F4 k 0) := by
  obtain ⟨e2, e3, e4⟩ := heisX_even i hi
  have hmem : heisX.getD i [] ∈ heisX := by
    rw [List.getD_eq_getElem _ _ (by simpa [heisX] using hi)]
    exact List.getElem_mem _
  exact gWordG_mem_commutator_of_even _ (heis_letters _ (List.mem_append_right _ hmem)) e2 e3 e4

theorem titsD_action_trivial (hk : Nat.card k = 2) {Λ : Type*} [Finite Λ]
    (hΛ : Nat.card Λ < 32)
    (π : ↥(commutator (reeFixed ReeTag.F4 k 0)) →* Equiv.Perm Λ) : ∀ d, π d = 1 := by
  classical
  have hfin : Finite (reeFixed ReeTag.F4 k 0) := by
    have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
    have : Finite (adjointGroup ReeTag.F4.tag k) := Subtype.finite
    exact Subtype.finite
  have hZ : heisZG k ∈ commutator (reeFixed ReeTag.F4 k 0) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hzz : (⟨heisZG k, hZ⟩ : ↥(commutator (reeFixed ReeTag.F4 k 0))) * ⟨heisZG k, hZ⟩ = 1 := by
    apply Subtype.ext
    exact heisZG_mul_self
  have haa : ∀ j j' : Fin 4,
      (⟨heisAG k j.val, heisAG_mem_commutator j.2⟩ : ↥(commutator (reeFixed ReeTag.F4 k 0))) *
        ⟨heisAG k j'.val, heisAG_mem_commutator j'.2⟩ =
      ⟨heisAG k j'.val, heisAG_mem_commutator j'.2⟩ *
        ⟨heisAG k j.val, heisAG_mem_commutator j.2⟩ := fun j j' => by
    apply Subtype.ext
    exact heisAG_comm j.2 j'.2
  have haz : ∀ j : Fin 4,
      (⟨heisAG k j.val, heisAG_mem_commutator j.2⟩ : ↥(commutator (reeFixed ReeTag.F4 k 0))) *
        ⟨heisZG k, hZ⟩ = ⟨heisZG k, hZ⟩ * ⟨heisAG k j.val, heisAG_mem_commutator j.2⟩ :=
    fun j => by
    apply Subtype.ext
    exact heisAG_comm_Z j.2
  have hxz : ∀ i : Fin 16,
      (⟨heisXG k i.val, heisXG_mem_commutator i.2⟩ : ↥(commutator (reeFixed ReeTag.F4 k 0))) *
        ⟨heisZG k, hZ⟩ = ⟨heisZG k, hZ⟩ * ⟨heisXG k i.val, heisXG_mem_commutator i.2⟩ :=
    fun i => by
    apply Subtype.ext
    exact heisXG_comm_Z i.2
  have hxa : ∀ (i : Fin 16) (j : Fin 4),
      ⁅(⟨heisXG k i.val, heisXG_mem_commutator i.2⟩ : ↥(commutator (reeFixed ReeTag.F4 k 0))),
        (⟨heisAG k j.val, heisAG_mem_commutator j.2⟩ : ↥(commutator (reeFixed ReeTag.F4 k 0)))⁆ =
      if (i.val >>> j.val) % 2 = 1 then
        (⟨heisZG k, hZ⟩ : ↥(commutator (reeFixed ReeTag.F4 k 0))) else 1 := fun i j => by
    apply Subtype.ext
    have h := heis_commutator (K := k) i.2 j.2
    show ⁅heisXG k i.val, heisAG k j.val⁆ = _
    rw [h]
    split_ifs <;> rfl
  have hπz : π ⟨heisZG k, hZ⟩ = 1 :=
    heis_system_trivial (G := ↥(commutator (reeFixed ReeTag.F4 k 0)))
      (fun j : Fin 4 => ⟨heisAG k j.val, heisAG_mem_commutator j.2⟩)
      (fun i : Fin 16 => ⟨heisXG k i.val, heisXG_mem_commutator i.2⟩)
      ⟨heisZG k, hZ⟩ hzz haa haz hxz hxa hΛ π
  have hMD : π.ker.map (commutator (reeFixed ReeTag.F4 k 0)).subtype ≤
      commutator (reeFixed ReeTag.F4 k 0) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hMn : ∀ d ∈ commutator (reeFixed ReeTag.F4 k 0),
      ∀ m ∈ π.ker.map (commutator (reeFixed ReeTag.F4 k 0)).subtype,
        d * m * d⁻¹ ∈ π.ker.map (commutator (reeFixed ReeTag.F4 k 0)).subtype := by
    rintro d hd _ ⟨x, hx, rfl⟩
    exact ⟨⟨d, hd⟩ * x * ⟨d, hd⟩⁻¹, π.normal_ker.conj_mem x hx ⟨d, hd⟩, rfl⟩
  rcases (titsData k hk).eq_bot_or_eq_of_le hk _ hMD hMn with h | h
  · exfalso
    have : heisZG k ∈ π.ker.map (commutator (reeFixed ReeTag.F4 k 0)).subtype := ⟨_, hπz, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact heisZG_ne_one this
  · intro d
    have hd : (d : reeFixed ReeTag.F4 k 0) ∈
        π.ker.map (commutator (reeFixed ReeTag.F4 k 0)).subtype := by
      rw [h]
      exact d.2
    obtain ⟨x, hx, hxd⟩ := hd
    have : x = d := Subtype.ext hxd
    rw [← this]
    exact hx

end Heis

end CFSG.SignalizerFunctorTheorem.CatalogBridge
