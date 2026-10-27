module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsWords
public import CFSG.SignalizerFunctorTheorem.NonLocal.PermHeis
public import CFSG.LieType.Chevalley.SylowOpposition

public noncomputable section

open CFSG.LieType.Simplicity.TitsBits CFSG.SectionRank.TitsOrder CFSG.LieType.Ree
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Simplicity
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def heisA : List (List ℤ) :=
  [[3, 2, 2, 3], [3, 4, 1, 4, 3], [4, 3, 2, 2, 3, 4], [-2, 3, 2, 2, 3, 2]]

@[expose] def heisX : List (List ℤ) :=
  [[], [1, 2, 1, -2], [2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2], [4, 1, 4, 2, 1, -2], [1, 4, 1, 4],
    [4, 1, 2, 1, -2, 4], [-2, 1, 2], [2, 2, 1, 2, 1, 2], [4, 1, 4], [2, 1, 2, 2, 1, 2],
    [-2, 1, 2, 1], [1], [2, 1, -2], [4, 1, 4, -2, 1, 2], [2, 2, 1, 2, 2]]

@[expose] def commBits (P Q : ℕ × ℕ) : ℕ := mul (mul (mul P.1 Q.1) P.2) Q.2

@[expose] def heisZ : ℕ := commBits (wordPair (heisX.getD 1 [])) (wordPair (heisA.getD 0 []))

instance : DecidablePred GoodLetter := fun l => inferInstanceAs (Decidable (l ≠ 0 ∧ l.natAbs ≤ 4))

theorem heis_letters : ∀ w ∈ heisA ++ heisX, ∀ l ∈ w, GoodLetter l := by decide

theorem heis_aa : ∀ j < 4, ∀ j' < 4,
    mul (wordPair (heisA.getD j [])).1 (wordPair (heisA.getD j' [])).1 % 2 ^ 2704 =
      mul (wordPair (heisA.getD j' [])).1 (wordPair (heisA.getD j [])).1 % 2 ^ 2704 := by
  decide +kernel

theorem heis_zz : mul heisZ heisZ % 2 ^ 2704 = oneBits % 2 ^ 2704 := by decide +kernel

theorem heis_z_ne : heisZ % 2 ^ 2704 ≠ oneBits % 2 ^ 2704 := by decide +kernel

theorem heis_za : ∀ j < 4, mul heisZ (wordPair (heisA.getD j [])).1 % 2 ^ 2704 =
    mul (wordPair (heisA.getD j [])).1 heisZ % 2 ^ 2704 := by decide +kernel

theorem heis_zx : ∀ i < 16, mul heisZ (wordPair (heisX.getD i [])).1 % 2 ^ 2704 =
    mul (wordPair (heisX.getD i [])).1 heisZ % 2 ^ 2704 := by decide +kernel

theorem heis_xa : ∀ i < 16, ∀ j < 4,
    commBits (wordPair (heisX.getD i [])) (wordPair (heisA.getD j [])) % 2 ^ 2704 =
      (if (i >>> j) % 2 = 1 then heisZ else oneBits) % 2 ^ 2704 := by decide +kernel


section Group

variable {K : Type} [Field K] [CharP K ReeTag.F4.prime]

theorem hasBits_mul_prime
    {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ} (hg : HasBits K g A) (hh : HasBits K h B) :
    HasBits K (g * h) (mul A B) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact hg.mul hh

theorem hasBits_commutator
    {x y : adjointGroup ReeTag.F4.tag K} {X X' Y Y' : ℕ} (hx : HasBits K x X)
    (hx' : HasBits K x⁻¹ X') (hy : HasBits K y Y) (hy' : HasBits K y⁻¹ Y') :
    HasBits K (x * y * x⁻¹ * y⁻¹) (mul (mul (mul X Y) X') Y') :=
  hasBits_mul_prime (hasBits_mul_prime (hasBits_mul_prime hx hy) hx') hy'

variable [Finite K] in
theorem eq_of_hasBits
    {g h : reeFixed ReeTag.F4 K 0} {A B : ℕ}
    (hg : HasBits K (g : adjointGroup ReeTag.F4.tag K) A)
    (hh : HasBits K (h : adjointGroup ReeTag.F4.tag K) B) (hAB : A % 2 ^ 2704 = B % 2 ^ 2704) :
    g = h :=
  Subtype.ext ((hg.eq_iff hh).2 hAB)

end Group


section Elements

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

variable (K) in
@[expose] def heisAG
    (j : ℕ) : reeFixed ReeTag.F4 K 0 := gWordG K (heisA.getD j [])

variable (K) in
@[expose] def heisXG
    (i : ℕ) : reeFixed ReeTag.F4 K 0 := gWordG K (heisX.getD i [])

variable (K) in
@[expose] def heisZG
    : reeFixed ReeTag.F4 K 0 := ⁅heisXG K 1, heisAG K 0⁆

theorem hasBits_coe_mul
    {g h : reeFixed ReeTag.F4 K 0} {A B : ℕ} (hg : HasBits K (g : adjointGroup ReeTag.F4.tag K) A)
    (hh : HasBits K (h : adjointGroup ReeTag.F4.tag K) B) :
    HasBits K ((g * h : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) (mul A B) := by
  rw [Subgroup.coe_mul]
  exact hasBits_mul_prime hg hh

theorem hasBits_coe_one
    : HasBits K ((1 : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) oneBits := by
  rw [Subgroup.coe_one]
  exact hasBits_one

theorem hasBits_coe_comm
    {x y : reeFixed ReeTag.F4 K 0} {X X' Y Y' : ℕ}
    (hx : HasBits K (x : adjointGroup ReeTag.F4.tag K) X)
    (hx' : HasBits K (x : adjointGroup ReeTag.F4.tag K)⁻¹ X')
    (hy : HasBits K (y : adjointGroup ReeTag.F4.tag K) Y)
    (hy' : HasBits K (y : adjointGroup ReeTag.F4.tag K)⁻¹ Y') :
    HasBits K ((⁅x, y⁆ : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K)
      (mul (mul (mul X Y) X') Y') := by
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_inv]
  exact hasBits_commutator hx hx' hy hy'

theorem heis_mem_a {j : ℕ} (hj : j < 4) : heisA.getD j [] ∈ heisA ++ heisX := by
  have : j < heisA.length := by simpa [heisA] using hj
  rw [List.getD_eq_getElem _ _ this]
  exact List.mem_append_left _ (List.getElem_mem this)

theorem heis_mem_x {i : ℕ} (hi : i < 16) : heisX.getD i [] ∈ heisA ++ heisX := by
  have : i < heisX.length := by simpa [heisX] using hi
  rw [List.getD_eq_getElem _ _ this]
  exact List.mem_append_right _ (List.getElem_mem this)

theorem hasBits_heisAG
    {j : ℕ} (hj : j < 4) :
    HasBits K (heisAG K j : adjointGroup ReeTag.F4.tag K) (wordPair (heisA.getD j [])).1 ∧
    HasBits K (heisAG K j : adjointGroup ReeTag.F4.tag K)⁻¹ (wordPair (heisA.getD j [])).2 :=
  hasBits_gWordG _ fun l hl => heis_letters _ (heis_mem_a hj) l hl

theorem hasBits_heisXG
    {i : ℕ} (hi : i < 16) :
    HasBits K (heisXG K i : adjointGroup ReeTag.F4.tag K) (wordPair (heisX.getD i [])).1 ∧
    HasBits K (heisXG K i : adjointGroup ReeTag.F4.tag K)⁻¹ (wordPair (heisX.getD i [])).2 :=
  hasBits_gWordG _ fun l hl => heis_letters _ (heis_mem_x hi) l hl

theorem hasBits_heisZG
    : HasBits K (heisZG K : adjointGroup ReeTag.F4.tag K) heisZ :=
  hasBits_coe_comm (hasBits_heisXG (by norm_num : 1 < 16)).1
    (hasBits_heisXG (by norm_num : 1 < 16)).2 (hasBits_heisAG (by norm_num : 0 < 4)).1
    (hasBits_heisAG (by norm_num : 0 < 4)).2

theorem heisAG_comm
    {j j' : ℕ} (hj : j < 4) (hj' : j' < 4) : heisAG K j * heisAG K j' = heisAG K j' * heisAG K j :=
  eq_of_hasBits (hasBits_coe_mul (hasBits_heisAG hj).1 (hasBits_heisAG hj').1)
    (hasBits_coe_mul (hasBits_heisAG hj').1 (hasBits_heisAG hj).1) (heis_aa j hj j' hj')

theorem heisZG_mul_self
    : heisZG K * heisZG K = 1 :=
  eq_of_hasBits (hasBits_coe_mul hasBits_heisZG hasBits_heisZG) hasBits_coe_one heis_zz

theorem heisZG_ne_one
    : heisZG K ≠ 1 := fun h => heis_z_ne
  ((hasBits_heisZG (K := K)).eq_iff hasBits_coe_one |>.1 (by rw [h]) |> fun h' => h')

theorem heisAG_comm_Z
    {j : ℕ} (hj : j < 4) : heisAG K j * heisZG K = heisZG K * heisAG K j :=
  eq_of_hasBits (hasBits_coe_mul (hasBits_heisAG hj).1 hasBits_heisZG)
    (hasBits_coe_mul hasBits_heisZG (hasBits_heisAG hj).1) (by
      have := heis_za j hj
      exact this.symm)

theorem heisXG_comm_Z
    {i : ℕ} (hi : i < 16) : heisXG K i * heisZG K = heisZG K * heisXG K i :=
  eq_of_hasBits (hasBits_coe_mul (hasBits_heisXG hi).1 hasBits_heisZG)
    (hasBits_coe_mul hasBits_heisZG (hasBits_heisXG hi).1) (by
      have := heis_zx i hi
      exact this.symm)

theorem heis_commutator
    {i j : ℕ} (hi : i < 16) (hj : j < 4) :
    ⁅heisXG K i, heisAG K j⁆ = if (i >>> j) % 2 = 1 then heisZG K else 1 := by
  by_cases hb : (i >>> j) % 2 = 1
  · rw [ite_eq_left hb]
    refine eq_of_hasBits (hasBits_coe_comm (hasBits_heisXG hi).1 (hasBits_heisXG hi).2
      (hasBits_heisAG hj).1 (hasBits_heisAG hj).2) hasBits_heisZG ?_
    have := heis_xa i hi j hj
    rw [ite_eq_left hb] at this
    exact this
  · rw [ite_eq_right hb]
    refine eq_of_hasBits (hasBits_coe_comm (hasBits_heisXG hi).1 (hasBits_heisXG hi).2
      (hasBits_heisAG hj).1 (hasBits_heisAG hj).2) hasBits_coe_one ?_
    have := heis_xa i hi j hj
    rw [ite_eq_right hb] at this
    exact this

end Elements



section Abstract

open scoped IsMulCommutative

theorem heis_system_trivial {G : Type*} [Group G] [Finite G] (a : Fin 4 → G) (x : Fin 16 → G)
    (z : G) (hzz : z * z = 1) (haa : ∀ j j', a j * a j' = a j' * a j)
    (haz : ∀ j, a j * z = z * a j) (hxz : ∀ i, x i * z = z * x i)
    (hxa : ∀ (i : Fin 16) (j : Fin 4),
      ⁅x i, a j⁆ = if (i.val >>> j.val) % 2 = 1 then z else 1)
    {Λ : Type*} [Finite Λ] (hΛ : Nat.card Λ < 32) (π : G →* Equiv.Perm Λ) : π z = 1 := by
  classical
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  obtain ⟨Z, hmemZ⟩ : ∃ Z : Subgroup G, ∀ u, u ∈ Z ↔ u = 1 ∨ u = z :=
    ⟨{ carrier := {1, z}
       mul_mem' := by
         rintro u v (rfl | rfl) (rfl | rfl) <;> simp [hzz]
       one_mem' := Or.inl rfl
       inv_mem' := by
         rintro u (rfl | rfl) <;> simp [hzinv] }, fun u => Iff.rfl⟩
  obtain ⟨A, hmemA⟩ : ∃ A : Subgroup G, A = Subgroup.closure (insert z (Set.range a)) := ⟨_, rfl⟩
  have hpw : (insert z (Set.range a)).Pairwise Commute := by
    intro u hu v hv huv
    rcases hu with rfl | ⟨j, rfl⟩ <;> rcases hv with rfl | ⟨j', rfl⟩
    · exact absurd rfl huv
    · exact (haz j').symm
    · exact haz j
    · exact haa j j'
  have hAc : IsMulCommutative A := by
    rw [hmemA]
    exact Subgroup.isMulCommutative_closure hpw
  have hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (mul_comm (⟨u, hu⟩ : A) ⟨v, hv⟩)
  have hzA : z ∈ A := by
    rw [hmemA]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have haA : ∀ j, a j ∈ A := fun j => by
    rw [hmemA]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  have hZA : Z ≤ A := by
    intro u hu
    rcases (hmemZ u).1 hu with rfl | rfl
    · exact one_mem A
    · exact hzA
  have hzZ : z ∈ Z := (hmemZ z).2 (Or.inr rfl)
  have hcomm : ∀ i : Fin 16, ∀ g ∈ A, ⁅x i, g⁆ ∈ Z := by
    intro i g hg
    rw [hmemA] at hg
    refine Subgroup.closure_induction (p := fun g _ => ⁅x i, g⁆ ∈ Z) ?_ ?_ ?_ ?_ hg
    · rintro g (rfl | ⟨j, rfl⟩)
      · have : ⁅x i, g⁆ = 1 := by
          rw [commutatorElement_def, hxz i]
          group
        rw [this]
        exact one_mem Z
      · rw [hxa i j]
        split_ifs
        · exact hzZ
        · exact one_mem Z
    · rw [commutatorElement_def]
      simp
    · intro g h hgA hhA hg hh
      have hg' : g ∈ A := hmemA ▸ hgA
      have e : ⁅x i, g * h⁆ = ⁅x i, g⁆ * (g * ⁅x i, h⁆ * g⁻¹) := by
        simp only [commutatorElement_def]; group
      have hcz : g * ⁅x i, h⁆ * g⁻¹ = ⁅x i, h⁆ := by
        have hmZ : ⁅x i, h⁆ ∈ A := hZA hh
        rw [hAcomm g hg' _ hmZ]
        group
      rw [e, hcz]
      exact mul_mem hg hh
    · intro g hgA hg
      have hg' : g ∈ A := hmemA ▸ hgA
      have e : ⁅x i, g⁻¹⁆ = g⁻¹ * ⁅x i, g⁆⁻¹ * g := by
        simp only [commutatorElement_def]; group
      have hmZ : ⁅x i, g⁆ ∈ A := hZA hg
      have hcz : g⁻¹ * ⁅x i, g⁆⁻¹ * g = ⁅x i, g⁆⁻¹ := by
        have hmZ' : ⁅x i, g⁆⁻¹ ∈ A := inv_mem hmZ
        rw [hAcomm g⁻¹ (inv_mem hg') _ hmZ']
        group
      rw [e, hcz]
      exact inv_mem hg
  have hdig : ∀ i j : Fin 16, i ≠ j → ∃ m : Fin 4,
      ((i.val >>> m.val) % 2 = 1) ≠ ((j.val >>> m.val) % 2 = 1) := by decide
  have hHD : ∀ i j : Fin 16, i ≠ j → ∀ u ∈ Z, ∃ g ∈ A, ⁅x i, g⁆ = u * ⁅x j, g⁆ := by
    intro i j hij u hu
    rcases (hmemZ u).1 hu with rfl | rfl
    · exact ⟨1, one_mem A, by simp [commutatorElement_def]⟩
    · obtain ⟨m, hm⟩ := hdig i j hij
      refine ⟨a m, haA m, ?_⟩
      rw [hxa i m, hxa j m]
      by_cases h1 : (i.val >>> m.val) % 2 = 1
      · have h2 : ¬ (j.val >>> m.val) % 2 = 1 := fun h2 => hm (by simp [h1, h2])
        rw [ite_eq_left h1, ite_eq_right h2, mul_one]
      · have h2 : (j.val >>> m.val) % 2 = 1 := by
          by_contra h2
          exact hm (by simp [h1, h2])
        rw [ite_eq_right h1, ite_eq_left h2, hzz]
  by_contra hπ
  have hcard := NonLocal.two_mul_card_le_card_of_heisenberg_perm π A Z hAc hZA
    (fun i : Fin 16 => (x i)⁻¹)
    (fun i g hg => by rw [inv_inv]; exact hcomm i g hg)
    (fun i j hij u hu => by
      rw [inv_inv, inv_inv]
      exact hHD i j hij u hu)
    (z₀ := z) hzZ hzz hπ (fun i => by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hxz i]
      group)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega

end Abstract

section Main

variable {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem titsGamma_commutator_le_ker
    (hk : Nat.card k = 2) {Λ : Type*} [Finite Λ] (hΛ : Nat.card Λ < 32)
    (π : reeFixed ReeTag.F4 k 0 →* Equiv.Perm Λ) :
    commutator (reeFixed ReeTag.F4 k 0) ≤ π.ker := by
  have hfin : Finite (reeFixed ReeTag.F4 k 0) := by
    have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
    have : Finite (adjointGroup ReeTag.F4.tag k) := Subtype.finite
    exact Subtype.finite
  have hπz : π (heisZG k) = 1 :=
    heis_system_trivial (fun j : Fin 4 => heisAG k j.val) (fun i : Fin 16 => heisXG k i.val)
      (heisZG k) heisZG_mul_self (fun j j' => heisAG_comm j.2 j'.2)
      (fun j => heisAG_comm_Z j.2) (fun i => heisXG_comm_Z i.2)
      (fun i j => heis_commutator i.2 j.2) hΛ π
  have hzker : heisZG k ∈ π.ker := hπz
  rcases (titsData k hk).le_of_normal hk π.ker with h | h
  · exfalso
    rw [h, Subgroup.mem_bot] at hzker
    exact heisZG_ne_one hzker
  · exact h

end Main

end CFSG.SignalizerFunctorTheorem.CatalogBridge
