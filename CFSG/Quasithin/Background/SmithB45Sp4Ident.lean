module

public import CFSG.Quasithin.Background.SmithB45Sp4Herm
public import CFSG.Quasithin.Background.SmithB42Sp4Ident

public section

namespace CFSG.Quasithin.B45Sp4

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.X7 (matRep MatIso permMat permMat_mulVec_apply
  permMat_mul_permMat matMap matMap_apply)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Quasithin.B42Sp4
open scoped Matrix

section Fixed

variable {D F : Type} [Field D] [Field F] [Finite D]

theorem map_pow_two_pow {a : ℕ} (hD : Nat.card D = 2 ^ a) (ι : D →+* F) (y : D) :
    ι y ^ 2 ^ a = ι y := by
  have : Fintype D := Fintype.ofFinite D
  rw [← map_pow, ← hD, Nat.card_eq_fintype_card, FiniteField.pow_card]

end Fixed

section FrobMat

variable {F : Type} [Field F] [CharP F 2] [Finite F] {κ κ' : Type} [Fintype κ] [Fintype κ']

omit [Fintype κ] [Fintype κ'] in
theorem map_frob_map_frob {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (X : Matrix κ κ' F) :
    (X.map (iterateFrobenius F 2 a)).map (iterateFrobenius F 2 a) = X := by
  ext i j
  simp only [Matrix.map_apply, iterateFrobenius_def]
  exact pow_pow_frob hF _

omit [Fintype κ] [Fintype κ'] [Finite F] in
theorem permMat_map_frob [DecidableEq κ'] (a : ℕ) (e : κ ≃ κ') :
    (permMat F e).map (iterateFrobenius F 2 a) = permMat F e := by
  ext i j
  simp only [Matrix.map_apply, permMat, Matrix.of_apply]
  split_ifs <;> simp

end FrobMat

section Descent

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem exists_tensor_coords {a : ℕ} (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hD : Nat.card (EndRing (repOf π)) = 2 ^ a)
    (hdim : Module.finrank (EndRing (repOf π)) M = 16) :
    ∃ (S : Finset ℕ) (hS : S ⊆ Finset.range (2 * (2 * a)))
      (hsh : shiftSet (2 * a) (2 * a) S = S) (Φ : M →+ ((↥S → Fin 4) → F)),
      S.card = 2 ∧ Function.Injective Φ ∧
      (∀ w, (permMat F (flipEquiv hS hsh)).mulVec (fun x => Φ w x ^ 2 ^ a) = Φ w) ∧
      ∀ g w, Φ (π g w) = (tensorRepS (F := F) F S g).mulVec (Φ w) := by
  classical
  set ρ := repOf π with hρ
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have hcharD : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hFcard : Nat.card F = 2 ^ (2 * a) := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨ιD⟩ := exists_ringHom_of_dvd hD hFcard (Dvd.intro_left 2 rfl)
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  let b : Module.Basis (Fin 16) (EndRing ρ) M := Module.finBasisOfFinrankEq (EndRing ρ) M hdim
  obtain ⟨S, hSne, hS, ⟨Φ₀⟩, h16⟩ := exists_label hF (by omega) hnt b (RingHom.id F) ιD
  have hS2 : S.card = 2 := by
    have h := (Nat.pow_right_injective (le_refl 2) (by
      rw [show (2 : ℕ) ^ (2 * S.card) = 4 ^ S.card by rw [pow_mul]; norm_num, ← h16]
      norm_num : 2 ^ (2 * S.card) = 2 ^ 4))
    omega
  have e : (matRep (tensorRepS (F := F) F S)).Equiv (matRep (matHomE ρ b ιD)) :=
    Φ₀.trans (Representation.Equiv.mk (LinearEquiv.refl F _) (fun g => by
      rw [matRep_matHomE]
      rfl))
  have hfrobD : ∀ g, (matHomE ρ b ιD g).map (iterateFrobenius F 2 a) = matHomE ρ b ιD g := by
    intro g
    ext i j
    rw [Matrix.map_apply, matHomE_apply, Matrix.map_apply, iterateFrobenius_def]
    exact map_pow_two_pow hD ιD _
  have hshift : shiftSet (2 * a) (2 * a) S = S :=
    shiftSet_eq_of_frob F hF (by omega) hS (matHomE ρ b ιD) a hfrobD e
  obtain ⟨P, Q, hPQ⟩ := MatIso.exists_of_equiv e
  set σ : F →+* F := iterateFrobenius F 2 a with hσ
  set Pm : Matrix (↥S → Fin 4) (↥S → Fin 4) F := permMat F (flipEquiv hS hshift) with hPm
  have hPmPm : Pm * Pm = 1 := by
    have h := permMat_mul_permMat (k := F) (flipEquiv hS hshift)
    rwa [flipEquiv_symm] at h
  have hPmσ : Pm.map σ = Pm := permMat_map_frob a _
  have hT : matMap σ (tensorRepS (F := F) F S) =
      (tensorRepS (F := F) F S).comp (minorAut F ^ (2 * a)).toMonoidHom :=
    MonoidHom.ext fun g => tensorRepS_map_frob F S a g
  have hM : matMap σ (matHomE ρ b ιD) = matHomE ρ b ιD := MonoidHom.ext fun g => hfrobD g
  have h1 := hPQ.map σ
  rw [hT, hM] at h1
  have h2 := flip_matIso hS hshift hF
  rw [flipEquiv_symm] at h2
  have h3 := h2.symm.trans h1
  have h4 := h3.trans hPQ.symm
  obtain ⟨c, hc⟩ := schur_tensorRepS hF hS (Q * (P.map σ * Pm)) h4.comm
  have hR : P.map σ * Pm = c • P := by
    calc P.map σ * Pm = (P * Q) * (P.map σ * Pm) := by rw [hPQ.mul_inv, Matrix.one_mul]
      _ = P * (Q * (P.map σ * Pm)) := Matrix.mul_assoc _ _ _
      _ = c • P := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨l, hl⟩ : ∃ l : F, l + σ l * c ≠ 0 := by
    by_cases hc1 : c = 1
    · obtain ⟨θ, hθ⟩ := exists_ne_frob ha hFcard
      refine ⟨θ, ?_⟩
      rw [hc1, mul_one, hσ, iterateFrobenius_def]
      exact add_frob_ne_zero hθ
    · refine ⟨1, ?_⟩
      rw [map_one, one_mul]
      intro h
      apply hc1
      have := eq_neg_of_add_eq_zero_right h
      rw [this, CharTwo.neg_eq]
  set μ : F := l + σ l * c with hμ
  set P' : Matrix (Fin 16) (↥S → Fin 4) F := l • P + σ l • (P.map σ * Pm) with hP'
  have hP'μ : P' = μ • P := by
    rw [hP', hR, smul_smul, ← add_smul, mul_comm (σ l) c, hμ, mul_comm c (σ l)]
  set Q' : Matrix (↥S → Fin 4) (Fin 16) F := μ⁻¹ • Q with hQ'
  have hP'Q' : P' * Q' = 1 := by
    rw [hP'μ, hQ', Matrix.smul_mul, Matrix.mul_smul, hPQ.mul_inv, smul_smul,
      mul_inv_cancel₀ hl, one_smul]
  have hQ'P' : Q' * P' = 1 := by
    rw [hP'μ, hQ', Matrix.smul_mul, Matrix.mul_smul, hPQ.inv_mul, smul_smul,
      inv_mul_cancel₀ hl, one_smul]
  have hQ'comm : ∀ g, Q' * matHomE ρ b ιD g = tensorRepS (F := F) F S g * Q' := by
    intro g
    have h5 := (hPQ.symm).comm g
    rw [hQ', Matrix.smul_mul, Matrix.mul_smul, h5]
  have hσP' : P'.map σ = P' * Pm := by
    rw [hP', Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hPmPm,
      Matrix.mul_one]
    have e1 : (l • P + σ l • (P.map σ * Pm)).map σ = σ l • P.map σ + l • (P * Pm) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
        map_mul]
      rw [← Matrix.map_apply (f := σ) (M := P.map σ * Pm), Matrix.map_mul, map_frob_map_frob hFcard,
        hPmσ]
      have hσσ : σ (σ l) = l := by
        rw [hσ, iterateFrobenius_def, iterateFrobenius_def]
        exact pow_pow_frob hFcard l
      rw [hσσ]
    rw [e1, add_comm]
  have hσQ' : Q'.map σ = Pm * Q' := by
    have hPPmQ : P'.map σ * (Pm * Q') = 1 := by
      rw [hσP', Matrix.mul_assoc, ← Matrix.mul_assoc Pm Pm Q', hPmPm, Matrix.one_mul, hP'Q']
    have hQP : Q'.map σ * P'.map σ = 1 := by
      rw [← Matrix.map_mul, hQ'P', Matrix.map_one σ (map_zero σ) (map_one σ)]
    calc Q'.map σ = Q'.map σ * (P'.map σ * (Pm * Q')) := by rw [hPPmQ, Matrix.mul_one]
      _ = (Q'.map σ * P'.map σ) * (Pm * Q') := (Matrix.mul_assoc _ _ _).symm
      _ = Pm * Q' := by rw [hQP, Matrix.one_mul]
  let coord : M →+ (Fin 16 → F) :=
    { toFun := fun w i => ιD (b.equivFun w i)
      map_zero' := by
        funext i
        show ιD (b.equivFun 0 i) = 0
        rw [map_zero b.equivFun, Pi.zero_apply, RingHom.map_zero]
      map_add' := fun w w' => by
        funext i
        show ιD (b.equivFun (w + w') i) = ιD (b.equivFun w i) + ιD (b.equivFun w' i)
        rw [map_add b.equivFun, Pi.add_apply, RingHom.map_add] }
  have hcoord : ∀ w i, coord w i = ιD (b.equivFun w i) := fun _ _ => rfl
  have hcoord_g : ∀ g w, coord (π g w) = (matHomE ρ b ιD g).mulVec (coord w) := by
    intro g w
    funext i
    rw [hcoord, matHomE_apply]
    have h6 := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
    have h7 : b.equivFun (π g w) = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).mulVec
        (b.equivFun w) := by
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
      exact h6.symm
    rw [h7, RingHom.map_mulVec]
    rfl
  have hcoord_σ : ∀ w, (fun i => σ (coord w i)) = coord w := by
    intro w
    funext i
    rw [hcoord, hσ, iterateFrobenius_def]
    exact map_pow_two_pow hD ιD _
  let Φ : M →+ ((↥S → Fin 4) → F) :=
    { toFun := fun w => Q'.mulVec (coord w)
      map_zero' := by rw [map_zero, Matrix.mulVec_zero]
      map_add' := fun w w' => by rw [map_add, Matrix.mulVec_add] }
  have hΦ : ∀ w, Φ w = Q'.mulVec (coord w) := fun _ => rfl
  refine ⟨S, hS, hshift, Φ, hS2, ?_, ?_, ?_⟩
  ·
    intro w w' h
    rw [hΦ, hΦ] at h
    have h8 : coord w = coord w' := by
      have := congrArg (fun y => P'.mulVec y) h
      simpa only [Matrix.mulVec_mulVec, hP'Q', Matrix.one_mulVec] using this
    have h9 : b.equivFun w = b.equivFun w' := by
      funext i
      exact ιD.injective (congrFun h8 i)
    exact b.equivFun.injective h9
  ·
    intro w
    have h10 : (fun x => Φ w x ^ 2 ^ a) = (Q'.map σ).mulVec (fun i => σ (coord w i)) := by
      funext x
      rw [hΦ]
      have := RingHom.map_mulVec σ Q' (coord w) x
      rw [hσ, iterateFrobenius_def] at this
      rw [this]
      rfl
    rw [← hPm, h10, hcoord_σ, hσQ', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPmPm,
      Matrix.one_mul, hΦ]
  ·
    intro g w
    rw [hΦ, hΦ, hcoord_g, Matrix.mulVec_mulVec, hQ'comm, ← Matrix.mulVec_mulVec]

end Descent

section Coords

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

@[expose] def pq {S : Finset ℕ} (j : ℕ) (p q : Fin 4) : ↥S → Fin 4 :=
  fun i => if (i : ℕ) = j then p else q

theorem pq_apply {S : Finset ℕ} (j : ℕ) (p q : Fin 4) (i : ↥S) :
    pq (S := S) j p q i = if (i : ℕ) = j then p else q := rfl

theorem eq_pq {S : Finset ℕ} {j j' : ℕ} (hS : S = {j, j'}) (hj : j ∈ S) (hj' : j' ∈ S)
    (x : ↥S → Fin 4) : x = pq j (x ⟨j, hj⟩) (x ⟨j', hj'⟩) := by
  funext i
  rw [pq_apply]
  have hmem : ∀ n ∈ S, n = j ∨ n = j' := fun n hn => by
    rw [hS, Finset.mem_insert, Finset.mem_singleton] at hn
    exact hn
  have hi := hmem i i.2
  split_ifs with h
  · exact congrArg x (Subtype.ext h)
  · exact congrArg x (Subtype.ext (hi.resolve_left h))

@[expose] def pqEquiv {S : Finset ℕ} {j j' : ℕ} (hS : S = {j, j'}) (hj : j ∈ S) (hj' : j' ∈ S)
    (hne : j' ≠ j) : Fin 4 × Fin 4 ≃ (↥S → Fin 4) where
  toFun pq' := pq j pq'.1 pq'.2
  invFun x := (x ⟨j, hj⟩, x ⟨j', hj'⟩)
  left_inv pq' := by
    simp [pq_apply, hne]
  right_inv x := (eq_pq hS hj hj' x).symm

theorem tensorRepS_pq {S : Finset ℕ} {j j' : ℕ} (hS : S = {j, j'}) (hne : j' ≠ j)
    (g : antiSp F) (p' q' p q : Fin 4) :
    tensorRepS (F := F) F S g (pq j p' q') (pq j p q) =
      natRepS F j g p' p * natRepS F j' g q' q := by
  rw [tensorRepS_apply]
  have h1 : (∏ i : ↥S, natRepS F (i : ℕ) g (pq j p' q' i) (pq j p q i)) =
      ∏ n ∈ S, natRepS F n g (if n = j then p' else q') (if n = j then p else q) :=
    Finset.prod_coe_sort S (fun n => natRepS F n g (if n = j then p' else q')
      (if n = j then p else q))
  rw [h1, hS, Finset.prod_pair hne.symm]
  simp [hne]

theorem natRepS_shift {a : ℕ} (hF : Fintype.card F = 2 ^ (2 * a)) (j : ℕ) (g : antiSp F) :
    natRepS F (shiftNat (2 * a) j) g = (natRepS F j g).map fun x => x ^ 2 ^ a := by
  rw [← natRepS_add_two_mul_pow, natRepS_mod (k := F) hF (j + 2 * a), shiftNat]

theorem natRepS_self (j : ℕ) (g : antiSp F) :
    natRepS F j g = glMat (((minorAut F ^ j) g : antiSp F) : GL (Fin 4) F) := by
  rw [natRepS_apply]
  ext x y
  rfl

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem exists_herm_coords {a : ℕ} (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hD : Nat.card (EndRing (repOf π)) = 2 ^ a)
    (hdim : Module.finrank (EndRing (repOf π)) M = 16) :
    ∃ (j : ℕ) (Ψ : M →+ Matrix (Fin 4) (Fin 4) F), Function.Injective Ψ ∧
      (∀ w, Ψ w ∈ hermA a (Fin 4) F) ∧
      ∀ g w, Ψ (π g w) = tw a (glMat (((minorAut F ^ j) g : antiSp F) : GL (Fin 4) F)) (Ψ w) := by
  classical
  obtain ⟨S, hS, hsh, Φ, hS2, hinj, hherm, hequiv⟩ :=
    exists_tensor_coords ha hF π hnt hD hdim
  obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set j' := shiftNat (2 * a) j with hj'def
  have hjS : (shiftFun hsh ⟨j, hj⟩ : ℕ) = j' := rfl
  have hj' : j' ∈ S := (shiftFun hsh ⟨j, hj⟩).2
  have hjlt : j < 2 * (2 * a) := Finset.mem_range.mp (hS hj)
  have hne : j' ≠ j := shiftNat_ne_self (by omega) hjlt
  have hSeq : S = {j, j'} := by
    have hsub : ({j, j'} : Finset ℕ) ⊆ S := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hj
      · exact hj'
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hS2, Finset.card_pair hne.symm]
  have hflip : ∀ p q : Fin 4, flipEquiv hS hsh (pq j p q) = pq j q p := by
    intro p q
    funext i
    rw [flipEquiv_apply, pq_apply, pq_apply]
    have hmem : ∀ n ∈ S, n = j ∨ n = j' := fun n hn => by
      rw [hSeq, Finset.mem_insert, Finset.mem_singleton] at hn
      exact hn
    rcases hmem i i.2 with hi | hi
    · have hsi : (shiftFun hsh i : ℕ) = j' := by
        rw [show i = ⟨j, hj⟩ from Subtype.ext hi]
        exact hjS
      rw [hsi, hi]
      simp [hne]
    · have hsi : (shiftFun hsh i : ℕ) = j := by
        have h1 : i = shiftFun hsh ⟨j, hj⟩ := Subtype.ext (hi.trans hjS.symm)
        rw [h1, shiftFun_involutive hS hsh]
      rw [hsi, hi]
      simp [hne]
  let Ψ : M →+ Matrix (Fin 4) (Fin 4) F :=
    { toFun := fun w => Matrix.of fun p q => Φ w (pq j p q)
      map_zero' := by
        ext p q
        simp
      map_add' := fun w w' => by
        ext p q
        simp }
  have hΨ : ∀ w p q, Ψ w p q = Φ w (pq j p q) := fun _ _ _ => rfl
  refine ⟨j, Ψ, ?_, ?_, ?_⟩
  ·
    intro w w' h
    apply hinj
    funext x
    rw [eq_pq hSeq hj hj' x]
    have := congrFun (congrFun h (x ⟨j, hj⟩)) (x ⟨j', hj'⟩)
    rwa [hΨ, hΨ] at this
  ·
    intro w
    rw [mem_hermA]
    ext p q
    rw [Matrix.transpose_apply, frobPow, Matrix.map_apply, hΨ, hΨ]
    have h1 := congrFun (hherm w) (pq j p q)
    rw [permMat_mulVec_apply, flipEquiv_symm, hflip] at h1
    exact h1
  ·
    intro g w
    ext p' q'
    rw [hΨ, hequiv, Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp (pqEquiv hSeq hj hj' hne), Fintype.sum_prod_type]
    simp only [pqEquiv, Equiv.coe_fn_mk]
    rw [tw_apply, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, frobPow, Matrix.map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [tensorRepS_pq hSeq hne, natRepS_shift hF, natRepS_self, Matrix.map_apply, hΨ]
    ring

end Coords

section Std

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

omit [CharP F 2] [Fintype F] in
theorem frobPow_submatrix {ι κ : Type} (a : ℕ) (Y : Matrix ι ι F) (e : κ → ι) :
    frobPow a (Y.submatrix e e) = (frobPow a Y).submatrix e e := rfl

omit [CharP F 2] [Fintype F] in
theorem tw_submatrix {ι κ : Type} [Fintype ι] [Fintype κ] (a : ℕ) (g Y : Matrix ι ι F)
    (e : κ ≃ ι) : (tw a g Y).submatrix e e = tw a (g.submatrix e e) (Y.submatrix e e) := by
  rw [tw_apply, tw_apply, ← Matrix.submatrix_mul_equiv _ _ _ e _,
    ← Matrix.submatrix_mul_equiv _ _ _ e _, frobPow_submatrix, Matrix.transpose_submatrix]

omit [Fintype F] in
theorem submatrix_mem_hermA {ι κ : Type} {a : ℕ} {Y : Matrix ι ι F} (hY : Y ∈ hermA a ι F)
    (e : κ → ι) : Y.submatrix e e ∈ hermA a κ F := by
  rw [mem_hermA] at hY ⊢
  rw [frobPow_submatrix, Matrix.transpose_submatrix, hY]

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem card_hermA_four {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) :
    Nat.card ↥(hermA a (Fin 2 ⊕ Fin 2) F) = 2 ^ (16 * a) := by
  have h := card_hermA_sq (ι := Fin 2 ⊕ Fin 2) ha hF
  rw [hF] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  refine Nat.pow_left_injective (n := 2) (by norm_num) ?_
  simp only
  rw [h, ← pow_mul, ← pow_mul]
  ring_nf

theorem exists_hermA_equiv {a : ℕ} (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hD : Nat.card (EndRing (repOf π)) = 2 ^ a)
    (hdim : Module.finrank (EndRing (repOf π)) M = 16) :
    ∃ (j : ℕ) (φ : M ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) F)), ∀ g w,
      (φ (π g w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        tw a (spMat (antiSpEquiv F ((minorAut F ^ j) g))) (φ w) := by
  classical
  obtain ⟨j, Ψ, hinj, hherm, hequiv⟩ := exists_herm_coords ha hF π hnt hD hdim
  have hFcard : Nat.card F = 2 ^ (2 * a) := by rw [Nat.card_eq_fintype_card, hF]
  let f : M →+ ↥(hermA a (Fin 2 ⊕ Fin 2) F) :=
    { toFun := fun w => ⟨(Ψ w).submatrix antiIdx antiIdx, submatrix_mem_hermA (hherm w) _⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun w w' => by
        apply Subtype.ext
        simp [Matrix.submatrix_add] }
  have hf : ∀ w, (f w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (Ψ w).submatrix antiIdx antiIdx := fun _ => rfl
  have hfinj : Function.Injective f := by
    intro w w' h
    apply hinj
    have h1 := congrArg (fun x : ↥(hermA a (Fin 2 ⊕ Fin 2) F) =>
      (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).submatrix antiIdx.symm antiIdx.symm) h
    simpa [hf, Matrix.submatrix_submatrix] using h1
  have hcardM : Nat.card M = 2 ^ (16 * a) := by
    rw [natCard_eq_pow_finrank (ρ := repOf π), hD, hdim, ← pow_mul, mul_comm]
  have hbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [hcardM, card_hermA_four ha hFcard])
  refine ⟨j, AddEquiv.ofBijective f hbij, fun g w => ?_⟩
  show (f (π g w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
  rw [hf, hequiv, tw_submatrix]
  rfl

end Std

end CFSG.Quasithin.B45Sp4
