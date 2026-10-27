module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDCommute
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCBlockField
public import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

abbrev PSUF (g : ℕ) : Type := GaloisField 2 (2 * (g + 1))

noncomputable abbrev PSUσ (g : ℕ) : PSUF g ≃+* PSUF g :=
  CFSG.LieType.BorelTits.unitaryInvolution (PSUF g) 2 (g + 1)

noncomputable abbrev PSUj (n g : ℕ) : ↥(Unitary.SU (PSUσ g) n) →* GL (Fin n) (PSUF g) :=
  (Unitary.SU (PSUσ g) n).subtype

theorem card_PSUF (g : ℕ) : Nat.card (PSUF g) = (2 ^ (g + 1)) ^ 2 :=
  CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)

section GU

variable {F : Type} [Field F]

@[expose] def GUsub (σ : F ≃+* F) (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {A | Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
    (A : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n}
  mul_mem' {A B} hA hB := by
    have hA' : Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
      (A : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := hA
    have hB' : Unitary.conjTr σ (B : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
      (B : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := hB
    have e : Unitary.conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
        Unitary.antidiag n * ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        Unitary.conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
            (A : Matrix (Fin n) (Fin n) F)) * (B : Matrix (Fin n) (Fin n) F) := by
      rw [Unitary.conjTr_mul]
      simp only [Matrix.mul_assoc]
    change Unitary.conjTr σ (((A * B : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      Unitary.antidiag n * (((A * B : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) =
        Unitary.antidiag n
    rw [Units.val_mul, e, hA', hB']
  one_mem' := by
    change Unitary.conjTr σ (((1 : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      Unitary.antidiag n * (((1 : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) =
        Unitary.antidiag n
    simp [Unitary.conjTr_one]
  inv_mem' {A} hA := by
    have hA' : Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
      (A : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := hA
    have hAB : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have key : Unitary.conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) *
        (Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
          (A : Matrix _ _ F)) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) =
        Unitary.conjTr σ ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) *
          Unitary.antidiag n *
          ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) := by
      rw [Unitary.conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [hA', hAB, Unitary.conjTr_one, Matrix.one_mul, Matrix.mul_one] at key
    exact key

theorem mem_GUsub {σ : F ≃+* F} {n : ℕ} {A : GL (Fin n) F} :
    A ∈ GUsub σ n ↔ Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
      (A : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := Iff.rfl

end GU

section Lifts

variable {X : Type} [Group X] {n g p : ℕ}

structure PSULiftHyp (n g : ℕ) (ψ : ↥(Unitary.SU (PSUσ g) n) →* X) (p : ℕ) (B : Subgroup X) :
    Prop where
  adm : StatedLieAdmissible .PSU n 2 (g + 1)
  ker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (PSUσ g) n)
  prime : p.Prime
  ne_two : p ≠ 2
  norm : B ≤ Subgroup.normalizer (ψ.range : Set X)
  diag : ∀ b ∈ B, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF g) n) ψ b
  elem : IsElemAbelian p B
  card4 : p ^ 4 ≤ Nat.card B
  faithful : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥
  hN : p ∣ 2 ^ (g + 1) + 1 → p ^ (n - 3) ≤ Nat.card B

variable {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

theorem PSULiftHyp.three_le (hH : PSULiftHyp n g ψ p B) : 3 ≤ n := hH.adm.2.2.1

theorem PSULiftHyp.one_le (hH : PSULiftHyp n g ψ p B) : 1 ≤ g + 1 := hH.adm.2.1

theorem PSULiftHyp.pow_eq_one (hH : PSULiftHyp n g ψ p B) {b : X} (hb : b ∈ B) : b ^ p = 1 :=
  hH.elem.2 b hb

theorem PSULiftHyp.comm (hH : PSULiftHyp n g ψ p B) {b b' : X} (hb : b ∈ B) (hb' : b' ∈ B) :
    b * b' = b' * b :=
  congrArg (fun x : ↥B => (x : X))
    (isMulCommutative_iff.mp hH.elem.1 ⟨b, hb⟩ ⟨b', hb'⟩)

theorem PSULiftHyp.commute_lifts (hH : PSULiftHyp n g ψ p B) {b b' : X} (hb : b ∈ B)
    (hb' : b' ∈ B) {s s' : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s b)
    (hs' : IsGLLift (PSUj n g) ψ s' b') : Commute s s' :=
  isGLLift_commute_PSU (card_PSUF g) n ψ hH.ker hH.adm hH.prime hH.ne_two hH.norm hH.diag
    hH.elem hH.card4 (fun hd => ⟨hH.faithful, hH.hN hd⟩) hb hb' hs hs'

theorem PSULiftHyp.exists_lift (hH : PSULiftHyp n g ψ p B) {b : X} (hb : b ∈ B) :
    ∃ s ∈ GUsub (PSUσ g) n, IsGLLift (PSUj n g) ψ s b := by
  obtain ⟨s, hs, hsl⟩ := exists_isGLLift_PSU (card_PSUF g) n hH.three_le ψ hH.ker (hH.norm hb)
    (hH.diag b hb)
  exact ⟨s, hs, hsl⟩

private theorem psu_odd_card_sub_one {F : Type} {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) : Odd (Nat.card F - 1) := by
  have hpowF : Nat.card F = 2 * 2 ^ (2 * f - 1) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hc
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm f 2]
      _ = 2 * 2 ^ (2 * f - 1) := by
            conv_lhs => rw [show 2 * f = (2 * f - 1) + 1 by omega]
            rw [pow_add, pow_one]
            ring
  rw [hpowF]
  refine ⟨2 ^ (2 * f - 1) - 1, ?_⟩
  have hX : 1 ≤ 2 ^ (2 * f - 1) := Nat.one_le_two_pow
  omega

theorem PSULiftHyp.lift_pow_scalar_odd (hH : PSULiftHyp n g ψ p B) {b : X} (hb : b ∈ B)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s b) :
    Odd (orderOf s) ∧ ∃ c : PSUF g, c ≠ 0 ∧ (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p =
      Matrix.scalar (Fin n) c := by
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hsp : IsGLLift (PSUj n g) ψ (s ^ p) 1 := by
    have h := hs.pow p
    rwa [hH.pow_eq_one hb] at h
  obtain ⟨c, hc_eq⟩ := isGLLift_unique_PSU (card_PSUF g) n ψ hH.ker hsp isGLLift_one
  have hsmat : (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) c := by
    have h := hc_eq
    rw [inv_one, one_mul] at h
    simpa only [Units.val_pow_eq_pow_val] using h
  have hcne : c ≠ 0 := by
    have hunit : IsUnit ((s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p) := IsUnit.pow p ⟨s, rfl⟩
    have hm : IsUnit ((Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) (PSUF g)).det) := by
      rw [← hsmat]
      exact (Matrix.isUnit_iff_isUnit_det
        (A := (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p)).mp hunit
    have hdet : (Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) (PSUF g)).det = c ^ n := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hdet] at hm
    have hn0 : n ≠ 0 := by have := hH.three_le; omega
    exact ((isUnit_pow_iff (a := c) (n := n) hn0).mp hm).ne_zero
  refine ⟨?_, c, hcne, hsmat⟩
  let u : (PSUF g)ˣ := Units.mk0 c hcne
  have hspu : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hsmat, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hpow1 : s ^ (p * orderOf u) = 1 := by
    rw [pow_mul, hspu, ← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf s ∣ p * orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  have hoddF : Odd (Nat.card (PSUF g) - 1) := psu_odd_card_sub_one (card_PSUF g) hH.one_le
  have hu_pow : u ^ (Nat.card (PSUF g) - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (u : PSUF g) (Units.ne_zero u)
  have hodd_u : Odd (orderOf u) :=
    Odd.of_dvd_nat hoddF (orderOf_dvd_iff_pow_eq_one.mpr hu_pow)
  have hodd_p : Odd p := hH.prime.odd_of_ne_two hH.ne_two
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hodd_p, hodd_u⟩) hdvd

end Lifts

section EGroup

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

noncomputable abbrev psuE (ψ : ↥(Unitary.SU (PSUσ g) n) →* X) (B : Subgroup X) :
    Subgroup (GL (Fin n) (PSUF g)) :=
  liftGroup (j := PSUj n g) (Subgroup.subtype_injective _) ψ (GUsub (PSUσ g) n) B

theorem mem_psuE {t : GL (Fin n) (PSUF g)} :
    t ∈ psuE ψ B ↔ t ∈ GUsub (PSUσ g) n ∧ ∃ b ∈ B, IsGLLift (PSUj n g) ψ t b := Iff.rfl

theorem PSULiftHyp.psuE_comm (hH : PSULiftHyp n g ψ p B) {t t' : GL (Fin n) (PSUF g)}
    (ht : t ∈ psuE ψ B) (ht' : t' ∈ psuE ψ B) : t * t' = t' * t := by
  obtain ⟨-, b, hb, hl⟩ := ht
  obtain ⟨-, b', hb', hl'⟩ := ht'
  exact (hH.commute_lifts hb hb' hl hl').eq

theorem PSULiftHyp.psuE_pow_scalar_odd (hH : PSULiftHyp n g ψ p B) {t : GL (Fin n) (PSUF g)}
    (ht : t ∈ psuE ψ B) : Odd (orderOf t) ∧ ∃ c : PSUF g, c ≠ 0 ∧
      (t : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) c := by
  obtain ⟨-, b, hb, hl⟩ := ht
  exact hH.lift_pow_scalar_odd hb hl

noncomputable def PSULiftHyp.phi (hH : PSULiftHyp n g ψ p B) : ↥(psuE ψ B) →* B :=
  liftHom (hj := Subgroup.subtype_injective _) (ψ := ψ) hH.faithful
    (fun _ hb _ hb' => hH.comm hb hb')

theorem PSULiftHyp.isGLLift_phi (hH : PSULiftHyp n g ψ p B) (t : ↥(psuE ψ B)) :
    IsGLLift (PSUj n g) ψ (t : GL (Fin n) (PSUF g)) (hH.phi t : X) :=
  isGLLift_liftHom (hj := Subgroup.subtype_injective _) hH.faithful
    (fun _ hb _ hb' => hH.comm hb hb') t

theorem PSULiftHyp.phi_surjective (hH : PSULiftHyp n g ψ p B) :
    Function.Surjective hH.phi :=
  liftHom_surjective (hj := Subgroup.subtype_injective _) (Q := GUsub (PSUσ g) n) hH.faithful
    (fun _ hb _ hb' => hH.comm hb hb') (fun _ hb => hH.exists_lift hb)

theorem PSULiftHyp.scalar_of_isGLLift_one (hH : PSULiftHyp n g ψ p B)
    {t : GL (Fin n) (PSUF g)} (ht : IsGLLift (PSUj n g) ψ t 1) :
    ∃ c : PSUF g, (t : Matrix (Fin n) (Fin n) (PSUF g)) = Matrix.scalar (Fin n) c := by
  obtain ⟨c, hc⟩ := isGLLift_unique_PSU (card_PSUF g) n ψ hH.ker ht
    (isGLLift_one : IsGLLift (PSUj n g) ψ 1 1)
  exact ⟨c, by simpa using hc⟩

theorem PSULiftHyp.scalar_of_phi_eq_one (hH : PSULiftHyp n g ψ p B) {t : ↥(psuE ψ B)}
    (ht : hH.phi t = 1) :
    ∃ c : PSUF g, ((t : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      Matrix.scalar (Fin n) c :=
  hH.scalar_of_isGLLift_one
    ((liftHom_eq_one_iff (hj := Subgroup.subtype_injective _) hH.faithful
      (fun _ hb _ hb' => hH.comm hb hb') t).mp ht)

end EGroup

section BlockData

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

theorem PSUσ_involutive (g : ℕ) (x : PSUF g) : PSUσ g (PSUσ g x) = x :=
  CFSG.LieType.BorelTits.unitaryInvolution_involutive (card_PSUF g) x

theorem PSUantidiag_transpose_map (n g : ℕ) :
    Matrix.transpose ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).map
      (⇑(PSUσ g).toRingHom)) = Unitary.antidiag n := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply]
  have hanti : ∀ (a b : Fin n),
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) a b
      = if b = a.rev then 1 else 0 := fun a b => rfl
  rw [hanti j i, hanti i j]
  by_cases h : i = j.rev
  · have h2 : j = i.rev := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h2, map_one]
  · have h2 : j ≠ i.rev := by
      intro h2
      apply h
      rw [h2, Fin.rev_rev]
    rw [if_neg h, if_neg h2, map_zero]

theorem PSUantidiag_isUnit_det (n g : ℕ) :
    IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).det :=
  isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)

theorem mem_GUsub_iff {s : GL (Fin n) (PSUF g)} :
    s ∈ GUsub (PSUσ g) n ↔ Matrix.transpose ((s : Matrix (Fin n) (Fin n) (PSUF g)).map
      (⇑(PSUσ g).toRingHom)) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (PSUF g)) =
      Unitary.antidiag n := Iff.rfl

structure PSUBlock (ψ : ↥(Unitary.SU (PSUσ g) n) →* X) (B : Subgroup X)
    (S : Set (GL (Fin n) (PSUF g))) (ε e : Matrix (Fin n) (Fin n) (PSUF g)) : Prop where
  subE : ∀ s ∈ S, s ∈ psuE ψ B
  eps_prim : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
    (Algebra.adjoin (PSUF g) (Units.val '' S)) ε
  e_prim : IsPrimIdemIn (Algebra.adjoin (PSUF g) (Units.val '' S)) e
  ee : e * ε = e
  cases : e = ε ∨ (e ≠ ε ∧
    formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ≠ e ∧
    ε = e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)

variable {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}

theorem PSUBlock.S_comm (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e) :
    ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := fun s hs s' hs' =>
  hH.psuE_comm (hb.subE s hs) (hb.subE s' hs')

theorem PSUBlock.S_odd (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e) :
    ∀ s ∈ S, Odd (orderOf s) := fun s hs => (hH.psuE_pow_scalar_odd (hb.subE s hs)).1

theorem PSUBlock.E_comm_A (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e)
    {t : GL (Fin n) (PSUF g)} (ht : t ∈ psuE ψ B) :
    ∀ a ∈ Algebra.adjoin (PSUF g) (Units.val '' S),
      (t : Matrix (Fin n) (Fin n) (PSUF g)) * a = a * (t : Matrix (Fin n) (Fin n) (PSUF g)) := by
  refine commute_adjoin_of_commute_gens (fun s hs => ?_)
  have h := hH.psuE_comm ht (hb.subE s hs)
  have h' := congrArg (fun u : GL (Fin n) (PSUF g) => (u : Matrix (Fin n) (Fin n) (PSUF g))) h
  simpa [Units.val_mul] using h'

theorem PSUBlock.exists_mul_eps (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e)
    {t : GL (Fin n) (PSUF g)} (ht : t ∈ psuE ψ B) {a : Matrix (Fin n) (Fin n) (PSUF g)}
    (ha : a ∈ Algebra.adjoin (PSUF g) (Units.val '' S))
    (hta : (t : Matrix (Fin n) (Fin n) (PSUF g)) * e = a * e) :
    ∃ c ∈ Algebra.adjoin (PSUF g) (Units.val '' S),
      (t : Matrix (Fin n) (Fin n) (PSUF g)) * ε = c * ε := by
  rcases hb.cases with h | ⟨_, hpair, hε⟩
  · exact ⟨a, ha, by rw [← h]; exact hta⟩
  · rw [hε]
    have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
    exact exists_mem_mul_add_formAdj_eq_of_isometry (PSUσ g).toRingHom (PSUσ_involutive g)
      (PSUantidiag_isUnit_det n g) (PSUantidiag_transpose_map n g)
      (fun s hs => mem_GUsub_iff.mp (hb.subE s hs).1) (hb.S_comm hH) (hb.S_odd hH) hb.e_prim hpair
      (mem_GUsub_iff.mp ht.1) (hb.E_comm_A hH ht) ha hta

theorem PSUBlock.commute_glBlock (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e)
    {t : GL (Fin n) (PSUF g)} (ht : t ∈ psuE ψ B) {a : Matrix (Fin n) (Fin n) (PSUF g)}
    (ha : a ∈ Algebra.adjoin (PSUF g) (Units.val '' S))
    (hta : (t : Matrix (Fin n) (Fin n) (PSUF g)) * e = a * e)
    {u : ↥(Unitary.SU (PSUσ g) n)} (hu : u ∈ glBlockCentralizer (PSUj n g) S ε) :
    t * PSUj n g u = PSUj n g u * t := by
  obtain ⟨c, hc, htc⟩ := hb.exists_mul_eps hH ht ha hta
  have hu' : PSUj n g u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) := hu
  obtain ⟨hcent, hfix⟩ := hu'
  have huA : ∀ b ∈ Algebra.adjoin (PSUF g) (Units.val '' S),
      ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * b =
        b * ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
    refine commute_adjoin_of_commute_gens (fun s hs => ?_)
    have h := (Subgroup.mem_centralizer_iff.mp hcent) s hs
    have h' := congrArg (fun v : GL (Fin n) (PSUF g) => (v : Matrix (Fin n) (Fin n) (PSUF g))) h
    simpa [Units.val_mul] using h'.symm
  exact commute_of_blockScalar hb.eps_prim.1 hc (hb.E_comm_A hH ht) huA hfix htc

theorem PSUBlock.phi_commute (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e)
    {t : GL (Fin n) (PSUF g)} (ht : t ∈ psuE ψ B) {a : Matrix (Fin n) (Fin n) (PSUF g)}
    (ha : a ∈ Algebra.adjoin (PSUF g) (Units.val '' S))
    (hta : (t : Matrix (Fin n) (Fin n) (PSUF g)) * e = a * e)
    {u : ↥(Unitary.SU (PSUσ g) n)} (hu : u ∈ glBlockCentralizer (PSUj n g) S ε) :
    (hH.phi ⟨t, ht⟩ : X) * ψ u = ψ u * (hH.phi ⟨t, ht⟩ : X) := by
  obtain ⟨u', hj, hψ'⟩ := hH.isGLLift_phi ⟨t, ht⟩ u
  have hcomm := hb.commute_glBlock hH ht ha hta hu
  have hj' : PSUj n g u' = PSUj n g u := by
    rw [hj]
    change t * PSUj n g u * t⁻¹ = PSUj n g u
    rw [hcomm]
    group
  have hu'u : u' = u := Subgroup.subtype_injective _ hj'
  rw [hu'u] at hψ'
  set b : X := (hH.phi ⟨t, ht⟩ : X) with hbdef
  calc b * ψ u = b * (b⁻¹ * ψ u * b) := by rw [hψ']
    _ = ψ u * b := by group

theorem PSULiftHyp.exists_block [Finite X] (hH : PSULiftHyp n g ψ p B) {D J : Subgroup X}
    (hDB : D ≤ B) (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X))) :
    ∃ (S : Set (GL (Fin n) (PSUF g))) (ε e : Matrix (Fin n) (Fin n) (PSUF g))
      (J' : Subgroup ↥(Unitary.SU (PSUσ g) n)),
      (∀ s, s ∈ S ↔ (s ∈ GUsub (PSUσ g) n ∧ ∃ d ∈ D, IsGLLift (PSUj n g) ψ s d)) ∧
      PSUBlock ψ B S ε e ∧
      IsComponentOf J' ((Subgroup.centralizer S).comap (PSUj n g)) ∧
      IsComponentOf J'
        ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆ ∧
      J'.map ψ = J := by
  classical
  let P : GL (Fin n) (PSUF g) → Prop := fun s => s ∈ GUsub (PSUσ g) n
  have hlift : ∀ d ∈ D, ∃ s : GL (Fin n) (PSUF g), P s ∧ IsGLLift (PSUj n g) ψ s d := by
    intro d hd
    obtain ⟨s, hs, hsl⟩ := hH.exists_lift (hDB hd)
    exact ⟨s, hs, hsl⟩
  obtain ⟨J', hJ'c, hJ'm⟩ := StepA.exists_isComponentOf_comap_lift_of_isGLLift (PSUj n g)
    (Subgroup.subtype_injective _) ψ hH.ker P hJ hlift
  have hSE : ∀ s ∈ {s : GL (Fin n) (PSUF g) | P s ∧ ∃ d ∈ D, IsGLLift (PSUj n g) ψ s d},
      s ∈ psuE ψ B := fun s hs => ⟨hs.1, hs.2.choose, hDB hs.2.choose_spec.1, hs.2.choose_spec.2⟩
  have hSU : ∀ s ∈ {s : GL (Fin n) (PSUF g) | P s ∧ ∃ d ∈ D, IsGLLift (PSUj n g) ψ s d},
      Unitary.conjTr (PSUσ g) (s : Matrix (Fin n) (Fin n) (PSUF g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n := fun s hs => hs.1
  have hScomm : ∀ s ∈ {s : GL (Fin n) (PSUF g) | P s ∧ ∃ d ∈ D, IsGLLift (PSUj n g) ψ s d},
      ∀ s' ∈ {s : GL (Fin n) (PSUF g) | P s ∧ ∃ d ∈ D, IsGLLift (PSUj n g) ψ s d},
      Commute s s' := fun s hs s' hs' => hH.psuE_comm (hSE s hs) (hSE s' hs')
  obtain ⟨ε, hε, hcomp⟩ := exists_isComponentOf_glBlockCentralizer_PSU (f := g + 1) n _ hScomm
    hJ'c
  obtain ⟨e, he, hee, hcases⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSU n g _ hSU hScomm hε
  exact ⟨_, ε, e, J', fun s => Iff.rfl, ⟨hSE, hε, he, hee, hcases⟩, hJ'c, hcomp, hJ'm⟩

theorem PSUBlock.three_mul_blockDegree_le_rank [Finite X] (hH : PSULiftHyp n g ψ p B)
    (hb : PSUBlock ψ B S ε e) {D J : Subgroup X} (hDcard : Nat.card D = p ^ 2)
    (hjc : B ⊓ Subgroup.centralizer (J : Set X) = D)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ' : IsComponentOf J'
      ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆)
    (hJψ : J'.map ψ = J) :
    3 * blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e ≤ Matrix.rank e := by
  classical
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hS := hb.S_comm hH
  have hodd := hb.S_odd hH
  obtain ⟨hdpos, k, hk⟩ := exists_blockDegree_mul_eq_rank hS hodd hb.e_prim
  have hp0 : ((p : ℕ) : PSUF g) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff (PSUF g) 2 p] at h0
    exact hH.ne_two ((Nat.Prime.dvd_iff_eq hH.prime (by decide : (2 : ℕ) ≠ 1)).mp h0)
  obtain ⟨Γ₀, hΓ₀s, hΓ₀e, hidx⟩ := exists_subgroup_index_le_blockBound
    (psuE ψ B).subtype hS hodd hb.e_prim
    (fun γ a ha => hb.E_comm_A hH γ.2 a ha)
    (fun γ γ' => hH.psuE_comm γ.2 γ'.2) hp0
    (fun γ => (hH.psuE_pow_scalar_odd γ.2).2.imp fun c h => h.2)
  have hDle : D ≤ B := hjc ▸ inf_le_left
  have hker : hH.phi.ker ≤ Γ₀ := by
    intro γ hγ
    obtain ⟨c, hc⟩ := hH.scalar_of_phi_eq_one (MonoidHom.mem_ker.mp hγ)
    exact hΓ₀s γ c hc
  have hGεle : ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆ ≤
      glBlockCentralizer (PSUj n g) S ε := by
    rw [Subgroup.commutator_le]
    intro a ha b hb'
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb')
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb')
  have hmap : Γ₀.map hH.phi ≤ D.subgroupOf B := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [Subgroup.mem_subgroupOf, ← hjc]
    refine ⟨(hH.phi γ).2, ?_⟩
    change ((hH.phi γ : ↥B) : X) ∈ Subgroup.centralizer (J : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hJψ] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨a, ha, hae⟩ := hΓ₀e γ hγ
    exact (hb.phi_commute hH γ.2 ha hae (hGεle (hJ'.1 hu))).symm
  have hB := card_le_mul_of_surjective_of_index_le hH.phi hH.phi_surjective hker hmap hidx
  have hDcard' : Nat.card (D.subgroupOf B) = p ^ 2 := by
    rw [← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
  rw [hDcard'] at hB
  have hk' : Matrix.rank e / blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e = k := by
    rw [← hk]
    exact Nat.mul_div_cancel_left k hdpos
  rw [hk'] at hB
  have hp2 : 2 ≤ p := hH.prime.two_le
  have hpow : p ^ 4 ≤ p ^ (2 + (k - 1)) := by
    calc p ^ 4 ≤ Nat.card B := hH.card4
      _ ≤ p ^ 2 * p ^ (k - 1) := hB
      _ = p ^ (2 + (k - 1)) := by rw [pow_add]
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_le_pow_iff_right hp2).mp hpow
    omega
  calc 3 * blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e
      = blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e * 3 := by ring
    _ ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e * k :=
        Nat.mul_le_mul_left _ hk3
    _ = Matrix.rank e := hk

theorem mem_center_GL_of_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] {z : GL ι F}
    {c : F} (hz : (z : Matrix ι ι F) = Matrix.scalar ι c) : z ∈ Subgroup.center (GL ι F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz]
  exact ((Matrix.scalar_commute (n := ι) c (fun r' => Commute.all c r')
    (g : Matrix ι ι F)).eq).symm

theorem PSULiftHyp.false_of_not_pow [Finite X] (hH : PSULiftHyp n g ψ p B)
    (hpq : p ∣ 2 ^ (g + 1) + 1) {s : GL (Fin n) (PSUF g)} (hs : s ∈ psuE ψ B) {c : PSUF g}
    (hsc : (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) c)
    (hc : ∀ b : PSUF g, b ^ p ≠ c) : False := by
  classical
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hn3 := hH.three_le
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hS : ∀ a ∈ ({s} : Set (GL (Fin n) (PSUF g))), ∀ b ∈ ({s} : Set (GL (Fin n) (PSUF g))),
      Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst ha
    subst hb
    exact Commute.refl _
  have hodd : ∀ a ∈ ({s} : Set (GL (Fin n) (PSUF g))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact (hH.psuE_pow_scalar_odd hs).1
  have he := isPrimIdemIn_one_adjoin_singleton_of_not_pow hH.prime hsc hc
  have hd2 := two_le_blockDegree_one_adjoin_singleton_of_not_pow hH.prime hsc hc
  let τ : ↥B → ↥(psuE ψ B) := Function.surjInv hH.phi_surjective
  have hτ : ∀ b, hH.phi (τ b) = b := Function.surjInv_eq hH.phi_surjective
  let t : ↥B → GL (Fin n) (PSUF g) := fun b => ((τ b : ↥(psuE ψ B)) : GL (Fin n) (PSUF g))
  have hp0 : ((p : ℕ) : PSUF g) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff (PSUF g) 2 p] at h0
    exact hH.ne_two ((Nat.Prime.dvd_iff_eq hH.prime (by decide : (2 : ℕ) ≠ 1)).mp h0)
  have htA : ∀ i, ∀ a ∈ Algebra.adjoin (PSUF g)
      (Units.val '' ({s} : Set (GL (Fin n) (PSUF g)))),
      (t i : Matrix (Fin n) (Fin n) (PSUF g)) * a =
        a * (t i : Matrix (Fin n) (Fin n) (PSUF g)) := by
    intro i
    refine commute_adjoin_of_commute_gens (fun s' hs' => ?_)
    rw [Set.mem_singleton_iff] at hs'
    subst hs'
    have h := hH.psuE_comm (τ i).2 hs
    have h' := congrArg (fun u : GL (Fin n) (PSUF g) => (u : Matrix (Fin n) (Fin n) (PSUF g))) h
    simpa [Units.val_mul, t] using h'
  have htc : ∀ i j, t i * t j = t j * t i := fun i j => hH.psuE_comm (τ i).2 (τ j).2
  have htp : ∀ i, ∃ c' : PSUF g, c' ≠ 0 ∧
      (t i : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) c' :=
    fun i => (hH.psuE_pow_scalar_odd (τ i).2).2
  have hinj : ∀ i j (c' : PSUF g), c' ≠ 0 →
      (t i : Matrix (Fin n) (Fin n) (PSUF g)) * (1 : Matrix (Fin n) (Fin n) (PSUF g)) =
        c' • ((t j : Matrix (Fin n) (Fin n) (PSUF g)) * (1 : Matrix (Fin n) (Fin n) (PSUF g))) →
      i = j := by
    intro i j c' hc' h
    rw [Matrix.mul_one, Matrix.mul_one] at h
    let z : GL (Fin n) (PSUF g) := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c' hc')
    have hz : (z : Matrix (Fin n) (Fin n) (PSUF g)) = Matrix.scalar (Fin n) c' := by
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      rfl
    have hzc : z ∈ Subgroup.center (GL (Fin n) (PSUF g)) := mem_center_GL_of_scalar hz
    have htz : t i = z * t j := by
      apply Units.ext
      rw [Units.val_mul, hz, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
      exact h
    have h1 : IsGLLift (PSUj n g) ψ (t i) (i : X) := by
      have := hH.isGLLift_phi (τ i)
      rwa [hτ i] at this
    have h2 : IsGLLift (PSUj n g) ψ (t i) (j : X) := by
      rw [htz]
      have := hH.isGLLift_phi (τ j)
      rw [hτ j] at this
      exact IsGLLift.central_mul (j := PSUj n g) (ψ := ψ) this hzc
    exact Subtype.ext (IsGLLift.unique_of_faithful (Subgroup.subtype_injective _) hH.faithful
      i.2 j.2 h1 h2)
  have hcard := card_le_pow_rank_div_blockDegree t hS hodd he htA htc hH.prime hp0 htp hinj
  rw [Matrix.rank_one, Fintype.card_fin] at hcard
  have hdiv : n / blockDegree (Algebra.adjoin (PSUF g)
      (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) 1 ≤ n / 2 := Nat.div_le_div_left hd2
        (by norm_num)
  have hp2 : 2 ≤ p := hH.prime.two_le
  have hB4 : p ^ 4 ≤ p ^ (n / 2) :=
    calc p ^ 4 ≤ Nat.card B := hH.card4
      _ ≤ p ^ (n / blockDegree (Algebra.adjoin (PSUF g)
          (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) 1) := hcard
      _ ≤ p ^ (n / 2) := Nat.pow_le_pow_right (by omega) hdiv
  have hBn : p ^ (n - 3) ≤ p ^ (n / 2) :=
    calc p ^ (n - 3) ≤ Nat.card B := hH.hN hpq
      _ ≤ p ^ (n / blockDegree (Algebra.adjoin (PSUF g)
          (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) 1) := hcard
      _ ≤ p ^ (n / 2) := Nat.pow_le_pow_right (by omega) hdiv
  have h1 := (Nat.pow_le_pow_iff_right hp2).mp hB4
  have h2 := (Nat.pow_le_pow_iff_right hp2).mp hBn
  omega

end BlockData

end CFSG.StandardType.TableCRes
