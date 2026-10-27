module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUS5

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.RootSystem CFSG.Assembly CFSG.StandardType.RCKC1 CFSG.Open

abbrev SUF : Type := GaloisField 2 (2 * 1)

noncomputable abbrev SUσ : SUF ≃+* SUF := unitaryInvolution SUF 2 1

abbrev SUG (k : ℕ) : Type := ↥(Unitary.SU SUσ k)

variable {k : ℕ}

private theorem su_card : Nat.card SUF = 4 := by
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

private theorem su_card_sq : Nat.card SUF = (2 ^ 1) ^ 2 := by
  rw [su_card]; norm_num

private theorem su_sigma_involutive : ∀ c : SUF, SUσ (SUσ c) = c :=
  unitaryInvolution_involutive su_card_sq

private theorem su_sigma_apply (c : SUF) : SUσ c = c ^ 2 := by
  rw [SUσ, unitaryInvolution_apply]
  norm_num

private theorem su_algebraMap_sq (z : ZMod 2) :
    (algebraMap (ZMod 2) SUF z) ^ 2 = algebraMap (ZMod 2) SUF z := by
  rw [← map_pow]
  congr 1
  exact (by decide : ∀ z : ZMod 2, z ^ 2 = z) z

private theorem su_algebraMap_traceZero (z : ZMod 2) :
    algebraMap (ZMod 2) SUF z + SUσ (algebraMap (ZMod 2) SUF z) = 0 := by
  rw [su_sigma_apply, su_algebraMap_sq]
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  rw [← two_mul, h2, zero_mul]

private theorem su_algebraMap_injective : Function.Injective (algebraMap (ZMod 2) SUF) :=
  (algebraMap (ZMod 2) SUF).injective

theorem exists_suOmega : ∃ ω : SUF, ω ^ 2 + ω + 1 = 0 := by
  classical
  haveI : CharP SUF 2 := inferInstance
  have hcard : Nat.card SUF = 4 := su_card
  obtain ⟨ω, hω0, hω1, hω⟩ : ∃ ω : SUF, ω ≠ 0 ∧ ω ≠ 1 ∧ ω * ω = ω + 1 := by
    have : Fintype SUF := Fintype.ofFinite SUF
    obtain ⟨ω, hω0, hω1⟩ : ∃ ω : SUF, ω ≠ 0 ∧ ω ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset SUF) ⊆ {0, 1} := fun x _ => by
        by_cases hx : x = 0
        · simp [hx]
        · simp [hcon x hx]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at h1
      have h2 : ({0, 1} : Finset SUF).card ≤ 2 := Finset.card_le_two
      omega
    refine ⟨ω, hω0, hω1, ?_⟩
    have h3 : ω ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one ω hω0
      rwa [← Nat.card_eq_fintype_card, hcard] at this
    have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
    have h4 : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (sub_eq_zero.1 h5) hω1
    · linear_combination h5 - (ω + 1) * h2
  refine ⟨ω, ?_⟩
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  linear_combination hω + (ω + 1) * h2

noncomputable def suOmega : SUF := exists_suOmega.choose

theorem suOmega_spec : suOmega ^ 2 + suOmega + 1 = 0 := exists_suOmega.choose_spec

private theorem suOmega_ne_zero : suOmega ≠ 0 := by
  intro h
  have hspec := suOmega_spec
  rw [h] at hspec
  norm_num at hspec

private theorem suOmega_ne_one : suOmega ≠ 1 := by
  intro h
  have hspec := suOmega_spec
  rw [h] at hspec
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  norm_num at hspec
  have h3 : (3 : SUF) = 1 := by
    rw [show (3 : SUF) = 2 + 1 by norm_num, h2, zero_add]
  rw [h3] at hspec
  exact one_ne_zero hspec

private theorem suOmega_sq : suOmega ^ 2 = suOmega + 1 := by
  have h := suOmega_spec
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  linear_combination h - (suOmega + 1) * h2

private noncomputable def suB (v : Fin 4 → ZMod 2) : SUF :=
  algebraMap (ZMod 2) SUF (v 1) + algebraMap (ZMod 2) SUF (v 2) * suOmega

private theorem suB_add (v w : Fin 4 → ZMod 2) : suB (v + w) = suB v + suB w := by
  simp only [suB, Pi.add_apply, map_add, add_mul]
  ring

@[expose] def sI0 (hk : 4 ≤ k) : Fin k := ⟨0, by omega⟩

@[expose] def sI1 (hk : 4 ≤ k) : Fin k := ⟨1, by omega⟩

private theorem su_sI0_ne_sI1 (hk : 4 ≤ k) : sI0 hk ≠ sI1 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, sI1] at hv

private theorem su_rev_sI0_ne_sI0 (hk : 4 ≤ k) : Fin.rev (sI0 hk) ≠ sI0 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, Fin.val_rev] at hv
  omega

private theorem su_rev_sI0_ne_sI1 (hk : 4 ≤ k) : Fin.rev (sI0 hk) ≠ sI1 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, sI1, Fin.val_rev] at hv
  omega

private theorem su_rev_sI1_ne_sI0 (hk : 4 ≤ k) : Fin.rev (sI1 hk) ≠ sI0 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, sI1, Fin.val_rev] at hv
  omega

private theorem su_rev_sI1_ne_sI1 (hk : 4 ≤ k) : Fin.rev (sI1 hk) ≠ sI1 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI1, Fin.val_rev] at hv
  omega

private theorem su_rev_sI0_ne_rev_sI1 (hk : 4 ≤ k) :
    Fin.rev (sI0 hk) ≠ Fin.rev (sI1 hk) := fun h => su_sI0_ne_sI1 hk (Fin.rev_injective h)

private theorem su_sI0_ne_rev_sI0 (hk : 4 ≤ k) : sI0 hk ≠ Fin.rev (sI0 hk) :=
  (su_rev_sI0_ne_sI0 hk).symm

private theorem su_sI0_ne_rev_sI1 (hk : 4 ≤ k) : sI0 hk ≠ Fin.rev (sI1 hk) :=
  (su_rev_sI1_ne_sI0 hk).symm

private theorem su_sI1_ne_sI0 (hk : 4 ≤ k) : sI1 hk ≠ sI0 hk :=
  (su_sI0_ne_sI1 hk).symm

private theorem su_sI1_ne_rev_sI0 (hk : 4 ≤ k) : sI1 hk ≠ Fin.rev (sI0 hk) :=
  (su_rev_sI0_ne_sI1 hk).symm

private theorem su_sI1_ne_rev_sI1 (hk : 4 ≤ k) : sI1 hk ≠ Fin.rev (sI1 hk) :=
  (su_rev_sI1_ne_sI1 hk).symm

private theorem su_rev_sI1_ne_rev_sI0 (hk : 4 ≤ k) :
    Fin.rev (sI1 hk) ≠ Fin.rev (sI0 hk) := (su_rev_sI0_ne_rev_sI1 hk).symm

@[expose] noncomputable def suCorner (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    Matrix (Fin k) (Fin k) SUF :=
  1 + Matrix.single (sI0 hk) (Fin.rev (sI0 hk)) (algebraMap (ZMod 2) SUF (v 0))
    + Matrix.single (sI0 hk) (Fin.rev (sI1 hk))
        (algebraMap (ZMod 2) SUF (v 1) + algebraMap (ZMod 2) SUF (v 2) * suOmega)
    + Matrix.single (sI1 hk) (Fin.rev (sI0 hk))
        (SUσ (algebraMap (ZMod 2) SUF (v 1) + algebraMap (ZMod 2) SUF (v 2) * suOmega))
    + Matrix.single (sI1 hk) (Fin.rev (sI1 hk)) (algebraMap (ZMod 2) SUF (v 3))

private noncomputable def suN (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    Matrix (Fin k) (Fin k) SUF :=
  Matrix.single (sI0 hk) (Fin.rev (sI0 hk)) (algebraMap (ZMod 2) SUF (v 0))
    + Matrix.single (sI0 hk) (Fin.rev (sI1 hk)) (suB v)
    + Matrix.single (sI1 hk) (Fin.rev (sI0 hk)) (SUσ (suB v))
    + Matrix.single (sI1 hk) (Fin.rev (sI1 hk)) (algebraMap (ZMod 2) SUF (v 3))

private theorem suCorner_eq_one_add_suN (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v = 1 + suN hk v := by
  simp only [suCorner, suN, suB]
  abel

private theorem suN_add (hk : 4 ≤ k) (v w : Fin 4 → ZMod 2) :
    suN hk (v + w) = suN hk v + suN hk w := by
  simp only [suN, suB_add, Pi.add_apply, map_add, Matrix.single_add]
  abel

private theorem suN_mul_zero (hk : 4 ≤ k) (v w : Fin 4 → ZMod 2) :
    suN hk v * suN hk w = 0 := by
  have h00 := su_rev_sI0_ne_sI0 hk
  have h01 := su_rev_sI0_ne_sI1 hk
  have h10 := su_rev_sI1_ne_sI0 hk
  have h11 := su_rev_sI1_ne_sI1 hk
  simp only [suN, Matrix.add_mul, Matrix.mul_add, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, single_mul_single_of_ne _ _ _ _ h00, single_mul_single_of_ne _ _ _ _ h01,
    single_mul_single_of_ne _ _ _ _ h10, single_mul_single_of_ne _ _ _ _ h11]

private theorem suCorner_mul (hk : 4 ≤ k) (v w : Fin 4 → ZMod 2) :
    suCorner hk v * suCorner hk w = suCorner hk (v + w) := by
  rw [suCorner_eq_one_add_suN hk v, suCorner_eq_one_add_suN hk w,
    suCorner_eq_one_add_suN hk (v + w), suN_add hk v w]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, suN_mul_zero hk v w]
  abel

private theorem suCorner_apply_00 (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v (sI0 hk) (Fin.rev (sI0 hk)) = algebraMap (ZMod 2) SUF (v 0) := by
  rw [suCorner_eq_one_add_suN hk v]
  simp only [Matrix.add_apply, Matrix.one_apply, suN, Matrix.single_apply]
  simp [su_sI0_ne_sI1 hk, su_sI1_ne_sI0 hk, su_rev_sI0_ne_sI0 hk, su_sI0_ne_rev_sI0 hk,
    su_rev_sI1_ne_sI0 hk, su_sI1_ne_rev_sI0 hk, su_rev_sI0_ne_rev_sI1 hk,
    su_rev_sI1_ne_rev_sI0 hk]

private theorem suCorner_apply_01 (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v (sI0 hk) (Fin.rev (sI1 hk)) = suB v := by
  rw [suCorner_eq_one_add_suN hk v]
  simp only [Matrix.add_apply, Matrix.one_apply, suN, Matrix.single_apply]
  simp [su_sI0_ne_sI1 hk, su_sI1_ne_sI0 hk, su_rev_sI0_ne_sI1 hk, su_sI0_ne_rev_sI1 hk,
    su_rev_sI1_ne_sI0 hk, su_sI1_ne_rev_sI0 hk, su_rev_sI0_ne_rev_sI1 hk,
    su_rev_sI1_ne_rev_sI0 hk]

private theorem suCorner_apply_10 (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v (sI1 hk) (Fin.rev (sI0 hk)) = SUσ (suB v) := by
  rw [suCorner_eq_one_add_suN hk v]
  simp only [Matrix.add_apply, Matrix.one_apply, suN, Matrix.single_apply]
  simp [su_sI0_ne_sI1 hk, su_sI1_ne_sI0 hk, su_rev_sI0_ne_sI0 hk, su_sI0_ne_rev_sI0 hk,
    su_rev_sI0_ne_sI1 hk, su_sI1_ne_rev_sI0 hk, su_rev_sI0_ne_rev_sI1 hk,
    su_rev_sI1_ne_rev_sI0 hk]

private theorem suCorner_apply_11 (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v (sI1 hk) (Fin.rev (sI1 hk)) = algebraMap (ZMod 2) SUF (v 3) := by
  rw [suCorner_eq_one_add_suN hk v]
  simp only [Matrix.add_apply, Matrix.one_apply, suN, Matrix.single_apply]
  simp [su_sI0_ne_sI1 hk, su_sI1_ne_sI0 hk, su_rev_sI1_ne_sI1 hk, su_sI1_ne_rev_sI1 hk,
    su_rev_sI1_ne_sI0 hk, su_sI1_ne_rev_sI0 hk, su_rev_sI0_ne_rev_sI1 hk,
    su_rev_sI1_ne_rev_sI0 hk]

private theorem su_neg_eq (x : SUF) : -x = x := by
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  have hxx : x + x = 0 := by rw [← two_mul, h2, zero_mul]
  exact neg_eq_of_add_eq_zero_left hxx

private noncomputable def suTZ (z : ZMod 2) : traceZero SUσ :=
  ⟨algebraMap (ZMod 2) SUF z, su_algebraMap_traceZero z⟩

private noncomputable def suRootH (hk : 4 ≤ k) : Multiplicative SUF →* SUG k :=
  rootHom SUσ su_sigma_involutive (su_sI0_ne_rev_sI1 hk) (su_sI0_ne_rev_sI0 hk)
    (by rw [Fin.rev_rev]; exact su_rev_sI1_ne_sI1 hk)

private noncomputable def suLongH0 (hk : 4 ≤ k) : Multiplicative (traceZero SUσ) →* SUG k :=
  longRootHom SUσ (su_sI0_ne_rev_sI0 hk)

private noncomputable def suLongH1 (hk : 4 ≤ k) : Multiplicative (traceZero SUσ) →* SUG k :=
  longRootHom SUσ (su_sI1_ne_rev_sI1 hk)

private noncomputable def suPhi (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) : SUG k :=
  suLongH0 hk (Multiplicative.ofAdd (suTZ (v 0))) *
    suRootH hk (Multiplicative.ofAdd (suB v)) *
    suLongH1 hk (Multiplicative.ofAdd (suTZ (v 3)))

private theorem suPhi_val (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    ((suPhi hk v : SUG k) : GL (Fin k) SUF).1 =
      longRootMatrix (F := SUF) (sI0 hk) (algebraMap (ZMod 2) SUF (v 0)) *
        rootMatrix SUσ (sI0 hk) (Fin.rev (sI1 hk)) (suB v) *
        longRootMatrix (F := SUF) (sI1 hk) (algebraMap (ZMod 2) SUF (v 3)) := by
  simp only [suPhi, suLongH0, suLongH1, suRootH, Subgroup.coe_mul, Units.val_mul,
    coe_longRootHom, coe_rootHom, toAdd_ofAdd, suTZ]

private theorem suCorner_eq_roots (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v =
      longRootMatrix (F := SUF) (sI0 hk) (algebraMap (ZMod 2) SUF (v 0)) *
        rootMatrix SUσ (sI0 hk) (Fin.rev (sI1 hk)) (suB v) *
        longRootMatrix (F := SUF) (sI1 hk) (algebraMap (ZMod 2) SUF (v 3)) := by
  have h00 := su_rev_sI0_ne_sI0 hk
  have h01 := su_rev_sI0_ne_sI1 hk
  have h11 := su_rev_sI1_ne_sI1 hk
  rw [longRootMatrix, rootMatrix, longRootMatrix, sub_eq_add_neg, Matrix.single_neg, su_neg_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Fin.rev_rev, single_mul_single_of_ne _ _ _ _ h00,
    single_mul_single_of_ne _ _ _ _ h01, single_mul_single_of_ne _ _ _ _ h11]
  rw [suCorner_eq_one_add_suN hk v]
  simp only [suN, suB]
  abel

private theorem su_range_inv {x : SUF} (hx : x ∈ Set.range (algebraMap (ZMod 2) SUF)) :
    x⁻¹ ∈ Set.range (algebraMap (ZMod 2) SUF) := by
  obtain ⟨z, rfl⟩ := hx
  by_cases h : z = 0
  · subst h
    exact ⟨0, by simp⟩
  · refine ⟨z⁻¹, ?_⟩
    have hz : algebraMap (ZMod 2) SUF z * algebraMap (ZMod 2) SUF z⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h, map_one]
    exact (inv_eq_of_mul_eq_one_right hz).symm

private theorem suOmega_notMem_range : suOmega ∉ Set.range (algebraMap (ZMod 2) SUF) := by
  rintro ⟨z, hz⟩
  have hzspec : z ^ 2 + z + 1 = 0 := by
    apply su_algebraMap_injective
    rw [map_add, map_add, map_pow, map_one, map_zero, hz]
    exact suOmega_spec
  exact (by decide : ∀ z : ZMod 2, z ^ 2 + z + 1 ≠ 0) z hzspec

private theorem suB_inj {a b a' b' : ZMod 2}
    (h : algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega =
      algebraMap (ZMod 2) SUF a' + algebraMap (ZMod 2) SUF b' * suOmega) :
    a = a' ∧ b = b' := by
  have hzero : algebraMap (ZMod 2) SUF (a - a') +
      algebraMap (ZMod 2) SUF (b - b') * suOmega = 0 := by
    rw [map_sub, map_sub]
    linear_combination h
  have hb : b - b' = 0 := by
    by_contra hne
    have hBne : algebraMap (ZMod 2) SUF (b - b') ≠ 0 := fun h0 =>
      hne (su_algebraMap_injective (by rw [h0, map_zero]))
    have hmem : suOmega ∈ Set.range (algebraMap (ZMod 2) SUF) := by
      have hB : algebraMap (ZMod 2) SUF (b - b') * suOmega =
          -algebraMap (ZMod 2) SUF (a - a') := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzero
      obtain ⟨c, hc⟩ := su_range_inv (x := algebraMap (ZMod 2) SUF (b - b')) ⟨b - b', rfl⟩
      refine ⟨c * (-(a - a')), ?_⟩
      rw [map_mul, map_neg, hc]
      calc (algebraMap (ZMod 2) SUF (b - b'))⁻¹ * -(algebraMap (ZMod 2) SUF (a - a'))
          = (algebraMap (ZMod 2) SUF (b - b'))⁻¹ *
              (algebraMap (ZMod 2) SUF (b - b') * suOmega) := by rw [hB]
        _ = suOmega := inv_mul_cancel_left₀ hBne suOmega
    exact suOmega_notMem_range hmem
  have ha : a - a' = 0 := by
    have hA : algebraMap (ZMod 2) SUF (a - a') = 0 := by
      have hthis := hzero
      rw [hb, map_zero, zero_mul, add_zero] at hthis
      exact hthis
    exact su_algebraMap_injective (by rw [hA, map_zero])
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩

theorem exists_suOmega_coordinates (c : SUF) :
    ∃ a b : ZMod 2,
      algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega = c := by
  classical
  haveI : Fintype SUF := Fintype.ofFinite SUF
  let f : ZMod 2 × ZMod 2 → SUF := fun p =>
    algebraMap (ZMod 2) SUF p.1 + algebraMap (ZMod 2) SUF p.2 * suOmega
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨ha, hb⟩ := suB_inj h
    exact Prod.ext ha hb
  have hcard : Fintype.card (ZMod 2 × ZMod 2) = Fintype.card SUF := by
    rw [Fintype.card_prod, ZMod.card, ← Nat.card_eq_fintype_card, su_card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := hbij.2 c
  exact ⟨a, b, rfl⟩

theorem exists_suZ (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    ∃ g : SUG k, ((g : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) = suCorner hk v := by
  refine ⟨suPhi hk v, ?_⟩
  rw [suPhi_val]
  exact (suCorner_eq_roots hk v).symm

noncomputable def suZ (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) : SUG k := (exists_suZ hk v).choose

theorem suZ_val (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    ((suZ hk v : SUG k) : GL (Fin k) SUF).1 = suCorner hk v :=
  (exists_suZ hk v).choose_spec

theorem suZ_add (hk : 4 ≤ k) (v w : Fin 4 → ZMod 2) :
    suZ hk v * suZ hk w = suZ hk (v + w) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, suZ_val, suCorner_mul]

theorem suZ_zero (hk : 4 ≤ k) : suZ hk 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [suZ_val]
  simp [suCorner, suN, suB]

theorem suZ_injective (hk : 4 ≤ k) : Function.Injective (suZ hk) := by
  intro v w h
  have hm : suCorner hk v = suCorner hk w := by
    have := congrArg (fun g : SUG k => ((g : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) h
    rwa [suZ_val, suZ_val] at this
  have h0 : algebraMap (ZMod 2) SUF (v 0) = algebraMap (ZMod 2) SUF (w 0) := by
    have := congrFun (congrFun hm (sI0 hk)) (Fin.rev (sI0 hk))
    rwa [suCorner_apply_00, suCorner_apply_00] at this
  have hb : suB v = suB w := by
    have := congrFun (congrFun hm (sI0 hk)) (Fin.rev (sI1 hk))
    rwa [suCorner_apply_01, suCorner_apply_01] at this
  have h3 : algebraMap (ZMod 2) SUF (v 3) = algebraMap (ZMod 2) SUF (w 3) := by
    have := congrFun (congrFun hm (sI1 hk)) (Fin.rev (sI1 hk))
    rwa [suCorner_apply_11, suCorner_apply_11] at this
  have h12 : v 1 = w 1 ∧ v 2 = w 2 := suB_inj (by simpa only [suB] using hb)
  funext i
  fin_cases i
  · exact su_algebraMap_injective h0
  · exact h12.1
  · exact h12.2
  · exact su_algebraMap_injective h3

private noncomputable def suHom (hk : 4 ≤ k) :
    Multiplicative (Fin 4 → ZMod 2) →* SUG k :=
  MonoidHom.mk' (fun v => suZ hk v.toAdd) (fun v w => (suZ_add hk v.toAdd w.toAdd).symm)

private theorem suHom_apply (hk : 4 ≤ k) (v : Multiplicative (Fin 4 → ZMod 2)) :
    suHom hk v = suZ hk v.toAdd := rfl

private theorem suHom_injective (hk : 4 ≤ k) : Function.Injective (suHom hk) := by
  intro v w h
  have h' : suZ hk v.toAdd = suZ hk w.toAdd := h
  exact Multiplicative.toAdd.injective (suZ_injective hk h')

@[expose] noncomputable def suZ0 (hk : 4 ≤ k) : Subgroup (SUG k) :=
  (MonoidHom.mk' (fun v : Multiplicative (Fin 4 → ZMod 2) => suZ hk v.toAdd)
    (fun v w => (suZ_add hk v.toAdd w.toAdd).symm)).range

theorem card_suZ0 (hk : 4 ≤ k) : Nat.card (suZ0 hk) = 16 := by
  have hZ : suZ0 hk = (suHom hk).range := rfl
  rw [hZ, ← Nat.card_congr (MonoidHom.ofInjective (suHom_injective hk)).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  norm_num [Fintype.card_fun, ZMod.card]

theorem isElemAbelian_suZ0 (hk : 4 ≤ k) : IsElemAbelian 2 (suZ0 hk) := by
  change IsMulCommutative (suZ0 hk) ∧ ∀ x ∈ suZ0 hk, x ^ 2 = 1
  constructor
  · refine ⟨⟨?_⟩⟩
    intro x y
    obtain ⟨v, hv⟩ := x.2
    obtain ⟨w, hw⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv, ← hw]
    change suZ hk v.toAdd * suZ hk w.toAdd = suZ hk w.toAdd * suZ hk v.toAdd
    rw [suZ_add, suZ_add, add_comm]
  · intro x hx
    obtain ⟨v, hv⟩ := hx
    rw [← hv]
    change (suZ hk v.toAdd) ^ 2 = 1
    rw [sq, suZ_add]
    have hv2 : v.toAdd + v.toAdd = 0 := by
      funext i
      exact (by decide : ∀ a : ZMod 2, a + a = 0) (v.toAdd i)
    rw [hv2, suZ_zero]

end CFSG.StandardType.RCKK1IIISU
