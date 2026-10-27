module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity

import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Artinian.Ring

public section

namespace CFSG.StandardType.TableC

open CFSG.StandardType.ClassicalPosition

private lemma gbd_odd_orderOf_of_pow_prime {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : G} (hs : s ^ p = 1) : Odd (orderOf s) := by
  have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf s) hdvd with h1 | hp'
  · rw [h1]
    exact odd_one
  · rw [hp']
    exact hp.odd_of_ne_two hp2

private lemma gbd_pairwise_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
  rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
  have h := hS s hs s' hs'
  show (s : Matrix ι ι F) * (s' : Matrix ι ι F) =
    (s' : Matrix ι ι F) * (s : Matrix ι ι F)
  rw [← Units.val_mul, ← Units.val_mul, h]

private lemma gbd_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rcases hy with ⟨s', hs', rfl⟩
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s' hs' s hs).eq
    simpa [Units.val_mul] using h
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have ha' : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  have hgen2 : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := (Subalgebra.mem_centralizer_iff F).mp ha' (s : Matrix ι ι F) ⟨s, hs, rfl⟩
    exact h.symm
  have hA2 : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen2
  have hb' : b ∈ Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := hA2 hb
  exact (Subalgebra.mem_centralizer_iff F).mp hb' a (Set.mem_singleton a)

private noncomputable def gbd_adjointAlgEquiv {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    Algebra.adjoin F (Units.val '' S) ≃ₐ[F] Algebra.adjoin F (Units.val '' S) := by
  classical
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  have hcommP : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute :=
    gbd_pairwise_commute hS
  letI : CommRing A := Algebra.adjoinCommRingOfComm F hcommP
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin F hcommP
  have hmem : ∀ a : A, formAdj (RingHom.id F) G (a : Matrix ι ι F) ∈ A := by
    intro a
    exact Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU a.2
  let gfun : A → A := fun a => ⟨formAdj (RingHom.id F) G (a : Matrix ι ι F), hmem a⟩
  let f : A →ₐ[F] A :=
    { toFun := gfun
      map_one' := Subtype.ext (Geo.formAdj_one (RingHom.id F) hG)
      map_mul' := by
        intro a b
        apply Subtype.ext
        change formAdj (RingHom.id F) G ((a : Matrix ι ι F) * (b : Matrix ι ι F)) =
          formAdj (RingHom.id F) G (a : Matrix ι ι F) *
            formAdj (RingHom.id F) G (b : Matrix ι ι F)
        rw [Geo.formAdj_mul (RingHom.id F) hG]
        exact congrArg Subtype.val (mul_comm' (gfun b) (gfun a))
      map_zero' := Subtype.ext (by
        change formAdj (RingHom.id F) G (0 : Matrix ι ι F) = 0
        unfold formAdj
        rw [Matrix.map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
        rfl)
      map_add' := by
        intro a b
        apply Subtype.ext
        change formAdj (RingHom.id F) G ((a : Matrix ι ι F) + (b : Matrix ι ι F)) =
          formAdj (RingHom.id F) G (a : Matrix ι ι F) +
            formAdj (RingHom.id F) G (b : Matrix ι ι F)
        rw [Geo.formAdj_add]
      commutes' := by
        intro r
        apply Subtype.ext
        have h1 : ((algebraMap F A) r : Matrix ι ι F) = r • (1 : Matrix ι ι F) := by
          change (algebraMap F (Matrix ι ι F)) r = r • (1 : Matrix ι ι F)
          rw [Algebra.algebraMap_eq_smul_one]
        show formAdj (RingHom.id F) G (((algebraMap F A) r) : Matrix ι ι F) =
          ((algebraMap F A) r : Matrix ι ι F)
        rw [h1, Geo.formAdj_smul, Geo.formAdj_one (RingHom.id F) hG]
        rfl }
  have hff : f.comp f = AlgHom.id F A :=
    AlgHom.ext fun a => by
      apply Subtype.ext
      show formAdj (RingHom.id F) G (formAdj (RingHom.id F) G (a : Matrix ι ι F)) =
        (a : Matrix ι ι F)
      exact Geo.formAdj_formAdj (RingHom.id F) (fun _ => rfl) hG hGh (a : Matrix ι ι F)
  exact AlgEquiv.ofAlgHom f f hff hff

private lemma gbd_adjointAlgEquiv_apply_generator {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (s : GL ι F) (hs : s ∈ S) :
    (gbd_adjointAlgEquiv hG hGh hSU hS
        ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ :
      Algebra.adjoin F (Units.val '' S)) =
      ⟨((s⁻¹ : GL ι F) : Matrix ι ι F), by
        rw [← Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSU s hs)]
        exact Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU
          (Algebra.subset_adjoin ⟨s, hs, rfl⟩)⟩ := by
  apply Subtype.ext
  change formAdj (RingHom.id F) G (s : Matrix ι ι F) = ((s⁻¹ : GL ι F) : Matrix ι ι F)
  exact Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSU s hs)

private lemma gbd_formAdj_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) : formAdj (RingHom.id F) G (0 : Matrix ι ι F) = 0 := by
  unfold formAdj
  rw [Matrix.map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
  rfl

private lemma gbd_isPrimIdemIn_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) (formAdj (RingHom.id F) G e) := by
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  have hmem : formAdj (RingHom.id F) G e ∈ A :=
    Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU he.1
  refine ⟨hmem, ?_, ?_, ?_⟩
  · refine isIdempotentElem_iff.mpr ?_
    rw [← Geo.formAdj_mul (RingHom.id F) hG, he.2.1.eq]
  · intro h0
    have h : e = 0 := by
      calc e = formAdj (RingHom.id F) G (formAdj (RingHom.id F) G e) :=
            (Geo.formAdj_formAdj (RingHom.id F) (fun _ => rfl) hG hGh e).symm
        _ = formAdj (RingHom.id F) G 0 := by rw [h0]
        _ = 0 := gbd_formAdj_zero G
    exact he.2.2.1 h
  · intro f hfA hfid hfe
    have hfmem : formAdj (RingHom.id F) G f ∈ A :=
      Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU hfA
    have hfid' : IsIdempotentElem (formAdj (RingHom.id F) G f) :=
      isIdempotentElem_iff.mpr (by
        rw [← Geo.formAdj_mul (RingHom.id F) hG, hfid.eq])
    have hfe' : formAdj (RingHom.id F) G f * e = formAdj (RingHom.id F) G f := by
      have h := congrArg (formAdj (RingHom.id F) G) hfe
      rw [Geo.formAdj_mul (RingHom.id F) hG,
        Geo.formAdj_formAdj (RingHom.id F) (fun _ => rfl) hG hGh e] at h
      exact (gbd_adjoin_comm hS (formAdj (RingHom.id F) G f) hfmem e he.1).eq.trans h
    rcases he.2.2.2 (formAdj (RingHom.id F) G f) hfmem hfid' hfe' with h0 | heq
    · left
      have h := congrArg (formAdj (RingHom.id F) G) h0
      rw [Geo.formAdj_formAdj (RingHom.id F) (fun _ => rfl) hG hGh f,
        gbd_formAdj_zero G] at h
      exact h
    · right
      have h := congrArg (formAdj (RingHom.id F) G) heq
      rwa [Geo.formAdj_formAdj (RingHom.id F) (fun _ => rfl) hG hGh f] at h

private lemma gbd_frobenius_pow_apply {F K : Type} [Field F] [Fintype F] [Field K]
    [Algebra F K] [Algebra.IsAlgebraic F K] (k : ℕ) (x : K) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ k) x =
      x ^ (Fintype.card F ^ k) := by
  rw [AlgEquiv.coe_pow]
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih,
        FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← pow_mul, Nat.mul_comm,
        ← pow_succ]

private lemma gbd_exists_ne_one_of_pow_prime {D K : Type} [Group D] [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hcard : p < Nat.card D) (φ : D →* Kˣ)
    (hpow : ∀ d : D, φ d ^ p = 1) :
    ∃ d : D, d ≠ 1 ∧ φ d = 1 := by
  classical
  have hDfin : Finite D := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hTcard : Nat.card {x : Kˣ // x ^ p = 1} ≤ p := by
    calc Nat.card {x : Kˣ // x ^ p = 1}
        = Fintype.card {x : Kˣ // x ^ p = 1} := Nat.card_eq_fintype_card
      _ = (Finset.univ.filter (fun x : Kˣ => x ^ p = 1)).card :=
            Fintype.card_subtype _
      _ ≤ p := IsCyclic.card_pow_eq_one_le hp.pos
  by_contra hcon
  have hker : ∀ d : D, φ d = 1 → d = 1 := by
    intro d hd
    by_contra hne
    exact hcon ⟨d, hne, hd⟩
  let Φ : D → {x : Kˣ // x ^ p = 1} := fun d => ⟨φ d, hpow d⟩
  have hinj : Function.Injective Φ := by
    intro a b hab
    have hφ : φ a = φ b := congrArg Subtype.val hab
    have h1 : φ (a * b⁻¹) = 1 := by
      rw [map_mul, hφ]
      simpa using mul_inv_cancel (φ b)
    exact mul_inv_eq_one.mp (hker (a * b⁻¹) h1)
  have hle : Nat.card D ≤ Nat.card {x : Kˣ // x ^ p = 1} :=
    Nat.card_le_card_of_injective Φ hinj
  omega

private lemma gbd_blockDegree_eq_orderOf_of_exists_zeta_ne_one {ι F K : Type}
    [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [Field K] [Algebra F K] [Finite K]
    {S : Set (GL ι F)} {e : Matrix ι ι F} {p : ℕ} (hp : p.Prime)
    (hSp : ∀ s ∈ S, s ^ p = 1)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπdeg : Module.finrank F K =
      blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hnt : ∃ (s : GL ι F) (hs : s ∈ S),
      π ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ ≠ 1) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) e =
      orderOf ((Nat.card F : ℕ) : ZMod p) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype K := Fintype.ofFinite K
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  let π' : A →ₐ[F] K := π
  let ζ : (s : GL ι F) → s ∈ S → K := fun s hs =>
    π' ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  let q : ℕ := Nat.card F
  let d : ℕ := Module.finrank F K
  let c : ℕ := orderOf ((q : ℕ) : ZMod p)
  obtain ⟨s0, hs0, hζ0ne_orig⟩ := hnt
  have hζ0ne : ζ s0 hs0 ≠ 1 := by simpa [ζ, π'] using hζ0ne_orig
  have hζpow : ∀ (s : GL ι F) (hs : s ∈ S), ζ s hs ^ p = 1 := by
    intro s hs
    have hs_pow :
        (⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : A) ^ p = 1 := by
      apply Subtype.ext
      change (s : Matrix ι ι F) ^ p = 1
      rw [← Units.val_pow_eq_pow_val, hSp s hs, Units.val_one]
    change (π' ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩) ^ p = 1
    rw [← map_pow, hs_pow, map_one]
  have hζne : ∀ (s : GL ι F) (hs : s ∈ S), ζ s hs ≠ 0 := by
    intro s hs h0
    have h := hζpow s hs
    rw [h0, zero_pow (Nat.pos_iff_ne_zero.mp hp.pos)] at h
    exact zero_ne_one h
  haveI : Fact p.Prime := ⟨hp⟩
  have hord0 : orderOf (ζ s0 hs0) = p := orderOf_eq_prime (hζpow s0 hs0) hζ0ne
  have hpowK : (ζ s0 hs0) ^ (Nat.card K - 1) = 1 := by
    simpa [Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one (ζ s0 hs0) (hζne s0 hs0)
  have hpdvd : p ∣ Nat.card K - 1 := by
    rw [← hord0]
    exact orderOf_dvd_of_pow_eq_one hpowK
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  have hKcard : Nat.card K = q ^ d := by
    simpa [q, d] using Module.natCard_eq_pow_finrank (K := F) (V := K)
  have hpdvd_pow : p ∣ q ^ d - 1 := by
    rw [← hKcard]
    exact hpdvd
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.card_pos
  have hq1 : 1 < q := by simpa [q] using Finite.one_lt_card (α := F)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Module.finrank_pos_iff.mpr inferInstance
  have hqd1 : 1 ≤ q ^ d := Nat.one_le_pow d q hqpos
  have hqmod : ((q : ZMod p) ^ d) = 1 := by
    have hzero : ((q ^ d - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (q ^ d - 1) p).mpr hpdvd_pow
    rw [Nat.cast_sub hqd1, Nat.cast_one, sub_eq_zero] at hzero
    rw [← Nat.cast_pow]
    exact hzero
  have hc_dvd_d : c ∣ d := by
    dsimp [c]
    exact orderOf_dvd_of_pow_eq_one hqmod
  have hqc : ((q : ZMod p) ^ c) = 1 := by
    dsimp [c]
    exact pow_orderOf_eq_one _
  have hqc1 : 1 ≤ q ^ c := Nat.one_le_pow c q hqpos
  have hqcpow : ((q ^ c : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_pow]
    exact hqc
  have hqc_sub : ((q ^ c - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hqc1, Nat.cast_one, sub_eq_zero]
    exact hqcpow
  have hp_dvd_qc : p ∣ q ^ c - 1 :=
    (ZMod.natCast_eq_zero_iff (q ^ c - 1) p).mp hqc_sub
  have hmod : q ^ c ≡ 1 [MOD p] := by
    apply Nat.modEq_of_dvd
    have hInt : (p : ℤ) ∣ (q ^ c : ℕ) - 1 := by exact_mod_cast hp_dvd_qc
    simpa using dvd_neg.mpr hInt
  have hfixgen : ∀ (s : GL ι F) (hs : s ∈ S),
      (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ c) (ζ s hs) = ζ s hs := by
    intro s hs
    rw [gbd_frobenius_pow_apply (F := F) (K := K) c (ζ s hs)]
    simpa [q] using pow_eq_pow_of_modEq hmod (hζpow s hs)
  let τ : K ≃ₐ[F] K := FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ c
  have hgen_top : Algebra.adjoin F
      (Set.range fun t : {s : GL ι F // s ∈ S} => ζ t.1 t.2) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, rfl⟩ := hπsurj x
    have hmem : ∀ b : A,
        π' b ∈ Algebra.adjoin F (Set.range fun t : {s : GL ι F // s ∈ S} =>
          ζ t.1 t.2) := by
      intro b
      refine Algebra.adjoin_induction
        (p := fun z hz => π' ⟨z, hz⟩ ∈ Algebra.adjoin F
          (Set.range fun t : {s : GL ι F // s ∈ S} => ζ t.1 t.2)) ?_ ?_ ?_ ?_ b.2
      · rintro z ⟨s, hs, rfl⟩
        exact Algebra.subset_adjoin ⟨⟨s, hs⟩, rfl⟩
      · intro r
        have hz : (algebraMap F (Matrix ι ι F)) r ∈ A := Subalgebra.algebraMap_mem A r
        have heq : (⟨(algebraMap F (Matrix ι ι F)) r, hz⟩ : A) = algebraMap F A r :=
          Subtype.ext rfl
        rw [heq, AlgHom.commutes]
        exact Subalgebra.algebraMap_mem _ r
      · intro y z hy hz ihy ihz
        have hyz : y + z ∈ A := Subalgebra.add_mem A hy hz
        have heq : (⟨y + z, hyz⟩ : A) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_add]
        exact Subalgebra.add_mem _ ihy ihz
      · intro y z hy hz ihy ihz
        have hyz : y * z ∈ A := Subalgebra.mul_mem A hy hz
        have heq : (⟨y * z, hyz⟩ : A) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_mul]
        exact Subalgebra.mul_mem _ ihy ihz
    exact hmem a
  have hτhom : τ.toAlgHom = AlgHom.id F K := by
    apply AlgHom.ext_of_adjoin_eq_top hgen_top
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    exact hfixgen t.1 t.2
  have hτid : τ = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    simpa using AlgHom.congr_fun hτhom x
  have hroot : ∀ x : K, x ^ (q ^ c) = x := by
    intro x
    have h := AlgEquiv.congr_fun hτid x
    dsimp [τ] at h
    rw [gbd_frobenius_pow_apply (F := F) (K := K) c x] at h
    simpa [q] using h
  have hcpos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos h
    rw [hc0] at hc_dvd_d
    exact (ne_of_gt hdpos) (Nat.zero_dvd.mp hc_dvd_d)
  have hn2 : 1 < q ^ c := Nat.one_lt_pow hcpos.ne' hq1
  have hPne : (Polynomial.X ^ (q ^ c) - Polynomial.X : Polynomial F) ≠ 0 := by
    have hdegX : Polynomial.degree (Polynomial.X : Polynomial F) < (q ^ c : WithBot ℕ) := by
      rw [Polynomial.degree_X]
      exact WithBot.coe_lt_coe.mpr hn2
    exact (Polynomial.monic_X_pow_sub hdegX).ne_zero
  have hcardK_le : Nat.card K ≤ q ^ c := by
    let P : Polynomial F := Polynomial.X ^ (q ^ c) - Polynomial.X
    have hPne' : P ≠ 0 := by simpa [P] using hPne
    have hsubset : (Set.univ : Set K) ⊆ P.rootSet K := by
      intro x _
      rw [Polynomial.mem_rootSet]
      refine ⟨hPne', ?_⟩
      have h1 : (Polynomial.aeval x) (Polynomial.X ^ (q ^ c) : Polynomial F) =
          x ^ (q ^ c) := by simp
      simp only [P, map_sub, h1, Polynomial.aeval_X]
      rw [hroot x, sub_self]
    have hdeg : P.natDegree ≤ q ^ c := by
      calc P.natDegree
          ≤ max (Polynomial.X ^ (q ^ c) : Polynomial F).natDegree
              (Polynomial.X : Polynomial F).natDegree := by
            simpa [P] using Polynomial.natDegree_sub_le
              (Polynomial.X ^ (q ^ c) : Polynomial F) Polynomial.X
        _ = max (q ^ c) 1 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        _ = q ^ c := max_eq_left (by omega)
    calc Nat.card K = (Set.univ : Set K).ncard := (Set.ncard_univ K).symm
      _ ≤ (P.rootSet K).ncard := Set.ncard_le_ncard hsubset
      _ ≤ P.natDegree := Polynomial.ncard_rootSet_le P K
      _ ≤ q ^ c := hdeg
  have hpow_le : q ^ d ≤ q ^ c := by
    rw [← hKcard]
    exact hcardK_le
  have hq1 : 1 < q := by simpa [q] using Finite.one_lt_card (α := F)
  have hd_le_c : d ≤ c := (pow_le_pow_iff_right₀ hq1).mp hpow_le
  have hdpos : 0 < d := by
    dsimp [d]
    exact Module.finrank_pos_iff.mpr inferInstance
  have hc_le_d : c ≤ d := Nat.le_of_dvd hdpos hc_dvd_d
  have hdc : d = c := le_antisymm hd_le_c hc_le_d
  rw [← hπdeg]
  exact hdc

private lemma gbd_blockDegree_pos {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e) :
    0 < blockDegree A e := by
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M := ⟨e, he.1, by rw [LinearMap.mulRight_apply, he.2.1.eq]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  change 0 < Module.finrank F M
  exact Module.finrank_pos_iff.mpr inferInstance

private lemma gbd_block_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F}
    (he : IsPrimIdemIn A e) (hdeg : blockDegree A e = 1) {a : Matrix ι ι F} (ha : a ∈ A) :
    ∃ c : F, a * e = c • e := by
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have hMdeg : Module.finrank F M = 1 := hdeg
  have heM : e ∈ M := ⟨e, he.1, by rw [LinearMap.mulRight_apply, he.2.1.eq]⟩
  have hene : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  have haM : a * e ∈ M := ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, heM⟩ : M) hene).mp hMdeg
    (⟨a * e, haM⟩ : M)
  exact ⟨c, by simpa using congrArg Subtype.val hc.symm⟩

private lemma gbd_act_eq_of_formAdj_eq_of_blockDegree_one {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] [Finite F] {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hSp : ∀ s ∈ S, s ^ p = 1)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e = 1)
    (hadj : formAdj (RingHom.id F) G e = e) :
    ∀ s ∈ S, (s : Matrix ι ι F) * e = e := by
  intro s hs
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  obtain ⟨c, hce⟩ :=
    gbd_block_scalar he hdeg (Algebra.subset_adjoin ⟨s, hs, rfl⟩)
  have hsinv_mul : ((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcne : c ≠ 0 := by
    intro hc0
    have he0 : e = 0 := by
      calc e = 1 * e := (Matrix.one_mul e).symm
        _ = (((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F)) * e := by
              rw [hsinv_mul]
        _ = ((s⁻¹ : GL ι F) : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
              rw [Matrix.mul_assoc]
        _ = ((s⁻¹ : GL ι F) : Matrix ι ι F) * (c • e) := by rw [hce]
        _ = c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e) := by rw [Matrix.mul_smul]
        _ = 0 := by rw [hc0, zero_smul F]
    exact he.2.2.1 he0
  have hs_inv_A : ((s⁻¹ : GL ι F) : Matrix ι ι F) ∈ A := by
    rw [← Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSU s hs)]
    exact Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU
      (Algebra.subset_adjoin ⟨s, hs, rfl⟩)
  have hright : ((s⁻¹ : GL ι F) : Matrix ι ι F) * e = c⁻¹ • e := by
    have h1 : e = c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e) := by
      calc e = ((s⁻¹ : GL ι F) : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
              rw [← Matrix.mul_assoc, hsinv_mul, Matrix.one_mul]
        _ = ((s⁻¹ : GL ι F) : Matrix ι ι F) * (c • e) := by rw [hce]
        _ = c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e) := by rw [Matrix.mul_smul]
    calc ((s⁻¹ : GL ι F) : Matrix ι ι F) * e
        = c⁻¹ • (c • (((s⁻¹ : GL ι F) : Matrix ι ι F) * e)) := by
            rw [inv_smul_smul₀ hcne]
      _ = c⁻¹ • e := by rw [← h1]
  have hleft : e * ((s⁻¹ : GL ι F) : Matrix ι ι F) = c • e := by
    have h := congrArg (formAdj (RingHom.id F) G) hce
    rw [Geo.formAdj_mul (RingHom.id F) hG,
      Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSU s hs),
      Geo.formAdj_smul, hadj] at h
    simpa using h
  have hcomm : Commute e ((s⁻¹ : GL ι F) : Matrix ι ι F) :=
    gbd_adjoin_comm hS e he.1 ((s⁻¹ : GL ι F) : Matrix ι ι F) hs_inv_A
  have hcc : c = c⁻¹ := by
    apply smul_left_injective F he.2.2.1
    change c • e = c⁻¹ • e
    rw [← hleft, hcomm.eq, hright]
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hcc]
    exact inv_mul_cancel₀ hcne
  have hpow : ∀ k : ℕ, (s : Matrix ι ι F) ^ k * e = c ^ k • e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Matrix.mul_assoc, hce, Matrix.mul_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have hsp : (s : Matrix ι ι F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hSp s hs, Units.val_one]
  have hcp : c ^ p = 1 := by
    have h := hpow p
    rw [hsp, Matrix.one_mul] at h
    exact smul_left_injective F he.2.2.1 (by simpa using h.symm)
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
  have hordp : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have hcop : Nat.Coprime 2 p := (hp.odd_of_ne_two hp2).coprime_two_left
  have hgcd : Nat.gcd 2 p = 1 := hcop
  have hord1 : orderOf c = 1 := by
    exact Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hord2 hordp)
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hord1
  rw [hce, hc1, one_smul]

private lemma gbd_blockDegree_eq_one_of_forall_zeta_eq_one {ι F K : Type}
    [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [Field K] [Algebra F K] [Finite K]
    {S : Set (GL ι F)} {e : Matrix ι ι F}
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπdeg : Module.finrank F K =
      blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hζ : ∀ (s : GL ι F) (hs : s ∈ S),
      π ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ = 1) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) e = 1 := by
  classical
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  let π' : A →ₐ[F] K := π
  have hspan : Submodule.span F ({1} : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, rfl⟩ := hπsurj x
    have hmem : ∀ b : A, π' b ∈ (⊥ : Subalgebra F K) := by
      intro b
      refine Algebra.adjoin_induction
        (p := fun z hz => π' ⟨z, hz⟩ ∈ (⊥ : Subalgebra F K)) ?_ ?_ ?_ ?_ b.2
      · rintro z ⟨s, hs, rfl⟩
        rw [hζ s hs]
        exact Subalgebra.one_mem (⊥ : Subalgebra F K)
      · intro r
        have hz : (algebraMap F (Matrix ι ι F)) r ∈ A := Subalgebra.algebraMap_mem A r
        have heq : (⟨(algebraMap F (Matrix ι ι F)) r, hz⟩ : A) = algebraMap F A r :=
          Subtype.ext rfl
        rw [heq, AlgHom.commutes]
        exact Subalgebra.algebraMap_mem (⊥ : Subalgebra F K) r
      · intro y z hy hz ihy ihz
        have hyz : y + z ∈ A := Subalgebra.add_mem A hy hz
        have heq : (⟨y + z, hyz⟩ : A) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_add]
        exact Subalgebra.add_mem _ ihy ihz
      · intro y z hy hz ihy ihz
        have hyz : y * z ∈ A := Subalgebra.mul_mem A hy hz
        have heq : (⟨y * z, hyz⟩ : A) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_mul]
        exact Subalgebra.mul_mem _ ihy ihz
    have hxbot : π' a ∈ (⊥ : Subalgebra F K) := hmem a
    rw [Algebra.mem_bot] at hxbot
    obtain ⟨c, hc⟩ := hxbot
    rw [← hc, Algebra.algebraMap_eq_smul_one]
    exact (Submodule.mem_span_singleton).mpr ⟨c, rfl⟩
  have hfin : Module.finrank F K = 1 :=
    (finrank_eq_one_iff_of_nonzero (1 : K) one_ne_zero).mpr hspan
  rw [← hπdeg, hfin]

private lemma gbd_formAdj_eq_self_of_exists_algEquiv {ι F K : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] [Field K] [Algebra F K] [Finite K]
    {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix ι ι F) * e = 0)
    (τ : K ≃ₐ[F] K)
    (hτ : ∀ (s : GL ι F) (hs : s ∈ S),
      τ (π ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩) =
        (π ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩)⁻¹) :
    formAdj (RingHom.id F) G e = e := by
  classical
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  let π' : A →ₐ[F] K := π
  let ιa : A ≃ₐ[F] A := gbd_adjointAlgEquiv hG hGh hSU hS
  have hgen : ∀ (s : GL ι F) (hs : s ∈ S),
      ιa ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ =
        ⟨((s⁻¹ : GL ι F) : Matrix ι ι F), by
          rw [← Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSU s hs)]
          exact Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU
            (Algebra.subset_adjoin ⟨s, hs, rfl⟩)⟩ :=
    fun s hs => gbd_adjointAlgEquiv_apply_generator hG hGh hSU hS s hs
  have hcomp : π'.comp ιa.toAlgHom = τ.toAlgHom.comp π' := by
    apply AlgHom.adjoin_ext
    intro x hx
    rcases hx with ⟨s, hs, rfl⟩
    have hsinv : (⟨((s⁻¹ : GL ι F) : Matrix ι ι F), by
          rw [← Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSU s hs)]
          exact Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU
            (Algebra.subset_adjoin ⟨s, hs, rfl⟩)⟩ : A) *
        (⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : A) = 1 := by
      apply Subtype.ext
      change ((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hπinv : π' ⟨((s⁻¹ : GL ι F) : Matrix ι ι F), by
          rw [← Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSU s hs)]
          exact Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU
            (Algebra.subset_adjoin ⟨s, hs, rfl⟩)⟩ =
        (π' ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩)⁻¹ := by
      have h := congrArg π' hsinv
      rw [map_mul, map_one] at h
      exact eq_inv_of_mul_eq_one_left h
    change π' (ιa ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩) =
      τ (π' ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩)
    rw [hgen s hs]
    rw [hπinv]
    exact (hτ s hs).symm
  have hkerAdj : ∀ a : A, π' (ιa a) = 0 ↔ π' a = 0 := by
    intro a
    have h1 : π' (ιa a) = τ (π' a) := by
      have := AlgHom.congr_fun hcomp a
      simpa [AlgHom.comp_apply] using this
    rw [h1]
    constructor
    · intro h
      exact τ.injective (h.trans (map_zero τ).symm)
    · intro h
      rw [h, map_zero]
  let eA : A := ⟨e, he.1⟩
  have heStarPrim : IsPrimIdemIn A (formAdj (RingHom.id F) G e) :=
    gbd_isPrimIdemIn_formAdj hG hGh hSU hS he
  let eStarA : A := ⟨formAdj (RingHom.id F) G e, heStarPrim.1⟩
  have hπ_one_sub : π' (1 - eA) = 0 := by
    rw [hπker]
    change ((1 : Matrix ι ι F) - e) * e = 0
    rw [Matrix.sub_mul, Matrix.one_mul, he.2.1.eq, sub_self]
  have hπ_adj : π' (ιa (1 - eA)) = 0 := (hkerAdj (1 - eA)).mpr hπ_one_sub
  have hzero : (((ιa (1 - eA) : A) : Matrix ι ι F)) * e = 0 := (hπker _).mp hπ_adj
  have hι_sub : ιa (1 - eA) = 1 - ιa eA := by rw [map_sub, map_one]
  have hι_e : ιa eA = eStarA := by
    apply Subtype.ext
    change formAdj (RingHom.id F) G e = formAdj (RingHom.id F) G e
    rfl
  have hzero' : (1 - formAdj (RingHom.id F) G e) * e = 0 := by
    simpa [hι_sub, hι_e] using hzero
  have hfix : formAdj (RingHom.id F) G e * e = e := by
    have h := sub_eq_zero.mp (by simpa [Matrix.sub_mul, Matrix.one_mul] using hzero')
    exact h.symm
  have hcomm : Commute e (formAdj (RingHom.id F) G e) :=
    gbd_adjoin_comm hS e he.1 (formAdj (RingHom.id F) G e) heStarPrim.1
  have he_eStar : eA * eStarA = eA := by
    apply Subtype.ext
    change e * formAdj (RingHom.id F) G e = e
    rw [hcomm.eq, hfix]
  have he_eStar' : (eA : Matrix ι ι F) * formAdj (RingHom.id F) G e =
      (eA : Matrix ι ι F) := by
    simpa [eA, eStarA] using congrArg Subtype.val he_eStar
  rcases heStarPrim.2.2.2 (eA : Matrix ι ι F) he.1 he.2.1 he_eStar' with h0 | heq
  · exfalso
    have h : e = 0 := by simpa [eA] using h0
    exact he.2.2.1 h
  · have h : e = formAdj (RingHom.id F) G e := by simpa [eA] using heq
    exact h.symm

theorem blockDegree_trivial_or_eq_orderOf_gram {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Type) [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Jm : Matrix ι ι F) (hJt : Matrix.transpose Jm = Jm) (hJu : IsUnit Jm.det)
    {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι F) * Jm * (s : Matrix ι ι F) = Jm)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hSp : ∀ s ∈ S, s ^ p = 1)
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    ((∀ s ∈ S, (s : Matrix ι ι F) * e = e) ∧
        blockDegree (Algebra.adjoin F (Units.val '' S)) e = 1 ∧
        formAdj (RingHom.id F) Jm e = e) ∨
      ((∃ s ∈ S, (s : Matrix ι ι F) * e ≠ e) ∧
        blockDegree (Algebra.adjoin F (Units.val '' S)) e = orderOf ((Nat.card F : ℕ) : ZMod p) ∧
        (formAdj (RingHom.id F) Jm e = e ↔ Even (orderOf ((Nat.card F : ℕ) : ZMod p)))) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hG : IsUnit Jm.det := hJu
  have hGh : Matrix.transpose (Jm.map (RingHom.id F)) = Jm := by
    simpa [Matrix.map_id] using hJt
  have hSUgeo : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * Jm *
      (s : Matrix ι ι F) = Jm := by
    intro s hs
    simpa [Matrix.map_id] using hSU s hs
  have hodd : ∀ s ∈ S, Odd (orderOf s) := fun s hs =>
    gbd_odd_orderOf_of_pow_prime hp hp2 (hSp s hs)
  obtain ⟨K, fieldK, algK, finiteK, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField hS hodd he
  letI : Field K := fieldK
  letI : Algebra F K := algK
  letI : Finite K := finiteK
  letI : Fintype K := Fintype.ofFinite K
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  let q : ℕ := Nat.card F
  let c : ℕ := orderOf ((q : ℕ) : ZMod p)
  let ζ : (s : GL ι F) → s ∈ S → K := fun s hs =>
    π ⟨(s : Matrix ι ι F),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hζpow : ∀ (s : GL ι F) (hs : s ∈ S), ζ s hs ^ p = 1 := by
    intro s hs
    have hs_pow : (⟨(s : Matrix ι ι F),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : Algebra.adjoin F (Units.val '' S)) ^ p = 1 := by
      apply Subtype.ext
      change (s : Matrix ι ι F) ^ p = 1
      rw [← Units.val_pow_eq_pow_val, hSp s hs, Units.val_one]
    change (π ⟨(s : Matrix ι ι F),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩) ^ p = 1
    rw [← map_pow, hs_pow, map_one]
  have hζone_iff : ∀ (s : GL ι F) (hs : s ∈ S),
      (s : Matrix ι ι F) * e = e ↔ ζ s hs = 1 := by
    intro s hs
    constructor
    · intro hse
      have hmat : (((⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : Algebra.adjoin F (Units.val '' S)) - 1 :
          Algebra.adjoin F (Units.val '' S)) :
          Matrix ι ι F) * e = 0 := by
        change ((s : Matrix ι ι F) - 1) * e = 0
        rw [Matrix.sub_mul, Matrix.one_mul, hse, sub_self]
      have hπzero : π ((⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : Algebra.adjoin F (Units.val '' S)) - 1) = 0 :=
        (hπker _).mpr hmat
      have hsub : π ⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ - 1 = 0 := by simpa using hπzero
      simpa [ζ] using sub_eq_zero.mp hsub
    · intro hζ
      have hπa : π ⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ = 1 := by simpa [ζ] using hζ
      have hπzero : π ((⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : Algebra.adjoin F (Units.val '' S)) - 1) = 0 := by
        rw [map_sub, hπa, map_one, sub_self]
      have hmat : (((⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : Algebra.adjoin F (Units.val '' S)) - 1 :
          Algebra.adjoin F (Units.val '' S)) : Matrix ι ι F) * e = 0 :=
        (hπker _).mp hπzero
      change ((s : Matrix ι ι F) - 1) * e = 0 at hmat
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hmat
      exact hmat
  by_cases htriv : ∀ (s : GL ι F) (hs : s ∈ S), ζ s hs = 1
  · left
    have hact : ∀ s ∈ S,
        (s : Matrix ι ι F) * e = e :=
      fun s hs => (hζone_iff s hs).mpr (htriv s hs)
    refine ⟨hact, ?_, ?_⟩
    · exact gbd_blockDegree_eq_one_of_forall_zeta_eq_one π hπsurj hπdeg
        (fun s hs => by simpa [ζ] using htriv s hs)
    · apply gbd_formAdj_eq_self_of_exists_algEquiv hG hGh hSUgeo hS he π hπsurj hπker
        (AlgEquiv.refl) ?_
      intro s hs
      change π ⟨(s : Matrix ι ι F),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ =
        (π ⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩)⁻¹
      rw [show π ⟨(s : Matrix ι ι F),
          Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ = 1 from by simpa [ζ] using htriv s hs]
      simp
  · right
    have hnt : ∃ (s : GL ι F) (hs : s ∈ S), ζ s hs ≠ 1 := by
      by_contra h
      apply htriv
      intro s hs
      by_contra hne
      exact h ⟨s, hs, hne⟩
    obtain ⟨snt, hsnt, hneζ⟩ := hnt
    have hnt_act : ∃ s ∈ S,
        (s : Matrix ι ι F) * e ≠ e :=
      ⟨snt, hsnt, fun h => hneζ ((hζone_iff snt hsnt).mp h)⟩
    have hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e = c := by
      simpa [c, q] using
        gbd_blockDegree_eq_orderOf_of_exists_zeta_ne_one hp hSp π hπsurj hπdeg
          ⟨snt, hsnt, by simpa [ζ] using hneζ⟩
    refine ⟨hnt_act, hdeg, ?_⟩
    constructor
    · intro hadj
      have hgeom := blockDegree_eq_one_or_even_of_formAdj_eq hG hS hodd hSUgeo he hadj
      rcases hgeom with h1 | hev
      · exfalso
        have hact := gbd_act_eq_of_formAdj_eq_of_blockDegree_one hG hGh hSUgeo hS he hp hp2
          hSp h1 hadj
        obtain ⟨s, hs, hne⟩ := hnt_act
        exact hne (hact s hs)
      · rwa [hdeg] at hev
    · intro heven
      have hcpos : 0 < c := by
        rw [← hdeg]
        exact gbd_blockDegree_pos he
      obtain ⟨k, hk⟩ := heven
      have hc : c = k + k := hk
      have hqc : ((q : ZMod p) ^ c) = 1 := by
        simpa [c] using (pow_orderOf_eq_one (((q : ℕ) : ZMod p)))
      have hqk_sq : (((q : ZMod p) ^ k) ^ 2) = 1 := by
        have h := hqc
        rw [hc, pow_add] at h
        simpa [pow_two] using h
      have hkpos : 0 < k := by omega
      have hk_lt_c : k < c := by omega
      have hqk_ne_one : ((q : ZMod p) ^ k) ≠ 1 := by
        intro hx
        have hdvd : c ∣ k := by
          dsimp [c]
          exact orderOf_dvd_of_pow_eq_one hx
        have hc_le_k : c ≤ k := Nat.le_of_dvd hkpos hdvd
        omega
      have hqk_neg : ((q : ZMod p) ^ k) = -1 := by
        rcases sq_eq_one_iff.mp hqk_sq with h1 | hneg
        · exact absurd h1 hqk_ne_one
        · exact hneg
      have hzero : ((q ^ k + 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, hqk_neg]
        exact neg_add_cancel (1 : ZMod p)
      have hp_dvd_qk1 : p ∣ q ^ k + 1 :=
        (ZMod.natCast_eq_zero_iff (q ^ k + 1) p).mp hzero
      have hmod0 : q ^ k + 1 ≡ 0 [MOD p] := by
        apply Nat.modEq_of_dvd
        have hInt : (p : ℤ) ∣ (q ^ k : ℕ) + 1 := by exact_mod_cast hp_dvd_qk1
        simpa using dvd_neg.mpr hInt
      have hfixinv : ∀ (s : GL ι F) (hs : s ∈ S),
          (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ k) (ζ s hs) = (ζ s hs)⁻¹ := by
        intro s hs
        rw [gbd_frobenius_pow_apply (F := F) (K := K) k (ζ s hs)]
        have hpow1 : ζ s hs ^ (q ^ k + 1) = 1 := by
          simpa using pow_eq_pow_of_modEq hmod0 (hζpow s hs)
        have hpow1' : ζ s hs ^ (Fintype.card F ^ k + 1) = 1 := by
          simpa [q, Nat.card_eq_fintype_card] using hpow1
        rw [pow_add, pow_one] at hpow1'
        exact eq_inv_of_mul_eq_one_left hpow1'
      apply gbd_formAdj_eq_self_of_exists_algEquiv hG hGh hSUgeo hS he π hπsurj hπker
        (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ k) ?_
      intro s hs
      exact hfixinv s hs

theorem exists_ne_one_fix_blockIdem_gl {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Type) [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Type} [Group D] (hD : Nat.card D = p ^ 2) (ℓ : D →* GL ι F)
    (hℓp : ∀ d, (ℓ d) ^ p = 1) (hcomm : ∀ d d' : D, Commute d d')
    {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' Set.range fun d : D => (ℓ d : GL ι F))) e) :
    ∃ d : D, d ≠ 1 ∧ ((ℓ d : GL ι F) : Matrix ι ι F) * e = e := by
  classical
  let S : Set (GL ι F) :=
    Set.range fun d : D => (ℓ d : GL ι F)
  have hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    rintro s ⟨d, rfl⟩ s' ⟨d', rfl⟩
    exact (hcomm d d').map ℓ
  have hodd : ∀ s ∈ S, Odd (orderOf s) := by
    rintro s ⟨d, rfl⟩
    exact gbd_odd_orderOf_of_pow_prime hp hp2 (hℓp d)
  obtain ⟨K, fieldK, algK, finiteK, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField hS hodd he
  letI : Field K := fieldK
  letI : Algebra F K := algK
  letI : Finite K := finiteK
  let A : Subalgebra F (Matrix ι ι F) :=
    Algebra.adjoin F (Units.val '' S)
  let a : D → A := fun d =>
    ⟨((ℓ d : GL ι F) : Matrix ι ι F), by
      exact Algebra.subset_adjoin ⟨(ℓ d : GL ι F), ⟨d, rfl⟩, rfl⟩⟩
  have ha_one : a 1 = 1 := by
    apply Subtype.ext
    change (((ℓ 1 : GL ι F) : GL ι F) :
      Matrix ι ι F) = 1
    rw [map_one]
    rfl
  have ha_mul : ∀ d d' : D, a (d * d') = a d * a d' := by
    intro d d'
    apply Subtype.ext
    change (((ℓ (d * d') : GL ι F) : GL ι F) :
        Matrix ι ι F) =
      (((ℓ d : GL ι F) : GL ι F) :
        Matrix ι ι F) *
      (((ℓ d' : GL ι F) : GL ι F) :
        Matrix ι ι F)
    rw [map_mul]
    rfl
  have hζp : ∀ d : D, (π (a d)) ^ p = 1 := by
    intro d
    have ha_pow : a d ^ p = 1 := by
      apply Subtype.ext
      change ((((ℓ d : GL ι F) : GL ι F) :
        Matrix ι ι F) ^ p) = 1
      rw [← Units.val_pow_eq_pow_val, hℓp d, Units.val_one]
    rw [← map_pow, ha_pow, map_one]
  have hζne : ∀ d : D, π (a d) ≠ 0 := by
    intro d h0
    have h := hζp d
    rw [h0, zero_pow (Nat.pos_iff_ne_zero.mp hp.pos)] at h
    exact zero_ne_one h
  let φ : D →* Kˣ :=
    { toFun := fun d => Units.mk0 (π (a d)) (hζne d)
      map_one' := by
        apply Units.ext
        change π (a 1) = 1
        rw [ha_one, map_one]
      map_mul' := by
        intro d d'
        apply Units.ext
        change π (a (d * d')) = π (a d) * π (a d')
        rw [ha_mul, map_mul] }
  have hφpow : ∀ d : D, φ d ^ p = 1 := by
    intro d
    apply Units.ext
    simpa [φ, Units.val_pow_eq_pow_val] using hζp d
  have hcardD : p < Nat.card D := by
    rw [hD]
    have hlt : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
    simpa [pow_two] using hlt
  obtain ⟨d, hdne, hd1⟩ := gbd_exists_ne_one_of_pow_prime hp hcardD φ hφpow
  refine ⟨d, hdne, ?_⟩
  have hζ1 : π (a d) = 1 := by
    have h := congrArg Units.val hd1
    simpa [φ] using h
  have hsub : π (a d - 1) = 0 := by
    rw [map_sub, hζ1, map_one, sub_self]
  have hzero : (((a d - 1 : A) : Matrix ι ι F)) * e = 0 :=
    (hπker (a d - 1)).mp hsub
  have hzero' : (((ℓ d : GL ι F) :
      Matrix ι ι F) - 1) * e = 0 := by
    simpa [a] using hzero
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hzero'
  simpa using hzero'

end CFSG.StandardType.TableC

end
