module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphPsiNeOne
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphAlgebra
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition
open CFSG.LocalAnalysis.ComponentInitial

private lemma psuA5_psi_zero {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    {X : GL (Fin n) K} : psuPsi h X (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  have h2 := psuPsi_add h X 0 0
  rw [add_zero] at h2
  exact add_left_cancel (by rw [add_zero]; exact h2.symm)

private lemma psuA5_psi_sum {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    {X : GL (Fin n) K} (s : Finset (Matrix (Fin n) (Fin n) K))
    (g : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K) :
    psuPsi h X (∑ e ∈ s, g e) = ∑ e ∈ s, psuPsi h X (g e) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact psuA5_psi_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, psuPsi_add, ih]

private lemma psuA5_trivial_all {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (htriv : ∀ e ∈ P, ∀ a ∈ psuAlg B, psuPsi h X (a * e) = a * e) :
    ∀ a ∈ psuAlg B, psuPsi h X a = a := by
  classical
  intro a ha
  have hsum : ∑ e ∈ P, a * e = a := by
    rw [← Finset.mul_sum, hP.2.2, mul_one]
  have hmain : psuPsi h X (∑ e ∈ P, a * e) = ∑ e ∈ P, a * e := by
    rw [psuA5_psi_sum]
    exact Finset.sum_congr rfl (fun e he => htriv e he a ha)
  rw [← hsum]
  exact hmain

private lemma psuA5_kind2 {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} {e : Matrix (Fin n) (Fin n) K}
    (he : psuKind h X B e = 2) : psuPsiTrivial h X B e := by
  unfold psuKind at he
  by_cases hdag : psuDag h e = e
  · rw [if_pos hdag] at he
    by_cases hpsi : psuPsi h X e = e
    · rw [if_pos hpsi] at he; omega
    · rw [if_neg hpsi] at he; omega
  · rw [if_neg hdag] at he
    by_cases hpsi : psuPsi h X e = e
    · rw [if_pos hpsi] at he
      by_cases htr : psuPsiTrivial h X B e
      · exact htr
      · rw [if_neg htr] at he; omega
    · rw [if_neg hpsi] at he
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at he; omega
      · rw [if_neg h4] at he; omega

private lemma psuA5_kind0 {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} {e : Matrix (Fin n) (Fin n) K}
    (he : psuKind h X B e = 0) : psuDag h e = e ∧ psuPsi h X e = e := by
  unfold psuKind at he
  by_cases hdag : psuDag h e = e
  · rw [if_pos hdag] at he
    by_cases hpsi : psuPsi h X e = e
    · exact ⟨hdag, hpsi⟩
    · rw [if_neg hpsi] at he; omega
  · rw [if_neg hdag] at he
    by_cases hpsi : psuPsi h X e = e
    · rw [if_pos hpsi] at he
      by_cases htr : psuPsiTrivial h X B e
      · rw [if_pos htr] at he; omega
      · rw [if_neg htr] at he; omega
    · rw [if_neg hpsi] at he
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at he; omega
      · rw [if_neg h4] at he; omega

private lemma psuA5_blockField {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : IsPrimIdemIn (psuAlg B) e) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Finite L)
      (π : psuAlg B →ₐ[K] L), Function.Surjective π ∧
      (∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0) ∧
      Module.finrank K L = blockDegree (psuAlg B) e := by
  classical
  have hS : ∀ s ∈ ({B} : Set (GL (Fin n) K)), ∀ s' ∈ ({B} : Set (GL (Fin n) K)),
      Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    subst hs
    subst hs'
    exact Commute.refl _
  have hodd : ∀ s ∈ ({B} : Set (GL (Fin n) K)), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact S.odd
  exact exists_blockField hS hodd he

private lemma psuA5_induced_ringEquiv {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} (heA : e ∈ psuAlg B)
    {L : Type} [Field L] [Algebra K L]
    (π : psuAlg B →ₐ[K] L) (hπ : Function.Surjective π)
    (hker : ∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0)
    (φ : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b)
    (hmul : ∀ a b, a ∈ psuAlg B → b ∈ psuAlg B → φ (a * b) = φ a * φ b)
    (hone : φ 1 = 1)
    (hA : ∀ a ∈ psuAlg B, φ a ∈ psuAlg B)
    (hinv : ∀ a ∈ psuAlg B, φ (φ a) = a)
    (he : φ e = e) :
    ∃ Φ : L ≃+* L, ∀ a : psuAlg B, Φ (π a) = π ⟨φ (a : Matrix (Fin n) (Fin n) K), hA _ a.2⟩ := by
  classical
  let A : Subalgebra K (Matrix (Fin n) (Fin n) K) := psuAlg B
  let J : Ideal A := RingHom.ker (π : A →+* L)
  have hzero : φ 0 = 0 := by
    have h2 := hadd 0 0
    rw [add_zero] at h2
    exact add_left_cancel (by rw [add_zero]; exact h2.symm)
  let φA : A →+* A :=
    { toFun := fun a => ⟨φ a, hA a a.2⟩
      map_one' := Subtype.ext hone
      map_zero' := Subtype.ext hzero
      map_mul' := fun a b => Subtype.ext (hmul a b a.2 b.2)
      map_add' := fun a b => Subtype.ext (hadd a b) }
  have hφA2 : ∀ a : A, φA (φA a) = a := fun a => Subtype.ext (hinv a a.2)
  have hφker : ∀ a ∈ J, φA a ∈ J := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp ha
    have h1 : φ ((a : Matrix (Fin n) (Fin n) K) * e) = 0 := by rw [hae, hzero]
    have h2 : φ ((a : Matrix (Fin n) (Fin n) K) * e) =
        φ (a : Matrix (Fin n) (Fin n) K) * e := by
      rw [hmul (a : Matrix (Fin n) (Fin n) K) e a.2 heA, he]
    have h3 : φ (a : Matrix (Fin n) (Fin n) K) * e = 0 := by rw [← h2, h1]
    exact (hker ⟨φ (a : Matrix (Fin n) (Fin n) K), hA _ a.2⟩).mpr h3
  have hqproof : ∀ a ∈ J, (Ideal.Quotient.mk J) (φA a) = 0 := fun a ha => by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hφker a ha
  let hq : A ⧸ J →+* A ⧸ J :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk J).comp φA) hqproof
  have hhq : ∀ a : A, hq (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J (φA a) :=
    fun a => Ideal.Quotient.lift_mk J ((Ideal.Quotient.mk J).comp φA) hqproof (a := a)
  have hq2 : ∀ x, hq (hq x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) x
    rw [hhq a, hhq (φA a), hφA2]
  have hqbij : Function.Bijective hq := Function.Involutive.bijective hq2
  let hqe : A ⧸ J ≃+* A ⧸ J := RingEquiv.ofBijective hq hqbij
  let E1a := Ideal.quotientKerAlgEquivOfSurjective (f := π) hπ
  let E1r : A ⧸ J ≃+* L := E1a.toRingEquiv
  have hmk : ∀ a : A, E1r (Ideal.Quotient.mk J a) = π a := by
    intro a
    show E1a (Ideal.Quotient.mk J a) = π a
    exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := π) hπ a
  have hhqe : ∀ a : A, hqe (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J (φA a) := by
    intro a
    change hq (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J (φA a)
    rw [hhq a]
  refine ⟨E1r.symm.trans (hqe.trans E1r), fun a => ?_⟩
  have hsymm : E1r.symm (π a) = Ideal.Quotient.mk J a := by
    rw [← hmk a]
    exact E1r.symm_apply_apply (Ideal.Quotient.mk J a)
  show E1r (hqe (E1r.symm (π a))) = π ⟨φ (a : Matrix (Fin n) (Fin n) K), hA _ a.2⟩
  rw [hsymm, hhqe a, hmk (φA a)]
  rfl

private lemma psuA5_induced_sigma {K : Type} [Field K] {A : Type} [Ring A] [Algebra K A]
    {L : Type} [Field L] [Algebra K L]
    (π : A →ₐ[K] L) (Φ : L ≃+* L) (σ : K →+* K) (φA : A → A)
    (hφA : ∀ c : K, φA (algebraMap K A c) = algebraMap K A (σ c))
    (hΦπ : ∀ a : A, Φ (π a) = π (φA a)) :
    ∀ k : K, Φ (algebraMap K L k) = algebraMap K L (σ k) := by
  intro k
  rw [← AlgHom.commutes π k, hΦπ, hφA, AlgHom.commutes]

private lemma psuA5_unique_order_two {G : Type} [Group G] [Fintype G] [IsCyclic G]
    {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hx2 : orderOf x = 2 := by
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf x) hdvd with h | h
    · exact absurd h (fun h1 => hx1 (orderOf_eq_one_iff.mp h1))
    · exact h
  have hy2 : orderOf y = 2 := by
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hy)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf y) hdvd with h | h
    · exact absurd h (fun h1 => hy1 (orderOf_eq_one_iff.mp h1))
    · exact h
  have h2dvd : 2 ∣ Fintype.card G := by
    rw [← hx2]
    exact orderOf_dvd_card
  have hcard : (Finset.univ.filter (fun a : G => orderOf a = 2)).card = 1 := by
    have h := IsCyclic.card_orderOf_eq_totient (α := G) (d := 2) h2dvd
    simpa [Nat.totient_two] using h
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hxz : x = z := by
    have hmem : x ∈ Finset.univ.filter (fun a : G => orderOf a = 2) := by simp [hx2]
    rw [hz] at hmem
    simpa using hmem
  have hyz : y = z := by
    have hmem : y ∈ Finset.univ.filter (fun a : G => orderOf a = 2) := by simp [hy2]
    rw [hz] at hmem
    simpa using hmem
  exact hxz.trans hyz.symm

private lemma psuA5_ringEquiv_isCyclic (F : Type) [Field F] [Finite F] :
    IsCyclic (F ≃+* F) := by
  classical
  haveI : Fact (ringChar F).Prime := ⟨CharP.prime_ringChar F⟩
  haveI hchar : CharP F (ringChar F) := ⟨fun x => ringChar.spec F x⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  haveI : IsCyclic (F ≃ₐ[ZMod (ringChar F)] F) :=
    FiniteField.instIsCyclicAlgEquivOfFinite (ZMod (ringChar F)) F
  let f : (F ≃ₐ[ZMod (ringChar F)] F) →* (F ≃+* F) :=
    { toFun := fun e => e.toRingEquiv
      map_one' := rfl
      map_mul' := fun a b => rfl }
  refine isCyclic_of_surjective f ?_
  intro y
  refine ⟨AlgEquiv.ofRingEquiv (f := y) (fun x => ?_), ?_⟩
  · have h := RingHom.ext_zmod (y.toRingHom.comp (algebraMap (ZMod (ringChar F)) F))
      (algebraMap (ZMod (ringChar F)) F)
    exact congrArg (fun g : ZMod (ringChar F) →+* F => g x) h
  · exact RingEquiv.ext (fun a => rfl)

private lemma psuA5_involutions_eq {F : Type} [Field F] [Finite F]
    {K : Type} [Field K] [Algebra K F] (σ : K →+* K) (hσ : ∃ k, σ k ≠ k)
    (τ θ : F ≃+* F) (hτ : τ * τ = 1) (hθ : θ * θ = 1)
    (hτσ : ∀ k : K, τ (algebraMap K F k) = algebraMap K F (σ k))
    (hθσ : ∀ k : K, θ (algebraMap K F k) = algebraMap K F (σ k)) :
    τ = θ := by
  classical
  haveI : IsCyclic (F ≃+* F) := psuA5_ringEquiv_isCyclic F
  haveI : Fintype (F ≃+* F) := Fintype.ofFinite _
  refine psuA5_unique_order_two hτ hθ ?_ ?_
  · intro h1
    obtain ⟨k, hk⟩ := hσ
    have h := hτσ k
    rw [h1] at h
    have hk' : k = σ k := (algebraMap K F).injective (by simpa using h)
    exact hk hk'.symm
  · intro h1
    obtain ⟨k, hk⟩ := hσ
    have h := hθσ k
    rw [h1] at h
    have hk' : k = σ k := (algebraMap K F).injective (by simpa using h)
    exact hk hk'.symm

private lemma psuA5_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  have hgen : ∀ a ∈ psuAlg B, a * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * a := by
    intro a ha
    refine Algebra.adjoin_induction
      (p := fun x _ => x * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * x) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨s, hs, rfl⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rfl
    · intro r
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
    · intro x y hx hy hpx hpy
      rw [add_mul, mul_add, hpx, hpy]
    · intro x y hx hy hpx hpy
      rw [Matrix.mul_assoc x y (B : Matrix (Fin n) (Fin n) K), hpy,
        ← Matrix.mul_assoc x (B : Matrix (Fin n) (Fin n) K) y, hpx,
        Matrix.mul_assoc (B : Matrix (Fin n) (Fin n) K) x y]
  intro a ha b hb
  refine Algebra.adjoin_induction (p := fun x _ => a * x = x * a) ?_ ?_ ?_ ?_ hb
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hgen a ha
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  · intro x y hx hy hpx hpy
    rw [mul_add, add_mul, hpx, hpy]
  · intro x y hx hy hpx hpy
    rw [← Matrix.mul_assoc a x y, hpx, Matrix.mul_assoc x a y, hpy,
      ← Matrix.mul_assoc x y a]

private lemma psuA5_theta_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∀ a ∈ psuAlg B, psuTheta h X a ∈ psuAlg B := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun x _ => psuTheta h X x ∈ psuAlg B)
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have hB : (B : Matrix (Fin n) (Fin n) K) ∈ psuAlg B :=
      Algebra.subset_adjoin ⟨B, rfl, rfl⟩
    obtain ⟨c, hc⟩ := S.theta_B
    rw [hc]
    exact Subalgebra.smul_mem _ hB c
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, psuTheta_smul, psuTheta_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) (h.bar r)
  · intro x y hx hy hpx hpy
    rw [psuTheta_add]
    exact Subalgebra.add_mem _ hpx hpy
  · intro x y hx hy hpx hpy
    rw [psuTheta_mul]
    exact Subalgebra.mul_mem _ hpx hpy

private lemma psuA5_kind0_trivial {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    {e : Matrix (Fin n) (Fin n) K} (heP : e ∈ P) (hdag : psuDag h e = e)
    (hpsi : psuPsi h X e = e) :
    ∀ a ∈ psuAlg B, psuPsi h X (a * e) = a * e := by
  classical
  have hePrim : IsPrimIdemIn (psuAlg B) e := (hP.1 e).1 heP
  have heA : e ∈ psuAlg B := hePrim.1
  have hdagA : ∀ a ∈ psuAlg B, psuDag h a ∈ psuAlg B :=
    fun a ha => (psuGraph_star_mem S a ha).1
  have hθA : ∀ a ∈ psuAlg B, psuTheta h X a ∈ psuAlg B := psuA5_theta_mem S
  obtain ⟨L, instField, instAlg, instFin, π, hπsurj, hker, _⟩ := psuA5_blockField S hePrim
  letI : Field L := instField
  letI : Algebra K L := instAlg
  letI : Finite L := instFin
  have hdagmul : ∀ a b, a ∈ psuAlg B → b ∈ psuAlg B →
      psuDag h (a * b) = psuDag h a * psuDag h b := by
    intro a b ha hb
    rw [psuDag_mul]
    exact psuA5_comm B (psuDag h b) (hdagA b hb) (psuDag h a) (hdagA a ha)
  obtain ⟨τ, hτπ⟩ := psuA5_induced_ringEquiv heA π hπsurj hker (psuDag h)
    (psuDag_add h) hdagmul (psuDag_one h) hdagA (fun a _ => psuDag_dag h a) hdag
  have hθe : psuTheta h X e = e := by
    have h : psuPsi h X e = e := hpsi
    simp only [psuPsi] at h
    rwa [hdag] at h
  have hθmul : ∀ a b, a ∈ psuAlg B → b ∈ psuAlg B →
      psuTheta h X (a * b) = psuTheta h X a * psuTheta h X b :=
    fun a b _ _ => psuTheta_mul h X a b
  obtain ⟨θbar, hθπ⟩ := psuA5_induced_ringEquiv heA π hπsurj hker (psuTheta h X)
    (psuTheta_add h X) hθmul (psuTheta_one h X) hθA
    (fun a _ => psuTheta_theta h X S.X_sq a) hθe
  let dagF : psuAlg B → psuAlg B := fun a => ⟨psuDag h a, hdagA a a.2⟩
  let thetaF : psuAlg B → psuAlg B := fun a => ⟨psuTheta h X a, hθA a a.2⟩
  have hdagσ : ∀ c : K, dagF (algebraMap K (psuAlg B) c) =
      algebraMap K (psuAlg B) (h.bar c) := by
    intro c
    apply Subtype.ext
    show psuDag h ((algebraMap K (psuAlg B) c : psuAlg B) : Matrix (Fin n) (Fin n) K) =
      ((algebraMap K (psuAlg B) (h.bar c) : psuAlg B) : Matrix (Fin n) (Fin n) K)
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      psuDag_smul, psuDag_one]
  have hθσ : ∀ c : K, thetaF (algebraMap K (psuAlg B) c) =
      algebraMap K (psuAlg B) (h.bar c) := by
    intro c
    apply Subtype.ext
    show psuTheta h X ((algebraMap K (psuAlg B) c : psuAlg B) : Matrix (Fin n) (Fin n) K) =
      ((algebraMap K (psuAlg B) (h.bar c) : psuAlg B) : Matrix (Fin n) (Fin n) K)
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      psuTheta_smul, psuTheta_one]
  have hτπ' : ∀ a, τ (π a) = π (dagF a) := fun a => hτπ a
  have hθπ' : ∀ a, θbar (π a) = π (thetaF a) := fun a => hθπ a
  have hτσ : ∀ k : K, τ (algebraMap K L k) = algebraMap K L (h.bar k) :=
    psuA5_induced_sigma π τ h.bar dagF hdagσ hτπ'
  have hθσ' : ∀ k : K, θbar (algebraMap K L k) = algebraMap K L (h.bar k) :=
    psuA5_induced_sigma π θbar h.bar thetaF hθσ hθπ'
  have hτ2 : τ * τ = 1 := by
    ext x
    obtain ⟨a, rfl⟩ := hπsurj x
    show τ (τ (π a)) = π a
    rw [hτπ a, hτπ (dagF a)]
    congr 1
    exact Subtype.ext (psuDag_dag h (a : Matrix (Fin n) (Fin n) K))
  have hθ2 : θbar * θbar = 1 := by
    ext x
    obtain ⟨a, rfl⟩ := hπsurj x
    show θbar (θbar (π a)) = π a
    rw [hθπ a, hθπ (thetaF a)]
    congr 1
    exact Subtype.ext (psuTheta_theta h X S.X_sq (a : Matrix (Fin n) (Fin n) K))
  have hτθ : τ = θbar :=
    psuA5_involutions_eq h.bar h.exists_bar_ne τ θbar hτ2 hθ2 hτσ hθσ'
  intro a ha
  have hψa_mem : psuPsi h X a ∈ psuAlg B := (psuGraph_star_mem S a ha).2
  let psiA : psuAlg B := ⟨psuPsi h X a, hψa_mem⟩
  let aA : psuAlg B := ⟨a, ha⟩
  let eA : psuAlg B := ⟨e, heA⟩
  have hdagA_mem : psuDag h a ∈ psuAlg B := hdagA a ha
  have hpiψa : π psiA = π aA := by
    have h1 : π psiA = π ⟨psuTheta h X (psuDag h a), hθA _ hdagA_mem⟩ :=
      congrArg π (Subtype.ext rfl)
    rw [h1, ← hθπ ⟨psuDag h a, hdagA_mem⟩, ← hτπ aA, ← hτθ]
    simpa using DFunLike.congr_fun hτ2 (π aA)
  have hπmul : π (psiA * eA) = π (aA * eA) := by
    rw [map_mul, map_mul, hpiψa]
  have hker' : ((psiA * eA : psuAlg B) : Matrix (Fin n) (Fin n) K) * e =
      ((aA * eA : psuAlg B) : Matrix (Fin n) (Fin n) K) * e := by
    have hdiff : π (psiA * eA - aA * eA) = 0 := by
      rw [map_sub, hπmul, sub_self]
    have hz := (hker (psiA * eA - aA * eA)).mp hdiff
    rw [Subalgebra.coe_sub, sub_mul] at hz
    exact sub_eq_zero.mp hz
  have hfinal : psuPsi h X a * e = a * e := by
    have hee : e * e = e := hePrim.2.1
    have h1 : ((psiA * eA : psuAlg B) : Matrix (Fin n) (Fin n) K) * e =
        ((aA * eA : psuAlg B) : Matrix (Fin n) (Fin n) K) * e := hker'
    simpa [psiA, aA, eA, Subalgebra.coe_mul, Matrix.mul_assoc, hee] using h1
  rw [psuPsi_mul h X a e, hpsi]
  rw [psuA5_comm B e heA (psuPsi h X a) hψa_mem, hfinal]
theorem psuGraph_exists_not_trivial {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∃ e ∈ P, psuKind h X B e ≠ 0 ∧ psuKind h X B e ≠ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, hane⟩ := psuGraph_psi_ne_one S
  refine hane (psuA5_trivial_all P hP ?_ a ha)
  intro e he a' ha'
  have hk : psuKind h X B e = 0 ∨ psuKind h X B e = 2 := by
    rcases Classical.em (psuKind h X B e = 0) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (hcon e he h0)
  rcases hk with h0 | h2
  · exact psuA5_kind0_trivial S P hP he (psuA5_kind0 h0).1 (psuA5_kind0 h0).2 a' ha'
  · exact psuA5_kind2 h2 a' ha'

end CFSG.StandardType
