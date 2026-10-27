module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj

public section

namespace CFSG.StandardType.ClassicalPosition

private lemma bd1_gf2_eq_zero_or_one (a : GaloisField 2 1) : a = 0 ∨ a = 1 := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 one_ne_zero
  by_contra h
  push Not at h
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h3 : ({0, 1, a} : Finset (GaloisField 2 1)).card = 3 :=
    Finset.card_eq_three.2
      ⟨0, 1, a, zero_ne_one, fun h0 => h.1 h0.symm, fun h1 => h.2 h1.symm, rfl⟩
  have hle := Finset.card_le_univ ({0, 1, a} : Finset (GaloisField 2 1))
  rw [h3, ← Nat.card_eq_fintype_card, hcard] at hle
  omega

theorem mul_eq_self_of_blockDegree_lt_two_gf2 {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : GL ι (GaloisField 2 1)} {e : Matrix ι ι (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' {s})) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' {s})) e < 2) :
    (s : Matrix ι ι (GaloisField 2 1)) * e = e := by
  classical
  let F := GaloisField 2 1
  let A : Subalgebra F (Matrix ι ι F) :=
    Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F)))
  have hdegA : blockDegree A e < 2 := hdeg
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M :=
    ⟨1, by simp, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  have hnt : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  have hpos : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr hnt
  have hlt : Module.finrank F M < 2 := hdegA
  have hfin : Module.finrank F M = 1 := by omega
  have hspan : M = Submodule.span F {e} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin heM he.2.2.1
  have hsM : (s : Matrix ι ι F) * e ∈ M :=
    ⟨(s : Matrix ι ι F),
      Algebra.subset_adjoin (Set.mem_image_of_mem Units.val (Set.mem_singleton s)),
      by rw [LinearMap.mulRight_apply]⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hsM)
  have hcne : c ≠ 0 := by
    rintro rfl
    have hSe0 : (s : Matrix ι ι F) * e = 0 := by rw [← hc, zero_smul]
    have hunit : ((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have he0 : e = 0 := by
      calc e = 1 * e := (one_mul e).symm
        _ = (((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F)) * e := by rw [hunit]
        _ = ((s⁻¹ : GL ι F) : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
            rw [Matrix.mul_assoc]
        _ = 0 := by rw [hSe0, Matrix.mul_zero]
    exact he.2.2.1 he0
  have hc1 : c = 1 := (bd1_gf2_eq_zero_or_one c).resolve_left hcne
  simpa [hc1] using hc.symm

private lemma bd1_gf2_aeval_mul_of_mul_eq_self {ι : Type} [Fintype ι] [DecidableEq ι]
    {S x : Matrix ι ι (GaloisField 2 1)} (hSx : S * x = x)
    (p : Polynomial (GaloisField 2 1)) :
    Polynomial.aeval S p * x = p.eval 1 • x := by
  have hpow : ∀ k : ℕ, S ^ k * x = x := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mul]
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, hSx, ih]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  simp only [Matrix.smul_mul, hpow]
  rw [Finset.sum_smul]
  simp

theorem formAdj_eq_self_of_blockDegree_lt_two_gf2 {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι (GaloisField 2 1)} (hG : IsUnit G.det) {s : GL ι (GaloisField 2 1)}
    (hs : Matrix.transpose (s : Matrix ι ι (GaloisField 2 1)) * G *
      (s : Matrix ι ι (GaloisField 2 1)) = G)
    {e : Matrix ι ι (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' {s})) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' {s})) e < 2) :
    formAdj (RingHom.id (GaloisField 2 1)) G e = e := by
  classical
  let F := GaloisField 2 1
  let S : Matrix ι ι F := (s : Matrix ι ι F)
  let A : Subalgebra F (Matrix ι ι F) :=
    Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F)))
  let eStar : Matrix ι ι F := formAdj (RingHom.id F) G e
  have hSe : S * e = e := mul_eq_self_of_blockDegree_lt_two_gf2 he hdeg
  have hSinvS : ((s⁻¹ : GL ι F) : Matrix ι ι F) * S = 1 := by
    change ((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSadj : formAdj (RingHom.id F) G S = ((s⁻¹ : GL ι F) : Matrix ι ι F) :=
    Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa [Matrix.map_id] using hs)
  have hstarSinv : eStar * ((s⁻¹ : GL ι F) : Matrix ι ι F) = eStar := by
    have h := Geo.formAdj_mul (RingHom.id F) hG S e
    rw [hSe, hSadj] at h
    simpa [eStar] using h.symm
  have hstarS : eStar * S = eStar := by
    calc eStar * S = (eStar * ((s⁻¹ : GL ι F) : Matrix ι ι F)) * S := by rw [hstarSinv]
      _ = eStar * (((s⁻¹ : GL ι F) : Matrix ι ι F) * S) := by rw [Matrix.mul_assoc]
      _ = eStar * 1 := by rw [hSinvS]
      _ = eStar := Matrix.mul_one eStar
  have hSU : ∀ t ∈ ({s} : Set (GL ι F)),
      Matrix.transpose ((t : Matrix ι ι F).map (RingHom.id F)) * G *
        (t : Matrix ι ι F) = G := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    simpa [Matrix.map_id] using hs
  have heStarmem : eStar ∈ A := by
    have h := Geo.formAdj_mem_adjoin (RingHom.id F) hG
      (S := ({s} : Set (GL ι F))) hSU he.1
    simpa [A, eStar] using h
  have heStaridem : IsIdempotentElem eStar := by
    rw [isIdempotentElem_iff]
    change formAdj (RingHom.id F) G e * formAdj (RingHom.id F) G e =
      formAdj (RingHom.id F) G e
    rw [← Geo.formAdj_mul (RingHom.id F) hG e e, he.2.1.eq]
  have hformAdj_ne_zero : ∀ {a : Matrix ι ι F},
      formAdj (RingHom.id F) G a = 0 → a = 0 := by
    intro a ha
    have ha' : G⁻¹ * Matrix.transpose a * G = 0 := by
      simpa [formAdj, Matrix.map_id] using ha
    have h1 : Matrix.transpose a * G = 0 := by
      calc Matrix.transpose a * G
          = (G * G⁻¹) * Matrix.transpose a * G := by
              rw [Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
        _ = G * (G⁻¹ * Matrix.transpose a * G) := by
              simp only [Matrix.mul_assoc]
        _ = G * 0 := by rw [ha']
        _ = 0 := Matrix.mul_zero G
    have h2 : Matrix.transpose a = 0 := by
      calc Matrix.transpose a
          = Matrix.transpose a * (G * G⁻¹) := by
              rw [Matrix.mul_nonsing_inv G hG, Matrix.mul_one]
        _ = (Matrix.transpose a * G) * G⁻¹ := by
              simp only [Matrix.mul_assoc]
        _ = 0 * G⁻¹ := by rw [h1]
        _ = 0 := Matrix.zero_mul G⁻¹
    have h3 : a = 0 := by
      have := congrArg Matrix.transpose h2
      simpa using this
    exact h3
  have heStarne : eStar ≠ 0 := by
    intro h0
    exact he.2.2.1 (hformAdj_ne_zero (by simpa [eStar] using h0))
  have himg : Units.val '' ({s} : Set (GL ι F)) =
      ({S} : Set (Matrix ι ι F)) := Set.image_singleton
  have hA' : A = Algebra.adjoin F ({S} : Set (Matrix ι ι F)) := by
    change Algebra.adjoin F (Units.val '' ({s} : Set (GL ι F))) =
      Algebra.adjoin F ({S} : Set (Matrix ι ι F))
    rw [himg]
  have he_adjoin : e ∈ Algebra.adjoin F ({S} : Set (Matrix ι ι F)) := by
    rw [← hA']
    exact he.1
  have hstar_adjoin : eStar ∈ Algebra.adjoin F ({S} : Set (Matrix ι ι F)) := by
    rw [← hA']
    exact heStarmem
  have hcommS : S * eStar = eStar * S :=
    (Algebra.commute_of_mem_adjoin_self hstar_adjoin).eq
  have hSeStar : S * eStar = eStar := by rw [hcommS, hstarS]
  have hscalar_e : ∀ p : Polynomial F,
      Polynomial.aeval S p * e = p.eval 1 • e :=
    fun p => bd1_gf2_aeval_mul_of_mul_eq_self hSe p
  have hscalar_star : ∀ p : Polynomial F,
      Polynomial.aeval S p * eStar = p.eval 1 • eStar :=
    fun p => bd1_gf2_aeval_mul_of_mul_eq_self hSeStar p
  obtain ⟨p, hp⟩ := Algebra.adjoin_mem_exists_aeval (R := F) (x := S) he_adjoin
  obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval (R := F) (x := S) hstar_adjoin
  have hp1 : p.eval 1 = 1 := by
    have h : e = p.eval 1 • e := by
      calc e = e * e := he.2.1.eq.symm
        _ = Polynomial.aeval S p * e := by rw [hp]
        _ = p.eval 1 • e := hscalar_e p
    rcases bd1_gf2_eq_zero_or_one (p.eval 1) with h0 | h1
    · exfalso
      rw [h0, zero_smul] at h
      exact he.2.2.1 h
    · exact h1
  have hq1 : q.eval 1 = 1 := by
    have h : eStar = q.eval 1 • eStar := by
      calc eStar = eStar * eStar := heStaridem.eq.symm
        _ = Polynomial.aeval S q * eStar := by rw [hq]
        _ = q.eval 1 • eStar := hscalar_star q
    rcases bd1_gf2_eq_zero_or_one (q.eval 1) with h0 | h1
    · exfalso
      rw [h0, zero_smul] at h
      exact heStarne h
    · exact h1
  have heeStar : e * eStar = eStar := by
    calc e * eStar = Polynomial.aeval S p * eStar := by rw [hp]
      _ = p.eval 1 • eStar := hscalar_star p
      _ = eStar := by rw [hp1, one_smul]
  have heStare : eStar * e = e := by
    calc eStar * e = Polynomial.aeval S q * e := by rw [hq]
      _ = q.eval 1 • e := hscalar_e q
      _ = e := by rw [hq1, one_smul]
  have hSe_comm : Commute S e := Algebra.commute_of_mem_adjoin_self he_adjoin
  have hcommStar : Commute e eStar :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hstar_adjoin (by
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact hSe_comm.symm)
  have he_eq : e = eStar := by
    calc e = eStar * e := heStare.symm
      _ = e * eStar := hcommStar.eq.symm
      _ = eStar := heeStar
  change eStar = e
  exact he_eq.symm

end CFSG.StandardType.ClassicalPosition
