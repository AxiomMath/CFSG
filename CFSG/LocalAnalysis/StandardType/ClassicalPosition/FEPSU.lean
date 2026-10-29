module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoDualPair
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSUTwisted
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Adapters.StatedQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.Quasithin.Background.G1Basic

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

@[expose] def GGSixLSevenFieldExtCaseCl {X : Type} [Group X] (J : Subgroup X) (t : StatedLieTag)
    (f : ℕ) : Prop :=
  ∃ (t' : StatedLieTag) (m f' : ℕ), (t' = .PSL ∨ t' = .PSU) ∧ f < f' ∧
    LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f' ∧
      ¬ (t' = .PSL ∧ f' = 2 * f ∧ (t = .PSU ∨ t = .twistedE6))

theorem GGSixLSevenFieldExtCaseCl.fieldExtCase {X : Type} [Group X] {J : Subgroup X}
    {t : StatedLieTag} {f : ℕ} (h : GGSixLSevenFieldExtCaseCl J t f) :
    GGSixLSevenFieldExtCase J t f :=
  let ⟨t', m, f', _, h1, h2, h3⟩ := h
  ⟨t', m, f', h1, h2, h3⟩

private lemma fePSU_antidiag_map {F : Type} [Field F] (σ : F →+* F) (n : ℕ) :
    (Unitary.antidiag n : Matrix (Fin n) (Fin n) F).map σ = Unitary.antidiag n := by
  ext i j
  simp only [Unitary.antidiag, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · exact map_one σ
  · exact map_zero σ

private lemma fePSU_transpose_antidiag {F : Type} [Field F] (n : ℕ) :
    Matrix.transpose (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := by
  ext i j
  simp only [Matrix.transpose_apply, Unitary.antidiag, Matrix.of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h']
  · have h' : j ≠ Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h']

private lemma fePSU_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ {a b : Matrix ι ι F}, a ∈ Algebra.adjoin F (Units.val '' S) →
      b ∈ Algebra.adjoin F (Units.val '' S) → a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix ι ι F) * (s' : Matrix ι ι F) =
      (s' : Matrix ι ι F) * (s : Matrix ι ι F)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm F hcommS
  intro a b ha hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin F (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin F (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma fePSU_dichotomy {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e) :
    e = ε ∨ (formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
        (Unitary.antidiag n) e ≠ e ∧
      ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
        (Unitary.antidiag n) e) := by
  classical
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let A : Subalgebra F (Matrix (Fin n) (Fin n) F) := Algebra.adjoin F (Units.val '' S)
  change IsPrimAdjIdemIn σ G A ε at hε
  change IsPrimIdemIn A e at he
  change e = ε ∨ (formAdj σ G e ≠ e ∧ ε = e + formAdj σ G e)
  have hσ : ∀ x, σ (σ x) = x :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    simpa [G] using Unitary.det_antidiag_ne_zero (F := F) n
  have hGh : Matrix.transpose (G.map σ) = G := by
    show Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n
    rw [fePSU_antidiag_map σ n, fePSU_transpose_antidiag n]
  have hSU' : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (Fin n) (Fin n) F).map σ) * G * (s : Matrix (Fin n) (Fin n) F) = G := by
    intro s hs
    simpa [Unitary.conjTr, G, σ] using hSU s hs
  have hAcomm : ∀ {a b : Matrix (Fin n) (Fin n) F}, a ∈ A → b ∈ A → a * b = b * a :=
    fePSU_adjoin_comm hS
  have hstarA : ∀ {a : Matrix (Fin n) (Fin n) F}, a ∈ A → formAdj σ G a ∈ A :=
    fun ha => Geo.formAdj_mem_adjoin σ hG hSU' ha
  have heA : e ∈ A := he.1
  have heidem : IsIdempotentElem e := he.2.1
  have hene : e ≠ 0 := he.2.2.1
  have hprim_e : ∀ e' ∈ A, IsIdempotentElem e' → e' * e = e' → e' = 0 ∨ e' = e := he.2.2.2
  have hstar_e_idem : IsIdempotentElem (formAdj σ G e) := by
    show formAdj σ G e * formAdj σ G e = formAdj σ G e
    rw [← Geo.formAdj_mul σ hG e e, heidem.eq]
  have hstarA_e : formAdj σ G e ∈ A := hstarA heA
  have he_star_comm : e * formAdj σ G e = formAdj σ G e * e := hAcomm heA hstarA_e
  have hee : e * e = e := heidem.eq
  have hstar_e_eps : formAdj σ G e * ε = formAdj σ G e := by
    have hεe : ε * e = e := by rw [hAcomm hε.1 heA, heε]
    have h1 : formAdj σ G (ε * e) = formAdj σ G e := by rw [hεe]
    rw [Geo.formAdj_mul σ hG ε e, hε.2.2.2.1] at h1
    exact h1
  by_cases hfix : formAdj σ G e = e
  · refine Or.inl ?_
    rcases hε.2.2.2.2 e heA heidem hfix heε with h | h
    · exact absurd h hene
    · exact h
  · have hzero : e * formAdj σ G e = 0 := by
      by_cases hx0 : e * formAdj σ G e = 0
      · exact hx0
      · exfalso
        have hxidem : IsIdempotentElem (e * formAdj σ G e) :=
          IsIdempotentElem.mul_of_commute he_star_comm heidem hstar_e_idem
        have hxe : (e * formAdj σ G e) * e = e * formAdj σ G e := by
          rw [Matrix.mul_assoc, ← he_star_comm, ← Matrix.mul_assoc, heidem.eq]
        rcases hprim_e (e * formAdj σ G e) (Subalgebra.mul_mem A heA hstarA_e) hxidem hxe
          with h | h
        · exact hx0 h
        · apply hfix
          calc formAdj σ G e = formAdj σ G (e * formAdj σ G e) := by rw [h]
            _ = formAdj σ G (formAdj σ G e) * formAdj σ G e :=
                Geo.formAdj_mul σ hG e (formAdj σ G e)
            _ = e * formAdj σ G e := by rw [Geo.formAdj_formAdj σ hσ hG hGh e]
            _ = e := h
    have hε'idem : IsIdempotentElem (e + formAdj σ G e) := by
      refine IsIdempotentElem.add heidem hstar_e_idem ?_
      rw [hzero, ← he_star_comm, hzero, add_zero]
    have hstar_ε' : formAdj σ G (e + formAdj σ G e) = e + formAdj σ G e := by
      rw [Geo.formAdj_add, Geo.formAdj_formAdj σ hσ hG hGh e, add_comm]
    have hε'ε : (e + formAdj σ G e) * ε = e + formAdj σ G e := by
      rw [Matrix.add_mul, heε, hstar_e_eps]
    have hε'A : e + formAdj σ G e ∈ A := Subalgebra.add_mem A heA hstarA_e
    have hε'e : (e + formAdj σ G e) * e = e := by
      rw [Matrix.add_mul, hee, ← he_star_comm, hzero, add_zero]
    have hε'ne : e + formAdj σ G e ≠ 0 := by
      intro h0
      rw [h0, Matrix.zero_mul] at hε'e
      exact hene hε'e.symm
    have hε'eq : e + formAdj σ G e = ε := by
      rcases hε.2.2.2.2 (e + formAdj σ G e) hε'A hε'idem hstar_ε' hε'ε with h | h
      · exact absurd h hε'ne
      · exact h
    exact Or.inr ⟨hfix, hε'eq.symm⟩

private lemma fePSU_f_pos {F : Type} [Field F] [Finite F] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) : 1 ≤ f := by
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : 1 < Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · subst h0
    rw [hc] at h2
    norm_num at h2
  · exact hpos

private lemma fePSU_blockField_card {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
      (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K),
      Function.Surjective π ∧
        (∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0) ∧
        Module.finrank F K = d ∧ Nat.card K = (2 ^ f) ^ (2 * d) := by
  obtain ⟨K, hKfield, hKalg, hKfin, π, hsurj, hker, hfinrank⟩ :=
    exists_blockField hS hodd he
  refine ⟨K, hKfield, hKalg, hKfin, π, hsurj, hker, ?_, ?_⟩
  · rw [hfinrank, ← hd]
  · letI : Field K := hKfield
    letI : Algebra F K := hKalg
    letI : Finite K := hKfin
    have hcard : Nat.card K = (Nat.card F) ^ (Module.finrank F K) :=
      Module.natCard_eq_pow_finrank (K := F) (V := K)
    rw [hcard, hc, hfinrank, ← hd]
    rw [← pow_mul]

private lemma fePSU_statedSL_changeField {m : ℕ} {E K : Type} [Field E] [Finite E]
    [Field K] [Finite K] (hcard : Nat.card E = Nat.card K) :
    Nonempty (StatedProj (StatedSL m E) ≃* StatedProj (StatedSL m K)) := by
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card E = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  let φ : E ≃+* K := FiniteField.ringEquivOfCardEq hcard'
  exact ⟨CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSL φ m)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)⟩

private lemma fePSU_dualPair_Geps_commuteA {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n))
    (hu : u ∈ glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      Commute ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a := by
  have hcent : (u : GL (Fin n) F) ∈ Subgroup.centralizer S :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hu)).1
  let M : Matrix (Fin n) (Fin n) F := ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  let C : Subalgebra F (Matrix (Fin n) (Fin n) F) :=
    { carrier := {a | Commute M a},
      mul_mem' := fun ha hb => ha.mul_right hb,
      one_mem' := Commute.one_right M,
      add_mem' := fun ha hb => ha.add_right hb,
      zero_mem' := Commute.zero_right M,
      algebraMap_mem' := fun r => (Algebra.commute_algebraMap_left r M).symm }
  have hle : Algebra.adjoin F (Units.val '' S) ≤ C := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨s, hs, rfl⟩
    change M * (((s : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) =
      (((s : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) * M
    have h : (u : GL (Fin n) F) * s = s * (u : GL (Fin n) F) :=
      (Subgroup.mem_centralizer_iff.mp hcent s hs).symm
    simpa [M, Units.val_mul] using
      congrArg (fun v : GL (Fin n) F => (v : Matrix (Fin n) (Fin n) F)) h
  intro a ha
  exact hle ha

private lemma fePSU_dualPair_Geps_commuteE {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {n : ℕ} (S : Set (GL (Fin n) F))
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n))
    (hu : u ∈ glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) :
    Commute ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) e := by
  exact fePSU_dualPair_Geps_commuteA S u hu e he.1

private lemma fePSU_dualPair_Geps_WKLinear {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {n : ℕ} (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n))
    (hu : u ∈ glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
    (a b : Algebra.adjoin F (Units.val '' S)) :
    ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e) =
      ((a : Matrix (Fin n) (Fin n) F) * e) *
        (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((b : Matrix (Fin n) (Fin n) F) * e)) := by
  have hMa : Commute ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      (a : Matrix (Fin n) (Fin n) F) :=
    fePSU_dualPair_Geps_commuteA S u hu (a : Matrix (Fin n) (Fin n) F) a.2
  have hMb : Commute ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      (b : Matrix (Fin n) (Fin n) F) :=
    fePSU_dualPair_Geps_commuteA S u hu (b : Matrix (Fin n) (Fin n) F) b.2
  have hMe : Commute ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) e :=
    fePSU_dualPair_Geps_commuteE S he u hu
  have heb : e * (b : Matrix (Fin n) (Fin n) F) =
      (b : Matrix (Fin n) (Fin n) F) * e := fePSU_adjoin_comm hS he.1 b.2
  have hbe : ((a : Matrix (Fin n) (Fin n) F) * e) *
        ((b : Matrix (Fin n) (Fin n) F) * e) =
      (a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e := by
    calc ((a : Matrix (Fin n) (Fin n) F) * e) * ((b : Matrix (Fin n) (Fin n) F) * e)
        = (((a : Matrix (Fin n) (Fin n) F) * e) * (b : Matrix (Fin n) (Fin n) F)) * e :=
          (mul_assoc ((a : Matrix (Fin n) (Fin n) F) * e)
            (b : Matrix (Fin n) (Fin n) F) e).symm
      _ = ((a : Matrix (Fin n) (Fin n) F) *
            (e * (b : Matrix (Fin n) (Fin n) F))) * e := by
          rw [mul_assoc (a : Matrix (Fin n) (Fin n) F) e (b : Matrix (Fin n) (Fin n) F)]
      _ = ((a : Matrix (Fin n) (Fin n) F) *
            ((b : Matrix (Fin n) (Fin n) F) * e)) * e := by rw [heb]
      _ = (a : Matrix (Fin n) (Fin n) F) *
            (((b : Matrix (Fin n) (Fin n) F) * e) * e) :=
          mul_assoc (a : Matrix (Fin n) (Fin n) F)
            ((b : Matrix (Fin n) (Fin n) F) * e) e
      _ = (a : Matrix (Fin n) (Fin n) F) *
            ((b : Matrix (Fin n) (Fin n) F) * (e * e)) := by
          rw [mul_assoc (b : Matrix (Fin n) (Fin n) F) e e]
      _ = (a : Matrix (Fin n) (Fin n) F) * ((b : Matrix (Fin n) (Fin n) F) * e) := by
          rw [he.2.1.eq]
      _ = (a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e :=
          (mul_assoc (a : Matrix (Fin n) (Fin n) F) (b : Matrix (Fin n) (Fin n) F) e).symm
  have hL : ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e) =
      (a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e *
        ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    ((hMa.mul_right hMb).mul_right hMe).eq
  have hR : ((a : Matrix (Fin n) (Fin n) F) * e) *
        (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((b : Matrix (Fin n) (Fin n) F) * e)) =
      (a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e *
        ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [(hMb.mul_right hMe).eq]
    rw [← mul_assoc]
    rw [hbe]
  exact hL.trans hR.symm

private lemma fePSU_dualPair_blockPairing_nondegenerate {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det)
    {e w : Matrix ι ι F} (hw : formAdj σ G e * w = w)
    (horth : Matrix.transpose (e.map σ) * G * w = 0) :
    w = 0 := by
  have hGw : G * w = Matrix.transpose (e.map σ) * G * w := by
    have h1 : (G⁻¹ * Matrix.transpose (e.map σ) * G) * w = w := by
      simpa only [formAdj] using hw
    calc G * w = G * ((G⁻¹ * Matrix.transpose (e.map σ) * G) * w) := by rw [h1]
      _ = Matrix.transpose (e.map σ) * G * w := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
                Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  have hzero : G * w = 0 := by rw [hGw, horth]
  calc w = G⁻¹ * (G * w) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
    _ = 0 := by rw [hzero, Matrix.mul_zero]

private lemma fePSU_dualPair_GepsGLK_faithful_decomp {F : Type} [Field F] {n : ℕ}
    (σ : F →+* F) (G : Matrix (Fin n) (Fin n) F) {ε e M : Matrix (Fin n) (Fin n) F}
    (hεeq : ε = e + formAdj σ G e)
    (hMe : M * e = e) (hM1 : M * (1 - ε) = 1 - ε)
    (hMstar : M * formAdj σ G e = formAdj σ G e) :
    M = 1 := by
  have hone : (1 : Matrix (Fin n) (Fin n) F) = e + (1 - ε) + formAdj σ G e := by
    rw [hεeq]; abel
  calc M = M * 1 := (mul_one M).symm
    _ = M * (e + (1 - ε) + formAdj σ G e) := by
          conv_lhs => rw [hone]
    _ = M * e + M * (1 - ε) + M * formAdj σ G e := by rw [mul_add, mul_add]
    _ = e + (1 - ε) + formAdj σ G e := by rw [hMe, hM1, hMstar]
    _ = 1 := hone.symm

private lemma fePSU_dualPair_GepsGLK_action_matrix_linear {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    ∀ u : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      ∀ a b : Algebra.adjoin F (Units.val '' S),
        ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            ((a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e) =
          ((a : Matrix (Fin n) (Fin n) F) * e) *
            (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              ((b : Matrix (Fin n) (Fin n) F) * e)) :=
  fun u a b => fePSU_dualPair_Geps_WKLinear S hS he u.1 u.2 a b

private lemma fePSU_dualPair_GepsGLK_action_matrix_exists {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Algebra F K]
    (hKfr : Module.finrank F K = d)
    (hlin : ∀ u : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      ∀ a b : Algebra.adjoin F (Units.val '' S),
        ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            ((a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) * e) =
          ((a : Matrix (Fin n) (Fin n) F) * e) *
            (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              ((b : Matrix (Fin n) (Fin n) F) * e))) :
    ∃ (m : ℕ), 2 ≤ m ∧
      ∃ φ : glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
          (Matrix (Fin m) (Fin m) K)ˣ,
        Function.Injective φ := by
  refine ⟨n, ?_, ?_⟩
  · have hd_le : d ≤ n * n := by
      rw [hd]
      calc blockDegree (Algebra.adjoin F (Units.val '' S)) e
          = Module.finrank F ((Subalgebra.toSubmodule (Algebra.adjoin F (Units.val '' S))).map
              (LinearMap.mulRight F e)) := rfl
        _ ≤ Module.finrank F (Matrix (Fin n) (Fin n) F) := Submodule.finrank_le _
        _ = n * n := by rw [Module.finrank_matrix]; simp
    have h2 : 2 ≤ n * n := le_trans hdeg hd_le
    by_contra hn
    push Not at hn
    interval_cases n <;> omega
  · refine ⟨(Matrix.GeneralLinearGroup.map (algebraMap F K)).comp
      ((Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype.comp
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).subtype),
      ?_⟩
    exact (Matrix.GeneralLinearGroup.map_injective (algebraMap F K).injective).comp
      (Subtype.coe_injective.comp Subtype.coe_injective)

private lemma fePSU_dualPair_GepsGLK_action_matrix {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Algebra F K]
    (hKfr : Module.finrank F K = d) :
    ∃ (m : ℕ), 2 ≤ m ∧
      ∃ φ : glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
          (Matrix (Fin m) (Fin m) K)ˣ,
        Function.Injective φ :=
  fePSU_dualPair_GepsGLK_action_matrix_exists S hS he heε d hd hdeg K hKfr
    (fePSU_dualPair_GepsGLK_action_matrix_linear S hS he)

private lemma fePSU_isSubnormal_le {G : Type} [Group G] {K H : Subgroup G}
    (h : IsSubnormal K H) : K ≤ H := by
  induction h with
  | refl H => exact le_refl H
  | step hle hnorm hsub ih => exact hle.trans ih

private lemma fePSU_isSubnormal_subgroupOf_refl {G : Type} [Group G] (H : Subgroup G) :
    IsSubnormal (H.subgroupOf H) ⊤ := by
  rw [Subgroup.subgroupOf_self]
  exact IsSubnormal.refl ⊤

private lemma fePSU_isSubnormal_subgroupOf_step_le {G : Type} [Group G] {H M K : Subgroup G}
    (hKM : K ≤ M) : K.subgroupOf H ≤ M.subgroupOf H :=
  Subgroup.subgroupOf_mono H hKM

private lemma fePSU_isSubnormal_subgroupOf_step_normal {G : Type} [Group G] {H M K : Subgroup G}
    (hMH : M ≤ H) (hnorm : (K.subgroupOf M).Normal) :
    ((K.subgroupOf H).subgroupOf (M.subgroupOf H)).Normal := by
  have hEq : (K.subgroupOf H).subgroupOf (M.subgroupOf H) =
      (K.subgroupOf M).comap (Subgroup.subgroupOfEquivOfLe hMH).toMonoidHom := by
    ext x
    rfl
  rw [hEq]
  exact hnorm.comap _

private lemma fePSU_isSubnormal_subgroupOf_step {G : Type} [Group G] {H M K : Subgroup G}
    (hKM : K ≤ M) (hMH : M ≤ H) (hnorm : (K.subgroupOf M).Normal)
    (ih : IsSubnormal (M.subgroupOf H) ⊤) :
    IsSubnormal (K.subgroupOf H) ⊤ :=
  IsSubnormal.step (fePSU_isSubnormal_subgroupOf_step_le hKM)
    (fePSU_isSubnormal_subgroupOf_step_normal hMH hnorm) ih

private lemma fePSU_isSubnormal_subgroupOf {G : Type} [Group G] {K H : Subgroup G}
    (h : IsSubnormal K H) : IsSubnormal (K.subgroupOf H) ⊤ := by
  induction h with
  | refl H => exact fePSU_isSubnormal_subgroupOf_refl H
  | step hle hnorm hsub ih =>
      exact fePSU_isSubnormal_subgroupOf_step hle (fePSU_isSubnormal_le hsub) hnorm ih

private lemma fePSU_isSubnormal_subgroupOf_map_normal {G G' : Type} [Group G] [Group G']
    (f : G →* G') {H M : Subgroup G} (hle : H ≤ M) (hnorm : (H.subgroupOf M).Normal) :
    ((H.map f).subgroupOf (M.map f)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨h, hhH, hfh⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
  obtain ⟨k, hkM, hfk⟩ := Subgroup.mem_map.mp (show (g : G') ∈ M.map f from g.2)
  have hconj : k * h * k⁻¹ ∈ H := by
    have hhM : h ∈ M := hle hhH
    exact hnorm.conj_mem (⟨h, hhM⟩ : M) (show (⟨h, hhM⟩ : M) ∈ H.subgroupOf M from hhH)
      (⟨k, hkM⟩ : M)
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hfk, ← hfh]
  exact Subgroup.mem_map.mpr ⟨k * h * k⁻¹, hconj, by rw [map_mul, map_mul, map_inv]⟩

private lemma fePSU_isSubnormal_map {G G' : Type} [Group G] [Group G'] (f : G →* G')
    {K H : Subgroup G} (h : IsSubnormal K H) :
    IsSubnormal (K.map f) (H.map f) := by
  induction h with
  | refl H => exact IsSubnormal.refl (H.map f)
  | step hle hnorm hsub ih =>
      exact IsSubnormal.step (Subgroup.map_mono hle)
        (fePSU_isSubnormal_subgroupOf_map_normal f hle hnorm) ih

private lemma fePSU_isSubnormal_map_top {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) {K : Subgroup G} (h : IsSubnormal K ⊤) :
    IsSubnormal (K.map f) ⊤ := by
  have := fePSU_isSubnormal_map f h
  rwa [Subgroup.map_top_of_surjective f hf] at this

private lemma fePSU_dualPair_heldSize_eq_unique_mapSubnormal {F : Type} [Field F] [Finite F] [CharP
    F 2] {f : ℕ} (n : ℕ) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hsub : IsSubnormal J' (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))) :
    IsSubnormal (((J'.subgroupOf (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (QuotientGroup.mk' (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))))) ⊤ := by
  exact fePSU_isSubnormal_map_top (QuotientGroup.mk' (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))))
            (QuotientGroup.mk'_surjective _)
    (fePSU_isSubnormal_subgroupOf hsub)

private lemma fePSU_isSubnormal_subgroupOf_isSubnormal {G : Type} [Group G] {K H : Subgroup G}
    (h : IsSubnormal K H) : Subgroup.IsSubnormal (K.subgroupOf H) := by
  induction h with
  | refl H =>
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.IsSubnormal.top
  | @step L M K hle hnorm hsub ih =>
      have hle' : L.subgroupOf K ≤ M.subgroupOf K := Subgroup.comap_mono hle
      refine Subgroup.IsSubnormal.step (L.subgroupOf K) (M.subgroupOf K) hle' ih ?_
      rw [Subgroup.normal_subgroupOf_iff hle']
      intro x g hx hg
      exact (Subgroup.normal_subgroupOf_iff hle).1 hnorm x g hx hg

private lemma fePSU_isSubnormal_eq_bot_or_eq_of_isSimpleGroup {G : Type} [Group G]
    {K H : Subgroup G} (h : IsSubnormal K H) (hH : IsSimpleGroup ↥H) : K = ⊥ ∨ K = H := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hH
      (fePSU_isSubnormal_subgroupOf_isSubnormal h) with h1 | h1
  · exact Or.inl ((Subgroup.subgroupOf_eq_bot.1 h1).eq_bot_of_le (fePSU_isSubnormal_le h))
  · exact Or.inr (le_antisymm (fePSU_isSubnormal_le h) (Subgroup.subgroupOf_eq_top.1 h1))

private lemma fePSU_isSubnormal_eq_bot_or_top {G : Type} [Group G] [IsSimpleGroup G]
    {K : Subgroup G} (h : IsSubnormal K ⊤) : K = ⊥ ∨ K = ⊤ := by
  have hH : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).isSimpleGroup
  simpa using fePSU_isSubnormal_eq_bot_or_eq_of_isSimpleGroup h hH

private lemma fePSU_dualPair_heldSize_eq_unique_quotDichotomy {F : Type} [Field F] [Finite F] [CharP
    F 2] {f : ℕ} (n : ℕ) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hsub : IsSubnormal J' (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))
    (hqH : CFSG.Assembly.IsQuasisimple ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))) :
    ((J'.subgroupOf (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (QuotientGroup.mk' (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))))) = ⊥ ∨
            ((J'.subgroupOf (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (QuotientGroup.mk' (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))))) = ⊤ := by
  haveI := hqH.2
  exact fePSU_isSubnormal_eq_bot_or_top
    (fePSU_dualPair_heldSize_eq_unique_mapSubnormal n S hsub)

private lemma fePSU_quot_pullback_of_map_mk' {G : Type} [Group G] {J H : Subgroup G} (hJH : J ≤ H)
    (h : (J.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H)) = ⊥ ∨
      (J.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H)) = ⊤) :
    J ≤ (Subgroup.center ↥H).map H.subtype ∨
      J ⊔ (Subgroup.center ↥H).map H.subtype = H := by
  rcases h with h | h
  · left
    have hker : J.subgroupOf H ≤ Subgroup.center ↥H := by
      have := (Subgroup.map_eq_bot_iff (J.subgroupOf H)).mp h
      rwa [QuotientGroup.ker_mk'] at this
    have := Subgroup.map_mono (f := H.subtype) hker
    rwa [Subgroup.map_subgroupOf_eq_of_le hJH] at this
  · right
    have hsup : Subgroup.center ↥H ⊔ J.subgroupOf H = ⊤ := by
      have := QuotientGroup.comap_map_mk' (Subgroup.center ↥H) (J.subgroupOf H)
      rw [h, Subgroup.comap_top] at this
      exact this.symm
    have hmap := congrArg (Subgroup.map H.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJH, Subgroup.map_top,
      Subgroup.range_subtype] at hmap
    exact (sup_comm ..).trans hmap

private lemma fePSU_dualPair_heldSize_eq_unique_pullback {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (n : ℕ) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hle : J' ≤ Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) :
    (((J'.subgroupOf (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (QuotientGroup.mk' (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))))) = ⊥ ∨
            ((J'.subgroupOf (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (QuotientGroup.mk' (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))))) = ⊤) →
      J' ≤ (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).subtype ∨ J' ⊔
            (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).subtype =
            Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) := by
  intro h
  exact fePSU_quot_pullback_of_map_mk' hle h

private lemma fePSU_dualPair_heldSize_eq_unique_dichotomy {F : Type} [Field F] [Finite F] [CharP F
    2] {f : ℕ} (n : ℕ) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hle : J' ≤ Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))
    (hsub : IsSubnormal J' (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))
    (hqH : CFSG.Assembly.IsQuasisimple ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))) :
    J' ≤ (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).subtype ∨ J' ⊔
            (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).subtype =
            Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) :=
  fePSU_dualPair_heldSize_eq_unique_pullback n S hle
    (fePSU_dualPair_heldSize_eq_unique_quotDichotomy n S hsub hqH)

private lemma fePSU_isQuasisimple_not_isMulCommutative {G : Type} [Group G]
    (h : CFSG.Assembly.IsQuasisimple G) : ¬ IsMulCommutative G := by
  intro hcomm
  haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := h.2
  haveI : IsMulCommutative G := hcomm
  have hsub : Subsingleton (G ⧸ Subgroup.center G) := by
    rw [Subgroup.center_eq_top]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton _) hsub

private lemma fePSU_isMulCommutative_of_le_center_map {G : Type} [Group G] {J H : Subgroup G}
    (hleZ : J ≤ (Subgroup.center ↥H).map H.subtype) : IsMulCommutative ↥J := by
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  have hcomm := mul_comm' (⟨(a : G), hleZ a.2⟩ : ↥((Subgroup.center ↥H).map H.subtype))
    ⟨(b : G), hleZ b.2⟩
  simpa using congrArg Subtype.val hcomm

private lemma fePSU_dualPair_heldSize_eq_unique_bot {F : Type} [Field F] [Finite F] [CharP F 2] {f :
    ℕ} (n : ℕ) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hJq : CFSG.Assembly.IsQuasisimple ↥J') :
    J' ≤ (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).subtype →
            False := by
  intro hleZ
  exact fePSU_isQuasisimple_not_isMulCommutative hJq
    (fePSU_isMulCommutative_of_le_center_map hleZ)

private lemma fePSU_eq_of_sup_center_eq_top {A : Type} [Group A] {J K : Subgroup A} (hKq :
    CFSG.Assembly.IsQuasisimple ↥K)
    (hJK : J ≤ K) (hgen : J ⊔ (Subgroup.center ↥K).map K.subtype = K) :
    J = K := by
  have hsupeq : J.subgroupOf K ⊔ Subgroup.center ↥K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJK, hgen, Subgroup.map_top,
      Subgroup.range_subtype]
  haveI : (J.subgroupOf K).Normal := by
    have hZn : Subgroup.center ↥K ≤ Subgroup.normalizer (J.subgroupOf K : Set ↥K) :=
      (Subgroup.center_le_centralizer (J.subgroupOf K : Set ↥K)).trans
        (Subgroup.centralizer_le_normalizer (J.subgroupOf K : Set ↥K))
    have hnorm : Subgroup.normalizer (J.subgroupOf K : Set ↥K) = ⊤ := by
      have := sup_le Subgroup.le_normalizer hZn
      rw [hsupeq] at this
      exact top_le_iff.mp this
    exact (Subgroup.normalizer_eq_top_iff).mp hnorm
  have hcomm : _root_.commutator ↥K ≤ J.subgroupOf K :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := J.subgroupOf K) hsupeq
      (inferInstance : IsMulCommutative (Subgroup.center ↥K))
  have hNtop : J.subgroupOf K = ⊤ := by
    rw [hKq.1] at hcomm
    exact top_le_iff.mp hcomm
  calc J = (J.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hJK).symm
    _ = (⊤ : Subgroup ↥K).map K.subtype := by rw [hNtop]
    _ = K := by rw [Subgroup.map_top, Subgroup.range_subtype]

private lemma fePSU_dualPair_heldSize_eq_unique_top {F : Type} [Field F] [Finite F] [CharP F 2] {f :
    ℕ} (n : ℕ) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hle : J' ≤ Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))
    (hqH : CFSG.Assembly.IsQuasisimple ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))) :
    J' ⊔ (Subgroup.center ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))).map
            (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).subtype =
            Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) → J' =
            Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) := by
  intro hgen
  exact fePSU_eq_of_sup_center_eq_top hqH hle hgen

private lemma fePSU_dualPair_heldSize_eq_unique {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (n : ℕ) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hJq : CFSG.Assembly.IsQuasisimple ↥J')
    (hle : J' ≤ Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))
    (hsub : IsSubnormal J' (Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))
    (hqH : CFSG.Assembly.IsQuasisimple ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))) :
    J' = Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) := by
  rcases fePSU_dualPair_heldSize_eq_unique_dichotomy n S hle hsub hqH with hcent | hgen
  · exact False.elim (fePSU_dualPair_heldSize_eq_unique_bot n S hJq hcent)
  · exact fePSU_dualPair_heldSize_eq_unique_top n S hle hqH hgen

private lemma fePSU_dualPair_heldSize_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (n : ℕ)
    (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (hq : CFSG.Assembly.IsQuasisimple ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))) :
    J' = Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) :=
  fePSU_dualPair_heldSize_eq_unique n S
    hJε.2.2 hJε.1 hJε.2.1 hq

private lemma fePSU_blockCentralizer_commute_adjoin {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (u : glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
    {a : Matrix (Fin n) (Fin n) F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * a =
      a * ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  (fePSU_dualPair_Geps_commuteA S u.1 u.2 a ha).eq

private lemma fePSU_blockCentralizer_stable {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F))
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (u : glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) :
    ∀ w ∈ LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVecLin ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w ∈
        LinearMap.range (Matrix.mulVecLin e) := by
  let M : Matrix (Fin n) (Fin n) F := ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  intro w hw
  obtain ⟨v, hv⟩ := hw
  refine ⟨Matrix.mulVec M v, ?_⟩
  rw [← hv]
  calc Matrix.mulVecLin e (Matrix.mulVec M v)
      = Matrix.mulVec e (Matrix.mulVec M v) := rfl
    _ = Matrix.mulVec (e * M) v := Matrix.mulVec_mulVec v e M
    _ = Matrix.mulVec (M * e) v := by
          rw [fePSU_blockCentralizer_commute_adjoin S u he.1]
    _ = Matrix.mulVec M (Matrix.mulVec e v) := (Matrix.mulVec_mulVec v M e).symm
    _ = Matrix.mulVecLin M (Matrix.mulVecLin e v) := rfl

private lemma fePSU_blockAction {F : Type} [Field F] {n : ℕ}
    (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ actA : Algebra.adjoin F (Units.val '' S) →ₐ[F]
        Module.End F (LinearMap.range (Matrix.mulVecLin e)),
      ∀ (a : Algebra.adjoin F (Units.val '' S))
        (w : LinearMap.range (Matrix.mulVecLin e)),
        (actA a w : Fin n → F) =
          Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) w := by
  classical
  let A := Algebra.adjoin F (Units.val '' S)
  let W : Submodule F (Fin n → F) := LinearMap.range (Matrix.mulVecLin e)
  have hpair : (Units.val '' S : Set (Matrix (Fin n) (Fin n) F)).Pairwise Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (Fin n) (Fin n) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hcomm : ∀ a : A,
      (a : Matrix (Fin n) (Fin n) F) * e = e * (a : Matrix (Fin n) (Fin n) F) := by
    intro a
    exact congrArg Subtype.val (mul_comm a (⟨e, he.1⟩ : A))
  let actA : A →ₐ[F] Module.End F W :=
  { toFun := fun a =>
      ((Matrix.mulVecLin (a : Matrix (Fin n) (Fin n) F)).comp W.subtype).codRestrict W
        (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          obtain ⟨u, hu⟩ := v.2
          rw [← hu]
          refine ⟨Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) u, ?_⟩
          calc Matrix.mulVecLin e (Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) u)
              = Matrix.mulVec e (Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) u) := rfl
            _ = Matrix.mulVec (e * (a : Matrix (Fin n) (Fin n) F)) u :=
                  Matrix.mulVec_mulVec u e (a : Matrix (Fin n) (Fin n) F)
            _ = Matrix.mulVec ((a : Matrix (Fin n) (Fin n) F) * e) u := by rw [hcomm a]
            _ = Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) (Matrix.mulVec e u) :=
                  (Matrix.mulVec_mulVec u (a : Matrix (Fin n) (Fin n) F) e).symm
            _ = Matrix.mulVecLin a (Matrix.mulVecLin e u) := rfl)
    map_one' := by ext w; simp
    map_mul' := by intro a b; ext w; simp
    map_zero' := by ext w; simp
    map_add' := by intro a b; ext w; simp
    commutes' := by
      intro c
      ext w
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
        Submodule.coe_subtype, Matrix.mulVecLin_apply, Subalgebra.coe_algebraMap,
        Module.algebraMap_end_apply, Matrix.algebraMap_eq_diagonal, Submodule.coe_smul]
      rw [show algebraMap F (Fin n → F) c = fun _ => c from rfl,
        Matrix.diagonal_const_mulVec] }
  refine ⟨actA, ?_⟩
  intro a w
  rfl

private lemma fePSU_blockAction_ker {F : Type} [Field F] {n : ℕ}
    (S : Set (GL (Fin n) F))
    {e : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0)
    (actA : Algebra.adjoin F (Units.val '' S) →ₐ[F]
      Module.End F (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (a : Algebra.adjoin F (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actA a w : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) w) :
    RingHom.ker (π : Algebra.adjoin F (Units.val '' S) →+* K) ≤
      RingHom.ker (actA : Algebra.adjoin F (Units.val '' S) →+*
        Module.End F (LinearMap.range (Matrix.mulVecLin e))) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  have hae : (a : Matrix (Fin n) (Fin n) F) * e = 0 := (hπker a).mp ha
  refine LinearMap.ext fun w => Subtype.ext ?_
  change (actA a w : Fin n → F) = 0
  rw [hact a w]
  obtain ⟨v, hv⟩ := w.2
  rw [← hv, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec v (a : Matrix (Fin n) (Fin n) F) e, hae, Matrix.zero_mulVec]

private lemma fePSU_blockKAction {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {n : ℕ}
    (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (K : Type) [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0) :
    ∃ (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)))
      (actK : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        Module.End K (LinearMap.range (Matrix.mulVecLin e))),
      (∀ (u : glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
        (w : LinearMap.range (Matrix.mulVecLin e)),
        (actK u w : Fin n → F) =
          Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w) ∧
      (∀ (a : Algebra.adjoin F (Units.val '' S)) (w : LinearMap.range (Matrix.mulVecLin e)),
        ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) =
          Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) w) := by

  classical
  obtain ⟨actA, hact⟩ := fePSU_blockAction S hS he
  have hker : RingHom.ker (π : Algebra.adjoin (F) (Units.val '' S) →+* K) ≤
      RingHom.ker (actA : Algebra.adjoin (F) (Units.val '' S) →+*
        Module.End (F) (LinearMap.range (Matrix.mulVecLin e))) :=
    fePSU_blockAction_ker S K π hπker actA hact
  have hp : Function.Surjective (π : Algebra.adjoin (F) (Units.val '' S) →+* K) :=
    fun k => hπsurj k
  let ψ : K →+* Module.End (F) (LinearMap.range (Matrix.mulVecLin e)) :=
    (Ideal.Quotient.lift
      (RingHom.ker (π : Algebra.adjoin (F) (Units.val '' S) →+* K))
      (actA : Algebra.adjoin (F) (Units.val '' S) →+*
        Module.End (F) (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha))).comp
      (RingHom.quotientKerEquivOfSurjective
        (f := (π : Algebra.adjoin (F) (Units.val '' S) →+* K)) hp).symm.toRingHom
  have hψ : ∀ a : Algebra.adjoin (F) (Units.val '' S), ψ (π a) = actA a :=
    fun a => by
    change (Ideal.Quotient.lift
      (RingHom.ker (π : Algebra.adjoin (F) (Units.val '' S) →+* K))
      (actA : Algebra.adjoin (F) (Units.val '' S) →+*
        Module.End (F) (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha)))
      ((RingHom.quotientKerEquivOfSurjective
        (f := (π : Algebra.adjoin (F) (Units.val '' S) →+* K)) hp).symm
        ((π : Algebra.adjoin (F) (Units.val '' S) →+* K) a)) = actA a
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.compHom (LinearMap.range (Matrix.mulVecLin e)) ψ
  have htower : IsScalarTower (F) K (LinearMap.range (Matrix.mulVecLin e)) :=
    ⟨fun c k w => by
    change (ψ (c • k)) w = c • ((ψ k) w)
    obtain ⟨a, rfl⟩ := hπsurj k
    rw [← map_smul π c a, hψ (c • a), hψ a, map_smul]
    rfl⟩
  let rhoF (u : glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      n).subtype S ε) :
      LinearMap.range (Matrix.mulVecLin e) →ₗ[F]
        LinearMap.range (Matrix.mulVecLin e) :=
    ((Matrix.mulVecLin ((u : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) (F))).comp
      (LinearMap.range (Matrix.mulVecLin e)).subtype).codRestrict
        (LinearMap.range (Matrix.mulVecLin e)) (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          exact fePSU_blockCentralizer_stable S he u v v.2)
  have hrhoF_apply (u : glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2
      f) n).subtype S ε)
      (v : LinearMap.range (Matrix.mulVecLin e)) :
      (rhoF u v : Fin n → F) =
        Matrix.mulVec ((u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) (F)) v := rfl
  have hrhoF_smul (u : glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2
      f) n).subtype S ε) (k : K)
      (v : LinearMap.range (Matrix.mulVecLin e)) : rhoF u (k • v) = k • rhoF u v := by
    obtain ⟨a, ha⟩ := hπsurj k
    have hψk : ψ k = actA a := by rw [← ha, hψ a]
    apply Subtype.ext
    change (rhoF u (ψ k v) : Fin n → F) =
      (ψ k (rhoF u v) : Fin n → F)
    rw [hψk]
    have h1 : (rhoF u (actA a v) : Fin n → F) =
        Matrix.mulVec ((u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) (F))
          (Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
            (v : Fin n → F)) := by
      rw [hrhoF_apply, hact a v]
    have h2 : (actA a (rhoF u v) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
          (Matrix.mulVec ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F))
            (v : Fin n → F)) := by
      rw [hact a (rhoF u v), hrhoF_apply]
    rw [h1, h2]
    calc Matrix.mulVec ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F))
            (Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
              (v : Fin n → F))
        = Matrix.mulVec (((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) *
            (a : Matrix (Fin n) (Fin n) (F)))
            (v : Fin n → F) :=
          Matrix.mulVec_mulVec (v : Fin n → F)
            ((u : GL (Fin n) F) :
              Matrix (Fin n) (Fin n) (F))
            (a : Matrix (Fin n) (Fin n) (F))
      _ = Matrix.mulVec ((a : Matrix (Fin n) (Fin n) (F)) *
            ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)))
            (v : Fin n → F) := by
          rw [fePSU_blockCentralizer_commute_adjoin S u a.2]
      _ = Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
            (Matrix.mulVec ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F))
            (v : Fin n → F)) :=
          (Matrix.mulVec_mulVec (v : Fin n → F)
            (a : Matrix (Fin n) (Fin n) (F))
            ((u : GL (Fin n) F) :
              Matrix (Fin n) (Fin n) (F))).symm
  let rhoK (u : glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      n).subtype S ε) :
      LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e) :=
    { toFun := fun v => rhoF u v
      map_add' := fun v v' => (rhoF u).map_add v v'
      map_smul' := fun k v => hrhoF_smul u k v }
  refine ⟨inferInstance, htower, ?_, ?_, ?_⟩
  · refine
      { toFun := rhoK
        map_one' := ?_
        map_mul' := ?_ }
    · refine LinearMap.ext fun v => Subtype.ext ?_
      change (rhoF 1 v : Fin n → F) =
        (v : Fin n → F)
      rw [hrhoF_apply]
      change Matrix.mulVec (1 : Matrix (Fin n) (Fin n) (F)) v =
        (v : Fin n → F)
      rw [Matrix.one_mulVec]
    · intro u u'
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (rhoF (u * u') v : Fin n → F) =
        (rhoF u (rhoF u' v) : Fin n → F)
      rw [hrhoF_apply, hrhoF_apply, hrhoF_apply]
      have hcoe : (((u * u' : glBlockCentralizer (Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) :
            GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) =
          ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) *
          ((u' : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) := rfl
      rw [hcoe, Matrix.mulVec_mulVec]
  · intro u w
    exact hrhoF_apply u w
  · intro a w
    change (ψ (π a) w : Fin n → F) =
      Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) (w : Fin n → F)
    rw [hψ a]
    exact hact a w



private lemma fePSU_dualPair_GepsGLK_extension_left {F : Type} [Field F] {n : ℕ}
    (S : Set (GL (Fin n) F))
    {K : Type} [Field K] [Algebra F K] {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))]
    (T : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e)) :
    ∃ N : Matrix (Fin n) (Fin n) F,
      N * e = N ∧
        (∀ w : LinearMap.range (Matrix.mulVecLin e),
          Matrix.mulVec N (w : Fin n → F) = (T w : Fin n → F)) := by
  let W₀ := LinearMap.range (Matrix.mulVecLin e)
  let proj : (Fin n → F) →ₗ[F] W₀ :=
    (Matrix.mulVecLin e).codRestrict W₀ (fun v => LinearMap.mem_range.mpr ⟨v, rfl⟩)
  let Nop : (Fin n → F) →ₗ[F] (Fin n → F) :=
    W₀.subtype.comp
      (((T : W₀ →ₗ[K] W₀).restrictScalars F).comp proj)
  let N : Matrix (Fin n) (Fin n) F := LinearMap.toMatrix' Nop
  have hproj : ∀ w : W₀, proj w = w := by
    intro w
    apply Subtype.ext
    obtain ⟨v, hv⟩ := w.2
    change Matrix.mulVec e (w : Fin n → F) = (w : Fin n → F)
    rw [← hv]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]
  have hNop_dom : Nop.comp (Matrix.toLin' e) = Nop := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, Matrix.toLin'_apply]
    have hp : proj (Matrix.mulVec e v) = proj v := by
      apply Subtype.ext
      change Matrix.mulVec e (Matrix.mulVec e v) = Matrix.mulVec e v
      rw [Matrix.mulVec_mulVec, he.2.1.eq]
    simp only [Nop, LinearMap.comp_apply]
    rw [hp]
  refine ⟨N, ?_, ?_⟩
  · have he' : e = LinearMap.toMatrix' (Matrix.toLin' e) := (LinearMap.toMatrix'_toLin' e).symm
    rw [he', ← LinearMap.toMatrix'_comp, hNop_dom]
  · intro w
    have h1 : Matrix.mulVec N (w : Fin n → F) = Nop (w : Fin n → F) :=
      LinearMap.toMatrix'_mulVec Nop (w : Fin n → F)
    rw [h1]
    change Nop (w : Fin n → F) = (T w : Fin n → F)
    simp only [Nop, LinearMap.comp_apply]
    rw [hproj w]
    rfl

private lemma fePSU_dualPair_GepsGLK_extension_right {F : Type} [Field F] {n : ℕ}
    (S : Set (GL (Fin n) F))
    {K : Type} [Field K] [Algebra F K] {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))]
    (T : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    {N : Matrix (Fin n) (Fin n) F} (hN : N * e = N)
    (hNv : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVec N (w : Fin n → F) = (T w : Fin n → F)) :
    ∃ N' : Matrix (Fin n) (Fin n) F,
      N' * e = N' ∧
        (∀ w : LinearMap.range (Matrix.mulVecLin e),
          Matrix.mulVec N' (w : Fin n → F) = (T.symm w : Fin n → F)) ∧
        N' * N = e := by
  let W₀ := LinearMap.range (Matrix.mulVecLin e)
  let proj : (Fin n → F) →ₗ[F] W₀ :=
    (Matrix.mulVecLin e).codRestrict W₀ (fun v => LinearMap.mem_range.mpr ⟨v, rfl⟩)
  let Nop' : (Fin n → F) →ₗ[F] (Fin n → F) :=
    W₀.subtype.comp (((T.symm : W₀ →ₗ[K] W₀).restrictScalars F).comp proj)
  let N' : Matrix (Fin n) (Fin n) F := LinearMap.toMatrix' Nop'
  have hproj : ∀ w : W₀, proj w = w := by
    intro w
    apply Subtype.ext
    obtain ⟨v, hv⟩ := w.2
    change Matrix.mulVec e (w : Fin n → F) = (w : Fin n → F)
    rw [← hv]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]
  have hNop'_dom : Nop'.comp (Matrix.toLin' e) = Nop' := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, Matrix.toLin'_apply]
    have hp : proj (Matrix.mulVec e v) = proj v := by
      apply Subtype.ext
      change Matrix.mulVec e (Matrix.mulVec e v) = Matrix.mulVec e v
      rw [Matrix.mulVec_mulVec, he.2.1.eq]
    simp only [Nop', LinearMap.comp_apply]
    rw [hp]
  have htoLinN : ∀ v : Fin n → F, Matrix.toLin' N v = (T (proj v) : Fin n → F) := by
    intro v
    have h1 : Matrix.toLin' N v = Matrix.toLin' N (Matrix.toLin' e v) := by
      have h2 : Matrix.toLin' (N * e) v = Matrix.toLin' N (Matrix.toLin' e v) :=
        Matrix.toLin'_mul_apply N e v
      rwa [hN] at h2
    rw [h1]
    have h4 : Matrix.toLin' e v = (proj v : Fin n → F) := by
      rw [Matrix.toLin'_apply]
      rfl
    rw [h4, Matrix.toLin'_apply]
    exact hNv (proj v)
  refine ⟨N', ?_, ?_, ?_⟩
  · have he' : e = LinearMap.toMatrix' (Matrix.toLin' e) := (LinearMap.toMatrix'_toLin' e).symm
    rw [he', ← LinearMap.toMatrix'_comp, hNop'_dom]
  · intro w
    have h1 : Matrix.mulVec N' (w : Fin n → F) = Nop' (w : Fin n → F) :=
      LinearMap.toMatrix'_mulVec Nop' (w : Fin n → F)
    rw [h1]
    change Nop' (w : Fin n → F) = (T.symm w : Fin n → F)
    simp only [Nop', LinearMap.comp_apply]
    rw [hproj w]
    rfl
  · have he' : e = LinearMap.toMatrix' (Matrix.toLin' e) := (LinearMap.toMatrix'_toLin' e).symm
    have hN' : N = LinearMap.toMatrix' (Matrix.toLin' N) := (LinearMap.toMatrix'_toLin' N).symm
    rw [he', hN']
    change LinearMap.toMatrix' Nop' * LinearMap.toMatrix' (Matrix.toLin' N) =
      LinearMap.toMatrix' (Matrix.toLin' e)
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply]
    change Nop' (Matrix.toLin' N v) = Matrix.toLin' e v
    rw [htoLinN v]
    have h4 : Matrix.toLin' e v = (proj v : Fin n → F) := by
      rw [Matrix.toLin'_apply]
      rfl
    rw [h4]
    simp only [Nop', LinearMap.comp_apply]
    rw [hproj (T (proj v))]
    simp

private noncomputable def fePSU_dualPair_GepsGLK_extensionGraph {F : Type} [Field F] {n : ℕ}
    (σ : F →+* F) (G e N N' : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  N + formAdj σ G N' * formAdj σ G e + (1 - (e + formAdj σ G e))

private lemma fePSU_dualPair_GepsGLK_extension_graph_adjoint {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F)
    (hσ : ∀ x, σ (σ x) = x) (hG : IsUnit G.det) (hGh : Matrix.transpose (G.map σ.toRingHom) = G) :
    formAdj σ.toRingHom G (fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N') =
      formAdj σ.toRingHom G N + e * N' + (1 - (e + formAdj σ.toRingHom G e)) := by
  have hbar_e : formAdj σ.toRingHom G (formAdj σ.toRingHom G e) = e :=
    Geo.formAdj_formAdj σ.toRingHom hσ hG hGh e
  have hbar_N' : formAdj σ.toRingHom G (formAdj σ.toRingHom G N') = N' :=
    Geo.formAdj_formAdj σ.toRingHom hσ hG hGh N'
  have hbar_add : formAdj σ.toRingHom G (e + formAdj σ.toRingHom G e) =
      e + formAdj σ.toRingHom G e := by
    rw [Geo.formAdj_add, hbar_e, add_comm]
  have hbar_one_sub : formAdj σ.toRingHom G (1 - (e + formAdj σ.toRingHom G e)) =
      1 - (e + formAdj σ.toRingHom G e) := by
    rw [sub_eq_add_neg, Geo.formAdj_add, Geo.formAdj_one σ.toRingHom hG]
    congr 1
    rw [show -(e + formAdj σ.toRingHom G e) = (-1 : F) • (e + formAdj σ.toRingHom G e) from
      (neg_one_smul F _).symm, Geo.formAdj_smul, map_neg, map_one, hbar_add, neg_one_smul]
  unfold fePSU_dualPair_GepsGLK_extensionGraph
  rw [Geo.formAdj_add, Geo.formAdj_add, Geo.formAdj_mul σ.toRingHom hG, hbar_e, hbar_N',
    hbar_one_sub]

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_expand {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) :
    (formAdj σ.toRingHom G N + e * N' + (1 - (e + formAdj σ.toRingHom G e))) *
        fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N' =
      (formAdj σ.toRingHom G N * N +
          formAdj σ.toRingHom G N * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
          formAdj σ.toRingHom G N * (1 - (e + formAdj σ.toRingHom G e))) +
        ((e * N') * N + (e * N') * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
          (e * N') * (1 - (e + formAdj σ.toRingHom G e))) +
        ((1 - (e + formAdj σ.toRingHom G e)) * N +
          (1 - (e + formAdj σ.toRingHom G e)) *
            (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
          (1 - (e + formAdj σ.toRingHom G e)) * (1 - (e + formAdj σ.toRingHom G e))) := by
  unfold fePSU_dualPair_GepsGLK_extensionGraph
  noncomm_ring

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_e_idem {F : Type} [Field F]
    {n : ℕ} (e N N' : Matrix (Fin n) (Fin n) F)
    (hN : N * e = N) (hcomp : N' * N = e) :
    e * e = e := by
  calc e * e = (N' * N) * e := by rw [← hcomp]
    _ = N' * (N * e) := by rw [mul_assoc]
    _ = N' * N := by rw [hN]
    _ = e := hcomp

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_star_idem {F : Type} [Field F]
    {n : ℕ} (σ : F ≃+* F) (G e : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (he : e * e = e) :
    formAdj σ.toRingHom G e * formAdj σ.toRingHom G e = formAdj σ.toRingHom G e := by
  rw [← Geo.formAdj_mul σ.toRingHom hG e e, he]

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_barN {F : Type} [Field F]
    {n : ℕ} (σ : F ≃+* F) (G e N : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hN : N * e = N) :
    formAdj σ.toRingHom G N = formAdj σ.toRingHom G e * formAdj σ.toRingHom G N := by
  conv_lhs => rw [← hN]
  rw [Geo.formAdj_mul σ.toRingHom hG N e]

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_middle {F : Type} [Field F]
    {n : ℕ} (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hcomp : N' * N = e)
    (hstar : formAdj σ.toRingHom G e * formAdj σ.toRingHom G e = formAdj σ.toRingHom G e) :
    formAdj σ.toRingHom G N * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) =
      formAdj σ.toRingHom G e := by
  rw [← mul_assoc, ← Geo.formAdj_mul σ.toRingHom hG N' N, hcomp, hstar]

private lemma fePSU_dualPair_GepsGLK_mulVec_e_fixes {F : Type} [Field F] {n : ℕ}
    {e : Matrix (Fin n) (Fin n) F} (he : e * e = e) {u : Fin n → F}
    (hu : u ∈ LinearMap.range (Matrix.mulVecLin e)) :
    Matrix.mulVec e u = u := by
  obtain ⟨u', hu'⟩ := hu
  rw [← hu', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]

private lemma fePSU_dualPair_GepsGLK_extension_graph_e_mul_N {F : Type} [Field F] {n : ℕ}
    {K : Type} [Field K] {e : Matrix (Fin n) (Fin n) F}
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    {N : Matrix (Fin n) (Fin n) F}
    (T : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (he : e * e = e) (hN : N * e = N)
    (hNv : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVec N (w : Fin n → F) = (T w : Fin n → F)) :
    e * N = N := by
  have hfix : ∀ u : Fin n → F, Matrix.mulVec e (Matrix.mulVec e u) = Matrix.mulVec e u :=
    fun u => fePSU_dualPair_GepsGLK_mulVec_e_fixes he ⟨u, by rw [Matrix.mulVecLin_apply]⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hmem : Matrix.mulVec N v ∈ LinearMap.range (Matrix.mulVecLin e) := by
    rw [← hN, ← Matrix.mulVec_mulVec]
    refine ⟨T ⟨Matrix.mulVec e v, ⟨v, by rw [Matrix.mulVecLin_apply]⟩⟩, ?_⟩
    rw [Matrix.mulVecLin_apply,
      fePSU_dualPair_GepsGLK_mulVec_e_fixes he
        (T ⟨Matrix.mulVec e v, ⟨v, by rw [Matrix.mulVecLin_apply]⟩⟩).2]
    exact (hNv ⟨Matrix.mulVec e v, ⟨v, by rw [Matrix.mulVecLin_apply]⟩⟩).symm
  obtain ⟨u, hu⟩ := hmem
  rw [← hu]
  exact hfix u

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_expand {F : Type} [Field F]
    {n : ℕ} (σ : F ≃+* F) (G e N : Matrix (Fin n) (Fin n) F) :
    formAdj σ.toRingHom G N * N +
        formAdj σ.toRingHom G N * (1 - (e + formAdj σ.toRingHom G e)) =
      formAdj σ.toRingHom G N * (N + (1 - (e + formAdj σ.toRingHom G e))) := by
  noncomm_ring

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_barN {F : Type} [Field F]
    {n : ℕ} (σ : F ≃+* F) (G e N : Matrix (Fin n) (Fin n) F)
    (hG : IsUnit G.det) (hNe : e * N = N) :
    formAdj σ.toRingHom G N = formAdj σ.toRingHom G N * formAdj σ.toRingHom G e := by
  conv_lhs => rw [← hNe]
  rw [Geo.formAdj_mul σ.toRingHom hG e N]

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_shift {F : Type} [Field F]
    {n : ℕ} (σ : F ≃+* F) (G e N : Matrix (Fin n) (Fin n) F) (hNe : e * N = N) :
    N + (1 - (e + formAdj σ.toRingHom G e)) =
      e * N + (1 - (e + formAdj σ.toRingHom G e)) := by
  rw [hNe]

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_star_zero
    {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F) (G e N : Matrix (Fin n) (Fin n) F)
    (hG : IsUnit G.det) (he : e * e = e) (h0e : formAdj σ.toRingHom G e * e = 0) :
    formAdj σ.toRingHom G e * (e * N + (1 - (e + formAdj σ.toRingHom G e))) = 0 := by
  have hstare : formAdj σ.toRingHom G e * formAdj σ.toRingHom G e = formAdj σ.toRingHom G e :=
    fePSU_dualPair_GepsGLK_extension_graph_product_left_star_idem σ G e hG he
  calc formAdj σ.toRingHom G e * (e * N + (1 - (e + formAdj σ.toRingHom G e)))
      = (formAdj σ.toRingHom G e * e) * N +
          (formAdj σ.toRingHom G e -
            (formAdj σ.toRingHom G e * e +
              formAdj σ.toRingHom G e * formAdj σ.toRingHom G e)) := by
        noncomm_ring
      _ = 0 + (formAdj σ.toRingHom G e - (0 + formAdj σ.toRingHom G e)) := by
        rw [h0e, hstare, zero_mul]
      _ = 0 := by simp

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel {F : Type} [Field F]
    {n : ℕ} (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hNe : e * N = N) (h0e : formAdj σ.toRingHom G e * e = 0)
    (hN : N * e = N) (hcomp : N' * N = e) :
    formAdj σ.toRingHom G N * N +
        formAdj σ.toRingHom G N * (1 - (e + formAdj σ.toRingHom G e)) = 0 := by
  have h1 := fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_expand σ G e N
  have h2 := fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_barN σ G e N hG hNe
  have h3 := fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_shift σ G e N hNe
  have he := fePSU_dualPair_GepsGLK_extension_graph_product_left_e_idem e N N' hN hcomp
  have h4 := fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel_star_zero σ G e N hG he
    h0e
  rw [h1, h3, h2, mul_assoc, h4, mul_zero]

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_left {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hNe : e * N = N) (h0e : formAdj σ.toRingHom G e * e = 0)
    (hN : N * e = N) (hcomp : N' * N = e) :
    formAdj σ.toRingHom G N * N +
        formAdj σ.toRingHom G N * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
        formAdj σ.toRingHom G N * (1 - (e + formAdj σ.toRingHom G e)) =
      formAdj σ.toRingHom G e := by
  have he := fePSU_dualPair_GepsGLK_extension_graph_product_left_e_idem e N N' hN hcomp
  have hstar := fePSU_dualPair_GepsGLK_extension_graph_product_left_star_idem σ G e hG he
  have hbarN := fePSU_dualPair_GepsGLK_extension_graph_product_left_barN σ G e N hG hN
  have hmid := fePSU_dualPair_GepsGLK_extension_graph_product_left_middle σ G e N N' hG hcomp
    hstar
  have hcancel :=
    fePSU_dualPair_GepsGLK_extension_graph_product_left_cancel σ G e N N' hG hNe h0e hN hcomp
  calc formAdj σ.toRingHom G N * N +
        formAdj σ.toRingHom G N * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
        formAdj σ.toRingHom G N * (1 - (e + formAdj σ.toRingHom G e))
      = (formAdj σ.toRingHom G N * N +
          formAdj σ.toRingHom G N * (1 - (e + formAdj σ.toRingHom G e))) +
          formAdj σ.toRingHom G N * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) := by
        noncomm_ring
    _ = 0 + formAdj σ.toRingHom G e := by rw [hcancel, hmid]
    _ = formAdj σ.toRingHom G e := by rw [zero_add]

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_middle {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hN'e : e * N' = N') (he0 : e * formAdj σ.toRingHom G e = 0) (hN' : N' * e = N') (hcomp : N' * N
        = e) :
    (e * N') * N + (e * N') * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
        (e * N') * (1 - (e + formAdj σ.toRingHom G e)) = e := by
  have hN'_left : formAdj σ.toRingHom G N' = formAdj σ.toRingHom G e * formAdj σ.toRingHom G N' :=
      by
    conv_lhs => rw [← hN']
    rw [Geo.formAdj_mul σ.toRingHom hG N' e]
  have hN'_one_sub : N' * (1 - e) = 0 := by rw [mul_sub, mul_one, hN', sub_self]
  have he_one_sub : formAdj σ.toRingHom G e = (1 - e) * formAdj σ.toRingHom G e := by
    rw [sub_mul, one_mul, he0, sub_zero]
  have hN'_e_star : N' * formAdj σ.toRingHom G e = 0 := by
    rw [he_one_sub, ← mul_assoc, hN'_one_sub, zero_mul]
  have hfirst : (e * N') * N = e := by rw [hN'e, hcomp]
  have hmiddle : (e * N') * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) = 0 := by
    rw [hN'e, hN'_left, ← mul_assoc, ← mul_assoc, hN'_e_star, zero_mul, zero_mul]
  have hright : (e * N') * (1 - (e + formAdj σ.toRingHom G e)) = 0 := by
    rw [hN'e, mul_sub, mul_one, mul_add, hN', hN'_e_star, add_zero, sub_self]
  calc (e * N') * N + (e * N') * (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
        (e * N') * (1 - (e + formAdj σ.toRingHom G e))
      = e + 0 + 0 := by rw [hfirst, hmiddle, hright]
      _ = e := by simp

private lemma fePSU_dualPair_GepsGLK_extension_graph_product_right {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hNe : e * N = N) (he0 : e * formAdj σ.toRingHom G e = 0)
    (h0e : formAdj σ.toRingHom G e * e = 0)
    (hN : N * e = N) (hN' : N' * e = N') (hcomp : N' * N = e) :
    (1 - (e + formAdj σ.toRingHom G e)) * N +
        (1 - (e + formAdj σ.toRingHom G e)) *
          (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
        (1 - (e + formAdj σ.toRingHom G e)) * (1 - (e + formAdj σ.toRingHom G e)) =
      1 - (e + formAdj σ.toRingHom G e) := by
  have he : e * e = e := fePSU_dualPair_GepsGLK_extension_graph_product_left_e_idem e N N' hN hcomp
  have hstare : formAdj σ.toRingHom G e * formAdj σ.toRingHom G e = formAdj σ.toRingHom G e :=
    fePSU_dualPair_GepsGLK_extension_graph_product_left_star_idem σ G e hG he
  have hε : (e + formAdj σ.toRingHom G e) * (e + formAdj σ.toRingHom G e) =
      e + formAdj σ.toRingHom G e := by
    rw [add_mul, mul_add, mul_add, he, he0, h0e, hstare]
    simp
  have hεe : (1 - (e + formAdj σ.toRingHom G e)) * e = 0 := by
    rw [sub_mul, one_mul, add_mul, he, h0e, add_zero, sub_self]
  have hεe_star : (1 - (e + formAdj σ.toRingHom G e)) * formAdj σ.toRingHom G e = 0 := by
    rw [sub_mul, one_mul, add_mul, he0, hstare, zero_add, sub_self]
  have h1 : (1 - (e + formAdj σ.toRingHom G e)) * N = 0 := by
    rw [← hNe, ← mul_assoc, hεe, zero_mul]
  have h2 : (1 - (e + formAdj σ.toRingHom G e)) *
      (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) = 0 := by
    rw [fePSU_dualPair_GepsGLK_extension_graph_product_left_barN σ G e N' hG hN',
      ← mul_assoc, ← mul_assoc, hεe_star, zero_mul, zero_mul]
  have h1ε : (1 - (e + formAdj σ.toRingHom G e)) * (1 - (e + formAdj σ.toRingHom G e)) =
      1 - (e + formAdj σ.toRingHom G e) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]
  calc (1 - (e + formAdj σ.toRingHom G e)) * N +
        (1 - (e + formAdj σ.toRingHom G e)) *
          (formAdj σ.toRingHom G N' * formAdj σ.toRingHom G e) +
        (1 - (e + formAdj σ.toRingHom G e)) * (1 - (e + formAdj σ.toRingHom G e))
      = 0 + 0 + (1 - (e + formAdj σ.toRingHom G e)) := by rw [h1, h2, h1ε]
      _ = 1 - (e + formAdj σ.toRingHom G e) := by simp

private lemma fePSU_dualPair_GepsGLK_extension_graph_product {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hNe : e * N = N) (hN'e : e * N' = N')
    (he0 : e * formAdj σ.toRingHom G e = 0) (h0e : formAdj σ.toRingHom G e * e = 0)
    (hN : N * e = N) (hN' : N' * e = N') (hcomp : N' * N = e) :
    (formAdj σ.toRingHom G N + e * N' + (1 - (e + formAdj σ.toRingHom G e))) *
        fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N' = 1 := by
  have h1 := fePSU_dualPair_GepsGLK_extension_graph_product_expand σ G e N N'
  have h2 := fePSU_dualPair_GepsGLK_extension_graph_product_left σ G e N N' hG hNe h0e hN hcomp
  have h3 := fePSU_dualPair_GepsGLK_extension_graph_product_middle σ G e N N' hG hN'e he0 hN'
      hcomp
  have h4 := fePSU_dualPair_GepsGLK_extension_graph_product_right σ G e N N' hG hNe he0 h0e hN hN'
      hcomp
  rw [h1, h2, h3, h4]
  noncomm_ring

private lemma fePSU_dualPair_GepsGLK_extension_graph_conjTr {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (h : formAdj σ.toRingHom G (fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N') *
        fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N' = 1) :
    Unitary.conjTr σ (fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N') * G *
      fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N' = G := by
  have h1 : G * (formAdj σ.toRingHom G
      (fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N') *
      fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N') = G := by rw [h, mul_one]
  unfold formAdj at h1
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv G hG, Matrix.one_mul] at h1
  simpa [Unitary.conjTr] using h1

private lemma fePSU_dualPair_GepsGLK_extension_graph_unitary {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (G e N N' : Matrix (Fin n) (Fin n) F)
    (hσ : ∀ x, σ (σ x) = x) (hG : IsUnit G.det) (hGh : Matrix.transpose (G.map σ.toRingHom) = G)
    (hNe : e * N = N) (hN'e : e * N' = N')
    (he0 : e * formAdj σ.toRingHom G e = 0) (h0e : formAdj σ.toRingHom G e * e = 0)
    (hN : N * e = N) (hN' : N' * e = N') (hcomp : N' * N = e) :
    Unitary.conjTr σ (fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N') * G *
      fePSU_dualPair_GepsGLK_extensionGraph σ.toRingHom G e N N' = G := by
  have h1 := fePSU_dualPair_GepsGLK_extension_graph_adjoint σ G e N N' hσ hG hGh
  have h2 := fePSU_dualPair_GepsGLK_extension_graph_product σ G e N N' hG hNe hN'e he0 h0e hN hN'
      hcomp
  exact fePSU_dualPair_GepsGLK_extension_graph_conjTr σ G e N N' hG
    (by rw [h1]; exact h2)

private lemma fePSU_dualPair_GepsGLK_natural_pairing {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e) :
    e * formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
        (Unitary.antidiag n) e = 0 ∧
      formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
        (Unitary.antidiag n) e * e = 0 := by
  classical
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let A : Subalgebra F (Matrix (Fin n) (Fin n) F) := Algebra.adjoin F (Units.val '' S)
  change IsPrimAdjIdemIn σ G A ε at hε
  change IsPrimIdemIn A e at he
  change e * formAdj σ G e = 0 ∧ formAdj σ G e * e = 0
  have hσ : ∀ x, σ (σ x) = x :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    simpa [G] using Unitary.det_antidiag_ne_zero (F := F) n
  have hGh : Matrix.transpose (G.map σ) = G := by
    show Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n
    rw [fePSU_antidiag_map σ n, fePSU_transpose_antidiag n]
  have hSU' : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (Fin n) (Fin n) F).map σ) * G * (s : Matrix (Fin n) (Fin n) F) = G := by
    intro s hs
    simpa [Unitary.conjTr, G, σ] using hSU s hs
  exact Geo.mul_formAdj_eq_zero_of_dualPair σ hσ hG hGh hSU' hS he hpair

private def fePSU_dualPair_unitBlockCentralizer {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (S : Set (GL (Fin n) F)) (ε : Matrix (Fin n) (Fin n) F) :
    Subgroup (GL (Fin n) F) where
  carrier := {g | Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
        (g : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (g : Matrix (Fin n) (Fin n) F) =
        Unitary.antidiag n ∧
      (∀ s ∈ S, g * s = s * g) ∧ (g : Matrix (Fin n) (Fin n) F) * (1 - ε) = 1 - ε}
  mul_mem' {A B} hA hB := by
    obtain ⟨hAG, hAc, hAε⟩ := hA
    obtain ⟨hBG, hBc, hBε⟩ := hB
    refine ⟨?_, ?_, ?_⟩
    · have e : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
            (((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
          Unitary.antidiag n *
            (((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
          Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
              (B : Matrix (Fin n) (Fin n) F) *
            (Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
                (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
              (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
        rw [Units.val_mul, Unitary.conjTr_mul]
        simp only [Matrix.mul_assoc]
      rw [e, hAG, hBG]
    · intro s hs
      rw [mul_assoc, hBc s hs, ← mul_assoc, hAc s hs, mul_assoc]
    · rw [Units.val_mul, mul_assoc, hBε, hAε]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Unitary.conjTr_one]
    · intro s hs; rw [one_mul, mul_one]
    · rw [Units.val_one, one_mul]
  inv_mem' {A} hA := by
    obtain ⟨hAG, hAc, hAε⟩ := hA
    have hBA : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (A : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨?_, ?_, ?_⟩
    · have key : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
              (A : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
            (A : Matrix (Fin n) (Fin n) F)) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
              ((A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
            Unitary.antidiag n *
            ((A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
                by
        rw [Unitary.conjTr_mul]
        simp only [Matrix.mul_assoc]
      rw [hAG] at key
      rw [show (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
        Unitary.conjTr_one, Matrix.one_mul, Matrix.mul_one] at key
      exact key
    · intro s hs
      have h := hAc s hs
      calc (A⁻¹ : GL (Fin n) F) * s = A⁻¹ * (s * A) * A⁻¹ := by simp [mul_assoc]
        _ = A⁻¹ * (A * s) * A⁻¹ := by rw [← h]
        _ = s * A⁻¹ := by simp [mul_assoc]
    · have h := congrArg (fun x : Matrix (Fin n) (Fin n) F =>
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * x) hAε
      rw [← Matrix.mul_assoc, hBA, Matrix.one_mul] at h
      exact h.symm

private lemma fePSU_unitBlockCentralizer_commute_adjoin {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε))
    {a : Matrix (Fin n) (Fin n) F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * a =
      a * ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  have hcent : (u : GL (Fin n) F) ∈ Subgroup.centralizer S :=
    Subgroup.mem_centralizer_iff.mpr (fun s hs => (u.2.2.1 s hs).symm)
  let M : Matrix (Fin n) (Fin n) F := ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  let C : Subalgebra F (Matrix (Fin n) (Fin n) F) :=
    { carrier := {a | Commute M a},
      mul_mem' := fun ha hb => ha.mul_right hb,
      one_mem' := Commute.one_right M,
      add_mem' := fun ha hb => ha.add_right hb,
      zero_mem' := Commute.zero_right M,
      algebraMap_mem' := fun r => (Algebra.commute_algebraMap_left r M).symm }
  have hle : Algebra.adjoin F (Units.val '' S) ≤ C := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨s, hs, rfl⟩
    change M * (((s : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) =
      (((s : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) * M
    have h : (u : GL (Fin n) F) * s = s * (u : GL (Fin n) F) :=
      (Subgroup.mem_centralizer_iff.mp hcent s hs).symm
    simpa [M, Units.val_mul] using
      congrArg (fun v : GL (Fin n) F => (v : Matrix (Fin n) (Fin n) F)) h
  exact (hle ha).eq

private lemma fePSU_unitBlockCentralizer_stable {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F))
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) :
    ∀ w ∈ LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVecLin ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w ∈
        LinearMap.range (Matrix.mulVecLin e) := by
  let M : Matrix (Fin n) (Fin n) F := ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  intro w hw
  obtain ⟨v, hv⟩ := hw
  refine ⟨Matrix.mulVec M v, ?_⟩
  rw [← hv]
  calc Matrix.mulVecLin e (Matrix.mulVec M v)
      = Matrix.mulVec e (Matrix.mulVec M v) := rfl
    _ = Matrix.mulVec (e * M) v := Matrix.mulVec_mulVec v e M
    _ = Matrix.mulVec (M * e) v := by
          rw [fePSU_unitBlockCentralizer_commute_adjoin S u he.1]
    _ = Matrix.mulVec M (Matrix.mulVec e v) := (Matrix.mulVec_mulVec v M e).symm
    _ = Matrix.mulVecLin M (Matrix.mulVecLin e v) := rfl

private lemma fePSU_dualPair_unitBlockCentralizer_KAction_body {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} {n : ℕ}
    (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (K : Type) [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0) :
    ∃ (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)))
      (actK : fePSU_dualPair_unitBlockCentralizer (f := f) S ε →*
        Module.End K (LinearMap.range (Matrix.mulVecLin e))),
      (∀ (u : fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
        (w : LinearMap.range (Matrix.mulVecLin e)),
        (actK u w : Fin n → F) =
          Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w) ∧
      (∀ (a : Algebra.adjoin F (Units.val '' S))
        (w : LinearMap.range (Matrix.mulVecLin e)),
        ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) =
          Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) w) := by

  classical
  obtain ⟨actA, hact⟩ := fePSU_blockAction S hS he
  have hker : RingHom.ker (π : Algebra.adjoin (F) (Units.val '' S) →+* K) ≤
      RingHom.ker (actA : Algebra.adjoin (F) (Units.val '' S) →+*
        Module.End (F) (LinearMap.range (Matrix.mulVecLin e))) :=
    fePSU_blockAction_ker S K π hπker actA hact
  have hp : Function.Surjective (π : Algebra.adjoin (F) (Units.val '' S) →+* K) :=
    fun k => hπsurj k
  let ψ : K →+* Module.End (F) (LinearMap.range (Matrix.mulVecLin e)) :=
    (Ideal.Quotient.lift
      (RingHom.ker (π : Algebra.adjoin (F) (Units.val '' S) →+* K))
      (actA : Algebra.adjoin (F) (Units.val '' S) →+*
        Module.End (F) (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha))).comp
      (RingHom.quotientKerEquivOfSurjective
        (f := (π : Algebra.adjoin (F) (Units.val '' S) →+* K)) hp).symm.toRingHom
  have hψ : ∀ a : Algebra.adjoin (F) (Units.val '' S), ψ (π a) = actA a :=
    fun a => by
    change (Ideal.Quotient.lift
      (RingHom.ker (π : Algebra.adjoin (F) (Units.val '' S) →+* K))
      (actA : Algebra.adjoin (F) (Units.val '' S) →+*
        Module.End (F) (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha)))
      ((RingHom.quotientKerEquivOfSurjective
        (f := (π : Algebra.adjoin (F) (Units.val '' S) →+* K)) hp).symm
        ((π : Algebra.adjoin (F) (Units.val '' S) →+* K) a)) = actA a
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.compHom (LinearMap.range (Matrix.mulVecLin e)) ψ
  have htower : IsScalarTower (F) K (LinearMap.range (Matrix.mulVecLin e)) :=
    ⟨fun c k w => by
    change (ψ (c • k)) w = c • ((ψ k) w)
    obtain ⟨a, rfl⟩ := hπsurj k
    rw [← map_smul π c a, hψ (c • a), hψ a, map_smul]
    rfl⟩
  let rhoF (u : fePSU_dualPair_unitBlockCentralizer (f := f) S ε) :
      LinearMap.range (Matrix.mulVecLin e) →ₗ[F]
        LinearMap.range (Matrix.mulVecLin e) :=
    ((Matrix.mulVecLin ((u : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) (F))).comp
      (LinearMap.range (Matrix.mulVecLin e)).subtype).codRestrict
        (LinearMap.range (Matrix.mulVecLin e)) (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          exact fePSU_unitBlockCentralizer_stable S he u v v.2)
  have hrhoF_apply (u : fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
      (v : LinearMap.range (Matrix.mulVecLin e)) :
      (rhoF u v : Fin n → F) =
        Matrix.mulVec ((u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) (F)) v := rfl
  have hrhoF_smul (u : fePSU_dualPair_unitBlockCentralizer (f := f) S ε) (k : K)
      (v : LinearMap.range (Matrix.mulVecLin e)) : rhoF u (k • v) = k • rhoF u v := by
    obtain ⟨a, ha⟩ := hπsurj k
    have hψk : ψ k = actA a := by rw [← ha, hψ a]
    apply Subtype.ext
    change (rhoF u (ψ k v) : Fin n → F) =
      (ψ k (rhoF u v) : Fin n → F)
    rw [hψk]
    have h1 : (rhoF u (actA a v) : Fin n → F) =
        Matrix.mulVec ((u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) (F))
          (Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
            (v : Fin n → F)) := by
      rw [hrhoF_apply, hact a v]
    have h2 : (actA a (rhoF u v) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
          (Matrix.mulVec ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F))
            (v : Fin n → F)) := by
      rw [hact a (rhoF u v), hrhoF_apply]
    rw [h1, h2]
    calc Matrix.mulVec ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F))
            (Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
              (v : Fin n → F))
        = Matrix.mulVec (((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) *
            (a : Matrix (Fin n) (Fin n) (F)))
            (v : Fin n → F) :=
          Matrix.mulVec_mulVec (v : Fin n → F)
            ((u : GL (Fin n) F) :
              Matrix (Fin n) (Fin n) (F))
            (a : Matrix (Fin n) (Fin n) (F))
      _ = Matrix.mulVec ((a : Matrix (Fin n) (Fin n) (F)) *
            ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)))
            (v : Fin n → F) := by
          rw [fePSU_unitBlockCentralizer_commute_adjoin S u a.2]
      _ = Matrix.mulVec (a : Matrix (Fin n) (Fin n) (F))
            (Matrix.mulVec ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F))
            (v : Fin n → F)) :=
          (Matrix.mulVec_mulVec (v : Fin n → F)
            (a : Matrix (Fin n) (Fin n) (F))
            ((u : GL (Fin n) F) :
              Matrix (Fin n) (Fin n) (F))).symm
  let rhoK (u : fePSU_dualPair_unitBlockCentralizer (f := f) S ε) :
      LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e) :=
    { toFun := fun v => rhoF u v
      map_add' := fun v v' => (rhoF u).map_add v v'
      map_smul' := fun k v => hrhoF_smul u k v }
  refine ⟨inferInstance, htower, ?_, ?_⟩
  · refine
      { toFun := rhoK
        map_one' := ?_
        map_mul' := ?_ }
    · refine LinearMap.ext fun v => Subtype.ext ?_
      change (rhoF 1 v : Fin n → F) =
        (v : Fin n → F)
      rw [hrhoF_apply]
      change Matrix.mulVec (1 : Matrix (Fin n) (Fin n) (F)) v =
        (v : Fin n → F)
      rw [Matrix.one_mulVec]
    · intro u u'
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (rhoF (u * u') v : Fin n → F) =
        (rhoF u (rhoF u' v) : Fin n → F)
      rw [hrhoF_apply, hrhoF_apply, hrhoF_apply]
      have hcoe : (((u * u' : fePSU_dualPair_unitBlockCentralizer (f := f) S ε) :
            GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) =
          ((u : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) *
          ((u' : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) (F)) := rfl
      rw [hcoe, Matrix.mulVec_mulVec]
  · exact ⟨fun u w => hrhoF_apply u w, by
      intro a w
      change (ψ (π a) w : Fin n → F) = Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) w
      rw [hψ a]
      exact hact a w⟩


private lemma fePSU_dualPair_extension_rep_mul_commute {F : Type} [Field F] {n : ℕ}
    {K : Type} [Field K] [Algebra F K] {e N : Matrix (Fin n) (Fin n) F}
    {A : Subalgebra F (Matrix (Fin n) (Fin n) F)}
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (π : A →ₐ[F] K)
    (hcomp : ∀ (a : A) (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) (w : Fin n → F))
    {s : Matrix (Fin n) (Fin n) F} (hsA : s ∈ A)
    (T : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (hN : N * e = N)
    (hNv : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVec N (w : Fin n → F) = (T w : Fin n → F))
    (hse : s * e = e * s) :
    N * s = s * N := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  show Matrix.mulVec (N * s) x = Matrix.mulVec (s * N) x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  let w : LinearMap.range (Matrix.mulVecLin e) := ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩
  have hxN : Matrix.mulVec N x = Matrix.mulVec N (w : Fin n → F) := by
    rw [show (w : Fin n → F) = Matrix.mulVec e x from rfl, Matrix.mulVec_mulVec, hN]
  calc Matrix.mulVec N (Matrix.mulVec s x)
      = Matrix.mulVec N (Matrix.mulVec e (Matrix.mulVec s x)) := by
          conv_rhs => rw [Matrix.mulVec_mulVec, hN]
    _ = Matrix.mulVec N (Matrix.mulVec s (Matrix.mulVec e x)) := by
          congr 1
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hse]
    _ = Matrix.mulVec N
          ((π ⟨s, hsA⟩ • w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) := by
          congr 1
          exact (hcomp ⟨s, hsA⟩ w).symm
    _ = (T (π ⟨s, hsA⟩ • w) : Fin n → F) := hNv (π ⟨s, hsA⟩ • w)
    _ = ((π ⟨s, hsA⟩ • T w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) :=
          congrArg Subtype.val (map_smul T (π ⟨s, hsA⟩) w)
    _ = Matrix.mulVec s ((T w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) :=
          hcomp ⟨s, hsA⟩ (T w)
    _ = Matrix.mulVec s (Matrix.mulVec N (w : Fin n → F)) := by rw [hNv w]
    _ = Matrix.mulVec s (Matrix.mulVec N x) := by rw [hxN]

private lemma fePSU_dualPair_unitBlockCentralizer_extensionGraph_commute {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2)
    (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    {K : Type} [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hcomp : ∀ (a : Algebra.adjoin F (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) (w : Fin n → F))
    (T : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    {N N' : Matrix (Fin n) (Fin n) F} (hN : N * e = N)
    (hNv : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVec N (w : Fin n → F) = (T w : Fin n → F))
    (hN' : N' * e = N') (hN'v : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVec N' (w : Fin n → F) = (T.symm w : Fin n → F)) :
    ∀ s ∈ S,
      fePSU_dualPair_GepsGLK_extensionGraph
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) e N N' *
        (s : Matrix (Fin n) (Fin n) F) =
      (s : Matrix (Fin n) (Fin n) F) *
        fePSU_dualPair_GepsGLK_extensionGraph
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) e N N' :=
              by
  intro s hs
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hee : e * e = e := he.2.1.eq
  have hεε : ε * ε = ε := hε.2.1.eq
  obtain ⟨he0, h0e⟩ := fePSU_dualPair_GepsGLK_natural_pairing hc S hS hSU hε he hpair
  have hstar_idem : formAdj σ G e * formAdj σ G e = formAdj σ G e := by
    have h := Geo.formAdj_mul σ hG e e
    rw [hee] at h
    exact h.symm
  have hpairA : (Units.val '' S : Set (Matrix (Fin n) (Fin n) F)).Pairwise Commute := by
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ _
    exact (hS s₁ hs₁ s₂ hs₂).map (Units.coeHom (Matrix (Fin n) (Fin n) F))
  letI : CommRing (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpairA
  have hsA : (s : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hse : (s : Matrix (Fin n) (Fin n) F) * e = e * (s : Matrix (Fin n) (Fin n) F) :=
    congrArg Subtype.val (mul_comm (⟨(s : Matrix (Fin n) (Fin n) F), hsA⟩ :
      Algebra.adjoin F (Units.val '' S)) (⟨e, he.1⟩ : Algebra.adjoin F (Units.val '' S)))
  have hseps : (s : Matrix (Fin n) (Fin n) F) * ε = ε * (s : Matrix (Fin n) (Fin n) F) :=
    congrArg Subtype.val (mul_comm (⟨(s : Matrix (Fin n) (Fin n) F), hsA⟩ :
      Algebra.adjoin F (Units.val '' S)) (⟨ε, hε.1⟩ : Algebra.adjoin F (Units.val '' S)))
  have hse_star : (s : Matrix (Fin n) (Fin n) F) * formAdj σ G e =
      formAdj σ G e * (s : Matrix (Fin n) (Fin n) F) := by
    have h : formAdj σ G e = ε - e := by rw [hεeq]; abel
    rw [h, Matrix.mul_sub, Matrix.sub_mul, hseps, hse]
  have hsinv : (s : Matrix (Fin n) (Fin n) F) *
      ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsinv' : ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (s : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hformAdj_s : formAdj σ G (s : Matrix (Fin n) (Fin n) F) =
      ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    have hiso : Matrix.transpose ((s : Matrix (Fin n) (Fin n) F).map σ) * G *
        (s : Matrix (Fin n) (Fin n) F) = G := by
      simpa [Unitary.conjTr, σ, G] using hSU s hs
    have h1 : Matrix.transpose ((s : Matrix (Fin n) (Fin n) F).map σ) * G =
        G * ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      have h := congrArg (fun M => M * ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hiso
      simpa only [Matrix.mul_assoc, hsinv, Matrix.mul_one] using h
    show G⁻¹ * Matrix.transpose ((s : Matrix (Fin n) (Fin n) F).map σ) * G =
      ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
  have hNs : N * (s : Matrix (Fin n) (Fin n) F) = (s : Matrix (Fin n) (Fin n) F) * N :=
    fePSU_dualPair_extension_rep_mul_commute (A := Algebra.adjoin F (Units.val '' S))
      π hcomp hsA T hN hNv hse
  have hN's : N' * (s : Matrix (Fin n) (Fin n) F) = (s : Matrix (Fin n) (Fin n) F) * N' :=
    fePSU_dualPair_extension_rep_mul_commute (A := Algebra.adjoin F (Units.val '' S))
      π hcomp hsA T.symm hN' hN'v hse
  have hstar_comm : formAdj σ G N' * (s : Matrix (Fin n) (Fin n) F) =
      (s : Matrix (Fin n) (Fin n) F) * formAdj σ G N' := by
    have h := congrArg (formAdj σ G) hN's
    rw [Geo.formAdj_mul σ hG, Geo.formAdj_mul σ hG, hformAdj_s] at h
    calc formAdj σ G N' * (s : Matrix (Fin n) (Fin n) F)
        = ((s : Matrix (Fin n) (Fin n) F) * ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
            formAdj σ G N' * (s : Matrix (Fin n) (Fin n) F) := by
          rw [hsinv, Matrix.one_mul]
      _ = (s : Matrix (Fin n) (Fin n) F) *
            (((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * formAdj σ G N') *
            (s : Matrix (Fin n) (Fin n) F) := by noncomm_ring
      _ = (s : Matrix (Fin n) (Fin n) F) *
            (formAdj σ G N' * ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
            (s : Matrix (Fin n) (Fin n) F) := by rw [h]
      _ = (s : Matrix (Fin n) (Fin n) F) * formAdj σ G N' *
            (((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (s : Matrix (Fin n) (Fin n) F)) := by noncomm_ring
      _ = (s : Matrix (Fin n) (Fin n) F) * formAdj σ G N' := by
          rw [hsinv', Matrix.mul_one]
  let M : Matrix (Fin n) (Fin n) F := fePSU_dualPair_GepsGLK_extensionGraph σ G e N N'
  have hMe : M * e = N := by
    show fePSU_dualPair_GepsGLK_extensionGraph σ G e N N' * e = N
    have hεe : ε * e = e := by rw [hεeq, Matrix.add_mul, hee, h0e, add_zero]
    unfold fePSU_dualPair_GepsGLK_extensionGraph
    rw [← hεeq]
    rw [Matrix.add_mul, Matrix.add_mul, hN, Matrix.mul_assoc, h0e, Matrix.mul_zero,
      Matrix.sub_mul, Matrix.one_mul, hεe, sub_self, add_zero, add_zero]
  have hM1 : M * (1 - ε) = 1 - ε := by
    show fePSU_dualPair_GepsGLK_extensionGraph σ G e N N' * (1 - ε) = 1 - ε
    have he1 : e * (1 - ε) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, heε, sub_self]
    have hstar1 : formAdj σ G e * (1 - ε) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      have h : formAdj σ G e * ε = formAdj σ G e := by
        rw [hεeq, Matrix.mul_add, h0e, hstar_idem, zero_add]
      rw [h, sub_self]
    have hone : (1 - ε) * (1 - ε) = 1 - ε := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hεε, sub_self,
        sub_zero]
    unfold fePSU_dualPair_GepsGLK_extensionGraph
    rw [← hεeq]
    rw [Matrix.add_mul, Matrix.add_mul, ← hN, Matrix.mul_assoc, he1, Matrix.mul_zero,
      Matrix.mul_assoc, hstar1, Matrix.mul_zero, hone, zero_add, zero_add]
  have hMestar : M * formAdj σ G e = formAdj σ G N' * formAdj σ G e := by
    show fePSU_dualPair_GepsGLK_extensionGraph σ G e N N' * formAdj σ G e =
      formAdj σ G N' * formAdj σ G e
    have hNe : N * formAdj σ G e = 0 := by
      rw [← hN, Matrix.mul_assoc, he0, Matrix.mul_zero]
    have hone : (1 - ε) * formAdj σ G e = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      have h : ε * formAdj σ G e = formAdj σ G e := by
        rw [hεeq, Matrix.add_mul, he0, hstar_idem, zero_add]
      rw [h, sub_self]
    unfold fePSU_dualPair_GepsGLK_extensionGraph
    rw [← hεeq]
    rw [Matrix.add_mul, Matrix.add_mul, hNe, Matrix.mul_assoc, hstar_idem, hone, zero_add,
      add_zero]
  have hse1 : (s : Matrix (Fin n) (Fin n) F) * (1 - ε) =
      (1 - ε) * (s : Matrix (Fin n) (Fin n) F) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hseps]
  have h1 : M * (s : Matrix (Fin n) (Fin n) F) * e =
      (s : Matrix (Fin n) (Fin n) F) * M * e := by
    calc M * (s : Matrix (Fin n) (Fin n) F) * e
        = M * (s * e) := by rw [Matrix.mul_assoc]
      _ = M * (e * s) := by rw [hse]
      _ = M * e * (s : Matrix (Fin n) (Fin n) F) := by rw [Matrix.mul_assoc]
      _ = N * (s : Matrix (Fin n) (Fin n) F) := by rw [hMe]
      _ = (s : Matrix (Fin n) (Fin n) F) * N := hNs
      _ = (s : Matrix (Fin n) (Fin n) F) * (M * e) := by rw [hMe]
      _ = (s : Matrix (Fin n) (Fin n) F) * M * e := by rw [Matrix.mul_assoc]
  have h2 : M * (s : Matrix (Fin n) (Fin n) F) * (1 - ε) =
      (s : Matrix (Fin n) (Fin n) F) * M * (1 - ε) := by
    calc M * (s : Matrix (Fin n) (Fin n) F) * (1 - ε)
        = M * (s * (1 - ε)) := by rw [Matrix.mul_assoc]
      _ = M * ((1 - ε) * s) := by rw [hse1]
      _ = M * (1 - ε) * (s : Matrix (Fin n) (Fin n) F) := by rw [Matrix.mul_assoc]
      _ = (1 - ε) * (s : Matrix (Fin n) (Fin n) F) := by rw [hM1]
      _ = (s : Matrix (Fin n) (Fin n) F) * (1 - ε) := hse1.symm
      _ = (s : Matrix (Fin n) (Fin n) F) * (M * (1 - ε)) := by rw [hM1]
      _ = (s : Matrix (Fin n) (Fin n) F) * M * (1 - ε) := by rw [Matrix.mul_assoc]
  have h3 : M * (s : Matrix (Fin n) (Fin n) F) * formAdj σ G e =
      (s : Matrix (Fin n) (Fin n) F) * M * formAdj σ G e := by
    calc M * (s : Matrix (Fin n) (Fin n) F) * formAdj σ G e
        = M * (s * formAdj σ G e) := by rw [Matrix.mul_assoc]
      _ = M * (formAdj σ G e * s) := by rw [hse_star]
      _ = M * formAdj σ G e * (s : Matrix (Fin n) (Fin n) F) := by rw [Matrix.mul_assoc]
      _ = (formAdj σ G N' * formAdj σ G e) * (s : Matrix (Fin n) (Fin n) F) := by rw [hMestar]
      _ = formAdj σ G N' * (formAdj σ G e * (s : Matrix (Fin n) (Fin n) F)) := by
          rw [Matrix.mul_assoc]
      _ = formAdj σ G N' * ((s : Matrix (Fin n) (Fin n) F) * formAdj σ G e) := by rw [hse_star]
      _ = (formAdj σ G N' * (s : Matrix (Fin n) (Fin n) F)) * formAdj σ G e := by
          rw [Matrix.mul_assoc]
      _ = ((s : Matrix (Fin n) (Fin n) F) * formAdj σ G N') * formAdj σ G e := by rw [hstar_comm]
      _ = (s : Matrix (Fin n) (Fin n) F) * (formAdj σ G N' * formAdj σ G e) := by
          rw [Matrix.mul_assoc]
      _ = (s : Matrix (Fin n) (Fin n) F) * (M * formAdj σ G e) := by rw [hMestar]
      _ = (s : Matrix (Fin n) (Fin n) F) * M * formAdj σ G e := by rw [Matrix.mul_assoc]
  have hone : (1 : Matrix (Fin n) (Fin n) F) = e + (1 - ε) + formAdj σ G e := by
    rw [hεeq]; abel
  calc M * (s : Matrix (Fin n) (Fin n) F)
      = M * (s : Matrix (Fin n) (Fin n) F) * 1 := (Matrix.mul_one _).symm
    _ = M * (s : Matrix (Fin n) (Fin n) F) * (e + (1 - ε) + formAdj σ G e) := by
          conv_lhs => rw [hone]
    _ = M * (s : Matrix (Fin n) (Fin n) F) * e +
          M * (s : Matrix (Fin n) (Fin n) F) * (1 - ε) +
          M * (s : Matrix (Fin n) (Fin n) F) * formAdj σ G e := by noncomm_ring
    _ = (s : Matrix (Fin n) (Fin n) F) * M * e +
          (s : Matrix (Fin n) (Fin n) F) * M * (1 - ε) +
          (s : Matrix (Fin n) (Fin n) F) * M * formAdj σ G e := by rw [h1, h2, h3]
    _ = (s : Matrix (Fin n) (Fin n) F) * M * (e + (1 - ε) + formAdj σ G e) := by noncomm_ring
    _ = (s : Matrix (Fin n) (Fin n) F) * M * 1 := by conv_rhs => rw [hone]
    _ = (s : Matrix (Fin n) (Fin n) F) * M := Matrix.mul_one _

private lemma fePSU_dualPair_unitBlockCentralizer_extension_realizes {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2)
    (S : Set (GL (Fin n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (K : Type) [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))]
    (actK : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin n → F) =
        Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w)
    (hcomp : ∀ (a : Algebra.adjoin F (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) (w : Fin n → F)) :
    ∀ T : (Module.End K (LinearMap.range (Matrix.mulVecLin e)))ˣ,
      ∃ u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε), actK.toHomUnits u = T := by
  intro T
  let W := LinearMap.range (Matrix.mulVecLin e)
  have hleftT : ((T⁻¹ : (Module.End K W)ˣ) : Module.End K W) * (T : Module.End K W) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrightT : (T : Module.End K W) * ((T⁻¹ : (Module.End K W)ˣ) : Module.End K W) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let Tl : W ≃ₗ[K] W := LinearEquiv.ofBijective (T : W →ₗ[K] W) ⟨
    fun x y hxy => by
      have hx := congrArg (fun f : Module.End K W => f x) hleftT
      have hy := congrArg (fun f : Module.End K W => f y) hleftT
      change ((T⁻¹ : (Module.End K W)ˣ) : Module.End K W) ((T : Module.End K W) x) = x at hx
      change ((T⁻¹ : (Module.End K W)ˣ) : Module.End K W) ((T : Module.End K W) y) = y at hy
      rw [← hx, hxy, hy]
    , fun y => ⟨((T⁻¹ : (Module.End K W)ˣ) : Module.End K W) y, by
        have hy := congrArg (fun f : Module.End K W => f y) hrightT
        change (T : Module.End K W) (((T⁻¹ : (Module.End K W)ˣ) : Module.End K W) y) = y at hy
        exact hy⟩⟩
  let σe : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 f
  let σ : F →+* F := σe.toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  obtain ⟨N, hN, hNv⟩ := fePSU_dualPair_GepsGLK_extension_left S he Tl
  have hNe : e * N = N :=
    fePSU_dualPair_GepsGLK_extension_graph_e_mul_N Tl he.2.1.eq hN hNv
  obtain ⟨N', hN', hN'v, hcomp'⟩ := fePSU_dualPair_GepsGLK_extension_right S he Tl hN hNv
  have hN'e : e * N' = N' :=
    fePSU_dualPair_GepsGLK_extension_graph_e_mul_N Tl.symm he.2.1.eq hN' hN'v
  have hσ : ∀ x, σe (σe x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hGh : Matrix.transpose (G.map σ) = G := by
    show Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n
    rw [fePSU_antidiag_map σ n, fePSU_transpose_antidiag n]
  obtain ⟨he0, h0e⟩ := fePSU_dualPair_GepsGLK_natural_pairing hc S hS hSU hε he hpair
  let M : Matrix (Fin n) (Fin n) F := fePSU_dualPair_GepsGLK_extensionGraph σ G e N N'
  have huni : Unitary.conjTr σe M * G * M = G :=
    fePSU_dualPair_GepsGLK_extension_graph_unitary σe G e N N' hσ hG hGh hNe hN'e he0 h0e
      hN hN' hcomp'
  have hcomm := fePSU_dualPair_unitBlockCentralizer_extensionGraph_commute hc S hS hSU hε he
    heε hpair hεeq π hcomp Tl hN hNv hN' hN'v
  have hM1 : M * (1 - ε) = 1 - ε := by
    show fePSU_dualPair_GepsGLK_extensionGraph σ G e N N' * (1 - ε) = 1 - ε
    have he1 : e * (1 - ε) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, heε, sub_self]
    have hstar_idem : formAdj σ G e * formAdj σ G e = formAdj σ G e := by
      have h := Geo.formAdj_mul σ hG e e
      rw [he.2.1.eq] at h
      exact h.symm
    have hstar1 : formAdj σ G e * (1 - ε) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      have h : formAdj σ G e * ε = formAdj σ G e := by
        rw [hεeq, Matrix.mul_add, h0e, hstar_idem, zero_add]
      rw [h, sub_self]
    have hone : (1 - ε) * (1 - ε) = 1 - ε := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hε.2.1.eq, sub_self,
        sub_zero]
    unfold fePSU_dualPair_GepsGLK_extensionGraph
    rw [← hεeq]
    rw [Matrix.add_mul, Matrix.add_mul, ← hN, Matrix.mul_assoc, he1, Matrix.mul_zero,
      Matrix.mul_assoc, hstar1, Matrix.mul_zero, hone, zero_add, zero_add]
  have hleft : (G⁻¹ * Unitary.conjTr σe M * G) * M = 1 := by
    have h1 : G⁻¹ * (Unitary.conjTr σe M * G * M) = 1 := by
      rw [huni, Matrix.nonsing_inv_mul G hG]
    simpa only [Matrix.mul_assoc] using h1
  have hdet : M.det ≠ 0 := by
    intro h0
    have hdetmul : (G⁻¹ * Unitary.conjTr σe M * G).det * M.det = 1 := by
      rw [← Matrix.det_mul, hleft, Matrix.det_one]
    rw [h0, mul_zero] at hdetmul
    exact one_ne_zero hdetmul.symm
  let uM : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have huM : (uM : Matrix (Fin n) (Fin n) F) = M :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero M hdet
  have hIsom : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      ((uM : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
      ((uM : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := by
    rw [huM]
    exact huni
  have hCent : ∀ s ∈ S, uM * s = s * uM := by
    intro s hs
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, huM]
    exact hcomm s hs
  have hFix : (uM : Matrix (Fin n) (Fin n) F) * (1 - ε) = 1 - ε := by
    rw [huM]
    exact hM1
  let u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) := ⟨uM, hIsom, hCent, hFix⟩
  refine ⟨u, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (actK u w : Fin n → F) = ((T : Module.End K W) w : Fin n → F)
  rw [hact u w]
  have huMat : ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
    change (uM : Matrix (Fin n) (Fin n) F) = M
    exact huM
  rw [huMat]
  obtain ⟨v, hv⟩ := w.2
  rw [Matrix.mulVecLin_apply] at hv
  have hMe : M * e = N := by
    show fePSU_dualPair_GepsGLK_extensionGraph σ G e N N' * e = N
    have hεe : ε * e = e := by rw [hεeq, Matrix.add_mul, he.2.1.eq, h0e, add_zero]
    unfold fePSU_dualPair_GepsGLK_extensionGraph
    rw [← hεeq]
    rw [Matrix.add_mul, Matrix.add_mul, hN, Matrix.mul_assoc, h0e, Matrix.mul_zero,
      Matrix.sub_mul, Matrix.one_mul, hεe, sub_self, add_zero, add_zero]
  calc Matrix.mulVec M (w : Fin n → F)
      = Matrix.mulVec M (Matrix.mulVec e v) := by rw [hv]
    _ = Matrix.mulVec (M * e) v := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec N v := by rw [hMe]
    _ = Matrix.mulVec N (Matrix.mulVec e v) := by rw [Matrix.mulVec_mulVec, hN]
    _ = Matrix.mulVec N (w : Fin n → F) := by rw [hv]
    _ = (Tl w : Fin n → F) := hNv w
    _ = ((T : Module.End K W) w : Fin n → F) := rfl

private lemma fePSU_dualPair_unitBlockCentralizer_faithful {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε))
    (hu : ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e = e) : u = 1 := by
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let M : Matrix (Fin n) (Fin n) F := ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hiso : Matrix.transpose (M.map σ) * G * M = G := by
    simpa [M, Unitary.conjTr, σ, G] using u.2.1
  have hM1 : M * (1 - ε) = 1 - ε := by simpa [M] using u.2.2.2
  have hcommA : ∀ a ∈ Algebra.adjoin F (Units.val '' S), M * a = a * M := by
    let C : Subalgebra F (Matrix (Fin n) (Fin n) F) :=
      { carrier := {a | M * a = a * M}
        add_mem' := by
          intro a b ha hb
          show M * (a + b) = (a + b) * M
          rw [mul_add, add_mul, ha, hb]
        mul_mem' := by
          intro a b ha hb
          show M * (a * b) = (a * b) * M
          calc M * (a * b) = (M * a) * b := by rw [mul_assoc]
            _ = (a * M) * b := by rw [ha]
            _ = a * (M * b) := by rw [mul_assoc]
            _ = a * (b * M) := by rw [hb]
            _ = (a * b) * M := by rw [← mul_assoc]
        algebraMap_mem' := by
          intro c
          show M * algebraMap F (Matrix (Fin n) (Fin n) F) c =
            algebraMap F (Matrix (Fin n) (Fin n) F) c * M
          simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one,
            Matrix.smul_mul, Matrix.one_mul] }
    have hsub : Algebra.adjoin F (Units.val '' S) ≤ C := by
      apply Algebra.adjoin_le
      rintro x ⟨s, hs, rfl⟩
      change M * (s : Matrix (Fin n) (Fin n) F) = (s : Matrix (Fin n) (Fin n) F) * M
      have hval := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F))
        (u.2.2.1 s hs)
      simpa [M] using hval
    intro a ha
    exact hsub ha
  let A' : Matrix (Fin n) (Fin n) F := Matrix.transpose (e.map σ)
  let estar : Matrix (Fin n) (Fin n) F := formAdj σ G e
  have hMe : M * e = e := hu
  have hAA : A' * Matrix.transpose (M.map σ) = A' := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hMe]
  have hAGM : A' * G * M = A' * G := by
    conv_lhs => rw [← hAA]
    rw [Matrix.mul_assoc A' (Matrix.transpose (M.map σ)) G,
        Matrix.mul_assoc A' (Matrix.transpose (M.map σ) * G) M, hiso]
  have hAsq : A' * A' = A' := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, he.2.1.eq]
  have hGestar : G * estar = A' * G := by
    show G * (G⁻¹ * A' * G) = A' * G
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  have hAGestar : A' * G * estar = A' * G := by
    rw [Matrix.mul_assoc, hGestar, ← Matrix.mul_assoc, hAsq]
  have hEstarA : estar ∈ Algebra.adjoin F (Units.val '' S) := by
    have h : estar = ε - e := by rw [hεeq]; abel
    rw [h]
    exact sub_mem hε.1 he.1
  have hcomm : M * estar = estar * M := hcommA estar hEstarA
  have hestar2 : estar * estar = estar := by
    have h := Geo.formAdj_mul σ hG e e
    rw [he.2.1.eq] at h
    exact h.symm
  have hw : estar * (M * estar - estar) = M * estar - estar := by
    rw [mul_sub, ← mul_assoc, hcomm.symm, mul_assoc, hestar2]
  have horth : A' * G * (M * estar - estar) = 0 := by
    have h1 : A' * G * (M * estar) = A' * G := by
      rw [← Matrix.mul_assoc, hAGM, hAGestar]
    rw [mul_sub, h1, hAGestar, sub_self]
  have hMstar : M * formAdj σ G e = formAdj σ G e :=
    sub_eq_zero.mp (fePSU_dualPair_blockPairing_nondegenerate σ hG hw horth)
  have hMone : M = 1 :=
    fePSU_dualPair_GepsGLK_faithful_decomp σ G hεeq hMe hM1 hMstar
  apply Subtype.ext
  apply Units.ext
  exact hMone

private lemma fePSU_dualPair_unitBlockCentralizer_equiv_iso {F : Type} [Field F] [Finite F] [CharP F
    2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (K : Type) [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0) :
    ∃ (m : ℕ), 1 ≤ m ∧
      Nonempty (↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) ≃*
        (Matrix (Fin m) (Fin m) K)ˣ) := by
  obtain ⟨hmod, htower, actK, hact, hcomp⟩ :=
    fePSU_dualPair_unitBlockCentralizer_KAction_body S hS he K π hπsurj hπker
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) := hmod
  letI : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)) := htower
  have hrealize := fePSU_dualPair_unitBlockCentralizer_extension_realizes hc S hS hSU hε he heε
    hpair hεeq K π actK hact hcomp
  let W := LinearMap.range (Matrix.mulVecLin e)
  haveI hWfin : Module.Finite K W := Module.Finite.of_restrictScalars_finite F K W
  haveI hWfree : Module.Free K W := Module.Free.of_divisionRing K W
  have hne : W ≠ ⊥ := by
    intro hbot
    have hf : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp hbot
    have h2 : e = 0 := by
      ext i j
      have h := congrFun (congrArg (fun g : (Fin n → F) →ₗ[F] (Fin n → F) =>
        g (Pi.single j 1)) hf) i
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h
    exact he.2.2.1 h2
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 1 ≤ Module.finrank K W :=
    (Module.finrank_pos_iff_of_free (R := K) (M := W)).mpr inferInstance
  let b : Module.Basis (Fin (Module.finrank K W)) K W := Module.finBasis K W
  let eGL : (Module.End K W)ˣ ≃* (Matrix (Fin (Module.finrank K W))
      (Fin (Module.finrank K W)) K)ˣ :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let φ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) →*
      (Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K)ˣ :=
    eGL.toMonoidHom.comp actK.toHomUnits
  have hinjUnits : Function.Injective actK.toHomUnits := by
    intro u v huv
    have h1 : actK.toHomUnits (u * v⁻¹) = 1 := by
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h1' : actK (u * v⁻¹) = 1 := by
      have h := congrArg (fun T : (Module.End K W)ˣ => (T : Module.End K W)) h1
      exact h
    have h2 : (((u * v⁻¹ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e = e := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro x
      show Matrix.mulVec ((((u * v⁻¹ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e) x = Matrix.mulVec e x
      rw [← Matrix.mulVec_mulVec]
      have hw : Matrix.mulVec (((u * v⁻¹ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (Matrix.mulVec e x) = Matrix.mulVec e x := by
        have h := congrArg (fun (f : Module.End K W) => f ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩) h1'
        have h' := congrArg Subtype.val h
        rw [hact (u * v⁻¹) ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩] at h'
        simpa using h'
      exact hw
    have h3 := fePSU_dualPair_unitBlockCentralizer_faithful S hε he hεeq
      (u * v⁻¹) h2
    exact mul_inv_eq_one.mp h3
  refine ⟨Module.finrank K W, hpos, ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩⟩⟩
  · exact eGL.injective.comp hinjUnits
  · intro A
    obtain ⟨u, hu⟩ := hrealize (eGL.symm A)
    exact ⟨u, by
      change eGL (actK.toHomUnits u) = A
      rw [hu]
      exact eGL.apply_symm_apply A⟩

private lemma fePSU_dualPair_unitBlockCentralizer_commutator_le_Geps {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F)) {ε : Matrix (Fin n) (Fin n) F} :
    Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
        (fePSU_dualPair_unitBlockCentralizer (f := f) S ε) ≤
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  let U := fePSU_dualPair_unitBlockCentralizer (f := f) S ε
  let c : GL (Fin n) F :=
    @Bracket.bracket (GL (Fin n) F) (GL (Fin n) F) commutatorElement a b
  have haU : a ∈ U := ha
  have hbU : b ∈ U := hb
  have hcU : c ∈ U := by
    change @Bracket.bracket (GL (Fin n) F) (GL (Fin n) F) commutatorElement a b ∈ U
    rw [commutatorElement_def]
    exact U.mul_mem (U.mul_mem (U.mul_mem haU hbU) (U.inv_mem haU)) (U.inv_mem hbU)
  have hxIso : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (c : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
      (c : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := hcU.1
  have hxCent : ∀ s ∈ S, c * s = s * c := hcU.2.1
  have hxFix : (c : Matrix (Fin n) (Fin n) F) * (1 - ε) = 1 - ε := hcU.2.2
  have hdetUnits : Matrix.GeneralLinearGroup.det c = 1 := by
    change Matrix.GeneralLinearGroup.det
      (@Bracket.bracket (GL (Fin n) F) (GL (Fin n) F) commutatorElement a b) = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hdetMat : (c : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Units.val_eq_one]
    exact hdetUnits
  let xSU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) :=
    ⟨c, Unitary.mem_SU.mpr ⟨hdetMat, hxIso⟩⟩
  have hGeps : xSU ∈ glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε := by
    change (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype xSU ∈
      Subgroup.centralizer S ⊓ glFixing (1 - ε)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (hxCent s hs).symm
    · show ((xSU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
          GL (Fin n) F) * (1 - ε) = 1 - ε
      exact hxFix
  exact Subgroup.mem_map.mpr ⟨xSU, hGeps, rfl⟩

private lemma fePSU_dualPair_Geps_le_unitBlockCentralizer {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F)) {ε : Matrix (Fin n) (Fin n) F} :
    (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ≤
      fePSU_dualPair_unitBlockCentralizer (f := f) S ε := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨hcent, hfix⟩ := Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hy)
  refine ⟨(Unitary.mem_SU.mp y.2).2, ?_, ?_⟩
  · intro s hs
    exact (Subgroup.mem_centralizer_iff.mp hcent s hs).symm
  · exact hfix

private lemma fePSU_dualPair_unitBlockCentralizer_derived_iso_of_equiv {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F)) {ε : Matrix (Fin n) (Fin n) F}
    {K : Type} [Field K] [Finite K] {m : ℕ}
    (eiso : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) ≃*
      (Matrix (Fin m) (Fin m) K)ˣ)
    (hm : 2 ≤ m) (hcond : 3 ≤ m ∨ ∃ s : Finset K, s.card = 4) :
    ∃ (m' : ℕ), 2 ≤ m' ∧
      Nonempty (↥(Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
        (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) ≃* StatedSL m' K) ∧
      Group.IsPerfect ↥(Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
        (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) := by
  let U := fePSU_dualPair_unitBlockCentralizer (f := f) S ε
  let D : Subgroup ↥U := ⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆
  have hGL : commutator (Matrix.GeneralLinearGroup (Fin m) K) = StatedSL m K :=
    GGNbrLSideKit.commutator_generalLinear_eq_statedSL hm hcond
  have hDmap : D.map eiso.toMonoidHom = StatedSL m K := by
    show (⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆ : Subgroup ↥U).map eiso.toMonoidHom = StatedSL m K
    rw [Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr eiso.surjective]
    exact hGL
  have hDsub : D.map U.subtype = (⁅U, U⁆ : Subgroup (GL (Fin n) F)) := by
    show (⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆ : Subgroup ↥U).map U.subtype =
      (⁅U, U⁆ : Subgroup (GL (Fin n) F))
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  let e1 : D ≃* StatedSL m K :=
    (D.equivMapOfInjective eiso.toMonoidHom eiso.injective).trans
      (MulEquiv.subgroupCongr hDmap)
  let e2 : D ≃* (⁅U, U⁆ : Subgroup (GL (Fin n) F)) :=
    (D.equivMapOfInjective U.subtype U.subtype_injective).trans
      (MulEquiv.subgroupCongr hDsub)
  have hperfSL : Group.IsPerfect ↥(StatedSL m K) := by
    by_cases h3 : 3 ≤ m
    · exact CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le h3 K
    · have hm2 : m = 2 := by omega
      subst hm2
      rcases hcond with h3' | ⟨s, hs⟩
      · exact absurd h3' h3
      · haveI : Fintype K := Fintype.ofFinite K
        have h4 : 4 ≤ Nat.card K := by
          have hle := Finset.card_le_univ s
          rw [hs] at hle
          simpa [Nat.card_eq_fintype_card] using hle
        exact CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card h4
  have hperfD : Group.IsPerfect ↥D := by
    haveI : Group.IsPerfect ↥(StatedSL m K) := hperfSL
    exact Group.IsPerfect.ofSurjective (f := e1.symm.toMonoidHom) e1.symm.surjective
  have hperf : Group.IsPerfect ↥(⁅U, U⁆ : Subgroup (GL (Fin n) F)) := by
    haveI : Group.IsPerfect ↥D := hperfD
    exact Group.IsPerfect.ofSurjective (f := e2.toMonoidHom) e2.surjective
  exact ⟨m, hm, ⟨e2.symm.trans e1⟩, hperf⟩

private lemma fePSU_matrix_units_commutative_of_le_one {K : Type} [Field K] {m : ℕ} (hm : m ≤ 1) :
    IsMulCommutative (Matrix (Fin m) (Fin m) K)ˣ := by
  have hm0 : m = 0 ∨ m = 1 := by omega
  rcases hm0 with rfl | rfl
  · haveI : Subsingleton (Matrix (Fin 0) (Fin 0) K)ˣ :=
      ⟨fun A B => Units.ext (Subsingleton.elim _ _)⟩
    exact ⟨⟨fun A B => Subsingleton.elim _ _⟩⟩
  · refine ⟨⟨fun A B => ?_⟩⟩
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]

private lemma fePSU_dualPair_unitBlockCentralizer_derived_iso_rank {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F)) {ε : Matrix (Fin n) (Fin n) F}
    {K : Type} [Field K] {m : ℕ}
    (eiso : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) ≃*
      (Matrix (Fin m) (Fin m) K)ˣ)
    (hnt : Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
      (fePSU_dualPair_unitBlockCentralizer (f := f) S ε) ≠ ⊥) :
    2 ≤ m := by
  by_contra h
  push Not at h
  have hm : m ≤ 1 := by omega
  haveI : IsMulCommutative (Matrix (Fin m) (Fin m) K)ˣ :=
    fePSU_matrix_units_commutative_of_le_one hm
  refine hnt ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hba : (⟨b, hb⟩ * ⟨a, ha⟩ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) =
      ⟨a, ha⟩ * ⟨b, hb⟩ := by
    apply eiso.injective
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _
  simpa using congrArg Subtype.val hba

private lemma fePSU_dualPair_blockField_card_ge_four {F : Type} [Field F] [Finite F]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {K : Type} [Field K] [Finite K] [Algebra F K]
    {d : ℕ} (hKfr : Module.finrank F K = d) (hdeg : 2 ≤ d) :
    4 ≤ Nat.card K := by
  have hF2 : 2 ≤ Nat.card F := by
    haveI : Nontrivial F := inferInstance
    have := Finite.one_lt_card (α := F)
    omega
  have hK : Nat.card K = Nat.card F ^ d := by
    rw [← hKfr]
    exact Module.natCard_eq_pow_finrank (K := F) (V := K)
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hdeg
    _ ≤ Nat.card F ^ d := Nat.pow_le_pow_left (by omega) d

private lemma fePSU_dualPair_finset_card_four_of_four_le {K : Type} [Finite K]
    (h : 4 ≤ Nat.card K) : ∃ s : Finset K, s.card = 4 := by
  letI : Fintype K := Fintype.ofFinite K
  have hle : 4 ≤ (Finset.univ : Finset K).card := by
    simpa [Nat.card_eq_fintype_card] using h
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4) hle
  exact ⟨s, hs⟩

private lemma fePSU_dualPair_unitBlockCentralizer_derived_iso {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} {n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (d : ℕ) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] (hKfr : Module.finrank F K = d)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0)
    (hnt : Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
      (fePSU_dualPair_unitBlockCentralizer (f := f) S ε) ≠ ⊥) :
    ∃ (m : ℕ), 2 ≤ m ∧
      Nonempty (↥(Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
        (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) ≃* StatedSL m K) ∧
      Group.IsPerfect ↥(Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
        (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) := by
  obtain ⟨m, _hm, ⟨eiso⟩⟩ :=
    fePSU_dualPair_unitBlockCentralizer_equiv_iso hc S hS hSU hε he heε hpair hεeq
      K π hπsurj hπker
  have hm : 2 ≤ m := fePSU_dualPair_unitBlockCentralizer_derived_iso_rank S eiso hnt
  have hcard : 4 ≤ Nat.card K := fePSU_dualPair_blockField_card_ge_four hc hKfr hdeg
  have hcond : 3 ≤ m ∨ ∃ s : Finset K, s.card = 4 :=
    Or.inr (fePSU_dualPair_finset_card_four_of_four_le hcard)
  exact fePSU_dualPair_unitBlockCentralizer_derived_iso_of_equiv S eiso hm hcond

private lemma fePSU_dualPair_Geps_derived_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (d : ℕ) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] (hKfr : Module.finrank F K = d)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0)
    (hnt : Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) ≠ ⊥) :
    Bracket.bracket
        ((glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype)
        ((glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype) =
      Bracket.bracket (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
        (fePSU_dualPair_unitBlockCentralizer (f := f) S ε) := by
  let U := fePSU_dualPair_unitBlockCentralizer (f := f) S ε
  let G : Subgroup (GL (Fin n) F) :=
    (glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε).map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
  have hG_le_U : G ≤ U := fePSU_dualPair_Geps_le_unitBlockCentralizer S
  have hUU_le_G : ⁅U, U⁆ ≤ G := fePSU_dualPair_unitBlockCentralizer_commutator_le_Geps S
  have hntU : ⁅U, U⁆ ≠ ⊥ := by
    intro hbot
    apply hnt
    have h1 : ⁅G, G⁆ = ⊥ := le_bot_iff.mp (hbot ▸ Subgroup.commutator_mono hG_le_U hG_le_U)
    have h2 : (⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype = ⊥ := by
      rw [Subgroup.map_commutator]
      exact h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (Subgroup.subtype_injective
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n))).mp h2
  obtain ⟨_, _, _, hperf⟩ :=
    fePSU_dualPair_unitBlockCentralizer_derived_iso hc S hS hSU hε he heε hpair hεeq
      d hdeg K hKfr π hπsurj hπker hntU
  have hH_perf : ⁅⁅U, U⁆, ⁅U, U⁆⁆ = ⁅U, U⁆ := by
    let H : Subgroup (GL (Fin n) F) := ⁅U, U⁆
    have hmap : (commutator ↥H).map H.subtype = H := by
      rw [Group.isPerfect_def.mp hperf, Subgroup.map_top, Subgroup.range_subtype]
    have hmap2 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
      show (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ : Subgroup ↥H).map H.subtype = ⁅H, H⁆
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap2]
    exact hmap
  show ⁅G, G⁆ = ⁅U, U⁆
  apply le_antisymm
  · exact Subgroup.commutator_mono hG_le_U hG_le_U
  · calc ⁅U, U⁆ = ⁅⁅U, U⁆, ⁅U, U⁆⁆ := hH_perf.symm
      _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono hUU_le_G hUU_le_G

private lemma fePSU_dualPair_GepsGLK_natural_derived_iso {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ}
    {n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (d : ℕ) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] (hKfr : Module.finrank F K = d)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0)
    (hnt : Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) ≠ ⊥) :
    ∃ (m : ℕ), 2 ≤ m ∧
      Nonempty (↥(Bracket.bracket
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) ≃*
        StatedSL m K) := by
  let U := fePSU_dualPair_unitBlockCentralizer (f := f) S ε
  let G : Subgroup (GL (Fin n) F) :=
    (glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
  have hG_le_U : G ≤ U := fePSU_dualPair_Geps_le_unitBlockCentralizer S
  have hUU_le_G : ⁅U, U⁆ ≤ G := fePSU_dualPair_unitBlockCentralizer_commutator_le_Geps S
  have hntU : ⁅U, U⁆ ≠ ⊥ := by
    intro hbot
    apply hnt
    have h1 : ⁅G, G⁆ = ⊥ := le_bot_iff.mp (hbot ▸ Subgroup.commutator_mono hG_le_U hG_le_U)
    have h2 : (⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype = ⊥ := by
      rw [Subgroup.map_commutator]
      exact h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (Subgroup.subtype_injective
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n))).mp h2
  obtain ⟨m, hm, ⟨eU⟩, _⟩ :=
    fePSU_dualPair_unitBlockCentralizer_derived_iso hc S hS hSU hε he heε hpair hεeq
      d hdeg K hKfr π hπsurj hπker hntU
  have heq : ⁅G, G⁆ = ⁅U, U⁆ :=
    fePSU_dualPair_Geps_derived_eq hc S hS hSU hε he heε hpair hεeq d hdeg K hKfr
      π hπsurj hπker hnt
  have hmap : (⁅glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype = ⁅G, G⁆ := by
    rw [Subgroup.map_commutator]
  let e1 : ↥(⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆) ≃*
      ↥⁅G, G⁆ :=
    ((⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
              ε⁆).equivMapOfInjective
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact ⟨m, hm, ⟨e1.trans ((MulEquiv.subgroupCongr heq).trans eU)⟩⟩

private lemma fePSU_dualPair_GepsGLK_natural {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (d : ℕ) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] (hKfr : Module.finrank F K = d)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0)
    (hnt : Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) ≠ ⊥) :
    ∃ (m : ℕ), 2 ≤ m ∧
      Nonempty (↥(Bracket.bracket
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) ≃*
        StatedSL m K) := by
  exact fePSU_dualPair_GepsGLK_natural_derived_iso hc S hS hSU hε he heε hpair hεeq d hdeg
    K hKfr π hπsurj hπker hnt

private lemma fePSU_dualPair_heldSize_derived_commutator {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K]
    (m : ℕ)
    (hiso : Nonempty (↥(Bracket.bracket
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) ≃*
        StatedSL m K)) :
    Nonempty (↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) ≃*
      StatedSL m K) := by
  exact hiso

private lemma fePSU_dualPair_heldSize_derived {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e) :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Finite E),
      2 ≤ m ∧ Nat.card E = (2 ^ f) ^ (2 * d) ∧
        Nonempty (↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) ≃* StatedSL m
            E) := by
  obtain ⟨K, hKf, hKa, hKfin, π, hπsurj, hπker, hKfr, hKcard⟩ :=
    fePSU_blockField_card hc S hS hodd he d hd
  letI : Field K := hKf
  letI : Algebra F K := hKa
  letI : Finite K := hKfin
  have hnt : Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) ≠ ⊥ := by
    intro h
    have hJbot : J' = ⊥ := le_bot_iff.mp (h ▸ hJε.1)
    exact (Subgroup.nontrivial_iff_ne_bot J').mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hJε.2.2) hJbot
  obtain ⟨m, hm, hiso⟩ :=
    fePSU_dualPair_GepsGLK_natural hc S hS hSU hε he heε hpair hεeq d hdeg K hKfr
      π hπsurj hπker hnt
  exact ⟨m, K, hKf, hKa, hKfin, hm, hKcard,
    fePSU_dualPair_heldSize_derived_commutator S K
      m hiso⟩

private lemma fePSU_dualPair_heldSize_transport {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (m : ℕ) (E : Type) [Field E]
    (hJ : J' = Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))
    (hiso : Nonempty (↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) ≃* StatedSL m
            E)) :
    Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃* StatedProj (StatedSL m E)) := by
  obtain ⟨eD⟩ := hiso
  obtain ⟨-, ⟨eC⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e.centralImage_facts ψ hψ hJε.2.2
  let e' : ↥J' ≃* StatedSL m E := (MulEquiv.subgroupCongr hJ).trans eD
  let eZ : ↥J' ⧸ Subgroup.center ↥J' ≃* StatedSL m E ⧸ Subgroup.center (StatedSL m E) :=
    QuotientGroup.congr (Subgroup.center ↥J') (Subgroup.center ↥(StatedSL m E)) e'
      (Subgroup.map_center_eq e')
  have hcenterSL : Subgroup.center ↥(StatedSL m E) =
      (StatedScalars (Fin m) E).subgroupOf (StatedSL m E) :=
    ((Subgroup.map_center_eq
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E)).symm).trans
      (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars m E)
  let eP : StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      StatedProj (StatedSL m E) :=
    QuotientGroup.quotientMulEquivOfEq hcenterSL
  exact ⟨eC.symm.trans (eZ.trans eP)⟩

private lemma fePSU_statedSL_quasisimple {m : ℕ} (K : Type) [Field K] [Finite K]
    (hm : 2 ≤ m) (h4 : 4 ≤ Nat.card K) : CFSG.Assembly.IsQuasisimple ↥(StatedSL m K) := by
  obtain h2 | h3 := eq_or_lt_of_le hm
  · subst h2
    exact (CFSG.Foundations.SteinbergCA.quasisimple_iff (↥(StatedSL 2 K))).2.1.mp
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
        (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4))
  · have hm' : 2 ≤ m - 1 := by omega
    have h := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := m - 1) hm' K
    have h' : (m - 1) + 1 = m := by omega
    rw [h'] at h
    exact (CFSG.Foundations.SteinbergCA.quasisimple_iff (↥(StatedSL m K))).2.1.mp h

private lemma fePSU_dualPair_heldSize {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e) :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Finite E),
      2 ≤ m ∧ Nat.card E = (2 ^ f) ^ (2 * d) ∧
        Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃* StatedProj (StatedSL m E)) := by
  obtain ⟨m, E, hEf, hEa, hEfin, hm, hEcard, ⟨hiso⟩⟩ :=
    fePSU_dualPair_heldSize_derived hc n S hSU hS hodd hε hJε he heε d hd hdeg hpair hεeq
  have hf1 : 1 ≤ f := by
    by_contra hf
    push Not at hf
    have hf0 : f = 0 := by omega
    subst hf0
    simp at hc
    haveI : Nontrivial F := inferInstance
    have := Finite.one_lt_card (α := F)
    omega
  have h4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    have h2f : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (2 ^ f) ^ (2 * d) := Nat.pow_le_pow_left h2f (2 * d)
  have hqSL : CFSG.Assembly.IsQuasisimple ↥(StatedSL m E) := fePSU_statedSL_quasisimple E hm h4
  have hqH : CFSG.Assembly.IsQuasisimple ↥(Bracket.bracket
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv hiso hqSL
  have hJ :=
    fePSU_dualPair_heldSize_eq n S hJε hqH
  exact ⟨m, E, hEf, hEa, hEfin, hm, hEcard,
    fePSU_dualPair_heldSize_transport n ψ hψ S hJε
      m E hJ ⟨hiso⟩⟩

private lemma fePSU_dualPair_derived {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (K : Type) [Field K] [Finite K]
    (hKcard : Nat.card K = (2 ^ f) ^ (2 * d)) :
    ∃ (m : ℕ), 2 ≤ m ∧
      Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃* StatedProj (StatedSL m K)) := by
  obtain ⟨m, E, hEfield, hEalg, hEfin, hm, hEcard, ⟨eiso⟩⟩ :=
    fePSU_dualPair_heldSize hc n ψ hψ S hSU hS hodd hε hJε he heε d hd hdeg hpair hεeq
  letI : Field E := hEfield
  letI : Finite E := hEfin
  obtain ⟨eKE⟩ := fePSU_statedSL_changeField (m := m) (E := E) (K := K)
    (by rw [hEcard, hKcard])
  exact ⟨m, hm, ⟨eiso.trans eKE⟩⟩

private lemma fePSU_dualPair_iso {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ f) ^ (2 * d) ∧ 2 ≤ m ∧
        Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃* StatedProj (StatedSL m K)) := by
  obtain ⟨K, hKfield, hKalg, hKfin, π, hsurj, hker, hfin, hcard⟩ :=
    fePSU_blockField_card hc S hS hodd he d hd
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨m, hm, eiso⟩ :=
    fePSU_dualPair_derived hc n ψ hψ S hSU hS hodd hε hJε he heε d hd hdeg hpair hεeq K hcard
  exact ⟨m, K, hKfield, hKfin, hcard, hm, eiso⟩

private theorem fePSU_dualPair {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e) :
    GGSixLSevenFieldExtCaseCl (J'.map ψ) .PSU f := by
  classical
  set d : ℕ := blockDegree (Algebra.adjoin F (Units.val '' S)) e with hd
  have hdeg' : 2 ≤ d := by rw [hd]; exact hdeg
  obtain ⟨m, K, hKfield, hKfin, hcard, hm, ⟨eiso⟩⟩ :=
    fePSU_dualPair_iso hc n ψ hψ S hSU hS hodd hε hJε he heε d hd hdeg' hpair hεeq
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hf : 1 ≤ f := fePSU_f_pos hc
  have h4 : 4 ≤ 2 * d * f := by
    calc (4 : ℕ) = (2 * 2) * 1 := by norm_num
      _ ≤ (2 * d) * f := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdeg') hf
      _ = 2 * d * f := by rw [mul_assoc]
  refine ⟨.PSL, m, 2 * d * f, Or.inl rfl, ?_, ?_, ?_⟩
  · have hlt : (1 : ℕ) * f < (2 * d) * f :=
      mul_lt_mul_of_pos_right (by omega : (1 : ℕ) < 2 * d) (by omega : 0 < f)
    simpa [one_mul] using hlt
  · refine Or.inl ⟨by decide, ?_⟩
    refine ⟨?_, ?_⟩
    · refine ⟨Nat.prime_two, ?_, ?_, ?_, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.mul_pos (by omega : 0 < 2 * d) (by omega : 0 < f))
      · omega
      · intro h
        have hp : 2 ^ (2 * d * f) = 2 := (Prod.mk.inj h).2
        have hle : 4 ≤ 2 ^ (2 * d * f) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (2 * d * f) :=
                Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num : 2 ≤ 4) h4)
        omega
      · intro h
        have hp : 2 ^ (2 * d * f) = 3 := (Prod.mk.inj h).2
        have hle : 4 ≤ 2 ^ (2 * d * f) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (2 * d * f) :=
                Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num : 2 ≤ 4) h4)
        omega
    · refine ⟨K, hKfield, hKfin, ?_, ⟨eiso⟩⟩
      calc Nat.card K = (2 ^ f) ^ (2 * d) := hcard
        _ = 2 ^ (f * (2 * d)) := (pow_mul 2 f (2 * d)).symm
        _ = 2 ^ (2 * d * f) := by congr 1; ring
  · intro h
    have hne : 2 * d * f ≠ 2 * f := by
      intro heq
      have h2 : 2 * d = 2 := mul_right_cancel₀ (by omega : f ≠ 0) heq
      have hd1 : d = 1 := by
        have h : 2 * d = 2 * 1 := by rw [h2]
        exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) h
      omega
    exact hne h.2.1

private lemma fePSU_selfDual_blockField_adjoint {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hfix : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e = e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K) (τ : K ≃+* K)
      (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K),
      Nat.card K = ((2 ^ f) ^ d) ^ 2 ∧ (∀ x, τ (τ x) = x) ∧
      (τ : K →+* K) ≠ RingHom.id K ∧
      (∀ x : F, τ (algebraMap F K x) = algebraMap F K
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f x)) ∧
      Function.Surjective π ∧ (∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0) := by
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let A : Subalgebra F (Matrix (Fin n) (Fin n) F) := Algebra.adjoin F (Units.val '' S)
  obtain ⟨K, hKf, hKa, hKfin, π, hπsurj, hπker, hKfr, hKcard⟩ :=
    fePSU_blockField_card hc S hS hodd he d hd
  letI : Field K := hKf
  letI : Algebra F K := hKa
  letI : Finite K := hKfin
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hσ : ∀ x, σ (σ x) = x :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hGh : Matrix.transpose (G.map σ) = G := by
    show Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n
    rw [fePSU_antidiag_map σ n, fePSU_transpose_antidiag n]
  have hSU' : ∀ s ∈ S, Matrix.transpose ((s : Matrix (Fin n) (Fin n) F).map σ) * G *
      (s : Matrix (Fin n) (Fin n) F) = G := by
    intro s hs
    simpa [Unitary.conjTr, G, σ] using hSU s hs
  haveI hAcomm : IsMulCommutative A := by
    refine Algebra.isMulCommutative_adjoin F ?_
    intro x hx y hy _
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    simpa using hS s hs t ht
  have hadjmem : ∀ a : A, formAdj σ G a.1 ∈ A :=
    fun a => Geo.formAdj_mem_adjoin σ hG hSU' a.2
  let adjHom : A →+* A :=
  { toFun := fun a => ⟨formAdj σ G a.1, hadjmem a⟩
    map_one' := by apply Subtype.ext; exact Geo.formAdj_one σ hG
    map_zero' := by apply Subtype.ext; simp [formAdj]
    map_mul' := fun a b => by
      apply Subtype.ext
      change formAdj σ G ((a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F)) =
        formAdj σ G (a : Matrix (Fin n) (Fin n) F) * formAdj σ G (b : Matrix (Fin n) (Fin n) F)
      rw [Geo.formAdj_mul σ hG]
      exact (congrArg Subtype.val (mul_comm' (⟨formAdj σ G a.1, hadjmem a⟩ : A)
        (⟨formAdj σ G b.1, hadjmem b⟩ : A))).symm
    map_add' := fun a b => by
      apply Subtype.ext
      exact Geo.formAdj_add σ G a.1 b.1 }
  let πr : A →+* K := (π : A →+* K)
  have hπr : Function.Surjective πr := hπsurj
  let fr : A →+* K := πr.comp adjHom
  have hker : ∀ a ∈ RingHom.ker πr, fr a = 0 := by
    intro a ha
    change πr (adjHom a) = 0
    change πr a = 0 at ha
    have hae : (a : Matrix (Fin n) (Fin n) F) * e = 0 := (hπker a).mp ha
    apply (hπker (adjHom a)).mpr
    have h1 : formAdj σ G ((a : Matrix (Fin n) (Fin n) F) * e) = 0 := by
      rw [hae]; simp [formAdj]
    rw [Geo.formAdj_mul σ hG, hfix] at h1
    have hc : formAdj σ G (a : Matrix (Fin n) (Fin n) F) * e =
        e * formAdj σ G (a : Matrix (Fin n) (Fin n) F) :=
      congrArg Subtype.val (mul_comm'
        (⟨formAdj σ G (a : Matrix (Fin n) (Fin n) F), hadjmem a⟩ : A) (⟨e, he.1⟩ : A))
    show formAdj σ G (a : Matrix (Fin n) (Fin n) F) * e = 0
    rw [hc, h1]
  let eK : A ⧸ RingHom.ker πr ≃+* K :=
    RingHom.quotientKerEquivOfSurjective (f := πr) hπr
  let τhom : K →+* K :=
    (Ideal.Quotient.lift (RingHom.ker πr) fr hker).comp eK.symm.toRingHom
  have hτπ : ∀ a : A, τhom (πr a) = πr (adjHom a) := by
    intro a
    have heK : eK.symm (πr a) = Ideal.Quotient.mk (RingHom.ker πr) a := by
      rw [← RingHom.quotientKerEquivOfSurjective_apply_mk (f := πr) hπr a,
        RingEquiv.symm_apply_apply]
    change (Ideal.Quotient.lift (RingHom.ker πr) fr hker) (eK.symm (πr a)) = πr (adjHom a)
    rw [heK]
    exact Ideal.Quotient.lift_mk (RingHom.ker πr) fr hker
  have hττ : ∀ k, τhom (τhom k) = k := by
    intro k
    obtain ⟨a, ha⟩ := hπr k
    rw [← ha, hτπ a, hτπ (adjHom a)]
    have hfix2 : adjHom (adjHom a) = a := by
      apply Subtype.ext
      exact Geo.formAdj_formAdj σ hσ hG hGh a.1
    rw [hfix2]
  have hinj : Function.Injective τhom := fun x y hxy => by
    have := congrArg τhom hxy
    rwa [hττ x, hττ y] at this
  have hsurj : Function.Surjective τhom := fun x => ⟨τhom x, hττ x⟩
  let τ : K ≃+* K := RingEquiv.ofBijective τhom ⟨hinj, hsurj⟩
  have hτalg : ∀ x : F, τ (algebraMap F K x) = algebraMap F K (σ x) := by
    intro x
    rw [← π.commutes x, ← π.commutes (σ x)]
    change τhom (πr (algebraMap F A x)) = πr (algebraMap F A (σ x))
    rw [hτπ (algebraMap F A x)]
    have h2 : adjHom (algebraMap F A x) = algebraMap F A (σ x) := by
      apply Subtype.ext
      show formAdj σ G (algebraMap F (Matrix (Fin n) (Fin n) F) x) =
        algebraMap F (Matrix (Fin n) (Fin n) F) (σ x)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        Geo.formAdj_smul, Geo.formAdj_one σ hG]
    rw [h2]
  have hcard : Nat.card K = ((2 ^ f) ^ d) ^ 2 := by
    rw [hKcard]
    rw [show ((2 ^ f) ^ d) ^ 2 = (2 ^ f) ^ (d * 2) from by rw [pow_mul], Nat.mul_comm]
  refine ⟨K, hKf, hKa, hKfin, τ, π, hcard, fun x => hττ x, ?_, fun x => hτalg x, hπsurj, hπker⟩
  intro hid
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hc
  have hid' : (τ : K → K) = (RingHom.id K : K → K) :=
    congrArg (fun g : K →+* K => (g : K → K)) hid
  have h : τ (algebraMap F K a) = algebraMap F K a := by rw [hid']; rfl
  rw [hτalg a] at h
  exact ha (RingHom.injective (algebraMap F K) h)

private lemma fePSU_subfield_pow_card {K : Type} [Field K] [Finite K] (L : Subfield K)
    {x : K} (hx : x ∈ L) : x ^ Nat.card L = x := by
  haveI : Fintype ↥L := Fintype.ofFinite ↥L
  rw [Nat.card_eq_fintype_card]
  have h := FiniteField.pow_card (⟨x, hx⟩ : L)
  have h' := congrArg (fun y : L => (y : K)) h
  simpa using h'

private lemma fePSU_pow_two_pow_of_dvd {K : Type} [Field K] {x : K} {a b : ℕ}
    (ha : x ^ 2 ^ a = x) (hab : a ∣ b) : x ^ 2 ^ b = x := by
  obtain ⟨k, rfl⟩ := hab
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, ha]

private lemma fePSU_rootSet_card_le {K : Type} [Field K] {m : ℕ} (hm : 1 ≤ m) :
    (Set.ncard {y : K | y ^ 2 ^ m = y}) ≤ 2 ^ m := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hmono : (Polynomial.X ^ 2 ^ m - Polynomial.X : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub (by
      rw [Polynomial.degree_X]
      exact WithBot.coe_lt_coe.mpr (by omega : (1 : ℕ) < 2 ^ m))
  have hroot : {y : K | y ^ 2 ^ m = y} =
      (Polynomial.X ^ 2 ^ m - Polynomial.X : Polynomial K).rootSet K := by
    ext y
    rw [Set.mem_setOf_eq, hmono.mem_rootSet]
    simp [Polynomial.aeval_X, sub_eq_zero]
  have hdeg : (Polynomial.X ^ 2 ^ m - Polynomial.X : Polynomial K).natDegree ≤ 2 ^ m := by
    calc (Polynomial.X ^ 2 ^ m - Polynomial.X : Polynomial K).natDegree
        ≤ max (Polynomial.X ^ 2 ^ m : Polynomial K).natDegree
            (Polynomial.X : Polynomial K).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ = max (2 ^ m) 1 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      _ = 2 ^ m := max_eq_left (by omega)
  rw [hroot]
  exact (Polynomial.ncard_rootSet_le
    (Polynomial.X ^ 2 ^ m - Polynomial.X : Polynomial K) K).trans hdeg

private lemma fePSU_set_eq_of_subset_card_le {α : Type} [Finite α] {S T : Set α}
    (hST : S ⊆ T) (hcard : T.ncard ≤ S.ncard) : S = T :=
  Set.eq_of_subset_of_ncard_le hST hcard

private lemma fePSU_subfield_le_of_card_pow_dvd {K : Type} [Field K] [Finite K]
    {L₁ L₂ : Subfield K} {a b : ℕ} (h₁ : Nat.card L₁ = 2 ^ a) (h₂ : Nat.card L₂ = 2 ^ b)
    (hab : a ∣ b) : L₁ ≤ L₂ := by
  have hb1 : 1 ≤ b := by
    by_contra hb
    push Not at hb
    have hb0 : b = 0 := by omega
    subst hb0
    simp at h₂
    haveI : Nontrivial ↥L₂ := inferInstance
    have := Finite.one_lt_card (α := ↥L₂)
    omega
  obtain ⟨k, rfl⟩ := hab
  intro x hx
  have hx1 : x ^ 2 ^ a = x := by
    have h := fePSU_subfield_pow_card L₁ hx
    rwa [h₁] at h
  have hxb : x ^ 2 ^ (a * k) = x := fePSU_pow_two_pow_of_dvd hx1 ⟨k, rfl⟩
  have hsub : (L₂ : Set K) ⊆ {y : K | y ^ 2 ^ (a * k) = y} := by
    intro y hy
    have h := fePSU_subfield_pow_card L₂ hy
    rwa [h₂] at h
  have hset : (L₂ : Set K) = {y : K | y ^ 2 ^ (a * k) = y} := by
    refine fePSU_set_eq_of_subset_card_le hsub ?_
    have h2' : (L₂ : Set K).ncard = 2 ^ (a * k) := by
      rw [← Nat.card_coe_set_eq (L₂ : Set K)]
      exact h₂
    rw [h2']
    exact fePSU_rootSet_card_le hb1
  change x ∈ (L₂ : Set K)
  rw [hset]
  exact hxb

private lemma fePSU_selfDual_involution_odd {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {K : Type} [Field K] [Finite K] [Algebra F K]
    (d : ℕ) (hcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (τ : K ≃+* K) (hτ2 : ∀ x, τ (τ x) = x) (hτne : (τ : K →+* K) ≠ RingHom.id K)
    (hτF : ∀ x : F, τ (algebraMap F K x) = algebraMap F K
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 f x)) :
    Odd d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτsq : τ ^ 2 = 1 := by
    ext x
    simp [pow_two, hτ2 x]
  have hτne1 : τ ≠ 1 := by
    intro h1
    exact hτne (by rw [h1]; rfl)
  have horderτ : orderOf τ = 2 := orderOf_eq_prime hτsq hτne1
  have hpowτ := CFSG.GH74.GLS.IVK.fixedField_card_pow τ
  rw [horderτ] at hpowτ
  have hAeq : Nat.card (CFSG.GH74.GLS.IVK.fixedField τ) = (2 ^ f) ^ d := by
    apply Nat.pow_left_injective (n := 2) (by norm_num : (2 : ℕ) ≠ 0)
    change Nat.card (CFSG.GH74.GLS.IVK.fixedField τ) ^ 2 = ((2 ^ f) ^ d) ^ 2
    rw [hpowτ, hcard]
  have hA : Nat.card (CFSG.GH74.GLS.IVK.fixedField τ) = 2 ^ (f * d) := by
    rw [hAeq, pow_mul]
  have hBF : Nat.card ((⊤ : Subfield F).map (algebraMap F K)) = 2 ^ (2 * f) := by
    show (((⊤ : Subfield F).map (algebraMap F K) : Subfield K) : Set K).ncard = 2 ^ (2 * f)
    have hset : (((⊤ : Subfield F).map (algebraMap F K) : Subfield K) : Set K) =
        algebraMap F K '' (⊤ : Set F) := by
      ext y
      change y ∈ (Subfield.map (algebraMap F K) (⊤ : Subfield F) : Subfield K) ↔
        y ∈ ⇑(algebraMap F K) '' (⊤ : Set F)
      rw [Subfield.mem_map]
      constructor
      · rintro ⟨x, -, hx⟩; exact ⟨x, Set.mem_univ x, hx⟩
      · rintro ⟨x, -, hx⟩; exact ⟨x, Subfield.mem_top x, hx⟩
    rw [hset, Set.InjOn.ncard_image (Set.injOn_of_injective (algebraMap F K).injective)]
    change (Set.univ : Set F).ncard = 2 ^ (2 * f)
    rw [Set.ncard_univ, hc, ← pow_mul]
    rw [Nat.mul_comm f 2]
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨m, hm⟩ := hodd
  have hab : 2 * f ∣ f * d := by
    rw [hm]
    exact ⟨m, by ring⟩
  have hle : (⊤ : Subfield F).map (algebraMap F K) ≤ CFSG.GH74.GLS.IVK.fixedField τ :=
    fePSU_subfield_le_of_card_pow_dvd (a := 2 * f) (b := f * d) hBF hA hab
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hc
  have hmem : algebraMap F K a ∈ (⊤ : Subfield F).map (algebraMap F K) := by
    rw [Subfield.mem_map]
    exact ⟨a, Subfield.mem_top a, rfl⟩
  have hfix : τ (algebraMap F K a) = algebraMap F K a :=
    (CFSG.GH74.GLS.IVK.mem_fixedField_iff τ (algebraMap F K a)).mp (hle hmem)
  have hσeq : algebraMap F K (CFSG.LieType.BorelTits.unitaryInvolution F 2 f a) =
      algebraMap F K a := by
    rw [← hτF a]
    exact hfix
  exact ha ((algebraMap F K).injective hσeq)

private lemma fePSU_selfDual_blockDegree_odd {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hfix : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e = e) :
    Odd d := by
  obtain ⟨K, hKf, hKa, hKfin, τ, _, hcard, hτ2, hτne, hτF, _, _⟩ :=
    fePSU_selfDual_blockField_adjoint hc S hSU hS hodd he d hd hfix
  letI : Field K := hKf
  letI : Algebra F K := hKa
  letI : Finite K := hKfin
  exact fePSU_selfDual_involution_odd hc d hcard τ hτ2 hτne hτF

private lemma fePSU_selfDual_GepsSU_embed {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) :
    ∃ (m : ℕ) (ψ : ↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ →*
        (Matrix (Fin m) (Fin m) K)ˣ),
      2 ≤ m ∧ Function.Injective ψ := by
  have hKfr : Module.finrank F K = d := by
    have h1 : Nat.card K = (2 ^ f) ^ (2 * d) := by
      rw [hKcard, ← pow_mul, Nat.mul_comm d 2]
    have h2 : Nat.card K = (2 ^ f) ^ (2 * Module.finrank F K) := by
      rw [Module.natCard_eq_pow_finrank (K := F) (V := K), hc, ← pow_mul]
    have h3 : (2 ^ f) ^ (2 * d) = (2 ^ f) ^ (2 * Module.finrank F K) := h1.symm.trans h2
    have hbase : 2 ≤ 2 ^ f := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (fePSU_f_pos hc)
    have h4 : 2 * d = 2 * Module.finrank F K := Nat.pow_right_injective hbase h3
    omega
  obtain ⟨m, hm, φ, hφ⟩ :=
    fePSU_dualPair_GepsGLK_action_matrix (f := f) (ε := ε) (e := ε) S hS he hε.2.1 d hd hdeg K hKfr
  exact ⟨m, φ.comp (Subgroup.inclusion (Subgroup.commutator_le_self _)), hm,
    hφ.comp (Subgroup.inclusion_injective (Subgroup.commutator_le_self _))⟩

private lemma fePSU_selfDual_blockKModW_range {F : Type} [Field F] {n : ℕ}
    (ε : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    Matrix.mulVec ε (Pi.single j 1) ∈ LinearMap.range (Matrix.mulVecLin ε) :=
  ⟨Pi.single j 1, rfl⟩

private lemma fePSU_selfDual_blockKModW_fix {F : Type} [Field F] {n : ℕ}
    (ε M : Matrix (Fin n) (Fin n) F)
    (hu : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec M w = w) (j : Fin n) :
    Matrix.mulVec M (Matrix.mulVec ε (Pi.single j 1)) = Matrix.mulVec ε (Pi.single j 1) :=
  hu ⟨Matrix.mulVec ε (Pi.single j 1), fePSU_selfDual_blockKModW_range ε j⟩

private lemma fePSU_selfDual_blockKModW_entry {F : Type} [Field F] {n : ℕ}
    (ε M : Matrix (Fin n) (Fin n) F)
    (hu : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec M w = w) (i j : Fin n) :
    (M * ε) i j = ε i j := by
  have h2 : Matrix.mulVec (M * ε) (Pi.single j 1) = Matrix.mulVec ε (Pi.single j 1) := by
    rw [← Matrix.mulVec_mulVec]
    exact fePSU_selfDual_blockKModW_fix ε M hu j
  have h3 := congrFun h2 i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h3

private lemma fePSU_selfDual_blockKModW {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (S :
    Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F} :
    ∀ u : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w = w) →
        ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε = ε := by
  intro u hu
  ext i j
  exact fePSU_selfDual_blockKModW_entry ε
    ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) hu i j

private lemma fePSU_selfDual_blockKModW_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F} :
    ∀ u : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w = w) → u = 1 := by
  intro u hu
  have hfix : ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 - ε) = 1 - ε := by
    have hm := (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).2
    show ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 - ε) = 1 - ε
    exact hm
  have hε' : ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε = ε :=
    fePSU_selfDual_blockKModW S u hu
  have hone : ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    calc ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * 1 := by rw [mul_one]
      _ = ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (ε + (1 - ε)) := by rw
          [add_sub_cancel]
      _ = ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε + ((u.1 : GL (Fin n) F) : Matrix
          (Fin n) (Fin n) F) * (1 - ε) := by
            rw [mul_add]
      _ = 1 := by rw [hε', hfix, add_sub_cancel]
  exact Subtype.ext (Subtype.ext (Units.ext hone))

private lemma fePSU_selfDual_blockKAction_faithful {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        (Module.End K (LinearMap.range (Matrix.mulVecLin ε)))ˣ)
    (hact : ∀ (u : glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)
        (w : LinearMap.range (Matrix.mulVecLin ε)),
        (((act u : Module.End K (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) =
          Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w) :
    Function.Injective act := by
  intro u v huv
  have h1 : act (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
  have h2 : ∀ w : LinearMap.range (Matrix.mulVecLin ε),
      ((act (u * v⁻¹) : Module.End K (LinearMap.range (Matrix.mulVecLin ε))) w) = w := by
    intro w; rw [h1]; rfl
  have hfix : ∀ w : LinearMap.range (Matrix.mulVecLin ε),
      Matrix.mulVec (((u * v⁻¹).1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w = w := by
    intro w
    rw [← hact (u * v⁻¹) w]
    exact congrArg Subtype.val (h2 w)
  have h3 : u * v⁻¹ = 1 :=
    fePSU_selfDual_blockKModW_eq_one S (u * v⁻¹) hfix
  exact mul_inv_eq_one.mp h3


private lemma fePSU_selfDual_blockField_algEquiv {F : Type} [Field F]
    (K K' : Type) [Field K] [Finite K] [Algebra F K] [Field K'] [Finite K'] [Algebra F K']
    (h : Nat.card K = Nat.card K') : Nonempty (K ≃ₐ[F] K') := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  have hcard : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h
  haveI : Polynomial.IsSplittingField F K (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial
      F) :=
    FiniteField.isSplittingField_sub K F
  haveI : Polynomial.IsSplittingField F K' (Polynomial.X ^ Fintype.card K - Polynomial.X :
      Polynomial F) := by
    rw [hcard]
    exact FiniteField.isSplittingField_sub K' F
  exact ⟨(Polynomial.IsSplittingField.algEquiv (K := F) (L := K)
      (f := Polynomial.X ^ Fintype.card K - Polynomial.X)).trans
    (Polynomial.IsSplittingField.algEquiv (K := F) (L := K')
      (f := Polynomial.X ^ Fintype.card K - Polynomial.X)).symm⟩

private lemma fePSU_selfDual_blockHeldSUid_pi {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) :
    ∃ π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K,
      Function.Surjective π ∧ (∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * ε = 0) := by
  obtain ⟨K', hK'f, hK'a, hK'fin, π', hπ'surj, hπ'ker, -, hK'card⟩ :=
    fePSU_blockField_card hc S hS hodd he d hd
  letI : Field K' := hK'f
  letI : Algebra F K' := hK'a
  letI : Finite K' := hK'fin
  have hcardK' : Nat.card K' = ((2 ^ f) ^ d) ^ 2 := by
    rw [hK'card, show (2 ^ f) ^ (2 * d) = (2 ^ f) ^ (d * 2) from by rw [Nat.mul_comm], pow_mul]
  have hcard : Nat.card K = Nat.card K' := by rw [hKcard, hcardK']
  obtain ⟨e⟩ := fePSU_selfDual_blockField_algEquiv (F := F) K' K hcard.symm
  refine ⟨e.toAlgHom.comp π', e.surjective.comp hπ'surj, ?_⟩
  intro a
  change e (π' a) = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * ε = 0
  rw [show e (π' a) = 0 ↔ π' a = 0 from by
    constructor
    · intro h; exact e.injective (by rw [h, map_zero])
    · intro h; rw [h, map_zero]]
  exact hπ'ker a

private lemma fePSU_selfDual_blockHeldSUid_action {F : Type} [Field F] [Finite F] [CharP F 2] {f n :
    ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * ε = 0) :
    ∃ (_ : Module K (LinearMap.range (Matrix.mulVecLin ε)))
      (_ : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin ε)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε)))
      (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε)))),
      Function.Injective (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))) ∧
      (∀ u w, (((act u : Module.End K (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) =
        Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w) ∧
      (∀ (a : Algebra.adjoin F (Units.val '' S)) (w : LinearMap.range (Matrix.mulVecLin ε)),
        ((π a • w : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F) =
          Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) w) := by
  obtain ⟨hmod, htower, actK, hactK, hactπ⟩ :=
    fePSU_blockKAction S hS (ε := ε) (e := ε) he K π hπsurj hπker
  letI : Module K (LinearMap.range (Matrix.mulVecLin ε)) := hmod
  letI : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε)) := htower
  haveI : Module.Finite F (LinearMap.range (Matrix.mulVecLin ε)) :=
    FiniteDimensional.of_injective (LinearMap.range (Matrix.mulVecLin ε)).subtype
      (LinearMap.range (Matrix.mulVecLin ε)).subtype_injective
  haveI : Module.Finite K (LinearMap.range (Matrix.mulVecLin ε)) :=
    Module.Finite.of_restrictScalars_finite F K (LinearMap.range (Matrix.mulVecLin ε))
  have hfaith : Function.Injective
      (actK.toHomUnits : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        (Module.End K (LinearMap.range (Matrix.mulVecLin ε)))ˣ) :=
    fePSU_selfDual_blockKAction_faithful S K
      actK.toHomUnits (fun u w => hactK u w)
  exact ⟨hmod, inferInstance, htower, actK.toHomUnits, hfaith.comp (Subgroup.inclusion_injective _),
    fun u w => hactK u w, hactπ⟩

open scoped commutatorElement

private lemma fePSU_selfDual_blockDim_commute {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (hW : Module.finrank E W ≤ 1)
    (u u' : LinearMap.GeneralLinearGroup E W) : Commute u u' := by
  rcases Nat.lt_or_ge (Module.finrank E W) 1 with h0 | h1
  · have : Subsingleton W := (Module.finrank_zero_iff (R := E)).mp (by omega)
    exact Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _)
  · have hfr : Module.finrank E W = 1 := by omega
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hfr
    obtain ⟨a, ha⟩ := hv ((u : Module.End E W) v)
    obtain ⟨b, hb⟩ := hv ((u' : Module.End E W) v)
    have hu : ∀ t : E, (u : Module.End E W) (t • v) = (t * a) • v := fun t => by
      rw [map_smul, ← ha, smul_smul]
    have hu' : ∀ t : E, (u' : Module.End E W) (t • v) = (t * b) • v := fun t => by
      rw [map_smul, ← hb, smul_smul]
    refine Units.ext (LinearMap.ext fun w => ?_)
    obtain ⟨c, rfl⟩ := hv w
    change (u : Module.End E W) ((u' : Module.End E W) (c • v)) =
      (u' : Module.End E W) ((u : Module.End E W) (c • v))
    rw [hu', hu, hu, hu']
    congr 1
    ring

private lemma fePSU_selfDual_blockHeldSUid_dim {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hact : Function.Injective (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))))
    (hnt : ⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≠ ⊥) :
    2 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin ε)) := by
  by_contra h
  push Not at h
  have hle : Module.finrank K (LinearMap.range (Matrix.mulVecLin ε)) ≤ 1 := by omega
  have hcomm : ∀ a b : LinearMap.GeneralLinearGroup K
      (LinearMap.range (Matrix.mulVecLin ε)), Commute a b :=
    fun a b => fePSU_selfDual_blockDim_commute hle a b
  let G : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) :=
    glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε
  let D : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) := ⁅G, G⁆
  have hbot : D = ⊥ := by
    refine le_bot_iff.mp ?_
    change ⁅G, G⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot]
    have h1 : act ⁅(⟨x, hx⟩ : ↥G), (⟨y, hy⟩ : ↥G)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
    have h3 : (⟨⁅x, y⁆, Subgroup.commutator_mem_commutator hx hy⟩ : ↥D) = 1 := by
      apply hact
      change act ⁅(⟨x, hx⟩ : ↥G), (⟨y, hy⟩ : ↥G)⁆ = act (1 : ↥G)
      rw [h1, map_one]
    simpa using congrArg Subtype.val h3
  exact hnt hbot

private noncomputable def fePSU_selfDual_blockFormF {F : Type} [Field F] [Finite F] [CharP F 2] {f n
    : ℕ}
    (ε : Matrix (Fin n) (Fin n) F) :
    (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom]
      (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[F] F :=
  (Matrix.toLinearMapₛₗ₂ (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n)) (Unitary.antidiag n)).domRestrict₁₂
    (LinearMap.range (Matrix.mulVecLin ε)) (LinearMap.range (Matrix.mulVecLin ε))

private lemma fePSU_selfDual_blockFormF_isSymm {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (ε : Matrix (Fin n) (Fin n) F) :
    (fePSU_selfDual_blockFormF (f := f) ε).IsSymm := by
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  have hσ : ∀ x, σ (σ x) = x :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hGσ : ∀ i j, σ (G i j) = G i j := by
    intro i j
    exact congrFun (congrFun (fePSU_antidiag_map σ n) i) j
  have hGt : ∀ i j, G i j = G j i := by
    intro i j
    exact (congrFun (congrFun (fePSU_transpose_antidiag n) i) j).symm
  have hB₀ : (Matrix.toLinearMapₛₗ₂ σ (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n)) G).IsSymm :=
      by
    refine ⟨fun x y => ?_⟩
    simp only [Matrix.toLinearMapₛₗ₂_apply, Pi.basisFun_repr, map_sum, map_mul, hσ, hGσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hGt i j]
    simp only [smul_eq_mul]
    rw [map_mul, map_mul, hσ, hGσ]
    ring
  simpa [fePSU_selfDual_blockFormF, σ, G] using
    hB₀.domRestrict (LinearMap.range (Matrix.mulVecLin ε))

private lemma fePSU_selfDual_blockFormF_separatingLeft {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {ε : Matrix (Fin n) (Fin n) F}
    (hεadj : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) ε = ε) (hεidem : ε * ε = ε) :
    (fePSU_selfDual_blockFormF (f := f) ε).SeparatingLeft := by
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let W : Submodule F (Fin n → F) := LinearMap.range (Matrix.mulVecLin ε)
  let B₀ : (Fin n → F) →ₛₗ[σ] (Fin n → F) →ₗ[F] F :=
    Matrix.toLinearMapₛₗ₂ σ (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n)) G
  have hσ : ∀ x, σ (σ x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hadj : G * ε = Matrix.transpose (ε.map σ) * G := by
    have h := hεadj
    simp only [formAdj] at h
    calc G * ε = G * (G⁻¹ * Matrix.transpose (ε.map σ) * G) := by rw [h]
      _ = Matrix.transpose (ε.map σ) * G := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  have hB₀apply : ∀ x y : Fin n → F, B₀ x y = ∑ i, σ (x i) * (G.mulVec y) i := by
    intro x y
    simp only [B₀, Matrix.toLinearMapₛₗ₂_apply, Pi.basisFun_repr, smul_eq_mul,
      Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hstep : ∀ x w : Fin n → F,
      B₀ x (Matrix.mulVec ε w) = ∑ j, σ ((Matrix.mulVec ε x) j) * (G.mulVec w) j := by
    intro x w
    rw [hB₀apply]
    have e : ∀ i, (G.mulVec (Matrix.mulVec ε w)) i = ∑ j, σ (ε j i) * (G.mulVec w) j := by
      intro i
      rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, Matrix.map_apply]
    simp only [e, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec_apply_eq_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    ring
  have hBsep : (B₀.domRestrict₁₂ W W).SeparatingLeft := by
    rw [LinearMap.separatingLeft_iff_linear_nontrivial]
    intro x hx
    have hxw : ∀ w : Fin n → F, B₀ (x : Fin n → F) (Matrix.mulVec ε w) = 0 := by
      intro w
      have h := congrArg (fun f : W →ₗ[F] F => f ⟨Matrix.mulVec ε w, ⟨w, rfl⟩⟩) hx
      simpa [B₀, W, LinearMap.domRestrict₁₂_apply] using h
    have hsig : ∀ k, σ (Matrix.mulVec ε (x : Fin n → F) k) = 0 := by
      intro k
      have hk := hxw (Matrix.mulVec G⁻¹ (Pi.single k 1))
      rw [hstep, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec] at hk
      simpa [Pi.single_apply] using hk
    have hεx : Matrix.mulVec ε (x : Fin n → F) = 0 := by
      funext k
      have := hsig k
      simpa [hσ] using congrArg σ this
    obtain ⟨v, hv⟩ := x.2
    refine Subtype.ext ?_
    have hxx : (x : Fin n → F) = Matrix.mulVec ε (x : Fin n → F) := by
      rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεidem]
    exact hxx.trans hεx
  simpa [fePSU_selfDual_blockFormF, σ, G, W, B₀] using hBsep

private lemma fePSU_selfDual_blockFormDescent_involution {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2] :
    ∀ c : F, (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) (algebraMap F K c) =
      algebraMap F K ((CFSG.LieType.BorelTits.unitaryInvolution F 2 f) c) := by
  have hodd_d : Odd d :=
    fePSU_selfDual_blockDegree_odd hc S hSU hS hodd he d hd hε.2.2.2.1
  have hσ2 : CFSG.LieType.BorelTits.unitaryInvolution F 2 f ^ 2 = 1 := by
    ext x
    change CFSG.LieType.BorelTits.unitaryInvolution F 2 f
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 f x) = x
    exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hc x
  have hpow : CFSG.LieType.BorelTits.unitaryInvolution F 2 f ^ d =
      CFSG.LieType.BorelTits.unitaryInvolution F 2 f := by
    obtain ⟨k, hk⟩ := hodd_d
    rw [hk, pow_succ, pow_mul, hσ2, one_pow, one_mul]
  have hcomp : CFSG.LieType.BorelTits.unitaryInvolution F 2 (f * d) =
      CFSG.LieType.BorelTits.unitaryInvolution F 2 f := by
    change iterateFrobeniusEquiv F 2 (f * d) = iterateFrobeniusEquiv F 2 f
    rw [iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_eq_pow, pow_mul,
      ← iterateFrobeniusEquiv_eq_pow]
    exact hpow
  intro c
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← map_pow]
  have hc_eq : c ^ 2 ^ (f * d) = CFSG.LieType.BorelTits.unitaryInvolution F 2 f c := by
    rw [← CFSG.LieType.BorelTits.unitaryInvolution_apply]
    exact DFunLike.congr_fun hcomp c
  rw [hc_eq]

private lemma fePSU_selfDual_blockFormDescent_adjoint_eval {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F} :
    ∀ x y : (LinearMap.range (Matrix.mulVecLin ε)),
      fePSU_selfDual_blockFormF (f := f) ε x y =
        ∑ i, (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
            (((x : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F) i) *
          (Matrix.mulVec (Unitary.antidiag n)
            ((y : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F)) i := by
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let B₀ : (Fin n → F) →ₛₗ[σ] (Fin n → F) →ₗ[F] F :=
    Matrix.toLinearMapₛₗ₂ σ (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n)) G
  have hB₀ : ∀ x y : Fin n → F, B₀ x y = ∑ i, σ (x i) * (G.mulVec y) i := by
    intro x y
    simp only [B₀, Matrix.toLinearMapₛₗ₂_apply, Pi.basisFun_repr, smul_eq_mul,
      Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  intro x y
  change B₀ (x : Fin n → F) (y : Fin n → F) =
    ∑ i, σ ((x : Fin n → F) i) * (G.mulVec (y : Fin n → F)) i
  exact hB₀ (x : Fin n → F) (y : Fin n → F)

private lemma fePSU_selfDual_blockFormDescent_adjoint_matrix {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ}
    (M N : Matrix (Fin n) (Fin n) F)
    (hMN : Unitary.antidiag n * N =
      Matrix.transpose (M.map (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) *
        Unitary.antidiag n) :
    ∀ x y : Fin n → F,
      (∑ i, (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) ((Matrix.mulVec M x) i) *
        (Matrix.mulVec (Unitary.antidiag n) y) i) =
      ∑ i, (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (x i) *
        (Matrix.mulVec (Unitary.antidiag n) (Matrix.mulVec N y)) i := by
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  intro x y
  have hσM : (fun i => σ ((Matrix.mulVec M x) i)) =
      Matrix.mulVec (M.map σ) (fun i => σ (x i)) := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
    simp only [Matrix.map_apply, map_sum, map_mul]
  have hmain : dotProduct (Matrix.mulVec (M.map σ) (fun i => σ (x i)))
        (Matrix.mulVec G y) =
      dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec N y)) := by
    calc dotProduct (Matrix.mulVec (M.map σ) (fun i => σ (x i))) (Matrix.mulVec G y)
        = dotProduct (Matrix.mulVec G y) (Matrix.mulVec (M.map σ) (fun i => σ (x i))) :=
          dotProduct_comm _ _
      _ = dotProduct (fun i => σ (x i))
            (Matrix.mulVec (Matrix.transpose (M.map σ)) (Matrix.mulVec G y)) :=
          (Matrix.dotProduct_transpose_mulVec (M.map σ) (fun i => σ (x i))
            (Matrix.mulVec G y)).symm
      _ = dotProduct (fun i => σ (x i))
            (Matrix.mulVec (Matrix.transpose (M.map σ) * G) y) := by rw [Matrix.mulVec_mulVec]
      _ = dotProduct (fun i => σ (x i)) (Matrix.mulVec (G * N) y) := by rw [← hMN]
      _ = dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec N y)) := by rw
          [Matrix.mulVec_mulVec]
  change dotProduct (fun i => σ ((Matrix.mulVec M x) i)) (Matrix.mulVec G y) =
    dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec N y))
  rw [hσM]
  exact hmain

private lemma fePSU_selfDual_blockFormDescent_adjoint {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hactπ : ∀ (a : Algebra.adjoin F (Units.val '' S)) (w : LinearMap.range (Matrix.mulVecLin ε)),
      (((π a) • w : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) w)
    (hτπ : ∀ (a : Algebra.adjoin F (Units.val '' S)) (w : LinearMap.range (Matrix.mulVecLin ε)),
      (((CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) (π a)) • w :
          LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F) =
        Matrix.mulVec (formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
          (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) F)) w) :
    ∀ (a : K) (x y : (LinearMap.range (Matrix.mulVecLin ε))),
      fePSU_selfDual_blockFormF (f := f) ε (a • x) y =
        fePSU_selfDual_blockFormF (f := f) ε x
          ((CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) a) • y) := by
  intro a x y
  obtain ⟨ã, rfl⟩ := hπsurj a
  have heval :=
    fePSU_selfDual_blockFormDescent_adjoint_eval (F := F) (f := f) (ε := ε)
  have hG : IsUnit (Unitary.antidiag n).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hMN : Unitary.antidiag n *
      formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
        (ã : Matrix (Fin n) (Fin n) F) =
      Matrix.transpose (((ã : Matrix (Fin n) (Fin n) F)).map
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) * Unitary.antidiag n := by
    rw [formAdj, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  rw [heval (π ã • x) y]
  rw [heval x (((CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) (π ã)) • y)]
  rw [hactπ ã x, hτπ ã y]
  exact fePSU_selfDual_blockFormDescent_adjoint_matrix (ã : Matrix (Fin n) (Fin n) F)
    (formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
      (ã : Matrix (Fin n) (Fin n) F)) hMN x y

private lemma fePSU_selfDual_blockFormDescent_actInvariant {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε))))
    (hactm : ∀ u w, (((act u : Module.End K (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
        =
        Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w) :
    ∀ u x y, fePSU_selfDual_blockFormF (f := f) ε
        ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
          (LinearMap.range (Matrix.mulVecLin ε))) x)
      ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) y) = fePSU_selfDual_blockFormF (f := f) ε x y := by
  intro u x y
  let M : Matrix (Fin n) (Fin n) F := (u.1 : GL (Fin n) F)
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  have heval :=
    fePSU_selfDual_blockFormDescent_adjoint_eval (F := F) (f := f) (ε := ε)
  have hx := hactm u x
  have hy := hactm u y
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hiso : Matrix.transpose (M.map σ) * G * M = G := by
    have h := (Unitary.mem_SU.mp (u.1).2).2
    simpa [Unitary.conjTr, M, G, σ] using h
  have hMN : G * formAdj σ G M = Matrix.transpose (M.map σ) * G := by
    rw [formAdj, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hMM : formAdj σ G M * M = 1 := by
    rw [formAdj]
    rw [show (G⁻¹ * Matrix.transpose (M.map σ) * G) * M =
        G⁻¹ * (Matrix.transpose (M.map σ) * G * M) from by
      simp only [Matrix.mul_assoc]]
    rw [hiso, Matrix.nonsing_inv_mul G hG]
  have hNy : Matrix.mulVec (formAdj σ G M) (Matrix.mulVec M y) = y := by
    rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  rw [heval ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
      (LinearMap.range (Matrix.mulVecLin ε))) x)
    ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
      (LinearMap.range (Matrix.mulVecLin ε))) y)]
  rw [heval x y]
  rw [hx, hy]
  exact (fePSU_selfDual_blockFormDescent_adjoint_matrix M (formAdj σ G M) hMN x
    (Matrix.mulVec M y)).trans (by rw [hNy])

private lemma fePSU_selfDual_blockFormDescent_trace {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (B_F : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[F] F)
    (hBs : B_F.IsSymm) (hBl : B_F.SeparatingLeft)
    (hbar : ∀ c : F, (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) (algebraMap F K c) =
      algebraMap F K ((CFSG.LieType.BorelTits.unitaryInvolution F 2 f) c))
    (hadj : ∀ (a : K) (x y : (LinearMap.range (Matrix.mulVecLin ε))),
      B_F (a • x) y = B_F x ((CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) a) • y)) :
    ∃ B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K,
      B.IsSymm ∧ B.SeparatingLeft ∧
      (∀ v w, Algebra.trace F K (B v w) = B_F v w) := by
  have hf : 1 ≤ f := fePSU_f_pos hc
  have hfd : 1 ≤ f * d := le_trans hf (Nat.le_mul_of_pos_right f (by omega))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : FiniteDimensional F K :=
    ⟨⟨Finset.univ, by simpa using Submodule.span_univ F K⟩⟩
  haveI : Algebra.IsSeparable F K := inferInstance
  haveI hKF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, hf, by rw [hc, ← pow_mul]; congr 1; ring⟩
  haveI hKK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f * d) K :=
    ⟨Nat.prime_two, hfd, by rw [hKcard, ← pow_mul, ← pow_mul]; congr 1; ring⟩
  have hbarF : hKF.bar = (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom := by
    ext x
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
      ← CFSG.LieType.BorelTits.unitaryInvolution_apply]
    rfl
  have hbarK : hKK.bar = (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom := by
    ext x
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
      ← CFSG.LieType.BorelTits.unitaryInvolution_apply]
    rfl
  have hbar' : ∀ c : F, hKK.bar (algebraMap F K c) = algebraMap F K (hKF.bar c) := by
    intro c
    rw [hbarK, hbarF]
    exact hbar c
  have hadj' : ∀ (l : K) (v w : (LinearMap.range (Matrix.mulVecLin ε))),
      B_F (l • v) w = B_F v (hKK.bar l • w) := by
    intro l v w
    rw [hbarK]
    exact hadj l v w
  obtain ⟨H, hHs, hHl, hHtr⟩ :=
    CFSG.StandardType.OrdPOutSU.exists_transfer (K := F) (L := K)
      (V := (LinearMap.range (Matrix.mulVecLin ε))) hbar' B_F hBs hBl hadj'
  exact ⟨H, hHs, hHl, hHtr⟩

private lemma fePSU_selfDual_blockFormDescent_unitary {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε))))
    (B_F : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[F] F)
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K) (hBt : ∀ v w, Algebra.trace F K (B v w) =
            B_F v w)
    (hunitF : ∀ u x y, B_F ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) x)
      ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) y) = B_F x y) :
    ∀ u, act u ∈ CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B := by
  intro u
  rw [CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
  intro x y
  have htr : ∀ v w c, Algebra.trace F K (B v w * c) = B_F v (c • w) := by
    intro v w c
    rw [mul_comm (B v w) c, ← smul_eq_mul, ← map_smul, hBt]
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate F K).1
    (B ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) x)
      ((act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) y) - B x y) fun c => ?_
  rw [Algebra.traceForm_apply, sub_mul, map_sub, htr, htr,
    show c • (act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) y =
      (act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) (c • y) from
      (map_smul (act u : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) c y).symm,
    hunitF, sub_self]


private lemma fePSU_selfDual_blockHeldSUid_surj_commutator {F : Type} [Field F] [Finite F] [CharP F
    2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε)))) :
(act.comp (Subgroup.inclusion (Subgroup.commutator_le_self
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))).range =
      ⁅act.range, act.range⁆ := by
  let G : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) :=
    glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε
  change (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self G))).range = ⁅act.range,
      act.range⁆
  rw [MonoidHom.range_eq_map (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self G)))]
  rw [← Subgroup.map_map]
  rw [show ⁅act.range, act.range⁆ = ⁅Subgroup.map act ⊤, Subgroup.map act ⊤⁆ by
    rw [MonoidHom.range_eq_map]]
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective (Subgroup.subtype_injective G)
  rw [Subgroup.map_map]
  rw [show ((Subgroup.subtype G).comp (Subgroup.inclusion (Subgroup.commutator_le_self G))) =
      Subgroup.subtype ⁅G,G⁆ from rfl]
  rw [show Subgroup.map (Subgroup.subtype ⁅G,G⁆) ⊤ = ⁅G,G⁆ by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩]
  rw [show (⁅(⊤ : Subgroup ↥G), ⊤⁆ : Subgroup ↥G) = _root_.commutator ↥G from rfl,
      Subgroup.map_subtype_commutator G]

private lemma fePSU_selfDual_blockHeldSUid_surj_perfect {F : Type} [Field F] [Finite F]
    {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [FiniteDimensional K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBs : B.IsSymm) (hBl : B.SeparatingLeft)
    (hdim : 2 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin ε))) :
⁅CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B,
        CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B⁆ =
      CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B := by
  have hf : 1 ≤ f := fePSU_f_pos hc
  have hfd : 1 ≤ f * d := le_trans hf (Nat.le_mul_of_pos_right f (by omega))
  have h2fd : 2 ≤ f * d := by
    calc (2 : ℕ) = 1 * 2 := by norm_num
      _ ≤ f * d := Nat.mul_le_mul hf hdeg
  haveI hKK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f * d) K :=
    ⟨Nat.prime_two, hfd, by rw [hKcard, ← pow_mul, ← pow_mul]; congr 1; ring⟩
  have hgood : (Module.finrank K (LinearMap.range (Matrix.mulVecLin ε)) = 2 → 4 ≤ 2 ^ (f * d)) ∧
      (Module.finrank K (LinearMap.range (Matrix.mulVecLin ε)) = 3 → 3 ≤ 2 ^ (f * d)) := by
    constructor
    · intro _
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) h2fd
    · intro _
      calc (3 : ℕ) ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) h2fd
  haveI hq : CFSG.IsQuasisimple ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hKK hBs hBl hdim hgood
  have hperf : Group.IsPerfect ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
      hq.1
  rw [← Subgroup.map_subtype_commutator
    (CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)]
  rw [Group.isPerfect_def.mp hperf]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

private lemma fePSU_selfDual_blockHeldSUid_extend_det_mem {F K : Type} [Field F] [Field K] {n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] LinearMap.range (Matrix.mulVecLin ε))
    (U : GL (Fin n) F)
    (hact : ∀ w : LinearMap.range (Matrix.mulVecLin ε),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) = (g w : Fin n → F)) :
    ∀ v : Fin n → F, v ∈ LinearMap.range (Matrix.mulVecLin ε) →
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) v ∈ LinearMap.range (Matrix.mulVecLin ε) := by
  intro v hv
  rw [hact ⟨v, hv⟩]
  exact (g ⟨v, hv⟩).2

private lemma fePSU_selfDual_blockHeldSUid_extend_det_mat {F : Type} [Field F] {n : ℕ}
    (U : GL (Fin n) F) :
    (U : Matrix (Fin n) (Fin n) F).det =
      LinearMap.det (Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) F)) := by
  rw [← Matrix.toLin'_apply' (U : Matrix (Fin n) (Fin n) F)]
  rw [← LinearMap.det_toMatrix' (Matrix.toLin' (U : Matrix (Fin n) (Fin n) F))]
  rw [LinearMap.toMatrix'_toLin' (U : Matrix (Fin n) (Fin n) F)]

private lemma fePSU_selfDual_blockHeldSUid_extend_det_factor {F : Type} [Field F] {n : ℕ}
    (ε : Matrix (Fin n) (Fin n) F) (U : GL (Fin n) F)
    (hW : ∀ v : Fin n → F, v ∈ LinearMap.range (Matrix.mulVecLin ε) →
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) v ∈ LinearMap.range (Matrix.mulVecLin ε))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    LinearMap.det (Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) F)) =
      LinearMap.det (((Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) F)).domRestrict
        (LinearMap.range (Matrix.mulVecLin ε))).codRestrict
        (LinearMap.range (Matrix.mulVecLin ε)) (fun w => hW w.1 w.2)) := by
  let W : Submodule F (Fin n → F) := LinearMap.range (Matrix.mulVecLin ε)
  let M : (Fin n → F) →ₗ[F] (Fin n → F) := Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) F)
  have hW' : W ≤ Submodule.comap M W := fun v hv => hW v hv
  have hQ : W.mapQ W M hW' = LinearMap.id := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on W x (fun v => ?_)
    rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]
    have hv : M v - v = Matrix.mulVec ((U : Matrix (Fin n) (Fin n) F) - 1) v := by
      simp [M, Matrix.sub_mulVec]
    rw [hv]
    have hU : (U : Matrix (Fin n) (Fin n) F) - 1 =
        (U : Matrix (Fin n) (Fin n) F) * ε - ε := by
      have h' : (U : Matrix (Fin n) (Fin n) F) * ε +
          (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (U : Matrix (Fin n) (Fin n) F) := by
        rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
      rw [hfix] at h'
      nth_rewrite 1 [← h']
      abel
    rw [hU, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    exact W.sub_mem (hW _ (LinearMap.mem_range.mpr ⟨v, rfl⟩))
      (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  rw [LinearMap.det_eq_det_mul_det W M hW', hQ, LinearMap.det_id, mul_one]
  rfl

private lemma fePSU_selfDual_blockHeldSUid_extend_det_block_one {F K : Type} [Field F] [Field K]
    [Algebra F K]
    {n : ℕ} {ε : Matrix (Fin n) (Fin n) F}
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] LinearMap.range (Matrix.mulVecLin ε))
    (hgdet : LinearMap.det g = 1)
    (U : GL (Fin n) F)
    (hact : ∀ w : LinearMap.range (Matrix.mulVecLin ε),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) = (g w : Fin n → F))
    (hW : ∀ v : Fin n → F, v ∈ LinearMap.range (Matrix.mulVecLin ε) →
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) v ∈ LinearMap.range (Matrix.mulVecLin ε)) :
    LinearMap.det (((Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) F)).domRestrict
        (LinearMap.range (Matrix.mulVecLin ε))).codRestrict
        (LinearMap.range (Matrix.mulVecLin ε)) (fun w => hW w.1 w.2)) = 1 := by
  have hEq : ((Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) F)).domRestrict
        (LinearMap.range (Matrix.mulVecLin ε))).codRestrict
        (LinearMap.range (Matrix.mulVecLin ε)) (fun w => hW w.1 w.2) =
      g.restrictScalars F := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact hact w
  rw [hEq, LinearMap.det_restrictScalars, hgdet, map_one]

private lemma fePSU_selfDual_blockHeldSUid_extend_det {F : Type} [Field F] {f
    n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    (U : Matrix (Fin n) (Fin n) F).det = 1 := by
  have hW : ∀ v : Fin n → F, v ∈ LinearMap.range (Matrix.mulVecLin ε) →
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) v ∈ LinearMap.range (Matrix.mulVecLin ε) :=
    fePSU_selfDual_blockHeldSUid_extend_det_mem
      (g := (g : LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] LinearMap.range (Matrix.mulVecLin ε)))
      U hact
  have hmat := fePSU_selfDual_blockHeldSUid_extend_det_mat U
  have hfac := fePSU_selfDual_blockHeldSUid_extend_det_factor ε U hW hfix
  have hone := fePSU_selfDual_blockHeldSUid_extend_det_block_one
    (g := (g : LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] LinearMap.range (Matrix.mulVecLin ε)))
    (CFSG.LocalAnalysis.ComponentInitial.mem_sesqSpecialUnitaryGroup.mp hg).2 U hact hW
  exact hmat.trans (hfac.trans hone)

private lemma fePSU_selfDual_blockHeldSUid_extend_form_decomp {F : Type} [Field F] {n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    ∀ x : Fin n → F,
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) x = ((((g : (LinearMap.range (Matrix.mulVecLin
          ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) ⟨Matrix.mulVec ε x,
              LinearMap.mem_range.mpr ⟨x, rfl⟩⟩) : Fin n → F) + Matrix.mulVec (1 - ε) x) := by
  intro x
  have hx : Matrix.mulVec ε x + Matrix.mulVec (1 - ε) x = x := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  conv_lhs => rw [← hx, Matrix.mulVec_add]
  rw [hact ⟨Matrix.mulVec ε x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩,
    Matrix.mulVec_mulVec, hfix]

private lemma fePSU_selfDual_blockHeldSUid_extend_form_orth_core {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ (v : LinearMap.range (Matrix.mulVecLin ε)) (y : Fin n → F),
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (↑v : Fin n → F)
          (Matrix.mulVec (1 - ε) y) = 0 := by
  intro v y
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hadj : G * ε = Matrix.transpose (ε.map σ) * G := by
    have h := hε.2.2.2.1
    simp only [formAdj] at h
    calc G * ε = G * (G⁻¹ * Matrix.transpose (ε.map σ) * G) := by rw [h]
      _ = Matrix.transpose (ε.map σ) * G := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  have hv : Matrix.mulVec ε (v : Fin n → F) = (v : Fin n → F) := by
    obtain ⟨w, hw⟩ := v.2
    rw [← hw, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]
  rw [CFSG.ClassicalGroups.UnitaryFlag.gramForm_apply]
  change (fun a => σ ((v : Fin n → F) a)) ⬝ᵥ Matrix.mulVec G (Matrix.mulVec (1 - ε) y) = 0
  have h1 : Matrix.mulVec (1 - ε) y = y - Matrix.mulVec ε y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_sub]
  have h2 : Matrix.mulVec G (Matrix.mulVec ε y) =
      Matrix.mulVec (Matrix.transpose (ε.map σ)) (Matrix.mulVec G y) := by
    rw [Matrix.mulVec_mulVec, hadj, Matrix.mulVec_mulVec]
  rw [h2]
  have hsplit : (fun a => σ ((v : Fin n → F) a)) ⬝ᵥ
      (Matrix.mulVec G y - Matrix.mulVec (Matrix.transpose (ε.map σ)) (Matrix.mulVec G y)) =
      (fun a => σ ((v : Fin n → F) a)) ⬝ᵥ Matrix.mulVec G y -
        (fun a => σ ((v : Fin n → F) a)) ⬝ᵥ Matrix.mulVec (Matrix.transpose (ε.map σ))
            (Matrix.mulVec G y) := by
    simp [dotProduct, Finset.sum_sub_distrib, mul_sub]
  rw [hsplit]
  have h3 : Matrix.mulVec (ε.map σ) (fun a => σ ((v : Fin n → F) a)) = fun a => σ ((v : Fin n → F)
      a) := by
    funext a
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct]
    simp only [← map_mul, ← map_sum]
    rw [show (∑ j, ε a j * ((v : Fin n → F) j)) = (Matrix.mulVec ε (v : Fin n → F)) a from rfl, hv]
  have h4 : (fun a => σ ((v : Fin n → F) a)) ⬝ᵥ
      Matrix.mulVec (Matrix.transpose (ε.map σ)) (Matrix.mulVec G y) =
      (fun a => σ ((v : Fin n → F) a)) ⬝ᵥ Matrix.mulVec G y := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h3]
  rw [h4, sub_self]
private lemma fePSU_selfDual_blockHeldSUid_extend_form_orth {F : Type} [Field F] [Finite F] [CharP F
    2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ (v : LinearMap.range (Matrix.mulVecLin ε)) (y : Fin n → F),
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (↑v : Fin n → F)
          (Matrix.mulVec (1 - ε) y) = 0 := by
  exact fePSU_selfDual_blockHeldSUid_extend_form_orth_core S hε he hF

private lemma fePSU_selfDual_blockHeldSUid_extend_form_orth' {F : Type} [Field F] [Finite F] [CharP
    F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ (x : Fin n → F) (w : LinearMap.range (Matrix.mulVecLin ε)),
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (Matrix.mulVec (1 - ε) x)
          (↑w : Fin n → F) = 0 := by
  intro x w
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hadj : G * ε = Matrix.transpose (ε.map σ) * G := by
    have h := hε.2.2.2.1
    simp only [formAdj] at h
    calc G * ε = G * (G⁻¹ * Matrix.transpose (ε.map σ) * G) := by rw [h]
      _ = Matrix.transpose (ε.map σ) * G := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  have hw : Matrix.mulVec ε (w : Fin n → F) = (w : Fin n → F) := by
    obtain ⟨v, hv⟩ := w.2
    rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]
  rw [CFSG.ClassicalGroups.UnitaryFlag.gramForm_apply]
  change (fun a => σ ((Matrix.mulVec (1 - ε) x) a)) ⬝ᵥ Matrix.mulVec G (w : Fin n → F) = 0
  have h1 : Matrix.mulVec (1 - ε) x = x - Matrix.mulVec ε x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [h1]
  have hσsub : (fun a => σ ((x - Matrix.mulVec ε x) a)) =
      (fun a => σ (x a)) - (fun a => σ ((Matrix.mulVec ε x) a)) := by
    funext a
    simp [Pi.sub_apply, map_sub]
  rw [hσsub]
  have hεσ : (fun a => σ ((Matrix.mulVec ε x) a)) =
      Matrix.mulVec (ε.map σ) (fun a => σ (x a)) := by
    funext a
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, map_sum, map_mul]
  rw [hεσ]
  have hsub : ((fun a => σ (x a)) - Matrix.mulVec (ε.map σ) (fun a => σ (x a))) ⬝ᵥ
      Matrix.mulVec G (w : Fin n → F) =
      (fun a => σ (x a)) ⬝ᵥ Matrix.mulVec G (w : Fin n → F) -
        Matrix.mulVec (ε.map σ) (fun a => σ (x a)) ⬝ᵥ Matrix.mulVec G (w : Fin n → F) := by
    simp [dotProduct, Finset.sum_sub_distrib, sub_mul]
  rw [hsub]
  have hsym : ∀ (A : Matrix (Fin n) (Fin n) F) (u z : Fin n → F),
      (Matrix.mulVec A u) ⬝ᵥ z = u ⬝ᵥ Matrix.mulVec (Matrix.transpose A) z := by
    intro A u z
    rw [← Matrix.vecMul_transpose A u, Matrix.dotProduct_mulVec]
  have hstar : Matrix.mulVec (Matrix.transpose (ε.map σ)) (Matrix.mulVec G (w : Fin n → F)) =
      Matrix.mulVec G (w : Fin n → F) := by
    rw [Matrix.mulVec_mulVec, ← hadj, ← Matrix.mulVec_mulVec, hw]
  have h4 : Matrix.mulVec (ε.map σ) (fun a => σ (x a)) ⬝ᵥ Matrix.mulVec G (w : Fin n → F) =
      (fun a => σ (x a)) ⬝ᵥ Matrix.mulVec G (w : Fin n → F) := by
    rw [hsym (ε.map σ) (fun a => σ (x a)) (Matrix.mulVec G (w : Fin n → F)), hstar]
  rw [h4, sub_self]

private lemma fePSU_selfDual_blockHeldSUid_extend_blockF_eq_gramForm {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :

    ∀ v w : (LinearMap.range (Matrix.mulVecLin ε)),
      fePSU_selfDual_blockFormF (f := f) ε v w = CFSG.ClassicalGroups.UnitaryFlag.gramForm hF
          (Unitary.antidiag n) (↑v : Fin n → F) (↑w : Fin n → F) := by
  intro v w
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let B₀ : (Fin n → F) →ₛₗ[σ] (Fin n → F) →ₗ[F] F :=
    Matrix.toLinearMapₛₗ₂ σ (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n)) G
  change B₀ (↑v) (↑w) = CFSG.ClassicalGroups.UnitaryFlag.gramForm hF G (↑v) (↑w)
  have hB : B₀ (↑v) (↑w) = ∑ i, σ ((↑v : Fin n → F) i) * (Matrix.mulVec G (↑w)) i := by
    simp only [B₀, Matrix.toLinearMapₛₗ₂_apply, Pi.basisFun_repr, smul_eq_mul,
      Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hG' : CFSG.ClassicalGroups.UnitaryFlag.gramForm hF G (↑v) (↑w) =
      ∑ i, σ ((↑v : Fin n → F) i) * (Matrix.mulVec G (↑w)) i := by
    rw [CFSG.ClassicalGroups.UnitaryFlag.gramForm_apply]
    simp only [dotProduct]
    rfl
  rw [hB, hG']

private lemma fePSU_selfDual_blockHeldSUid_extend_form_trace {F : Type} [Field F] [Finite F] [CharP
    F 2] {f n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ v w : (LinearMap.range (Matrix.mulVecLin ε)),
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (↑v : Fin n → F) (↑w : Fin n
          → F) = Algebra.trace F K (B v w) := by
  intro v w
  rw [hBt v w]
  exact (fePSU_selfDual_blockHeldSUid_extend_blockF_eq_gramForm hF v w).symm

private lemma fePSU_selfDual_blockHeldSUid_extend_form_gpres {F : Type} [Field F] [Finite F] [CharP
    F 2] {f n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ v w : (LinearMap.range (Matrix.mulVecLin ε)),
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (↑((g : (LinearMap.range
          (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) v) : Fin n → F) (↑((g
              : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
                  w) : Fin n → F) =
        CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (↑v : Fin n → F) (↑w : Fin
            n → F) := by
  intro v w
  rw [fePSU_selfDual_blockHeldSUid_extend_form_trace d K B hBt hF ((g : (LinearMap.range
      (Matrix.mulVecLin ε)) →ₗ[K]
          (LinearMap.range (Matrix.mulVecLin ε))) v) ((g : (LinearMap.range (Matrix.mulVecLin ε))
              →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w),
                  fePSU_selfDual_blockHeldSUid_extend_form_trace d K B hBt hF v w]
  exact congrArg (Algebra.trace F K) ((CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup.mp
      hg.1) v w)

private lemma fePSU_selfDual_blockHeldSUid_extend_form_pres_blocks {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ x y : Fin n → F,
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) ((((g : (LinearMap.range
          (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) ⟨Matrix.mulVec ε x,
              LinearMap.mem_range.mpr ⟨x, by rw [Matrix.mulVecLin_apply]⟩⟩) : Fin n → F) +
                  Matrix.mulVec (1 - ε) x) ((((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
                      (LinearMap.range (Matrix.mulVecLin ε))) ⟨Matrix.mulVec ε y,
                          LinearMap.mem_range.mpr ⟨y, by rw [Matrix.mulVecLin_apply]⟩⟩) : Fin n → F)
                              + Matrix.mulVec (1 - ε) y) =
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) x y := by
  intro x y
  have hx : Matrix.mulVec ε x + Matrix.mulVec (1 - ε) x = x := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hy : Matrix.mulVec ε y + Matrix.mulVec (1 - ε) y = y := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  conv_rhs => rw [← hx, ← hy]
  simp only [map_add, LinearMap.add_apply]
  rw [
      fePSU_selfDual_blockHeldSUid_extend_form_orth S hε he hF ((g : (LinearMap.range
          (Matrix.mulVecLin ε))
          →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) ⟨Matrix.mulVec ε x, LinearMap.mem_range.mpr
          ⟨x, by rw [Matrix.mulVecLin_apply]⟩⟩) y,
      fePSU_selfDual_blockHeldSUid_extend_form_orth' S hε he hF x ((g : (LinearMap.range
          (Matrix.mulVecLin ε))
          →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) ⟨Matrix.mulVec ε y, LinearMap.mem_range.mpr
          ⟨y, by rw [Matrix.mulVecLin_apply]⟩⟩),
      fePSU_selfDual_blockHeldSUid_extend_form_gpres d K B hBt g hg hF ⟨Matrix.mulVec ε x,
          LinearMap.mem_range.mpr ⟨x,
          by rw [Matrix.mulVecLin_apply]⟩⟩ ⟨Matrix.mulVec ε y, LinearMap.mem_range.mpr ⟨y, by rw
          [Matrix.mulVecLin_apply]⟩⟩,
      fePSU_selfDual_blockHeldSUid_extend_form_orth S hε he hF ⟨Matrix.mulVec ε x,
          LinearMap.mem_range.mpr ⟨x,
          by rw [Matrix.mulVecLin_apply]⟩⟩ y,
      fePSU_selfDual_blockHeldSUid_extend_form_orth' S hε he hF x ⟨Matrix.mulVec ε y,
          LinearMap.mem_range.mpr
          ⟨y, by rw [Matrix.mulVecLin_apply]⟩⟩]

private lemma fePSU_selfDual_blockHeldSUid_extend_isometry_aux_form_core {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε))
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ x y : Fin n → F,
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (Matrix.mulVec (U : Matrix
          (Fin n) (Fin n) F) x) (Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) y) =
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) x y := by
  intro x y
  rw [fePSU_selfDual_blockHeldSUid_extend_form_decomp K g U hact hfix x,
    fePSU_selfDual_blockHeldSUid_extend_form_decomp K g U hact hfix y]
  exact fePSU_selfDual_blockHeldSUid_extend_form_pres_blocks S hε he d K B hBt g hg hF x y
private lemma fePSU_selfDual_blockHeldSUid_extend_isometry_aux_form {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε))
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) :
    ∀ x y : Fin n → F,
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) (Matrix.mulVec (U : Matrix
          (Fin n) (Fin n) F) x) (Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) y) =
      CFSG.ClassicalGroups.UnitaryFlag.gramForm hF (Unitary.antidiag n) x y := by
  exact fePSU_selfDual_blockHeldSUid_extend_isometry_aux_form_core S hε he d
      K B hBt g hg U hact hfix hF

private lemma fePSU_selfDual_blockHeldSUid_extend_isometry_aux_pres {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (U :
        Matrix (Fin n) (Fin n) F) * CFSG.LieType.Universal.Unitary.antidiag n * (U : Matrix (Fin n)
            (Fin n) F) = CFSG.LieType.Universal.Unitary.antidiag n := by
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, fePSU_f_pos hc, by rw [hc, ← pow_mul]; congr 1; ring⟩
  exact (CFSG.ClassicalGroups.UnitaryFlag.gramForm_isometry_iff hF (Unitary.antidiag n) (U : Matrix
      (Fin n) (Fin n) F)).mp
    (fePSU_selfDual_blockHeldSUid_extend_isometry_aux_form S hε he d K B hBt g hg U hact hfix hF)
private lemma fePSU_selfDual_blockHeldSUid_extend_isometry_aux {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (U :
        Matrix (Fin n) (Fin n) F) * CFSG.LieType.Universal.Unitary.antidiag n * (U : Matrix (Fin n)
            (Fin n) F) = CFSG.LieType.Universal.Unitary.antidiag n := by
  exact fePSU_selfDual_blockHeldSUid_extend_isometry_aux_pres hc S hε he d K B hBt g hg U hact hfix
private lemma fePSU_selfDual_blockHeldSUid_extend_isometry {F : Type} [Field F] [Finite F] [CharP F
    2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (U :
        Matrix (Fin n) (Fin n) F) * CFSG.LieType.Universal.Unitary.antidiag n * (U : Matrix (Fin n)
            (Fin n) F) = CFSG.LieType.Universal.Unitary.antidiag n := by
  exact fePSU_selfDual_blockHeldSUid_extend_isometry_aux hc S hε he d K B hBt g hg U hact hfix

private lemma fePSU_selfDual_blockHeldSUid_extend_unitary {F : Type} [Field F] [Finite F] [CharP F
    2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    U ∈ Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n := by
  rw [CFSG.LieType.Universal.Unitary.mem_SU]
  exact ⟨fePSU_selfDual_blockHeldSUid_extend_det d K B g hg U hact hfix,
    fePSU_selfDual_blockHeldSUid_extend_isometry hc S hε he d K B hBt g hg U hact hfix⟩

private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_eps_commute {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε) :

    ∀ s ∈ S, (s : Matrix (Fin n) (Fin n) F) * ε = ε * (s : Matrix (Fin n) (Fin n) F) := by
  intro s hs
  have hsA : (s : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hpairA : (Units.val '' S : Set (Matrix (Fin n) (Fin n) F)).Pairwise Commute := by
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ _
    exact (hS s₁ hs₁ s₂ hs₂).map (Units.coeHom (Matrix (Fin n) (Fin n) F))
  letI : CommRing (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpairA
  exact congrArg Subtype.val (mul_comm (⟨(s : Matrix (Fin n) (Fin n) F), hsA⟩ :
    Algebra.adjoin F (Units.val '' S)) (⟨ε, hε.1⟩ : Algebra.adjoin F (Units.val '' S)))

private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_eps_apply {F : Type} [Field F] {n : ℕ}
    (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε) :

    ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec ε (w : Fin n → F) = (w : Fin n → F)
        := by
  intro w
  obtain ⟨x, hx⟩ := w.2
  rw [← hx, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]

private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_smul_mem {F : Type} [Field F] [Finite
    F] [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε) :

    ∀ s ∈ S, ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec (s : Matrix (Fin n) (Fin n)
        F) (w : Fin n → F) ∈ (LinearMap.range (Matrix.mulVecLin ε)) := by
  intro s hs w
  refine ⟨Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (w : Fin n → F), ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ←
      fePSU_selfDual_blockHeldSUid_extend_centralizer_eps_commute S hS hε s hs,
    ← Matrix.mulVec_mulVec, fePSU_selfDual_blockHeldSUid_extend_centralizer_eps_apply S he w]

private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_g_smul {F : Type} [Field F] {n : ℕ} (S
    : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :

    ∀ s ∈ S, ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), ∀ (h : Matrix.mulVec (s : Matrix (Fin n)
        (Fin n) F) (w : Fin n → F) ∈ (LinearMap.range (Matrix.mulVecLin ε))),
      (((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
          ⟨Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (w : Fin n → F), h⟩ : Fin n → F)) =
        Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (((g : (LinearMap.range (Matrix.mulVecLin ε))
            →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) := by
  intro s hs w h
  have hA : (s : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hπw : ((π ⟨s, hA⟩ • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) =
      Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (w : Fin n → F) := hactπ ⟨s, hA⟩ w
  have hπgw : ((π ⟨s, hA⟩ • ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) w) : (LinearMap.range (Matrix.mulVecLin ε))) :
      Fin n → F) = Matrix.mulVec (s : Matrix (Fin n) (Fin n) F)
        ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
          (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F) :=
    hactπ ⟨s, hA⟩ ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
      (LinearMap.range (Matrix.mulVecLin ε))) w)
  have harg : (⟨Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (w : Fin n → F), h⟩ :
      (LinearMap.range (Matrix.mulVecLin ε))) = π ⟨s, hA⟩ • w := by
    apply Subtype.ext
    rw [hπw]
  rw [harg, map_smul, hπgw]

private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_onW {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :

    ∀ s ∈ S, ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (w
          : Fin n → F)) =
        Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (Matrix.mulVec (U : Matrix (Fin n) (Fin n) F)
            (w : Fin n → F)) := by
  intro s hs w
  let wS : (LinearMap.range (Matrix.mulVecLin ε)) := ⟨Matrix.mulVec (s : Matrix (Fin n) (Fin n) F)
      (w : Fin n → F), fePSU_selfDual_blockHeldSUid_extend_centralizer_smul_mem S hS hε
          he s hs w⟩
  have h1 := hact wS
  have h2 := hact w
  have h3 := fePSU_selfDual_blockHeldSUid_extend_centralizer_g_smul S
      K g π hactπ s hs w wS.2
  rw [h1, h3, h2]

private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_onE {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (U : GL (Fin n) F)
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    ∀ s ∈ S, ∀ v : Fin n → F, Matrix.mulVec (1 - ε) v = v →
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) v)
          =
        Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) (Matrix.mulVec (U : Matrix (Fin n) (Fin n) F)
            v) := by
  intro s hs v hv
  have hUv : Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) v = v := by
    rw [← hv, Matrix.mulVec_mulVec, hfix]
  have hcomm : (s : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε) * (s : Matrix (Fin n) (Fin n) F)
      := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      fePSU_selfDual_blockHeldSUid_extend_centralizer_eps_commute S hS hε s hs]
  have hsv : Matrix.mulVec (1 - ε) (Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) v) =
      Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) v := by
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hv]
  have hUsv : Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (Matrix.mulVec (s : Matrix (Fin n) (Fin
      n) F) v) =
      Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) v := by
    rw [← hsv, Matrix.mulVec_mulVec, hfix]
  rw [hUsv, hUv]

private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_matrix_core {F : Type} [Field F]
    [Finite F] [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε))
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
    ∀ s ∈ S, (U : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F) = (s : Matrix (Fin n)
        (Fin n) F) * (U : Matrix (Fin n) (Fin n) F) := by
  intro s hs
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change Matrix.mulVec ((U : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F)) x =
    Matrix.mulVec ((s : Matrix (Fin n) (Fin n) F) * (U : Matrix (Fin n) (Fin n) F)) x
  have hx : x = Matrix.mulVec ε x + Matrix.mulVec (1 - ε) x := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hE : Matrix.mulVec (1 - ε) (Matrix.mulVec (1 - ε) x) = Matrix.mulVec (1 - ε) x := by
    rw [Matrix.mulVec_mulVec, sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      he.2.1.eq, sub_self, sub_zero]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx]
  simp only [Matrix.mulVec_add]
  rw [fePSU_selfDual_blockHeldSUid_extend_centralizer_onW S hS hε he K g U hact π hactπ s hs
      ⟨Matrix.mulVec ε x,
          LinearMap.mem_range.mpr ⟨x, rfl⟩⟩,
      fePSU_selfDual_blockHeldSUid_extend_centralizer_onE S hS hε U hfix s hs (Matrix.mulVec (1 - ε)
          x) hE]
private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer_matrix {F : Type} [Field F] [Finite F]
    [CharP F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε))
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
    ∀ s ∈ S, (U : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F) = (s : Matrix (Fin n)
        (Fin n) F) * (U : Matrix (Fin n) (Fin n) F) := by
  intro s hs
  exact fePSU_selfDual_blockHeldSUid_extend_centralizer_matrix_core S hS hε he
      K g U hact hfix π hactπ s hs


private lemma fePSU_selfDual_blockHeldSUid_extend_centralizer {F : Type} [Field F] [Finite F] [CharP
    F 2] {f n : ℕ} (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (U : GL (Fin n) F)
    (hact : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F))
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε))
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
    U ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  show s * U = U * s
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (fePSU_selfDual_blockHeldSUid_extend_centralizer_matrix S hS hε he K g U hact hfix π hactπ s
      hs).symm

private lemma fePSU_selfDual_blockHeldSUid_extend_fixing {F : Type} [Field F]
    {n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (U : GL (Fin n) F)
    (hfix : (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε)) :
    U ∈ glFixing (1 - ε) := by
  exact hfix

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr_left {F : Type} [Field F] {n : ℕ} (S : Set
    (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
∃ N : Matrix (Fin n) (Fin n) F,
      N * ε = N ∧
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
          LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
              (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :=
                  by
  obtain ⟨N, hN, hNv⟩ :=
    fePSU_dualPair_GepsGLK_extension_left S he
      (LinearMap.GeneralLinearGroup.toLinearEquiv g)
  refine ⟨N, hN, ?_⟩
  intro w
  simpa only [LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using hNv w

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_inv {F : Type} [Field F] {n : ℕ} (S
    : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N : Matrix (Fin n) (Fin n) F) (hN : N * ε = N)
    (hNv : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :
∃ N' : Matrix (Fin n) (Fin n) F,
      N' * ε = N' ∧
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹ :
          LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
              (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) ∧
      N' * N = ε := by
  obtain ⟨N', hN', hN'v, hcomp⟩ :=
    fePSU_dualPair_GepsGLK_extension_right S he
      (LinearMap.GeneralLinearGroup.toLinearEquiv g) hN (by
        intro w
        simpa only [LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using hNv w)
  refine ⟨N', hN', ?_, hcomp⟩
  intro w
  have hsymm : (LinearMap.GeneralLinearGroup.toLinearEquiv g).symm =
      LinearMap.GeneralLinearGroup.toLinearEquiv (g⁻¹) := by
    ext x
    rfl
  rw [hN'v w, hsymm, LinearMap.GeneralLinearGroup.coe_toLinearEquiv]

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul_W {F : Type} [Field F] {n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N : Matrix (Fin n) (Fin n) F)
    (hNv : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
    (N' : Matrix (Fin n) (Fin n) F)
    (hN'v : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹
        : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :
∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec (N * N') (w : Fin n → F) = (w : Fin n →
    F) := by
  intro w
  have hsymm : (LinearMap.GeneralLinearGroup.toLinearEquiv g).symm =
      LinearMap.GeneralLinearGroup.toLinearEquiv (g⁻¹) := by
    ext x
    rfl
  rw [← Matrix.mulVec_mulVec, hN'v w,
    hNv (((g⁻¹ : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
      LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] LinearMap.range (Matrix.mulVecLin ε)) w)]
  have h : (((g⁻¹ : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
        LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] LinearMap.range (Matrix.mulVecLin ε)) w) =
      (LinearMap.GeneralLinearGroup.toLinearEquiv g).symm w := by
    rw [← LinearMap.GeneralLinearGroup.coe_toLinearEquiv (g⁻¹), ← hsymm]
  rw [h, ← LinearMap.GeneralLinearGroup.coe_toLinearEquiv g]
  exact congrArg Subtype.val ((LinearMap.GeneralLinearGroup.toLinearEquiv g).apply_symm_apply w)

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul_E {F : Type} [Field F] {n : ℕ}
    {ε : Matrix (Fin n) (Fin n) F}
    (N : Matrix (Fin n) (Fin n) F)
    (N' : Matrix (Fin n) (Fin n) F) (hN' : N' * ε = N') :
∀ x : Fin n → F, Matrix.mulVec (N * N') (Matrix.mulVec (1 - ε) x) = 0 := by
  intro x
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hN', sub_self,
    Matrix.mul_zero, Matrix.zero_mulVec]

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul_Eeps {F : Type} [Field F] {n :
    ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε) :
∀ x : Fin n → F, Matrix.mulVec ε (Matrix.mulVec (1 - ε) x) = 0 := by
  intro x
  rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, he.2.1.eq, sub_self,
    Matrix.zero_mulVec]

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul {F : Type} [Field F] {n : ℕ} (S
    : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N : Matrix (Fin n) (Fin n) F)
    (hNv : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
    (N' : Matrix (Fin n) (Fin n) F) (hN' : N' * ε = N')
    (hN'v : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹
        : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :
    N * N' = ε := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change Matrix.mulVec (N * N') x = Matrix.mulVec ε x
  have hx : x = Matrix.mulVec ε x + Matrix.mulVec (1 - ε) x := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  rw [hx, Matrix.mulVec_add, Matrix.mulVec_add]
  rw [fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul_W K g N hNv N' hN'v ⟨Matrix.mulVec ε x,
          LinearMap.mem_range.mpr ⟨x, rfl⟩⟩,
    fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul_E N N' hN' x,
            fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul_Eeps S he x]
  rw [Matrix.mulVec_mulVec, he.2.1.eq, add_zero]

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr_right {F : Type} [Field F] {n : ℕ} (S :
    Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N : Matrix (Fin n) (Fin n) F) (hN : N * ε = N)
    (hNv : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :

    ∃ N' : Matrix (Fin n) (Fin n) F,
      N' * ε = N' ∧
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹ :
          LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
              (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) ∧
      N' * N = ε ∧ N * N' = ε := by
  obtain ⟨N', hN', hN'v, hcomp⟩ := fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_inv S he K g N
      hN hNv
  exact ⟨N', hN', hN'v, hcomp, fePSU_selfDual_blockHeldSUid_extend_GL_repr_right_mul S he K g N hNv
      N' hN' hN'v⟩

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_repr {F : Type} [Field F] {n : ℕ} (S : Set (GL
    (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
∃ N N' : Matrix (Fin n) (Fin n) F,
      N * ε = N ∧ N' * ε = N' ∧ N' * N = ε ∧ N * N' = ε ∧
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
          LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
              (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) ∧
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹ :
          LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
              (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :=
                  by
  obtain ⟨N, hN, hNv⟩ := fePSU_selfDual_blockHeldSUid_extend_GL_repr_left S he K g
  obtain ⟨N', hN', hN'v, hcomp, hcomp'⟩ := fePSU_selfDual_blockHeldSUid_extend_GL_repr_right S he K
      g N hN hNv
  exact ⟨N, N', hN, hN', hcomp, hcomp', hNv, hN'v⟩

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_unit_idem {F : Type} [Field F] {n : ℕ} (S : Set
    (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N N' : Matrix (Fin n) (Fin n) F)
    (hN : N * ε = N) (hN' : N' * ε = N')
    (hvN : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
    (hvN' : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹
        : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :
ε * N = N ∧ ε * N' = N' := by
  have hdec : ∀ x : Fin n → F, x = Matrix.mulVec ε x + Matrix.mulVec (1 - ε) x := by
    intro x
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hNW : ∀ x : Fin n → F, Matrix.mulVec N x ∈ (LinearMap.range (Matrix.mulVecLin ε)) := by
    intro x
    rw [hdec x, Matrix.mulVec_add,
      show Matrix.mulVec N (Matrix.mulVec (1 - ε) x) = 0 from by
        rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hN, sub_self, Matrix.zero_mulVec],
      add_zero]
    rw [hvN ⟨Matrix.mulVec ε x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩]
    exact ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
        ⟨Matrix.mulVec ε x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩).2
  have hN'W : ∀ x : Fin n → F, Matrix.mulVec N' x ∈ (LinearMap.range (Matrix.mulVecLin ε)) := by
    intro x
    rw [hdec x, Matrix.mulVec_add,
      show Matrix.mulVec N' (Matrix.mulVec (1 - ε) x) = 0 from by
        rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hN', sub_self,
            Matrix.zero_mulVec],
      add_zero]
    rw [hvN' ⟨Matrix.mulVec ε x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩]
    exact (((g⁻¹ : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
            ⟨Matrix.mulVec ε x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩).2
  have hfixW : ∀ x : Fin n → F, Matrix.mulVec ε (Matrix.mulVec N x) = Matrix.mulVec N x := by
    intro x
    obtain ⟨v, hv⟩ := hNW x
    rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]
  have hfixW' : ∀ x : Fin n → F, Matrix.mulVec ε (Matrix.mulVec N' x) = Matrix.mulVec N' x := by
    intro x
    obtain ⟨v, hv⟩ := hN'W x
    rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1.eq]
  constructor
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change Matrix.mulVec (ε * N) x = Matrix.mulVec N x
    rw [← Matrix.mulVec_mulVec]
    exact hfixW x
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change Matrix.mulVec (ε * N') x = Matrix.mulVec N' x
    rw [← Matrix.mulVec_mulVec]
    exact hfixW' x

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_unit_inv {F : Type} [Field F] {n : ℕ} (S : Set
    (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N N' : Matrix (Fin n) (Fin n) F)
    (hN : N * ε = N) (hN' : N' * ε = N') (hcomp : N' * N = ε) (hcomp' : N * N' = ε)
    (hvN : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
    (hvN' : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹
        : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :
(N + (1 - ε)) * (N' + (1 - ε)) = 1 ∧ (N' + (1 - ε)) * (N + (1 - ε)) = 1 := by
  have hεε : ε * ε = ε := he.2.1.eq
  have hidem := fePSU_selfDual_blockHeldSUid_extend_GL_unit_idem S he K g N N' hN hN' hvN hvN'
  have hεN : ε * N = N := hidem.1
  have hεN' : ε * N' = N' := hidem.2
  have hNε0 : N * (1 - ε) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hN, sub_self]
  have hN'0 : N' * (1 - ε) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hN', sub_self]
  have hεN0 : (1 - ε) * N = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hεN, sub_self]
  have hεN'0 : (1 - ε) * N' = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hεN', sub_self]
  have h1m : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hεε, sub_self, sub_zero]
  constructor
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hcomp', hNε0, hεN'0, h1m,
      add_zero, zero_add, add_sub_cancel]
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hcomp, hN'0, hεN0, h1m,
      add_zero, zero_add, add_sub_cancel]

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_unit_act {F : Type} [Field F] {n : ℕ} (S : Set
    (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N : Matrix (Fin n) (Fin n) F)
    (hvN : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :
∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec (N + (1 - ε)) (w : Fin n → F) = (((g :
    LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
        (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F) := by
  intro w
  obtain ⟨v, hv⟩ := w.2
  have hz : Matrix.mulVec (1 - ε) (w : Fin n → F) = 0 := by
    rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul,
      he.2.1.eq, sub_self, Matrix.zero_mulVec]
  rw [Matrix.add_mulVec, hvN w, hz, add_zero]

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_unit_fix {F : Type} [Field F] {n : ℕ} (S : Set
    (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (N : Matrix (Fin n) (Fin n) F)
    (hN : N * ε = N) :
(N + (1 - ε)) * (1 - ε) = (1 - ε) := by
  have hNε0 : N * (1 - ε) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hN, sub_self]
  have h1m : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, he.2.1.eq, sub_self,
        sub_zero]
  rw [Matrix.add_mul, hNε0, h1m, zero_add]

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_unit {F : Type} [Field F] {n : ℕ} (S : Set (GL
    (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (N N' : Matrix (Fin n) (Fin n) F)
    (hN : N * ε = N) (hN' : N' * ε = N') (hcomp : N' * N = ε) (hcomp' : N * N' = ε)
    (hvN : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N (w : Fin n → F) = (((g :
        LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
    (hvN' : ∀ w : (LinearMap.range (Matrix.mulVecLin ε)), Matrix.mulVec N' (w : Fin n → F) = (((g⁻¹
        : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :
    ∃ U : GL (Fin n) F,
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) = (((g :
            LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
                (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
                    w : Fin n → F)) ∧
      (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε) := by
  obtain ⟨hUU', hU'U⟩ := fePSU_selfDual_blockHeldSUid_extend_GL_unit_inv S he K g N N' hN hN' hcomp
      hcomp' hvN hvN'
  exact ⟨⟨N + (1 - ε), N' + (1 - ε), hUU', hU'U⟩,
    fePSU_selfDual_blockHeldSUid_extend_GL_unit_act S he K g N hvN,
            fePSU_selfDual_blockHeldSUid_extend_GL_unit_fix S he N hN⟩

private lemma fePSU_selfDual_blockHeldSUid_extend_GL_exists {F : Type} [Field F] {n : ℕ} (S : Set
    (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
∃ U : GL (Fin n) F,
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) = (((g :
            LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
                (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
                    w : Fin n → F)) ∧
      (U : Matrix (Fin n) (Fin n) F) * (1 - ε) = (1 - ε) := by
  obtain ⟨N, N', hN, hN', hcomp, hcomp', hvN, hvN'⟩ := fePSU_selfDual_blockHeldSUid_extend_GL_repr S
      he K g
  exact fePSU_selfDual_blockHeldSUid_extend_GL_unit S he K g N N' hN hN' hcomp hcomp' hvN hvN'

private lemma fePSU_selfDual_blockHeldSUid_extend_GL {F : Type} [Field F] [Finite F] [CharP F 2] {f
    n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
    ∃ U : GL (Fin n) F,
      (U ∈ Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) ∧
      (U ∈ Subgroup.centralizer S) ∧
      (U ∈ glFixing (1 - ε)) ∧
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) = ((g : (LinearMap.range
            (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F)) :=
                by
  obtain ⟨U, hact, hfix⟩ :=
    fePSU_selfDual_blockHeldSUid_extend_GL_exists S he K g
  exact ⟨U,
    fePSU_selfDual_blockHeldSUid_extend_unitary hc S hε he d K B hBt g hg U hact hfix,
    fePSU_selfDual_blockHeldSUid_extend_centralizer S hS hε he K g U hact hfix π hactπ,
    fePSU_selfDual_blockHeldSUid_extend_fixing U hfix,
    hact⟩

private lemma fePSU_selfDual_blockHeldSUid_extend_U {F : Type} [Field F] [Finite F] [CharP F 2] {f n
    : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)))
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B)
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
    ∃ U : GL (Fin n) F,
      (U ∈ Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) ∧
      (U ∈ Subgroup.centralizer S) ∧
      (U ∈ glFixing (1 - ε)) ∧
      (∀ w : (LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (U : Matrix (Fin n) (Fin n) F) (w : Fin n → F) =
          ((g : (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
              w : Fin n → F)) := by
  exact fePSU_selfDual_blockHeldSUid_extend_GL hc S hS hε he d K B hBt g hg π hactπ

private lemma fePSU_selfDual_blockHeldSUid_extend {F : Type} [Field F] [Finite F] [CharP F 2] {f n :
    ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε))))
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hactm : ∀ u w, (((act u : Module.End K (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
        = Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
∀ g : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)),
      g ∈ CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B → ∃ u : glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε, act u = g :=
              by
  intro g hg
  obtain ⟨U, hSU, hcen, hfix, hactW⟩ :=
    fePSU_selfDual_blockHeldSUid_extend_U hc S hS hε he d K B hBt g hg π hactπ
  refine ⟨⟨⟨U, hSU⟩, Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨hcen, hfix⟩)⟩, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  rw [hactm]
  exact hactW w

private lemma fePSU_selfDual_blockHeldSUid_surj_SU_le {F : Type} [Field F] [Finite F] [CharP F 2] {f
    n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε))))
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hactm : ∀ u w, (((act u : Module.End K (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
        = Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B ≤ act.range := by
  intro g hg
  obtain ⟨u, hu⟩ := fePSU_selfDual_blockHeldSUid_extend hc S hS hε he d K
      act B hactm hBt π hactπ g hg
  rw [MonoidHom.range_eq_map]
  exact ⟨u, Subgroup.mem_top u, hu⟩


private lemma fePSU_selfDual_blockHeldSUid_surj {F : Type} [Field F] [Finite F] [CharP F 2] {f n :
    ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε))]
    [FiniteDimensional K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε))))
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hBs : B.IsSymm) (hBl : B.SeparatingLeft)
    (hdim : 2 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin ε)))
    (hactm : ∀ u w, (((act u : Module.End K (LinearMap.range (Matrix.mulVecLin ε))) w : Fin n → F))
        = Matrix.mulVec ((u.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w)
    (hBt : ∀ v w, Algebra.trace F K (B v w) = fePSU_selfDual_blockFormF (f := f) ε v w)
    (π : (Algebra.adjoin F (Units.val '' S)) →ₐ[F] K)
    (hactπ : ∀ (a : (Algebra.adjoin F (Units.val '' S))) (w : (LinearMap.range (Matrix.mulVecLin
        ε))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin ε))) : Fin n → F) = Matrix.mulVec (a : Matrix
          (Fin n) (Fin n) F) (w : Fin n → F)) :
CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B ≤
      (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))).range :=
              by
  have hperfect := fePSU_selfDual_blockHeldSUid_surj_perfect hc S d hd hdeg K
      hKcard B hBs hBl hdim
  have hSUle := fePSU_selfDual_blockHeldSUid_surj_SU_le hc S hS hε he d K
      act B hactm hBt π hactπ
  have hcomm := fePSU_selfDual_blockHeldSUid_surj_commutator S K act
  intro x hx
  have hx' : x ∈ ⁅CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B,
      CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B⁆ := by
    rw [hperfect]
    exact hx
  have hle : ⁅CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B,
      CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B⁆ ≤
      ⁅act.range, act.range⁆ := Subgroup.commutator_mono hSUle hSUle
  have hx'' : x ∈ ⁅act.range, act.range⁆ := hle hx'
  rw [hcomm]
  exact hx''


private lemma fePSU_selfDual_blockHeldSUid_held {F : Type} [Field F] [Finite F] [CharP F 2] {f n :
    ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (act : glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε →*
        LinearMap.GeneralLinearGroup K ((LinearMap.range (Matrix.mulVecLin ε))))
    (B : (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom]
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] K)
    (hunit : ∀ u, act u ∈ CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B)
    (hsurj : CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B ≤
      (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)))).range)
    (hact : Function.Injective (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε))))) :
    Nonempty (↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≃*
        CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) := by
  let G : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) :=
    glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε
  let D : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) := ⁅G, G⁆
  let φ : ↥D →* LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε)) :=
    act.comp (Subgroup.inclusion (Subgroup.commutator_le_self G))
  let ψ : ↥G →* Kˣ :=
    (Units.map (LinearMap.det :
      ((LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin ε))) →* K)).comp act
  have hle : D ≤ (MonoidHom.ker ψ).map (Subgroup.subtype G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⟨⁅a, b⁆, Subgroup.commutator_le_self G (Subgroup.commutator_mem_commutator ha hb)⟩, ?_,
        rfl⟩
    change ψ ⟨⁅a, b⁆, Subgroup.commutator_le_self G (Subgroup.commutator_mem_commutator ha hb)⟩ = 1
    have heq : (⟨⁅a, b⁆, Subgroup.commutator_le_self G (Subgroup.commutator_mem_commutator ha hb)⟩ :
        ↥G) = ⁅(⟨a, ha⟩ : ↥G), (⟨b, hb⟩ : ↥G)⁆ := Subtype.ext rfl
    rw [heq, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hdet : ∀ u : ↥D,
      LinearMap.det ((φ u : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
        (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) = 1 :=
            by
    intro u
    obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.mp (hle u.2)
    have hincl : Subgroup.inclusion (Subgroup.commutator_le_self G) u = k :=
      Subtype.ext hkval.symm
    have hφ : φ u = act k := congrArg act hincl
    have hk1 : ψ k = 1 := hk
    rw [show ((φ u : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
          (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε))) =
        ((act k : LinearMap.GeneralLinearGroup K (LinearMap.range (Matrix.mulVecLin ε))) :
          (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))
        from congrArg (fun z => ((z : LinearMap.GeneralLinearGroup K
          (LinearMap.range (Matrix.mulVecLin ε))) :
          (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[K] (LinearMap.range (Matrix.mulVecLin ε)))) hφ]
    exact congrArg (fun z : Kˣ => (z : K)) hk1
  let φSU : ↥D →* CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B :=
    { toFun := fun u => ⟨φ u, CFSG.LocalAnalysis.ComponentInitial.mem_sesqSpecialUnitaryGroup.mpr
        ⟨hunit (Subgroup.inclusion (Subgroup.commutator_le_self G) u), hdet u⟩⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b) }
  refine ⟨MulEquiv.ofBijective φSU ⟨?_, ?_⟩⟩
  · intro a b hab
    exact hact (congrArg Subtype.val hab)
  · intro s
    have hs : s.1 ∈ (act.comp (Subgroup.inclusion (Subgroup.commutator_le_self G))).range :=
      hsurj s.2
    obtain ⟨u, _, hu⟩ := Subgroup.mem_map.mp (by
      rwa [MonoidHom.range_eq_map] at hs)
    exact ⟨u, Subtype.ext hu⟩

private lemma fePSU_selfDual_blockHeldSUid_model {K : Type} [Field K] [Finite K] [CharP K 2]
    {f d : ℕ} {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₛₗ[(CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)).toRingHom] V →ₗ[K] K)
    (hBs : B.IsSymm) (hBl : B.SeparatingLeft) (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) :
    Nonempty (CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B ≃*
      CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d))
        (Module.finrank K V)) := by
  have hcard2 : 2 ≤ Nat.card K := by
    letI : Fintype K := Fintype.ofFinite K
    haveI : Nontrivial K := inferInstance
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hfd : 1 ≤ f * d := by
    rcases Nat.eq_zero_or_pos (f * d) with h0 | hpos
    · exfalso
      rcases Nat.mul_eq_zero.mp h0 with hf | hd
      · rw [hf] at hKcard; norm_num at hKcard; omega
      · rw [hd] at hKcard; norm_num at hKcard; omega
    · exact hpos
  have hge2 : 2 ≤ 2 ^ (f*d) := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2 ^ (f*d) := Nat.pow_le_pow_right (by norm_num) hfd
  have hcard' : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
  haveI hKK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f * d) K :=
    ⟨Nat.prime_two, hfd, by rw [hKcard, ← pow_mul, ← pow_mul]; congr 1; ring⟩
  have hσ2 : CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) ^ 2 = 1 := by
    ext x
    change CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) x) = x
    exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hcard' x
  have hσ1 : CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) ≠ 1 := by
    intro h
    have hfix : ∀ x : K, x ≠ 0 → x ^ (2 ^ (f*d) - 1) = 1 := by
      intro x hx
      have hxpow : x ^ (2 ^ (f*d)) = x := by
        have hc := congrArg (fun e : K ≃+* K => e x) h
        rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hc
        exact hc
      have hh := hxpow
      rw [show 2 ^ (f*d) = (2 ^ (f*d) - 1) + 1 by omega, pow_succ] at hh
      have h' : x ^ (2 ^ (f*d) - 1) * x = 1 * x := by rw [hh, one_mul]
      exact mul_right_cancel₀ hx h'
    let p : Polynomial K := Polynomial.X ^ (2 ^ (f*d) - 1) - Polynomial.C 1
    have hpdeg : p.natDegree = 2 ^ (f*d) - 1 := Polynomial.natDegree_X_pow_sub_C
    have hpne : p ≠ 0 := by
      intro hp
      have h0 : p.natDegree = 0 := by rw [hp]; exact Polynomial.natDegree_zero
      rw [hpdeg] at h0
      omega
    have heval : ∀ u : Kˣ, Polynomial.eval (u : K) p = 0 := by
      intro u
      simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [hfix (u : K) (Units.ne_zero u)]
      ring
    have hinj : Function.Injective (fun u : Kˣ => (u : K)) := Units.val_injective
    letI : Fintype Kˣ := Fintype.ofFinite Kˣ
    have hbase : ((2 ^ f) ^ d) ^ 2 = 2 ^ (2*(f*d)) := by ring_nf
    have hcardu : Fintype.card Kˣ = 2 ^ (2*(f*d)) - 1 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_units, hKcard, hbase]
    have hlt : p.natDegree < Fintype.card Kˣ := by
      rw [hpdeg, hcardu]
      have h2 : 2 ^ (f*d) < 2 ^ (2*(f*d)) := by
        rw [show 2*(f*d) = (f*d)+(f*d) by ring, pow_add]
        have hpos : 0 < 2 ^ (f*d) := by positivity
        nlinarith [hge2, hpos]
      omega
    exact hpne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hinj heval hlt)
  have hnd : B.Nondegenerate :=
    CFSG.ComponentClassification.CatalogueBUnitaryB.nondegenerate_of_isSymm hBs hBl
  obtain ⟨e, he⟩ :=
    CFSG.ComponentClassification.CatalogueBHermitian.exists_orthonormal_basis
      (sigma := CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) B hBs hnd hσ2 hσ1
  let Ψ := Matrix.GeneralLinearGroup.toLin' e
  have hiff := CFSG.LocalAnalysis.ComponentInitial.toLin'_mem_sesqSpecialUnitaryGroup_iff hKK e he
  have hEq : (CFSG.LieType.Universal.Unitary.SUid hKK.barEquiv (Module.finrank K V)).map
      Ψ.toMonoidHom
      = CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B := by
    ext g
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (hiff M).2 hM
    · intro hg
      refine ⟨Ψ.symm g, (hiff (Ψ.symm g)).1 ?_, ?_⟩
      · change Ψ (Ψ.symm g) ∈ _
        rwa [MulEquiv.apply_symm_apply]
      · exact Ψ.apply_symm_apply g
  exact ⟨(Subgroup.equivMapOfInjective
    (CFSG.LieType.Universal.Unitary.SUid hKK.barEquiv (Module.finrank K V))
    Ψ.toMonoidHom Ψ.injective).trans (MulEquiv.subgroupCongr hEq) |>.symm⟩


private lemma fePSU_selfDual_blockHeldSUid_adjoint_descend {F : Type} [Field F] [Finite F] [CharP F
    2]
    {f n : ℕ} {S : Set (GL (Fin n) F)} (hc : Nat.card F = (2 ^ f) ^ 2)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    {K : Type} [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * ε = 0)
    (hadjmem : ∀ a : Algebra.adjoin F (Units.val '' S),
      formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
        (a : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S)) :
    ∃ τ : K ≃+* K,
      (∀ a : Algebra.adjoin F (Units.val '' S),
        τ (π a) = π ⟨formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
          (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) F), hadjmem a⟩) ∧
      (∀ x : K, τ (τ x) = x) := by
  let A : Subalgebra F (Matrix (Fin n) (Fin n) F) := Algebra.adjoin F (Units.val '' S)
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  have hfix : formAdj σ G ε = ε := hε.2.2.2.1
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  have hσ : ∀ x, σ (σ x) = x :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hGh : Matrix.transpose (G.map σ) = G := by
    show Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n
    rw [fePSU_antidiag_map σ n, fePSU_transpose_antidiag n]
  haveI hAcomm : IsMulCommutative A := by
    refine Algebra.isMulCommutative_adjoin F ?_
    intro x hx y hy _
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    simpa using hS s hs t ht
  let adjHom : A →+* A :=
  { toFun := fun a => ⟨formAdj σ G a.1, hadjmem a⟩
    map_one' := by apply Subtype.ext; exact Geo.formAdj_one σ hG
    map_zero' := by apply Subtype.ext; simp [formAdj]
    map_mul' := fun a b => by
      apply Subtype.ext
      change formAdj σ G ((a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F)) =
        formAdj σ G (a : Matrix (Fin n) (Fin n) F) * formAdj σ G (b : Matrix (Fin n) (Fin n) F)
      rw [Geo.formAdj_mul σ hG]
      exact (congrArg Subtype.val (mul_comm' (⟨formAdj σ G a.1, hadjmem a⟩ : A)
        (⟨formAdj σ G b.1, hadjmem b⟩ : A))).symm
    map_add' := fun a b => by
      apply Subtype.ext
      exact Geo.formAdj_add σ G a.1 b.1 }
  let πr : A →+* K := (π : A →+* K)
  have hπr : Function.Surjective πr := hπsurj
  let fr : A →+* K := πr.comp adjHom
  have hker : ∀ a ∈ RingHom.ker πr, fr a = 0 := by
    intro a ha
    change πr (adjHom a) = 0
    change πr a = 0 at ha
    have hae : (a : Matrix (Fin n) (Fin n) F) * ε = 0 := (hπker a).mp ha
    apply (hπker (adjHom a)).mpr
    have h1 : formAdj σ G ((a : Matrix (Fin n) (Fin n) F) * ε) = 0 := by
      rw [hae]; simp [formAdj]
    rw [Geo.formAdj_mul σ hG, hfix] at h1
    have hc' : formAdj σ G (a : Matrix (Fin n) (Fin n) F) * ε =
        ε * formAdj σ G (a : Matrix (Fin n) (Fin n) F) :=
      congrArg Subtype.val (mul_comm'
        (⟨formAdj σ G (a : Matrix (Fin n) (Fin n) F), hadjmem a⟩ : A) (⟨ε, hε.1⟩ : A))
    show formAdj σ G (a : Matrix (Fin n) (Fin n) F) * ε = 0
    rw [hc', h1]
  let eK : A ⧸ RingHom.ker πr ≃+* K :=
    RingHom.quotientKerEquivOfSurjective (f := πr) hπr
  let τhom : K →+* K :=
    (Ideal.Quotient.lift (RingHom.ker πr) fr hker).comp eK.symm.toRingHom
  have hτπ : ∀ a : A, τhom (πr a) = πr (adjHom a) := by
    intro a
    have heK : eK.symm (πr a) = Ideal.Quotient.mk (RingHom.ker πr) a := by
      rw [← RingHom.quotientKerEquivOfSurjective_apply_mk (f := πr) hπr a,
        RingEquiv.symm_apply_apply]
    change (Ideal.Quotient.lift (RingHom.ker πr) fr hker) (eK.symm (πr a)) = πr (adjHom a)
    rw [heK]
    exact Ideal.Quotient.lift_mk (RingHom.ker πr) fr hker
  have hττ : ∀ k, τhom (τhom k) = k := by
    intro k
    obtain ⟨a, ha⟩ := hπr k
    rw [← ha, hτπ a, hτπ (adjHom a)]
    have hfix2 : adjHom (adjHom a) = a := by
      apply Subtype.ext
      exact Geo.formAdj_formAdj σ hσ hG hGh a.1
    rw [hfix2]
  have hinj : Function.Injective τhom := fun x y hxy => by
    have := congrArg τhom hxy
    rwa [hττ x, hττ y] at this
  have hsurj : Function.Surjective τhom := fun x => ⟨τhom x, hττ x⟩
  let τ : K ≃+* K := RingEquiv.ofBijective τhom ⟨hinj, hsurj⟩
  exact ⟨τ, fun a => hτπ a, fun x => hττ x⟩

private lemma fePSU_unitaryInvolution_ne_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {f d : ℕ} (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) :
    CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) ≠ 1 := by
  have hcard2 : 2 ≤ Nat.card K := by
    letI : Fintype K := Fintype.ofFinite K
    haveI : Nontrivial K := inferInstance
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hfd : 1 ≤ f * d := by
    rcases Nat.eq_zero_or_pos (f * d) with h0 | hpos
    · exfalso
      rcases Nat.mul_eq_zero.mp h0 with hf | hd
      · rw [hf] at hKcard; norm_num at hKcard; omega
      · rw [hd] at hKcard; norm_num at hKcard; omega
    · exact hpos
  have hge2 : 2 ≤ 2 ^ (f*d) := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2 ^ (f*d) := Nat.pow_le_pow_right (by norm_num) hfd
  intro h
  have hfix : ∀ x : K, x ≠ 0 → x ^ (2 ^ (f*d) - 1) = 1 := by
    intro x hx
    have hxpow : x ^ (2 ^ (f*d)) = x := by
      have hc := congrArg (fun e : K ≃+* K => e x) h
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hc
      exact hc
    have hh := hxpow
    rw [show 2 ^ (f*d) = (2 ^ (f*d) - 1) + 1 by omega, pow_succ] at hh
    have h' : x ^ (2 ^ (f*d) - 1) * x = 1 * x := by rw [hh, one_mul]
    exact mul_right_cancel₀ hx h'
  let p : Polynomial K := Polynomial.X ^ (2 ^ (f*d) - 1) - Polynomial.C 1
  have hpdeg : p.natDegree = 2 ^ (f*d) - 1 := Polynomial.natDegree_X_pow_sub_C
  have hpne : p ≠ 0 := by
    intro hp
    have h0 : p.natDegree = 0 := by rw [hp]; exact Polynomial.natDegree_zero
    rw [hpdeg] at h0
    omega
  have heval : ∀ u : Kˣ, Polynomial.eval (u : K) p = 0 := by
    intro u
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [hfix (u : K) (Units.ne_zero u)]
    ring
  have hinj : Function.Injective (fun u : Kˣ => (u : K)) := Units.val_injective
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hbase : ((2 ^ f) ^ d) ^ 2 = 2 ^ (2*(f*d)) := by ring_nf
  have hcardu : Fintype.card Kˣ = 2 ^ (2*(f*d)) - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hKcard, hbase]
  have hlt : p.natDegree < Fintype.card Kˣ := by
    rw [hpdeg, hcardu]
    have h2 : 2 ^ (f*d) < 2 ^ (2*(f*d)) := by
      rw [show 2*(f*d) = (f*d)+(f*d) by ring, pow_add]
      have hpos : 0 < 2 ^ (f*d) := by positivity
      nlinarith [hge2, hpos]
    omega
  exact hpne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hinj heval hlt)

private lemma fePSU_selfDual_blockHeldSUid_adjoint_tau_eq
    {f d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (τ : K ≃+* K) (hτ2 : ∀ x, τ (τ x) = x) (hτne : τ ≠ 1) :
    τ = CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) := by
  have hcard' : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
  have hτσ2 : CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) ^ 2 = 1 := by
    ext x
    change CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) x) = x
    exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hcard' x
  have hτ2' : τ ^ 2 = 1 := by
    ext x
    change τ (τ x) = x
    exact hτ2 x
  have hne : CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) ≠ 1 :=
    fePSU_unitaryInvolution_ne_one hKcard
  exact CFSG.ABGDGroups.ringEquiv_eq_of_sq_eq_one hτ2' hτσ2 hτne hne

private lemma fePSU_selfDual_blockHeldSUid_pi_adjoint {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {S : Set (GL (Fin n) F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    {d : ℕ} {K : Type} [Field K] [Finite K] [Algebra F K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * ε = 0)
    (hadjmem : ∀ a : Algebra.adjoin F (Units.val '' S),
      formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
        (a : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S)) :
    ∀ a : Algebra.adjoin F (Units.val '' S),
      CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) (π a) =
        π ⟨formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
          (a : Matrix (Fin n) (Fin n) F), hadjmem a⟩ := by
  let σ : F →+* F := (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
  obtain ⟨τ, hτπ, hττ⟩ :=
    fePSU_selfDual_blockHeldSUid_adjoint_descend (S := S) hc hS hε π hπsurj hπker hadjmem
  have hτF : ∀ c : F, τ (algebraMap F K c) = algebraMap F K
      ((CFSG.LieType.BorelTits.unitaryInvolution F 2 f) c) := by
    intro c
    rw [← π.commutes c]
    change τ (π (algebraMap F (Algebra.adjoin F (Units.val '' S)) c)) =
      algebraMap F K ((CFSG.LieType.BorelTits.unitaryInvolution F 2 f) c)
    rw [hτπ]
    have h2 : (⟨formAdj σ G ((algebraMap F (Algebra.adjoin F (Units.val '' S)) c) :
          Matrix (Fin n) (Fin n) F), hadjmem _⟩ : Algebra.adjoin F (Units.val '' S)) =
        algebraMap F (Algebra.adjoin F (Units.val '' S))
          ((CFSG.LieType.BorelTits.unitaryInvolution F 2 f) c) := by
      apply Subtype.ext
      show formAdj σ G (algebraMap F (Matrix (Fin n) (Fin n) F) c) =
        algebraMap F (Matrix (Fin n) (Fin n) F)
          ((CFSG.LieType.BorelTits.unitaryInvolution F 2 f) c)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        Geo.formAdj_smul, Geo.formAdj_one σ hG]
      rfl
    rw [h2, π.commutes]
  have hτne : τ ≠ 1 := by
    intro hid
    obtain ⟨c, hcne⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hc
    have h : τ (algebraMap F K c) = algebraMap F K c := by
      have hid' : (τ : K → K) = (RingHom.id K : K → K) := by
        rw [hid]; rfl
      rw [hid']; rfl
    rw [hτF c] at h
    exact hcne (RingHom.injective (algebraMap F K) h)
  have hτeq := fePSU_selfDual_blockHeldSUid_adjoint_tau_eq hKcard τ hττ hτne
  intro a
  rw [← hτeq]
  exact hτπ a

private lemma fePSU_selfDual_blockHeldSUid_tau_action {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} {d : ℕ} {S : Set (GL (Fin n) F)} {ε : Matrix (Fin n) (Fin n) F}
    {K : Type} [Field K] [Finite K] [Algebra F K] [CharP K 2]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hactπ : ∀ (a : Algebra.adjoin F (Units.val '' S)) (w : LinearMap.range (Matrix.mulVecLin ε)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) (w : Fin n → F))
    (hadjmem : ∀ a : Algebra.adjoin F (Units.val '' S),
      formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
        (a : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S))
    (hpiadj : ∀ a : Algebra.adjoin F (Units.val '' S),
      CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) (π a) =
        π ⟨formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
          (a : Matrix (Fin n) (Fin n) F), hadjmem a⟩) :
    ∀ (a : Algebra.adjoin F (Units.val '' S)) (w : LinearMap.range (Matrix.mulVecLin ε)),
      ((CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) (π a) • w :
          LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F) =
        Matrix.mulVec (formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
          (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) F)) w := by
  intro a w
  rw [hpiadj a]
  simpa using hactπ ⟨formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
    (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) F), hadjmem a⟩ w

private lemma fePSU_selfDual_blockHeldSUid_hadj {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * ε = 0)
    (hactπ : ∀ (a : Algebra.adjoin F (Units.val '' S)) (w : LinearMap.range (Matrix.mulVecLin ε)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → F) =
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) F) (w : Fin n → F))
    (hadjmem : ∀ a : Algebra.adjoin F (Units.val '' S),
      formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
        (a : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S)) :
    ∀ (a : K) (x y : (LinearMap.range (Matrix.mulVecLin ε))),
      fePSU_selfDual_blockFormF (f := f) ε (a • x) y =
        fePSU_selfDual_blockFormF (f := f) ε x
          ((CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) a) • y) := by
  have hpiadj := fePSU_selfDual_blockHeldSUid_pi_adjoint hc hS hε hKcard π hπsurj hπker hadjmem
  have hτπ := fePSU_selfDual_blockHeldSUid_tau_action (S := S) π hactπ hadjmem hpiadj
  exact fePSU_selfDual_blockFormDescent_adjoint S d K π hπsurj hactπ hτπ

private lemma fePSU_selfDual_blockHeldSUid_core {F : Type} [Field F] [Finite F] [CharP F 2] {f n :
    ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (hnt : ⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≠ ⊥) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≃*
        CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) m) := by
  obtain ⟨π, hπsurj, hπker⟩ :=
    fePSU_selfDual_blockHeldSUid_pi hc S hS hodd he d hd K hKcard
  obtain ⟨hmod, hfin, htower, act, hact, hactm, hactπ⟩ :=
    fePSU_selfDual_blockHeldSUid_action S hS he K π hπsurj hπker
  letI : Module K (LinearMap.range (Matrix.mulVecLin ε)) := hmod
  letI : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin ε)) := hfin
  letI : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin ε)) := htower
  have hdim :=
    fePSU_selfDual_blockHeldSUid_dim S K act hact hnt
  have hadjmem : ∀ a : Algebra.adjoin F (Units.val '' S),
      formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n)
        (a : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S) := by
    intro a
    have hG : IsUnit (Unitary.antidiag n).det :=
      isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
    have hSU' : ∀ s ∈ S, Matrix.transpose
        ((s : Matrix (Fin n) (Fin n) F).map
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) * Unitary.antidiag n *
          (s : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := by
      intro s hs
      simpa [Unitary.conjTr] using hSU s hs
    exact Geo.formAdj_mem_adjoin
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom hG hSU' a.2
  have hadj :=
    fePSU_selfDual_blockHeldSUid_hadj hc S hS hε d K hKcard
      π hπsurj hπker hactπ hadjmem
  have hunitF :=
    fePSU_selfDual_blockFormDescent_actInvariant S K act
      hactm
  have hbar :=
    fePSU_selfDual_blockFormDescent_involution hc S hSU hS hodd hε he d hd K
  have hBsF := fePSU_selfDual_blockFormF_isSymm (f := f) hc ε
  have hBlF := fePSU_selfDual_blockFormF_separatingLeft hc hε.2.2.2.1 hε.2.1
  obtain ⟨B, hBs, hBl, hBt⟩ :=
    fePSU_selfDual_blockFormDescent_trace hc S d hd hdeg K hKcard
      (fePSU_selfDual_blockFormF (f := f) ε) hBsF hBlF hbar hadj
  have hunit :=
    fePSU_selfDual_blockFormDescent_unitary S d K act
      (fePSU_selfDual_blockFormF (f := f) ε) B hBt hunitF
  have hsurj :=
    fePSU_selfDual_blockHeldSUid_surj hc S hS hε he d hd hdeg K hKcard act B hBs hBl hdim
        hactm hBt π hactπ
  obtain ⟨eSU⟩ :=
    fePSU_selfDual_blockHeldSUid_held S d K act B hunit hsurj
      hact
  obtain ⟨emod⟩ :=
    fePSU_selfDual_blockHeldSUid_model (K := K) (f := f) (d := d) B hBs hBl hKcard
  exact ⟨Module.finrank K (LinearMap.range (Matrix.mulVecLin ε)), hdim, ⟨eSU.trans emod⟩⟩

private lemma fePSU_selfDual_blockHeldSUid {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (hnt : ⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≠ ⊥) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≃*
        CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) m) :=
  fePSU_selfDual_blockHeldSUid_core hc S hSU hS hodd hε he d hd hdeg K hKcard hnt

private lemma fePSU_selfDual_SUid_eq_statedSU {K : Type} [Field K] [Finite K] [CharP K 2]
    {f d : ℕ} (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) (m : ℕ) :
    CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) m =
      StatedSU m ((2 ^ f) ^ d) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
  have h := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := f * d) hK m
  rw [h, pow_mul]

private lemma fePSU_selfDual_derived_iso {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (hnt : ⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≠ ⊥)
    :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≃*
        StatedSU m ((2 ^ f) ^ d) K) := by
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    fePSU_selfDual_blockHeldSUid hc S hSU hS hodd hε he d hd hdeg K hKcard hnt
  exact ⟨m, hm, ⟨e.trans (MulEquiv.subgroupCongr
    (fePSU_selfDual_SUid_eq_statedSU (f := f) (d := d) hKcard m))⟩⟩

private lemma fePSU_selfDual_GepsSU_model {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (hnt : ⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≠ ⊥)
    (m : ℕ)
    (ψ : ↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ →*
        (Matrix (Fin m) (Fin m) K)ˣ)
    (hψ : Function.Injective ψ) :
    ∃ m' : ℕ, 2 ≤ m' ∧
      Nonempty (↥(MonoidHom.range ψ) ≃* StatedSU m' ((2 ^ f) ^ d) K) := by
  obtain ⟨m', hm', ⟨eiso⟩⟩ :=
    fePSU_selfDual_derived_iso hc S hSU hS hodd hε he d hd hdeg K hKcard hnt
  have hψ' : Function.Injective ψ.rangeRestrict :=
    fun _ _ h => hψ (congrArg Subtype.val h)
  have e₁ : ↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≃*
      ↥(MonoidHom.range ψ) :=
    MulEquiv.ofBijective ψ.rangeRestrict ⟨hψ', MonoidHom.rangeRestrict_surjective ψ⟩
  exact ⟨m', hm', ⟨e₁.symm.trans eiso⟩⟩

private lemma fePSU_selfDual_derived_SU {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (hnt : ⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≠ ⊥) :
    ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
        glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≃*
        StatedSU m ((2 ^ f) ^ d) K) := by
  obtain ⟨m, ψ, hm, hψ⟩ :=
    fePSU_selfDual_GepsSU_embed hc S hS hε he d hd hdeg K hKcard
  obtain ⟨m', hm', ⟨emod⟩⟩ :=
    fePSU_selfDual_GepsSU_model hc S hSU hS hodd hε he d hd hdeg K hKcard hnt m ψ hψ
  have hψ' : Function.Injective ψ.rangeRestrict :=
    fun _ _ h => hψ (congrArg Subtype.val h)
  exact ⟨m', hm', ⟨(MulEquiv.ofBijective ψ.rangeRestrict
    ⟨hψ', MonoidHom.rangeRestrict_surjective ψ⟩).trans emod⟩⟩

private lemma fePSU_selfDual_transport_quasisimple_large {F : Type} [Field F] [Finite F]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {d : ℕ} (hdeg : 2 ≤ d)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) {m : ℕ} (hm : 4 ≤ m) :
    CFSG.Open.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := fePSU_f_pos hc
  have hfd : 1 ≤ f * d := le_trans hf (Nat.le_mul_of_pos_right f (by omega))
  haveI hKK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f * d) K :=
    ⟨Nat.prime_two, hfd, by rw [hKcard, ← pow_mul, ← pow_mul]; congr 1; ring⟩
  have hK' : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
  have hq : (2 ^ f) ^ d = 2 ^ (f * d) := (pow_mul 2 f d).symm
  have hperf : Group.IsPerfect ↥(StatedSU m ((2 ^ f) ^ d) K) := by
    rw [hq]
    exact CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU
      (F := K) (p := 2) (f := f * d) hK' hm
  have hsimple : IsSimpleGroup (CFSG.Open.StatedProj (StatedSU m ((2 ^ f) ^ d) K)) := by
    rw [hq]
    exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 (f * d) hK' m
      (by omega) (by
        intro hcon
        exact absurd (Prod.mk.inj hcon).1 (by omega))
  have hcenter :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimple).2
  refine ⟨?_, ?_⟩
  · exact hperf.commutator_eq_top
  · convert hsimple using 2

private lemma fePSU_selfDual_transport_quasisimple_three {F : Type} [Field F] [Finite F]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {d : ℕ} (hdeg : 2 ≤ d)
    {K : Type} [Field K] [Finite K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) {m : ℕ} (hm : 3 ≤ m) :
    CFSG.Open.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K)  := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfd : 1 ≤ f * d := le_trans (fePSU_f_pos hc) (Nat.le_mul_of_pos_right f (by omega))
  have hfd2 : 2 ≤ f * d := by
    calc (2:ℕ) = 1 * 2 := by norm_num
      _ ≤ f * d := Nat.mul_le_mul (fePSU_f_pos hc) hdeg
  haveI hKK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f * d) K :=
    ⟨Nat.prime_two, hfd, by rw [hKcard, ← pow_mul, ← pow_mul]; congr 1; ring⟩
  have hK' : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
  have hq : (2 ^ f) ^ d = 2 ^ (f * d) := (pow_mul 2 f d).symm
  have hge4 : 4 ≤ 2 ^ (f * d) := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) hfd2
  have hbad : (m, 2 ^ (f * d)) ≠ (3, 2) := by
    intro hcon
    have h2 : 2 ^ (f * d) = 2 := (Prod.mk.inj hcon).2
    omega
  have hperf : Group.IsPerfect ↥(StatedSU m ((2 ^ f) ^ d) K) := by
    rw [hq]
    exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK' hm hbad
  have hsimple : IsSimpleGroup (CFSG.Open.StatedProj (StatedSU m ((2 ^ f) ^ d) K)) := by
    rw [hq]
    exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 (f * d) hK' m hm hbad
  have hcenter := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimple).2
  refine ⟨?_, ?_⟩
  · exact hperf.commutator_eq_top
  · convert hsimple using 2

private lemma fePSU_selfDual_transport_quasisimple_two {F : Type} [Field F] [Finite F]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {d : ℕ} (hdeg : 2 ≤ d)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) {m : ℕ} (hm : 2 ≤ m) (hm2 : m = 2) :
    CFSG.Open.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K)  := by
  subst hm2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
  have hfd2 : 2 ≤ f * d := by
    calc (2:ℕ) = 1 * 2 := by norm_num
      _ ≤ f * d := Nat.mul_le_mul (fePSU_f_pos hc) hdeg
  have hcard : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d)) = 2 ^ (f * d) :=
    CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := 2) (f := f * d) hK'
  have h4 : 4 ≤ Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d)) := by
    rw [hcard]
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) hfd2
  have hqSL : CFSG.Assembly.IsQuasisimple
      ↥(StatedSL 2 ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d))) :=
    fePSU_statedSL_quasisimple ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d)) (by norm_num) h4
  obtain ⟨eSU⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
    (K := K) (r := 2) (f := f * d) hK'
  rw [pow_mul] at eSU
  have e : ↥(StatedSU 2 ((2 ^ f) ^ d) K) ≃*
      ↥(StatedSL 2 ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d))) :=
    eSU.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
      ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d)))
  have hq : CFSG.Assembly.IsQuasisimple ↥(StatedSU 2 ((2 ^ f) ^ d) K) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hqSL
  have hC : CFSG.IsQuasisimple ↥(StatedSU 2 ((2 ^ f) ^ d) K) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr hq
  exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hC

private lemma fePSU_selfDual_transport_quasisimple_small {F : Type} [Field F] [Finite F]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {d : ℕ} (hdeg : 2 ≤ d)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3) :
    CFSG.Open.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K) := by
  rcases eq_or_lt_of_le hm with hm2 | hlt
  · exact fePSU_selfDual_transport_quasisimple_two hc hdeg hKcard hm hm2.symm
  · exact fePSU_selfDual_transport_quasisimple_three hc hdeg hKcard (by omega)

private lemma fePSU_selfDual_transport_quasisimple {F : Type} [Field F] [Finite F]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {d : ℕ} (hdeg : 2 ≤ d)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) {m : ℕ} (hm : 2 ≤ m) :
    CFSG.Open.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · exact fePSU_selfDual_transport_quasisimple_small hc hdeg hKcard hm (by omega)
  · exact fePSU_selfDual_transport_quasisimple_large hc hdeg hKcard h

private lemma fePSU_selfDual_transport_hqG {F : Type} [Field F] [Finite F] [CharP F 2] {f d n : ℕ}
    (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    {K : Type} [Field K] {m : ℕ}
    (hiso : Nonempty (↥⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2
        f) n).subtype S ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            F 2 f) n).subtype S ε⁆ ≃* StatedSU m ((2 ^ f) ^ d) K))
    (hqSU : CFSG.Open.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K)) :
    CFSG.Open.IsQuasisimple ↥⁅glBlockCentralizer (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε, glBlockCentralizer
            (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ := by
  have hC : CFSG.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hqSU
  have hA : CFSG.Assembly.IsQuasisimple ↥(StatedSU m ((2 ^ f) ^ d) K) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mp hC
  obtain ⟨e⟩ := hiso
  have hAH : CFSG.Assembly.IsQuasisimple ↥⁅glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hA
  have hCH : CFSG.IsQuasisimple ↥⁅glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr hAH
  exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hCH

private lemma fePSU_selfDual_transport_component_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (S : Set (GL (Fin n) F))
    {ε : Matrix (Fin n) (Fin n) F}
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε, glBlockCentralizer
            (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆)
    (hqG : CFSG.Open.IsQuasisimple ↥⁅glBlockCentralizer (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε, glBlockCentralizer
            (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆) :
    J' = ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
        S ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
            n).subtype S ε⁆ := by
  have hJqA : CFSG.Assembly.IsQuasisimple ↥J' := hJε.2.2
  have hJqC : CFSG.IsQuasisimple ↥J' :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr hJqA
  have hJqO : CFSG.Open.IsQuasisimple ↥J' :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hJqC
  exact CFSG.HardMathSupport.Solomon.Coordinator.i253_eq_of_isSubnormal hqG hJqO
    ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open J' _).mp hJε.2.1)

private lemma fePSU2_scalars_subgroupOf_statedSL_two_eq_bot {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzscal : (z : GL (Fin 2) K) ∈ StatedScalars (Fin 2) K := hz
  rw [CFSG.Open.StatedAPI.statedScalars_eq_center] at hzscal
  obtain ⟨c, hc⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).mp hzscal
  have hdet : ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    (CFSG.Open.StatedAPI.mem_statedSL_iff).mp z.2
  have hc2 : c ^ 2 = 1 := by
    have h := hdet
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hc1 : c = 1 := by
    rcases (sq_eq_one_iff.mp hc2) with h | h
    · exact h
    · rw [h]; exact CharTwo.neg_eq 1
  apply Subtype.ext
  apply Units.ext
  simp [← hc, hc1, Matrix.scalar_apply, Matrix.diagonal_one]

private lemma fePSU2_scalars_subgroupOf_statedSU_two_eq_bot {K : Type} [Field K] [CharP K 2]
    (q : ℕ) :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSU 2 q K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzscal : (z : GL (Fin 2) K) ∈ StatedScalars (Fin 2) K := hz
  rw [CFSG.Open.StatedAPI.statedScalars_eq_center] at hzscal
  obtain ⟨c, hc⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).mp hzscal
  have hzSL : (z : GL (Fin 2) K) ∈ StatedSL 2 K :=
    CFSG.Open.StatedAPI.statedSU_le_statedSL 2 q K z.2
  have hdet : ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    (CFSG.Open.StatedAPI.mem_statedSL_iff).mp hzSL
  have hc2 : c ^ 2 = 1 := by
    have h := hdet
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hc1 : c = 1 := by
    rcases (sq_eq_one_iff.mp hc2) with h | h
    · exact h
    · rw [h]; exact CharTwo.neg_eq 1
  apply Subtype.ext
  apply Units.ext
  simp [← hc, hc1, Matrix.scalar_apply, Matrix.diagonal_one]

private lemma fePSU_selfDual_transport_center {K : Type} [Field K] [Finite K] [CharP K 2]
    {f d m : ℕ} (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) (hm : 2 ≤ m)
    (hbad : (m, (2 ^ f) ^ d) ≠ (3, 2)) :
    Subgroup.center ↥(StatedSU m ((2 ^ f) ^ d) K) =
      (StatedScalars (Fin m) K).subgroupOf (StatedSU m ((2 ^ f) ^ d) K) := by
  rcases eq_or_lt_of_le hm with hm2 | hlt
  · subst hm2
    have hK' : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := K) (r := 2) (f := f * d) hK'
    rw [pow_mul] at e
    have hbot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
        ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d))) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro A hA
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
      obtain ⟨r, hr2, hAeq⟩ := hA
      have hr1 : r = 1 := by
        have h : r ^ 2 = 1 := by simpa using hr2
        rcases sq_eq_one_iff.mp h with h | h
        · exact h
        · rw [h]; exact CharTwo.neg_eq 1
      apply Subtype.ext
      rw [← hAeq, hr1]
      simp
    have hmap := Subgroup.map_center_eq e
    rw [hbot, Subgroup.map_bot] at hmap
    rw [hmap.symm, fePSU2_scalars_subgroupOf_statedSU_two_eq_bot]
  · have hm3 : 3 ≤ m := by omega
    have hK' : Nat.card K = (2 ^ (f * d)) ^ 2 := by rw [hKcard, pow_mul]
    have hq : (2 ^ f) ^ d = 2 ^ (f * d) := (pow_mul 2 f d).symm
    have hbad' : (m, 2 ^ (f * d)) ≠ (3, 2) := by
      intro hcon
      exact hbad (by rw [hq]; exact hcon)
    have hperf : Group.IsPerfect ↥(StatedSU m ((2 ^ f) ^ d) K) := by
      rw [hq]
      exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK' hm3 hbad'
    have hsimple : IsSimpleGroup (CFSG.Open.StatedProj (StatedSU m ((2 ^ f) ^ d) K)) := by
      rw [hq]
      exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 (f * d) hK' m hm3
          hbad'
    exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimple).2

private lemma fePSU_selfDual_transport_quotient {F : Type} [Field F] [Finite F] [CharP F 2]
    {f d n : ℕ} {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε, glBlockCentralizer
            (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆)
    {K : Type} [Field K] {m : ℕ}
    (hiso : Nonempty (↥⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2
        f) n).subtype S ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            F 2 f) n).subtype S ε⁆ ≃* StatedSU m ((2 ^ f) ^ d) K))
    (hJ : J' = ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
        n).subtype S ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2
            f) n).subtype S ε⁆)
    (hcenter : Subgroup.center ↥(StatedSU m ((2 ^ f) ^ d) K) =
      (StatedScalars (Fin m) K).subgroupOf (StatedSU m ((2 ^ f) ^ d) K)) :
    Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃*
      StatedProj (StatedSU m ((2 ^ f) ^ d) K)) := by
  obtain ⟨eD⟩ := hiso
  obtain ⟨-, ⟨eC⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e.centralImage_facts ψ hψ hJε.2.2
  let e' : ↥J' ≃* StatedSU m ((2 ^ f) ^ d) K :=
    (MulEquiv.subgroupCongr hJ).trans eD
  let eZ : ↥J' ⧸ Subgroup.center ↥J' ≃*
      StatedSU m ((2 ^ f) ^ d) K ⧸ Subgroup.center ↥(StatedSU m ((2 ^ f) ^ d) K) :=
    QuotientGroup.congr (Subgroup.center ↥J')
      (Subgroup.center ↥(StatedSU m ((2 ^ f) ^ d) K)) e' (Subgroup.map_center_eq e')
  let eP : StatedSU m ((2 ^ f) ^ d) K ⧸
        Subgroup.center ↥(StatedSU m ((2 ^ f) ^ d) K) ≃*
      StatedProj (StatedSU m ((2 ^ f) ^ d) K) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  exact ⟨eC.symm.trans (eZ.trans eP)⟩

private lemma fePSU_selfDual_transport {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε : Matrix (Fin n) (Fin n) F}
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (d : ℕ) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2)
    (m : ℕ) (hm : 2 ≤ m)
    (hiso : Nonempty (↥⁅glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≃*
      StatedSU m ((2 ^ f) ^ d) K)) :
    Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃*
      StatedProj (StatedSU m ((2 ^ f) ^ d) K)) := by
  have hqSU := fePSU_selfDual_transport_quasisimple hc hdeg hKcard hm
  have hqG := fePSU_selfDual_transport_hqG S hiso hqSU
  have hJ := fePSU_selfDual_transport_component_eq S hJε hqG
  have hfd2 : 2 ≤ f * d := by
    calc (2:ℕ) = 1 * 2 := by norm_num
      _ ≤ f * d := Nat.mul_le_mul (fePSU_f_pos hc) hdeg
  have hq4 : 4 ≤ (2 ^ f) ^ d := by
    rw [show (2 ^ f) ^ d = 2 ^ (f * d) from (pow_mul 2 f d).symm]
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) hfd2
  have hbad : (m, (2 ^ f) ^ d) ≠ (3, 2) := by
    intro hcon
    have h2 : (2 ^ f) ^ d = 2 := (Prod.mk.inj hcon).2
    omega
  have hcenter := fePSU_selfDual_transport_center hKcard hm hbad
  exact fePSU_selfDual_transport_quotient ψ hψ S hJε hiso hJ hcenter

private lemma fePSU_selfDual_SU2_to_SL2 {F : Type} [Field F] [CharP F 2] {f : ℕ}
    (d : ℕ) {K : Type} [Field K] [Finite K] [Algebra F K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
      Nat.card K' = (2 ^ f) ^ d ∧
      Nonempty (StatedProj (StatedSU 2 ((2 ^ f) ^ d) K) ≃* StatedProj (StatedSL 2 K')) := by
  classical
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' : Type := ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d))
  haveI : CharP K' 2 := Subfield.charP (CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d)) 2
  have hK' : Nat.card K = (2 ^ (f * d)) ^ 2 := by
    rw [hKcard, ← pow_mul 2 f d]
  have hcard : Nat.card K' = 2 ^ (f * d) :=
    CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := 2) (f := f * d) hK'
  refine ⟨K', inferInstance, inferInstance, ?_, ?_⟩
  · rw [hcard, pow_mul]
  · obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := K) (r := 2) (f := f * d) hK'
    rw [pow_mul] at e
    have eSL : ↥(StatedSL 2 K') ≃* StatedSU 2 ((2 ^ f) ^ d) K :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K').symm.trans e
    have hbotSL : (StatedScalars (Fin 2) K').subgroupOf (StatedSL 2 K') = ⊥ :=
      fePSU2_scalars_subgroupOf_statedSL_two_eq_bot
    have hbotSU : (StatedScalars (Fin 2) K).subgroupOf (StatedSU 2 ((2 ^ f) ^ d) K) = ⊥ :=
      fePSU2_scalars_subgroupOf_statedSU_two_eq_bot ((2 ^ f) ^ d)
    have projSU : StatedProj (StatedSU 2 ((2 ^ f) ^ d) K) ≃* StatedSU 2 ((2 ^ f) ^ d) K :=
      (QuotientGroup.quotientMulEquivOfEq hbotSU).trans QuotientGroup.quotientBot
    have projSL : StatedProj (StatedSL 2 K') ≃* ↥(StatedSL 2 K') :=
      (QuotientGroup.quotientMulEquivOfEq hbotSL).trans QuotientGroup.quotientBot
    exact ⟨projSU.trans (eSL.symm.trans projSL.symm)⟩

private lemma fePSU_selfDual_classification {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (hfix : e = ε) :
    (∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = ((2 ^ f) ^ d) ^ 2 ∧ 3 ≤ m ∧ (m, (2 ^ f) ^ d) ≠ (3, 2) ∧
        Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃*
          StatedProj (StatedSU m ((2 ^ f) ^ d) K))) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = (2 ^ f) ^ d ∧
        Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃*
          StatedProj (StatedSL 2 K))) := by
  classical
  have hfixadj : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e = e := by
    rw [hfix]
    exact hε.2.2.2.1
  have hdε : d = blockDegree (Algebra.adjoin F (Units.val '' S)) ε := by rw [hd, hfix]
  obtain ⟨K, hKf, hKa, hKfin, τ, _, hKcard, hτ2, -, -, -, -⟩ :=
    fePSU_selfDual_blockField_adjoint hc S hSU hS hodd he d hd hfixadj
  letI : Field K := hKf
  letI : Algebra F K := hKa
  letI : Finite K := hKfin
  have heprim : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) ε := by rw [← hfix]; exact he
  have hnt : ⁅glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ ≠ ⊥ := by
    intro hbot
    have hJbot : J' = ⊥ := le_bot_iff.mp (hbot ▸ hJε.1)
    exact (Subgroup.nontrivial_iff_ne_bot J').mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hJε.2.2) hJbot
  obtain ⟨m, hm2, hiso⟩ :=
    fePSU_selfDual_derived_SU hc S hSU hS hodd hε heprim d hdε hdeg K hKcard hnt
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  have htrans := fePSU_selfDual_transport hc n ψ hψ S hJε d hdeg
    K hKcard m hm2 hiso
  by_cases hm3 : 3 ≤ m
  · left
    refine ⟨m, K, hKf, hKfin, hKcard, hm3, ?_, htrans⟩
    intro h
    have hp : (2 ^ f) ^ d = 2 := (Prod.mk.inj h).2
    have hf : 1 ≤ f := fePSU_f_pos hc
    have h2fd : 2 ≤ f * d := by
      calc (2 : ℕ) = 1 * 2 := by norm_num
        _ ≤ f * d := Nat.mul_le_mul hf hdeg
    have h4 : 4 ≤ (2 ^ f) ^ d := by
      rw [← pow_mul]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) h2fd
    omega
  · right
    have hm2' : m = 2 := by omega
    subst hm2'
    obtain ⟨K', hK'f, hK'fin, hK'card, ⟨econv⟩⟩ :=
      fePSU_selfDual_SU2_to_SL2 (F := F) (f := f) d hKcard
    obtain ⟨ftrans⟩ := htrans
    exact ⟨K', hK'f, hK'fin, hK'card, ⟨ftrans.trans econv⟩⟩

private lemma fePSU_selfDual_iso {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (d : ℕ) (hd : d = blockDegree (Algebra.adjoin F (Units.val '' S)) e) (hdeg : 2 ≤ d)
    (hfix : e = ε) :
    (∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = ((2 ^ f) ^ d) ^ 2 ∧ 3 ≤ m ∧ (m, (2 ^ f) ^ d) ≠ (3, 2) ∧
        Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃*
          StatedProj (StatedSU m ((2 ^ f) ^ d) K))) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = (2 ^ f) ^ d ∧
        Nonempty ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ) ≃*
          StatedProj (StatedSL 2 K))) := by
  exact fePSU_selfDual_classification hc n ψ hψ S hSU hS hodd hε hJε he d hd hdeg hfix

private theorem fePSU_selfDual {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hfix : e = ε) :
    GGSixLSevenFieldExtCaseCl (J'.map ψ) .PSU f := by
  classical
  set d : ℕ := blockDegree (Algebra.adjoin F (Units.val '' S)) e with hd
  have hdeg' : 2 ≤ d := by rw [hd]; exact hdeg
  have hfixadj : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e = e := by
    rw [hfix]
    exact hε.2.2.2.1
  have hdodd : Odd d :=
    fePSU_selfDual_blockDegree_odd hc S hSU hS hodd he d hd hfixadj
  have hf : 1 ≤ f := fePSU_f_pos hc
  have h2fd : 2 ≤ f * d := by
    calc (2 : ℕ) = 1 * 2 := by norm_num
      _ ≤ f * d := Nat.mul_le_mul hf hdeg'
  have hlt : f < f * d := by
    calc f = f * 1 := (mul_one f).symm
      _ < f * d := Nat.mul_lt_mul_of_pos_left (by omega) hf
  have h4fd : 4 ≤ 2 ^ (f * d) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) h2fd
  rcases fePSU_selfDual_iso hc n ψ hψ S hSU hS hodd hε hJε he d hd hdeg' hfix with
    ⟨m, K, hKfield, hKfin, hKcard, hm3, _, ⟨eiso⟩⟩ | ⟨K, hKfield, hKfin, hKcard, ⟨eiso⟩⟩
  · letI : Field K := hKfield
    letI : Finite K := hKfin
    have hq : (2 ^ f) ^ d = 2 ^ (f * d) := (pow_mul 2 f d).symm
    refine ⟨.PSU, m, f * d, Or.inr rfl, hlt, ?_, ?_⟩
    · refine Or.inl ⟨by decide, ?_⟩
      refine ⟨⟨Nat.prime_two, ?_, hm3, ?_⟩, ?_⟩
      · exact Nat.mul_pos hf (by omega)
      · intro h
        have hp : 2 ^ (f * d) = 2 := (Prod.mk.inj h).2
        omega
      · refine ⟨K, hKfield, hKfin, ?_, ?_⟩
        · rw [hKcard, hq]
        · rw [hq] at eiso
          exact ⟨eiso⟩
    · intro h
      exact absurd h.1 (by decide)
  · letI : Field K := hKfield
    letI : Finite K := hKfin
    have hq : (2 ^ f) ^ d = 2 ^ (f * d) := (pow_mul 2 f d).symm
    have hdne : d ≠ 2 := by
      intro hd2
      have heven : Even d := by rw [hd2]; exact ⟨1, by omega⟩
      exact (Nat.not_even_iff_odd.mpr hdodd) heven
    refine ⟨.PSL, 2, f * d, Or.inl rfl, hlt, ?_, ?_⟩
    · refine Or.inl ⟨by decide, ?_⟩
      refine ⟨⟨Nat.prime_two, ?_, le_rfl, ?_, ?_⟩, ?_⟩
      · exact Nat.mul_pos hf (by omega)
      · intro h
        have hp : 2 ^ (f * d) = 2 := (Prod.mk.inj h).2
        omega
      · intro h
        have hp : 2 ^ (f * d) = 3 := (Prod.mk.inj h).2
        omega
      · refine ⟨K, hKfield, hKfin, ?_, ?_⟩
        · rw [hKcard, hq]
        · exact ⟨eiso⟩
    · intro h
      have heq : f * d = f * 2 := by rw [h.2.1]; ring
      exact hdne (mul_left_cancel₀ (by omega : f ≠ 0) heq)

theorem ggSixLSevenFieldExtCaseCl_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    GGSixLSevenFieldExtCaseCl (J'.map ψ) .PSU f := by
  rcases fePSU_dichotomy hc S hSU hS hε he heε with hfix | ⟨hpair, hεeq⟩
  · exact fePSU_selfDual hc n ψ hψ S hSU hS hodd hε hJε he hdeg hfix
  · exact fePSU_dualPair hc n ψ hψ S hSU hS hodd hε hJε he heε hdeg hpair hεeq

theorem ggSixLSevenFieldExtCase_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    GGSixLSevenFieldExtCase (J'.map ψ) .PSU f :=
  (ggSixLSevenFieldExtCaseCl_PSU hc n ψ hψ S hSU hS hodd hε hJε he heε hdeg).fieldExtCase

end CFSG.StandardType.ClassicalPosition
