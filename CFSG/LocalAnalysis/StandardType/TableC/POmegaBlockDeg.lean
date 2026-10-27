module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaBlockIso
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaFieldExtRigid
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaLeafDefs
public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockDegree
public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockRank
public import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary

public section

namespace CFSG.StandardType.TableC

open Module QuadraticMap
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.RankThree.Classical2
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks

private lemma j3a_adjoin_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin K (Units.val '' S), ∀ b ∈ Algebra.adjoin K (Units.val '' S),
      a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix ι ι K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix ι ι K) * (s' : Matrix ι ι K) = (s' : Matrix ι ι K) * (s : Matrix ι ι K)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin K (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm K hcommS
  intro a ha b hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin K (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin K (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma j3a_isPrim_formAdj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id K)) = G)
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * G *
      (s : Matrix ι ι K) = G)
    {e : Matrix ι ι K} (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e) :
    IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) (formAdj (RingHom.id K) G e) := by
  have hmem : ∀ {a : Matrix ι ι K}, a ∈ Algebra.adjoin K (Units.val '' S) →
      formAdj (RingHom.id K) G a ∈ Algebra.adjoin K (Units.val '' S) :=
    fun {a} ha => Geo.formAdj_mem_adjoin (RingHom.id K) hG hSU ha
  have hff : formAdj (RingHom.id K) G (formAdj (RingHom.id K) G e) = e :=
    Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG hGh e
  refine ⟨hmem he.1, ?_, ?_, ?_⟩
  · rw [isIdempotentElem_iff]
    calc formAdj (RingHom.id K) G e * formAdj (RingHom.id K) G e
        = formAdj (RingHom.id K) G (e * e) :=
          (Geo.formAdj_mul (RingHom.id K) hG e e).symm
      _ = formAdj (RingHom.id K) G e := by rw [he.2.1.eq]
  · intro h0
    have : e = 0 := by
      rw [← hff, h0]
      simp [formAdj]
    exact he.2.2.1 this
  · intro x hx hxidem hxe
    have hxmem : formAdj (RingHom.id K) G x ∈ Algebra.adjoin K (Units.val '' S) := hmem hx
    have hxidem' : IsIdempotentElem (formAdj (RingHom.id K) G x) := by
      rw [isIdempotentElem_iff]
      calc formAdj (RingHom.id K) G x * formAdj (RingHom.id K) G x
          = formAdj (RingHom.id K) G (x * x) :=
            (Geo.formAdj_mul (RingHom.id K) hG x x).symm
        _ = formAdj (RingHom.id K) G x := by rw [hxidem.eq]
    have hxe' : formAdj (RingHom.id K) G x * e = formAdj (RingHom.id K) G x := by
      have h := congrArg (formAdj (RingHom.id K) G) hxe
      rw [Geo.formAdj_mul (RingHom.id K) hG x (formAdj (RingHom.id K) G e), hff] at h
      rw [j3a_adjoin_comm hS (formAdj (RingHom.id K) G x) hxmem e he.1]
      exact h
    rcases he.2.2.2 (formAdj (RingHom.id K) G x) hxmem hxidem' hxe' with h0 | heq
    · left
      rw [← Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG hGh x, h0]
      simp [formAdj]
    · right
      rw [← Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG hGh x, heq]

private lemma j3a_orth_sum_cases {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e e₁ e₂ : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    (he₁ : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e₁)
    (he₂ : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e₂)
    (hdecomp : e = e * e₁ + e * e₂) :
    e = e₁ ∨ e = e₂ ∨ e = e₁ + e₂ := by
  have hAcomm := j3a_adjoin_comm hS
  have hx₁idem : IsIdempotentElem (e * e₁) :=
    IsIdempotentElem.mul_of_commute (hAcomm e he.1 e₁ he₁.1) he.2.1 he₁.2.1
  have hx₁ : e * e₁ = 0 ∨ e * e₁ = e₁ :=
    he₁.2.2.2 (e * e₁) (Subalgebra.mul_mem _ he.1 he₁.1) hx₁idem
      (by rw [Matrix.mul_assoc, he₁.2.1.eq])
  have hx₂idem : IsIdempotentElem (e * e₂) :=
    IsIdempotentElem.mul_of_commute (hAcomm e he.1 e₂ he₂.1) he.2.1 he₂.2.1
  have hx₂ : e * e₂ = 0 ∨ e * e₂ = e₂ :=
    he₂.2.2.2 (e * e₂) (Subalgebra.mul_mem _ he.1 he₂.1) hx₂idem
      (by rw [Matrix.mul_assoc, he₂.2.1.eq])
  rcases hx₁ with h10 | h1e <;> rcases hx₂ with h20 | h2e
  · exfalso
    have h0 : e = 0 := by rw [hdecomp, h10, h20, add_zero]
    exact he.2.2.1 h0
  · right; left
    rw [hdecomp, h10, h2e, zero_add]
  · left
    rw [hdecomp, h1e, h20, add_zero]
  · right; right
    rw [hdecomp, h1e, h2e]

theorem isPrimIdemIn_cases {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {G : Matrix ι ι K} (hG : IsUnit G.det) (hGt : Matrix.transpose G = G)
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι K) * G * (s : Matrix ι ι K) = G)
    {ε e : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) G (Algebra.adjoin K (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e) (heε : e * ε = e) :
    e = ε ∨ (e ≠ ε ∧ ∃ e' : Matrix ι ι K, IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e' ∧
      e ≠ e' ∧ ε = e + e') := by
  classical
  have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by
    simpa [Matrix.map_id] using hGt
  have hSU' : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * G *
      (s : Matrix ι ι K) = G := by
    intro s hs
    simpa [Matrix.map_id] using hSU s hs
  obtain ⟨e₁, he₁, he₁ε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K) (fun _ => rfl) hG hGh hS hSU' hε
  rcases hcase with he₁_eq | ⟨_, hstar_ne, hεeq⟩
  · left
    have hxe : e * e₁ = e := by rw [he₁_eq]; exact heε
    rcases he₁.2.2.2 e he.1 he.2.1 hxe with h0 | heq
    · exact absurd h0 he.2.2.1
    · exact heq.trans he₁_eq
  · right
    let e₂ : Matrix ι ι K := formAdj (RingHom.id K) G e₁
    have he₂ : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e₂ :=
      j3a_isPrim_formAdj hG hGh hS hSU' he₁
    have horth : e₁ * e₂ = 0 := by
      have h1 : e₁ * (e₁ + e₂) = e₁ + e₁ * e₂ := by rw [Matrix.mul_add, he₁.2.1.eq]
      have h2 : e₁ * (e₁ + e₂) = e₁ := by rw [← hεeq]; exact he₁ε
      have h3 : e₁ + e₁ * e₂ = e₁ + 0 := by rw [add_zero]; exact h1.symm.trans h2
      exact add_left_cancel h3
    have hedecomp : e = e * e₁ + e * e₂ := calc
      e = e * ε := heε.symm
      _ = e * (e₁ + e₂) := by rw [hεeq]
      _ = e * e₁ + e * e₂ := by rw [Matrix.mul_add]
    have he_ne_eps : e ≠ ε := by
      intro hee
      have horth' : e₁ * e = e₁ := by
        rw [hee, hεeq, Matrix.mul_add, he₁.2.1.eq, horth, add_zero]
      have he₁_ne_e : e₁ ≠ e := by
        intro h
        have hz : e₂ = 0 := by
          have h2 : e₁ + e₂ = e₁ + 0 := by
            rw [add_zero]
            exact (h.trans (hee.trans hεeq)).symm
          exact add_left_cancel h2
        exact he₂.2.2.1 hz
      rcases he.2.2.2 e₁ he₁.1 he₁.2.1 horth' with h0 | heq
      · exact he₁.2.2.1 h0
      · exact he₁_ne_e heq
    refine ⟨he_ne_eps, ?_⟩
    rcases j3a_orth_sum_cases hS he he₁ he₂ hedecomp with hee₁ | hee₂ | hee₁₂
    · refine ⟨e₂, he₂, ?_, ?_⟩
      · rw [hee₁]; exact fun h => hstar_ne h.symm
      · rw [hee₁]; exact hεeq
    · refine ⟨e₁, he₁, ?_, ?_⟩
      · rw [hee₂]; exact hstar_ne
      · rw [hee₂]; exact hεeq.trans (add_comm e₁ e₂)
    · exfalso
      have horth' : e₁ * e = e₁ := by
        rw [hee₁₂, Matrix.mul_add, he₁.2.1.eq, horth, add_zero]
      have he₁_ne_e : e₁ ≠ e := by
        intro h
        have hz : e₂ = 0 := by
          have h2 : e₁ + e₂ = e₁ + 0 := by
            rw [add_zero]
            exact (h.trans hee₁₂).symm
          exact add_left_cancel h2
        exact he₂.2.2.1 hz
      rcases he.2.2.2 e₁ he₁.1 he₁.2.1 horth' with h0 | heq
      · exact he₁.2.2.1 h0
      · exact he₁_ne_e heq


private def j3b_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Φ ((A : Matrix ι ι K).mulVec v) = Φ v}
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' v := by
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha v := by
    have h1 : Φ (((a : GL ι K) : Matrix ι ι K).mulVec
        (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v)) = Φ v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    exact (ha (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v)).symm.trans h1

private lemma j3b_iso_of_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {A : GL ι K} (hA : A ∈ StatedOmega ⇑Φ) :
    ∀ v, Φ ((A : Matrix ι ι K).mulVec v) = Φ v := by
  have h : StatedOmega ⇑Φ = ⁅j3b_orth Φ, j3b_orth Φ⁆ := by
    have hcl : Subgroup.closure {A : GL ι K | ∀ v, Φ ((A : Matrix ι ι K).mulVec v) = Φ v} =
        j3b_orth Φ := Subgroup.closure_eq (j3b_orth Φ)
    unfold StatedOmega
    rw [hcl]
  rw [h] at hA
  exact Subgroup.commutator_le_self (j3b_orth Φ) hA

private lemma j3b_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma j3b_gram_of_quad {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (M : Matrix ι ι F)
    (hM : ∀ x : ι → F, Q (M.mulVec x) = Q x) :
    M.transpose * LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) * M =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  have hpol : ∀ x y, QuadraticMap.polar Q (M.mulVec x) (M.mulVec y) =
      QuadraticMap.polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hM (x + y), hM x, hM y]
  apply (LinearEquiv.injective Matrix.toBilin')
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, ← j3b_polar_eq_dot Q (M.mulVec x) (M.mulVec y),
    ← j3b_polar_eq_dot Q x y]
  exact hpol x y

private lemma j3b_gram_of_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {s : GL ι K} (hs : s ∈ StatedOmega ⇑Φ) :
    Matrix.transpose (s : Matrix ι ι K) * LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) *
        (s : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) :=
  j3b_gram_of_quad Φ (s : Matrix ι ι K) (j3b_iso_of_mem_statedOmega Φ hs)

private lemma j3b_two_le_of_lt_mul {f d : ℕ} (hlt : f < f * d) : 2 ≤ d := by
  by_contra h
  have hd1 : d ≤ 1 := by omega
  have hle : f * d ≤ f := by simpa using Nat.mul_le_mul_left f hd1
  omega

private lemma j3b_blockDegree_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} {ε : Matrix ι ι K}
    (hε : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) ε)
    (hfix : ∀ s ∈ S, (s : Matrix ι ι K) * ε = ε) :
    blockDegree (Algebra.adjoin K (Units.val '' S)) ε = 1 := by
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  have hεA : IsPrimIdemIn A ε := hε
  have hmem : ∀ a ∈ A, ∃ c : K, a * ε = c • ε := by
    intro a ha
    refine Algebra.adjoin_induction (p := fun a _ => ∃ c : K, a * ε = c • ε)
      ?_ ?_ ?_ ?_ ha
    · intro x hx
      rcases hx with ⟨s, hs, rfl⟩
      exact ⟨1, by rw [hfix s hs, one_smul]⟩
    · intro r
      exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]⟩
    · intro x y hx hy hx' hy'
      rcases hx' with ⟨c, hc⟩
      rcases hy' with ⟨d, hd⟩
      exact ⟨c + d, by rw [add_mul, hc, hd, add_smul]⟩
    · intro x y hx hy hx' hy'
      rcases hx' with ⟨c, hc⟩
      rcases hy' with ⟨d, hd⟩
      refine ⟨d * c, ?_⟩
      calc (x * y) * ε = x * (y * ε) := by rw [mul_assoc]
        _ = x * (d • ε) := by rw [hd]
        _ = d • (x * ε) := by rw [mul_smul_comm]
        _ = d • (c • ε) := by rw [hc]
        _ = (d * c) • ε := by rw [smul_smul, mul_comm]
  have hmap : (Subalgebra.toSubmodule A).map (LinearMap.mulRight K ε) =
      Submodule.span K {ε} := by
    apply le_antisymm
    · intro b hb
      rcases hb with ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := hmem a ha
      rw [LinearMap.mulRight_apply, hc]
      exact Submodule.smul_mem' (Submodule.span K {ε}) c
        (Submodule.subset_span (Set.mem_singleton ε))
    · intro b hb
      rw [Submodule.mem_span_singleton] at hb
      obtain ⟨c, rfl⟩ := hb
      refine Submodule.mem_map.mpr ⟨c • 1, A.smul_mem A.one_mem c, ?_⟩
      rw [LinearMap.mulRight_apply, smul_mul_assoc, one_mul]
  change blockDegree A ε = 1
  unfold blockDegree
  rw [hmap]
  exact finrank_span_singleton hεA.2.2.1

theorem blockDeg_of_fieldExt
    {ι K U X : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2] [Group U]
    [Group X] {f : ℕ} (hK : Fintype.card K = 2 ^ f) (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (j : U →* GL ι K) (hj : Function.Injective j) (hrange : j.range = StatedOmega ⇑Φ)
    (ψ : U →* X) (hψ : Function.Injective ψ) (S : Set (GL ι K)) (hSU : ∀ s ∈ S, s ∈ j.range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup U} {ε e : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    (hJ' : IsComponentOf J' ⁅glBlockCentralizer j S ε, glBlockCentralizer j S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e) (heε : e * ε = e) {t : StatedLieTag}
    (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f) :
    (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin K (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin K (Units.val '' S)) e) ∨
      (e = ε ∧ blockDegree (Algebra.adjoin K (Units.val '' S)) e = 1 ∧ Matrix.rank e = 4) := by
  classical
  haveI : Finite K := Finite.of_fintype K
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  let G : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  have hGt : Matrix.transpose G = G := polarGram_transpose Φ
  have hGu : IsUnit G.det := polarGram_isUnit_det Φ hΦ
  have hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ := by
    intro s hs
    rw [← hrange]
    exact hSU s hs
  have hSiso : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι K) * G *
      (s : Matrix ι ι K) = G := by
    intro s hs
    exact j3b_gram_of_mem_statedOmega Φ (hSΩ s hs)
  have hεA : IsPrimAdjIdemIn (RingHom.id K) G A ε := hε
  have heA : IsPrimIdemIn A e := he
  rcases isPrimIdemIn_cases hGu hGt hS hSiso hεA heA heε with
    hee | ⟨hne, e', he', hne', hεe⟩
  · have hpe : IsPrimIdemIn A ε := by simpa [hee] using heA
    by_cases h1 : ∃ s ∈ S, (s : Matrix ι ι K) * ε ≠ ε
    · have h4 : 4 ≤ blockDegree A ε := by
        obtain ⟨d, m, E, hEfield, hEfintype, _, hcardE, _, hdeg, eG⟩ :=
          blockGroup_iso_Omega_unitary_S Φ hΦ h8 j hj hrange S hSU hS hodd hεA hpe h1
        letI : Field E := hEfield
        letI : Fintype E := hEfintype
        have hKd : Fintype.card K ^ d = 2 ^ (f * d) := by rw [hK, ← pow_mul]
        have hcardE' : Fintype.card E = (2 ^ (f * d)) ^ 2 := by simpa [hKd] using hcardE
        have eG' : ↥(glBlockCentralizer j S ε) ≃* ↥(GUFull m (2 ^ (f * d)) E) :=
          hKd ▸ eG.some
        have hlt : f < f * d := fieldExt_unitary_lt ψ hψ hJ' hcardE' eG' hFE
        have hd2 : 2 ≤ d := j3b_two_le_of_lt_mul hlt
        have hdegA : blockDegree A ε = 2 * d := hdeg
        rw [hdegA]
        omega
      left
      exact ⟨hee, by rw [hee]; exact h4⟩
    · push Not at h1
      have hbd1 : blockDegree A ε = 1 := j3b_blockDegree_one hpe h1
      have hrk4 : Matrix.rank ε = 4 := by
        obtain ⟨ι₁, hι₁fin, hι₁dec, Q₁, hcardι₁, hΦ₁ex, hdisj⟩ :=
          blockGroup_iso_Omega_one_S Φ hΦ h8 j hj hrange S hSU hS hodd hεA h1
        letI : Fintype ι₁ := hι₁fin
        letI : DecidableEq ι₁ := hι₁dec
        have hfin : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = 4 := by
          rcases hdisj with ⟨hGiso, _⟩ | ⟨_, hcard4, _, _⟩
          · obtain ⟨Φ₁, hΦ₁eq, hΦ₁nd⟩ := hΦ₁ex
            have hGiso' : ↥(glBlockCentralizer j S ε) ≃* ↥(StatedOmega ⇑Φ₁) :=
              hΦ₁eq.symm ▸ hGiso.some
            have hcard := fieldExt_one_card ψ hψ hJ' hK Φ₁ hΦ₁nd hGiso' hFE
            rw [← hcardι₁, hcard]
          · rw [← hcardι₁, hcard4]
        exact hfin
      right
      right
      refine ⟨hee, ?_⟩
      rw [hee]
      exact ⟨hbd1, hrk4⟩
  · have h2 : 2 ≤ blockDegree A e := by
      obtain ⟨d, m, E, hEfield, hEfintype, _, hcardE, _, hdeg, eG⟩ :=
        blockGroup_iso_Omega_linear_S Φ hΦ h8 j hj hrange S hSU hS hodd hεA heA he' hne'
          hεe
      letI : Field E := hEfield
      letI : Fintype E := hEfintype
      have hKd : Fintype.card K ^ d = 2 ^ (f * d) := by rw [hK, ← pow_mul]
      have hcardE' : Fintype.card E = 2 ^ (f * d) := by simpa [hKd] using hcardE
      have eG' : ↥(glBlockCentralizer j S ε) ≃* GL (Fin m) E := by
        simpa [hKd] using eG.some
      have hlt : f < f * d := fieldExt_lin_lt ψ hψ hJ' hcardE' eG' hFE
      have hd2 : 2 ≤ d := j3b_two_le_of_lt_mul hlt
      have hdegA : blockDegree A e = d := hdeg
      rw [hdegA]
      exact hd2
    right
    left
    exact ⟨hne, h2⟩

private lemma j3c_data_plus (k f : ℕ) (hk : 1 ≤ k) (hf : 1 ≤ f) {X : Type} [Group X]
    (ψ : ↥(spinGroup (ggOmQuadPlus k f)) →* X)
    (hker : ψ.ker ≤ Subgroup.center (↥(spinGroup (ggOmQuadPlus k f)))) :
    (QuadraticMap.polarBilin (ggOmQuadPlus k f)).Nondegenerate ∧
    8 ≤ Fintype.card (ggOmIdxPlus k) ∧
    Function.Injective (ggOmSpinPlus k f) ∧
    (ggOmSpinPlus k f).range = StatedOmega ⇑(ggOmQuadPlus k f) ∧
    Nat.card (GaloisField 2 f) = 2 ^ f ∧
    Function.Injective ψ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
  · simp only [ggOmIdxPlus, Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [← MonoidHom.ker_eq_bot_iff]
    simpa only [ggOmSpinPlus, ggOmQuadPlus] using
      Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero (GaloisField 2 f) 2)
  · simpa only [ggOmSpinPlus, ggOmQuadPlus, Spin.coe_quadPlus] using
      Spin.range_spinMatrix_quadPlus (n := k + 3) (K := GaloisField 2 f) (by omega)
  · exact GaloisField.card 2 f (by omega)
  · rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    intro u hu
    have hcenter : Subgroup.center (↥(spinGroup (ggOmQuadPlus k f))) = ⊥ := by
      simpa only [ggOmQuadPlus] using
        RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (n := k + 3)
          (K := GaloisField 2 f) (by omega)
    exact Subgroup.mem_bot.mp (hcenter ▸ hker hu)

theorem ggSixTCBlockDegPOmegaPlus_holds
    : GGSixTCBlockDegPOmegaPlus := by
  intro k f hk hf X _ _ ψ hker S hSU hS hodd J' ε e hε hJ' he heε hFE
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  obtain ⟨hΦ, h8, hj, hrange, hcFn, hψ⟩ := j3c_data_plus k f hk hf ψ hker
  have hcF : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hcFn
  exact blockDeg_of_fieldExt hcF (ggOmQuadPlus k f) hΦ h8 (ggOmSpinPlus k f) hj hrange
    ψ hψ S hSU hS hodd hε hJ' he heε hFE

private lemma j3c_data_minus (n f : ℕ) (hn : 4 ≤ n) (hf : 1 ≤ f) {X : Type} [Group X]
    (ψ : ↥(spinGroup (ggOmQuadMinus n f)) →* X)
    (hker : ψ.ker ≤ Subgroup.center (↥(spinGroup (ggOmQuadMinus n f)))) :
    (QuadraticMap.polarBilin (ggOmQuadMinus n f)).Nondegenerate ∧
    8 ≤ Fintype.card (ggOmIdxMinus n) ∧
    Function.Injective (ggOmSpinMinus n f) ∧
    (ggOmSpinMinus n f).range = StatedOmega ⇑(ggOmQuadMinus n f) ∧
    Nat.card (GaloisField 2 f) = 2 ^ f ∧
    Function.Injective ψ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f)
      (minusCoeffs_irr 2 f)
  · simp only [ggOmIdxMinus, Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [← MonoidHom.ker_eq_bot_iff]
    simpa only [ggOmSpinMinus, ggOmQuadMinus] using
      Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 f)
        (CharP.cast_eq_zero (GaloisField 2 f) 2)
  · simpa only [ggOmSpinMinus, ggOmQuadMinus, Spin.coe_quadMinus] using
      Spin.range_spinMatrix_quadMinus (n := n) (K := GaloisField 2 f)
        (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) hn (minusCoeffs_irr 2 f)
  · exact GaloisField.card 2 f (by omega)
  · rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    intro u hu
    have hcenter : Subgroup.center (↥(spinGroup (ggOmQuadMinus n f))) = ⊥ := by
      simpa only [ggOmQuadMinus] using
        CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (F := GaloisField 2 f)
          hn (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) (minusCoeffs_irr 2 f)
    exact Subgroup.mem_bot.mp (hcenter ▸ hker hu)

theorem ggSixTCBlockDegPOmegaMinus_holds
    : GGSixTCBlockDegPOmegaMinus := by
  intro n f hn hf X _ _ ψ hker S hSU hS hodd J' ε e hε hJ' he heε hFE
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  obtain ⟨hΦ, h8, hj, hrange, hcFn, hψ⟩ := j3c_data_minus n f hn hf ψ hker
  have hcF : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hcFn
  exact blockDeg_of_fieldExt hcF (ggOmQuadMinus n f) hΦ h8 (ggOmSpinMinus n f) hj hrange
    ψ hψ S hSU hS hodd hε hJ' he heε hFE

end CFSG.StandardType.TableC

end
