module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaLeafDefs
public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockDegree
public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockRank
public import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaTrivialBlock
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaNoFieldExt
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaMarking
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.StandardType.TableC CFSG.StandardType.ClassicalPosition
open CFSG.RankThree.Classical2 CFSG.ComponentClassification.UnbalancedCatalog
open Module QuadraticMap

section POmegaPlus

@[expose] def GGSixTCDstarPOmegaPlus
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (k f : ℕ) (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixTCPos .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x →
    ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1 ∧
      ∃ d ∈ D, d ≠ 1 ∧ ∃ K : Subgroup X,
        IsComponentOf K (G₀ ⊓ Subgroup.centralizer {d}) ∧ J ≤ K ∧
        (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
          OmNonsplit.OmModel F K) ∧
        (∃ r ∈ K, ∀ l ∈ K, x⁻¹ * l * x = r⁻¹ * l * r) ∧
        (d ∈ Subgroup.zpowers x → K = L) ∧ (d ∉ Subgroup.zpowers x → K ≠ J)

theorem ggSixTCKnown_POmegaPlus_of_dstar
    (h : GGSixTCDstarPOmegaPlus) : GGSixTCKnownAt .POmegaPlus := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos
  exfalso
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by
    have := (hpos.model.admissible).2.2
    omega⟩
  obtain ⟨hq1, hq2, d, hd, hd1, K, hK, hJK, ⟨F, _, _, _, hF, hM⟩, hinn, hKL, hKJ⟩ :=
    h X k f ψ p G₀ B₁ D J L x hpos
  by_cases hdx : d ∈ Subgroup.zpowers x
  · rw [hKL hdx] at hM
    exact not_largeEvenSplit_marking_omModel hF hM hpos.prime hpos.ne_two hq1 hq2 hpos.L_split
  · exact OmNonsplit.not_ggNbrClauseFiveMarking_of_omModel hF hM hpos.prime hpos.ne_two hq1 hq2
      hinn (hpos.nbr d hd hdx K hK hJK (hKJ hdx)).2

private lemma o5a_spinMatrix_injective (F : Type) [Field F] [CharP F 2] (n : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadPlus n F)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)

private lemma o5a_odd_orderOf_of_pow_prime {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : G} (hs : s ^ p = 1) : Odd (orderOf s) := by
  have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf s) hdvd with h1 | hp'
  · rw [h1]
    exact odd_one
  · rw [hp']
    exact hp.odd_of_ne_two hp2

private lemma o5b_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ {a b : Matrix ι ι F}, a ∈ Algebra.adjoin F (Units.val '' S) →
      b ∈ Algebra.adjoin F (Units.val '' S) → a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix ι ι F) * (s' : Matrix ι ι F) = (s' : Matrix ι ι F) * (s : Matrix ι ι F)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm F hcommS
  intro a b ha hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin F (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin F (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma o5b_prime_ne_zero {F : Type} [Field F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (p : F) ≠ 0 := by
  intro hzero
  have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp hzero
  exact hp2 ((hp.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd)

private lemma o5b_rank_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G M : Matrix ι ι F} (hG : IsUnit G.det) :
    Matrix.rank (formAdj (RingHom.id F) G M) = Matrix.rank M := by
  have h1 : Matrix.rank (G⁻¹ * Matrix.transpose M * G) =
      Matrix.rank (G⁻¹ * Matrix.transpose M) :=
    Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose M) hG
  have h2 : Matrix.rank (G⁻¹ * Matrix.transpose M) = Matrix.rank (Matrix.transpose M) :=
    Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose M)
      (Matrix.isUnit_nonsing_inv_det G hG)
  have hmap : M.map (RingHom.id F) = M := Matrix.map_id M
  rw [formAdj, hmap, h1, h2, Matrix.rank_transpose]

private lemma o5b_rank_add_idem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e f : Matrix ι ι F} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    Matrix.rank (e + f) = Matrix.rank e + Matrix.rank f := by
  have hee : e * e = e := he.eq
  have hff : f * f = f := hf.eq
  have hsup : LinearMap.range ((e + f).mulVecLin) =
      LinearMap.range e.mulVecLin ⊔ LinearMap.range f.mulVecLin := by
    apply le_antisymm
    · rintro w ⟨v, hv⟩
      rw [Matrix.mulVecLin_apply, Matrix.add_mulVec] at hv
      rw [← hv]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply e v⟩))
        (Submodule.mem_sup_right (LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply f v⟩))
    · refine sup_le ?_ ?_
      · rintro w ⟨v, hv⟩
        refine LinearMap.mem_range.mpr ⟨e.mulVec v, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, hee, hfe, Matrix.zero_mulVec, add_zero]
        rw [Matrix.mulVecLin_apply] at hv
        exact hv
      · rintro w ⟨v, hv⟩
        refine LinearMap.mem_range.mpr ⟨f.mulVec v, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, hff, hef, Matrix.zero_mulVec, zero_add]
        rw [Matrix.mulVecLin_apply] at hv
        exact hv
  have hker : LinearMap.range f.mulVecLin ≤ LinearMap.ker e.mulVecLin := by
    rintro w ⟨v, hv⟩
    rw [← hv, LinearMap.mem_ker]
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hef]
    simp
  have h_inf : LinearMap.range e.mulVecLin ⊓ LinearMap.range f.mulVecLin = ⊥ := by
    apply le_antisymm _ bot_le
    rintro w ⟨hwe, hwf⟩
    rw [Submodule.mem_bot]
    have hw0 : e.mulVec w = 0 := by
      have h := hker hwf
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h
    obtain ⟨v, hv⟩ := hwe
    have hweq : w = e.mulVec w := by
      rw [← hv]
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, hee]
    rw [hweq]
    exact hw0
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range e.mulVecLin) (LinearMap.range f.mulVecLin)
  rw [h_inf, finrank_bot, add_zero] at hfin
  change Module.finrank F (LinearMap.range ((e + f).mulVecLin)) =
    Module.finrank F (LinearMap.range e.mulVecLin) +
      Module.finrank F (LinearMap.range f.mulVecLin)
  rw [hsup]
  exact hfin

private lemma o5c_fixIdem_mem_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {s : GL ι F} (hs : s ∈ S) {p : ℕ} :
    fixIdem p s ∈ Algebra.adjoin F (Units.val '' S) := by
  unfold fixIdem
  refine Subalgebra.smul_mem _ ?_ _
  refine Subalgebra.sum_mem _ ?_
  intro i _
  have hsA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin (show (s : Matrix ι ι F) ∈ Units.val '' S from ⟨s, hs, rfl⟩)
  exact Subalgebra.pow_mem _ hsA i

private lemma o5c_centralizer_comap_eq {U X : Type} [Group U] [Group X]
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j)
    (ψ : U →* X) (hψ : Function.Injective ψ)
    (s : U) (b : X) (hL : IsGLLift j ψ (j s) b) :
    Subgroup.comap ψ (Subgroup.centralizer ({b} : Set X)) =
      Subgroup.centralizer ({s} : Set U) := by
  ext u
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    obtain ⟨u', hu'j, hu'psi⟩ := hL u
    have hconj : b⁻¹ * ψ u * b = ψ u := by
      calc b⁻¹ * ψ u * b = b⁻¹ * (ψ u * b) := by group
        _ = b⁻¹ * (b * ψ u) := by rw [h]
        _ = ψ u := by group
    have hpsi : ψ u' = ψ u := by rw [← hu'psi, hconj]
    have hu' : u' = u := hψ hpsi
    have hju : j s * j u * (j s)⁻¹ = j u := by rw [← hu'j, hu']
    have h2 : j s * j u = j u * j s := by
      calc j s * j u = j s * j u * (j s)⁻¹ * j s := by group
        _ = j u * j s := by rw [hju]
    apply hj
    simp only [map_mul]
    exact h2.symm
  · intro h
    obtain ⟨u', hu'j, hu'psi⟩ := hL u
    have hju : j u' = j u := by
      rw [hu'j]
      have h' : j u * j s = j s * j u := by simpa only [map_mul] using congrArg j h
      rw [← h', mul_assoc, mul_inv_cancel, mul_one]
    have hu' : u' = u := hj hju
    have hconj : b⁻¹ * ψ u * b = ψ u := by simpa [hu'] using hu'psi
    calc ψ u * b = b * (b⁻¹ * ψ u * b) := by group
      _ = b * ψ u := by rw [hconj]

private lemma o5c_assembly_quasisimple_of_cfsg {G : Type} [Group G]
    (h : CFSG.IsQuasisimple G) : CFSG.Assembly.IsQuasisimple G :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem ggSixTCDstarPOmegaPlus_of_leaves
    (hL1 : GGSixTCLiftPOmegaPlus) (hL2 : GGSixTCBlockDegPOmegaPlus)
    (hA : GGSixTCCaseAPOmegaPlus) :
    GGSixTCDstarPOmegaPlus := by
  intro X _ _ k f ψ p G₀ B₁ D J L x hpos
  have hf : 1 ≤ f := (hpos.model.admissible).2.1
  have hk : 1 ≤ k := by
    have := (hpos.model.admissible).2.2
    omega
  have hcF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let Q := ggOmQuadPlus k f
  let j := ggOmSpinPlus k f
  let G := LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
  have hGu : IsUnit G.det := polarGram_isUnit_det Q hQnd
  have hGt : Matrix.transpose G = G := polarGram_transpose Q
  have hj : Function.Injective j := by
    simpa only [j, ggOmSpinPlus, ggOmQuadPlus] using
      o5a_spinMatrix_injective (GaloisField 2 f) (k + 3)
  have hrange : (Spin.spinAction Q).range = orthDerived Q := by
    simpa only [Q, ggOmQuadPlus, orthDerived] using
      Spin.range_spinAction_quadPlus_eq_commutator (n := k + 3) (K := GaloisField 2 f) (by omega)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    intro u hu
    have hcenter : Subgroup.center (ggU .POmegaPlus (k + 3) f).K = ⊥ :=
      RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (n := k + 3)
        (K := GaloisField 2 f) (by omega)
    exact Subgroup.mem_bot.mp (hcenter ▸ hpos.ker_le hu)
  obtain ⟨ℓ, hℓ, hℓp, J', hJ', hJmap⟩ := hL1 k f ψ p G₀ B₁ D J L x hpos
  let S : Set (GL (ggOmIdxPlus k) (GaloisField 2 f)) := Set.range fun d : ↥D => j (ℓ d)
  have hSU : ∀ s ∈ S, s ∈ j.range := by
    rintro s ⟨d, rfl⟩
    exact ⟨ℓ d, rfl⟩
  have hSiso : ∀ s ∈ S, Matrix.transpose (s : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k)
      (GaloisField 2 f)) * G * (s : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k)
      (GaloisField 2 f)) = G := by
    rintro s ⟨d, rfl⟩
    exact spinMatrix_isometry Q (ℓ d)
  have hDcomm : ∀ d d' : ↥D, Commute d d' := by
    intro d d'
    have h := (hpos.elemAbelian.1).is_comm.comm ⟨d, hpos.D_le d.2⟩ ⟨d', hpos.D_le d'.2⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val h
  have hScomm : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    rintro s ⟨d, rfl⟩ s' ⟨d', rfl⟩
    exact ((hDcomm d d').map ℓ).map j
  have hSp : ∀ s ∈ S, s ^ p = 1 := by
    rintro s ⟨d, rfl⟩
    rw [← map_pow, hℓp d, map_one]
  have hSodd : ∀ s ∈ S, Odd (orderOf s) := by
    intro s hs
    exact o5a_odd_orderOf_of_pow_prime hpos.prime hpos.ne_two (hSp s hs)
  obtain ⟨ε, hε, hJε⟩ := exists_isComponentOf_glBlockCentralizer_POmegaPlus (k + 3)
    (GaloisField 2 f) (by omega) S hScomm hJ'
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus k f S hSU hScomm hε
  have hFE : GGSixLSevenFieldExtCase (J'.map ψ) .POmegaPlus f := by
    rw [hJmap]
    exact hpos.fieldExt
  have hdeg := hL2 k f hk hf ψ hpos.ker_le S hSU hScomm hSodd hε hJε he heε hFE
  have hL3 := blockDegree_trivial_or_eq_orderOf_gram (GaloisField 2 f) hpos.prime hpos.ne_two G
    hGt hGu hSiso hScomm hSp he
  set c := orderOf (((Nat.card (GaloisField 2 f) : ℕ)) : ZMod p) with hc
  have hnt : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = c ∧
      ((e = ε ∧ 4 ≤ c) ∨ (e ≠ ε ∧ 3 ≤ c)) := by
    rcases hL3 with ⟨htriv, h1, -⟩ | ⟨-, h1, h2⟩
    · exfalso
      rcases hdeg with ⟨-, h⟩ | ⟨-, h⟩ | ⟨hee, -, hrk⟩
      · omega
      · omega
      · exact hA k f ψ p G₀ B₁ D J L x hpos ℓ S rfl hℓ hℓp J' e hJ' hJmap hFE
          (by rw [hee]; exact hJε) he htriv hrk
    · refine ⟨h1, ?_⟩
      rcases hcase with hee | ⟨hne, hnadj, -⟩
      · left
        refine ⟨hee, ?_⟩
        rcases hdeg with ⟨-, h⟩ | ⟨hne, -⟩ | ⟨-, hd1, -⟩
        · omega
        · exact absurd hee hne
        · exfalso
          have hadj : formAdj (RingHom.id (GaloisField 2 f)) G e = e := by
            rw [hee]
            exact hε.2.2.2.1
          obtain ⟨r, hr⟩ := h2.mp hadj
          omega
      · right
        refine ⟨hne, ?_⟩
        rcases hdeg with ⟨hee, -⟩ | ⟨-, h⟩ | ⟨hee, -, -⟩
        · exact absurd hee hne
        · have hodd : ¬ Even c := fun hev => hnadj (h2.mpr hev)
          have : c ≠ 2 := fun h2' => hodd (h2' ▸ even_two)
          omega
        · exact absurd hee hne
  have hc3 : 3 ≤ c := by
    rcases hnt.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hq1 : ¬ p ∣ 2 ^ f - 1 := by
    intro h
    have hc1 : c = 1 := by
      rw [hc, hcF]
      exact orderOf_eq_one_iff.mpr (by
        have h2f : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        have hzero : (((2 ^ f - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
        rw [Nat.cast_sub h2f, Nat.cast_one, sub_eq_zero] at hzero
        exact hzero)
    omega
  have hq2 : ¬ p ∣ 2 ^ f + 1 := by
    intro h
    have hzero : (((2 ^ f + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
    have hneg : (((2 ^ f : ℕ)) : ZMod p) = -1 := by
      rw [Nat.cast_add, Nat.cast_one] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    have hsq : ((((2 ^ f : ℕ)) : ZMod p)) ^ 2 = 1 := by
      rw [hneg]
      ring
    have hdvd : c ∣ 2 := by
      rw [hc, hcF]
      exact orderOf_dvd_of_pow_eq_one hsq
    have hle : c ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨d, hd1, hdfix⟩ := exists_ne_one_fix_blockIdem_gl (GaloisField 2 f) hpos.prime
    hpos.ne_two (D := ↥D) hpos.card_D (j.comp ℓ)
    (fun d => by rw [MonoidHom.comp_apply, ← map_pow, hℓp d, map_one]) hDcomm he
  have hfixε : ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
      Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) * ε = ε := by
    have hSUiso : ∀ s ∈ S, Matrix.transpose ((s :
        Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) * G *
        (s : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) = G := by
      intro s hs
      simpa [Matrix.map_id] using hSiso s hs
    have hs_mem : (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) ∈ S :=
      Set.mem_range_self d
    have hdfix' : ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
        Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) * e = e := hdfix
    rcases hcase with hee | ⟨-, -, hεeq⟩
    · rw [← hee]
      exact hdfix'
    · rw [hεeq, Matrix.mul_add, hdfix']
      have heStar : ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
          Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) *
          formAdj (RingHom.id (GaloisField 2 f)) G e =
          formAdj (RingHom.id (GaloisField 2 f)) G e := by
        have h1 := congrArg (formAdj (RingHom.id (GaloisField 2 f)) G) hdfix'
        rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hGu] at h1
        rw [Geo.formAdj_eq_inv_of_isometry (RingHom.id (GaloisField 2 f)) hGu
          (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))
          (hSUiso (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) hs_mem)] at h1
        have hcomm : Commute (((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
            Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)))
            (formAdj (RingHom.id (GaloisField 2 f)) G e) :=
          o5b_adjoin_comm hScomm
            (Algebra.subset_adjoin (show ((j (ℓ d) : GL (ggOmIdxPlus k)
                (GaloisField 2 f)) : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k)
                (GaloisField 2 f)) ∈ Units.val '' S from ⟨_, hs_mem, rfl⟩))
            (Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hGu hSUiso he.1)
        have h2 : formAdj (RingHom.id (GaloisField 2 f)) G e *
            ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
              Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) =
            formAdj (RingHom.id (GaloisField 2 f)) G e := by
          have h3 := congrArg (fun x : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k)
              (GaloisField 2 f) =>
              x * ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
                Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f))) h1
          have h3' : formAdj (RingHom.id (GaloisField 2 f)) G e =
              formAdj (RingHom.id (GaloisField 2 f)) G e *
              ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
                Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) := by
            have hsinv : (((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))⁻¹ :
                GL (ggOmIdxPlus k) (GaloisField 2 f)) :
                Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) *
                ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
                Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) = 1 := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
            rw [Matrix.mul_assoc, hsinv, Matrix.mul_one] at h3
            exact h3
          exact h3'.symm
        exact hcomm.eq.trans h2
      rw [heStar]
  have hε₀ε : fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) * ε = ε := by
    have hc : (p : GaloisField 2 f) ≠ 0 := o5b_prime_ne_zero hpos.prime hpos.ne_two
    have hpow : ∀ i : ℕ,
        (((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) :
          Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) ^ i * ε = ε := by
      intro i
      induction i with
      | zero => rw [pow_zero, Matrix.one_mul]
      | succ i ih => rw [pow_succ, Matrix.mul_assoc, hfixε, ih]
    have hsum : (∑ i ∈ Finset.range p,
        (((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) :
          Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) ^ i) * ε =
        (p : GaloisField 2 f) • ε := by
      rw [Finset.sum_mul]
      simp only [hpow]
      rw [Finset.sum_const, Finset.card_range]
      exact (Nat.cast_smul_eq_nsmul (GaloisField 2 f) p ε).symm
    unfold fixIdem
    rw [Matrix.smul_mul, hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h8 : 8 ≤ Matrix.rank (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) := by
    have hSUiso : ∀ s ∈ S, Matrix.transpose ((s :
        Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) * G *
        (s : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) = G := by
      intro s hs
      simpa [Matrix.map_id] using hSiso s hs
    have hε₀e : fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) * e = e := by
      have hc : (p : GaloisField 2 f) ≠ 0 := o5b_prime_ne_zero hpos.prime hpos.ne_two
      have hdfix' : ((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) :
          Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) * e = e := hdfix
      have hpow : ∀ i : ℕ,
          (((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) :
            Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) ^ i * e = e := by
        intro i
        induction i with
        | zero => rw [pow_zero, Matrix.one_mul]
        | succ i ih => rw [pow_succ, Matrix.mul_assoc, hdfix', ih]
      have hsum : (∑ i ∈ Finset.range p,
          (((j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) :
            Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) ^ i) * e =
          (p : GaloisField 2 f) • e := by
        rw [Finset.sum_mul]
        simp only [hpow]
        rw [Finset.sum_const, Finset.card_range]
        exact (Nat.cast_smul_eq_nsmul (GaloisField 2 f) p e).symm
      unfold fixIdem
      rw [Matrix.smul_mul, hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hre : Matrix.rank e ≤
        Matrix.rank (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) := by
      calc Matrix.rank e = Matrix.rank
            (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) * e) := by
              rw [hε₀e]
        _ ≤ Matrix.rank (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) :=
              Matrix.rank_mul_le_left _ _
    have hrε : Matrix.rank ε ≤
        Matrix.rank (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) := by
      calc Matrix.rank ε = Matrix.rank
            (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) * ε) := by
              rw [hε₀ε]
        _ ≤ Matrix.rank (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) :=
              Matrix.rank_mul_le_left _ _
    have hrk : 2 * c ≤ Matrix.rank e := by
      have h := two_mul_blockDegree_le_rank_gram (GaloisField 2 f) G hGt hGu j hj S hSiso
        hScomm hSodd hε hJε he heε
      rwa [hnt.1] at h
    rcases hnt.2 with ⟨hee, h4c⟩ | ⟨hne, h3c⟩
    · calc 8 ≤ 2 * c := by omega
        _ ≤ Matrix.rank e := hrk
        _ = Matrix.rank ε := by rw [hee]
        _ ≤ Matrix.rank (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) := hrε
    · have hεeq : ε = e + formAdj (RingHom.id (GaloisField 2 f)) G e := by
        rcases hcase with hee | ⟨-, -, hεeq⟩
        · exact absurd hee hne
        · exact hεeq
      have heStar_prim : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
          (formAdj (RingHom.id (GaloisField 2 f)) G e) :=
        isPrimIdemIn_formAdj_gram (GaloisField 2 f) G hGt hGu hSiso hScomm he
      have hnadj : formAdj (RingHom.id (GaloisField 2 f)) G e ≠ e := by
        rcases hcase with hee | ⟨-, hnadj, -⟩
        · exact absurd hee hne
        · exact hnadj
      have hcomm_e : e * formAdj (RingHom.id (GaloisField 2 f)) G e =
          formAdj (RingHom.id (GaloisField 2 f)) G e * e :=
        o5b_adjoin_comm hScomm he.1
          (Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hGu hSUiso he.1)
      have hprod : e * formAdj (RingHom.id (GaloisField 2 f)) G e = 0 := by
        by_contra h0
        have hidem : IsIdempotentElem (e * formAdj (RingHom.id (GaloisField 2 f)) G e) :=
          IsIdempotentElem.mul_of_commute hcomm_e he.2.1 heStar_prim.2.1
        have hmul : (e * formAdj (RingHom.id (GaloisField 2 f)) G e) * e =
            e * formAdj (RingHom.id (GaloisField 2 f)) G e := by
          rw [Matrix.mul_assoc, ← hcomm_e, ← Matrix.mul_assoc, he.2.1.eq]
        have hmem : e * formAdj (RingHom.id (GaloisField 2 f)) G e ∈
            Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
          Subalgebra.mul_mem _ he.1
            (Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hGu hSUiso he.1)
        rcases he.2.2.2 _ hmem hidem hmul with hz | heq
        · exact h0 hz
        · rcases heStar_prim.2.2.2 e he.1 he.2.1 heq with hz' | heq'
          · exact he.2.2.1 hz'
          · exact hnadj heq'.symm
      have hrank_add : Matrix.rank (e + formAdj (RingHom.id (GaloisField 2 f)) G e) =
          Matrix.rank e + Matrix.rank (formAdj (RingHom.id (GaloisField 2 f)) G e) :=
        o5b_rank_add_idem he.2.1 heStar_prim.2.1 hprod (by rw [← hcomm_e]; exact hprod)
      have hrank_adj : Matrix.rank (formAdj (RingHom.id (GaloisField 2 f)) G e) =
          Matrix.rank e := o5b_rank_formAdj (G := G) (M := e) hGu
      calc 8 ≤ 4 * c := by omega
        _ = 2 * (2 * c) := by ring
        _ ≤ 2 * Matrix.rank e := Nat.mul_le_mul_left 2 hrk
        _ = Matrix.rank e +
              Matrix.rank (formAdj (RingHom.id (GaloisField 2 f)) G e) := by
              rw [hrank_adj]; ring
        _ = Matrix.rank (e + formAdj (RingHom.id (GaloisField 2 f)) G e) := hrank_add.symm
        _ = Matrix.rank ε := by rw [hεeq]
        _ ≤ Matrix.rank (fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) := hrε
  obtain ⟨W, _, _, _, R, hRnd, hWdim, ⟨eqv⟩, hnorm, hinner⟩ :=
    trivialBlock_orth Q hQnd hj hrange hpos.prime hpos.ne_two (ℓ d) (hℓp d) h8
  have hRdim : 8 ≤ finrank (GaloisField 2 f) W := by
    rw [hWdim]
    exact h8
  have hJ'le : J' ≤ trivBlockOrth Q p (ℓ d) := by
    have hs_mem : j (ℓ d) ∈ S := Set.mem_range_self d
    have hεε₀ : ε * fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) = ε := by
      rw [o5b_adjoin_comm hScomm hε.1 (o5c_fixIdem_mem_adjoin (p := p) hs_mem)]
      exact hε₀ε
    have h1mε0 : (1 - ε) *
        (1 - fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) =
        1 - fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hεε₀]
      abel
    have hGtriv : glBlockCentralizer j S ε ≤ trivBlockOrth Q p (ℓ d) := by
      intro g hg
      rw [glBlockCentralizer, Subgroup.mem_comap] at hg
      obtain ⟨hgc, hgf⟩ := Subgroup.mem_inf.mp hg
      have hgfeq : (j g : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) *
          (1 - ε) = 1 - ε := hgf
      rw [trivBlockOrth, glBlockCentralizer, Subgroup.mem_comap]
      refine ⟨?_, ?_⟩
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact Subgroup.mem_centralizer_iff.mp hgc (j (ℓ d)) hs_mem
      · calc (j g : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) *
              (1 - fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)))
            = (j g : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) *
                ((1 - ε) * (1 - fixIdem p
                  (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)))) := by rw [h1mε0]
          _ = ((j g : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) *
                (1 - ε)) * (1 - fixIdem p
                  (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) := by
              rw [Matrix.mul_assoc]
          _ = (1 - ε) * (1 - fixIdem p
                (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f))) := by rw [hgfeq]
          _ = 1 - fixIdem p (j (ℓ d) : GL (ggOmIdxPlus k) (GaloisField 2 f)) := h1mε0
    have hGG : ⁅glBlockCentralizer j S ε, glBlockCentralizer j S ε⁆ ≤
        glBlockCentralizer j S ε := by
      rw [Subgroup.commutator_le]
      intro g1 h1 g2 h2
      show g1 * g2 * g1⁻¹ * g2⁻¹ ∈ glBlockCentralizer j S ε
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
    exact hJε.1.trans (hGG.trans hGtriv)
  have hQtb : CFSG.Assembly.IsQuasisimple ↥(trivBlockOrth Q p (ℓ d)) := by
    obtain ⟨m, hm⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hRnd
    have hm4 : 4 ≤ m := by omega
    have hdim : finrank (GaloisField 2 f) W = 2 * m := by omega
    have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim R hRnd hm4 hdim
    exact o5c_assembly_quasisimple_of_cfsg
      (CFSG.IsQuasisimple.of_mulEquiv eqv
        (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hRnd hT))
  have hK'comp : IsComponentOf (trivBlockOrth Q p (ℓ d))
      (Subgroup.centralizer ({ℓ d} : Set ↥(spinGroup Q))) := by
    have hle : trivBlockOrth Q p (ℓ d) ≤
        Subgroup.centralizer ({ℓ d} : Set ↥(spinGroup Q)) := by
      intro g hg
      rw [trivBlockOrth, glBlockCentralizer, Subgroup.mem_comap] at hg
      have hgc := (Subgroup.mem_inf.mp hg).1
      rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
      apply hj
      simpa only [map_mul] using hgc
    exact ⟨hle, IsSubnormal.step hle hnorm
      (IsSubnormal.refl (Subgroup.centralizer ({ℓ d} : Set ↥(spinGroup Q)))), hQtb⟩
  have hmap : (Subgroup.centralizer ({ℓ d} : Set ↥(spinGroup Q))).map ψ =
      G₀ ⊓ Subgroup.centralizer ({((d : ↥D) : X)} : Set X) := by
    rw [← o5c_centralizer_comap_eq j hj ψ hψ (ℓ d) ((d : ↥D) : X) (hℓ d)]
    exact (Subgroup.map_comap_eq ψ
      (Subgroup.centralizer ({((d : ↥D) : X)} : Set X))).trans
      (by rw [hpos.range_eq])
  have hKcomp : IsComponentOf ((trivBlockOrth Q p (ℓ d)).map ψ)
      (G₀ ⊓ Subgroup.centralizer {((d : ↥D) : X)}) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hK'comp ψ hψ
    convert h using 1
    · rfl
    · exact hmap.symm
  have heK : Nonempty (↥((trivBlockOrth Q p (ℓ d)).map ψ) ≃* ↥(orthDerived R)) :=
    ⟨(Subgroup.equivMapOfInjective (trivBlockOrth Q p (ℓ d)) ψ hψ).symm.trans eqv⟩
  obtain ⟨eK⟩ := heK
  refine ⟨hq1, hq2, ((d : ↥D) : X), d.2, fun h => hd1 (Subtype.ext h),
    (trivBlockOrth Q p (ℓ d)).map ψ, hKcomp, ?_,
    ⟨GaloisField 2 f, inferInstance, inferInstance, inferInstance, hcF,
      Or.inl ⟨W, inferInstance, inferInstance, inferInstance, R, hRnd, by omega,
        fun h => by have := h.1; omega, ⟨eK⟩⟩⟩, ?_, ?_, ?_⟩
  · rw [← hJmap]
    exact Subgroup.map_mono hJ'le
  · have hcomm_xd : Commute ((ℓ ⟨x, hpos.x_mem⟩)⁻¹) (ℓ d) :=
      ((hDcomm ⟨x, hpos.x_mem⟩ d).map ℓ).inv_left
    have hgp : ((ℓ ⟨x, hpos.x_mem⟩)⁻¹) ^ p = 1 := by
      rw [inv_pow, hℓp ⟨x, hpos.x_mem⟩, inv_one]
    obtain ⟨r, hr_mem, hr⟩ := hinner ((ℓ ⟨x, hpos.x_mem⟩)⁻¹) hcomm_xd hgp
    let jT : (ggU .POmegaPlus (k + 3) f).K →* GL (ggOmIdxPlus k) (GaloisField 2 f) := j
    have hjT : Function.Injective jT := hj
    let gT : (ggU .POmegaPlus (k + 3) f).K := ℓ ⟨x, hpos.x_mem⟩
    let rT : (ggU .POmegaPlus (k + 3) f).K := r
    refine ⟨ψ rT, Subgroup.mem_map.mpr ⟨r, hr_mem, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨u, hu_mem, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨u', hu'j, hu'psi⟩ := hℓ ⟨x, hpos.x_mem⟩ u
    have hu'jT : jT u' = jT gT * jT u * (jT gT)⁻¹ := hu'j
    have hrT : gT * u * gT⁻¹ = rT⁻¹ * u * rT := by
      have h := hr u hu_mem
      rw [inv_inv] at h
      exact h
    have hu'eq : u' = rT⁻¹ * u * rT := by
      apply hjT
      calc jT u' = jT gT * jT u * (jT gT)⁻¹ := hu'jT
        _ = jT (rT⁻¹ * u * rT) := by
              simpa only [map_mul, map_inv] using congrArg jT hrT
    calc x⁻¹ * ψ u * x = ψ u' := hu'psi
      _ = ψ (rT⁻¹ * u * rT) := by rw [hu'eq]
      _ = (ψ rT)⁻¹ * ψ u * ψ rT := by simp only [map_mul, map_inv]
  · intro hdx
    have hdxp : (((d : ↥D) : X)) ^ p = 1 := hpos.elemAbelian.2 _ (hpos.D_le d.2)
    have hxp : x ^ p = 1 := hpos.elemAbelian.2 x (hpos.D_le hpos.x_mem)
    have hdx1 : ((d : ↥D) : X) ≠ 1 := fun h => hd1 (Subtype.ext h)
    haveI : Fact p.Prime := ⟨hpos.prime⟩
    have hord_dx : orderOf ((d : ↥D) : X) = p := orderOf_eq_prime hdxp hdx1
    have hord_x : orderOf x = p := orderOf_eq_prime hxp hpos.x_ne_one
    have hzp_le : Subgroup.zpowers ((d : ↥D) : X) ≤ Subgroup.zpowers x :=
      Subgroup.zpowers_le_of_mem hdx
    have hzp : Subgroup.zpowers ((d : ↥D) : X) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hzp_le (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord_dx, hord_x])
    have hcent_dx : Subgroup.centralizer ({((d : ↥D) : X)} : Set X) =
        Subgroup.centralizer (Subgroup.zpowers ((d : ↥D) : X) : Set X) := by
      apply le_antisymm
      · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp hy
      · apply Subgroup.centralizer_le
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_zpowers ((d : ↥D) : X)
    have hcent_x : Subgroup.centralizer ({x} : Set X) =
        Subgroup.centralizer (Subgroup.zpowers x : Set X) := by
      apply le_antisymm
      · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp hy
      · apply Subgroup.centralizer_le
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_zpowers x
    have hcent_eq : Subgroup.centralizer ({((d : ↥D) : X)} : Set X) =
        Subgroup.centralizer ({x} : Set X) := by
      rw [hcent_dx, hzp, ← hcent_x]
    have hcentN : G₀ ⊓ Subgroup.centralizer ({((d : ↥D) : X)} : Set X) =
        G₀ ⊓ Subgroup.centralizer ({x} : Set X) := by rw [hcent_eq]
    have hJK : J ≤ (trivBlockOrth Q p (ℓ d)).map ψ := by
      rw [← hJmap]
      exact Subgroup.map_mono hJ'le
    have hJq : CFSG.Assembly.IsQuasisimple ↥J := hpos.J_comp.2.2
    rw [hcentN] at hKcomp
    exact CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJq hKcomp
      hpos.L_comp hJK hpos.J_le_L
  · intro _ hKJ
    exact not_fieldExtCase_of_mulEquiv_orthDerived hcF hRnd hRdim
      ((MulEquiv.subgroupCongr hKJ.symm).trans eK) hpos.fieldExt

end POmegaPlus

end CFSG.StandardType

end
