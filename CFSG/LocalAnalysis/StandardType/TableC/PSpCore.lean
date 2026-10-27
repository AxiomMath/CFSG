module

public import CFSG.LocalAnalysis.StandardType.TableC.Extract
public import CFSG.LocalAnalysis.StandardType.TableC.PSpLeafDefs
public import CFSG.LocalAnalysis.StandardType.TableC.PSpLift
public import CFSG.LocalAnalysis.StandardType.TableC.PSpBlockDegreeHolds
public import CFSG.LocalAnalysis.StandardType.TableC.PSpBlockDegree
public import CFSG.LocalAnalysis.StandardType.TableC.PSpBlockRank
public import CFSG.LocalAnalysis.StandardType.TableC.PSpTrivialBlock
public import CFSG.LocalAnalysis.StandardType.TableC.PSpNoFieldExt
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClMark
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (StatedSp)
open CFSG.StandardType.TableC CFSG.StandardType.ClassicalPosition

section PSp

theorem not_largeEvenSplit_marking_sp
    {G : Type} [Group G] {K' : Subgroup G} {s f : ℕ}
    {F' : Type} [Field F'] (hF' : Nat.card F' = 2 ^ f) (e : ↥K' ≃* StatedSp s F') (hs : 2 ≤ s)
    (hsf : (s, f) ≠ (2, 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) :
    ¬ LargeEvenMarking ↥K' (fun lab _ _ _ _ _ => LargeEvenSplit p lab) := by
  intro hmk
  refine ClNonsplit.not_ggNbrClauseFiveMarking_sp (x := (1 : G)) hF' e hs hsf hp hp2 hq1 hq2
    ⟨1, K'.one_mem, fun l _ => by simp⟩ ?_
  exact largeEvenMarking_mono (fun lab _ _ _ _ _ hS => Or.inl (Or.inl hS)) hmk

@[expose] def GGSixTCDstarPSp
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixTCPos .PSp n f ψ p G₀ B₁ D J L x →
    ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1 ∧
      ∃ d ∈ D, d ≠ 1 ∧ ∃ K : Subgroup X,
        IsComponentOf K (G₀ ⊓ Subgroup.centralizer {d}) ∧ J ≤ K ∧
        (∃ (s : ℕ) (F : Type) (_ : Field F), Nat.card F = 2 ^ f ∧ 2 ≤ s ∧ (s, f) ≠ (2, 1) ∧
          Nonempty (↥K ≃* StatedSp s F)) ∧
        (∃ k ∈ K, ∀ l ∈ K, x⁻¹ * l * x = k⁻¹ * l * k) ∧
        (d ∈ Subgroup.zpowers x → K = L) ∧ (d ∉ Subgroup.zpowers x → K ≠ J)

theorem ggSixTCKnown_PSp_of_dstar
    (h : GGSixTCDstarPSp) : GGSixTCKnownAt .PSp := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos
  exfalso
  obtain ⟨hq1, hq2, d, hd, hd1, K, hK, hJK, ⟨s, F, _, hF, hs, hsf, ⟨e⟩⟩, hinn, hKL, hKJ⟩ :=
    h X n f ψ p G₀ B₁ D J L x hpos
  by_cases hdx : d ∈ Subgroup.zpowers x
  · rw [hKL hdx] at e
    exact not_largeEvenSplit_marking_sp hF e hs hsf hpos.prime hpos.ne_two hq1 hq2 hpos.L_split
  · exact ClNonsplit.not_ggNbrClauseFiveMarking_sp hF e hs hsf hpos.prime hpos.ne_two hq1 hq2 hinn
      (hpos.nbr d hd hdx K hK hJK (hKJ hdx)).2


private lemma g_odd_orderOf_of_pow_prime {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : G} (hs : s ^ p = 1) : Odd (orderOf s) := by
  have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf s) hdvd with h1 | hp'
  · rw [h1]
    exact odd_one
  · rw [hp']
    exact hp.odd_of_ne_two hp2

private lemma g_prime_ne_zero {F : Type} [Field F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (p : F) ≠ 0 := by
  intro hzero
  have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp hzero
  exact hp2 ((hp.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd)

private lemma g_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma g_fixIdem_mem_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {s : GL ι F} (hs : s ∈ S) {p : ℕ} :
    fixIdem p s ∈ Algebra.adjoin F (Units.val '' S) := by
  unfold fixIdem
  refine Subalgebra.smul_mem _ ?_ _
  refine Subalgebra.sum_mem _ ?_
  intro i _
  have hsA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin (show (s : Matrix ι ι F) ∈ Units.val '' S from ⟨s, hs, rfl⟩)
  exact Subalgebra.pow_mem _ hsA i

private lemma g_centralizer_comap_eq {U X : Type} [Group U] [Group X]
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

private lemma g_assembly_quasisimple_of_cfsg {Q : Type} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Assembly.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem ggSixTCDstarPSp_of_leaves
    (hL1 : GGSixTCLiftPSp) (hL2 : GGSixTCBlockDegPSp) :
    GGSixTCDstarPSp := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos
  have hf : 1 ≤ f :=
    (CFSG.SeitzReduction.SymplecticPilot.admissible_of_lieModel_PSp hpos.model).1
  have hcF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hn1 : 1 ≤ n := by
    have := (CFSG.SeitzReduction.SymplecticPilot.admissible_of_lieModel_PSp hpos.model).2.1
    omega
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    intro u hu
    have hcenter : Subgroup.center (ggU .PSp n f).K = ⊥ :=
      CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot hn1
    exact Subgroup.mem_bot.mp (hcenter ▸ hpos.ker_le hu)
  obtain ⟨ℓ, hℓ, hℓp, J', hJ', hJmap⟩ := hL1 n f ψ p G₀ B₁ D J L x hpos
  let S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    Set.range fun d : ↥D => (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
  have hSU : ∀ s ∈ S, s ∈ StatedSp n (GaloisField 2 f) := by
    rintro s ⟨d, rfl⟩
    exact (ℓ d).2
  have hDcomm : ∀ d d' : ↥D, Commute d d' := by
    intro d d'
    have h := (hpos.elemAbelian.1).is_comm.comm ⟨d, hpos.D_le d.2⟩ ⟨d', hpos.D_le d'.2⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val h
  have hScomm : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    rintro s ⟨d, rfl⟩ s' ⟨d', rfl⟩
    exact ((hDcomm d d').map ℓ).map (Subgroup.subtype (StatedSp n (GaloisField 2 f)))
  have hSp : ∀ s ∈ S, s ^ p = 1 := by
    rintro s ⟨d, rfl⟩
    exact hℓp d
  have hSodd : ∀ s ∈ S, Odd (orderOf s) := by
    intro s hs
    exact g_odd_orderOf_of_pow_prime hpos.prime hpos.ne_two (hSp s hs)
  obtain ⟨ε, hε, hJε⟩ := exists_isComponentOf_glBlockCentralizer_PSp n (GaloisField 2 f) S hScomm
    (J' := J') hJ'
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSp n f S hSU hScomm hε
  have hFE : GGSixLSevenFieldExtCase (J'.map ψ) .PSp f := by
    rw [hJmap]
    exact hpos.fieldExt
  have hdeg := hL2 n f hn1 hf ψ hpos.ker_le S hSU
    hScomm hSodd hε hJε he heε hFE
  have hL3 := blockDegree_trivial_or_eq_orderOf n (GaloisField 2 f) hpos.prime hpos.ne_two hSU
    hScomm hSp he
  set c := orderOf (((Nat.card (GaloisField 2 f) : ℕ)) : ZMod p) with hc
  have hc3 : 3 ≤ c := by
    rcases hL3 with ⟨-, h1, -⟩ | ⟨-, h1, h2⟩
    · exfalso
      rcases hdeg with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    · rcases hcase with hee | ⟨hne, hnadj, -⟩
      · rcases hdeg with ⟨-, h⟩ | ⟨hne, -⟩
        · omega
        · exact absurd hee hne
      · rcases hdeg with ⟨hee, -⟩ | ⟨-, h⟩
        · exact absurd hee hne
        · have hodd : ¬ Even c := fun hev => hnadj (h2.mpr hev)
          have : c ≠ 2 := fun h2' => hodd (h2' ▸ even_two)
          omega
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
  obtain ⟨d, hd1, hdfix⟩ := exists_ne_one_fix_blockIdem_PSp n (GaloisField 2 f) hpos.prime
    hpos.ne_two (D := ↥D) hpos.card_D ℓ hℓp hDcomm he
  obtain ⟨m, hm2, ⟨eqv⟩, hnorm, hinner⟩ := trivialBlock_PSp n (GaloisField 2 f) hpos.prime
    hpos.ne_two (ℓ d) (Subtype.ext (by simpa using hℓp d))
  have hrk := two_mul_blockDegree_le_rank_PSp n (GaloisField 2 f) S hSU hScomm hSodd hε hJε he heε
  have hm3 : 3 ≤ m := by
    have hbd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = c := by
      rcases hL3 with ⟨-, h1, -⟩ | ⟨-, h1, -⟩
      · exfalso
        rcases hdeg with ⟨-, h2⟩ | ⟨hne, h2⟩ <;> omega
      · exact h1
    have hrk' : 2 * c ≤ Matrix.rank e := by
      simpa [hbd] using hrk
    have hε₀e : fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) * e = e := by
      have hc : (p : GaloisField 2 f) ≠ 0 := g_prime_ne_zero hpos.prime hpos.ne_two
      have hpow : ∀ i : ℕ,
          (((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ^ i * e = e := by
        intro i
        induction i with
        | zero => rw [pow_zero, Matrix.one_mul]
        | succ i ih => rw [pow_succ, Matrix.mul_assoc, hdfix, ih]
      have hsum : (∑ i ∈ Finset.range p,
          (((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ^ i) * e =
          (p : GaloisField 2 f) • e := by
        rw [Finset.sum_mul]
        simp only [hpow]
        rw [Finset.sum_const, Finset.card_range]
        exact (Nat.cast_smul_eq_nsmul (GaloisField 2 f) p e).symm
      unfold fixIdem
      rw [Matrix.smul_mul, hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hrank_le : Matrix.rank e ≤ 2 * m := by
      have h1 : Matrix.rank e = Matrix.rank
          (fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) := by rw [hε₀e]
      rw [h1]
      calc Matrix.rank (fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) * e)
          ≤ Matrix.rank (fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :=
            Matrix.rank_mul_le_left _ _
        _ = 2 * m := hm2.symm
    omega
  have hmf : (m, f) ≠ (2, 1) := by
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hJ'le : J' ≤ trivBlock n (GaloisField 2 f) p (ℓ d) := by
    have hneg : (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) = 1 := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [CharTwo.neg_eq]
      · simp [h]
    have hJmJ : Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
        (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
        (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0 =
        Matrix.J (Fin n) (GaloisField 2 f) := by
      rw [Matrix.J, Matrix.fromBlocks_inj]
      exact ⟨rfl, hneg.symm, hneg, rfl⟩
    have hJm : IsUnit (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
        (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
        (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0).det := by
      rw [hJmJ]
      exact Matrix.isUnit_det_J (Fin n) (GaloisField 2 f)
    have hSUiso : ∀ s ∈ S, Matrix.transpose ((s :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) *
          (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
            (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
            (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) *
          (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
            (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
            (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0 := by
      intro s hs
      have h := CFSG.Open.StatedAPI.mem_statedSp_iff.mp (hSU s hs)
      have hmap : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f)) =
          (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := Matrix.map_id _
      rw [hmap]
      simpa only [hJmJ] using h
    have hs_mem : (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ S := Set.mem_range_self d
    have hfix : ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε = ε := by
      rcases hcase with hee | ⟨-, -, hεeq⟩
      · rw [← hee]
        exact hdfix
      · rw [hεeq, Matrix.mul_add, hdfix]
        have heStar : ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
            formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) e =
            formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) e := by
          have h1 := congrArg (formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
              (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
              (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0)) hdfix
          rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hJm] at h1
          rw [Geo.formAdj_eq_inv_of_isometry (RingHom.id (GaloisField 2 f)) hJm
            ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
            (hSUiso (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) hs_mem)] at h1
          have hcomm : Commute (((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
              (formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                  (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                  (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) e) :=
            g_adjoin_comm hScomm
              (Algebra.subset_adjoin (show ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
                  Units.val '' S from ⟨_, hs_mem, rfl⟩))
              (Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hJm hSUiso he.1)
          have h2 : formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) e *
              ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
              formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                  (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                  (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) e := by
            have h3 := congrArg (fun x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f) =>
                x * ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) h1
            have h3' : formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                  (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                  (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) e =
                formAdj (RingHom.id (GaloisField 2 f))
                  (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                    (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
                    (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0) e *
                  ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
              have hsinv : (((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))⁻¹ :
                  GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
                  ((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = 1 := by
                rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
              rw [Matrix.mul_assoc, hsinv, Matrix.mul_one] at h3
              exact h3
            exact h3'.symm
          exact hcomm.eq.trans h2
        rw [heStar]
    have hε₀ε : fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε = ε := by
      have hc : (p : GaloisField 2 f) ≠ 0 := g_prime_ne_zero hpos.prime hpos.ne_two
      have hpow : ∀ i : ℕ,
          (((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ^ i * ε = ε := by
        intro i
        induction i with
        | zero => rw [pow_zero, Matrix.one_mul]
        | succ i ih => rw [pow_succ, Matrix.mul_assoc, hfix, ih]
      have hsum : (∑ i ∈ Finset.range p,
          (((ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ^ i) * ε =
          (p : GaloisField 2 f) • ε := by
        rw [Finset.sum_mul]
        simp only [hpow]
        rw [Finset.sum_const, Finset.card_range]
        exact (Nat.cast_smul_eq_nsmul (GaloisField 2 f) p ε).symm
      unfold fixIdem
      rw [Matrix.smul_mul, hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hεε₀ : ε * fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) = ε := by
      rw [g_adjoin_comm hScomm hε.1 (g_fixIdem_mem_adjoin (p := p) hs_mem)]
      exact hε₀ε
    have h1mε0 : (1 - ε) * (1 - fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) =
        1 - fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hεε₀]
      abel
    have hGtriv : glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε ≤
        trivBlock n (GaloisField 2 f) p (ℓ d) := by
      intro g hg
      rw [glBlockCentralizer, Subgroup.mem_comap] at hg
      obtain ⟨hgc, hgf⟩ := Subgroup.mem_inf.mp hg
      have hgfeq : ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - ε) = 1 - ε := hgf
      rw [trivBlock, glBlockCentralizer, Subgroup.mem_comap]
      refine ⟨?_, ?_⟩
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact Subgroup.mem_centralizer_iff.mp hgc
          (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) (Set.mem_range_self d)
      · calc ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              (1 - fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
            = ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
                ((1 - ε) * (1 - fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)))) := by
              rw [h1mε0]
          _ = (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - ε)) *
                (1 - fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) := by
              rw [Matrix.mul_assoc]
          _ = (1 - ε) * (1 - fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) := by
              rw [hgfeq]
          _ = 1 - fixIdem p (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := h1mε0
    have hGG : ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε,
        glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε⁆ ≤
        glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε := by
      rw [Subgroup.commutator_le]
      intro g1 h1 g2 h2
      show g1 * g2 * g1⁻¹ * g2⁻¹ ∈ glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
    exact hJε.1.trans (hGG.trans hGtriv)
  have hQtb : CFSG.Assembly.IsQuasisimple ↥(trivBlock n (GaloisField 2 f) p (ℓ d)) := by
    have hQF : (Infinite (GaloisField 2 f) ∨ 4 ≤ Nat.card (GaloisField 2 f)) ∨
        Nat.card (GaloisField 2 f) = 3 ∧ 2 ≤ m ∨
        Nat.card (GaloisField 2 f) = 2 ∧ 3 ≤ m := by
      by_cases hf1 : f ≤ 1
      · right; right
        have hf1' : f = 1 := by omega
        exact ⟨by rw [hcF, hf1']; norm_num, hm3⟩
      · left; right
        rw [hcF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact g_assembly_quasisimple_of_cfsg
      (CFSG.IsQuasisimple.of_mulEquiv eqv
        (CFSG.LieType.Universal.Symplectic.isQuasisimple m (GaloisField 2 f) (by omega) hQF))
  have hK'comp : IsComponentOf (trivBlock n (GaloisField 2 f) p (ℓ d))
      (Subgroup.centralizer ({ℓ d} : Set ↥(StatedSp n (GaloisField 2 f)))) := by
    have hle : trivBlock n (GaloisField 2 f) p (ℓ d) ≤
        Subgroup.centralizer ({ℓ d} : Set ↥(StatedSp n (GaloisField 2 f))) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hg' : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
          Subgroup.centralizer ({(ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
            Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) := by
        rw [trivBlock, glBlockCentralizer, Subgroup.mem_comap] at hg
        exact (Subgroup.mem_inf.mp hg).1
      rw [Subgroup.mem_centralizer_singleton_iff] at hg'
      exact Subtype.ext hg'
    exact ⟨hle, IsSubnormal.step hle hnorm
      (IsSubnormal.refl (Subgroup.centralizer ({ℓ d} : Set ↥(StatedSp n (GaloisField 2 f))))), hQtb⟩
  have hmap : (Subgroup.centralizer ({ℓ d} : Set ↥(StatedSp n (GaloisField 2 f)))).map ψ =
      G₀ ⊓ Subgroup.centralizer ({((d : ↥D) : X)} : Set X) := by
    rw [← g_centralizer_comap_eq (StatedSp n (GaloisField 2 f)).subtype
      (Subgroup.subtype_injective _) ψ hψ (ℓ d) ((d : ↥D) : X) (hℓ d)]
    exact (Subgroup.map_comap_eq ψ (Subgroup.centralizer ({((d : ↥D) : X)} : Set X))).trans
      (by rw [hpos.range_eq])
  have hKcomp : IsComponentOf ((trivBlock n (GaloisField 2 f) p (ℓ d)).map ψ)
      (G₀ ⊓ Subgroup.centralizer {((d : ↥D) : X)}) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hK'comp ψ hψ
    convert h using 1
    · rfl
    · exact hmap.symm
  have heK : Nonempty (↥((trivBlock n (GaloisField 2 f) p (ℓ d)).map ψ) ≃*
      ↥(StatedSp m (GaloisField 2 f))) :=
    ⟨(Subgroup.equivMapOfInjective (trivBlock n (GaloisField 2 f) p (ℓ d)) ψ hψ).symm.trans eqv⟩
  obtain ⟨eK⟩ := heK
  refine ⟨hq1, hq2, ((d : ↥D) : X), d.2, fun h => hd1 (Subtype.ext h),
    (trivBlock n (GaloisField 2 f) p (ℓ d)).map ψ, hKcomp, ?_,
    ⟨m, GaloisField 2 f, inferInstance, hcF, by omega, hmf, ⟨eK⟩⟩, ?_, ?_, ?_⟩
  · rw [← hJmap]
    exact Subgroup.map_mono hJ'le
  · have hcomm_xd : Commute ((ℓ ⟨x, hpos.x_mem⟩)⁻¹) (ℓ d) :=
      ((hDcomm ⟨x, hpos.x_mem⟩ d).map ℓ).inv_left
    obtain ⟨r, hr_mem, hr⟩ := hinner ((ℓ ⟨x, hpos.x_mem⟩)⁻¹) hcomm_xd
    let rK : (ggU .PSp n f).K := r
    refine ⟨ψ rK, Subgroup.mem_map.mpr ⟨rK, hr_mem, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨u, hu_mem, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨u', hu'j, hu'psi⟩ := hℓ ⟨x, hpos.x_mem⟩ u
    have hu'eq : u' = rK⁻¹ * u * rK := by
      apply Subtype.ext
      change (StatedSp n (GaloisField 2 f)).subtype u' =
        (StatedSp n (GaloisField 2 f)).subtype (rK⁻¹ * u * rK)
      rw [hu'j]
      have hrc := congrArg (fun z : ↥(StatedSp n (GaloisField 2 f)) =>
        (z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hr u hu_mem)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hrc ⊢
      exact hrc
    calc x⁻¹ * ψ u * x = ψ u' := hu'psi
      _ = ψ (rK⁻¹ * u * rK) := by rw [hu'eq]
      _ = (ψ rK)⁻¹ * ψ u * ψ rK := by simp only [map_mul, map_inv]
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
    have hJK : J ≤ (trivBlock n (GaloisField 2 f) p (ℓ d)).map ψ := by
      rw [← hJmap]
      exact Subgroup.map_mono hJ'le
    have hJq : CFSG.Assembly.IsQuasisimple ↥J := hpos.J_comp.2.2
    rw [hcentN] at hKcomp
    exact CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJq hKcomp
      hpos.L_comp hJK hpos.J_le_L
  · intro _ hKJ
    exact not_fieldExtCase_of_mulEquiv_statedSp hcF (by omega) hmf
      ((MulEquiv.subgroupCongr hKJ.symm).trans eK) hpos.fieldExt

theorem ggSixTCKnown_PSp_of_leaves
    (hL1 : GGSixTCLiftPSp) (hL2 : GGSixTCBlockDegPSp) :
    GGSixTCKnownAt .PSp :=
  ggSixTCKnown_PSp_of_dstar (ggSixTCDstarPSp_of_leaves hL1 hL2)

theorem ggSixTCKnown_PSp_holds :
    GGSixTCKnownAt .PSp :=
  ggSixTCKnown_PSp_of_leaves ggSixTCLiftPSp_holds TableC.ggSixTCBlockDegPSp_holds

end PSp

end CFSG.StandardType

end
