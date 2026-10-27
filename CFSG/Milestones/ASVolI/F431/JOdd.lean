module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Out
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.LieType.Simplicity.TrialityD4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Conjugacy

public noncomputable section

namespace CFSG.ASVolI

open CFSG.Open

section BurnsideF4jbOuter

open CFSG.ASVolI.ChF CFSG.ComponentClassification.OuterAutomorphisms

theorem burnsideF4jb_odd_index_of_outer {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (hcen : Subgroup.center ↥Gp = ⊥)
    (hOut : Odd (Nat.card (Outer ↥Gp))) : Odd Gp.index := by
  have hinj : Function.Injective (burnsideF4d_rho Gp) := burnsideF4d_rho_injective hc
  have hS : (MulAut.conj : ↥Gp →* MulAut ↥Gp).range ≤ (burnsideF4d_rho Gp).range := by
    rintro _ ⟨d, rfl⟩
    refine ⟨(d : E), ?_⟩
    ext x
    simp [burnsideF4d_rho_apply]
  have h := CFSG.Quasithin.H13.F431.TwoF4.odd_card_div_of_outer hcen
    (burnsideF4d_rho Gp).range hS hOut
  have hcardE : Nat.card ↥(burnsideF4d_rho Gp).range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hcardE] at h
  have h2 := Subgroup.card_mul_index Gp
  have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
  rwa [show Nat.card E / Nat.card ↥Gp = Gp.index by
    rw [← h2, Nat.mul_div_cancel_left _ hpos]] at h

end BurnsideF4jbOuter

section BurnsideF4jbOddD4

set_option linter.unusedSectionVars false

open CFSG.ASVolI.ChF CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.OuterAutomorphisms


theorem burnsideF4jb_odd_index_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .D4tw 2 f Gp M₁ M₂) (hf : Odd f) : Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨-, hf1, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hyp.model
  have hσinj : Function.Injective σ := σ.injective
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  obtain ⟨σ', hσ'⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨hσinj, hσsurj⟩, RingHom.ext fun _ => rfl⟩
  subst hσ'
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  obtain ⟨-, -, ⟨Θ, -, hΘs, hΘk, -⟩, -, hcard, -, hZ, ⟨eC⟩⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf1 K hK' σ'
      (fun c => hσ c)
  let e' : ↥Gp ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) := e.trans eC
  have hcen : Subgroup.center ↥Gp = ⊥ := by
    have h := center_map_equiv e'.symm
    rw [hZ, Subgroup.map_bot] at h
    exact h.symm
  have hOut : Odd (Nat.card (Outer ↥Gp)) := by
    have h1 : Nat.card (Outer ↥Gp) =
        Nat.card (Outer ↥(graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) :=
      Nat.card_congr (equivalence e').toEquiv
    have hq : Outer ↥(graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) ≃* (K ≃+* K) :=
      (QuotientGroup.quotientMulEquivOfEq
        (show inner ↥(graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) = Θ.ker from hΘk.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective Θ hΘs)
    rw [h1, Nat.card_congr hq.toEquiv, hcard]
    exact (by decide : Odd 3).mul hf
  exact burnsideF4jb_odd_index_of_outer hyp.centralizer_trivial hcen hOut


theorem burnsideF4jb_card_outer_G2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) :
    Nat.card (Outer ↥(adjointGroup Tag.G2 K)) = Nat.card (K ≃+* K) := by
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    decide
  obtain ⟨hNF, hInn⟩ := CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4
  let ψ : (K ≃+* K) →* Outer ↥(adjointGroup Tag.G2 K) :=
    (QuotientGroup.mk' (inner ↥(adjointGroup Tag.G2 K))).comp
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K)
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨g, σ, rfl⟩ := hNF α
    refine ⟨σ, ?_⟩
    have h1 : (QuotientGroup.mk' (inner ↥(adjointGroup Tag.G2 K))) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff (MulAut.conj g)).2 ⟨g, rfl⟩
    show (QuotientGroup.mk' (inner ↥(adjointGroup Tag.G2 K)))
        (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) =
      (QuotientGroup.mk' (inner ↥(adjointGroup Tag.G2 K)))
        (MulAut.conj g * CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ)
    rw [map_mul, h1, one_mul]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    exact hInn σ ((QuotientGroup.eq_one_iff _).1 hσ)
  exact (Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)).symm

theorem burnsideF4jb_odd_index_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : Odd f) (hf2 : 2 ≤ f) : Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := hyp.model
  haveI : CharP K 2 := burnsideF4gSp_charP_of_card hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e' : ↥Gp ≃* ↥(adjointGroup Tag.G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have hcen : Subgroup.center ↥Gp = ⊥ := by
    have h := center_map_equiv e'.symm
    rw [hZ, Subgroup.map_bot] at h
    exact h.symm
  have hOut : Odd (Nat.card (Outer ↥Gp)) := by
    rw [Nat.card_congr (equivalence e').toEquiv, burnsideF4jb_card_outer_G2 hK4,
      CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card K Nat.prime_two hK]
    exact hf
  exact burnsideF4jb_odd_index_of_outer hyp.centralizer_trivial hcen hOut

end BurnsideF4jbOddD4

section BurnsideF4jbGen

open CFSG.ASVolI.ChF

theorem burnsideF4jb_oPPrime_eq_of_simple {E : Type} [Group E] {Gp : Subgroup E}
    (hs : IsSimpleGroup ↥Gp) {x : E} (hxG : x ∈ Gp) (hx1 : x ≠ 1) {k : ℕ}
    (hk : orderOf x = 2 ^ k) : oPPrime 2 Gp = Gp := by
  haveI := hs
  have hNle : oPPrime 2 Gp ≤ Gp := burnsideF4d_oPPrime_le Gp
  haveI : ((oPPrime 2 Gp).subgroupOf Gp).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr
      (burnsideF4d_le_normalizer_oPPrime Gp)
  have hne : (oPPrime 2 Gp).subgroupOf Gp ≠ ⊥ := by
    intro hbot
    have hxO : x ∈ oPPrime 2 Gp := Subgroup.subset_closure ⟨hxG, k, hk⟩
    have hmem : (⟨x, hxG⟩ : ↥Gp) ∈ (oPPrime 2 Gp).subgroupOf Gp := hxO
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 (congrArg Subtype.val hmem)
  have htop : (oPPrime 2 Gp).subgroupOf Gp = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((oPPrime 2 Gp).subgroupOf Gp)).resolve_left hne
  refine le_antisymm hNle fun g hg => ?_
  have hmem : (⟨g, hg⟩ : ↥Gp) ∈ (oPPrime 2 Gp).subgroupOf Gp := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem burnsideF4jb_exists_two_elt {E : Type} [Group E] {H B P₁ P₂ : Subgroup E}
    (hP : IsLieParabolics 2 H B P₁ P₂) : ∃ x ∈ H, x ≠ 1 ∧ ∃ k : ℕ, orderOf x = 2 ^ k := by
  obtain ⟨⟨S, ⟨hSH, hSp, -⟩, hB⟩, -, -, hmax⟩ := hP
  obtain ⟨hBP1, hP1H, hP1ne, -⟩ := (hmax P₁).mpr (Or.inl rfl)
  by_contra hcon
  push Not at hcon
  have hS : S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hSp ⟨x, hx⟩
    exact hcon x (hSH hx) hx1 k (by rw [← Subgroup.orderOf_mk x hx]; exact hk)
  have hBH : B = H := by
    rw [hB, hS, Subgroup.normalizer_eq_top, inf_top_eq]
  exact hP1ne (le_antisymm hP1H (by rw [← hBH]; exact hBP1))

theorem burnsideF4jb_parabolics (hcompat : NativeChartCompatibilityGoal) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨h1, h2, h3⟩ := hyp.toHypF_4_4g.chart_matches
  have hlp := (hcompat κ p f E Gp hyp.toHypF_4_4g.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  exact hlp

theorem burnsideF4jb_oPPrime_Gp_of_simple (hcompat : NativeChartCompatibilityGoal)
    {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hs : IsSimpleGroup ↥Gp) : oPPrime 2 Gp = Gp := by
  obtain ⟨x, hxG, hx1, k, hk⟩ := burnsideF4jb_exists_two_elt (burnsideF4jb_parabolics hcompat hyp)
  exact burnsideF4jb_oPPrime_eq_of_simple hs hxG hx1 hk

end BurnsideF4jbGen

section BurnsideF4jbSwap

open CFSG.ASVolI.ChF Matrix

variable {K : Type} [Field K]

@[expose] def burnsideF4jb_swapGL {n : ℕ} (K : Type) [Field K] (i j : Fin n) : GL (Fin n) K :=
  ⟨(Equiv.swap i j).permMatrix K, (Equiv.swap i j).permMatrix K,
    by rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]⟩

theorem burnsideF4jb_coe_swapGL {n : ℕ} (i j : Fin n) :
    ((burnsideF4jb_swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Equiv.swap i j).permMatrix K :=
  rfl

theorem burnsideF4jb_swapGL_apply {n : ℕ} (i j a b : Fin n) :
    ((burnsideF4jb_swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      if Equiv.swap i j a = b then 1 else 0 := by
  rw [burnsideF4jb_coe_swapGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_eq,
    Matrix.submatrix_apply, Matrix.one_apply]
  rfl

theorem burnsideF4jb_swapGL_mul_self {n : ℕ} (i j : Fin n) :
    burnsideF4jb_swapGL K i j * burnsideF4jb_swapGL K i j = 1 := by
  apply Units.ext
  rw [Units.val_mul, burnsideF4jb_coe_swapGL, ← Matrix.permMatrix_mul, Equiv.swap_mul_self,
    Matrix.permMatrix_one, Units.val_one]

theorem burnsideF4jb_det_swapGL [CharP K 2] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ((burnsideF4jb_swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [burnsideF4jb_coe_swapGL, Matrix.det_permutation, Equiv.Perm.sign_swap hij]
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  exact CharTwo.neg_eq 1

theorem burnsideF4jb_swapGL_not_scalar {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    burnsideF4jb_swapGL K i j ∉ CFSG.Open.StatedScalars (Fin n) K := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, burnsideF4jb_swapGL_apply,
    Equiv.swap_apply_left, if_true] at h
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h
  exact zero_ne_one h

theorem burnsideF4jb_swapGL_mem_SL [CharP K 2] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    burnsideF4jb_swapGL K i j ∈ CFSG.Open.StatedSL n K :=
  CFSG.Open.StatedAPI.mem_statedSL_iff.2 (burnsideF4jb_det_swapGL hij)

theorem burnsideF4jb_swapGL_mem_SU [CharP K 2] {n q : ℕ} (hq : q ≠ 0) {i j : Fin n}
    (hij : i ≠ j) : burnsideF4jb_swapGL K i j ∈ CFSG.Open.StatedSU n q K := by
  refine Subgroup.subset_closure ⟨burnsideF4jb_det_swapGL hij, ?_⟩
  have hmap : ((burnsideF4jb_swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map
      (· ^ q) = ((burnsideF4jb_swapGL K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    ext a b
    rw [Matrix.map_apply, burnsideF4jb_swapGL_apply]
    split_ifs
    · exact one_pow q
    · exact zero_pow hq
  rw [hmap, burnsideF4jb_coe_swapGL, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]

theorem burnsideF4jb_two_elt_of_proj {n : ℕ} {H : Subgroup (GL (Fin n) K)} {A : GL (Fin n) K}
    (hA : A ∈ H) (hA2 : A * A = 1) (hAs : A ∉ CFSG.Open.StatedScalars (Fin n) K)
    {E : Type} [Group E] {Gp : Subgroup E} (e : ↥Gp ≃* CFSG.Open.StatedProj H) :
    ∃ x ∈ Gp, x ≠ 1 ∧ ∃ k : ℕ, orderOf x = 2 ^ k := by
  have hy1 : (QuotientGroup.mk (⟨A, hA⟩ : ↥H) : CFSG.Open.StatedProj H) ≠ 1 := by
    intro h
    exact hAs (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))
  have hy2 : (QuotientGroup.mk (⟨A, hA⟩ : ↥H) : CFSG.Open.StatedProj H) *
      QuotientGroup.mk (⟨A, hA⟩ : ↥H) = 1 := by
    rw [← QuotientGroup.mk_mul, show (⟨A, hA⟩ * ⟨A, hA⟩ : ↥H) = 1 from Subtype.ext hA2,
      QuotientGroup.mk_one]
  have hz1 : e.symm (QuotientGroup.mk (⟨A, hA⟩ : ↥H)) ≠ 1 := by
    intro h
    exact hy1 (by simpa using congrArg e h)
  refine ⟨(e.symm (QuotientGroup.mk (⟨A, hA⟩ : ↥H)) : E),
    (e.symm (QuotientGroup.mk (⟨A, hA⟩ : ↥H))).2, fun h => hz1 (Subtype.ext h), 1, ?_⟩
  rw [pow_one]
  refine orderOf_eq_prime ?_ fun h => hz1 (Subtype.ext h)
  rw [sq, ← Subgroup.coe_mul, ← map_mul, hy2, map_one]
  rfl

theorem burnsideF4jb_oPPrime_Gp_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .L3 2 f Gp M₁ M₂) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := hyp.model
  haveI : CharP K 2 := burnsideF4gSp_charP_of_card hK
  obtain ⟨x, hxG, hx1, k, hk⟩ := burnsideF4jb_two_elt_of_proj
    (burnsideF4jb_swapGL_mem_SL (K := K) (show (0 : Fin 3) ≠ 1 by decide))
    (burnsideF4jb_swapGL_mul_self 0 1)
    (burnsideF4jb_swapGL_not_scalar (show (0 : Fin 3) ≠ 1 by decide)) e
  exact burnsideF4jb_oPPrime_eq_of_simple (burnsideF4d_Y1_simple hyp.toHypF_4_4g) hxG hx1 hk

theorem burnsideF4jb_oPPrime_Gp_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U4 2 f Gp M₁ M₂) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := hyp.model
  have hK' : Nat.card K = 2 ^ (f * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := burnsideF4gSp_charP_of_card hK'
  haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 (2 ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 f hK 4 (by norm_num)
      (by simp)
  obtain ⟨x, hxG, hx1, k, hk⟩ := burnsideF4jb_two_elt_of_proj
    (burnsideF4jb_swapGL_mem_SU (K := K) (q := 2 ^ f) (by positivity)
      (show (0 : Fin 4) ≠ 1 by decide))
    (burnsideF4jb_swapGL_mul_self 0 1)
    (burnsideF4jb_swapGL_not_scalar (show (0 : Fin 4) ≠ 1 by decide)) e
  exact burnsideF4jb_oPPrime_eq_of_simple e.isSimpleGroup hxG hx1 hk

theorem burnsideF4jb_oPPrime_Gp_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U5 2 f Gp M₁ M₂) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := hyp.model
  have hK' : Nat.card K = 2 ^ (f * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := burnsideF4gSp_charP_of_card hK'
  haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 5 (2 ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 f hK 5 (by norm_num)
      (by simp)
  obtain ⟨x, hxG, hx1, k, hk⟩ := burnsideF4jb_two_elt_of_proj
    (burnsideF4jb_swapGL_mem_SU (K := K) (q := 2 ^ f) (by positivity)
      (show (0 : Fin 5) ≠ 1 by decide))
    (burnsideF4jb_swapGL_mul_self 0 1)
    (burnsideF4jb_swapGL_not_scalar (show (0 : Fin 5) ≠ 1 by decide)) e
  exact burnsideF4jb_oPPrime_eq_of_simple e.isSimpleGroup hxG hx1 hk

end BurnsideF4jbSwap

section BurnsideF4jbExcSimple

set_option linter.unusedSectionVars false

open CFSG.ASVolI.ChF


theorem burnsideF4jb_oPPrime_Gp_Tits {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .Tits 2 f Gp M₁ M₂) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨-, -, hmodel⟩ := hyp.model
  exact burnsideF4jb_oPPrime_Gp_of_simple ChF.nativeChartCompatibility hyp
    (CFSG.LieType.Simplicity.fam_tits_simplicity ↥Gp 2 f hmodel).2

theorem burnsideF4jb_oPPrime_Gp_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 2 f Gp M₁ M₂) (hf2 : 2 ≤ f) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨-, -, hmodel⟩ := hyp.model
  exact burnsideF4jb_oPPrime_Gp_of_simple ChF.nativeChartCompatibility hyp
    (CFSG.LieType.Simplicity.fam_g2_simplicity ↥Gp 2 f
      ⟨CFSG.Open.StatedAPI.statedLieAdmissible_G2_two hf2, hmodel⟩).2

theorem burnsideF4jb_oPPrime_Gp_F4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .F4tw 2 f Gp M₁ M₂) (hf3 : 3 ≤ f) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨-, -, h1 | ⟨-, hmodel⟩⟩ := hyp.model
  · exact absurd h1.1 (by omega)
  · exact burnsideF4jb_oPPrime_Gp_of_simple ChF.nativeChartCompatibility hyp
      (CFSG.LieType.Simplicity.fam_ree_tits_simplicity ↥Gp .twistedF4 2 f hmodel).2

end BurnsideF4jbExcSimple

section BurnsideF4jbD4Simple

set_option linter.unusedSectionVars false

open CFSG.ASVolI.ChF


theorem burnsideF4jb_oPPrime_Gp_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .D4tw 2 f Gp M₁ M₂) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨-, hf1, hmodel⟩ := hyp.model
  exact burnsideF4jb_oPPrime_Gp_of_simple ChF.nativeChartCompatibility hyp
    (CFSG.LieType.Simplicity.fam_3d4_simplicity ↥Gp 2 f ⟨⟨Nat.prime_two, hf1, rfl⟩, hmodel⟩).2

end BurnsideF4jbD4Simple

end CFSG.ASVolI
