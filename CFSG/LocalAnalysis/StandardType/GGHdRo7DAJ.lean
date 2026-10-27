module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8D4Rank
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaMinusEightOrderThree
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaCentreZMod2
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.Assembly CFSG.HardMathSupport.Timmesfeld.Proving.MinusEightOrderThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7DAJAux_three_dvd_card_of_bigElem {T : Type} [Group T] [Finite T]
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om.BigElem T) : 3 ∣ Nat.card T := by
  obtain ⟨E, hE, hcard⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEne : E ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥E = 1 := by rw [hbot]; exact Subgroup.card_bot
    have : 3 ^ 4 ≤ 1 := by rw [← h1]; exact hcard
    omega
  exact (CFSG.RankThree.PartTwo.Sec21.dvd_card_of_isPGroup_ne_bot hE.isPGroup hEne).trans
    (Subgroup.card_subgroup_dvd_card E)

private theorem hdRo7DAJAux_card_statedProj_of_scalars_bot {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2) :
    Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega Q)) =
      Nat.card ↥(CFSG.Open.StatedOmega Q) := by
  have hbot : (CFSG.Open.StatedScalars ι (ZMod 2)).subgroupOf (CFSG.Open.StatedOmega Q) = ⊥ := by
    rw [CFSG.HardMathSupport.Timmesfeld.Proving.statedScalars_zmod2_eq_bot,
      Subgroup.bot_subgroupOf]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((CFSG.Open.StatedScalars ι (ZMod 2)).subgroupOf (CFSG.Open.StatedOmega Q))
  change Nat.card (↥(CFSG.Open.StatedOmega Q) ⧸
    (CFSG.Open.StatedScalars ι (ZMod 2)).subgroupOf (CFSG.Open.StatedOmega Q)) = _
  rw [hbot] at h ⊢
  rw [Subgroup.card_bot, Nat.mul_one] at h
  exact h.symm

private theorem hdRo7DAJAux_three_dvd_proj_quadMinus_four :
    3 ∣ Nat.card (CFSG.Open.StatedProj
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 (ZMod 2) 1 1))) := by
  rw [hdRo7DAJAux_card_statedProj_of_scalars_bot
    (CFSG.Open.StatedQuadMinus 4 (ZMod 2) 1 1)]
  exact three_dvd_card_statedOmega_quadMinus_four

private theorem hdRo7DAJAux_three_dvd_proj_quadMinus_four_field (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    3 ∣ Nat.card (CFSG.Open.StatedProj
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))) := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hirr' : ∀ s : ZMod 2, s ^ 2 + σ b * s + σ c ≠ 0 := by
    intro s hs
    apply hirr (σ.symm s)
    apply σ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  have key : ∀ x y : ZMod 2, (∀ s : ZMod 2, s ^ 2 + x * s + y ≠ 0) → x = 1 ∧ y = 1 := by
    decide
  obtain ⟨hb1, hc1⟩ := key (σ b) (σ c) hirr'
  have hmaps : Subgroup.map (CFSG.Adapters.RankTwoModelTransports.glCongr σ).toMonoidHom
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) =
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 (ZMod 2) (σ b) (σ c)) :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
      (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl v)
  have e1 : CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) ≃*
      CFSG.Open.StatedProj
        (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 (ZMod 2) (σ b) (σ c))) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr σ) hmaps
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars σ)
  rw [Nat.card_congr e1.toEquiv, hb1, hc1]
  exact hdRo7DAJAux_three_dvd_proj_quadMinus_four

private theorem hdRo7DAJAux_omegaPlus_eq (K : Type) [Field K] (m : ℕ) :
    CFSG.Assembly.LargeEvenOmega (CFSG.Assembly.LargeEvenQPlus K m) =
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K) := by
  rw [CFSG.StandardType.RecipeFieldOmega.omegaPlus_eq, CFSG.LieType.Universal.Spin.coe_quadPlus]

theorem hdRo7DAJAux_three_dvd_card_of_row {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {J X : Subgroup G}
    (hrow : GGResRowAt ggRowDCorank2 p J X) : p ∣ Nat.card J := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hp3, hJtag, hXtag, hJn, hXn, hXrank, hX6⟩ := hrow
  have hJrank : 4 ≤ labJ.rank := by omega
  subst hp3
  have h3Q : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rcases hJtag with hD | htwD
    · have hJ3 : labJ.rank ≠ 3 := by omega
      have hJlab' : CFSG.Assembly.LargeEvenRecipeOmegaPlus labJ.rank (2 ^ labJ.n)
          (fun R' _ _ _ => Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* R')) := by
        rw [GGHasLabel] at hJlab
        simpa only [LargeEvenRawDatum, hD, if_neg hJ3] using hJlab
      obtain ⟨K, hKfield, hKfin, hKcard, hKiso⟩ := hJlab'
      let : Field K := hKfield
      let : Finite K := hKfin
      obtain ⟨e⟩ := hKiso
      have hK2 : Nat.card K = 2 := by simpa [hJn] using hKcard
      rw [Nat.card_congr e.toEquiv]
      have h3big : 3 ∣ Nat.card (CFSG.Open.StatedProj
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus labJ.rank K))) := by
        refine hdRo7DAJAux_three_dvd_card_of_bigElem ?_
        by_cases h4 : labJ.rank = 4
        · rw [h4]
          exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om.bigElem_plus_two_four K hK2
        · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om.bigElem_plus_two K hK2
            (n := labJ.rank) (by omega)
      rw [hdRo7DAJAux_omegaPlus_eq K labJ.rank]
      exact h3big
    · have hJ2 : labJ.rank ≠ 2 := by omega
      have hJ3 : labJ.rank ≠ 3 := by omega
      have hJlab' : CFSG.Assembly.LargeEvenRecipeOmegaMinus (labJ.rank - 1) (2 ^ labJ.n)
          (fun R' _ _ _ => Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* R')) := by
        rw [GGHasLabel] at hJlab
        simpa only [LargeEvenRawDatum, htwD, if_neg hJ2, if_neg hJ3] using hJlab
      obtain ⟨K, hKfield, hKfin, hKcard, b, c, hirr, hKiso⟩ := hJlab'
      let : Field K := hKfield
      let : Finite K := hKfin
      obtain ⟨e⟩ := hKiso
      have hK2 : Nat.card K = 2 := by simpa [hJn] using hKcard
      have e' : (↥J ⧸ Subgroup.center ↥J) ≃*
          CFSG.Open.StatedProj
            (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus labJ.rank K b c)) :=
        e.trans (CFSG.StandardType.omegaMinusProjEquiv labJ.rank b c)
      rw [Nat.card_congr e'.toEquiv]
      by_cases h4 : labJ.rank = 4
      · rw [h4]
        exact hdRo7DAJAux_three_dvd_proj_quadMinus_four_field K hK2 b c hirr
      · refine hdRo7DAJAux_three_dvd_card_of_bigElem ?_
        exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om.bigElem_minus_two K hK2
          (n := labJ.rank) (by omega) b c hirr
  have h3J : 3 ∣ Nat.card ↥J :=
    h3Q.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
  simpa using h3J

private theorem hdRo7DAJAux_labelIso_eq {l1 l2 : LargeEvenLabel} (h : GGLabelIso l1 l2)
    (ht : l1.tag = .D ∨ l1.tag = .twD) (hr : 4 ≤ l1.rank) : l1 = l2 := by
  rcases h with h | ⟨hb, -, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨-, h1⟩
  · exact h
  · rcases ht with ht | ht <;> rw [ht] at hb <;> exact absurd hb (by decide)
  · have h3 : l1.rank = 3 := by rw [h1]
    omega
  · have ht' : l1.tag = .A := by rw [h1]
    rw [ht'] at ht
    exact absurd ht (by decide)
  · have h3 : l1.rank = 3 := by rw [h1]
    omega
  · have ht' : l1.tag = .twA := by rw [h1]
    rw [ht'] at ht
    exact absurd ht (by decide)
  · have h3 : l1.rank = 2 := by rw [h1]
    omega
  · have ht' : l1.tag = .A := by rw [h1]
    rw [ht'] at ht
    exact absurd ht (by decide)

private theorem hdRo7DAJAux_not_nonLevi {G : Type} [Group G] [Finite G] {p : ℕ}
    {J X : Subgroup G} (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowDCorank2 p J X)
    (hNL : GGResRowAt ggRowNonLevi p J X) : False := by
  obtain ⟨lJ1, lX1, hJ1Λ, hX1Λ, hJ1lab, hX1lab, hp3, hJ1tag, hX1tag, hJ1n, hX1n, hXrank,
    hX6⟩ := hrow
  obtain ⟨lJ2, lX2, hJ2Λ, hX2Λ, hJ2lab, hX2lab, hNL'⟩ := hNL
  have hisoJ : GGLabelIso lJ1 lJ2 := hRig lJ1 lJ2 _ hJ1Λ hJ2Λ hJ1lab hJ2lab
  have hisoX : GGLabelIso lX1 lX2 := hRig lX1 lX2 _ hX1Λ hX2Λ hX1lab hX2lab
  have hJ1rank : 4 ≤ lJ1.rank := by omega
  have hJeq : lJ1 = lJ2 := hdRo7DAJAux_labelIso_eq hisoJ hJ1tag hJ1rank
  have hXeq : lX1 = lX2 := hdRo7DAJAux_labelIso_eq hisoX hX1tag (by omega)
  rw [← hJeq, ← hXeq] at hNL'
  rcases hNL' with h2 | hmax | htri | htri2 | h7 | htw2
  · rcases h2 with ⟨hJA, -, -, -⟩ | ⟨hJtwA, -, -, -⟩ | ⟨-, -, -, hXA⟩ | ⟨-, -, -, hXA⟩
    · rw [hJA] at hJ1tag
      exact absurd hJ1tag (by decide)
    · rw [hJtwA] at hJ1tag
      exact absurd hJ1tag (by decide)
    · have hE : lX1.tag = .E6 := by rw [hXA]
      rw [hE] at hX1tag
      exact absurd hX1tag (by decide)
    · have hE : lX1.tag = .twE6 := by rw [hXA]
      rw [hE] at hX1tag
      exact absurd hX1tag (by decide)
  · rcases hmax with ⟨hJA, -, -, -⟩ | ⟨hJtwA, -, -, -⟩
    · have ht' : lJ1.tag = .A := by rw [hJA]
      rw [ht'] at hJ1tag
      exact absurd hJ1tag (by decide)
    · have ht' : lJ1.tag = .twA := by rw [hJtwA]
      rw [ht'] at hJ1tag
      exact absurd hJ1tag (by decide)
  · rcases htri with ⟨hJtri, -, -⟩ | ⟨hJG2, -, -⟩
    · rw [hJtri] at hJ1tag
      exact absurd hJ1tag (by decide)
    · rw [hJG2] at hJ1tag
      exact absurd hJ1tag (by decide)
  · obtain ⟨hJtri, -, -, -⟩ := htri2
    rw [hJtri] at hJ1tag
    exact absurd hJ1tag (by decide)
  · obtain ⟨hp7, -⟩ := h7
    omega
  · obtain ⟨hJtwA, -, -, -⟩ := htw2
    rw [hJtwA] at hJ1tag
    exact absurd hJ1tag (by decide)

private theorem hdRo7DAJAux_repr_unitsSMul {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (u : Fin (n + 1) → (ZMod p)ˣ) (v : V) (j : Fin (n + 1)) :
    b.repr (b.equiv (b.unitsSMul u) 1 v) j = (u j : ZMod p) * b.repr v j := by
  have hf : ∀ i, b.equiv (b.unitsSMul u) 1 (b i) = (u i : ZMod p) • b i := by
    intro i
    rw [Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply]
    rfl
  have hfun : b.equiv (b.unitsSMul u) 1 v = ∑ i, ((b.repr v) i * (u i : ZMod p)) • b i := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hf i, smul_smul]
  rw [hfun, map_sum, Finsupp.finset_sum_apply]
  have hterm : ∀ i, b.repr (((b.repr v) i * (u i : ZMod p)) • b i) j
      = ((b.repr v) i * (u i : ZMod p)) * (if i = j then 1 else 0) := by
    intro i
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul]
  simp only [hterm]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one, mul_comm]
  · intro i _ hij
    rw [if_neg hij, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem hdRo7DAJAux_dsp_c2sp {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    {a : V ≃ₗ[ZMod p] V} (h : DSP p b a) : C2SP p b a := by
  obtain ⟨σ, c, hσ, hc0, hc, -, ha⟩ := h
  exact ⟨σ, c, hσ, hc0, hc, ha⟩

private theorem hdRo7DAJAux_dsp_repr_eq_zero {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hn : 2 ≤ n)
    (v : V) (hv : ∀ g : V ≃ₗ[ZMod p] V, DSP p b g → g v = v) (j : Fin (n + 1)) (hj : j ≠ 0) :
    b.repr v j = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    have hp2 : p ≠ 2 := by omega
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have hjk : ∃ k : Fin (n + 1), k ≠ 0 ∧ k ≠ j := by
    have hj1 : 1 ≤ j.val := by
      rcases Nat.eq_zero_or_pos j.val with h | h
      · exfalso
        exact hj (Fin.ext (by simpa using h))
      · exact h
    by_cases h1 : j.val = 1
    · refine ⟨⟨2, by omega⟩, by simp, ?_⟩
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    · refine ⟨⟨1, by omega⟩, by simp, ?_⟩
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
  obtain ⟨k, hk0, hkj⟩ := hjk
  have hkj' : j ≠ k := fun h => hkj h.symm
  have h0j : (0 : Fin (n + 1)) ≠ j := fun h => hj h.symm
  have h0k : (0 : Fin (n + 1)) ≠ k := fun h => hk0 h.symm
  let u : Fin (n + 1) → (ZMod p)ˣ := fun i =>
    (if i = j then -1 else 1) * (if i = k then -1 else 1)
  have huval : ∀ i, ((u i : ZMod p)) =
      (if i = j then (-1 : ZMod p) else 1) * (if i = k then (-1 : ZMod p) else 1) := by
    intro i
    simp only [u, Units.val_mul, apply_ite Units.val, Units.val_neg, Units.val_one]
  have hu0 : ((u 0 : ZMod p)) = 1 := by
    rw [huval, if_neg h0j, if_neg h0k]
    norm_num
  have huj : ((u j : ZMod p)) = -1 := by
    rw [huval, if_pos rfl, if_neg hkj']
    norm_num
  have huk : ((u k : ZMod p)) = -1 := by
    rw [huval, if_neg hkj, if_pos rfl]
    norm_num
  have hu1 : ∀ i, ((u i : ZMod p)) = 1 ∨ ((u i : ZMod p)) = -1 := by
    intro i
    by_cases hij : i = j
    · rw [hij]; exact Or.inr huj
    · by_cases hik : i = k
      · rw [hik]; exact Or.inr huk
      · refine Or.inl ?_
        rw [huval, if_neg hij, if_neg hik]
        norm_num
  have huprod : ∏ i, ((u i : ZMod p)) = 1 := by
    simp only [huval, Finset.prod_mul_distrib]
    have hj1 : ∏ i, (if i = j then (-1 : ZMod p) else 1) = -1 := by
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hk1 : ∏ i, (if i = k then (-1 : ZMod p) else 1) = -1 := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro i _ hik
        simp [hik]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hj1, hk1]
    norm_num
  let s : V ≃ₗ[ZMod p] V := b.equiv (b.unitsSMul u) 1
  have hs : DSP p b s := by
    refine ⟨1, fun i => (u i : ZMod p), rfl, hu0, hu1, huprod, ?_⟩
    intro i
    rw [show s = b.equiv (b.unitsSMul u) 1 from rfl, Module.Basis.equiv_apply,
      Module.Basis.unitsSMul_apply]
    rfl
  have hfix : s v = v := hv s hs
  have hrepr := hdRo7DAJAux_repr_unitsSMul b u v j
  rw [hfix, huj] at hrepr
  have hr : b.repr v j = - b.repr v j := by simpa using hrepr
  have hsum : b.repr v j + b.repr v j = 0 := by
    nth_rewrite 1 [hr]
    simp
  rw [← two_mul] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left h2

theorem hdRo7DAJAux_model_card_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hp3 : p = 3) (hn : 2 ≤ n)
    (hsub : ∀ g : V ≃ₗ[ZMod p] V, DSP p b g → g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι))
    {Λ : Type} [Fintype Λ] {V' : Type} [AddCommGroup V'] [Module (ZMod p) V']
    (ι' : Additive ↥Bs ≃+ V') (φ : Λ → MulAut ↥Bs) (hh : Λ → V')
    (α : Λ → Module.Dual (ZMod p) V')
    (hformula : ∀ i w, ggLin (p := p) ι' (φ i) w = w - α i w • hh i)
    (hgenX : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) :
    n ≤ Nat.card Λ := by
  classical
  let Φ : Additive ↥Bs →+ (Λ → ZMod p) :=
    { toFun := fun β i => α i (ι' β)
      map_zero' := by
        ext i
        simp
      map_add' := by
        intro x y
        ext i
        simp }
  have hmem_ker : ∀ β ∈ Φ.ker, ∀ i, α i (ι' β) = 0 := by
    intro β hβ i
    have := congrFun (AddMonoidHom.mem_ker.mp hβ) i
    simpa [Φ] using this
  have hker_fix : ∀ β ∈ Φ.ker, ∀ i, Additive.ofMul (φ i (Additive.toMul β)) = β := by
    intro β hβ i
    have hβi := hmem_ker β hβ i
    have key : ggLin (p := p) ι' (φ i) (ι' β) = ι' β := by
      have h := hformula i (ι' β)
      rwa [hβi, zero_smul, sub_zero] at h
    have h2 := ggLin_apply_ofMul (p := p) ι' (φ i) (Additive.toMul β)
    have h3 : ι' (Additive.ofMul (φ i (Additive.toMul β))) = ι' β := by
      rw [← h2]
      exact key
    exact ι'.injective h3
  have hker_fixed : ∀ β ∈ Φ.ker, ∀ g : V ≃ₗ[ZMod p] V, DSP p b g → g (ι β) = ι β := by
    intro β hβ g hg
    have hmem : g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) := hsub g hg
    have hstab : ∀ i, ggLin (p := p) ι (φ i) ∈
        MulAction.stabilizer (V ≃ₗ[ZMod p] V) (ι β) := by
      intro i
      have h1 : (ggLin (p := p) ι (φ i)) (ι β) = ι β := by
        have h := ggLin_apply_ofMul (p := p) ι (φ i) (Additive.toMul β)
        rw [hker_fix β hβ i] at h
        exact h
      rw [MulAction.mem_stabilizer_iff]
      simpa using h1
    have hle : (ggAutomizer X Bs).map (ggLin (p := p) ι) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod p] V) (ι β) := by
      rw [hgenX, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      intro a ha
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨i, rfl⟩ := hx
      exact hstab i
    have := hle hmem
    rwa [MulAction.mem_stabilizer_iff] at this
  have hzero : ∀ β ∈ Φ.ker, ∀ j, j ≠ 0 → b.repr (ι β) j = 0 := by
    intro β hβ j hj
    exact hdRo7DAJAux_dsp_repr_eq_zero hp3 b hn (ι β) (hker_fixed β hβ) j hj
  have hrepr : ∀ β ∈ Φ.ker, ι β = (b.repr (ι β) 0) • b 0 := by
    intro β hβ
    conv_lhs => rw [← b.sum_repr (ι β)]
    rw [Finset.sum_eq_single 0]
    · intro i _ hi
      rw [hzero β hβ i hi, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h
  have hker_le : Nat.card ↥Φ.ker ≤ p := by
    have hinj : Function.Injective (fun β : ↥Φ.ker => b.repr (ι (β : Additive ↥Bs)) 0) := by
      intro β₁ β₂ heq
      have h1 := hrepr β₁ β₁.2
      have h2 := hrepr β₂ β₂.2
      refine Subtype.ext (ι.injective ?_)
      rw [h1, h2]
      simpa using congrArg (fun c : ZMod p => c • b 0) heq
    calc Nat.card ↥Φ.ker ≤ Nat.card (ZMod p) := Nat.card_le_card_of_injective _ hinj
      _ = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcard_bs : Nat.card (Additive ↥Bs) = p ^ (n + 1) := by
    rw [Nat.card_congr ι.toEquiv, Nat.card_congr b.equivFun.toEquiv]
    simp [ZMod.card]
  have hrange_le : Nat.card ↥Φ.range ≤ p ^ Nat.card Λ := by
    have hle : Nat.card ↥Φ.range ≤ Nat.card (Λ → ZMod p) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have hpi : Nat.card (Λ → ZMod p) = p ^ Nat.card Λ := by
      rw [Nat.card_pi]
      simp [ZMod.card]
    rwa [hpi] at hle
  have hcomb : p ^ (n + 1) ≤ p ^ (Nat.card Λ + 1) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ.ker
    have h2 : Nat.card (Additive ↥Bs ⧸ Φ.ker) = Nat.card ↥Φ.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Φ).toEquiv
    rw [h2, hcard_bs] at h1
    calc p ^ (n + 1) = Nat.card ↥Φ.range * Nat.card ↥Φ.ker := h1
      _ ≤ p ^ Nat.card Λ * p := Nat.mul_le_mul hrange_le hker_le
      _ = p ^ (Nat.card Λ + 1) := by rw [pow_succ]
  have hle' : n + 1 ≤ Nat.card Λ + 1 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcomb
  omega

private theorem hdRo7DAJAux_nonabelian_of_data
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    {n : ℕ} (hn5 : 5 ≤ n)
    {Λ K : Type} [Fintype Λ] [Fintype K]
    {MJ : CoxeterMatrix K}
    (hWeylMJ : GGIsWeylMatrix MJ)
    (fJ : MJ.Group ≃* ↥(ggAutomizer J Bs))
    (hΛcard : Nat.card Λ ≤ Nat.card K + 3)
    (hn : n ≤ Nat.card Λ) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  classical
  by_contra h
  push Not at h
  have hnoedge : ∀ j j' : K, j ≠ j' → MJ.M j j' = 2 := by
    intro j j' hne
    have hcomm : fJ (MJ.simple j) * fJ (MJ.simple j') =
        fJ (MJ.simple j') * fJ (MJ.simple j) :=
      Subtype.ext (h (fJ (MJ.simple j)) (fJ (MJ.simple j)).2
        (fJ (MJ.simple j')) (fJ (MJ.simple j')).2)
    have hsimple_comm : MJ.simple j * MJ.simple j' = MJ.simple j' * MJ.simple j :=
      fJ.injective (by simpa [map_mul] using hcomm)
    have hsq : (MJ.simple j * MJ.simple j') ^ 2 = 1 := by
      have hc : Commute (MJ.simple j) (MJ.simple j') := hsimple_comm
      rw [hc.mul_pow]
      rw [show MJ.simple j ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self MJ.toCoxeterSystem j,
          show MJ.simple j' ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self MJ.toCoxeterSystem j']
      simp
    have horder : orderOf (MJ.simple j * MJ.simple j') = MJ.M j j' := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple MJ.toCoxeterSystem j j'
    have hdvd : MJ.M j j' ∣ 2 := by
      rw [← horder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hsq
    have h1 : MJ.M j j' ≠ 1 := MJ.off_diagonal j j' hne
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact (h1 h').elim
    · exact h'
  have hsub : Subsingleton K := by
    refine ⟨fun j j' => ?_⟩
    by_contra hne
    have hpath := ggRC_weyl_connected hWeylMJ j j'
    have hEq : j = j' := by
      induction hpath with
      | refl => rfl
      | tail _ hstep _ =>
          exact (hstep.2 (hnoedge _ _ hstep.1)).elim
    exact hne hEq
  have hKpos : 0 < Nat.card K := by omega
  have : Nonempty K := by
    rw [← Fintype.card_pos_iff]
    simpa [Nat.card_eq_fintype_card] using hKpos
  have hKcard : Nat.card K = 1 := by
    have : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr
      ⟨Classical.arbitrary K, fun x => Subsingleton.elim x _⟩
    simpa [Nat.card_eq_fintype_card] using this
  omega

private theorem hdRo7DAJAux_sideDatum_nonabelian
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hp3 : p = 3) (hn5 : 5 ≤ n)
    (hsub : ∀ g : V ≃ₗ[ZMod p] V, DSP p b g → g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι))
    (hD : GGResSideDatum p Bs X J) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  obtain ⟨Λ, instΛ, decΛ, bnode, M, C, MJ, V', instV, instMod, ι', φ, hv, hα,
    hWeylM, hCartan, hWeylMJ, hMJsub, hformula, hrefl, hpair, ⟨f, hf⟩, hgenX,
    ⟨fJ, -⟩, hgenJ, hconj⟩ := hD
  let : Fintype Λ := instΛ
  let : DecidableEq Λ := decΛ
  let : AddCommGroup V' := instV
  let : Module (ZMod p) V' := instMod
  have hn : n ≤ Nat.card Λ :=
    hdRo7DAJAux_model_card_le (Λ := Λ) b ι hp3 (by omega) hsub ι' φ hv hα hformula hgenX
  have hΛcard : Nat.card Λ ≤ Nat.card {j : Λ // j ≠ bnode} + 3 := by
    have hEq : Nat.card Λ = Nat.card {j : Λ // j = bnode} +
        Nat.card {j : Λ // j ≠ bnode} := by
      rw [← Nat.card_congr (Equiv.sumCompl (fun j : Λ => j = bnode)), Nat.card_sum]
    have hsingle : Nat.card {j : Λ // j = bnode} = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have : (Finset.univ.filter (fun j : Λ => j = bnode)) = {bnode} := by
        ext j
        simp
      rw [this]
      simp
    omega
  exact hdRo7DAJAux_nonabelian_of_data (p := p) (Bs := Bs) (J := J) (n := n) hn5 hWeylMJ
    fJ hΛcard hn

private theorem hdRo7DAJAux_le3_nonabelian
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hp3 : p = 3) (hn5 : 5 ≤ n)
    (hsub : ∀ g : V ≃ₗ[ZMod p] V, DSP p b g → g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι))
    (hD : GGResLeviSideDatumLE3 p Bs X J) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  obtain ⟨Λ, instΛ, decΛ, S, M, C, MJ, V', instV, instMod, ι', φ, hv, hα,
    hS2, hS3, hWeylM, hCartan, hWeylMJ, hMJsub, hformula, hrefl, hpair, ⟨f, hf⟩, hgenX,
    ⟨fJ, -⟩, hgenJ, hconj⟩ := hD
  let : Fintype Λ := instΛ
  let : DecidableEq Λ := decΛ
  let : AddCommGroup V' := instV
  let : Module (ZMod p) V' := instMod
  have hn : n ≤ Nat.card Λ :=
    hdRo7DAJAux_model_card_le (Λ := Λ) b ι hp3 (by omega) hsub ι' φ hv hα hformula hgenX
  have hΛcard : Nat.card Λ ≤ Nat.card {j : Λ // j ∉ S} + 3 := by
    have hEq : Nat.card Λ = Nat.card {j : Λ // j ∈ S} +
        Nat.card {j : Λ // j ∉ S} := by
      rw [← Nat.card_congr (Equiv.sumCompl (fun j : Λ => j ∈ S)), Nat.card_sum]
    have hSsub : Nat.card {j : Λ // j ∈ S} = S.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe S
    omega
  exact hdRo7DAJAux_nonabelian_of_data (p := p) (Bs := Bs) (J := J) (n := n) hn5 hWeylMJ
    fJ hΛcard hn

theorem d_aj_holds : DAJLeaf := by
  intro hX hJ hRig hLB G _ _ p B Bs x L D J y K hH inst hmL hmK hrow
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hI : GGThmIHyp p B x L := hcfg.1
  have hStd : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hJL : J ≤ L := by
    have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
      hStd.1.2.2.2.2.2.1
    exact hcomp.1.trans inf_le_left
  have hpJ : p ∣ Nat.card J := by
    rcases hrow with hrow | hrow
    · exact hdRo7DAJAux_three_dvd_card_of_row hrow
    · exact hdRo7DAJAux_three_dvd_card_of_row hrow
  have hJK : J ≤ K := le_of_ggNbr hLB hI hStd hpJ hH.2.2.2.2.1
  have hle : ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs :=
    le_inf (ggAutomizer_mono Bs hJL) (ggAutomizer_mono Bs hJK)
  refine ⟨?_, hle⟩
  rcases hrow with hrowL | hrowK
  · obtain ⟨n, V, hVadd, hVmod, ι, b, hx, hp3, hxb, hcase⟩ := hmL hrowL
    let : AddCommGroup V := hVadd
    let : Module (ZMod p) V := hVmod
    have hn5 : 5 ≤ n := by
      rcases hcase with ⟨h6, -⟩ | ⟨h5, -⟩ <;> omega
    have hsub : ∀ g : V ≃ₗ[ZMod p] V, DSP p b g →
        g ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) := by
      intro g hg
      rcases hcase with ⟨-, hp⟩ | ⟨-, hp⟩
      · exact (hp g).mpr hg
      · exact (hp g).mpr (hdRo7DAJAux_dsp_c2sp b hg)
    have hXD : GGResXDatum p Bs L := by
      rcases (hX G p B Bs x L D J y K hH).1 with h | h7
      · exact h
      · exfalso
        obtain ⟨-, -, -, -, -, -, hp7, -⟩ := h7
        omega
    rcases (hJ G p B Bs x L D J y K hH).1 hXD with hSD | hLE3 | hNL
    · exact hdRo7DAJAux_sideDatum_nonabelian b ι hp3 hn5 hsub hSD
    · exact hdRo7DAJAux_le3_nonabelian b ι hp3 hn5 hsub hLE3
    · exact (hdRo7DAJAux_not_nonLevi hRig hrowL hNL).elim
  · obtain ⟨n, V, hVadd, hVmod, ι, b, hy, hp3, hyb, hcase⟩ := hmK hrowK
    let : AddCommGroup V := hVadd
    let : Module (ZMod p) V := hVmod
    have hn5 : 5 ≤ n := by
      rcases hcase with ⟨h6, -⟩ | ⟨h5, -⟩ <;> omega
    have hsub : ∀ g : V ≃ₗ[ZMod p] V, DSP p b g →
        g ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) := by
      intro g hg
      rcases hcase with ⟨-, hp⟩ | ⟨-, hp⟩
      · exact (hp g).mpr hg
      · exact (hp g).mpr (hdRo7DAJAux_dsp_c2sp b hg)
    have hXD : GGResXDatum p Bs K := by
      rcases (hX G p B Bs x L D J y K hH).2 with h | h7
      · exact h
      · exfalso
        obtain ⟨-, -, -, -, -, -, hp7, -⟩ := h7
        omega
    rcases (hJ G p B Bs x L D J y K hH).2 hXD with hSD | hLE3 | hNL
    · exact hdRo7DAJAux_sideDatum_nonabelian b ι hp3 hn5 hsub hSD
    · exact hdRo7DAJAux_le3_nonabelian b ι hp3 hn5 hsub hLE3
    · exact (hdRo7DAJAux_not_nonLevi hRig hrowK hNL).elim

end CFSG.StandardType.HdRo7D
