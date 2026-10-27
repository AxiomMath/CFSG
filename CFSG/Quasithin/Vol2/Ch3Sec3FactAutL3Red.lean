module

public import CFSG.Quasithin.Vol2.KGFactAutSylowU35
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructM12
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.Quasithin.H13.L3Eps

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsL3EpsModel (p : ℕ) (W : Type) [Group W] : Prop :=
  p.Prime ∧ p ≠ 2 ∧ (IsPSL 3 p 1 W ∨ IsPSU 3 p 1 W)

section Models

theorem center_eq_bot_of_isQuasisimple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hq : CFSG.IsQuasisimple Q) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    have h1 : ∀ x : Q ⧸ Subgroup.center Q, x = 1 := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [QuotientGroup.eq_one_iff, h]
        trivial
    exact hab (by rw [h1 a, h1 b])

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def statedProjEquivOfSimple (H : Subgroup (GL ι K))
    (hq : CFSG.IsQuasisimple ↥H) (hs : IsSimpleGroup (StatedProj H)) [IsSimpleGroup ↥H] :
    ↥H ≃* StatedProj H :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    ((center_eq_bot_of_isQuasisimple hq).symm.trans (F6.InspRest.center_eq_statedScalars H hq hs)))

@[expose] noncomputable def statedProjSUCongr {n a b : ℕ} (h : a = b) :
    StatedProj (StatedSU n a K) ≃* StatedProj (StatedSU n b K) := by
  subst h
  exact MulEquiv.refl _

variable {W : Type} [Group W] {p : ℕ}

theorem isPSL_of_mulEquiv_statedSL (hp : p.Prime) [Finite K] (hK : Nat.card K = p)
    (hs : IsSimpleGroup W) (e : W ≃* ↥(StatedSL 3 K)) : IsPSL 3 p 1 W := by
  have : IsSimpleGroup ↥(StatedSL 3 K) := e.symm.isSimpleGroup
  refine ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance,
    by rw [pow_one, hK], ⟨e.trans (statedProjEquivOfSimple _
      (Gold14610.Struct.isQuasisimple_statedSL_three hp K hK)
      (Gold14610.Struct.isSimpleGroup_statedProj_statedSL_three hp K hK))⟩⟩

theorem isPSU_of_mulEquiv_statedSU (hp : p.Prime) (hp3 : 3 ≤ p) [Finite K]
    (hK : Nat.card K = p ^ 2) (hs : IsSimpleGroup W) (e : W ≃* ↥(StatedSU 3 p K)) :
    IsPSU 3 p 1 W := by
  have : IsSimpleGroup ↥(StatedSU 3 p K) := e.symm.isSimpleGroup
  refine ⟨⟨hp, le_rfl, le_rfl, ?_⟩, K, inferInstance, inferInstance, by rw [pow_one, hK], ?_⟩
  · simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
    omega
  · exact ⟨(e.trans (statedProjEquivOfSimple _
      (Gold14610.Struct.isQuasisimple_statedSU_three hp hp3 K hK)
      (Gold14610.Struct.isSimpleGroup_statedProj_statedSU_three hp hp3 K hK))).trans
      (statedProjSUCongr (pow_one p).symm)⟩

theorem isL3EpsModel_of_hyp (hs : IsSimpleGroup W)
    (h : (∃ p : ℕ, F6.IsSLEps3 p W) ∨ ∃ (s : Bool) (p : ℕ), p.Prime ∧ 2 < p ∧ IsPSLEps3 s p 1 W) :
    ∃ p : ℕ, IsL3EpsModel p W := by
  rcases h with ⟨p, hp, K, _, _, hK⟩ | ⟨s, p, hp, hp2, hW⟩
  · rcases hK with ⟨h1, h2, hf | hf⟩ | ⟨h1, h2, hf | hf⟩
    · obtain ⟨e⟩ := hf
      exact ⟨p, hp, by omega, Or.inl (isPSL_of_mulEquiv_statedSL hp h2 hs e)⟩
    · exact ⟨p, hp, by omega, Or.inl ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩, K,
        inferInstance, inferInstance, by rw [pow_one, h2], hf⟩⟩
    · obtain ⟨e⟩ := hf
      exact ⟨p, hp, by omega, Or.inr (isPSU_of_mulEquiv_statedSU hp (by omega) h2 hs e)⟩
    · refine ⟨p, hp, by omega, Or.inr ⟨⟨hp, le_rfl, le_rfl, ?_⟩, K, inferInstance,
        inferInstance, by rw [pow_one, h2], ?_⟩⟩
      · simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
        omega
      · obtain ⟨f⟩ := hf
        exact ⟨f.trans (statedProjSUCongr (pow_one p).symm)⟩
  · cases s
    · exact ⟨p, hp, by omega, Or.inr hW⟩
    · exact ⟨p, hp, by omega, Or.inl hW⟩

end Models

section Outer

variable {W : Type} [Group W] {p : ℕ}

theorem exists_noncomm_of_isL3EpsModel (h : IsL3EpsModel p W) : ∃ a b : W, a * b ≠ b * a := by
  obtain ⟨hp, hp2, hW | hW⟩ := h
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hW
    rw [pow_one] at hK
    obtain ⟨a, b, hab⟩ := F6.InspRest.exists_noncomm_statedProj _
      (Gold14610.Struct.isQuasisimple_statedSL_three hp K hK)
      (Gold14610.Struct.isSimpleGroup_statedProj_statedSL_three hp K hK)
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hW
    rw [pow_one] at hK
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨a, b, hab⟩ := F6.InspRest.exists_noncomm_statedProj _
      (Gold14610.Struct.isQuasisimple_statedSU_three hp hp3 K hK)
      (Gold14610.Struct.isSimpleGroup_statedProj_statedSU_three hp hp3 K hK)
    let e' : W ≃* StatedProj (StatedSU 3 p K) := e.trans (statedProjSUCongr (pow_one p))
    exact ⟨e'.symm a, e'.symm b, fun hc => hab (by simpa using congrArg e' hc)⟩

theorem conj_injective_of_isL3EpsModel [IsSimpleGroup W] (h : IsL3EpsModel p W) :
    Function.Injective (MulAut.conj : W →* MulAut W) :=
  Gold14610.Struct.conjHom_injective_of_center_eq_bot
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (exists_noncomm_of_isL3EpsModel h)).2

theorem not_four_dvd_card_outer (h : IsL3EpsModel p W) : ¬ 4 ∣ Nat.card (Outer W) := by
  obtain ⟨-, -, hW | hW⟩ := h
  · have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound W 3 p 1
      hW).2.2.2.2 (by norm_num)
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (p ^ 1 - 1)) with hg | hg <;>
      rw [hg] at hdvd <;> intro h4 <;> have := Nat.dvd_trans h4 hdvd <;> norm_num at this
  · have hcard := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound W 3 p 1
      hW).2.2.1
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (p ^ 1 + 1)) with hg | hg <;>
      rw [hcard, hg] <;> norm_num

end Outer

section Sylow

variable {W : Type} [Group W] [Finite W]

theorem isPGroup_mulAut_of_sylow (P₀ : Sylow 2 W) (hP₀ : IsPGroup 2 (MulAut ↥(P₀ : Subgroup W))) :
    ∀ P : Subgroup W, IsSylowTwoOf P ⊤ → IsPGroup 2 (MulAut ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP
  obtain ⟨hP2, hPi⟩ := K1.isSylowTwoOf_top_iff.mp hP
  let P' : Sylow 2 W := hP2.toSylow hPi
  have eP : ↥P ≃* ↥(P₀ : Subgroup W) :=
    (MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hP2 hPi).symm).trans (Sylow.equiv P' P₀)
  exact hP₀.of_equiv (MulAut.congr eP).symm

omit [Finite W] in
theorem exists_sylow_of_mulEquiv {T : Type} [Group T] (e : W ≃* T)
    (hT : ∃ P : Sylow 2 T, IsPGroup 2 (MulAut ↥(P : Subgroup T))) :
    ∃ P : Sylow 2 W, IsPGroup 2 (MulAut ↥(P : Subgroup W)) := by
  obtain ⟨P, hP⟩ := hT
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_comap_eq_of_injective P (f := e.symm.toMonoidHom)
    e.symm.injective
  have hmap : (P₀ : Subgroup W).map e.toMonoidHom = P := by
    rw [← hP₀]
    exact Subgroup.map_equiv_eq_comap_symm e _
  let f : ↥(P₀ : Subgroup W) ≃* ↥(P : Subgroup T) :=
    (e.subgroupMap (P₀ : Subgroup W)).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨P₀, hP.of_equiv (MulAut.congr f).symm⟩

theorem autOddNormCent_of_isL3EpsModel [IsSimpleGroup W] {p : ℕ} (h : IsL3EpsModel p W)
    (hsyl : ∃ P : Sylow 2 W, IsPGroup 2 (MulAut ↥(P : Subgroup W))) : AutOddNormCent W := by
  obtain ⟨P₀, hP₀⟩ := hsyl
  exact KGAutSyl.autOddNormCent_of (conj_injective_of_isL3EpsModel h)
    (isPGroup_mulAut_of_sylow P₀ hP₀) (not_four_dvd_card_outer h)

end Sylow

end CFSG.Quasithin.H13.L3Eps
