module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Core
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Model
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Parity
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Open CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def GGTBJTwE6NoncommAt (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ₀ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p 5 R I L' ψ₀ A → ∀ y : MulAut L', y ∈ A → y ≠ 1 → ∀ J : Subgroup L',
      CFSG.Open.IsComponentOf J (fixSubgroup y) →
      (∀ Q : Subgroup L', CFSG.Open.IsComponentOf Q (fixSubgroup y) → Q ≤ J) →
      p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
        Nat.card ↥A →
      ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
        (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
        GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
        ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁


theorem ggTBJ_twE6_torusJNoncomm {K : Type} [Field K] [Finite K] {n p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) :
    GGTBJTwE6NoncommAt p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  intro L' _ _ ψ₀ A hA y hy hy1 J hJ hJl hcount
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn : 2 ≤ n := by
    by_contra hn
    push Not at hn
    interval_cases n
    · have := Nat.le_of_dvd (by norm_num) hpq
      omega
    · have := Nat.le_of_dvd (by norm_num) hpq
      omega
  obtain ⟨σ, hσ, E, F, ζ, hζ, T, ψ, σ', Θ, -, hv, hTinj, hT, hψ, hker, hσ', hΘ⟩ :=
    ggTBJ_twE6_stdModel (by omega) hK hp5 hpq ψ₀ A hA
  let f₀ : Multiplicative (Fin Tag.E6.rank → ZMod p) := Θ.symm ⟨y, hy⟩
  have hΘf₀ : Θ f₀ = ⟨y, hy⟩ := MulEquiv.apply_symm_apply Θ _
  have hy_eq : y = MulAut.conj (σ' f₀) := by rw [← hΘ f₀, hΘf₀]
  have hf₀ : f₀ ≠ 1 := by
    intro h
    apply hy1
    rw [hy_eq, h, map_one, map_one]
  have hfix : fixSubgroup y = Subgroup.centralizer ({σ' f₀} : Set L') := by
    ext x
    rw [mem_fixSubgroup, hy_eq, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => (mul_inv_eq_iff_eq_mul.mp h).symm,
      fun h => mul_inv_eq_iff_eq_mul.mpr h.symm⟩
  have hJ' : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({σ' f₀} : Set L')) := by
    rw [hfix] at hJ
    exact hJ
  have hJl' : ∀ Q : Subgroup L',
      CFSG.Open.IsComponentOf Q (Subgroup.centralizer ({σ' f₀} : Set L')) → Q ≤ J := by
    intro Q hQ
    rw [← hfix] at hQ
    exact hJl Q hQ
  let B : Subgroup (MulAut L') := A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')
  have hcardB : Nat.card ↥B = Nat.card {f : Multiplicative (Fin Tag.E6.rank → ZMod p) //
      ∀ j ∈ J, σ' f * j = j * σ' f} := by
    refine Nat.card_congr ?_
    let toF : ↥B → {f : Multiplicative (Fin Tag.E6.rank → ZMod p) //
        ∀ j ∈ J, σ' f * j = j * σ' f} := fun b =>
      let f : Multiplicative (Fin Tag.E6.rank → ZMod p) :=
        Θ.symm ⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩
      ⟨f, by
        intro j hj
        have hbj : (b : MulAut L') j = j := by
          have h := MulAction.mem_stabilizer_iff.mp
            (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp b.2).2 ⟨j, hj⟩)
          simpa [MulAut.smul_def] using h
        have hbf : (b : MulAut L') = MulAut.conj (σ' f) := by
          have hfA : Θ f = (⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩ : ↥A) :=
            MulEquiv.apply_symm_apply Θ _
          rw [← hΘ f]
          exact (congrArg Subtype.val hfA).symm
        rw [hbf, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hbj
        exact hbj⟩
    let toG : {f : Multiplicative (Fin Tag.E6.rank → ZMod p) //
        ∀ j ∈ J, σ' f * j = j * σ' f} → ↥B :=
      fun c => ⟨((Θ c.1 : ↥A) : MulAut L'), by
        refine Subgroup.mem_inf.mpr ⟨(Θ c.1).2, ?_⟩
        rw [Subgroup.mem_iInf]
        intro j
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hΘ, MulAut.conj_apply]
        have hcomm := c.2 j j.2
        rw [hcomm]
        group⟩
    refine ⟨toF, toG, ?_, ?_⟩
    · intro b
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.apply_symm_apply]
    · intro c
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.symm_apply_eq]
  have hcardV : Nat.card (Multiplicative (Fin Tag.E6.rank → ZMod p)) = p ^ 6 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have hcardA : Nat.card ↥A = p ^ 6 := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact hcardV
  have hcount' : p ^ 2 * Nat.card {f : Multiplicative (Fin Tag.E6.rank → ZMod p) //
      ∀ j ∈ J, σ' f * j = j * σ' f} ≤ p ^ 6 := by
    rw [← hcardB, ← hcardA]
    exact hcount
  obtain ⟨m₁, m₂, s₁, s₂, hm₁, hm₂, hform₁, hform₂, hs₁, hs₂, hfix₁, hfix₂, hne⟩ :=
    ggTBJ_twE6_core hn hK hσ hp5 hpq F hv hζ hTinj hT ψ hψ hker σ' hσ' f₀ hf₀ hJ' hJl' hcount'
  obtain ⟨hn₁, heq₁⟩ := exists_ggConjAut_eq_congr (n := m₁) (s := s₁) hker Θ hΘ hform₁
  obtain ⟨hn₂, heq₂⟩ := exists_ggConjAut_eq_congr (n := m₂) (s := s₂) hker Θ hΘ hform₂
  have hfixV₁ : Nat.card {f : Multiplicative (Fin Tag.E6.rank → ZMod p) // s₁ f = f} * p =
      Nat.card (Multiplicative (Fin Tag.E6.rank → ZMod p)) := by
    rw [hcardV]; exact hfix₁
  have hfixV₂ : Nat.card {f : Multiplicative (Fin Tag.E6.rank → ZMod p) // s₂ f = f} * p =
      Nat.card (Multiplicative (Fin Tag.E6.rank → ZMod p)) := by
    rw [hcardV]; exact hfix₂
  have hrefl₁ : GGIsReflection p (MulAut.congr Θ s₁) :=
    ⟨by rw [← map_pow, hs₁, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₁) hfixV₁).2⟩
  have hrefl₂ : GGIsReflection p (MulAut.congr Θ s₂) :=
    ⟨by rw [← map_pow, hs₂, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₂) hfixV₂).2⟩
  have hrefl₁' : GGIsReflection p (ggConjAut A hn₁) := by rw [heq₁]; exact hrefl₁
  have hrefl₂' : GGIsReflection p (ggConjAut A hn₂) := by rw [heq₂]; exact hrefl₂
  have hne' : MulAut.congr Θ s₁ * MulAut.congr Θ s₂ ≠
      MulAut.congr Θ s₂ * MulAut.congr Θ s₁ := by
    intro h
    apply hne
    apply (MulAut.congr Θ).injective
    rw [map_mul, map_mul]
    exact h
  have hconjne : ggConjAut A hn₁ * ggConjAut A hn₂ ≠ ggConjAut A hn₂ * ggConjAut A hn₁ := by
    rw [heq₁, heq₂]
    exact hne'
  exact ⟨m₁, m₂, hn₁, hn₂, hm₁, hm₂,
    ggTorusWeylElt_of_model hker Θ hΘ (fun f => ⟨s₁ f, hform₁ f⟩),
    ggTorusWeylElt_of_model hker Θ hΘ (fun f => ⟨s₂ f, hform₂ f⟩),
    hrefl₁', hrefl₂', hconjne⟩

theorem ggTBJTwE6Row_labelAll {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTBTwE6PlusLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift p 5 R ∧ GGTBJTwE6NoncommAt p R I := by
  obtain ⟨htag, hpn, hp3⟩ := h
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by norm_num)
    have h2' : p ≠ 2 := by
      rintro rfl
      have h0 : 1 ≤ lab.n := hlab.1
      have : (2 : ℕ) ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).1 hpn
      omega
    omega
  have hW : LargeEvenLabelAll lab fun R _ I _ => GGTBJTwE6NoncommAt p R I :=
    TwE6Delta.labelAll htag fun K _ _ hK => ggTBJ_twE6_torusJNoncomm hp hp5 hK hpn
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨htag, hpn⟩) hW).mono
    fun _ _ _ _ ⟨hl, hw⟩ => ⟨?_, hw⟩
  rwa [TwE6Delta.liftRank_of_ne hp3] at hl

theorem ggTBJTorusNoncommAt_of_twE6Plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hLF : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : GGTBJTorusNoncommAt p Bs L hN := by
  intro y hy hy1 J' hJ' hJl hcount
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := GGTBTwE6PlusLabel p)
    (fun lab hlab hs => nbrC_labelAll_guard (ggTBJTwE6Row_labelAll hp hlab hs))
    (fun _ _ _ _ _ _ hP => hP.1) hLF
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, hlift, hNC⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  exact hNC L (ggQuotHom θ) _ hTB y hy hy1 J' hJ' hJl hcount

theorem ggTBJTorusNoncomm_rowR6 (hRig : GGLabelRigidInput) :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR6 p lab := by
  intro G _ _ p B Bs x L D J hHyp _hq _hok hL hN
  exact ggTBJTorusNoncommAt_of_twE6Plus hHyp.1
    (ggInnerDiagOnLabel_twE6Plus_of_rowR6 hRig hHyp hL) hN

theorem ggTBJNaWeylQFourOn_rowR6 (hRig : GGLabelRigidInput) :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR6 p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm (ggTBJTorusNoncomm_rowR6 hRig)

end CFSG.StandardType

end
