module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FLinearField
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedSymplectic
public import CFSG.ClassicalInvolution.Q3.Q3YSModelSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FLift
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourLin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.SteinbergBR.EvenSp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem fieldSp_spPlane {K : Type} [Field K] (n : ℕ) (σ : K ≃+* K)
    (g : Fin n → SpecialLinearGroup (Fin 2) K) :
    fieldSp n K σ (spPlane n g) =
      spPlane n (fun j => SpecialLinearGroup.map σ.toRingHom (g j)) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSp, spPlane_val, spPlane_val]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [planeMat, SpecialLinearGroup.map_apply_coe, diagonal_apply] <;>
    split_ifs <;> simp

end CFSG.ClassicalInvolution.Q3.Q3YS

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem uc22s2114r4f_symplectic_field_descent {K : Type} [Field K] [Finite K]
    {n f r : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hr : r.Prime) (hr2 : r ≠ 2) (θ : MulAut (StatedProj (StatedSp n K)))
    (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : StatedProj (StatedSp n K) →*
      MulAut (StatedProj (StatedSp n K))).range) :
    r ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = r ∧
      ∃ δ : MulAut (StatedProj (StatedSp n K)), θ = δ * fieldAut n K σ * δ⁻¹ := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have := inner_normal (StatedProj (StatedSp n K))
  have O := spOuter Nat.prime_two hf hn hK
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hθE : θ ∈ spSemilinearAutGroup n K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hθ ▸ hr.odd_of_ne_two hr2)
  have hθD : θ ∉ spLinearAutGroup n K := fun hD =>
    hout (mem_of_pow_eq_one_of_relIndex_dvd_two
      (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hr hr2 hD hθr)
  obtain ⟨hrf, σ, hσ, δ, -, hδ⟩ := O.descent r hr θ hθE hθD hθ
  exact ⟨hrf, σ, hσ, δ, hδ⟩

theorem uc22s2114r4f_exists_fpf_nonsplit_symplectic {K : Type} [Field K] [Finite K]
    {n f r : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (σ : K ≃+* K) (hσ : orderOf σ = r) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* StatedProj (StatedSp n K), Function.Injective ι ∧
            ∀ a, fieldAut n K σ (ι a) = ι (κ a) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  obtain ⟨q, hq, hq7, hqr, -, -, Q, _, _, hQ, τ, hτ, j, hj, hσj⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_sl2 hf hK hr hr5 σ hσ
  let A := Q × Q
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 2) (by
    change Nat.card (Q × Q) = q ^ 2
    rw [Nat.card_prod, hQ]
    ring)
  have hAc : ¬ IsCyclic A := by
    intro hcyc
    have hcop := (Group.isCyclic_prod_iff.1 hcyc).2.2
    simp only [hQ] at hcop
    exact hq.ne_one (Nat.coprime_self q |>.1 hcop)
  let κ : A →* A := τ.prodMap τ
  have hκ : ∀ a : A, κ a = a → a = 1 := by
    intro a ha
    exact Prod.ext (hτ a.1 (congrArg Prod.fst ha)) (hτ a.2 (congrArg Prod.snd ha))
  let k0 : Fin n := ⟨0, by omega⟩
  let k1 : Fin n := ⟨1, by omega⟩
  have h01 : k0 ≠ k1 := by simp [k0, k1, Fin.ext_iff]
  let J : A →* (Fin n → SpecialLinearGroup (Fin 2) K) :=
    MonoidHom.pi fun i => if i = k0 then j.comp (MonoidHom.fst Q Q)
      else if i = k1 then j.comp (MonoidHom.snd Q Q) else 1
  have hJ : Function.Injective J := by
    intro a b hab
    apply Prod.ext
    · apply hj
      simpa [J, MonoidHom.fst] using congrFun hab k0
    · apply hj
      simpa [J, h01.symm, MonoidHom.snd] using congrFun hab k1
  have hproj : Function.Injective (proj n K) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    change (QuotientGroup.mk' _).ker = ⊥
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)
  let ι : A →* StatedProj (StatedSp n K) :=
    (proj n K).comp ((CFSG.ClassicalInvolution.Q3.Q3YS.spPlane n).comp J)
  have hι : Function.Injective ι := hproj.comp
    ((CFSG.ClassicalInvolution.Q3.Q3YS.spPlane_injective n).comp hJ)
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change fieldAut n K σ (proj n K (CFSG.ClassicalInvolution.Q3.Q3YS.spPlane n (J a))) =
    proj n K (CFSG.ClassicalInvolution.Q3.Q3YS.spPlane n (J (κ a)))
  rw [fieldAut_proj, CFSG.ClassicalInvolution.Q3.Q3YS.fieldSp_spPlane]
  congr 2
  funext i
  by_cases h0 : i = k0
  · subst i
    simpa [J, κ, MonoidHom.fst, MonoidHom.snd, MonoidHom.prodMap, MonoidHom.prod] using hσj a.1
  · by_cases h1 : i = k1
    · subst i
      simpa [J, κ, h01.symm, MonoidHom.fst, MonoidHom.snd, MonoidHom.prodMap,
        MonoidHom.prod] using hσj a.2
    · simp [J, h0, h1]

theorem uc22s2114r4f_exists_fixed_three_symplectic {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (σ : K ≃+* K) :
    ∃ X : Subgroup (StatedProj (StatedSp n K)), IsPGroup 3 X ∧ ¬ IsCyclic X ∧
      ∀ x ∈ X, fieldAut n K σ x = x := by
  obtain ⟨X, hX, hcard, hfix⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.exists_E9_fixed_fieldAut_sp hn σ
  exact ⟨X, hX.isPGroup, PartTwo.s16c7_not_isCyclic_of_elemAbelian Nat.prime_three
    hX (by rw [hcard]; norm_num), hfix⟩

theorem uc22s2114r4f_card_center_psp {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {n f : ℕ} (hn : 2 ≤ n) (hf : 3 ≤ f)
    (hX : LieModel (BarInf L) .PSp n 2 f) : Nat.card (center (Bar2 L)) ∣ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨-, ⟨ε⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier hn hK5
  have hMK : Nat.card (griessHopfMultiplier (StatedProj (StatedSp n K))) =
      Nat.gcd 2 (2 ^ f - 1) := by
    rw [Nat.card_congr ε.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hK]
  have hM : Nat.card (griessHopfMultiplier (BarInf L)) = Nat.gcd 2 (2 ^ f - 1) := by
    rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv,
      hMK]
  have : Finite (griessHopfMultiplier (BarInf L)) := Nat.finite_of_card_ne_zero (by
    rw [hM]
    exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 2)).ne')
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  rw [hM] at hd
  exact hd.trans (Nat.gcd_dvd_left 2 _)

theorem uc22s2114r4f_not_dvd_radical_psp {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {n f : ℕ} (hn : 2 ≤ n) (hf : 3 ≤ f)
    (hX : LieModel (BarInf L) .PSp n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL]
  intro hd
  rcases hq.dvd_mul.1 hd with h2 | hZ
  · obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
    rw [ha] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
      (hZ.trans (uc22s2114r4f_card_center_psp hL hn hf hX)))

theorem uc22s2114r4f_four_le_pRank_three_psp {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {n f : ℕ} (hn : 4 ≤ n) (hf : 3 ≤ f)
    (hX : LieModel (BarInf L) .PSp n 2 f) : 4 ≤ CFSG.Open.pRank 3 L := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := fun h => by
    have h2 := h.trans (uc22s2114r4f_card_center_psp hL (by omega) hf hX)
    norm_num at h2
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ :=
    (LieModel.of_mulEquiv eb hX).statedClassicalModel (by decide)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
    ← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three h3Z, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.four_le_pRank_projSp_of_four_le hn

theorem uc22s2114r4f_fieldSubgroups_of_psp {Y : Type} [Group Y] [Finite Y] {n f r : ℕ}
    (hn : 2 ≤ n) (hY : LieModel Y .PSp n 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hY.statedClassicalModel (by decide)
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : StatedProj (StatedSp n K) →* MulAut (StatedProj (StatedSp n K))).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hx]
  obtain ⟨hrf, σ, hσ, δ, hδ⟩ := uc22s2114r4f_symplectic_field_descent hn
    hadm.2.1 hK hr (by omega) (MulAut.congr e θ) hθ' hout'
  let ε : StatedProj (StatedSp n K) ≃* Y := δ.trans e.symm
  have hε : ∀ x, θ (ε x) = ε (fieldAut n K σ x) := by
    intro x
    have hx : (MulAut.congr e θ) (δ x) = δ (fieldAut n K σ x) := by
      simp [hδ, MulAut.mul_apply]
    have hx' := congrArg e.symm hx
    simpa [ε, MulAut.congr_apply] using hx'
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_symplectic hn σ
    let j : X →* Y := ε.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := ε.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg ε (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_nonsplit_symplectic hn hadm.2.1 hK hr hr5 σ hσ
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      ε.toMonoidHom.comp ι, ε.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg ε (hσι a))

theorem uc22s2114r4f_fieldDataBody_psp {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {n f : ℕ} (hn : 4 ≤ n) (hX : LieModel (BarInf L) .PSp n 2 f)
    {b : G} (hbL : b ∈ normalizer (L : Set G)) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p X ∧ ¬ IsCyclic X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨hrf, ⟨X, hXp, hXc, hXfix⟩, ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_psp (by omega) hX hr hr5
      (inducedBarInfAutHom L ⟨b, hbL⟩) (orderOf_eq_prime hθr hθ1) hin
  have hf : 3 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_psp hL (by omega) hf hX hr (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_psp hL hn hf hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_psp hL (by omega) hf hX hq (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
