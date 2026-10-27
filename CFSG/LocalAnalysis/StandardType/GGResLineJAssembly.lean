module

public import CFSG.LocalAnalysis.StandardType.GGResLineJCells
public import CFSG.LocalAnalysis.StandardType.GGResJPairedBlock
public import CFSG.LocalAnalysis.StandardType.GGResJA2UnitaryRecognition
public import CFSG.LocalAnalysis.StandardType.GGResJPairedRankTwo
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.HardMathSupport.Curtis.Coordinator.AutBounds
import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
import CFSG.LocalAnalysis.StandardType.GGResJB2derA2
import CFSG.LocalAnalysis.StandardType.GGResLineJB2Small
import CFSG.LocalAnalysis.StandardType.GGResJB2OppositeLinear
import CFSG.LocalAnalysis.StandardType.GGResJB3C3MatchedUnitary
import CFSG.LocalAnalysis.StandardType.GGResJB2MatchedUnitary
import CFSG.LocalAnalysis.StandardType.GGTwE6E4bOriginalA2

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResLineJCell.of_D3 {T : GGResLineJType} {s : ℕ → Prop}
    (h : GGResLineJCell T fun lab => lab.tag = .A ∧ lab.rank = 3 ∧ s lab.n) :
    GGResLineJCell T fun lab => lab.tag = .D ∧ lab.rank = 3 ∧ s lab.n := by
  intro G _ _ B Bs x L D J y K hH _ hD hM
  exact h G B Bs x L D J y K hH hD (ggInnerDiagOnLabel_D3_to_A3 (S := s) hM)

theorem GGResLineJCell.of_twD3 {T : GGResLineJType} {s : ℕ → Prop}
    (h : GGResLineJCell T fun lab => lab.tag = .twA ∧ lab.rank = 3 ∧ s lab.n) :
    GGResLineJCell T fun lab => lab.tag = .twD ∧ lab.rank = 3 ∧ s lab.n := by
  intro G _ _ B Bs x L D J y K hH _ hD hM
  exact h G B Bs x L D J y K hH hD (ggInnerDiagOnLabel_twD_to_twA (S := s) hM)

theorem ggInnerDiagOnLabel_twD2_to_A1 {G : Type} [Group G] {Bs L : Subgroup G} {p : ℕ}
    {S : ℕ → Prop}
    (h : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twD ∧ lab.rank = 2 ∧ S lab.n) p Bs L) :
    GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ lab.rank = 1 ∧ ∃ m, lab.n = 2 * m ∧ S m) p Bs L := by
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP⟩ := hQ
  obtain ⟨hS0, _, _⟩ := hP
  obtain ⟨htag, hrank, hS⟩ : tag = .twD ∧ rank = 2 ∧ S n := by
    simpa only using hS0
  subst htag
  subst hrank
  let lab₁ : LargeEvenLabel := ⟨.twD, 2, n⟩
  let lab₂ : LargeEvenLabel := ⟨.A, 1, 2 * n⟩
  let P : Q1DSmall.LargeEvenMarkCont ↥L := fun _ _ I _ θ => S n ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  have hΛ₁ : LargeEvenInLambda2 lab₁ := by
    simpa only [lab₁] using hΛ
  have hrawFix : LargeEvenRawDatum lab₁ (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R, lab₁ = lab₁ ∧ P R I F θ) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hS, hN, hInd⟩
    exact ⟨hs, hna, θ, rfl, hS.2.2, hN, hInd⟩
  have hFix : LargeEvenMarking ↥L (fun lab R _ I F θ => lab = lab₁ ∧ P R I F θ) :=
    ⟨hperf, lab₁, hΛ₁, hrawFix⟩
  have hTarget : LargeEvenMarking ↥L (fun lab R _ I F θ => lab = lab₂ ∧ P R I F θ) :=
    (Q1DSmall.largeEvenMarking_twD2_iff_A1 n).1 hFix
  unfold GGInnerDiagOnLabel
  refine largeEvenMarking_mono ?_ hTarget
  rintro lab R _ I F θ ⟨hlab, hS, hN, hInd⟩
  rw [hlab]
  exact ⟨⟨rfl, rfl, n, rfl, hS⟩, hN, hInd⟩

theorem GGResLineJCell.of_twD2 {T : GGResLineJType} {s : ℕ → Prop}
    (h : GGResLineJCell T fun lab => lab.tag = .A ∧ lab.rank = 1 ∧ ∃ m, lab.n = 2 * m ∧ s m) :
    GGResLineJCell T fun lab => lab.tag = .twD ∧ lab.rank = 2 ∧ s lab.n := by
  intro G _ _ B Bs x L D J y K hH _ hD hM
  exact h G B Bs x L D J y K hH hD (ggInnerDiagOnLabel_twD2_to_A1 (S := s) hM)

private theorem three_dvd_two_pow_two_mul_sub_one (m : ℕ) : 3 ∣ 2 ^ (2 * m) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 4 1 m
  rw [one_pow, show (4 : ℕ) - 1 = 3 by rfl] at h
  rwa [pow_mul, show (2 : ℕ) ^ 2 = 4 by rfl]

private theorem ggHasLabel_of_innerDiagOnLabel_eq {G : Type} [Group G] {Bs J : Subgroup G}
    {lab0 : LargeEvenLabel} (h : GGInnerDiagOnLabel (fun _ lab => lab = lab0) 3 Bs J) :
    GGHasLabel lab0 (J ⧸ Subgroup.center J) := by
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab = lab0 := hP.1
  subst hlab
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨-, -, θ, -⟩
  exact ⟨θ⟩

private theorem not_three_dvd_card_largeEvenSzGroup
    {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ 3 ∣ Nat.card (LargeEvenSzGroup a K) := by
  rw [largeEvenSzGroup_eq, CFSG.LieType.Ree.suzuki_order hK]
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = q2 at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
  · omega

private theorem card_lt_nine_of_elemAbelian_three_largeEvenSzGroup
    {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {E : Subgroup (LargeEvenSzGroup a K)} (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E < 3 ^ 2 := by
  have h3 : ¬ 3 ∣ Nat.card (LargeEvenSzGroup a K) :=
    not_three_dvd_card_largeEvenSzGroup hK
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hE)
  have hdvd : 3 ^ m ∣ Nat.card (LargeEvenSzGroup a K) :=
    hm ▸ Subgroup.card_subgroup_dvd_card E
  have hm0 : m = 0 := by
    by_contra h
    have h1 : 1 ≤ m := Nat.pos_of_ne_zero h
    have h3dvd : 3 ∣ 3 ^ m :=
      dvd_trans (by norm_num : 3 ∣ 3 ^ 1) (pow_dvd_pow 3 h1)
    exact h3 (h3dvd.trans hdvd)
  rw [hm, hm0, pow_zero]
  norm_num

theorem GGResHyp.not_twB2_marking {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twB2) 3 Bs J) : False := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hM
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  have htag : tag = .twB2 := hS
  subst htag
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K', hKfield, hKfinite, hKcard, hP⟩ := hraw
  obtain ⟨_hsimple, _hnonab, θ, _hS', hN, hind⟩ := hP
  let : Field K' := hKfield
  let : Finite K' := hKfinite
  have ha : 1 ≤ (n - 1) / 2 := by
    obtain ⟨k, hk⟩ := hΛ.2.2.1
    have hn3 : 3 ≤ n := hΛ.2.2.2
    omega
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN)
  let B' : Subgroup (MulAut (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K'))) :=
    A.map (ggInducedAut θ)
  have hBcard : Nat.card B' = Nat.card A :=
    Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hperfJ θ)
  have hBe : CFSG.Open.IsElemAbelian 3 B' := hAe.map _
  have hBI : (B' : Set (MulAut (LargeEvenCenterQuot
      (LargeEvenSzGroup ((n - 1) / 2) K')))) ⊆
      LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K')) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, rfl⟩ := ha
    have hmem := ggBeta_mem J θ hN hind b
    have hbeta : ggBeta J θ hN b = ggInducedAut θ (ggGamma J hN b) := by
      rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
      rfl
    rwa [hbeta] at hmem
  have hZ : Subgroup.center (LargeEvenSzGroup ((n - 1) / 2) K') = ⊥ := by
    rw [largeEvenSzGroup_eq]
    exact CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot (a := (n - 1) / 2) ha hKcard
  let e : LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K') ≃*
      LargeEvenSzGroup ((n - 1) / 2) K' :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Finite (LargeEvenSzGroup ((n - 1) / 2) K') := Subtype.finite
  have : Finite (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K')) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hbound : ∀ A' : Subgroup (LargeEvenSzGroup ((n - 1) / 2) K'),
      CFSG.Open.IsElemAbelian 3 A' → Nat.card A' < 3 ^ 2 :=
    fun A' hA' => card_lt_nine_of_elemAbelian_three_largeEvenSzGroup hKcard hA'
  have hlt : Nat.card B' < 3 ^ 2 :=
    TableBExcSmallRest.card_lt_of_subset_inn
      (TableBExcSmallRest.center_eq_bot_of_mulEquiv e hZ)
      (fun A' hA' => TableBExcSmallRest.card_lt_of_mulEquiv e hbound hA') hBI hBe
  have h9 : 9 ≤ Nat.card A := by
    have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
    simpa [A, hgamma] using h
  rw [hBcard] at hlt
  have hlt9 : Nat.card A < 9 := by simpa using hlt
  omega

theorem ggResLineJCell_twB2 (T : GGResLineJType) :
    GGResLineJCell T fun lab => lab.tag = .twB2 :=
  fun _ _ _ _ _ _ _ _ _ _ _ hH _ _ hM => (GGResHyp.not_twB2_marking hH hM).elim

theorem false_of_lineJDatum_A2_of_card_gamma_le_nine {G : Type} [Group G] [Finite G]
    {B Bs J : Subgroup G} (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hNoTr : GGNoTransvection 3 Bs) (hD : GGResLineJDatum 3 Bs J .A2)
    (hγ : Nat.card (ggGamma J hN).range ≤ 9)
    (hZ : Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) = ⊥) : False := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  let _ : AddCommGroup V := instA
  let _ : Module (ZMod 3) V := instM
  have hCommBs : IsMulCommutative ↥Bs := hBs.2.1.1
  let _ : CommGroup ↥Bs := IsMulCommutative.instCommGroup
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hmem : ∀ j : Fin 2, r j ∈ ggAutomizer J Bs := by
    intro j
    rw [hgen]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hroots : LinearIndependent (ZMod 3) α :=
    linearIndependent_roots_of_lineJDatum_A2 ι hform hpair hind hmem hNoTr
  let E : Subgroup G := Bs ⊓ J
  let U : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hEle : E ≤ Bs := inf_le_left
  have hUle : U ≤ Bs := inf_le_left
  let inclE : ↥E →* ↥Bs := Subgroup.inclusion hEle
  let inclU : ↥U →* ↥Bs := Subgroup.inclusion hUle
  have hEea : CFSG.IsElementaryAbelian 3 ↥E := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subgroup.inclusion_injective hEle
      rw [map_mul, map_mul]
      exact mul_comm _ _
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      have hx : ((x : ↥E) : G) ^ 3 = 1 := hBs.2.1.2 ((x : ↥E) : G) (inclE x).2
      simpa using hx
  have hUea : CFSG.IsElementaryAbelian 3 ↥U := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subgroup.inclusion_injective hUle
      rw [map_mul, map_mul]
      exact mul_comm _ _
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      have hx : ((x : ↥U) : G) ^ 3 = 1 := hBs.2.1.2 ((x : ↥U) : G) (inclU x).2
      simpa using hx
  let _ : CommGroup ↥E := IsMulCommutative.instCommGroup
  let _ : CommGroup ↥U := IsMulCommutative.instCommGroup
  let _ : Module (ZMod 3) (Additive ↥E) := CFSG.IsElementaryAbelian.isVectorSpace 3
  let _ : Module (ZMod 3) (Additive ↥U) := CFSG.IsElementaryAbelian.isVectorSpace 3
  let φadd : Additive ↥E →+ V := ι.toAddMonoidHom.comp (MonoidHom.toAdditive inclE)
  let φ : Additive ↥E →ₗ[ZMod 3] V := φadd.toZModLinearMap 3
  let ψadd : Additive ↥U →+ V := ι.toAddMonoidHom.comp (MonoidHom.toAdditive inclU)
  let ψ : Additive ↥U →ₗ[ZMod 3] V := ψadd.toZModLinearMap 3
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  let U' : Submodule (ZMod 3) V := LinearMap.range ψ
  have hmemW : ∀ i : Fin 2, h i ∈ LinearMap.range φ := by
    intro i
    obtain ⟨e, he⟩ := GGResLineJDatum.exists_mem_inf_of_coroot hN hform hpair hgen i
    exact LinearMap.mem_range.mpr ⟨Additive.ofMul e, by simpa [φ, φadd] using he⟩
  have hWle : W ≤ LinearMap.range φ := by
    rw [show W = Submodule.span (ZMod 3) (Set.range h) from rfl, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmemW i
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : Additive.ofMul (inclU (Additive.toMul x)) =
        Additive.ofMul (inclU (Additive.toMul y)) := by
      apply ι.injective
      simpa [ψ, ψadd] using hxy
    have h2 := Additive.ofMul.injective h1
    have h3 := Subgroup.inclusion_injective hUle h2
    simpa using h3
  have hdisj : W ⊓ U' = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxU⟩ := Submodule.mem_inf.mp hx
    obtain ⟨e, he⟩ := LinearMap.mem_range.mp (hWle hxW)
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hxU
    have hincl : inclE e = inclU u := by
      have h1 : Additive.ofMul (inclE e) = Additive.ofMul (inclU u) := by
        apply ι.injective
        rw [show ι (Additive.ofMul (inclE e)) = φ e from rfl,
          show ι (Additive.ofMul (inclU u)) = ψ u from rfl, he, hu]
      simpa using Additive.ofMul.injective h1
    have heqG : ((inclE e : ↥Bs) : G) = ((inclU u : ↥Bs) : G) := by
      simpa using congrArg (fun b : ↥Bs => (b : G)) hincl
    have hbot : ((inclE e : ↥Bs) : G) ∈
        Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_inf.mpr ⟨(inclE e).2, (Subgroup.mem_inf.mp e.2).2⟩
      · rw [heqG]
        exact (Subgroup.mem_inf.mp u.2).2
    have hg1 : ((inclE e : ↥Bs) : G) = 1 := by
      rw [hZ] at hbot
      exact Subgroup.mem_bot.mp hbot
    have he1 : e = 0 := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hg1
    rw [← he, he1, map_zero]
  have hker : (ggGamma J hN).ker = (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hkerCard : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf Bs) =
      Nat.card ↥U := by
    rw [show U = Bs ⊓ Subgroup.centralizer (J : Set G) from rfl, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcount := Subgroup.card_ker_mul_card_range (ggGamma J hN)
  rw [hker, hkerCard] at hcount
  have hcount' : Nat.card (ggGamma J hN).range * Nat.card ↥U = Nat.card ↥Bs := by
    rw [mul_comm]
    exact hcount
  have hVcard : Nat.card V = Nat.card ↥Bs :=
    (Nat.card_congr ι.toEquiv).symm.trans (Nat.card_congr Additive.toMul)
  have hVle : Nat.card V ≤ 9 * Nat.card ↥U := by
    rw [hVcard]
    calc Nat.card ↥Bs = Nat.card (ggGamma J hN).range * Nat.card ↥U := hcount'.symm
      _ ≤ 9 * Nat.card ↥U := Nat.mul_le_mul_right _ hγ
  have hfinW : Module.finrank (ZMod 3) W = 2 := by
    rw [show W = Submodule.span (ZMod 3) (Set.range h) from rfl,
      finrank_span_eq_card hind, Fintype.card_fin]
    rfl
  have hfinU' : Module.finrank (ZMod 3) U' =
      Module.finrank (ZMod 3) (Additive ↥U) := by
    simpa [U'] using LinearMap.finrank_range_of_inj (f := ψ) hψinj
  have hfinSup : Module.finrank (ZMod 3) ↥(W ⊔ U') =
      Module.finrank (ZMod 3) W + Module.finrank (ZMod 3) U' := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W U'
    rw [hdisj] at h
    rw [show Module.finrank (ZMod 3) (⊥ : Submodule (ZMod 3) V) = 0 from
      finrank_bot (ZMod 3) V, add_zero] at h
    exact h
  have hcardSupPow : Nat.card ↥(W ⊔ U') =
      3 ^ (2 + Module.finrank (ZMod 3) (Additive ↥U)) := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 ↥(W ⊔ U'), hfinSup, hfinU', hfinW]
  have hUcard : 3 ^ Module.finrank (ZMod 3) (Additive ↥U) = Nat.card ↥U := by
    rw [FiniteField.pow_finrank_eq_natCard 3 (Additive ↥U), Nat.card_congr Additive.toMul]
  have hcardSup : Nat.card ↥(W ⊔ U') = 9 * Nat.card ↥U := by
    rw [hcardSupPow, pow_add, hUcard]
    norm_num
  have hVle' : Nat.card V ≤ Nat.card ↥(W ⊔ U') := by
    rw [hcardSup]
    exact hVle
  have hfinV : Module.finrank (ZMod 3) V ≤ Module.finrank (ZMod 3) ↥(W ⊔ U') := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 V,
      ← FiniteField.pow_finrank_eq_natCard 3 ↥(W ⊔ U')] at hVle'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hVle'
  have htop : W ⊔ U' = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    refine le_antisymm ?_ hfinV
    simpa using Submodule.finrank_mono (le_top : W ⊔ U' ≤ ⊤)
  have hαW : ∀ w ∈ W, α (0 : Fin 2) w = α (1 : Fin 2) w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have h0 := hpair (0 : Fin 2) j
      have h1 := hpair (1 : Fin 2) j
      have hrow : ((GGResLineJType.cartan .A2) (0 : Fin 2) j : ZMod 3) =
          ((GGResLineJType.cartan .A2) (1 : Fin 2) j : ZMod 3) := by
        fin_cases j <;> decide
      rw [h0, h1, hrow]
    | zero => simp
    | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
    | smul a x hx ih => simp [map_smul, ih]
  have hαU : ∀ i : Fin 2, ∀ u : ↥U, α i (ι (Additive.ofMul (inclU u))) = 0 := by
    intro i u
    have hmem_u : ((inclU u : ↥Bs) : G) ∈
        Bs ⊓ Subgroup.centralizer (J : Set G) :=
      ⟨(inclU u).2, (Subgroup.mem_inf.mp u.2).2⟩
    have hfix := B48Om.ggAutomizer_central_factor_fixed (Bs := Bs) (J := J)
      (φ := ⟨r i, hmem i⟩) (u := ((inclU u : ↥Bs) : G)) hmem_u
    have hform_u := hform i (ι (Additive.ofMul (inclU u)))
    rw [ggLin_apply_ofMul (p := 3)] at hform_u
    have hfix' : (r i) (inclU u) = inclU u := hfix
    rw [hfix'] at hform_u
    have hzero : α i (ι (Additive.ofMul (inclU u))) • h i = 0 := by
      have heq := hform_u
      have h' : ι (Additive.ofMul (inclU u)) -
          (ι (Additive.ofMul (inclU u)) -
            α i (ι (Additive.ofMul (inclU u))) • h i) = 0 := by
        rw [← heq, sub_self]
      rwa [sub_sub_cancel] at h'
    exact (smul_eq_zero.mp hzero).resolve_right (hind.ne_zero i)
  have hαV : α (0 : Fin 2) = α (1 : Fin 2) := by
    ext v
    have hv : v ∈ W ⊔ U' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨w, hw, u, hu, hwu⟩ := Submodule.mem_sup.mp hv
    obtain ⟨u0, rfl⟩ := LinearMap.mem_range.mp hu
    have h0 : α (0 : Fin 2) (ψ u0) = 0 := by
      simpa [ψ, ψadd] using hαU (0 : Fin 2) (Additive.toMul u0)
    have h1 : α (1 : Fin 2) (ψ u0) = 0 := by
      simpa [ψ, ψadd] using hαU (1 : Fin 2) (Additive.toMul u0)
    rw [← hwu, map_add, map_add, hαW w hw, h0, h1, add_zero]
  exact (by decide : (0 : Fin 2) ≠ 1) (hroots.injective hαV)

abbrev ggResLineJSmallLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

private theorem torsBound_three_of_smallLabel {lab : LargeEvenLabel}
    (h : ggResLineJSmallLabel lab) :
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound 3
      (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = 1 := by
  obtain ⟨t, l, n⟩ := lab
  rcases h with rfl | rfl | rfl | rfl | rfl
  · by_cases hn : n = 2
    · subst hn
      norm_num [markTag, markRank, markChar, markDeg,
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound,
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.tors,
        CFSG.Blueprint.Multiplier.genericOrders,
        CFSG.Blueprint.Multiplier.exceptionalOrders]
    · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 2 n = (1, 1) := by
        unfold CFSG.Blueprint.Multiplier.exceptionalOrders
        split <;> simp_all
      norm_num [markTag, markRank, markChar, markDeg,
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound,
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.tors,
        CFSG.Blueprint.Multiplier.genericOrders, he]
  · norm_num [markTag, markRank, markChar, markDeg,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.tors,
      CFSG.Blueprint.Multiplier.genericOrders,
      CFSG.Blueprint.Multiplier.exceptionalOrders]
  · norm_num [markTag, markRank, markChar, markDeg,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.tors,
      CFSG.Blueprint.Multiplier.genericOrders,
      CFSG.Blueprint.Multiplier.exceptionalOrders]
  · norm_num [markTag, markRank, markChar, markDeg,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.tors,
      CFSG.Blueprint.Multiplier.genericOrders,
      CFSG.Blueprint.Multiplier.exceptionalOrders]
  · norm_num [markTag, markRank, markChar, markDeg,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound,
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.tors,
      CFSG.Blueprint.Multiplier.genericOrders,
      CFSG.Blueprint.Multiplier.exceptionalOrders]

theorem ggResLineJCell_A2_B2der :
    GGResLineJCell .A2 fun lab => lab.tag = .B2der := by
  refine GGResLineJCell.of_forall_eq fun lab0 hΛ0 hS0 => ?_
  obtain ⟨t, r, n⟩ := lab0
  obtain rfl : t = .B2der := hS0
  obtain ⟨rfl, rfl⟩ : r = 0 ∧ n = 1 := hΛ0.2
  exact fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
    (GGResHyp.not_B2der_of_lineJDatum_A2 hH hD (ggHasLabel_of_innerDiagOnLabel_eq hM)).elim

section Certificates


theorem GGResHyp.card_gamma_J_le_nine_of_smallLabel {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => ggResLineJSmallLabel lab) 3 Bs J) :
    Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range ≤ 9 := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hM
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  have hAll : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 := by
    rcases hS with ht | ht | ht | ht | ht
    · exact largeEvenLabelAll_card_lt_nineSmall (p := 3) Nat.prime_three (by norm_num) hΛ
        (Or.inl ht)
    · exact ggCSR_triD4 hΛ ht
    · exact ggCSR_twF4 hΛ ht
    · exact largeEvenLabelAll_card_lt_nineSmall (p := 3) Nat.prime_three (by norm_num) hΛ
        (Or.inr (Or.inl ht))
    · exact largeEvenLabelAll_card_lt_nineSmall (p := 3) Nat.prime_three (by norm_num) hΛ
        (Or.inr (Or.inr (Or.inl ht)))
  obtain ⟨R, _, I, F, ⟨⟨_, _, θ, _, hNmark, hind⟩, hlt⟩⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hNmark = ggGamma J hN0 := by ext b; rfl
  let A : Subgroup (MulAut ↥J) := (ggGamma J hNmark).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hNmark)
  let B' : Subgroup (MulAut R) := A.map (ggInducedAut θ)
  have hBcard : Nat.card B' = Nat.card A :=
    Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hperfJ θ)
  have hBe : CFSG.Open.IsElemAbelian 3 B' := hAe.map _
  have hBI : (B' : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, rfl⟩ := ha
    have hmem := ggBeta_mem J θ hNmark hind b
    have hbeta : ggBeta J θ hNmark b = ggInducedAut θ (ggGamma J hNmark b) := by
      rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
      rfl
    rwa [hbeta] at hmem
  have hlt' : Nat.card B' < 3 ^ 3 := hlt B' hBI hBe
  have hltA : Nat.card A < 3 ^ 3 := by rwa [hBcard] at hlt'
  have hpg : IsPGroup 3 A := TableB.isPGroup_of_isElemAbelian hAe
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hpg
  have hm2 : m ≤ 2 := by
    rw [hm] at hltA
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hltA
    omega
  have hfin : Nat.card A ≤ 9 := by
    calc Nat.card A = 3 ^ m := hm
      _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 9 := by norm_num
  simpa [A, ← hgamma, hN0] using hfin

theorem GGInnerDiagOnLabel.eq_one_of_mem_center_of_smallLabel {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G}
    (hM : GGInnerDiagOnLabel (fun _ lab => ggResLineJSmallLabel lab) 3 Bs J) {z : ↥J}
    (hz : z ∈ Subgroup.center ↥J) (hz3 : z ^ 3 = 1) : z = 1 := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hM
  obtain ⟨R, _, I, F, ⟨⟨_, _, θ, hS, hNmark, hind⟩, hmarkedR⟩⟩ :=
    largeEvenRawDatum_exists
      (largeEvenRawDatum_markedModel hΛ (fun _ _ _ _ hq => hq.2.1) hraw)
  have hmarked : MarkedModel lab (J ⧸ Subgroup.center J) :=
    MarkedModel.of_mulEquiv θ.symm hmarkedR
  obtain ⟨-, hT⟩ :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hmarked
  have hle := center_torsion_le_native hperfJ (MulEquiv.refl (J ⧸ Subgroup.center J))
    hmarked hT Nat.prime_three
  have hbound : Nat.card {z : Subgroup.center ↥J // z ^ 3 = 1} ≤ 1 :=
    hle.trans (le_of_eq (torsBound_three_of_smallLabel hS))
  have := Finite.card_le_one_iff_subsingleton.1 hbound
  have h1 : (⟨⟨z, hz⟩, Subtype.ext hz3⟩ : {z : Subgroup.center ↥J // z ^ 3 = 1}) =
      ⟨1, one_pow 3⟩ := Subsingleton.elim _ _
  exact congrArg (fun w : {z : Subgroup.center ↥J // z ^ 3 = 1} => (w.1 : ↥J)) h1

theorem GGResHyp.inf_centralizer_J_eq_bot_of_smallLabel {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun _ lab => ggResLineJSmallLabel lab) 3 Bs J) :
    Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  have hz : (⟨g, hg.1.2⟩ : ↥J) ∈ Subgroup.center ↥J :=
    Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_centralizer_iff.1 hg.2 h h.2)
  exact congrArg Subtype.val (hM.eq_one_of_mem_center_of_smallLabel hz
    (Subtype.ext (hH.1.2.1.2.1.2 g hg.1.1)))
theorem ggResLineJCell_A2_smallLabel : GGResLineJCell .A2 fun lab => ggResLineJSmallLabel lab :=
  fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
    (false_of_lineJDatum_A2_of_card_gamma_le_nine hH.1.2.1 (GGResHyp.Bs_le_normalizer_J hH)
      hH.2.2.2.1 hD (GGResHyp.card_gamma_J_le_nine_of_smallLabel hH hM)
      (GGResHyp.inf_centralizer_J_eq_bot_of_smallLabel hH hM)).elim

theorem ggResLineJCell_B2_smallLabel : GGResLineJCell .B2 fun lab => ggResLineJSmallLabel lab := by
  intro G _ _ B Bs x L D J y K hH _ hD hM
  exfalso
  have hZ3 : ∀ z ∈ Subgroup.center ↥J, z ^ 3 = 1 → z = 1 := fun _ hz hz3 =>
    hM.eq_one_of_mem_center_of_smallLabel hz hz3
  obtain ⟨hE9, hAut⟩ := card_inf_eq_nine_and_centralizes_of_lineJDatum_B2 hH.1.2.1
    (GGResHyp.Bs_le_normalizer_J hH) hD (GGResHyp.card_gamma_J_le_nine_of_smallLabel hH hM)
    (GGResHyp.inf_centralizer_J_eq_bot_of_smallLabel hH hM)
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hM
  have hS : ggResLineJSmallLabel lab := by
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    exact hP.1
  have hhas : GGHasLabel lab (J ⧸ Subgroup.center J) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have : Group.IsPerfect J := Group.isPerfect_def.2 hperfJ
  have hEab : IsElemAbelian 3 ((Bs ⊓ J).subgroupOf J) :=
    (hH.1.2.1.2.1.mono inf_le_left).subgroupOf J
  refine not_hasNoncommPair_three_of_elemAbelian_nine _
    (fun a ha b hb => congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hEab.2 hE9
    (fun A hAc hA3 => card_le_nine_of_elemAbelian_of_smallLabel hΛ hhas
      (by rcases hS with h | h | h | h | h <;> simp [h]) hZ3
      ⟨⟨⟨fun a b => Subtype.ext (hAc _ a.2 _ b.2)⟩⟩, hA3⟩) hAut
    (hasNoncommPair_three_of_quotient_center hZ3
      (hasNoncommPair_three_of_smallLabel hΛ hhas hS))

theorem ggResLineJCell_A2_of_open (h : GGResLineJCell .A2 ggResLineJOpenA2) :
    GGResLineJCell .A2 fun _ => True := by
  have cAm : GGResLineJCell .A2 fun lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      ResJCubicBlock.GGResHyp.exists_lineJLabel_A2_of_compatible_splitLinear_marking hH hD hM
  have cUp : GGResLineJCell .A2 fun lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      GGResHyp.exists_A2_label_of_compatible_unitary_marking hH hD hM
  have cAp : GGResLineJCell .A2 fun lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (ResJPairedBlock.ActualA.actual_J_not_opposite_linear_for_A2 hH hD hM).elim
  have cUm : GGResLineJCell .A2 fun lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_opposite_unitary_for_A2 hH hD hM).elim
  have cBC : GGResLineJCell .A2 fun lab => lab.tag = .B ∨ lab.tag = .C :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_B_or_C_for_A2 hH hD hM).elim
  have cDm : GGResLineJCell .A2 fun lab => 3 ∣ 2 ^ lab.n - 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .twD ∧ GGResLineJType.A2.highDTwDRank ≤ lab.rank)) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_D_high_or_twD_split_of_line hH hD hM).elim
  have cDp : GGResLineJCell .A2 fun lab => 3 ∣ 2 ^ lab.n + 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .twD ∧ GGResLineJType.A2.highDTwDRank ≤ lab.rank)) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_D_high_or_twD_nonsplit_of_line hH hD hM).elim
  have cE6m : GGResLineJCell .A2 fun lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E6_split_of_line hH hD (Or.inl rfl) hM).elim
  have cE6 : GGResLineJCell .A2 fun lab =>
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E6_qplus_or_twE6_split_for_all_lines hH hD hM).elim
  have cE78 : GGResLineJCell .A2 fun lab => lab.tag = .E7 ∨ lab.tag = .E8 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E7_or_E8_of_line hH hD (Or.inl rfl) hM).elim
  have cF4 : GGResLineJCell .A2 fun lab => lab.tag = .F4 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_F4_for_all_lines hH hD hM).elim
  have cD3m : GGResLineJCell .A2 fun lab => lab.tag = .D ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    GGResLineJCell.of_D3 (s := fun n => 3 ∣ 2 ^ n - 1) (cAm.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cD3p : GGResLineJCell .A2 fun lab => lab.tag = .D ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    GGResLineJCell.of_D3 (s := fun n => 3 ∣ 2 ^ n + 1) (cAp.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cTD3m : GGResLineJCell .A2 fun lab => lab.tag = .twD ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    GGResLineJCell.of_twD3 (s := fun n => 3 ∣ 2 ^ n - 1) (cUm.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cTD3p : GGResLineJCell .A2 fun lab => lab.tag = .twD ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    GGResLineJCell.of_twD3 (s := fun n => 3 ∣ 2 ^ n + 1)
      (cUp.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cTD2 : GGResLineJCell .A2 fun lab => lab.tag = .twD ∧ lab.rank = 2 ∧ True :=
    GGResLineJCell.of_twD2 (s := fun _ => True) (cAm.mono fun _ _ hl => ⟨hl.1, by
      obtain ⟨m, hm, -⟩ := hl.2.2
      rw [hm]
      exact three_dvd_two_pow_two_mul_sub_one m⟩)
  refine GGResLineJCell.of_forall_eq fun lab0 hΛ _ => ?_
  obtain ⟨t, r, n⟩ := lab0
  have hΛt := hΛ.2
  cases t
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cAm.at ⟨rfl, hm⟩
    · exact cAp.at ⟨rfl, hp⟩
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cUm.at ⟨rfl, hm⟩
    · exact cUp.at ⟨rfl, hp⟩
  · exact cBC.at (Or.inl rfl)
  · exact cBC.at (Or.inr rfl)
  ·
    have h3 : 3 ≤ r := hΛt
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · by_cases hr3 : r = 3
      · subst hr3
        exact cD3m.at ⟨rfl, rfl, hm⟩
      · exact cDm.at ⟨hm, Or.inl ⟨rfl, show 4 ≤ r by omega⟩⟩
    · by_cases hr3 : r = 3
      · subst hr3
        exact cD3p.at ⟨rfl, rfl, hp⟩
      · exact cDp.at ⟨hp, Or.inl ⟨rfl, show 4 ≤ r by omega⟩⟩
  ·
    have h2 : 2 ≤ r := hΛt
    by_cases hr2 : r = 2
    · subst hr2
      exact cTD2.at ⟨rfl, rfl, trivial⟩
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · by_cases hr3 : r = 3
      · subst hr3
        exact cTD3m.at ⟨rfl, rfl, hm⟩
      · exact cDm.at ⟨hm, Or.inr ⟨rfl, show 4 ≤ r by omega⟩⟩
    · by_cases hr3 : r = 3
      · subst hr3
        exact cTD3p.at ⟨rfl, rfl, hp⟩
      · exact cDp.at ⟨hp, Or.inr ⟨rfl, show 4 ≤ r by omega⟩⟩
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cE6m.at ⟨rfl, hm⟩
    · exact cE6.at (Or.inl ⟨rfl, hp⟩)
  · exact cE78.at (Or.inl rfl)
  · exact cE78.at (Or.inr rfl)
  · exact cF4.at rfl
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cE6.at (Or.inr ⟨rfl, hm⟩)
    · exact h.at (by simp [ggResLineJOpenA2, hp])
  · exact ggResLineJCell_A2_smallLabel.at (Or.inr (Or.inl rfl))
  · exact ggResLineJCell_A2_smallLabel.at (Or.inl rfl)
  · exact (ggResLineJCell_twB2 _).at rfl
  · exact ggResLineJCell_A2_smallLabel.at (Or.inr (Or.inr (Or.inl rfl)))
  · exact ggResLineJCell_A2_B2der.at rfl
  · exact ggResLineJCell_A2_smallLabel.at (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact ggResLineJCell_A2_smallLabel.at (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem ggResLineJCell_B2 : GGResLineJCell .B2 fun _ => True := by
  have cUp : GGResLineJCell .B2 fun lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_matched_unitary_for_B2 hH hD hM).elim
  have cE6p : GGResLineJCell .B2 fun lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_twE6_qplus_for_B2 hH hD hM).elim
  have cAm : GGResLineJCell .B2 fun lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (ResJCubicBlock.GGResHyp.actual_J_not_splitLinear_for_B2 hH hD hM).elim
  have cUm : GGResLineJCell .B2 fun lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      GGResHyp.exists_lineJLabel_of_opposite_unitary_B2 hH hD hM
  have cSmall := ggResLineJCell_B2_smallLabel
  have cAp : GGResLineJCell .B2 fun lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      GGResHyp.exists_lineJLabel_of_B2_oppositeLinear hH hD hM
  have cBC : GGResLineJCell .B2 fun lab => lab.tag = .B ∨ lab.tag = .C :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM => GGResHyp.exists_lineJLabel_of_B2 hH hD hM
  have cLab := ggResLineJCell_of_label .B2
  have cDm : GGResLineJCell .B2 fun lab => 3 ∣ 2 ^ lab.n - 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .twD ∧ GGResLineJType.B2.highDTwDRank ≤ lab.rank)) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_D_high_or_twD_split_of_line hH hD hM).elim
  have cDp : GGResLineJCell .B2 fun lab => 3 ∣ 2 ^ lab.n + 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .twD ∧ GGResLineJType.B2.highDTwDRank ≤ lab.rank)) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_D_high_or_twD_nonsplit_of_line hH hD hM).elim
  have cE6m : GGResLineJCell .B2 fun lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E6_split_of_line hH hD (Or.inr (Or.inl rfl)) hM).elim
  have cE6 : GGResLineJCell .B2 fun lab =>
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E6_qplus_or_twE6_split_for_all_lines hH hD hM).elim
  have cE78 : GGResLineJCell .B2 fun lab => lab.tag = .E7 ∨ lab.tag = .E8 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E7_or_E8_of_line hH hD (Or.inr (Or.inl rfl)) hM).elim
  have cF4 : GGResLineJCell .B2 fun lab => lab.tag = .F4 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_F4_for_all_lines hH hD hM).elim
  have cD3m : GGResLineJCell .B2 fun lab => lab.tag = .D ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    GGResLineJCell.of_D3 (s := fun n => 3 ∣ 2 ^ n - 1) (cAm.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cTD3p : GGResLineJCell .B2 fun lab => lab.tag = .twD ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    GGResLineJCell.of_twD3 (s := fun n => 3 ∣ 2 ^ n + 1)
      (cUp.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cTD2 : GGResLineJCell .B2 fun lab => lab.tag = .twD ∧ lab.rank = 2 ∧ True :=
    GGResLineJCell.of_twD2 (s := fun _ => True) (cAm.mono fun _ _ hl => ⟨hl.1, by
      obtain ⟨m, hm, -⟩ := hl.2.2
      rw [hm]
      exact three_dvd_two_pow_two_mul_sub_one m⟩)
  refine GGResLineJCell.of_forall_eq fun lab0 hΛ _ => ?_
  obtain ⟨t, r, n⟩ := lab0
  have hΛt := hΛ.2
  cases t
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cAm.at ⟨rfl, hm⟩
    · exact cAp.at ⟨rfl, hp⟩
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cUm.at ⟨rfl, hm⟩
    · exact cUp.at ⟨rfl, hp⟩
  · exact cBC.at (Or.inl rfl)
  · exact cBC.at (Or.inr rfl)
  ·
    have h3 : 3 ≤ r := hΛt
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · by_cases hr3 : r = 3
      · subst hr3
        exact cD3m.at ⟨rfl, rfl, hm⟩
      · exact cDm.at ⟨hm, Or.inl ⟨rfl, show 4 ≤ r by omega⟩⟩
    · by_cases hr3 : r = 3
      · subst hr3
        exact cLab.at (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, hp⟩)))
      · exact cDp.at ⟨hp, Or.inl ⟨rfl, show 4 ≤ r by omega⟩⟩
  ·
    have h2 : 2 ≤ r := hΛt
    by_cases hr2 : r = 2
    · subst hr2
      exact cTD2.at ⟨rfl, rfl, trivial⟩
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · by_cases hr3 : r = 3
      · subst hr3
        exact cLab.at (Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hm⟩)))
      · exact cDm.at ⟨hm, Or.inr ⟨rfl, show 4 ≤ r by omega⟩⟩
    · by_cases hr3 : r = 3
      · subst hr3
        exact cTD3p.at ⟨rfl, rfl, hp⟩
      · exact cDp.at ⟨hp, Or.inr ⟨rfl, show 4 ≤ r by omega⟩⟩
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cE6m.at ⟨rfl, hm⟩
    · exact cE6.at (Or.inl ⟨rfl, hp⟩)
  · exact cE78.at (Or.inl rfl)
  · exact cE78.at (Or.inr rfl)
  · exact cF4.at rfl
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cE6.at (Or.inr ⟨rfl, hm⟩)
    · exact cE6p.at ⟨rfl, hp⟩
  ·
    exact cSmall.at (Or.inr (Or.inl rfl))
  ·
    exact cSmall.at (Or.inl rfl)
  ·
    exact (ggResLineJCell_twB2 _).at rfl
  ·
    exact cSmall.at (Or.inr (Or.inr (Or.inl rfl)))
  ·
    have hl : r = 0 ∧ n = 1 := hΛt
    obtain ⟨rfl, rfl⟩ := hl
    exact cLab.at (Or.inr (Or.inl rfl))
  ·
    exact cSmall.at (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  ·
    exact cSmall.at (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem ggResLineJCell_BC {T : GGResLineJType} (hT : T = .B3 ∨ T = .C3) :
    GGResLineJCell T fun _ => True := by
  have hT' : T = .A2 ∨ T = .B2 ∨ T = .B3 ∨ T = .C3 :=
    hT.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr h)))
  have hlab : ∀ lab : LargeEvenLabel, (((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3) ∨
      (lab.tag = .A ∧ (lab.rank = 5 ∨ lab.rank = 6) ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twA ∧ (lab.rank = 5 ∨ lab.rank = 6) ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twD ∧ lab.rank = 4)) → ggResLineJLabel T lab := by
    rcases hT with rfl | rfl <;> exact fun _ hl => hl
  have hhigh : T.highDTwDRank = 5 := by rcases hT with rfl | rfl <;> rfl
  have cBC : GGResLineJCell T fun lab => lab.tag = .B ∨ lab.tag = .C :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM => GGResHyp.exists_lineJLabel_of_B3C3 hH hD hT hM
  have cAm : GGResLineJCell T fun lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (ResJCubicBlock.GGResHyp.not_exists_matched_splitLinear_marking_B3C3 hH hD hT hM).elim
  have cAp : GGResLineJCell T fun lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      GGResHyp.exists_lineJLabel_of_B3C3_oppositeLinear hH hD hT hM
  have cUm : GGResLineJCell T fun lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      GGResHyp.exists_lineJLabel_of_opposite_unitary_B3C3 hH hD hT hM
  have cU6 : GGResLineJCell T fun lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_unitary_six_for_B3C3_qplus hH hD hT hM).elim
  have cUp : GGResLineJCell T fun lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≠ 5 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_matched_unitary_for_B3C3 hH hD hT hM).elim
  have cLab := ggResLineJCell_of_label T
  have cDm : GGResLineJCell T fun lab => 3 ∣ 2 ^ lab.n - 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ T.highDTwDRank ≤ lab.rank)) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_D_high_or_twD_split_of_line hH hD hM).elim
  have cDp : GGResLineJCell T fun lab => 3 ∣ 2 ^ lab.n + 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ T.highDTwDRank ≤ lab.rank)) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_D_high_or_twD_nonsplit_of_line hH hD hM).elim
  have cE6m : GGResLineJCell T fun lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E6_split_of_line hH hD hT' hM).elim
  have cE6 : GGResLineJCell T fun lab =>
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E6_qplus_or_twE6_split_for_all_lines hH hD hM).elim
  have cE78 : GGResLineJCell T fun lab => lab.tag = .E7 ∨ lab.tag = .E8 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_E7_or_E8_of_line hH hD hT' hM).elim
  have cF4 : GGResLineJCell T fun lab => lab.tag = .F4 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_F4_for_all_lines hH hD hM).elim
  have cSmall : GGResLineJCell T fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨
      lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨
      lab.tag = .twF4der :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_small_of_B3C3 hH hD hT hM).elim
  have cTwE6p : GGResLineJCell T fun lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
      (GGResHyp.actual_J_not_twE6_qplus_for_B3C3 hH hD hT hM).elim
  have cD3m : GGResLineJCell T fun lab => lab.tag = .D ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    GGResLineJCell.of_D3 (s := fun n => 3 ∣ 2 ^ n - 1) (cAm.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cD3p : GGResLineJCell T fun lab => lab.tag = .D ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    GGResLineJCell.of_D3 (s := fun n => 3 ∣ 2 ^ n + 1) (cAp.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cTD3m : GGResLineJCell T fun lab => lab.tag = .twD ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1 :=
    GGResLineJCell.of_twD3 (s := fun n => 3 ∣ 2 ^ n - 1) (cUm.mono fun _ _ hl => ⟨hl.1, hl.2.2⟩)
  have cTD3p : GGResLineJCell T fun lab => lab.tag = .twD ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    GGResLineJCell.of_twD3 (s := fun n => 3 ∣ 2 ^ n + 1)
      (cUp.mono fun _ _ hl => ⟨hl.1, hl.2.2, by rw [hl.2.1]; decide⟩)
  have cTD2 : GGResLineJCell T fun lab => lab.tag = .twD ∧ lab.rank = 2 ∧ True :=
    GGResLineJCell.of_twD2 (s := fun _ => True) (cAm.mono fun _ _ hl => ⟨hl.1, by
      obtain ⟨m, hm, -⟩ := hl.2.2
      rw [hm]
      exact three_dvd_two_pow_two_mul_sub_one m⟩)
  refine GGResLineJCell.of_forall_eq fun lab0 hΛ _ => ?_
  obtain ⟨t, r, n⟩ := lab0
  have hΛt := hΛ.2
  cases t
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cAm.at ⟨rfl, hm⟩
    · exact cAp.at ⟨rfl, hp⟩
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cUm.at ⟨rfl, hm⟩
    · by_cases hr5 : r = 5
      · subst hr5
        exact cU6.at ⟨rfl, rfl, hp⟩
      · exact cUp.at ⟨rfl, hp, hr5⟩
  · exact cBC.at (Or.inl rfl)
  · exact cBC.at (Or.inr rfl)
  ·
    have h3 : 3 ≤ r := hΛt
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · by_cases hr3 : r = 3
      · subst hr3
        exact cD3m.at ⟨rfl, rfl, hm⟩
      · exact cDm.at ⟨hm, Or.inl ⟨rfl, show 4 ≤ r by omega⟩⟩
    · by_cases hr3 : r = 3
      · subst hr3
        exact cD3p.at ⟨rfl, rfl, hp⟩
      · exact cDp.at ⟨hp, Or.inl ⟨rfl, show 4 ≤ r by omega⟩⟩
  ·
    have h2 : 2 ≤ r := hΛt
    by_cases hr2 : r = 2
    · subst hr2
      exact cTD2.at ⟨rfl, rfl, trivial⟩
    by_cases hr4 : r = 4
    · subst hr4
      exact cLab.at (hlab _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · by_cases hr3 : r = 3
      · subst hr3
        exact cTD3m.at ⟨rfl, rfl, hm⟩
      · exact cDm.at ⟨hm, Or.inr ⟨rfl, by rw [hhigh]; show 5 ≤ r; omega⟩⟩
    · by_cases hr3 : r = 3
      · subst hr3
        exact cTD3p.at ⟨rfl, rfl, hp⟩
      · exact cDp.at ⟨hp, Or.inr ⟨rfl, by rw [hhigh]; show 5 ≤ r; omega⟩⟩
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cE6m.at ⟨rfl, hm⟩
    · exact cE6.at (Or.inl ⟨rfl, hp⟩)
  · exact cE78.at (Or.inl rfl)
  · exact cE78.at (Or.inr rfl)
  · exact cF4.at rfl
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hm | hp
    · exact cE6.at (Or.inr ⟨rfl, hm⟩)
    · exact cTwE6p.at ⟨rfl, hp⟩
  all_goals exact cSmall.at (by simp)

theorem ggResLineJLabelInput_of_cells (hA2 : GGResLineJCell .A2 fun _ => True)
    (hB2 : GGResLineJCell .B2 fun _ => True) (hB3 : GGResLineJCell .B3 fun _ => True)
    (hC3 : GGResLineJCell .C3 fun _ => True) : GGResLineJLabelInput := by
  intro G _ _ p B Bs x L D J y K hH _ hp T hD
  subst hp
  obtain ⟨lab0, -, -, hM⟩ := GGResHyp.exists_J_compatible_marking hH
  have hM' : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs J :=
    GGInnerDiagOnLabel.mono_label (fun _ _ => trivial) hM
  cases T
  · exact hA2 G B Bs x L D J y K hH hD hM'
  · exact hB2 G B Bs x L D J y K hH hD hM'
  · exact ggResLineJLabelInput_A3 G 3 B Bs x L D J y K hH rfl hD
  · exact hB3 G B Bs x L D J y K hH hD hM'
  · exact hC3 G B Bs x L D J y K hH hD hM'

theorem ggResLineJCell_A2 : GGResLineJCell .A2 fun _ => True :=
  ggResLineJCell_A2_of_open fun _ _ _ _ _ _ _ _ _ _ _ hH _ hD hM =>
    (GGResHyp.actual_J_not_twE6_qplus_for_A2 hH hD hM).elim

theorem ggResLineJLabelInput_holds : GGResLineJLabelInput :=
  ggResLineJLabelInput_of_cells ggResLineJCell_A2 ggResLineJCell_B2
    (ggResLineJCell_BC (Or.inl rfl)) (ggResLineJCell_BC (Or.inr rfl))

end Certificates

end CFSG.StandardType

end
