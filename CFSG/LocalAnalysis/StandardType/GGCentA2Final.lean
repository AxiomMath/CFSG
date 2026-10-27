module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneDiag
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneA2Split
public import CFSG.LocalAnalysis.StandardType.GGCentStructProof
public import CFSG.LocalAnalysis.StandardType.GGCentA2Diag
public import CFSG.LocalAnalysis.StandardType.GGCentA2Shape
public import CFSG.LocalAnalysis.StandardType.GGCentA2Lang
public import CFSG.LocalAnalysis.StandardType.GGCentA2Std
public import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open scoped MatrixGroups
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

private theorem a2f_normal_eq_top_or_le_center {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {N : Subgroup Q} (hN : N.Normal) :
    N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

private theorem a2f_frame_ker_le_center
    {L : Type} [Field L] {φ : SL(3, L) →* ModGL .E6 L}
    {σφ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hφ : IsSLFrame φ σφ) :
    φ.ker ≤ Subgroup.center SL(3, L) := by
  have hq : CFSG.Open.IsQuasisimple SL(3, L) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple (m := 2) (F := L) le_rfl)
  rcases a2f_normal_eq_top_or_le_center hq φ.normal_ker with h | h
  · exfalso
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    obtain ⟨ε, hε⟩ := hφ.transv 0 1 h01
    have h1 : φ (Matrix.SpecialLinearGroup.transvection h01 (1 : L)) = 1 :=
      MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
    have h2 : pinnedX Tag.E6 L (σφ 0 1) ((ε : L) * 1) = pinnedX Tag.E6 L (σφ 0 1) 0 :=
      ((hε 1).symm.trans h1).trans (pinnedX_zero (τ := Tag.E6) (R := L) (σφ 0 1)).symm
    have h3 := pinnedX_injective (τ := Tag.E6) (R := L) (σφ 0 1) h2
    exact ε.ne_zero (by simpa using h3)
  · exact h

private theorem a2f_step_diag {G : Type*} [Group G] (stp : G →* G) (n : G) (hn : stp n = n)
    (u : G) : stp (cycConjDiag n u) = cycConjDiag n (stp u) := by
  unfold cycConjDiag
  simp only [map_mul, map_inv, map_pow, hn]

private theorem a2f_diag_shift {G : Type*} [Group G] (n : G) (hn3 : n ^ 3 = 1) (R : Subgroup G)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, Commute r (n * s * n⁻¹)) {w : G} (hw : w ∈ R) (j : ℕ) :
    cycConjDiag n (n ^ j * w * (n ^ j)⁻¹) = cycConjDiag n w := by
  have hfix : n * cycConjDiag n w * n⁻¹ = cycConjDiag n w := cycConjDiag_conj n R hn3 hcomm hw
  have hc : Commute n (cycConjDiag n w) := mul_inv_eq_iff_eq_mul.1 hfix
  have hcn : n * n ^ j = n ^ j * n := (Commute.refl n).pow_right j |>.eq
  have key : ∀ x : G, n * (n ^ j * x * (n ^ j)⁻¹) * n⁻¹ = n ^ j * (n * x * n⁻¹) * (n ^ j)⁻¹ := by
    intro x
    calc n * (n ^ j * x * (n ^ j)⁻¹) * n⁻¹ = (n * n ^ j) * x * (n * n ^ j)⁻¹ := by group
      _ = (n ^ j * n) * x * (n ^ j * n)⁻¹ := by rw [hcn]
      _ = n ^ j * (n * x * n⁻¹) * (n ^ j)⁻¹ := by group
  have e2 : n ^ 2 * (n ^ j * w * (n ^ j)⁻¹) * (n ^ 2)⁻¹ =
      n ^ j * (n ^ 2 * w * (n ^ 2)⁻¹) * (n ^ j)⁻¹ := by
    calc n ^ 2 * (n ^ j * w * (n ^ j)⁻¹) * (n ^ 2)⁻¹
        = n * (n * (n ^ j * w * (n ^ j)⁻¹) * n⁻¹) * n⁻¹ := by group
      _ = n * (n ^ j * (n * w * n⁻¹) * (n ^ j)⁻¹) * n⁻¹ := by rw [key w]
      _ = n ^ j * (n * (n * w * n⁻¹) * n⁻¹) * (n ^ j)⁻¹ := by rw [key (n * w * n⁻¹)]
      _ = n ^ j * (n ^ 2 * w * (n ^ 2)⁻¹) * (n ^ j)⁻¹ := by group
  have h1 : cycConjDiag n (n ^ j * w * (n ^ j)⁻¹) = n ^ j * cycConjDiag n w * (n ^ j)⁻¹ := by
    unfold cycConjDiag
    rw [key w, e2]
    group
  rw [h1]
  exact mul_inv_eq_iff_eq_mul.2 ((hc.pow_left j).eq)

private lemma a2f_eq_of_isComponentOf_le_of_quasisimple {G : Type*} [Group G]
    {K Δ C : Subgroup G} (hKC : CFSG.Assembly.IsComponentOf K C)
    (hKΔ : K ≤ Δ) (hΔC : Δ ≤ C) (hΔq : CFSG.Open.IsQuasisimple ↥Δ)
    (hKq : CFSG.IsQuasisimple ↥K) :
    K = Δ := by
  have hKsub : CFSG.Assembly.IsSubnormal K Δ := by
    have h := hKC.2.1.inf_of_le hΔC
    rwa [inf_eq_left.mpr hKΔ] at h
  have hsubM : (K.subgroupOf Δ).IsSubnormal :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hKΔ).mp hKsub
  have hsub : CFSG.Open.IsSubnormal (K.subgroupOf Δ) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib
        (K.subgroupOf Δ)).mpr hsubM)
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hΔq
    (K.subgroupOf Δ) hsub with hc | htop
  · exfalso
    have hab2 : ∀ a b : ↥K, a * b = b * a := by
      intro a b
      let aΔ : ↥Δ := ⟨(a : G), hKΔ a.2⟩
      let bΔ : ↥Δ := ⟨(b : G), hKΔ b.2⟩
      have haΔ : aΔ ∈ K.subgroupOf Δ := by rw [Subgroup.mem_subgroupOf]; exact a.2
      have ha : aΔ ∈ Subgroup.center ↥Δ := hc haΔ
      have h := Subgroup.mem_center_iff.mp ha bΔ
      exact Subtype.ext (Subtype.ext_iff.mp h).symm
    obtain ⟨x, y, hxy⟩ := hKq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) y
    refine hxy ?_
    simp only [← map_mul, hab2 a b]
  · exact le_antisymm hKΔ (Subgroup.subgroupOf_eq_top.mp htop)


theorem langNontoralA2Descent_holds
    
    : LangNontoralA2Descent := by
  classical
  unfold LangNontoralA2Descent
  intro L hL hAlg hChar p₀ S a n hpair hker horb K hK
  have hpair' := hpair
  obtain ⟨hap, hT, h1, hnM, hn3, hcommd, -⟩ := hpair'
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  have h18 : (kernelRoots (rootCharHom a)).ncard = 18 := by
    rw [kernelRoots_rootCharHom]
    exact hker
  obtain ⟨f, hf, hqf⟩ : ∃ f : ℕ, 1 ≤ f ∧ S.D.q = 2 ^ f := by
    obtain ⟨hqpp, hq0⟩ := S.hqpow
    obtain ⟨p, k, hp, hk0, hpk⟩ := hqpp
    have hpN : p.Prime := Nat.prime_iff.mpr hp
    have h2dvd : 2 ∣ p ^ k := by
      rw [hpk]
      exact (CharP.cast_eq_zero_iff L 2 S.D.q).1 hq0
    have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2dvd
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpN).1 h2p).symm
    exact ⟨k, hk0, by rw [← hpk, hp2]⟩
  obtain ⟨Fr, hFrq, -⟩ := S.D.steinberg
  have hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f) := fun c => by rw [hFrq c, hqf]
  obtain ⟨hcard3, σ, hσ1, hσ3, hσ, -, hlayer⟩ := langNontoralStructure_holds L p₀ S a n hpair hker
  obtain ⟨c, hc, h6⟩ :=
    KSNotAll24.kernel_classes_of_ncard_eighteen h3L hap h18
  obtain ⟨φ, σφ, hφ, -, hΨ⟩ :=
    (TwE6UniqAbs.kac_facts h3L hap).frame (c 0) (h6 0)
  have hφker := a2f_frame_ker_le_center hφ
  obtain ⟨Δ, hΔ, hΔker, hΔcomm, hΔrange, hΔK, k, hk⟩ :=
    ntpA2_diag S a n hpair hker horb σ hσ1 hσ3 hσ hlayer (c 0) φ σφ hφ hΨ hφker
  obtain ⟨B, e, hBe⟩ := ntpA2_shape S a n hpair hker (c 0) φ σφ hφ hΨ Fr hFrq k hk
  have hstepn : S.D.step n = n := (S.D.mem_model.1 hnM).2
  have hstpΔ : ∀ X : SL(3, L), S.D.step (Δ X) =
      Δ (slConjugation 3 L B (if e then slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X)
        else Matrix.SpecialLinearGroup.map Fr X)) := by
    intro X
    rw [hΔ X, hΔ, a2f_step_diag S.D.step n hstepn (φ X), ← hBe X]
    have hw : n ^ k * S.D.step (φ X) * (n ^ k)⁻¹ ∈ φ.range := hk _ ⟨X, rfl⟩
    have hn3k : n ^ (2 * k) * n ^ k = 1 := by
      rw [← pow_add, show 2 * k + k = 3 * k by ring, pow_mul, hn3, one_pow]
    have hback : S.D.step (φ X) =
        n ^ (2 * k) * (n ^ k * S.D.step (φ X) * (n ^ k)⁻¹) * (n ^ (2 * k))⁻¹ := by
      calc S.D.step (φ X)
          = (n ^ (2 * k) * n ^ k) * S.D.step (φ X) * (n ^ (2 * k) * n ^ k)⁻¹ := by
            rw [hn3k]; group
        _ = n ^ (2 * k) * (n ^ k * S.D.step (φ X) * (n ^ k)⁻¹) * (n ^ (2 * k))⁻¹ := by group
    conv_lhs => rw [hback]
    exact a2f_diag_shift n hn3 φ.range hΔcomm hw (2 * k)
  obtain ⟨z, hz⟩ := ntpA2_lang hf Fr hFr B e
  have hzz : ∀ X : SL(3, L), slConjugation 3 L z (slConjugation 3 L z⁻¹ X) = X := fun X => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hzz' : ∀ X : SL(3, L), slConjugation 3 L z⁻¹ (slConjugation 3 L z X) = X := fun X => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  let ιz : SL(3, L) →* ModGL .E6 L := Δ.comp (slConjugation 3 L z⁻¹).toMonoidHom
  have hιz : ∀ X, ιz X = Δ (slConjugation 3 L z⁻¹ X) := fun X => rfl
  have hιzker : ιz.ker ≤ Subgroup.center SL(3, L) := by
    intro X hX
    have hX' : Δ (slConjugation 3 L z⁻¹ X) = 1 := MonoidHom.mem_ker.1 hX
    have hc' := hΔker (MonoidHom.mem_ker.2 hX')
    rw [Subgroup.mem_center_iff] at hc' ⊢
    intro W
    have h := congrArg (slConjugation 3 L z) (hc' (slConjugation 3 L z⁻¹ W))
    simpa only [map_mul, hzz] using h
  have hstpz : ∀ X : SL(3, L), S.D.step (ιz X) =
      ιz (if e then slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X)
        else Matrix.SpecialLinearGroup.map Fr X) := by
    intro X
    rw [hιz X, hstpΔ, hz (slConjugation 3 L z⁻¹ X), hzz X, hιz]
  have hKnat : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hK.2.2
  have hKleΔ : K ≤ Δ.range := hΔK K hK.1 hKnat
  have hKle : K ≤ ιz.range := by
    intro x hx
    obtain ⟨X, rfl⟩ := hKleΔ hx
    exact ⟨slConjugation 3 L z X, by rw [hιz, hzz']⟩
  have hKfix : ∀ k ∈ K, S.D.step k = k := by
    intro x hx
    have hxG : x ∈ S.Γ := (Subgroup.mem_inf.1 (hK.1 hx)).1
    exact (S.D.mem_model.1 (S.Γ_le_model hxG)).2
  obtain ⟨Q, hKQ, hQle, hQfix, hQq, hQlie⟩ :=
    ntpA2_std hf Fr hFr e ιz hιzker S.D.step hstpz K hK.2.2 hKle hKfix
  have hQΔ : Q ≤ Δ.range := by
    intro x hx
    obtain ⟨X, hX⟩ := hQle hx
    exact ⟨slConjugation 3 L z⁻¹ X, hX⟩
  have hQadj := hQΔ.trans hΔrange
  have hQM : Q ≤ S.D.model := fun x hx =>
    S.D.mem_model.2 ⟨(Subgroup.mem_inf.1 (hQadj hx)).1, hQfix x hx⟩
  have hQΓ : Q ≤ S.Γ := by
    have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.1 ⟨hQq.1⟩
    calc Q = ⁅Q, Q⁆ := hperf.symm
      _ ≤ ⁅S.D.model, S.D.model⁆ := Subgroup.commutator_mono hQM hQM
  have hQX : Q ≤ S.Γ ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)) :=
    fun x hx => Subgroup.mem_inf.2 ⟨hQΓ hx, (Subgroup.mem_inf.1 (hQadj hx)).2⟩
  have hKQeq : K = Q :=
    a2f_eq_of_isComponentOf_le_of_quasisimple (CFSG.Assembly.isComponentOf_iff_open.mpr hK) hKQ
      hQX hQq hKnat
  have hfield : GGCompFieldAt (2 ^ f) K := by
    rcases hQlie with ⟨-, hLie⟩ | ⟨-, hLie⟩
    · have hLie' : LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 3 2 f := by
        rw [hKQeq]
        exact hLie
      exact ggCompFieldAt_of_lieModel hK.2.2 hLie' (by decide)
    · have hLie' : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 3 2 f := by
        rw [hKQeq]
        exact hLie
      exact ggCompFieldAt_of_lieModel hK.2.2 hLie' (by decide)
  rw [hqf]
  exact hfield

end CFSG.StandardType.NTPlane

end
