module

public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofDefs
import CFSG.RankThree.PartTwo.Sec14.Wales1418OffTools
import CFSG.RankThree.PartTwo.Sec6.Wales65B
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKField
import CFSG.RankThree.PartTwo.Sec10.Item1012Res2ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofQN
import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotCentralizer)
open Proof1418Res3 (ActsTrivOnLayer3)

structure Off1418 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L S B : Subgroup G)
    (b : G) (E R : Subgroup G) : Prop where
  sec15R : Sec15R G A c L
  fail : Fail1411 A (lB A)
  S_mem : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)
  hyperplane_B : IsHyperplane A B
  S_inf : S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥
  b_mem : b ∈ B
  b_gamma : Subgroup.zpowers b ∈ gammaA A (lB A)
  gamma_uniq : ∀ F ∈ gammaA A (lB A), F ≤ B → F = Subgroup.zpowers b
  b_cent : ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), T ≤ Subgroup.centralizer ({b} : Set G)
  normalizer_b :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G)
  normalizer_inf : ∀ Lb ∈ lA A b, 3 ∣ Nat.card Lb → Subgroup.normalizer (A : Set G) ≤
    Subgroup.normalizer ((A ⊓ Lb : Subgroup G) : Set G)
  hyperplane_E : IsHyperplane A E
  off : ∀ F ∈ omegaA A, ¬ F ≤ E
  R_le : R ≤ Subgroup.centralizer (E : Set G)
  R_two : IsPGroup 2 R
  A_le_R : A ≤ Subgroup.normalizer (R : Set G)
  R_comm : ⁅R, Subgroup.zpowers b⁆ = R

@[expose] noncomputable def Step1418OffBridgeR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L S B : Subgroup G) (b : G)
    (E R : Subgroup G), Off1418 G A c L S B b E R →
      ¬ ActsTrivOnLayer3 (Subgroup.centralizer (E : Set G)) R →
        ∃ J ∈ thetaComponentsIn (Subgroup.centralizer (E : Set G)),
          A ≤ Subgroup.normalizer (J : Set G) ∧ R ≤ Subgroup.normalizer (J : Set G) ∧
            ¬ R ≤ thetaQuotCentralizer J

@[expose] noncomputable def Step1418OffPointR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L S B : Subgroup G) (b : G)
    (E R : Subgroup G), Off1418 G A c L S B b E R →
      ∀ e ∈ E, e ≠ 1 → ∀ K ∈ thetaComponentsAt 3 e,
        A ≤ Subgroup.normalizer (K : Set G) → R ≤ Subgroup.normalizer (K : Set G) →
        ¬ R ≤ thetaQuotCentralizer K →
        A ⊓ thetaQuotCentralizer K = Subgroup.zpowers e → False

section Off1418

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L S B : Subgroup G} {b : G}
  {E R : Subgroup G}

theorem Off1418.isE27 (h : Off1418 G A c L S B b E R) : IsE27 A :=
  h.sec15R.toSec14Std.isE27

theorem Off1418.b_mem_A (h : Off1418 G A c L S B b E R) : b ∈ A :=
  h.hyperplane_B.1 h.b_mem

theorem Off1418.b_omega (h : Off1418 G A c L S B b E R) : Subgroup.zpowers b ∈ omegaA A :=
  h.b_gamma.1

theorem Off1418.b_not_mem_E (h : Off1418 G A c L S B b E R) : b ∉ E := fun hbE =>
  h.off _ h.b_omega (Subgroup.zpowers_le.mpr hbE)

theorem Off1418.card_E (h : Off1418 G A c L S B b E R) : Nat.card E = 9 := by
  have h1 := h.hyperplane_E.2
  rw [h.isE27.2] at h1
  omega

theorem Off1418.elemE (h : Off1418 G A c L S B b E R) : CFSG.Assembly.IsElemAbelian 3 E :=
  ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
      (h.isE27.1.1.is_comm.comm ⟨x, h.hyperplane_E.1 x.2⟩ ⟨y, h.hyperplane_E.1 y.2⟩))⟩⟩,
    fun x hx => h.isE27.1.2 x (h.hyperplane_E.1 hx)⟩

theorem Off1418.le_centralizer_b (h : Off1418 G A c L S B b E R) {x : G} (hxA : x ∈ A)
    {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTθ : T ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G)))
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) : T ≤ Subgroup.centralizer ({b} : Set G) := by
  have hTO : T ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) :=
    hTθ.trans (Proof153Twin3.map_aschbacherSolvableCore_le_pPrimeCoreOf _)
  have hTQ := Proof15Res7.mem_scriptQ_of_le_pPrimeCoreOf h.sec15R.toSec14Std hxA hTO hAT
  have hpi : T ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hTQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hT2⟩
  obtain ⟨T', hTT', hT'⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hpi
  exact hTT'.trans (h.b_cent T' hT')

theorem Off1418.exists_mem_thetaComponentsAt (h : Off1418 G A c L S B b E R)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn (Subgroup.centralizer (E : Set G)))
    (hRJ : R ≤ Subgroup.normalizer (J : Set G)) (hRJθ : ¬ R ≤ thetaQuotCentralizer J)
    {e : G} (heE : e ∈ E) (he1 : e ≠ 1) :
    ∃ K ∈ thetaComponentsAt 3 e, J ≤ K ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
      R ≤ Subgroup.normalizer (K : Set G) ∧ ¬ R ≤ thetaQuotCentralizer K ∧
      ¬ J ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
  have hTF := h.sec15R.toPartTwoStanding.toTheoremFourHyp
  have hA := h.isE27
  have heA : e ∈ A := h.hyperplane_E.1 heE
  have hJp : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJE : J ≤ Subgroup.centralizer (E : Set G) := le_of_mem_thetaComponentsIn hJ
  have hEe : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heE)
  obtain ⟨x, hxE, hx1, -, hCeq⟩ := Sec6.exists_centralizer_eq_inf h.elemE h.card_E heE he1
  have hJ' : J ∈ thetaComponentsIn
      (Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) := hCeq ▸ hJ
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨y, hy⟩ ⟨e, heA⟩))
  have hS4 : SectionFourHyp (Subgroup.centralizer ({e} : Set G)) :=
    hTF.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hTF he1)
  obtain ⟨K, hK, hJK⟩ := Sec6.exists_le_mem_thetaComponentsIn h48 hS4 hAe hA.1
    ⟨3, le_rfl, by rw [hA.2]; norm_num⟩ (h.hyperplane_E.1 hxE) hx1 hJ'
  have hKe : K ∈ thetaComponentsAt 3 e := hK
  have hJθ : ¬ J ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
    intro hle
    have hJθJ : J ≤ inSubgroup (aschbacherSolvableCore 3) J :=
      (le_inf hle le_rfl).trans (Sec6.Res611Res7.theta_inf_le_theta (hJE.trans hEe))
    exact Sec15.Proof1423.not_le_thetaQuotCentralizer_self hJ
      (hJθJ.trans (Sec6.theta_le_thetaQuotCentralizer J))
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hTF hA.1 heA he1 K hKe
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := by
    intro r hr
    have hrC : r ∈ Subgroup.centralizer ({e} : Set G) := hEe (h.R_le hr)
    have hKr := Sec10.Item1012Res2Proof.conj_mem_thetaComponentsIn hK hrC
    have hJr : J ≤ K.map (MulAut.conj r).toMonoidHom := by
      intro j hj
      refine ⟨r⁻¹ * j * r, hJK ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hRJ hr)) j).mp hj
      simpa [mul_assoc] using this
    have heq := Wales1418Off.eq_of_le_inf hK hKr hJp (le_inf hJK hJr) hJθ
    refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [heq]
      exact ⟨k, hk, rfl⟩
    · have hk' : r * k * r⁻¹ ∈ K.map (MulAut.conj r).toMonoidHom := by rw [← heq]; exact hk
      obtain ⟨k', hk'K, hk'eq⟩ := hk'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hk'eq
      have : k' = k := mul_left_cancel (mul_right_cancel hk'eq)
      rwa [← this]
  have hRKθ : ¬ R ≤ thetaQuotCentralizer K := by
    intro hRC
    apply hRJθ
    have h1 : ⁅K, R⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K :=
      (Sec6.commutator_le_theta_iff hRK).mpr hRC
    have h2 : ⁅J, R⁆ ≤ inSubgroup (aschbacherSolvableCore 3) J := by
      have hJR : ⁅J, R⁆ ≤ J := Subgroup.le_normalizer_iff_commutator_le_left.mp hRJ
      exact (le_inf ((Subgroup.commutator_mono hJK le_rfl).trans h1) hJR).trans
        (Sec6.Res611Res7.theta_inf_le_theta hJK)
    exact (Sec6.commutator_le_theta_iff hRJ).mp h2
  exact ⟨K, hKe, hJK, hAK, hRK, hRKθ, hJθ⟩

end Off1418

open Wales1418Off

theorem step1418OffLayerR_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hBr : Step1418OffBridgeR) (hPt : Step1418OffPointR) : Step1418OffLayerR := by
  intro G _ _ A c L hR hfail S hS B hB hSB b hbB hbΓ hΓB hbT hWb hWL E hE hΩ R hRE hR2 hAR hRb
  by_contra hnt
  have h : Off1418 G A c L S B b E R :=
    ⟨hR, hfail, hS, hB, hSB, hbB, hbΓ, hΓB, hbT, hWb, hWL, hE, hΩ, hRE, hR2, hAR, hRb⟩
  have hA := h.isE27
  have hbA := h.b_mem_A
  have hG := h.sec15R.toPartTwoStanding
  obtain ⟨J, hJ, hAJ, hRJ, hRJθ⟩ := hBr G A c L S B b E R h hnt
  have hJp : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJE : J ≤ Subgroup.centralizer (E : Set G) := le_of_mem_thetaComponentsIn hJ
  have hall : ∀ e ∈ E, e ≠ 1 → ∀ K ∈ thetaComponentsAt 3 e, J ≤ K →
      A ≤ Subgroup.normalizer (K : Set G) → R ≤ Subgroup.normalizer (K : Set G) →
      ¬ R ≤ thetaQuotCentralizer K → A ⊓ thetaQuotCentralizer K = E := by
    intro e heE he1 K hK _ hAK hRK hRKθ
    rcases inf_thetaQuotCentralizer_eq hA.1 hA.2 h.hyperplane_E hbA heE he1 hK hAK hRK hRE hRb
        hRKθ with heq | heq
    · exact (hPt G A c L S B b E R h e heE he1 K hK hAK hRK hRKθ heq).elim
    · exact heq
  obtain ⟨e₀, he₀E, he₀1⟩ : ∃ e₀ ∈ E, e₀ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hEbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hno
    have := h.card_E
    rw [hEbot, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨K₀, hK₀, hJK₀, hAK₀, hRK₀, hRK₀θ, -⟩ :=
    h.exists_mem_thetaComponentsAt h45 h48 hJ hRJ hRJθ he₀E he₀1
  have hK₀E : A ⊓ thetaQuotCentralizer K₀ = E := hall e₀ he₀E he₀1 K₀ hK₀ hJK₀ hAK₀ hRK₀ hRK₀θ
  have hbK₀ : b ∉ thetaQuotCentralizer K₀ :=
    (inf_thetaQuotCentralizer_le hA.1 hA.2 h.hyperplane_E hbA hAK₀ hRK₀ hRE hRb hRK₀θ).2
  have hK₀fam : K₀ ∈ thetaComponentFamily 3 A :=
    mem_thetaComponentFamily_iff.mpr ⟨e₀, h.hyperplane_E.1 he₀E, he₀1, hK₀⟩
  obtain ⟨b', hb'E, hb'1, K', hK', hlt⟩ :=
    Sec6.Wales65B.rank3II_6_5Used_one_of_centralizes h45 h48 hG h.sec15R.mem_partTwoF
      h.sec15R.toSec13Data.mem_partTwoE hK₀fam h.elemE h.card_E (hK₀E ▸ le_rfl) hbA hbK₀
      fun x hx _ T hT2 hTθ hAT => h.le_centralizer_b (h.hyperplane_E.1 hx) hT2 hTθ hAT
  obtain ⟨K₁, hK₁, hJK₁, hAK₁, hRK₁, hRK₁θ, hJθ₁⟩ :=
    h.exists_mem_thetaComponentsAt h45 h48 hJ hRJ hRJθ hb'E hb'1
  set Lb := inSubgroup perfectResidual ((K₀ ⊓ Subgroup.centralizer {b'}) ⊔
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b'})) with hLb
  have hEb' : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({b'} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb'E)
  have hJLb : J ≤ Lb :=
    Sec6.le_inSubgroup_perfectResidual_of_isPerfect hJp
      ((le_inf hJK₀ (hJE.trans hEb')).trans le_sup_left)
  have hJK' : J ≤ K' := hJLb.trans hlt.le
  have hK'eq : K' = K₁ := Wales1418Off.eq_of_le_inf hK' hK₁ hJp (le_inf hJK' hJK₁) hJθ₁
  subst hK'eq
  have hE' : A ⊓ thetaQuotCentralizer K' = E := hall b' hb'E hb'1 K' hK' hJK' hAK₁ hRK₁ hRK₁θ
  have hEC : E ≤ thetaQuotCentralizer K' := fun x hx => (hE'.symm ▸ hx : x ∈ A ⊓ _).2
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian h.elemE
  have hK'p : Group.IsPerfect K' := isPerfect_of_mem_thetaComponentsIn hK'
  have hcov := Sec6.le_residual_inf_centralizer_sup_theta hK'p hE3 hEC
  have hZ := Sec6.residual_inf_centralizer_mem_thetaComponentsIn hK' hE3 hEC
  have hEinf : Subgroup.centralizer (E : Set G) ⊓ Subgroup.centralizer ({b'} : Set G) =
      Subgroup.centralizer (E : Set G) := inf_eq_left.mpr hEb'
  rw [hEinf] at hZ
  have hJZ : J ≤ inSubgroup perfectResidual (K' ⊓ Subgroup.centralizer (E : Set G)) :=
    Sec6.le_inSubgroup_perfectResidual_of_isPerfect hJp (le_inf hJK' hJE)
  have hJθE : ¬ J ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (E : Set G)) := by
    intro hle
    have hJθJ : J ≤ inSubgroup (aschbacherSolvableCore 3) J :=
      (le_inf hle le_rfl).trans (Sec6.Res611Res7.theta_inf_le_theta hJE)
    exact Sec15.Proof1423.not_le_thetaQuotCentralizer_self hJ
      (hJθJ.trans (Sec6.theta_le_thetaQuotCentralizer J))
  have hZJ : inSubgroup perfectResidual (K' ⊓ Subgroup.centralizer (E : Set G)) = J :=
    (Wales1418Off.eq_of_le_inf hJ hZ hJp (le_inf le_rfl hJZ) hJθE).symm
  rw [hZJ] at hcov
  have hθK' : inSubgroup (aschbacherSolvableCore 3) K' ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b'} : Set G)) := by
    obtain ⟨hK'C, hK'θ⟩ := mem_thetaComponentsIn_iff.mp hK'
    exact Sec13.inSubgroup_theta_le_of_isSubnormal hK'C hK'θ.2.1
  have hK'Lb : K' ≤ Lb :=
    Sec6.le_inSubgroup_perfectResidual_of_isPerfect hK'p
      (hcov.trans (sup_le_sup ((le_inf hJK₀ (hJE.trans hEb'))) hθK'))
  exact (lt_irrefl K') (lt_of_le_of_lt hK'Lb hlt)

end CFSG.RankThree.PartTwo.Sec14
