module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res6ProofCanon
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofImage
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofCentWA
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSwapW
import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofSylow
public import CFSG.RankThree.PartTwo.Sec11.Item119Used

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Statements

@[expose] def Gap1117NotActXPGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g e : G) (Y' : Subgroup G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} → orderOf x = 9 →
      g * x * g⁻¹ ∈ Subgroup.zpowers x → ⁅sec11P R g, sec11P R g⁆ = Subgroup.zpowers d →
      e ∈ A → e ∉ Subgroup.closure {c, d} → (∀ w ∈ sec11P R g, ⁅e, w⁆ = w ^ 3) →
      Y' ∈ thetaComponentsAt 3 e → sec11K L e ≤ Y' → ¬ KFacts.InducesStdKind Y' c .field →
      Sec8.IsZ3PGLThreePi (sec11YA e Y' A) →
      ∀ Q : Subgroup G, IsSylowOf 3 Q (Subgroup.centralizer {e}) →
        sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q →
          Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
            Subgroup.centralizer (A : Set G)

end Statements

namespace Item1117Res6Proof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

open Item1117ResProof in
theorem isSylowOf_inf_of_swap (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'') :
    IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G))
      (Subgroup.normalizer (Subgroup.zpowers e : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) with hT
  set CA := Subgroup.centralizer (A : Set G) with hCA
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hdA := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := hexp d hdA
  have hd3o : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hR'W : R' ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_eq_closure (h113 G A e Ye c R' Y'' hstd).1
  have hR'N : R' ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := hstd.isSylowOf.le
  have hR'3 : IsPGroup 3 R' := hstd.isSylowOf.isPGroup
  have hR'el : ∀ w ∈ R', ∃ k : ℕ, w ^ 3 ^ k = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hR'3 ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hact := Item1117Res5Proof.forall_commutator_mem_of_swap h45 h97 h113 h117 h119 h heA hecd
    hYe hKYe hstd
  have hR'c : ∀ w ∈ R', w * c * w⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := fun w hw =>
    hact w hw c h.mem_A
  have hR'd : ∀ w ∈ R', w * d = d * w := fun w hw => by
    obtain ⟨k, hk⟩ := hR'el w hw
    exact Sec12.commute_of_conj_mem_zpowers hd3o ((Subgroup.mem_normalizer_iff.mp
      (Item1115Proof.W_le_normalizer_d h117 h (hR'W hw)) d).mp (Subgroup.mem_zpowers d)) hk
  have hR'e : ∀ w ∈ R', w * e = e * w := fun w hw => by
    obtain ⟨k, hk⟩ := hR'el w hw
    have he1 : e ≠ 1 := fun h1 => hecd (h1 ▸ Subgroup.one_mem _)
    exact Sec12.commute_of_conj_mem_zpowers (orderOf_eq_prime (hexp e heA) he1)
      ((Subgroup.mem_normalizer_iff.mp (hR'N hw) e).mp (Subgroup.mem_zpowers e)) hk
  have hcard1 := card_le_three_mul_card_inf_centralizer hd3 hR'd hR'c
  have hA' : A = Subgroup.closure {c, e, d} := by
    rw [h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd, Set.insert_comm]
  have hR'cA : R' ⊓ Subgroup.centralizer ({c} : Set G) ≤ CA := by
    intro w hw
    rw [hCA, Subgroup.mem_centralizer_iff, hA']
    intro z hz
    refine (Subgroup.closure_induction (p := fun z _ => z * w = w * z) ?_ ?_ ?_ ?_ hz)
    · rintro y (rfl | rfl | rfl)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm
      · exact (hR'e w hw.1).symm
      · exact (hR'd w hw.1).symm
    · simp
    · intro y z _ _ hy hz
      rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
    · intro y _ hy
      calc y⁻¹ * w = y⁻¹ * (w * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * w) * y⁻¹ := by rw [hy]
        _ = w * y⁻¹ := by group
  have hCAH : CA ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) := by
    intro z hz
    refine ⟨?_, Subgroup.centralizer_le_normalizer _ hz⟩
    have hzc : z ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hz c h.mem_A).symm)
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hzc
    exact Subgroup.centralizer_le_normalizer _ hzc
  have hNCA : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (CA : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hz ⊢
    intro y hy
    have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hn.2) y).mp hy
    rw [inv_inv] at hy'
    have h1 := hz _ hy'
    calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * y := by group
  have hS := h.isSylowOf_inf.inf_of_le_normalizer hCAH hNCA
  have hcard2 : Nat.card (R' ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) ≤
      Nat.card ((R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA : Subgroup G) :=
    card_le_of_isSylowOf hR'cA (hR'3.to_le inf_le_left) hS
  obtain ⟨n, hn⟩ := Item1117StepsProof.exists_mul_pow_mem_inf h45 h117 h hsc hrs heA hecd
  have hCRT : (R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA ≤ T ⊓ CA := by
    refine le_inf ?_ inf_le_right
    intro z hz
    refine ⟨Item1119Proof.R_le_P R g hz.1.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 e heA).symm
  have hgxc : g * x ^ n ∉ T ⊓ CA := by
    intro hm
    have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp
      (Item1117Proof.R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)
    have h1 := Subgroup.mem_centralizer_iff.mp hm.2 c h.mem_A
    apply h.g_not_mem
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have e1 : g * c * g⁻¹ = (g * x ^ n) * c * (g * x ^ n)⁻¹ := by
      have := (Commute.pow_left hxc n).eq
      calc g * c * g⁻¹ = g * (x ^ n * c * (x ^ n)⁻¹) * g⁻¹ := by
            rw [this, mul_inv_cancel_right]
        _ = (g * x ^ n) * c * (g * x ^ n)⁻¹ := by group
    rw [e1, ← h1, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  have hcard3 : 3 * Nat.card (T ⊓ CA : Subgroup G) ≤ Nat.card T :=
    three_mul_card_le_of_lt inf_le_left (h.isPGroup_sec11P.to_le inf_le_left) hn hgxc
  have hcard4 : Nat.card ((R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA : Subgroup G) ≤
      Nat.card (T ⊓ CA : Subgroup G) := Subgroup.card_le_of_le hCRT
  have hgoal : Nat.card R' ≤ Nat.card T := by omega
  have hTN : T ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    refine inf_le_right.trans ?_
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  exact Item1117StepsProof.isSylowOf_of_card_le hTN (h.isPGroup_sec11P.to_le inf_le_left)
    hstd.isSylowOf hgoal

theorem false_of_not_field_of_big (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h119 : Item119) (hND : KFact1117Cube) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) (hx9 : 9 < orderOf x)
    {e : G} (heA : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hnf : ¬ KFacts.InducesStdKind Ye c .field) : False := by
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hYe hKYe
  have hAe := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  obtain ⟨a', Y', g', hstd', ha'A, ha'cd, hg3, hgYW, hgR, hgH, hgc, hnf'⟩ :=
    Item1117Proof.exists_choice_g_not_field h45 h113 h117 h119 hstdE h.inf_eq hAe hnf
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha'A ha'cd
  have hR := Item1117Proof.R_eq_closure_of_mem h hsc hrs ha'A ha'cd
  have h' : Sec11Data G A c L a' R Y' d x s a' g' :=
    { toSec11Std := hstd'
      inf_eq := h.inf_eq
      closure_eq := hA'
      inf_L_eq := h.inf_L_eq
      inf_centralizer_eq := h.inf_centralizer_eq
      R_eq := hR
      a_mem_closure := Subgroup.subset_closure (by simp)
      pow_eq_one := hg3
      g_mem := hgYW
      g_mem_normalizer := hgR
      g_not_mem := hgH
      conj_mem := hgc }
  exact Item1117Proof.false_of_not_field h119 hND h' hsc rfl hnf' hx9

end Data

section Big

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem isSylowOf_centralizer_of_not_field (h45 : Sec4.Item4_5) (h113 : Item113)
    (h117 : Item117) (h118 : Item118) (h119 : Item119Used) (hK : AutThree1129)
    (hpgl : Gap1117NotActXPGL) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) (hx9 : orderOf x = 9)
    (hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x)
    (hPP : ⁅sec11P R g, sec11P R g⁆ = Subgroup.zpowers d) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G))
    (hcan : ∀ w ∈ sec11P R g, ⁅e, w⁆ = w ^ 3) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y')
    (hnf : ¬ KFacts.InducesStdKind Y' c .field) :
    IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer {e}) (Subgroup.centralizer {e}) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  obtain ⟨-, hrest⟩ := h119 G A c L e R Y' hstd d h.inf_eq hA'
  obtain ⟨X, _, hX, ⟨φ⟩⟩ : ∃ (X : Type) (_ : Group X), IsList119 X ∧
      Nonempty (sec11YA e Y' A ≃* Multiplicative (ZMod 3) × X) := by
    rcases hrest with hf | hX
    · exact absurd hf hnf
    · exact hX
  set C := Subgroup.centralizer ({e} : Set G) with hC
  set T := sec11P R g ⊓ C with hT
  have hT3 : IsPGroup 3 T := h.isPGroup_sec11P.to_le inf_le_left
  obtain ⟨Q₀, hQ₀⟩ := (hT3.comap_subtype (K := C)).exists_le_sylow
  set Q := (Q₀ : Subgroup C).map C.subtype with hQdef
  have hQ : IsSylowOf 3 Q C := ⟨Q₀, rfl⟩
  have hTQ : T ≤ Q := fun y hy => ⟨⟨y, hy.2⟩, hQ₀ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have he1 : e ≠ 1 := fun he => hecd (he ▸ Subgroup.one_mem _)
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e heA)
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe heA he1 Y' hY'
  have hWA : Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
    by_cases hP : Sec8.IsZ3PGLThreePi (sec11YA e Y' A)
    · exact hpgl G A c L a R Y d x s r g e Y' h hsc hrs hx9 hgx hPP heA hecd hcan hY' hKY' hnf
        hP Q hQ hTQ
    · intro v hv
      have hns : ¬ Group.IsSolvable (_root_.commutator X) := by
        intro hsol
        obtain ⟨ψ⟩ := Item1116Proof.nonempty_thetaQuot_equiv_commutator hY' hAC hAY hAc φ
        have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY'
        have : Group.IsSolvable (Y' ⧸ aschbacherSolvableCore 3 Y') :=
          Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
        have : Group.IsPerfect (Y' ⧸ aschbacherSolvableCore 3 Y') := hq.1
        have : Nontrivial (Y' ⧸ aschbacherSolvableCore 3 Y') := by
          by_contra hnt
          rw [not_nontrivial_iff_subsingleton] at hnt
          obtain ⟨u, w, huw⟩ := hq.2.2
          exact huw (Subsingleton.elim _ _)
        exact Group.IsPerfect.not_isSolvable _ ‹_›
      have hP' : ¬ ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
          Sec4.ModThree π (p ^ f) ∧ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projImage
            (Sec4.glPi π 3 (p ^ f) K)) := by
        rintro ⟨π, p, f, K, hK, hPF, hmod, ⟨ψ⟩⟩
        exact hP ⟨π, p, f, K, hK, hPF, hmod, ⟨φ.trans (MulEquiv.prodCongr (MulEquiv.refl _) ψ)⟩⟩
      obtain ⟨hXp, hXZ⟩ := Item1117Res4Proof.isPerfect_center_of_isList119 hX hP' hns
      exact Item1117Res4Proof.mem_centralizer_of_sec11YA h45 h.toTheoremFourHyp h.mem_partTwoF heA
        he1 hY' φ hXp hXZ (hQ.le hv.1.1) hv.1.2 hv.2
  have hW : Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.zpowers e := fun v hv =>
    Item1117ResProof.mem_zpowers_of_mem_centralizer_A h45 h118 h heA hecd hY' hKY' hQ hTQ hv
      (hWA hv)
  have hV := Item1118StepsProof.inf_thetaQuotCentralizer_le h45 h heA hecd hY' hQ hTQ hW
  have hQT := Item1117Res4Proof.eq_of_case_two h45 h113 h117 hK h heA hecd hY' hKY' hsc hrs hx9 hX
    ⟨φ⟩ hQ hTQ hV
  have hTQ' : T = Q := hQT.symm
  rw [hTQ']
  exact hQ

end Big

end Item1117Res6Proof

section Main

open Item1117Res6Proof in
theorem gap1117NotActXNormal_of_res6 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h97 : Sec9.Item97) (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119)
    (h1016 : Sec10.Item1016) (hG2 : KFact1117CubeG2) (hL3 : KFact1117CubeL3)
    (hK : AutThree1129) (hpgl : Gap1117NotActXPGL) : Gap1117NotActXNormal := by
  intro G _ _ A c L a R Y d x s r g h hsc hrs _hcase hgx3 hgx hPP
  exfalso
  have hND := kFact1117Cube_of h45 h117 h118 hG2 hL3
  have h119U := item119Used_of_item119 h119
  obtain ⟨v, hvA, hcan, hxv⟩ := exists_canonical h45 h117 h hsc hrs hgx3 hPP
  have hvcd : v ∉ Subgroup.closure ({c, d} : Set G) := by
    intro hv
    apply hxv
    have hle : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
          (Item1117Proof.R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Item1117Proof.commute_d_x h)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
  obtain ⟨Yv, hYv, hKYv⟩ := exists_mem_thetaComponentsAt_sec11K_le h45 h48 h.toSec11Std h.inf_eq
    h.closure_eq hvA hvcd
  have hS : IsSylowOf 3 (sec11P R g) ⊤ := by
    by_cases hf : KFacts.InducesStdKind Yv c .field
    · obtain ⟨R', Y'', hstd⟩ :=
        Item1117Proof.exists_sec11Std_swap h45 h48 h97 h118 h1016 h hvA hvcd hYv hKYv hf
      have hC := isSylowOf_inf_of_swap h45 h97 h113 h117 h119 h hsc hrs hvA hvcd hYv hKYv hstd
      refine isSylowOf_top_of_canonical h45 h117 h hsc hrs hgx3 hPP hvA hcan hxv ?_ hC
      rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
      exact Subgroup.centralizer_le_normalizer _
    · have hx9 : orderOf x = 9 := by
        by_contra hx9
        have h9 : 9 ≤ orderOf x := Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x))
          (Item1117Proof.nine_dvd_orderOf_x h)
        exact false_of_not_field_of_big h45 h113 h117 h119 hND h hsc hrs (by omega) hvA hvcd hYv
          hKYv hf
      have hcan3 : ∀ w ∈ sec11P R g, ⁅v, w⁆ = w ^ 3 := by
        intro w hw
        rw [hcan w hw, hx9]
      have hC := isSylowOf_centralizer_of_not_field h45 h113 h117 h118 h119U hK hpgl h hsc hrs hx9
        hgx hPP hvA hvcd hcan3 hYv hKYv hf
      exact isSylowOf_top_of_canonical h45 h117 h hsc hrs hgx3 hPP hvA hcan hxv le_rfl hC
  exact false_of_isSylowOf h45 h117 h hsc hrs hgx3 hPP hS

theorem item1117_of_res6 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119)
    (h82 : Sec8.Item82One) (h1016 : Sec10.Item1016) (h1116 : Item1116)
    (hG2 : KFact1117CubeG2) (hL3 : KFact1117CubeL3) (hK : AutThree1129)
    (hpgl : Gap1117NotActXPGL) : Item1117 :=
  item1117_of_res5 h45 h48 h97 h113 h117 h118 h119 h82 h1016 h1116 hG2 hL3
    (gap1117NotActXNormal_of_res6 h45 h48 h97 h113 h117 h118 h119 h1016 hG2 hL3 hK hpgl)

end Main

end CFSG.RankThree.PartTwo.Sec11
