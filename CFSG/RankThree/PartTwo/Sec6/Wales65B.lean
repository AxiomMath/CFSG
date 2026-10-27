module

public import CFSG.RankThree.PartTwo.Sec6.Item65One
public import CFSG.RankThree.PartTwo.Sec6.Wales65BTrick
import CFSG.RankThree.PartTwo.Sec6.Item65UsedTools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec6.Wales65B

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx65B (G : Type) [Group G] [Finite G] (A L B : Subgroup G) (a₀ b : G) :
    Prop where
  standing : PartTwoStanding G
  mem_F : A ∈ partTwoF G
  mem_E : A ∈ partTwoE G
  a₀_mem : a₀ ∈ A
  a₀_ne : a₀ ≠ 1
  mem_L : L ∈ thetaComponentsAt 3 a₀
  elemB : CFSG.Assembly.IsElemAbelian 3 B
  cardB : Nat.card B = 9
  B_le : B ≤ A ⊓ thetaQuotCentralizer L
  b_mem : b ∈ A
  b_not_mem : b ∉ thetaQuotCentralizer L
  centralizes : ∀ x ∈ B, x ≠ 1 → ∀ T : Subgroup G, IsPGroup 2 T →
    T ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {x}) →
    A ≤ Subgroup.normalizer (T : Set G) → T ≤ Subgroup.centralizer {b}
  neg : ∀ x ∈ B, x ≠ 1 → ∀ K ∈ thetaComponentsAt 3 x,
    ¬ inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {x}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {x})) < K

private theorem le_sup_theta_self {M Z' Y : Subgroup G} (hZ' : Z' ∈ thetaComponentsIn M)
    (hYZ' : Y ≤ Z') (hZ'Y : Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) M) :
    Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) Z' := by
  have hZ'M := le_of_mem_thetaComponentsIn hZ'
  have hθeq := theta_eq_inf_of_mem_thetaComponentsIn hZ'
  intro z hz
  have hz' : z ∈ (Y : Set G) * (inSubgroup (aschbacherSolvableCore 3) M : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y _
      ((hYZ'.trans hZ'M).trans (le_normalizer_theta M))]
    exact hZ'Y hz
  obtain ⟨y, hy, t, ht, rfl⟩ := hz'
  have htZ' : t ∈ Z' := by
    have := Z'.mul_mem (Z'.inv_mem (hYZ' hy)) hz
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
    (Subgroup.mem_sup_right (hθeq ▸ ⟨htZ', ht⟩))

namespace Ctx65B

variable {A L B : Subgroup G} {a₀ b : G} (h : Ctx65B G A L B a₀ b)
include h

private theorem B_le_A : B ≤ A := h.B_le.trans inf_le_left

private theorem B_le_C : B ≤ thetaQuotCentralizer L := h.B_le.trans inf_le_right

private theorem elemA : CFSG.Assembly.IsElemAbelian 3 A := h.mem_F.1

private theorem isPGroup_B : IsPGroup 3 B := Sec5.isPGroup_of_isElemAbelian h.elemB

private theorem isPGroup_A : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian h.elemA

private theorem A_le_centralizer {a : G} (haA : a ∈ A) : A ≤ Subgroup.centralizer ({a} : Set G) :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (h.elemA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))

private theorem B_le_centralizer {a : G} (haB : a ∈ B) : B ≤ Subgroup.centralizer ({a} : Set G) :=
  h.B_le_A.trans (h.A_le_centralizer (h.B_le_A haB))

private theorem A_le_centralizer_B : A ≤ Subgroup.centralizer (B : Set G) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun β hβ =>
    congrArg Subtype.val (h.elemA.1.is_comm.comm ⟨β, h.B_le_A hβ⟩ ⟨x, hx⟩)

private theorem A_le_normalizer_B : A ≤ Subgroup.normalizer (B : Set G) :=
  h.A_le_centralizer_B.trans (Subgroup.centralizer_le_normalizer _)

private theorem A_le_normalizer (h45 : Sec4.Item4_5) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∀ K ∈ thetaComponentsAt 3 a, A ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_mem_thetaComponentsAt h45 h.standing.toTheoremFourHyp h.elemA haA ha1

private theorem sectionFourHyp {a : G} (ha1 : a ≠ 1) :
    SectionFourHyp (Subgroup.centralizer ({a} : Set G)) :=
  h.standing.toTheoremFourHyp.sectionFourHyp
    (centralizer_ne_top_of_ne_one h.standing.toTheoremFourHyp ha1)

private theorem exists_ne_one : ∃ x ∈ B, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
  have := h.cardB
  rw [hbot, Subgroup.card_bot] at this
  norm_num at this

private theorem sectionFourHyp_B : SectionFourHyp (Subgroup.centralizer (B : Set G)) := by
  obtain ⟨x, hxB, hx1⟩ := h.exists_ne_one
  refine h.standing.toTheoremFourHyp.sectionFourHyp fun htop => ?_
  apply centralizer_ne_top_of_ne_one h.standing.toTheoremFourHyp hx1
  rw [eq_top_iff, ← htop]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxB)

private theorem A_le_normalizer_B' (h45 : Sec4.Item4_5) :
    ∀ K ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)),
      A ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 h.sectionFourHyp_B h.A_le_centralizer_B
    h.elemA (exists_card_eq_of_mem_partTwoF h.mem_F)

private theorem le_thetaQuotCentralizer (h45 : Sec4.Item4_5) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hLK : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K)
    {V : Subgroup G} (hVa : V ≤ Subgroup.centralizer {a}) (hVB : V ≤ ⁅V, B⁆) :
    V ≤ thetaQuotCentralizer K := by
  have heq := (lt_or_eq_of_le hLK).resolve_left (h.neg a haB ha1 K hK)
  have hAK := h.A_le_normalizer h45 (h.B_le_A haB) ha1
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := h.B_le_A.trans (hAK K hK)
  have hBKC := le_thetaQuotCentralizer_of_residual_eq h.B_le_C (h.B_le_centralizer haB) hK hBK heq
  have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
    hVB.trans (commutator_le_normalizer_of_mem_thetaComponentsAt hVa
      (fun L' hL' => h.B_le_A.trans (hAK L' hL')) hK)
  refine hVB.trans ?_
  rw [Subgroup.commutator_le]
  intro v hv β hβ
  rw [commutatorElement_def]
  exact (thetaQuotCentralizer K).mul_mem (conj_mem_thetaQuotCentralizer (hBKC hβ) (hVK hv))
    ((thetaQuotCentralizer K).inv_mem (hBKC hβ))

private theorem exists_Z' (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) :
    ∃ Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)),
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) ≤ Z' ∧
      A ≤ Subgroup.normalizer (Z' : Set G) ∧
      ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
        inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K := by
  set Z := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) with hZdef
  have hZ := residual_inf_centralizer_mem_thetaComponentsIn h.mem_L h.isPGroup_B h.B_le_C
  have hLp := isPerfect_of_mem_thetaComponentsAt h.mem_L
  have hLq := isQuasisimple_of_mem_thetaComponentsAt h.mem_L
  have hZp : Group.IsPerfect Z := isPerfect_inSubgroup_perfectResidual _
  have hZ1 : Z ≠ ⊥ := residual_inf_centralizer_ne_bot hLp hLq h.isPGroup_B h.B_le_C
  have hAn := exists_card_eq_of_mem_partTwoF h.mem_F
  obtain ⟨Z', hZ', hZZ'⟩ := exists_le_mem_thetaComponentsIn h48 h.sectionFourHyp_B
    h.A_le_centralizer_B h.elemA hAn h.a₀_mem h.a₀_ne hZ
  refine ⟨Z', hZ', hZZ', h.A_le_normalizer_B' h45 Z' hZ', ?_⟩
  intro a haB ha1 K hK hLK
  obtain ⟨a', ha'B, ha'1, -, hCeq⟩ := exists_centralizer_eq_inf h.elemB h.cardB haB ha1
  have hZ'' : Z' ∈ thetaComponentsIn
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {a'}) := hCeq ▸ hZ'
  obtain ⟨K'', hK'', hZ'K''⟩ := exists_le_mem_thetaComponentsIn h48 (h.sectionFourHyp ha1)
    (h.A_le_centralizer (h.B_le_A haB)) h.elemA hAn (h.B_le_A ha'B) ha'1 hZ''
  have heq := eq_of_mem_thetaComponentsIn_of_le hK'' hK hZp hZ1 (hZZ'.trans hZ'K'')
    ((residual_inf_centralizer_le_residual haB).trans hLK)
  exact heq ▸ hZ'K''

private theorem not_mem_thetaQuotCentralizer (h45 : Sec4.Item4_5) {Z' : Subgroup G}
    (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZZ' : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) ≤ Z') :
    b ∉ thetaQuotCentralizer Z' := by
  have hLp := isPerfect_of_mem_thetaComponentsAt h.mem_L
  have hLq := isQuasisimple_of_mem_thetaComponentsAt h.mem_L
  have hbL : b ∈ Subgroup.normalizer (L : Set G) :=
    h.A_le_normalizer h45 h.a₀_mem h.a₀_ne L h.mem_L h.b_mem
  exact not_mem_thetaQuotCentralizer_of_cover hLp hLq hbL h.b_not_mem
    (isPerfect_inSubgroup_perfectResidual _) ((inSubgroup_perfectResidual_le _).trans inf_le_left)
    (le_residual_inf_centralizer_sup_theta hLp h.isPGroup_B h.B_le_C) hZZ'
    (h.A_le_normalizer_B' h45 Z' hZ' h.b_mem)

private theorem exists_R₀ : ∃ c ∈ B, c ≠ 1 ∧ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ IsPGroup 2 R₀ ∧
    R₀ ≤ Subgroup.centralizer {c} ∧ A ≤ Subgroup.normalizer (R₀ : Set G) ∧ ⁅R₀, B⁆ = R₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U₀, hU₀1, hU₀2, hAU₀⟩ := h.mem_E.2.2
  set N₀ := Subgroup.normalizer (U₀ : Set G) with hN₀
  set Q₀ := inSubgroup (CFSG.pCore 2) N₀ with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := CFSG.pCore_isPGroup.map _
  have hN₀Q₀ : N₀ ≤ Subgroup.normalizer (Q₀ : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 N₀))
  have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) := hAU₀.trans hN₀Q₀
  have hBQ₀ : B ≤ Subgroup.normalizer (Q₀ : Set G) := h.B_le_A.trans hAQ₀
  have hfaith : B ⊓ Subgroup.centralizer (Q₀ : Set G) = ⊥ := by
    have hc := h.standing.charTwoType N₀ ⟨U₀, hU₀1, hU₀2, rfl⟩
    rw [pCoreOf_two_eq_inSubgroup] at hc
    rw [eq_bot_iff]
    intro β hβ
    have hβQ : β ∈ Q₀ := hc ⟨hAU₀ (h.B_le_A hβ.1), hβ.2⟩
    exact Subgroup.mem_bot.mpr (Source.eq_one_of_pow_three_eq_one hQ₀2 hβQ (h.elemB.2 β hβ.1))
  have hcop : Nat.Coprime 3 (Nat.card Q₀) := by
    obtain ⟨k, hk⟩ := hQ₀2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hex : ∃ c ∈ B, c ≠ 1 ∧ ⁅Q₀ ⊓ Subgroup.centralizer {c}, B⁆ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hQB : Q₀ ≤ Subgroup.centralizer (B : Set G) :=
      Sec5.le_of_forall_inf_centralizer_le Nat.prime_three h.elemB (by rw [h.cardB]; norm_num)
        hBQ₀ hcop
        fun c hc hc1 => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hno c hc hc1)
    have hBC : B ≤ Subgroup.centralizer (Q₀ : Set G) := Subgroup.le_centralizer_iff.mp hQB
    have hB1 : B = ⊥ := by rw [← inf_eq_left.mpr hBC, hfaith]
    have := h.cardB
    rw [hB1, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨c, hcB, hc1, hR⟩ := hex
  set S₀ := Q₀ ⊓ Subgroup.centralizer ({c} : Set G) with hS₀
  have hAc := h.A_le_centralizer (h.B_le_A hcB)
  have hAS₀ : A ≤ Subgroup.normalizer (S₀ : Set G) :=
    (le_inf hAQ₀ (hAc.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hBS₀ : B ≤ Subgroup.normalizer (S₀ : Set G) := h.B_le_A.trans hAS₀
  have hRS₀ : ⁅S₀, B⁆ ≤ S₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hBS₀
  have hS₀2 : IsPGroup 2 S₀ := hQ₀2.to_le inf_le_left
  refine ⟨c, hcB, hc1, ⁅S₀, B⁆, hR, hS₀2.to_le hRS₀, hRS₀.trans inf_le_right, fun e he =>
    Source.mem_normalizer_commutator (hAS₀ he) (h.A_le_normalizer_B he), ?_⟩
  have hcop' : (Nat.card B).Coprime (Nat.card S₀) := by
    obtain ⟨k, hk⟩ := hS₀2.exists_card_eq
    rw [h.cardB, hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S₀ B hcop' hBS₀

private theorem exists_R_Y (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    {Z' : Subgroup G} (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZZ' : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) ≤ Z')
    (hAZ' : A ≤ Subgroup.normalizer (Z' : Set G))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K) :
    ∃ R Y : Subgroup G, R ≠ ⊥ ∧ IsPGroup 2 R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      Group.IsPerfect Y ∧ Y ≠ ⊥ ∧ Y ≤ Z' ∧
      Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)) ∧
      Y ≤ Subgroup.centralizer (R : Set G) ∧ A ≤ Subgroup.normalizer (Y : Set G) ∧
      ⁅Y, Subgroup.zpowers b⁆ = Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcB, hc1, R₀, hR₀1, hR₀2, hR₀c, hAR₀, hR₀B⟩ := h.exists_R₀
  obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_F
    h.a₀_mem h.a₀_ne (h.B_le_A hcB) hc1 h.mem_L (h.B_le_C hcB)
  have hR₀C : R₀ ≤ thetaQuotCentralizer K :=
    h.le_thetaQuotCentralizer h45 hcB hc1 hK hLK hR₀c hR₀B.ge
  have hR₀K : R₀ ≤ Subgroup.normalizer (K : Set G) :=
    hR₀C.trans (thetaQuotCentralizer_le_normalizer K)
  set Cc := Subgroup.centralizer ({c} : Set G) with hCc
  set θc := inSubgroup (aschbacherSolvableCore 3) Cc with hθc
  set N := R₀ ⊔ θc with hN
  have hAc := h.A_le_centralizer (h.B_le_A hcB)
  have hBc : B ≤ Cc := h.B_le_A.trans hAc
  have hKc : K ≤ Cc := le_centralizer_of_mem_thetaComponentsAt hK
  have hR₀θc : R₀ ≤ Subgroup.normalizer (θc : Set G) := hR₀c.trans (le_normalizer_theta Cc)
  have hN3 : ¬ 3 ∣ Nat.card N := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hR₀2
    hR₀θc (theta_solvable_and_not_dvd Cc).2
  have hNc : N ≤ Cc := sup_le hR₀c (theta_le Cc)
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro e he x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hAR₀ he) x).mp hx)
    · intro e he x hx
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta Cc (hAc he)) x).mp hx)
  obtain ⟨P, hPsyl, hR₀P, hAP⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two h.isPGroup_A hN3 hAN le_sup_left hR₀2 hAR₀
  have hPN : P ≤ N := hPsyl.1
  have hP2 : IsPGroup 2 P := hPsyl.2.1
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := h.B_le_A.trans hAP
  set R := ⁅P, B⁆ with hRdef
  have hRP : R ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hBP
  have hR2 : IsPGroup 2 R := hP2.to_le hRP
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := fun e he =>
    Source.mem_normalizer_commutator (hAP he) (h.A_le_normalizer_B he)
  have hR₀R : R₀ ≤ R := by
    rw [← hR₀B]
    exact Subgroup.commutator_mono hR₀P le_rfl
  have hR1 : R ≠ ⊥ := fun h0 => hR₀1 (le_bot_iff.mp (h0 ▸ hR₀R))
  have hKR₀ : ⁅K, R₀⁆ ≤ θc := by
    have h1 := (commutator_le_theta_iff hR₀K).mpr hR₀C
    rw [theta_eq_inf_of_mem_thetaComponentsAt hK] at h1
    exact h1.trans inf_le_right
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set T := inSubgroup (aschbacherSolvableCore 3) CB with hT
  set D := Subgroup.normalizer (P : Set G) ⊓ CB with hD
  have hZ'C : Z' ≤ CB := le_of_mem_thetaComponentsIn hZ'
  have hZ'K' : Z' ≤ K := hZ'K c hcB hc1 K hK hLK
  have hCBc : CB ≤ Cc := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  have hZ'N : Z' ≤ Subgroup.normalizer (N : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro z hz r hr
      have h1 : ⁅z, r⁆ ∈ θc := hKR₀ (Subgroup.commutator_mem_commutator (hZ'K' hz) hr)
      rw [show z * r * z⁻¹ = ⁅z, r⁆ * r by rw [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hr)
    · intro z hz x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_theta Cc (hCBc (hZ'C hz))) x).mp hx)
  have hθCB : θc ⊓ CB ≤ T := by
    have hn : CB ≤ Subgroup.normalizer ((θc ⊓ CB : Subgroup G) : Set G) :=
      (le_inf (hCBc.trans (le_normalizer_theta Cc)) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hsol : Group.IsSolvable (θc ⊓ CB : Subgroup G) :=
      isSolvable_subgroup_of_le inf_le_left (theta_solvable_and_not_dvd Cc).1
    have h3 : ¬ 3 ∣ Nat.card (θc ⊓ CB : Subgroup G) := fun h3 =>
      (theta_solvable_and_not_dvd Cc).2 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact le_theta_of_normal inf_le_right hn hsol h3
  have hDT : D ≤ Subgroup.normalizer (T : Set G) := inf_le_right.trans (le_normalizer_theta CB)
  have hPθc : P ≤ Subgroup.normalizer (θc : Set G) :=
    (hPN.trans hNc).trans (le_normalizer_theta Cc)
  have hNP : N ≤ P ⊔ θc := by
    obtain ⟨P₀, hP₀⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hPsyl
    have h1 := le_sylow_sup_of_forall_pow_mem (Y := N) (le_sup_right : θc ≤ N)
      (sup_le hR₀θc Subgroup.le_normalizer) (fun y hy => exists_pow_mem_of_mem_sup hR₀2 hR₀θc hy)
      P₀
    rwa [hP₀] at h1
  have hFrat : Z' ≤ D ⊔ T := by
    intro z hz
    have hzC := hZ'C hz
    have hS' := fusionIsSylowIn_map_conj hPsyl (hZ'N hz)
    have hBPz : B ≤ Subgroup.normalizer
        ((P.map (MulAut.conj z).toMonoidHom : Subgroup G) : Set G) :=
      le_normalizer_map_conj hBP hzC
    obtain ⟨x, ⟨hxN, hxB⟩, hxeq⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
      Nat.prime_three Nat.prime_two h.isPGroup_B hN3 (h.B_le_A.trans hAN) hPsyl hS' hBP hBPz
    have hd : x⁻¹ * z ∈ D :=
      ⟨inv_mul_mem_normalizer_of_map_conj_eq hxeq, CB.mul_mem (CB.inv_mem hxB) hzC⟩
    obtain ⟨p, hpP, hpB, hpx⟩ := exists_mem_centralizer_inv_mul_mem h.isPGroup_B hBP
      (hBc.trans (le_normalizer_theta Cc)) hPθc (theta_solvable_and_not_dvd Cc).2
      (hNP hxN) hxB
    have hpD : p ∈ D := ⟨Subgroup.le_normalizer hpP, hpB⟩
    have htT : p⁻¹ * x ∈ T := hθCB ⟨hpx, CB.mul_mem (CB.inv_mem hpB) hxB⟩
    rw [show z = p * (p⁻¹ * x) * (x⁻¹ * z) by group]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hpD)
      (Subgroup.mem_sup_right htT)) (Subgroup.mem_sup_left hd)
  set W := (Z' ⊔ T) ⊓ D with hW
  set Y := inSubgroup perfectResidual W with hY
  have hYp : Group.IsPerfect Y := isPerfect_inSubgroup_perfectResidual W
  have hYW : Y ≤ W := inSubgroup_perfectResidual_le W
  have hYD : Y ≤ D := hYW.trans inf_le_right
  have hYZ' : Y ≤ Z' := le_of_isPerfect_of_le_sup_theta hZ' hYp (hYW.trans inf_le_left)
  have hZ'p := isPerfect_of_mem_thetaComponentsIn hZ'
  have hZ'W : Z' ≤ W ⊔ T := by
    intro z hz
    have hz' : z ∈ (D : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D T hDT]
      exact hFrat hz
    obtain ⟨d, hd, t, ht, rfl⟩ := hz'
    have hdW : d ∈ W := by
      refine ⟨?_, hd⟩
      rw [show d = d * t * t⁻¹ by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right (T.inv_mem ht))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hdW) (Subgroup.mem_sup_right ht)
  have hZ'Y : Z' ≤ Y ⊔ T := le_perfectResidual_sup hZ'p (inf_le_right.trans hDT) hZ'W
  have hZ1 : inSubgroup perfectResidual (L ⊓ CB) ≠ ⊥ :=
    residual_inf_centralizer_ne_bot (isPerfect_of_mem_thetaComponentsAt h.mem_L)
      (isQuasisimple_of_mem_thetaComponentsAt h.mem_L) h.isPGroup_B h.B_le_C
  have hY1 : Y ≠ ⊥ := by
    intro hY0
    rw [hY0, bot_sup_eq] at hZ'Y
    have hsol : Group.IsSolvable Z' :=
      isSolvable_subgroup_of_le hZ'Y (theta_solvable_and_not_dvd CB).1
    have hZ'1 : Z' ≠ ⊥ := fun h0 => hZ1 (le_bot_iff.mp (h0 ▸ hZZ'))
    have : Nontrivial Z' := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ'1
    have := hZ'p
    exact Group.IsPerfect.not_isSolvable Z' hsol
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
    have hA1 : A ≤ Subgroup.normalizer ((Z' ⊔ T : Subgroup G) : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro e he x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hAZ' he) x).mp hx)
      · intro e he x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_theta CB (h.A_le_centralizer_B he)) x).mp hx)
    have hA2 : A ≤ Subgroup.normalizer (D : Set G) :=
      (le_inf (hAP.trans (normalizer_le_normalizer_normalizer P))
        (h.A_le_centralizer_B.trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hA1 hA2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    hAW.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hYb : ⁅Y, Subgroup.zpowers b⁆ = Y :=
    commutator_zpowers_eq_of_not_mem_thetaQuotCentralizer hZ'p
      (isQuasisimple_of_mem_thetaComponentsIn hZ') (hAZ' h.b_mem)
      (h.not_mem_thetaQuotCentralizer h45 hZ' hZZ') hYp hYZ' (le_sup_theta_self hZ' hYZ' hZ'Y)
      (hAY h.b_mem)
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := hYD.trans inf_le_left
  have hPYP : ⁅P, Y⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hYP
  have hPYθ : ⁅P, Y⁆ ≤ θc := by
    calc ⁅P, Y⁆ ≤ ⁅R₀ ⊔ θc, K⁆ := Subgroup.commutator_mono hPN (hYZ'.trans hZ'K')
      _ ≤ ⁅R₀, K⁆ ⊔ θc :=
          commutator_sup_le_of_le_normalizer hR₀θc (hKc.trans (le_normalizer_theta Cc))
      _ ≤ θc := sup_le (by rw [Subgroup.commutator_comm]; exact hKR₀) le_rfl
  have hAPY : A ≤ Subgroup.normalizer ((⁅P, Y⁆ : Subgroup G) : Set G) := fun e he =>
    Source.mem_normalizer_commutator (hAP he) (hAY he)
  have hPY : ⁅P, Y⁆ = ⊥ := commutator_eq_bot_of_commutator_zpowers_eq hYp hYb hYP
    (h.centralizes c hcB hc1 _ (hP2.to_le hPYP) hPYθ hAPY)
  have hYCP : Y ≤ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.commutator_comm] at hPY
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPY
  have hYR : Y ≤ Subgroup.centralizer (R : Set G) :=
    hYCP.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRP))
  exact ⟨R, Y, hR1, hR2, hAR, hYp, hY1, hYZ', hZ'Y, hYR, hAY, hYb⟩

private theorem commutator_theta_le_of_not_lt (h45 : Sec4.Item4_5) {Z' : Subgroup G}
    (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K)
    {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hLK : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K) :
    ⁅inSubgroup (aschbacherSolvableCore 3) Z', Z'⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  have heq := (lt_or_eq_of_le hLK).resolve_left (h.neg a haB ha1 K hK)
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    h.B_le_A.trans (h.A_le_normalizer h45 (h.B_le_A haB) ha1 K hK)
  have hBKC := le_thetaQuotCentralizer_of_residual_eq h.B_le_C (h.B_le_centralizer haB) hK hBK heq
  obtain ⟨a', ha'B, -, -, hCeq⟩ := exists_centralizer_eq_inf h.elemB h.cardB haB ha1
  have hZ'Ka : Z' ≤ K := hZ'K a haB ha1 K hK hLK
  have hZ'C : Z' ≤ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hZ'
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
  have hle : K ⊓ Subgroup.centralizer ({a'} : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    rw [hCeq]
    exact inf_le_inf_right _ hKa
  have hZ'le : Z' ≤ K ⊓ Subgroup.centralizer ({a'} : Set G) :=
    le_inf hZ'Ka (hZ'C.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha'B)))
  have hsn : (Z'.subgroupOf (K ⊓ Subgroup.centralizer ({a'} : Set G))).IsSubnormal := by
    have heq' : Z'.subgroupOf (K ⊓ Subgroup.centralizer ({a'} : Set G)) =
        (Z'.subgroupOf (Subgroup.centralizer (B : Set G))).comap (Subgroup.inclusion hle) := by
      ext m
      simp [Subgroup.mem_subgroupOf]
    rw [heq']
    exact (mem_thetaComponentsIn_iff.mp hZ').2.2.1.comap _
  exact commutator_theta_le_of_mem_thetaQuotCentralizer
    (isQuasisimple_of_mem_thetaComponentsAt hK) (h.elemB.2 a' ha'B) (hBKC ha'B) hZ'le hsn

private theorem false_of_R_Y (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {Z' R Y : Subgroup G}
    (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K)
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥) (hYZ' : Y ≤ Z')
    (hZ'Y : Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)))
    (hYR : Y ≤ Subgroup.centralizer (R : Set G)) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYb : ⁅Y, Subgroup.zpowers b⁆ = Y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set T := inSubgroup (aschbacherSolvableCore 3) CB with hT
  set NR := Subgroup.normalizer (R : Set G) with hNR
  set W := inSubgroup (CFSG.pCore 2) NR with hW
  have hW2 : IsPGroup 2 W := CFSG.pCore_isPGroup.map _
  have hcopW : Nat.Coprime 3 (Nat.card W) := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hNRW : NR ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 NR))
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := hAR.trans hNRW
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := h.B_le_A.trans hAW
  have hYNR : Y ≤ NR := hYR.trans (Subgroup.centralizer_le_normalizer _)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYNR.trans hNRW
  have hZ'C : Z' ≤ CB := le_of_mem_thetaComponentsIn hZ'
  have hYC : Y ≤ CB := hYZ'.trans hZ'C
  have hYNB : Y ≤ Subgroup.normalizer (B : Set G) :=
    hYC.trans (Subgroup.centralizer_le_normalizer _)
  have hWY : ⁅W, Y⁆ ≠ ⊥ := by
    intro h0
    rw [Subgroup.commutator_comm] at h0
    have hYCW : Y ≤ Subgroup.centralizer (W : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have hc := h.standing.charTwoType NR ⟨R, hR1, hR2, rfl⟩
    rw [pCoreOf_two_eq_inSubgroup] at hc
    exact not_isPGroup_two_of_isPerfect hYp hY1 (hW2.to_le ((le_inf hYNR hYCW).trans hc))
  have hVa : ∀ a ∈ B, a ≠ 1 → ⁅⁅W ⊓ Subgroup.centralizer {a}, B⁆, Y⁆ = ⊥ := by
    intro a haB ha1
    obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_F
      h.a₀_mem h.a₀_ne (h.B_le_A haB) ha1 h.mem_L (h.B_le_C haB)
    set S := W ⊓ Subgroup.centralizer ({a} : Set G) with hS
    have hAa := h.A_le_centralizer (h.B_le_A haB)
    have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf hAW (hAa.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hBS : B ≤ Subgroup.normalizer (S : Set G) := h.B_le_A.trans hAS
    set V := ⁅S, B⁆ with hV
    have hVS : V ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hBS
    have hS2 : IsPGroup 2 S := hW2.to_le inf_le_left
    have hV2 : IsPGroup 2 V := hS2.to_le hVS
    have hVa' : V ≤ Subgroup.centralizer {a} := hVS.trans inf_le_right
    have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun e he =>
      Source.mem_normalizer_commutator (hAS he) (h.A_le_normalizer_B he)
    have hVB : ⁅V, B⁆ = V := by
      have hcop : (Nat.card B).Coprime (Nat.card S) := by
        obtain ⟨k, hk⟩ := hS2.exists_card_eq
        rw [h.cardB, hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S B hcop hBS
    have hVC : V ≤ thetaQuotCentralizer K :=
      h.le_thetaQuotCentralizer h45 haB ha1 hK hLK hVa' hVB.ge
    have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
      hVC.trans (thetaQuotCentralizer_le_normalizer K)
    have hYK : Y ≤ K := hYZ'.trans (hZ'K a haB ha1 K hK hLK)
    have hCBa : CB ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hYS : Y ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf hYW ((hYC.trans hCBa).trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hYV : Y ≤ Subgroup.normalizer (V : Set G) := fun y hy =>
      Source.mem_normalizer_commutator (hYS hy) (hYNB hy)
    have hVYV : ⁅V, Y⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV
    have hVYθ : ⁅V, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a}) := by
      have h1 := (commutator_le_theta_iff hVK).mpr hVC
      rw [theta_eq_inf_of_mem_thetaComponentsAt hK] at h1
      calc ⁅V, Y⁆ ≤ ⁅V, K⁆ := Subgroup.commutator_mono le_rfl hYK
        _ = ⁅K, V⁆ := Subgroup.commutator_comm _ _
        _ ≤ _ := h1.trans inf_le_right
    have hAVY : A ≤ Subgroup.normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) := fun e he =>
      Source.mem_normalizer_commutator (hAV he) (hAY he)
    exact commutator_eq_bot_of_commutator_zpowers_eq hYp hYb hYV
      (h.centralizes a haB ha1 _ (hV2.to_le hVYV) hVYθ hAVY)
  set V₀ := W ⊓ CB with hV₀
  have hU : ⁅V₀, Y⁆ ≠ ⊥ := by
    intro hU0
    apply hWY
    have hWY' : W ≤ Subgroup.centralizer (Y : Set G) := by
      refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three h.elemB
        (by rw [h.cardB]; norm_num) hBW hcopW fun a haB ha1 => ?_
      set S := W ⊓ Subgroup.centralizer ({a} : Set G) with hS
      have hBS : B ≤ Subgroup.normalizer (S : Set G) :=
        (le_inf hBW ((h.B_le_centralizer haB).trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hcopS : Nat.Coprime 3 (Nat.card S) := by
        obtain ⟨k, hk⟩ := (hW2.to_le inf_le_left : IsPGroup 2 S).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
        Nat.prime_three B S h.isPGroup_B hBS hcopS
      rw [← hfac]
      refine sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hVa a haB ha1)) ?_
      exact (inf_le_inf_right CB inf_le_left).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hU0)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWY'
  have hV₀2 : IsPGroup 2 V₀ := hW2.to_le inf_le_left
  have hV₀sol : Group.IsSolvable V₀ := by
    have : Group.IsNilpotent V₀ := hV₀2.isNilpotent
    infer_instance
  have hYV₀ : Y ≤ Subgroup.normalizer (V₀ : Set G) :=
    (le_inf hYW (hYC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hV₀Z' : V₀ ≤ Subgroup.normalizer (Z' : Set G) :=
    le_normalizer_of_isPerfect_le_of_mem_thetaComponentsIn hZ' hYZ' hYp hY1 inf_le_right hV₀sol
      hYV₀
  set θZ' := inSubgroup (aschbacherSolvableCore 3) Z' with hθZ'
  have hZ'p := isPerfect_of_mem_thetaComponentsIn hZ'
  have hZ'q := isQuasisimple_of_mem_thetaComponentsIn hZ'
  have hZ'Yθ : Z' ≤ Y ⊔ θZ' := le_sup_theta_self hZ' hYZ' hZ'Y
  set U := ⁅V₀, Y⁆ with hUdef
  have hUV₀ : U ≤ V₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV₀
  have hU2 : IsPGroup 2 U := hV₀2.to_le hUV₀
  have hUZ' : U ≤ Z' := by
    calc U ≤ ⁅V₀, Z'⁆ := Subgroup.commutator_mono le_rfl hYZ'
      _ = ⁅Z', V₀⁆ := Subgroup.commutator_comm _ _
      _ ≤ Z' := Subgroup.le_normalizer_iff_commutator_le_left.mp hV₀Z'
  have hYθZ' : Y ≤ Subgroup.normalizer (θZ' : Set G) := hYZ'.trans (le_normalizer_theta Z')
  have hV₀θZ' : V₀ ≤ Subgroup.normalizer (θZ' : Set G) :=
    hV₀Z'.trans (normalizer_le_normalizer_theta Z')
  have hUθ : ⁅U ⊔ θZ', Z'⁆ ≤ θZ' := by
    have hXZ' : U ⊔ θZ' ≤ Z' := sup_le hUZ' (theta_le Z')
    have hZ'X : Z' ≤ Subgroup.normalizer ((U ⊔ θZ' : Subgroup G) : Set G) := by
      refine hZ'Yθ.trans (sup_le ?_ ?_)
      · apply le_normalizer_sup_of_conj
        · intro y hy x hx
          exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
            (le_normalizer_commutator_right V₀ Y hy) x).mp hx)
        · intro y hy x hx
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hYθZ' hy) x).mp hx)
      · apply le_normalizer_sup_of_conj
        · intro t ht u hu
          have h1 : u⁻¹ * t * u⁻¹⁻¹ ∈ θZ' := (Subgroup.mem_normalizer_iff.mp
            (le_normalizer_theta Z' (Z'.inv_mem (hUZ' hu))) t).mp ht
          rw [show t * u * t⁻¹ = u * ((u⁻¹ * t * u⁻¹⁻¹) * t⁻¹) by group]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
            (Subgroup.mem_sup_right (θZ'.mul_mem h1 (θZ'.inv_mem ht)))
        · intro t ht x hx
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
            (le_normalizer_theta Z' (theta_le Z' ht)) x).mp hx)
    rcases sup_theta_eq_or_commutator_le hZ'q hXZ' hZ'X with hcov | hcen
    · exfalso
      have hUθN : U ≤ Subgroup.normalizer (θZ' : Set G) :=
        hUZ'.trans (le_normalizer_theta Z')
      have hUsol : Group.IsSolvable U := by
        have : Group.IsNilpotent U := hU2.isNilpotent
        infer_instance
      have hXsol := isSolvable_sup_of_le_normalizer hUθN (theta_solvable_and_not_dvd Z').1 hUsol
      rw [sup_assoc, sup_idem] at hcov
      rw [sup_comm] at hXsol
      have hsol : Group.IsSolvable Z' := hcov ▸ hXsol
      have hZ'1 : Z' ≠ ⊥ := fun h0 => hY1 (le_bot_iff.mp (h0 ▸ hYZ'))
      have : Nontrivial Z' := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ'1
      have := hZ'p
      exact Group.IsPerfect.not_isSolvable Z' hsol
    · exact hcen
  have hZ'V₀ : ⁅Z', V₀⁆ ≤ θZ' := by
    have hA : ⁅Z', V₀⁆ ≤ U ⊔ θZ' := by
      calc ⁅Z', V₀⁆ ≤ ⁅Y ⊔ θZ', V₀⁆ := Subgroup.commutator_mono hZ'Yθ le_rfl
        _ ≤ ⁅Y, V₀⁆ ⊔ θZ' := commutator_sup_le_of_le_normalizer hYθZ' hV₀θZ'
        _ = U ⊔ θZ' := by rw [Subgroup.commutator_comm Y V₀]
    have h1 : ⁅⁅Z', V₀⁆, Z'⁆ ≤ θZ' := (Subgroup.commutator_mono hA le_rfl).trans hUθ
    have h2 : ⁅⁅V₀, Z'⁆, Z'⁆ ≤ θZ' := by rw [Subgroup.commutator_comm V₀ Z']; exact h1
    have h3 := three_subgroups_mod (X := Z') (Y := V₀) (Z := Z') (N := θZ')
      (le_normalizer_theta Z') hV₀θZ' (le_normalizer_theta Z') h1 h2
    rwa [commutator_self_eq_of_isPerfect hZ'p] at h3
  obtain ⟨a, haB, ha1⟩ := h.exists_ne_one
  obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_F
    h.a₀_mem h.a₀_ne (h.B_le_A haB) ha1 h.mem_L (h.B_le_C haB)
  have hZ'Ka : Z' ≤ K := hZ'K a haB ha1 K hK hLK
  have hYK : Y ≤ K := hYZ'.trans hZ'Ka
  have hCBa : CB ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
  have hV₀K : V₀ ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_isPerfect_le_of_mem_thetaComponentsIn hK hYK hYp hY1
      (inf_le_right.trans hCBa) hV₀sol hYV₀
  have hB3' := h.commutator_theta_le_of_not_lt h45 hZ' hZ'K haB ha1 hK hLK
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  have hZ'θK : Z' ≤ Subgroup.normalizer (θK : Set G) := hZ'Ka.trans (le_normalizer_theta K)
  have hV₀θK : V₀ ≤ Subgroup.normalizer (θK : Set G) :=
    hV₀K.trans (normalizer_le_normalizer_theta K)
  have h1 : ⁅⁅Z', V₀⁆, Z'⁆ ≤ θK := (Subgroup.commutator_mono hZ'V₀ le_rfl).trans hB3'
  have h2 : ⁅⁅V₀, Z'⁆, Z'⁆ ≤ θK := by rw [Subgroup.commutator_comm V₀ Z']; exact h1
  have h3 := three_subgroups_mod (X := Z') (Y := V₀) (Z := Z') (N := θK) hZ'θK hV₀θK hZ'θK h1 h2
  rw [commutator_self_eq_of_isPerfect hZ'p] at h3
  have hθKa :
      θK ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
    rw [hθK, theta_eq_inf_of_mem_thetaComponentsAt hK]
    exact inf_le_right
  have hUa : U ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
    calc U ≤ ⁅V₀, Z'⁆ := Subgroup.commutator_mono le_rfl hYZ'
      _ = ⁅Z', V₀⁆ := Subgroup.commutator_comm _ _
      _ ≤ θK := h3
      _ ≤ _ := hθKa
  have hAV₀ : A ≤ Subgroup.normalizer (V₀ : Set G) :=
    (le_inf hAW (h.A_le_centralizer_B.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := fun e he =>
    Source.mem_normalizer_commutator (hAV₀ he) (hAY he)
  exact hU (commutator_eq_bot_of_commutator_zpowers_eq hYp hYb hYV₀
    (h.centralizes a haB ha1 U hU2 hUa hAU))

end Ctx65B

theorem rank3II_6_5Used_one_of_centralizes (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hG : PartTwoStanding G) {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAE : A ∈ partTwoE G) {L : Subgroup G} (hL : L ∈ thetaComponentFamily 3 A) {B : Subgroup G}
    (hBab : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBAL : B ≤ A ⊓ thetaQuotCentralizer L)
    {b : G} (hbA : b ∈ A) (hbL : b ∉ thetaQuotCentralizer L)
    (hbθ : ∀ x ∈ B, x ≠ 1 → ∀ T : Subgroup G, IsPGroup 2 T →
      T ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {x}) →
      A ≤ Subgroup.normalizer (T : Set G) → T ≤ Subgroup.centralizer {b}) :
    ∃ b' ∈ B, b' ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b',
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b'}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b'})) < K := by
  by_contra hcon
  have hno : ∀ x ∈ B, x ≠ 1 → ∀ K ∈ thetaComponentsAt 3 x,
      ¬ inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {x}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {x})) < K :=
    fun x hx hx1 K hK hlt => hcon ⟨x, hx, hx1, K, hK, hlt⟩
  obtain ⟨a₀, ha₀A, ha₀1, hLa₀⟩ := mem_thetaComponentFamily_iff.mp hL
  have h : Ctx65B G A L B a₀ b :=
    ⟨hG, hAF, hAE, ha₀A, ha₀1, hLa₀, hBab, hB9, hBAL, hbA, hbL, hbθ, hno⟩
  obtain ⟨Z', hZ', hZZ', hAZ', hZ'K⟩ := h.exists_Z' h45 h48
  obtain ⟨R, Y, hR1, hR2, hAR, hYp, hY1, hYZ', hZ'Y, hYR, hAY, hYb⟩ :=
    h.exists_R_Y h45 h48 hZ' hZZ' hAZ' hZ'K
  exact h.false_of_R_Y h45 h48 hZ' hZ'K hR1 hR2 hAR hYp hY1 hYZ' hZ'Y hYR hAY hYb

end CFSG.RankThree.PartTwo.Sec6.Wales65B
