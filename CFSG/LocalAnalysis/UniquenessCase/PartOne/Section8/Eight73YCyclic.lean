module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Char
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight67Cases23
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.CharacteristicNormalizer
import CFSG.GroupTheory.TwoReflections
import CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel
import CFSG.GroupTheory.PGroup.OmegaComm
import CFSG.RankThree.PartOne.S12.Sec159Hom
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.FrattiniSylow
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2)

variable {G : Type} [Group G] [Finite G]

theorem commute_of_mem_centralizerBar {P Q L : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hQL : Q ≤ L) (hQP : Q ≤ P) {q c : G} (hq : q ∈ Q)
    (hc : c ∈ centralizerBar P L) : q * c = c * q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcP : c ∈ P := (mem_centralizerBar_iff.mp hc).1
  have hqP : q ∈ P := hQP hq
  have hcommP : ⁅c, q⁆ ∈ P :=
    Subgroup.commutator_le_self P (P.commutator_mem_commutator hcP hqP)
  have hcommO : ⁅c, q⁆ ∈ CFSG.Open.pCoreOf 2 L :=
    (mem_centralizerBar_iff.mp hc).2 q (hQL hq)
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L
  have hbot : P ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne p 2 hp2 P (CFSG.Open.pCoreOf 2 L) hP hO2).eq_bot
  have hmem : ⁅c, q⁆ ∈ P ⊓ CFSG.Open.pCoreOf 2 L := ⟨hcommP, hcommO⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm

theorem exists_mul_of_le_sup_centralizerBar {P Q L : Subgroup G} (hQL : Q ≤ L) (hQP : Q ≤ P)
    (hPQ : P ≤ Q ⊔ centralizerBar P L) {y : G} (hy : y ∈ P) :
    ∃ u ∈ Q, ∃ v ∈ centralizerBar P L, y = u * v := by
  have hQN : Q ≤ normalizer ((centralizerBar P L : Subgroup G) : Set G) := by
    intro q hq
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxP, hxL⟩ := mem_centralizerBar_iff.mp hx
    have hqO : q ∈ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L
        (Subgroup.le_normalizer (hQL hq))
    refine mem_centralizerBar_iff.mpr
      ⟨P.mul_mem (P.mul_mem (hQP hq) hxP) (P.inv_mem (hQP hq)), fun z hz => ?_⟩
    have hconj : ⁅q * x * q⁻¹, z⁆ = q * ⁅x, q⁻¹ * z * q⁆ * q⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp hqO _).1
      (hxL _ (L.mul_mem (L.mul_mem (L.inv_mem (hQL hq)) hz) (hQL hq)))
  have hmem : y ∈ ((Q ⊔ centralizerBar P L : Subgroup G) : Set G) := hPQ hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q _ hQN] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hmem
  exact ⟨u, hu, v, hv, huv.symm⟩

theorem isCyclic_centralizerBar_of_pRank_le_three {P Q L : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQL : Q ≤ L) (hQP : Q ≤ P) (hP : IsPGroup p P)
    (hQ2 : 2 ≤ CFSG.Open.pRank p Q) (hP3 : CFSG.Open.pRank p P ≤ 3)
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) : IsCyclic (centralizerBar P L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let C : Subgroup G := centralizerBar P L
  have hQPp : IsPGroup p Q := hP.to_le hQP
  have hQinfC : Q ⊓ C = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s213_inf_centralizerBar_eq_bot_of_prime
      (P := P) hp hp2 hQL hQPp hZ
  by_contra hnc
  have hCp : IsPGroup p C := hP.to_le (centralizerBar_le P L)
  haveI : Fact (IsPGroup p ↥C) := ⟨hCp⟩
  obtain ⟨S, -, hScard, hSelem⟩ :=
    CFSG.lemma_4_5_a (R := ↥C) (p := p) hp2 hnc
  let F : Subgroup G := S.map C.subtype
  have hFC : F ≤ C := Subgroup.map_subtype_le S
  have hFcard : Nat.card F = p ^ 2 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hScard]
  have hFel : IsElemAbelian p F :=
    CFSG.SectionRank.isElemAbelian_map
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSelem) C.subtype
  obtain ⟨E, hEQ, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt Q
  have hEFbot : E ⊓ F = ⊥ := by
    refine le_bot_iff.mp ?_
    calc E ⊓ F ≤ Q ⊓ C := inf_le_inf hEQ hFC
      _ = ⊥ := hQinfC
  have hEFcomm : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e :=
    fun e he f hf => commute_of_mem_centralizerBar hp hp2 hP hQL hQP (hEQ he) (hFC hf)
  have hcard : Nat.card ↥(E ⊔ F) = p ^ (CFSG.Open.pRank p Q + 2) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E F hEFcomm).1
    rw [hEFbot, Subgroup.card_bot, mul_one, hEcard, hFcard, ← pow_add] at h
    exact h
  have h4 : CFSG.Open.pRank p Q + 2 ≤ CFSG.Open.pRank p P :=
    CFSG.SectionRank.le_pRank hp.one_lt
      (sup_le (hEQ.trans hQP) (hFC.trans (centralizerBar_le P L)))
      (hEel.sup_of_commute hFel hEFcomm) hcard
  omega

theorem inf_eq_bot_of_isCyclic_of_rankThreeGamma_le {M Q Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hYp : IsPGroup p Y) (hYc : IsCyclic Y) (hΓ : rankThreeGamma 1 p Q ≤ M)
    (hYN : ¬ normalizer (Y : Set G) ≤ M) : Y ⊓ Q = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hYne : Y ≠ ⊥ := by
    intro hbot
    exact hne (by rw [hbot, bot_inf_eq])
  have hYdvd : p ∣ Nat.card Y := by
    rcases hYp.card_eq_or_dvd with h1 | h
    · exact absurd (Subgroup.card_eq_one.mp h1) hYne
    · exact h
  have hKp : IsPGroup p ↥(Y ⊓ Q) := hYp.to_le inf_le_left
  have hKdvd : p ∣ Nat.card ↥(Y ⊓ Q) := by
    rcases hKp.card_eq_or_dvd with h1 | h
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact h
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Y ⊓ Q)) p hKdvd
  let w : G := z
  have hwY : w ∈ Y := z.2.1
  have hwQ : w ∈ Q := z.2.2
  have hword : orderOf w = p := by
    rw [show w = ((z : ↥(Y ⊓ Q)) : G) from rfl, Subgroup.orderOf_coe, hzord]
  have hwp : w ^ p = 1 := by rw [← hword]; exact pow_orderOf_eq_one w
  let Ω : Subgroup G := CFSG.RankThree.PartOne.omegaOne p Y
  have hΩleY : Ω ≤ Y := CFSG.RankThree.PartOne.CTP.omegaOne_le (H := G) (p := p) Y
  have hwΩ : w ∈ Ω := Subgroup.subset_closure ⟨hwY, hwp⟩
  let ΩY : Subgroup ↥Y := CFSG.omega₁ (G := ↥Y) (p := p)
  have hΩY_top : ΩY = CFSG.RankThree.PartOne.omegaOne p (⊤ : Subgroup ↥Y) := by
    ext x
    simp [ΩY, CFSG.omega₁, CFSG.omega, CFSG.RankThree.PartOne.omegaOne]
  have hmap : ΩY.map Y.subtype = Ω := by
    rw [hΩY_top]
    rw [CFSG.RankThree.PartOne.Sec9B.map_omegaOne Y.subtype_injective p (⊤ : Subgroup ↥Y)]
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hΩcard : Nat.card Ω = p := by
    rw [← hmap, Subgroup.card_map_of_injective Y.subtype_injective,
      CFSG.card_omega₁_of_isCyclic, Nat.gcd_eq_right hYdvd]
  have hwΩQ : w ∈ Ω ⊓ Q := ⟨hwΩ, hwQ⟩
  have hzpowle : Subgroup.zpowers w ≤ Ω ⊓ Q := Subgroup.zpowers_le.mpr hwΩQ
  have hcardz : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hword]
  have hcard_inf : Nat.card ↥(Ω ⊓ Q) = p := by
    have hle : Nat.card ↥(Ω ⊓ Q) ≤ Nat.card Ω :=
      Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left)
    have hge : Nat.card Ω ≤ Nat.card ↥(Ω ⊓ Q) := by
      calc Nat.card Ω = Nat.card (Subgroup.zpowers w) := by rw [hΩcard, hcardz]
        _ ≤ Nat.card ↥(Ω ⊓ Q) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hzpowle)
            (Subgroup.inclusion_injective hzpowle)
    omega
  have hΩQ : Ω ≤ Q := by
    have heq : Ω ⊓ Q = Ω := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    intro x hx
    exact (heq ▸ hx).2
  have hΩel : IsElemAbelian p Ω := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (by
        haveI : IsCyclic ↥Ω := isCyclic_of_prime_card hΩcard
        letI : CommGroup ↥Ω := IsCyclic.commGroup
        exact congrArg Subtype.val (mul_comm (⟨a, a.2⟩ : ↥Ω) ⟨b, b.2⟩))
    · haveI : IsCyclic ↥Ω := isCyclic_of_prime_card hΩcard
      have h := pow_card_eq_one' (G := ↥Ω) (x := ⟨x, hx⟩)
      rw [hΩcard] at h
      simpa using congrArg Subtype.val h
  have hΩrank : 1 ≤ CFSG.Open.pRank p Ω :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hΩel (by rw [hΩcard]; norm_num)
  have hNΩ : normalizer (Y : Set G) ≤ normalizer (Ω : Set G) :=
    CFSG.RankThree.PartOne.Sec159Cfg.normalizer_le_normalizer_omegaOne (q := p) (K := Y)
  have hNΩ_le_Γ : normalizer (Ω : Set G) ≤ rankThreeGamma 1 p Q :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hΩQ hΩrank
  exact hYN ((hNΩ.trans hNΩ_le_Γ).trans hΓ)

theorem isCyclic_of_maximal_of_eight73Y {D : Data G} (h63 : UC6.R6_3 D) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L P Q Y : Subgroup G} (hP : IsPGroup p P) (hQL : Q ≤ L) (hQP : Q ≤ P)
    (hQexp : ∀ x ∈ Q, x ^ p = 1) (hQcard : p ^ 3 ∣ Nat.card Q)
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hPQ : P ≤ Q ⊔ centralizerBar P L)
    (hcyc : IsCyclic (centralizerBar P L)) (hQM : Q ≤ D.M) (hΓ : rankThreeGamma 1 p Q ≤ D.M)
    (hYP : Y ≤ P) (hYN : ¬ normalizer (Y : Set G) ≤ D.M)
    (hmax : ∀ Z : Subgroup G, Y < Z → Z ≤ D.M → IsPGroup p Z →
      normalizer (Z : Set G) ≤ D.M) :
    IsCyclic Y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let C : Subgroup G := centralizerBar P L
  have hCP : C ≤ P := centralizerBar_le P L
  have hcommQC : ∀ q ∈ Q, ∀ c ∈ C, q * c = c * q :=
    fun q hq c hc => commute_of_mem_centralizerBar hp hp2 hP hQL hQP hq hc
  have hP_eq : P = Q ⊔ C := le_antisymm hPQ (sup_le hQP hCP)
  haveI : IsCyclic ↥C := hcyc
  letI : CommGroup ↥C := IsCyclic.commGroup
  have hCcomm : ∀ c1 ∈ C, ∀ c2 ∈ C, c1 * c2 = c2 * c1 := by
    intro c1 h1 c2 h2
    exact congrArg Subtype.val (mul_comm (⟨c1, h1⟩ : ↥C) ⟨c2, h2⟩)
  have hC_CQ : C ≤ Subgroup.centralizer (Q : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hcommQC q hq c hc
  have hC_CC : C ≤ Subgroup.centralizer (C : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro c' hc'
    exact (hCcomm c hc c' hc').symm
  have hC_CP : C ≤ Subgroup.centralizer (P : Set G) := by
    rw [hP_eq, CFSG.centralizer_sup_eq]
    intro x hx
    exact ⟨hC_CQ hx, hC_CC hx⟩
  have hPPQ : ⁅P, P⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨q, hq, c, hc, rfl⟩ :=
      exists_mul_of_le_sup_centralizerBar hQL hQP hPQ hx
    obtain ⟨q', hq', c', hc', rfl⟩ :=
      exists_mul_of_le_sup_centralizerBar hQL hQP hPQ hy
    have hcc : ⁅c, c'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hCcomm c hc c' hc')
    have hmul : ⁅q * c, q' * c'⁆ = ⁅q, q'⁆ * ⁅c, c'⁆ :=
      CFSG.GroupTheory.commutatorElement_mul_of_commute (A := Q) (B := C)
        hcommQC hq hq' hc hc'
    rw [hmul, hcc, mul_one]
    exact Subgroup.commutator_le_self Q (Subgroup.commutator_mem_commutator hq hq')
  by_cases hYcyc : IsCyclic Y
  · exact hYcyc
  by_cases hYab : IsMulCommutative ↥Y
  · have hYp : IsPGroup p Y := hP.to_le hYP
    let A : Subgroup G := CFSG.RankThree.PartOne.omegaOne p Y
    have hAleY : A ≤ Y := CFSG.RankThree.PartOne.CTP.omegaOne_le (H := G) (p := p) Y
    have hYleCY : Y ≤ Subgroup.centralizer (Y : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      exact congrArg Subtype.val ((hYab.is_comm.comm ⟨y', hy'⟩ ⟨y, hy⟩))
    have hYleCA : Y ≤ Subgroup.centralizer (A : Set G) :=
      hYleCY.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAleY))
    have hAnoncyc : ¬ IsCyclic A := by
      intro hAcyc
      haveI : IsCyclic ↥A := hAcyc
      haveI : Fact (IsPGroup p ↥Y) := ⟨hYp⟩
      obtain ⟨S, -, hScard, hSelem⟩ :=
        CFSG.lemma_4_5_a (R := ↥Y) (p := p) hp2 hYcyc
      let E : Subgroup G := S.map Y.subtype
      have hEcard : Nat.card E = p ^ 2 := by
        rw [Subgroup.card_map_of_injective Y.subtype_injective, hScard]
      have hEel : IsElemAbelian p E :=
        CFSG.SectionRank.isElemAbelian_map
          ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSelem) Y.subtype
      have hEA : E ≤ A := by
        intro x hx
        exact Subgroup.subset_closure ⟨Subgroup.map_subtype_le S hx, hEel.2 x hx⟩
      have hEcyc : IsCyclic ↥E := Subgroup.isCyclic_of_le hEA
      haveI : IsElementaryAbelian p ↥E := hEel.isElementaryAbelian
      exact (CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := p) hEcard) hEcyc
    have hAQne : A ⊓ Q ≠ ⊥ := by
      intro hbot
      have hAleP : A ≤ P := hAleY.trans hYP
      have hC_NQ : C ≤ normalizer (Q : Set G) :=
        hC_CQ.trans (Subgroup.centralizer_le_normalizer (Q : Set G))
      have hPNQ : P ≤ normalizer (Q : Set G) := by
        rw [hP_eq]
        exact sup_le Subgroup.le_normalizer hC_NQ
      have hQnormP : (Q.subgroupOf P).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hPNQ
      have hAcyc : IsCyclic A :=
        isCyclic_of_le_of_sup_cyclic_of_inf_eq_bot hQP hCP hAleP hP_eq.symm hQnormP
          (show IsCyclic C from hcyc) hbot
      exact hAnoncyc hAcyc
    have hAQp : IsPGroup p ↥(A ⊓ Q) := hYp.to_le (inf_le_left.trans hAleY)
    have hAQdvd : p ∣ Nat.card ↥(A ⊓ Q) := by
      rcases hAQp.card_eq_or_dvd with h1 | h
      · exact absurd (Subgroup.card_eq_one.mp h1) hAQne
      · exact h
    obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ Q)) p hAQdvd
    let uG : G := u
    have huA : uG ∈ A := u.2.1
    have huQ : uG ∈ Q := u.2.2
    have huordG : orderOf uG = p := by
      rw [show uG = ((u : ↥(A ⊓ Q)) : G) from rfl, Subgroup.orderOf_coe, huord]
    have hCA_le_Nu : Subgroup.centralizer (A : Set G) ≤
        normalizer (Subgroup.zpowers uG : Set G) := by
      intro x hx
      have hxu : x * uG * x⁻¹ = uG := by
        have hcx : uG * x = x * uG := Subgroup.mem_centralizer_iff.mp hx uG huA
        calc x * uG * x⁻¹ = uG * x * x⁻¹ := by rw [← hcx]
          _ = uG := by group
      exact CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq hxu
    have hucard : Nat.card (Subgroup.zpowers uG) = p := by
      rw [Nat.card_zpowers, huordG]
    have huel : IsElemAbelian p (Subgroup.zpowers uG) :=
      isElemAbelian_zpowers (by rw [← huordG]; exact pow_orderOf_eq_one uG)
    have hurank : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers uG) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl huel (by rw [hucard]; norm_num)
    have hNu_le_Γ : normalizer (Subgroup.zpowers uG : Set G) ≤ rankThreeGamma 1 p Q :=
      CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
        (Subgroup.zpowers_le.mpr huQ) hurank
    have hCA_le_M : Subgroup.centralizer (A : Set G) ≤ D.M :=
      (hCA_le_Nu.trans hNu_le_Γ).trans hΓ
    let H : Subgroup G := normalizer (Y : Set G)
    let K : Subgroup G := Subgroup.centralizer (A : Set G) ⊓ H
    have hYleH : Y ≤ H := Subgroup.le_normalizer
    have hYleK : Y ≤ K := le_inf hYleCA hYleH
    have hKleM : K ≤ D.M := fun x hx => hCA_le_M hx.1
    have hAH : A ≤ H := hAleY.trans hYleH
    have hHNA : H ≤ normalizer (A : Set G) :=
      CFSG.RankThree.PartOne.Sec159Cfg.normalizer_le_normalizer_omegaOne (q := p) (K := Y)
    have hAnormH : (A.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mpr hHNA
    have hKnorm : (K.subgroupOf H).Normal := by
      have h :=
        CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel.centralizer_subgroupOf_normal
          (H := H) (C := A) hAH hAnormH
      simpa [K, Subgroup.inf_subgroupOf_right] using h
    have hYsubKp : IsPGroup p (Y.subgroupOf K) := by
      change IsPGroup p (Y.comap K.subtype)
      exact hYp.comap_subtype (K := K)
    obtain ⟨S, hS⟩ := hYsubKp.exists_le_sylow
    let SG : Subgroup G := (S : Subgroup ↥K).map K.subtype
    have hSGK : SG ≤ K := by simpa [SG] using Subgroup.map_subtype_le (S : Subgroup ↥K)
    have hSGp : IsPGroup p SG := by simpa [SG] using (S.isPGroup').map K.subtype
    have hYSG : Y ≤ SG := by
      have h1 : (Y.subgroupOf K).map K.subtype ≤ SG := Subgroup.map_mono hS
      rwa [Subgroup.map_subgroupOf_eq_of_le hYleK] at h1
    have hSG_le_Y : SG ≤ Y := by
      by_contra hnot
      have hYlt : Y < SG := lt_of_le_of_ne hYSG (by intro h; exact hnot (le_of_eq h.symm))
      have hNSG : normalizer (SG : Set G) ≤ D.M :=
        hmax SG hYlt (hSGK.trans hKleM) hSGp
      have hfr := eq_sup_normalizer_of_sylow (p := p) (K := K) (C := H) inf_le_right hKnorm S
      have hHleM : H ≤ D.M := by
        rw [hfr]
        exact sup_le hKleM (inf_le_left.trans hNSG)
      exact hYN hHleM
    have hSG_eq_Y : SG = Y := le_antisymm hSG_le_Y hYSG
    have hYsubK_eq_S : Y.subgroupOf K = (S : Subgroup ↥K) := by
      calc Y.subgroupOf K = SG.subgroupOf K := by rw [hSG_eq_Y]
        _ = (S.map K.subtype).subgroupOf K := rfl
        _ = S := by
            rw [← Subgroup.comap_subtype]
            exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective S
    let Dc : Subgroup G := P ⊓ Subgroup.centralizer (A : Set G)
    have hDcp : IsPGroup p Dc := hP.to_le inf_le_left
    have hYleDc : Y ≤ Dc := le_inf hYP hYleCA
    let ND : Subgroup G := Dc ⊓ H
    have hNDp : IsPGroup p ND := hDcp.to_le inf_le_left
    have hYleND : Y ≤ ND := le_inf hYleDc hYleH
    have hNDleK : ND ≤ K := fun x hx => ⟨hx.1.2, hx.2⟩
    have hNDsubKp : IsPGroup p (ND.subgroupOf K) := by
      change IsPGroup p (ND.comap K.subtype)
      exact hNDp.comap_subtype (K := K)
    have hS_le_NDsub : (S : Subgroup ↥K) ≤ ND.subgroupOf K := by
      rw [← hYsubK_eq_S]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hYleND (Subgroup.mem_subgroupOf.mp hx))
    have hNDsub_eq_S : ND.subgroupOf K = (S : Subgroup ↥K) :=
      S.is_maximal' hNDsubKp hS_le_NDsub
    have hND_eq_Y : ND = Y := by
      have hsub : ND.subgroupOf K = Y.subgroupOf K := by
        rw [hNDsub_eq_S, hYsubK_eq_S]
      have hinf : ND ⊓ K = Y ⊓ K := Subgroup.subgroupOf_inj.mp hsub
      rwa [inf_eq_left.mpr hNDleK, inf_eq_left.mpr hYleK] at hinf
    have hDc_eq_Y : Dc = Y := by
      by_contra hne
      have hlt : Y < Dc := lt_of_le_of_ne hYleDc (by intro h; exact hne h.symm)
      have hgrowth := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := p) hDcp hlt
      rw [show Dc ⊓ H = ND from rfl, hND_eq_Y] at hgrowth
      exact lt_irrefl Y hgrowth
    have hC_le_Y : C ≤ Y := by
      have hAleP : A ≤ P := hAleY.trans hYP
      have hC_le_Dc : C ≤ Dc :=
        le_inf hCP (hC_CP.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAleP)))
      rwa [hDc_eq_Y] at hC_le_Dc
    let B : Subgroup G := Y ⊓ Q
    have hB_le_Y : B ≤ Y := inf_le_left
    have hB_le_Q : B ≤ Q := inf_le_right
    have hY_eq_BC : Y = B ⊔ C := by
      refine le_antisymm ?_ (sup_le hB_le_Y hC_le_Y)
      intro y hy
      obtain ⟨q, hq, c, hc, hyq⟩ :=
        exists_mul_of_le_sup_centralizerBar hQL hQP hPQ (hYP hy)
      have hcY : c ∈ Y := hC_le_Y hc
      have hqY : q ∈ Y := by
        have hq_eq : q = y * c⁻¹ := by rw [hyq]; group
        rw [hq_eq]
        exact Y.mul_mem hy (Y.inv_mem hcY)
      rw [hyq]
      exact Subgroup.mul_mem_sup ⟨hqY, hq⟩ hc
    have hBself : Q ⊓ Subgroup.centralizer (B : Set G) = B := by
      refine le_antisymm ?_ ?_
      · intro x hx
        obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
        have hxC_C : x ∈ Subgroup.centralizer (C : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          exact (hcommQC x hxQ c hc).symm
        have hxCY : x ∈ Subgroup.centralizer (Y : Set G) := by
          rw [hY_eq_BC, CFSG.centralizer_sup_eq]
          exact ⟨hxC, hxC_C⟩
        have hxCA : x ∈ Subgroup.centralizer (A : Set G) :=
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAleY) hxCY
        have hxY : x ∈ Y := by
          have hxDc : x ∈ Dc := ⟨hQP hxQ, hxCA⟩
          rwa [hDc_eq_Y] at hxDc
        exact Subgroup.mem_inf.mpr ⟨hxY, hxQ⟩
      · intro x hx
        refine Subgroup.mem_inf.mpr ⟨hB_le_Q hx, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (congrArg Subtype.val
          ((hYab.is_comm.comm ⟨x, hB_le_Y hx⟩ ⟨b, hB_le_Y hb⟩))).symm
    have hBexp : ∀ x ∈ B, x ^ p = 1 := fun x hx => hQexp x (hB_le_Q hx)
    have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      intro x hx y hy
      exact congrArg Subtype.val ((hYab.is_comm.comm ⟨x, hB_le_Y hx⟩ ⟨y, hB_le_Y hy⟩))
    have hBel : IsElemAbelian p B :=
      ⟨⟨⟨fun a b => Subtype.ext (hBcomm a a.2 b b.2)⟩⟩, hBexp⟩
    have hBp : IsPGroup p B := hP.to_le (hB_le_Q.trans hQP)
    have hQp : IsPGroup p Q := hP.to_le hQP
    have hQcard_ge : p ^ 3 ≤ Nat.card Q := Nat.le_of_dvd Nat.card_pos hQcard
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hQne : Q ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hQcard_ge
      have h8 : 8 ≤ p ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
      omega
    have hBne : B ≠ ⊥ := by
      intro hBbot
      have hQbot : Q = ⊥ := by
        have hcentTop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
          rw [eq_top_iff]
          intro x _
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy1 : y = 1 := by simpa using hy
          simp [hy1]
        have h := hBself
        rw [hBbot, hcentTop, inf_top_eq] at h
        exact h
      exact hQne hQbot
    have hBcard_ge : p ^ 2 ≤ Nat.card B := by
      by_contra hlt
      have hlt' : Nat.card B < p ^ 2 := Nat.lt_of_not_le hlt
      obtain ⟨n, hn⟩ := hBp.exists_card_eq
      have hn0 : 0 < n := by
        by_contra h0
        have hnz : n = 0 := by omega
        rw [hnz, pow_zero] at hn
        exact hBne (Subgroup.card_eq_one.mp hn)
      have hnlt : n < 2 :=
        (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by rwa [hn] at hlt')
      have hn1 : n = 1 := by omega
      have hBcardp : Nat.card B = p := by rw [hn, hn1, pow_one]
      haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
      let ZQ : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
      have hZQ_ne : ZQ ≠ ⊥ := by
        intro hZQbot
        have hcenterbot : Subgroup.center ↥Q = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥Q) Q.subtype_injective).mp
            hZQbot
        exact (Subgroup.nontrivial_iff_ne_bot _).mp hQp.center_nontrivial hcenterbot
      have hZQ_le_B : ZQ ≤ B := by
        intro z hz
        have hzQ : z ∈ Q := Subgroup.map_subtype_le _ hz
        have hzC : z ∈ Subgroup.centralizer (B : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hz
          exact congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hz0 ⟨b, hB_le_Q hb⟩)
        exact hBself ▸ Subgroup.mem_inf.mpr ⟨hzQ, hzC⟩
      have hZQdvd : Nat.card ZQ ∣ p := by
        rw [← hBcardp]
        exact Subgroup.card_dvd_of_le hZQ_le_B
      have hZQcard_gt : 1 < Nat.card ZQ := by
        haveI : Nontrivial ZQ := (Subgroup.nontrivial_iff_ne_bot ZQ).mpr hZQ_ne
        exact Finite.one_lt_card
      have hZQcard : Nat.card ZQ = p := by
        rcases hp.eq_one_or_self_of_dvd (Nat.card ZQ) hZQdvd with h1 | hp'
        · omega
        · exact hp'
      have hZQ_eq_B : ZQ = B :=
        Subgroup.eq_of_le_of_card_ge hZQ_le_B (by rw [hZQcard, hBcardp])
      have hQ_eq_ZQ : Q = ZQ := by
        have hZQ_cent : Q ≤ Subgroup.centralizer (ZQ : Set G) := by
          intro q hq
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hz
          exact (congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hz0 ⟨q, hq⟩)).symm
        have hQinf : Q ⊓ Subgroup.centralizer (ZQ : Set G) = Q := inf_eq_left.mpr hZQ_cent
        have h := hBself
        rw [← hZQ_eq_B] at h
        exact hQinf.symm.trans h
      have hQcardp : Nat.card Q = p := by rw [hQ_eq_ZQ, hZQcard]
      rw [hQcardp] at hQcard_ge
      have hp_lt_p3 : p < p ^ 3 := by
        have h := (Nat.pow_lt_pow_iff_right hp.one_lt).mpr (by norm_num : 1 < 3)
        simpa using h
      omega
    have hBdvd : p ^ 2 ∣ Nat.card B := by
      obtain ⟨n, hn⟩ := hBp.exists_card_eq
      have h2n : 2 ≤ n := by
        have h : p ^ 2 ≤ p ^ n := by rwa [hn] at hBcard_ge
        exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
      rw [hn]
      exact pow_dvd_pow p h2n
    haveI : IsElementaryAbelian p ↥B := hBel.isElementaryAbelian
    obtain ⟨E, hEB, hEclass, hEcard⟩ :=
      CFSG.RankThree.PartOne.CTP.exists_elementaryAbelian_sq_le (p := p) (A := B) hBdvd
    haveI : IsElementaryAbelian p ↥E := hEclass
    have hEel : IsElemAbelian p E := CFSG.Open.isElemAbelian_of_isElementaryAbelian
    have hEBQ : E ≤ Q := hEB.trans hB_le_Q
    have hEM : E ≤ D.M := hEBQ.trans hQM
    have hΓE : rankThreeGamma 1 p E ≤ D.M :=
      (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono hEBQ).trans hΓ
    have hUM : CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax D.M E :=
      h63 p hp hp2 E hEM hEel hEcard hΓE
    have hInU : UC6.InU D.M E := inU_of_uniqueMax D.maxLocal hUM
    have hEnormY : (E.subgroupOf Y).Normal :=
      Subgroup.normal_of_isMulCommutative (E.subgroupOf Y)
    have hEsub : CFSG.Open.IsSubnormal E Y :=
      CFSG.Open.IsSubnormal.step (hEB.trans hB_le_Y) hEnormY (CFSG.Open.IsSubnormal.refl Y)
    exact (false_of_subnormal_InU_of_not_normalizer_le
      (UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal) hEsub hInU hYN).elim
  · have hYp : IsPGroup p Y := hP.to_le hYP
    have hder_ne : ⁅Y, Y⁆ ≠ ⊥ := by
      intro hbot
      exact hYab ((Subgroup.commutator_self_eq_bot_iff).mp hbot)
    have hder_le_Q : ⁅Y, Y⁆ ≤ Q := (Subgroup.commutator_mono hYP hYP).trans hPPQ
    have hder_le_Y : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le_self Y
    have hderp : IsPGroup p ↥⁅Y, Y⁆ := hP.to_le (hder_le_Q.trans hQP)
    have hderdvd : p ∣ Nat.card ↥⁅Y, Y⁆ := by
      rcases hderp.card_eq_or_dvd with h1 | h
      · exact absurd (Subgroup.card_eq_one.mp h1) hder_ne
      · exact h
    have hderrank : 1 ≤ CFSG.Open.pRank p ⁅Y, Y⁆ := by
      obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥⁅Y, Y⁆) p hderdvd
      have hzpowG : (z : G) ^ p = 1 := by
        have h := pow_orderOf_eq_one z
        rw [hzord] at h
        simpa using congrArg Subtype.val h
      have hzle : Subgroup.zpowers (z : G) ≤ ⁅Y, Y⁆ := Subgroup.zpowers_le.mpr z.2
      have hcardz : Nat.card (Subgroup.zpowers (z : G)) = p := by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzord]
      exact CFSG.SectionRank.le_pRank hp.one_lt hzle (isElemAbelian_zpowers hzpowG)
        (by rw [hcardz]; norm_num)
    have hderchar : ((⁅Y, Y⁆).subgroupOf Y).Characteristic := by
      have hmap1 : ((⁅Y, Y⁆).subgroupOf Y).map Y.subtype = ⁅Y, Y⁆ :=
        Subgroup.map_subgroupOf_eq_of_le hder_le_Y
      have hmap2 : ((⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆).map Y.subtype) = ⁅Y, Y⁆ := by
        have h := CFSG.commutator_subgroupOf_map_eq Y Y Y le_rfl le_rfl
        simpa using h
      have hEq : (⁅Y, Y⁆).subgroupOf Y = ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ :=
        Subgroup.map_injective Y.subtype_injective (hmap1.trans hmap2.symm)
      rw [hEq]
      infer_instance
    have hNY : normalizer (Y : Set G) ≤
        normalizer (((⁅Y, Y⁆ : Subgroup G) : Set G)) :=
      CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic hder_le_Y hderchar
    have hNder : normalizer (((⁅Y, Y⁆ : Subgroup G) : Set G)) ≤ rankThreeGamma 1 p Q :=
      CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hder_le_Q hderrank
    exact (hYN ((hNY.trans hNder).trans hΓ)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
