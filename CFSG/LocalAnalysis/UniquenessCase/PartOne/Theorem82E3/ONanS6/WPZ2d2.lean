module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPQ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPQ3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2d
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem z2d2_card_Q_wPZ2d2 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card ↥(P ⊓ c.L) = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPL : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ c.L) c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  rw [hPL.card_eq, pl7_factorization_card_L_wPL7 c hON]

theorem z2d2_card_center_Q_wPZ2d2
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card (Subgroup.center ↥(P ⊓ c.L)) = 3 := by
  have hcardmap : Nat.card (Subgroup.center ↥(P ⊓ c.L)) =
      Nat.card ↥((Subgroup.center ↥(P ⊓ c.L)).map (P ⊓ c.L).subtype) :=
    (Subgroup.card_map_of_injective (P ⊓ c.L).subtype_injective).symm
  rw [hcardmap, pl7_center_map_eq_wPL7]
  simpa [zSub] using c.card_inf_centralizer_of_onan hON hP

theorem z2d2_exp_Q_wPZ2d2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∀ x ∈ P ⊓ c.L, x ^ 3 = 1 :=
  c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP

theorem z2d2_commutator_Q_wPZ2d2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ⁅P ⊓ c.L, P ⊓ c.L⁆ ≤ zSub P c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let QL : Subgroup ↥c.L := (P ⊓ c.L).subgroupOf c.L
  have hQ3 : IsPGroup 3 (P ⊓ c.L : Subgroup G) := hP.isPGroup.to_le inf_le_left
  have hQL3 : IsPGroup 3 QL := hQ3.comap_subtype
  have hQbar3 : IsPGroup 3 (QL.map π) := hQL3.map π
  obtain ⟨S, hSle⟩ := IsPGroup.exists_le_sylow hQbar3
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar :=
    isHatON_lbar_of_onan_wPH2 c hON
  have hcommS := (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds
    c.Lbar hHat S).2.2.1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxL : x ∈ c.L := hx.2
  have hyL : y ∈ c.L := hy.2
  have hxQL : (⟨x, hxL⟩ : ↥c.L) ∈ QL :=
    Subgroup.mem_subgroupOf.mpr hx
  have hyQL : (⟨y, hyL⟩ : ↥c.L) ∈ QL :=
    Subgroup.mem_subgroupOf.mpr hy
  have hxS : π ⟨x, hxL⟩ ∈ (S : Subgroup c.Lbar) :=
    hSle (Subgroup.mem_map_of_mem π hxQL)
  have hyS : π ⟨y, hyL⟩ ∈ (S : Subgroup c.Lbar) :=
    hSle (Subgroup.mem_map_of_mem π hyQL)
  have hcommSub : (⁅(⟨x, hxL⟩ : ↥c.L), (⟨y, hyL⟩ : ↥c.L)⁆) ∈
      (Subgroup.center c.Lbar).comap π := by
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hcommS _ hxS _ hyS
  have hmemCP : ⁅x, y⁆ ∈ centerPreimage_of_onan c := by
    refine Subgroup.mem_map.mpr ⟨⁅(⟨x, hxL⟩ : ↥c.L), (⟨y, hyL⟩ : ↥c.L)⁆, hcommSub, ?_⟩
    simp [commutatorElement_def]
  have hxyP : ⁅x, y⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx.1 hy.1) (P.inv_mem hx.1)) (P.inv_mem hy.1)
  exact inf_centerPreimage_sylow_le_zSub_of_onan c hON hP ⟨hmemCP, hxyP⟩

theorem z2d2_e_not_center_Q_wPZ2d2 (c : Ctx82E3 D)
    {P : Subgroup G} {e : G} (he : e ∈ P ⊓ c.L) (heZ : e ∉ zSub P c.L) :
    (⟨e, he⟩ : ↥(P ⊓ c.L)) ∉ Subgroup.center ↥(P ⊓ c.L) := by
  intro hcenter
  have hmem : e ∈ (Subgroup.center ↥(P ⊓ c.L)).map (P ⊓ c.L).subtype :=
    Subgroup.mem_map.mpr ⟨⟨e, he⟩, hcenter, rfl⟩
  rw [pl7_center_map_eq_wPL7] at hmem
  exact heZ (by simpa [zSub] using hmem)

theorem z2d2_card_centralizer_Q_wPZ2d2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {e : G} (he : e ∈ P ⊓ c.L) (heZ : e ∉ zSub P c.L) :
    Nat.card ↥((P ⊓ c.L) ⊓ Subgroup.centralizer ({e} : Set G)) = 81 := by
  classical
  let Q : Subgroup G := P ⊓ c.L
  have hcomm : ∀ a b : ↥Q, ⁅a, b⁆ ∈ Subgroup.center ↥Q := by
    intro a b
    have hamb : ⁅(a : G), (b : G)⁆ ∈ zSub P c.L :=
      z2d2_commutator_Q_wPZ2d2 c hON hP (Subgroup.commutator_mem_commutator a.2 b.2)
    rw [show zSub P c.L = (Subgroup.center ↥Q).map Q.subtype from
      (pl7_center_map_eq_wPL7 Q).symm] at hamb
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hamb
    have hEq : ⁅a, b⁆ = z := by
      apply Subtype.ext
      simpa [commutatorElement_def] using hzeq.symm
    rwa [hEq]
  have hcard : Nat.card ↥Q = 3 ^ 5 := z2d2_card_Q_wPZ2d2 c hON hP
  have hZ : Nat.card (Subgroup.center ↥Q) = 3 := z2d2_card_center_Q_wPZ2d2 c hON hP
  have hg : (⟨e, he⟩ : ↥Q) ∉ Subgroup.center ↥Q := z2d2_e_not_center_Q_wPZ2d2 c he heZ
  have hcent := pl7_card_centralizer_of_card_three_pow_five_wPL7 hcard hZ hcomm hg
  have hmap : (Subgroup.centralizer ({⟨e, he⟩} : Set ↥Q)).map Q.subtype =
      Q ⊓ Subgroup.centralizer ({e} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))
    · rintro ⟨hxQ, hxC⟩
      refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC))
  have hcardmap : Nat.card ↥((Subgroup.centralizer ({⟨e, he⟩} : Set ↥Q)).map Q.subtype) =
      Nat.card ↥(Subgroup.centralizer ({⟨e, he⟩} : Set ↥Q)) :=
    Subgroup.card_map_of_injective Q.subtype_injective
  rw [← hmap, hcardmap]
  exact hcent

theorem exists_E27_through (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {e : G} (he : e ∈ P ⊓ c.L) (heZ : e ∉ zSub P c.L) :
    ∃ A : Subgroup G, A ≤ P ⊓ c.L ∧ e ∈ A ∧ zSub P c.L ≤ A ∧
      CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 := by
  classical
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := zSub P c.L
  let B : Subgroup G := Subgroup.zpowers e ⊔ Z
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({e} : Set G)
  have hQcard : Nat.card ↥Q = 3 ^ 5 := z2d2_card_Q_wPZ2d2 c hON hP
  have hCcard : Nat.card ↥C = 81 := z2d2_card_centralizer_Q_wPZ2d2 c hON hP he heZ
  have heQ : e ∈ Q := he
  have hZleQ : Z ≤ Q := fun z hz => hz.1
  have hZcard : Nat.card Z = 3 := c.card_inf_centralizer_of_onan hON hP
  have hepow : e ^ 3 = 1 := z2d2_exp_Q_wPZ2d2 c hON hP e he
  have he1 : e ≠ 1 := by
    intro h
    exact heZ (by rw [h]; exact (zSub P c.L).one_mem)
  have he3 : orderOf e = 3 := by
    have hdvd : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one hepow
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) he1
    · exact h
  have heC : e ∈ C :=
    ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr (by group)⟩
  have hZleC : Z ≤ C := by
    intro z hz
    refine ⟨hZleQ hz, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 e he).symm
  have hBcard : Nat.card ↥B = 9 := by
    have hdisj : Subgroup.zpowers e ⊓ Z = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      by_contra hx1
      have hHcard : Nat.card (Subgroup.zpowers x) = 3 := by
        have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := by
          have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx.1)
          rwa [Nat.card_zpowers e, he3] at h
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exfalso
          apply hx1
          have hxord : orderOf x = 1 := by
            rw [← Nat.card_zpowers x, h]
          exact orderOf_eq_one_iff.mp hxord
        · exact h
      have hzx : Subgroup.zpowers x = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx.1)
          (by rw [hHcard, Nat.card_zpowers e, he3])
      have hxZle : Subgroup.zpowers x ≤ Z := Subgroup.zpowers_le.mpr hx.2
      exact heZ (hxZle (by rw [hzx]; exact Subgroup.mem_zpowers e))
    have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ Z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hbe : Commute e b := Subgroup.mem_centralizer_iff.mp hb.2 e he
      exact (hbe.zpow_left k).eq
    have hsupcard := CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers e) Z hcomm hdisj
    change Nat.card ↥B = 9
    rw [hsupcard, Nat.card_zpowers e, he3, hZcard]
  have hex : ∃ f : G, f ∈ C ∧ f ∉ B := by
    by_contra h
    have hCB : C ≤ B := by
      intro x hx
      by_contra hxB
      exact h ⟨x, hx, hxB⟩
    have hBC : B ≤ C := sup_le (Subgroup.zpowers_le.mpr heC) hZleC
    have hEq : C = B := le_antisymm hCB hBC
    have hcardEq : Nat.card ↥C = Nat.card ↥B := by rw [hEq]
    omega
  obtain ⟨f, hfC, hfB⟩ := hex
  have hfQ : f ∈ Q := hfC.1
  have hfpow : f ^ 3 = 1 := z2d2_exp_Q_wPZ2d2 c hON hP f hfQ
  have hf1 : f ≠ 1 := by
    intro h
    apply hfB
    rw [h]
    exact B.one_mem
  have hf3 : orderOf f = 3 := by
    have hdvd : orderOf f ∣ 3 := orderOf_dvd_of_pow_eq_one hfpow
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hf1
    · exact h
  have hfe : f * e = e * f := Subgroup.mem_centralizer_singleton_iff.mp hfC.2
  have hfZ : ∀ b ∈ Z, f * b = b * f := fun b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 f hfQ
  have hFdisj : Subgroup.zpowers f ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    have hHcard : Nat.card (Subgroup.zpowers x) = 3 := by
      have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx.1)
        rwa [Nat.card_zpowers f, hf3] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exfalso
        apply hx1
        have hxord : orderOf x = 1 := by
          rw [← Nat.card_zpowers x, h]
        exact orderOf_eq_one_iff.mp hxord
      · exact h
    have hfx : Subgroup.zpowers x = Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx.1)
        (by rw [hHcard, Nat.card_zpowers f, hf3])
    have hxBle : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.mpr hx.2
    exact hfB (hxBle (by rw [hfx]; exact Subgroup.mem_zpowers f))
  have hBcent : B ≤ Subgroup.centralizer (Subgroup.zpowers f : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc : Commute e f := hfe.symm
      exact ((hc.zpow_left m).zpow_right k).eq.symm
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc : Commute b f := (hfZ b hb).symm
      exact ((hc.zpow_right k).eq).symm
  have hEea : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers e) := by
    have h := CFSG.Open.IsElemAbelian.closure_of_commute (p := 3) (s := ({e} : Set G))
      (by
        intro a ha b hb
        rw [Set.mem_singleton_iff] at ha hb
        subst a; subst b; rfl)
      (by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst a
        exact hepow)
    simpa [Subgroup.zpowers_eq_closure] using h
  have hZea : CFSG.Open.IsElemAbelian 3 Z := by
    have hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
    have hexp : ∀ a ∈ Z, a ^ 3 = 1 := fun a ha => z2d2_exp_Q_wPZ2d2 c hON hP a ha.1
    have h := CFSG.Open.IsElemAbelian.closure_of_commute (p := 3) (s := (Z : Set G)) hcomm hexp
    simpa [Subgroup.closure_eq] using h
  have hFea : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers f) := by
    have h := CFSG.Open.IsElemAbelian.closure_of_commute (p := 3) (s := ({f} : Set G))
      (by
        intro a ha b hb
        rw [Set.mem_singleton_iff] at ha hb
        subst a; subst b; rfl)
      (by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst a
        exact hfpow)
    simpa [Subgroup.zpowers_eq_closure] using h
  have hBea : CFSG.Open.IsElemAbelian 3 B := by
    have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ Z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hbe : Commute e b := Subgroup.mem_centralizer_iff.mp hb.2 e he
      exact (hbe.zpow_left k).eq
    exact hEea.sup_of_commute hZea hcomm
  let A : Subgroup G := B ⊔ Subgroup.zpowers f
  have hAea : CFSG.Open.IsElemAbelian 3 A := by
    have hcomm : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers f, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hBcent ha) b hb).symm
    exact hBea.sup_of_commute hFea hcomm
  have hAcard : Nat.card A = 27 := by
    have hcomm : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers f, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hBcent ha) b hb).symm
    have hFdisj' : B ⊓ Subgroup.zpowers f = ⊥ := by
      rw [inf_comm]
      exact hFdisj
    have hsupcard := CFSG.card_sup_eq_mul_of_commute B (Subgroup.zpowers f) hcomm hFdisj'
    change Nat.card ↥(B ⊔ Subgroup.zpowers f) = 27
    rw [hsupcard, hBcard, Nat.card_zpowers f, hf3]
  refine ⟨A, ?_, ?_, ?_, hAea, hAcard⟩
  · have hBQ : B ≤ Q := sup_le (Subgroup.zpowers_le.mpr heQ) hZleQ
    exact sup_le hBQ (Subgroup.zpowers_le.mpr hfQ)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers e))
  · have hZleB : Z ≤ B := le_sup_right
    exact hZleB.trans le_sup_left

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem j2_excluded'' 
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {z : G} (hzZ : z ∈ zSub P c.L) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hK9o : K9J2Order) (hK9out : K9J2Out)
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1)
    (hiso : Nonempty (J0 J ≃* Xbar c P J))
    (hinner : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ∈
      (MulAut.conj : (Jtilde J) →* MulAut (Jtilde J)).range)
    (hJ2 : Nonempty (Xbar c P J ≃* CFSG.Blueprint.NativeSporadic.J2)) : False := by
  classical
  have h7mem : 7 ∈ D.sig := by rw [h7]; exact Set.mem_singleton 7
  obtain ⟨y, hyM, hy7ord, hycent⟩ :=
    exists_seven_mem_centralizer_inf_L_of_onan c hON h7mem hP
  have hyN : y ∈ Subgroup.normalizer (J : Set G) :=
    seven_normalizes_thetaComp c hON h7 hP hNZ haL ha3 haZ hJ h3 hyM hy7ord hycent
  let fJ : Subgroup.normalizer (J : Set G) →* MulAut (Jtilde J) :=
    (thetaQuotMulAut J).comp J.normalizerMonoidHom
  let βy : MulAut (Jtilde J) := fJ ⟨y, hyN⟩
  let βz : MulAut (Jtilde J) := fJ ⟨z, hzN⟩
  let βy0 : MulAut (J0 J) :=
    CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J) βy
  let βz0 : MulAut (J0 J) :=
    CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J) βz
  have hcomm_yz : y * z = z * y := hycent z hzZ.1
  have hβcomm : βy * βz = βz * βy := by
    change fJ ⟨y, hyN⟩ * fJ ⟨z, hzN⟩ = fJ ⟨z, hzN⟩ * fJ ⟨y, hyN⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa [Subgroup.coe_mul] using hcomm_yz
  have hβ0comm : βy0 * βz0 = βz0 * βy0 := by
    calc βy0 * βz0 =
        CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J) (βy * βz) :=
          (map_mul (CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J)) βy βz).symm
      _ = CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J) (βz * βy) := by
          rw [hβcomm]
      _ = βz0 * βy0 :=
          map_mul (CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J)) βz βy
  have hβy7 : βy ^ 7 = 1 := by
    change fJ ⟨y, hyN⟩ ^ 7 = 1
    rw [← map_pow]
    have hyNpow : (⟨y, hyN⟩ : Subgroup.normalizer (J : Set G)) ^ 7 = 1 := by
      apply Subtype.ext
      rw [← hy7ord]
      exact pow_orderOf_eq_one y
    rw [hyNpow, map_one]
  have hβz3 : βz ^ 3 = 1 := by
    change fJ ⟨z, hzN⟩ ^ 3 = 1
    rw [← map_pow]
    have hzNpow : (⟨z, hzN⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [← hz3]
      exact pow_orderOf_eq_one z
    rw [hzNpow, map_one]
  have hβy07 : βy0 ^ 7 = 1 := by
    change CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J) βy ^ 7 = 1
    rw [← map_pow, hβy7, map_one]
  have hβz03 : βz0 ^ 3 = 1 := by
    change CFSG.RankThree.PartTwo.KFacts.centerDescend (Jtilde J) βz ^ 3 = 1
    rw [← map_pow, hβz3, map_one]
  have hQtilde : CFSG.Open.IsQuasisimple (Jtilde J) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).mp
      (CFSG.RankThree.PartOne.isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt
        Nat.prime_three hJ)
  obtain ⟨e0⟩ := hiso
  obtain ⟨e1⟩ := hJ2
  let e : J0 J ≃* CFSG.Blueprint.NativeSporadic.J2 := e0.trans e1
  have hinnerJ0 : βy0 ∈ (MulAut.conj : J0 J →* MulAut (J0 J)).range :=
    inner_of_pow_seven_of_mulEquiv e hK9out βy0 hβy07
  obtain ⟨u, hu⟩ := hinnerJ0
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  have hZJ2 : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi.center_eq_bot_of_simple_of_not_prime
      (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
  have hconjJ2 : Function.Injective
      (MulAut.conj : CFSG.Blueprint.NativeSporadic.J2 →* MulAut _) :=
    CFSG.LieType.Automorphisms.conj_injective_of_center_eq_bot hZJ2
  have hconjJ0 : Function.Injective (MulAut.conj : J0 J →* MulAut (J0 J)) :=
    conj_injective_J0 e hconjJ2
  obtain ⟨t, ht⟩ := hinner
  obtain ⟨v, hβz0conj⟩ := centerDescend_inner_data βz ht
  have hβz0_ne : βz0 ≠ 1 := by
    intro h
    apply hπ
    exact CFSG.HardMathSupport.Solomon.Coordinator.eq_one_of_centerDescend_eq_one hQtilde h
  by_cases hβy0one : βy0 = 1
  · have hβy1 : βy = 1 :=
      CFSG.HardMathSupport.Solomon.Coordinator.eq_one_of_centerDescend_eq_one hQtilde hβy0one
    obtain ⟨A, hAPL, haA, hZA, hAea, hAcard⟩ :=
      exists_E27_through c hON hP haL haZ
    have hAJ : A ≤ Subgroup.normalizer (J : Set G) := by
      intro u hu
      have huC : u ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcommA : (⟨u, hu⟩ : A) * ⟨a, haA⟩ = ⟨a, haA⟩ * ⟨u, hu⟩ :=
          hAea.1.is_comm.comm ⟨u, hu⟩ ⟨a, haA⟩
        exact congrArg Subtype.val hcommA
      have hu3 : ∃ k : ℕ, orderOf u = 3 ^ k := by
        have hpow : u ^ 3 = 1 := hAea.2 u hu
        have hdvd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact ⟨0, by rw [h, pow_zero]⟩
        · exact ⟨1, by rw [h, pow_one]⟩
      exact three_normalizes_thetaComp c hON h7 hP hNZ haL ha3 haZ hJ h3 huC hu3
    have hyC : y ∈ thetaQuotCentralizer J := by
      refine Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, ?_, rfl⟩
      exact MonoidHom.mem_ker.mpr hβy1
    have hJM : J = (J ⊓ D.M) ⊔ theta3 J :=
      eq_inf_sup_theta_of_seven c h7 hyM hy7ord hyC
    have hC : zSub P c.L ≤ modCentralizer D.M c.L (inSubgroup (pCore 2) c.L) :=
      zSub_le_modCentralizer' c hON hP
    have hDich : zSub P c.L ≤ thetaQuotCentralizer J ∨ A ≤ thetaQuotCentralizer J :=
      p6_dichotomy' c hP hAea hAcard hZA hAPL haA haZ hJ hAJ hJM hC
    rcases hDich with hZ | hA
    · have hzC : z ∈ thetaQuotCentralizer J := hZ hzZ
      have hβz1 : βz = 1 := by
        change fJ ⟨z, hzN⟩ = 1
        obtain ⟨w, hwker, hwz⟩ := Subgroup.mem_map.mp hzC
        have hw_eq : w = ⟨z, hzN⟩ := Subtype.ext hwz
        rw [← hw_eq]
        exact hwker
      exact hπ hβz1
    · have hzC : z ∈ thetaQuotCentralizer J := hA (hZA hzZ)
      have hβz1 : βz = 1 := by
        change fJ ⟨z, hzN⟩ = 1
        obtain ⟨w, hwker, hwz⟩ := Subgroup.mem_map.mp hzC
        have hw_eq : w = ⟨z, hzN⟩ := Subtype.ext hwz
        rw [← hw_eq]
        exact hwker
      exact hπ hβz1
  · have hord_u : orderOf u = 7 :=
      orderOf_eq_seven_of_conj (A := J0 J) hconjJ0 (β := βy0) hu hβy07 hβy0one
    have hord_v : orderOf v = 3 :=
      orderOf_eq_three_of_conj (A := J0 J) hconjJ0 (β := βz0) hβz0conj.symm hβz03 hβz0_ne
    have hcomm_uv : u * v = v * u :=
      commute_of_conj (A := J0 J) hconjJ0
        (βy := βy0) (βz := βz0) hβ0comm hu hβz0conj.symm
    exact j2_order21_J0 e hord_u hord_v hcomm_uv hK9o

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
