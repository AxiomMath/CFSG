module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen68Close
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Hyper
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem seventeen_two_three_barSub_mem_aSet {D : Data G} {V A : Subgroup G}
    (hV : Hyp125 D ⊥ V) (hs3 : 3 < E3.sParam hV.isElemAbelian) (hA : A ∈ E3.gammaSet V 2 D.T)
    (hA1 : barSub ⊥ V hV.isElemAbelian A ≠ ⊥) :
    barSub ⊥ V hV.isElemAbelian A ∈ calABar 2 D.M ⊥ V hV.isElemAbelian := by
  obtain ⟨hAT, g, hAg, hA2⟩ := hA
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hVg : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hV.isElemAbelian g
  refine s16c167_barSub_mem_calABar_of_hyperplanes hV.isElemAbelian rfl hAM
    (hAM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀))
    (B2F.isElemAbelian_mono hAg hVg) hA1 fun B hBA hm => ?_
  have hs : E3.mQuot (conjSubgroup V g) B < E3.sParam hVg := by
    rw [E3.sParam_conj hV.isElemAbelian g hVg, E3.mQuot_add hBA hAg, hm, hA2]
    omega
  exact (E3.e3_6 hVg hBA hAg hs hV.isElemAbelian.isPGroup).1.symm

private theorem seventeen_two_three_commutator_le_centralizer {D : Data G} {V A Dsub : Subgroup G}
    (hV : Hyp125 D ⊥ V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hDM : Dsub ≤ D.M)
    (hDp : IsPGroup p Dsub) (hnormal : ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hs3 : 3 < E3.sParam hV.isElemAbelian) (hA : A ∈ E3.gammaSet V 2 D.T)
    (hA1 : barSub ⊥ V hV.isElemAbelian A ≠ ⊥) :
    ∀ a ∈ A, ∀ d ∈ Dsub, ⁅a, d⁆ ∈ centralizer (V : Set G) := by
  have hVe : IsElemAbelian 2 V := hV.isElemAbelian
  have hMst : D.M ≤ stabTil ⊥ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hO2 : CFSG.Open.pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hnorm := TwelveEighteen.conj_mem_barSub (V₀ := ⊥) hVe
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hDM hO2)).1 hnormal)
  rw [barSub_sup_pCoreOf_eq_of_hyp125 hV hDM] at hnorm
  have hodd : Odd (Nat.card (barSub ⊥ V hVe Dsub)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hDbarp : IsPGroup p (barSub ⊥ V hVe Dsub) :=
      (hDp.comap_subtype (K := stabTil ⊥ V)).map (actTil ⊥ V hVe)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hDbarp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hcomm := commutator_eq_bot_of_mem_calABar_two hVe
    (seventeen_two_three_barSub_mem_aSet hV hs3 hA hA1) (barSub_mono ⊥ V hVe hDM) hodd hnorm
  intro a ha d hd
  have hast : a ∈ stabTil ⊥ V := hMst (hA.1.trans D.sylowM.le ha)
  have hdst : d ∈ stabTil ⊥ V := hMst (hDM hd)
  have h1 := Subgroup.commutator_mem_commutator (actTil_mem_barSub ⊥ V hVe hd hdst)
    (actTil_mem_barSub ⊥ V hVe ha hast)
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement] at h1
  have h2 := (TwelveTwentyThree.actTil_bot_eq_one_iff V hVe _).1 h1
  rw [← commutatorElement_inv]
  exact (centralizer (V : Set G)).inv_mem h2

private theorem seventeen_two_three_C_H_isPGroup {D : Data G} {V Dsub : Subgroup G}
    (hV : Hyp125 D ⊥ V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hDM : Dsub ≤ D.M)
    (hDp : IsPGroup p Dsub) (hperm : Permutes Dsub D.T)
    (hDsubC : Dsub ⊓ centralizer (V : Set G) = ⊥) :
    IsPGroup 2 ↥((Dsub ⊔ D.T) ⊓ centralizer (V : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 V := hV.isElemAbelian
  have hMst : D.M ≤ stabTil ⊥ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hinf : barSub ⊥ V hVe Dsub ⊓ barSub ⊥ V hVe D.T = ⊥ :=
    (IsPGroup.disjoint_of_ne (p₁ := p) (p₂ := 2) (H₁ := barSub ⊥ V hVe Dsub)
      (H₂ := barSub ⊥ V hVe D.T) hp2
      ((hDp.comap_subtype (K := stabTil ⊥ V)).map (actTil ⊥ V hVe))
      ((D.sylowM.isPGroup.comap_subtype (K := stabTil ⊥ V)).map (actTil ⊥ V hVe))).eq_bot
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd
      (Nat.card ↥((Dsub ⊔ D.T) ⊓ centralizer (V : Set G))) with ⟨k, hk⟩ | ⟨q, hq, hqdvd, hqodd⟩
  · exact (IsPGroup.iff_card (p := 2)).2 ⟨k, hk⟩
  · exfalso
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    have hyC : (y : G) ∈ centralizer (V : Set G) := y.2.2
    obtain ⟨d, hdD, t, htT, hdt⟩ := uc22p2214_mem_sup_of_permutes hperm y.2.1
    have hdst : d ∈ stabTil ⊥ V := hMst (hDM hdD)
    have htst : t ∈ stabTil ⊥ V := hMst (D.sylowM.le htT)
    have hyst : (y : G) ∈ stabTil ⊥ V := by rw [hdt]; exact mul_mem hdst htst
    have hprod : actTil ⊥ V hVe ⟨d, hdst⟩ * actTil ⊥ V hVe ⟨t, htst⟩ = 1 := by
      rw [← map_mul, show (⟨d, hdst⟩ * ⟨t, htst⟩ : stabTil ⊥ V) = ⟨(y : G), hyst⟩ from
        Subtype.ext hdt.symm, TwelveTwentyThree.actTil_bot_eq_one_iff]
      exact hyC
    have htinf : actTil ⊥ V hVe ⟨t, htst⟩ ∈ barSub ⊥ V hVe Dsub ⊓ barSub ⊥ V hVe D.T :=
      ⟨eq_inv_of_mul_eq_one_right hprod ▸ Subgroup.inv_mem _ (actTil_mem_barSub ⊥ V hVe hdD hdst),
        actTil_mem_barSub ⊥ V hVe htT htst⟩
    rw [hinf, Subgroup.mem_bot, TwelveTwentyThree.actTil_bot_eq_one_iff] at htinf
    have hd1 : d = 1 := by
      have : d ∈ Dsub ⊓ centralizer (V : Set G) :=
        ⟨hdD, by simpa [hdt] using mul_mem hyC (inv_mem htinf)⟩
      rwa [hDsubC, Subgroup.mem_bot] at this
    have hyT : (y : G) ∈ D.T := by rw [hdt, hd1, one_mul]; exact htT
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_orderOf_eq_pow (⟨(y : G), hyT⟩ : D.T)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hyord] at hk
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
      (hq.dvd_of_dvd_pow (by rw [← hk]))
    exact (Nat.not_even_iff_odd.mpr hqodd) (hq2 ▸ even_two)

private theorem seventeen_two_three_commutator_wClos_le {D : Data G} {V Dsub : Subgroup G}
    (hV : Hyp125 D ⊥ V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hDM : Dsub ≤ D.M) (hDp : IsPGroup p Dsub)
    (hnormal : ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hs3 : 3 < E3.sParam hV.isElemAbelian) :
    ⁅E3.wClos V 2 D.T, Dsub⁆ ≤ centralizer (V : Set G) := by
  have hVe : IsElemAbelian 2 V := hV.isElemAbelian
  have hCnorm : D.M ≤ normalizer (centralizer (V : Set G) : Set G) :=
    hV.pairFacts.le_normalizer.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V)
  have hHleM : Dsub ⊔ D.T ≤ D.M := sup_le hDM D.sylowM.le
  have hMst : D.M ≤ stabTil ⊥ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  rw [Subgroup.commutator_le]
  intro w hw d hd
  let K : Subgroup G :=
    { carrier := {x : G | x ∈ Dsub ⊔ D.T ∧ ⁅x, d⁆ ∈ centralizer (V : Set G)}
      one_mem' := ⟨(Dsub ⊔ D.T).one_mem, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro a b ⟨haH, haC⟩ ⟨hbH, hbC⟩
        refine ⟨(Dsub ⊔ D.T).mul_mem haH hbH, ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact (centralizer (V : Set G)).mul_mem
          ((Subgroup.mem_normalizer_iff.1 (hCnorm (hHleM haH)) ⁅b, d⁆).1 hbC) haC
      inv_mem' := by
        rintro a ⟨haH, haC⟩
        refine ⟨(Dsub ⊔ D.T).inv_mem haH, ?_⟩
        rw [commutatorElement_inv_left, ← commutatorElement_inv]
        simpa using (Subgroup.mem_normalizer_iff.1
          (hCnorm (hHleM ((Dsub ⊔ D.T).inv_mem haH))) ⁅a, d⁆⁻¹).1 (Subgroup.inv_mem _ haC) }
  have hA_le : ∀ A ∈ E3.gammaSet V 2 D.T, A ≤ K := by
    intro A hA x hx
    refine ⟨hA.1.trans le_sup_right hx, ?_⟩
    by_cases hA1 : barSub ⊥ V hVe A = ⊥
    · have hast : x ∈ stabTil ⊥ V := hMst (hA.1.trans D.sylowM.le hx)
      have hmem := actTil_mem_barSub ⊥ V hVe hx hast
      rw [hA1, Subgroup.mem_bot, TwelveTwentyThree.actTil_bot_eq_one_iff] at hmem
      have hxC : x ∈ centralizer (V : Set G) := hmem
      rw [commutatorElement_def, show x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) by group]
      exact (centralizer (V : Set G)).mul_mem hxC
        ((Subgroup.mem_normalizer_iff.1 (hCnorm (hDM hd)) x⁻¹).1 (Subgroup.inv_mem _ hxC))
    · exact seventeen_two_three_commutator_le_centralizer hV hp hp2 hDM hDp hnormal hs3 hA hA1
        x hx d hd
  exact (E3.wClos_le_of_forall hA_le hw).2

private theorem seventeen_two_three_le_normalizer_wClos {D : Data G} {V Dsub : Subgroup G}
    (hV : Hyp125 D ⊥ V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hDM : Dsub ≤ D.M)
    (hDp : IsPGroup p Dsub) (hperm : Permutes Dsub D.T)
    (hnormal : ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hDsubC : Dsub ⊓ centralizer (V : Set G) = ⊥) (hs3 : 3 < E3.sParam hV.isElemAbelian) :
    Dsub ≤ normalizer (E3.wClos V 2 D.T : Set G) := by
  set H : Subgroup G := Dsub ⊔ D.T with hHdef
  set R : Subgroup G := CFSG.Open.pCoreOf 2 H with hRdef
  set W : Subgroup G := E3.wClos V 2 D.T with hWdef
  have hHleM : H ≤ D.M := sup_le hDM D.sylowM.le
  have hW_le_T : W ≤ D.T := E3.wClos_le 2 D.T
  have hDsub_le_H : Dsub ≤ H := le_sup_left
  have hT_le_H : D.T ≤ H := le_sup_right
  have hR_le_H : R ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hRnormH : H ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hR_le_T : R ≤ D.T :=
    CFSG.Quasithin.IsSylowIn.le_of_normal
      (CFSG.ABGLocalTools.isSylowOf_iff.1 (D.sylowM.of_le hT_le_H hHleM)) hR_le_H
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hR_le_H).2 hRnormH)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hCHnormal : ((H ⊓ centralizer (V : Set G)).subgroupOf H).Normal := by
    haveI : ((centralizer (V : Set G)).subgroupOf D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centralizer_le_of_inCalV D hV.inCalV)).2
        (hV.pairFacts.le_normalizer.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V))
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A := D.M)
      (A' := centralizer (V : Set G)) H
    rwa [inf_eq_right.mpr hHleM, inf_comm] at h
  have hCH_le_R : H ⊓ centralizer (V : Set G) ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hCHnormal
      (seventeen_two_three_C_H_isPGroup hV hp hp2 hDM hDp hperm hDsubC)
  have hcomm_le_R : ⁅W, Dsub⁆ ≤ R :=
    (le_inf ((Subgroup.commutator_le_sup W Dsub).trans
      (sup_le (hW_le_T.trans hT_le_H) hDsub_le_H))
      (seventeen_two_three_commutator_wClos_le hV hp hp2 hDM hDp hnormal hs3)).trans hCH_le_R
  have hT_W : D.T ≤ normalizer (W : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := 2) D.T)
  have hT_norm : D.T ≤ normalizer ((W ⊔ R : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_sup W R ⟨hT_W ht, hRnormH (hT_le_H ht)⟩
  have hDsub_norm : Dsub ≤ normalizer ((W ⊔ R : Subgroup G) : Set G) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    refine (sup_le (fun w hw => ?_) (fun r hr => ?_) : W ⊔ R ≤
      (W ⊔ R).comap (MulAut.conj d).toMonoidHom) hx
    · have hc : ⁅w⁻¹, d⁆ ∈ R :=
        hcomm_le_R (Subgroup.commutator_mem_commutator (W.inv_mem hw) hd)
      have he : (MulAut.conj d).toMonoidHom w = w * ⁅w⁻¹, d⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def, inv_inv]
        group
      rw [Subgroup.mem_comap, he]
      exact Subgroup.mul_mem_sup hw hc
    · exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.1 (hRnormH (hDsub_le_H hd)) r).1 hr)
  have hW_le_R : W ≤ R :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf 2
      (sup_le (hW_le_T.trans hT_le_H) hR_le_H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le (hW_le_T.trans hT_le_H) hR_le_H)).2
        (sup_le hDsub_norm hT_norm))
      (D.sylowM.isPGroup.to_le (sup_le hW_le_T hR_le_T)))
  have hW_eq_R : W = E3.wClos V 2 R :=
    le_antisymm (E3.wClos_le_of_forall fun A hA =>
      E3.le_wClos ⟨(E3.le_wClos hA).trans hW_le_R, hA.2⟩) (E3.wClos_mono hR_le_T)
  rw [hW_eq_R]
  exact (hDsub_le_H.trans hRnormH).trans (E3.normalizer_le_normalizer_wClos (V := V) (i := 2) R)

private theorem seventeen_two_three_of_ne_bot (D : Data G) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h127 : R127 D) {V : Subgroup G} (hV : Hyp125 D ⊥ V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Dsub : Subgroup G} (hDM : Dsub ≤ D.M) (hDp : IsPGroup p Dsub)
    (hDnc : ¬ IsCyclic ↥Dsub) (hcardD : Nat.card ↥Dsub = p ^ 2)
    (hΓ : rankThreeGamma 1 p Dsub ≤ D.M) (hCne : Dsub ⊓ centralizer (V : Set G) ≠ ⊥) :
    ¬ IrrOn (D.M ⊓ normalizer (Dsub : Set G)) Dsub ∧
      Nat.card ↥(barSub ⊥ V hV.isElemAbelian Dsub) = p := by
  have hMnormV : D.M ≤ normalizer (V : Set G) := hV.pairFacts.le_normalizer
  have hCcyc : IsCyclic ↥(Dsub ⊓ centralizer (V : Set G)) :=
    UC22.uc22p22u_isCyclic_inf_centralizer D h61 h63 (Hyp125.hyp11 h127 hV) hp hp2 hDM hDp
      (Or.inl hΓ)
  have hCle : Dsub ⊓ centralizer (V : Set G) ≤ Dsub := inf_le_left
  have hCneD : Dsub ⊓ centralizer (V : Set G) ≠ Dsub := fun hEq => hDnc (hEq ▸ hCcyc)
  obtain ⟨n, hn2, hn⟩ :=
    (Nat.dvd_prime_pow hp).1 (hcardD ▸ Subgroup.card_dvd_of_le hCle)
  have hCn : Nat.card ↥(Dsub ⊓ centralizer (V : Set G)) = p := by
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hn]; simp)) hCne
    · simpa using hn
    · exact absurd (Subgroup.eq_of_le_of_card_ge hCle (by rw [hn, ← hcardD])) hCneD
  refine ⟨fun hirr => ?_, ?_⟩
  · rcases hirr (Dsub ⊓ centralizer (V : Set G)) hCle (fun n hn =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hn.2, CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V (hMnormV hn.1)⟩) with hbot | htop
    · exact hCne hbot
    · exact hCneD htop
  · rw [s1668_card_barSub_bot (V := V) (A := Dsub) hV.isElemAbelian (hDM.trans hMnormV)]
    have hrel := Subgroup.relIndex_mul_card (H := centralizer (V : Set G)) (K := Dsub)
    rw [inf_comm, hCn, hcardD, pow_two] at hrel
    exact Nat.eq_of_mul_eq_mul_right hp.pos hrel

theorem seventeen_two_three (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h77 : F07.R77Eq D) (h63 : UC6.R6_3 D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D)
    (h111 : W3Thm111 G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) : R17_2_3At D V₀ V hV := by
  intro p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  obtain ⟨p', hp', -, -, hDp', -, -, hperm, hΓ, -⟩ :=
    seventeen_two_one D hSg h1219 h77 hV p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  obtain ⟨hcardD, rfl, hk, hm⟩ :=
    seventeen_two_two D hSg h1219 h77 hV h17_1 p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  obtain rfl : p' = p := TwelveShort.eq_of_isPGroup_of_ne_bot hp' hp
    (fun h => hDnc (by rw [h]; exact isCyclic_of_subsingleton)) hDp' hDp
  by_cases hCbot : Dsub ⊓ centralizer (V : Set G) = ⊥
  · exfalso
    have hV1 : InCalV1 D.M D.T V := by
      rcases hV.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
      · exact hW.1.1
      · exact absurd rfl h0.1.1
    have hs3 : 3 < E3.sParam hV.isElemAbelian :=
      TwelveShort.lt_sParam_of_mBarGT D h111 hV1 ((hV.mBarGT_iff_lt_mBar 2).2 (by omega))
        ((hV.mBarGT_iff_lt_mBar 3).2 (by omega))
    have hU : InCalU D.M (D.M ⊓ normalizer (E3.wClos V 2 D.T : Set G)) :=
      InCalU.mono D.maxLocal
        (TwelveShort.inCalU_of_inP11 D h63 hp hp2 hDM hDp hexp hΓ Dsub le_rfl hDnc)
        (le_inf hDM (seventeen_two_three_le_normalizer_wClos hV hp hp2 hDM hDp hperm hnormal
          hCbot hs3)) inf_le_left
    have hrk : 2 < rk ↥V := by
      have h4 : 4 ≤ rk ↥V := by
        rw [← hm]
        exact CFSG.LocalAnalysis.WeakClosure81.mBar_le_rk (M := D.M) hV.isElemAbelian bot_le
      omega
    have h615 := six_fifteen_three (V := V) (M := D.M) (S := D.T)
      hV.isElemAbelian D.maxLocal D.sylowM.isPGroup
      (TwelveShort.wClos_zero_ne_bot D hV.inCalV) hrk hU
    have hmk : MBarGT D.M ⊥ V (D.k + 0) := by
      rw [hk, add_zero]
      exact (hV.mBarGT_iff_lt_mBar 2).2 (by omega)
    rcases twelve_ten_two D hx h61 h126 h111 hV rfl (i := 0) hmk with h | h
    · exact h (h615.1 0 (by omega))
    · exact h (by simpa [hk] using h615.2 0 (by omega))
  · exact seventeen_two_three_of_ne_bot D h61 h63 h127 hV hp hp2 hDM hDp hDnc hcardD hΓ hCbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
