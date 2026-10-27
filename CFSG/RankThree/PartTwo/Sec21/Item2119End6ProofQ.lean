module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs
import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQTools
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof2126
import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofFrame
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace Item2119End6Proof

variable {G : Type} [Group G] [Finite G]

theorem factorization_card_eq_two {Le : Subgroup G}
    (eLe : lBar Le ≃* projSL 3 (GaloisField 2 2)) : (Nat.card Le).factorization 3 = 2 := by
  have hL : Nat.card Le = Nat.card (lBar Le) * Nat.card (aschbacherSolvableCore 3 Le) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [Nat.card_congr eLe.toEquiv, KFacts.L34.card_projSL] at hL
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 Le) :=
    three_not_dvd_card_aschbacherSolvableCore
  rw [hL]
  refine CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (m := 2240 * Nat.card (aschbacherSolvableCore 3 Le)) (by ring) ?_
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · norm_num at h
  · exact hθ h

theorem facts_Le (h45 : Sec4.Item4_5) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) {Lf : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2))) {e : G} (he : e ∈ A)
    (hed : e ∉ Subgroup.zpowers d) :
    Nonempty (lBar (Lf e) ≃* projSL 3 (GaloisField 2 2)) ∧
      Lf e ≤ Subgroup.centralizer ({e} : Set G) ∧ e ∉ Lf e ∧
      A ≤ Subgroup.normalizer (Lf e : Set G) ∧
      Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (Lf e : Set G) ∧ d ∈ Lf e := by
  have hpair := hE.cfg.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have he3 : e ^ 3 = 1 := hAe.2 e he
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  obtain ⟨hLe, hLe3, hLeU, ⟨eLe⟩, hdLe, -, -⟩ := hLf e he hed
  obtain ⟨eL⟩ := h26
  have eLe' := eLe.trans eL
  have hZ : Subgroup.center (lBar (Lf e)) = ⊥ :=
    Item2119End3Proof.center_eq_bot_of_mulEquiv' eLe'
      (Item21Early2Proof.center_projSL_three_eq_bot (by norm_num) (by decide))
  have hLeC : Lf e ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLe
  have hALe : A ≤ Subgroup.normalizer (Lf e : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe he he1
      (Lf e) hLe
  have hCN : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (Lf e : Set G) := by
    intro g hg
    have hge : g * e * g⁻¹ = e := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
    have hL' : (Lf e).map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 e := by
      have h1 := map_mem_thetaComponentsAt (MulAut.conj g) hLe
      rwa [MulAut.conj_apply, hge] at h1
    have h3L' : 3 ∣ Nat.card ((Lf e).map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hLe3
    exact mem_normalizer_of_map_conj_eq (hLeU _ hL' h3L')
  exact ⟨⟨eLe'⟩, hLeC, Item2119End3Proof.not_mem_of_mem_thetaComponentsAt hLe hZ he3 he1, hALe,
    hCN, hdLe⟩

theorem three_pow_le_81 (h45 : Sec4.Item4_5) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) {Lf : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)))
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ F : Subgroup G, IsFOf2127 A (Lf e) F →
      IsSylowOf 3 (A ⊔ F) (Subgroup.centralizer ({e} : Set G)))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) :
    3 ^ (Nat.card (Subgroup.centralizer ({e} : Set G))).factorization 3 ≤ 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have h27A : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  obtain ⟨⟨eLe⟩, hLeC, heLe, hALe, -, hdLe⟩ := facts_Le h45 hE hLf h26 he hed
  obtain ⟨R₀, hR₀, hAR₀⟩ := Item2119End5Proof.exists_isSylowOf_ge
    (le_sup_left : A ≤ A ⊔ Lf e) hA3
  have hRL : IsSylowOf 3 (R₀ ⊓ Lf e) (Lf e) :=
    hR₀.inf_of_le_normalizer le_sup_right (sup_le hALe Subgroup.le_normalizer)
  have hRL9 : Nat.card (R₀ ⊓ Lf e : Subgroup G) = 9 := by
    rw [hRL.card_eq, factorization_card_eq_two eLe]
    norm_num
  obtain ⟨hF, -, hF81, -⟩ := isFOf2127_of_sylow hAe h27A he hE.mem_d.1 hdLe hE.ne_one_d hed eLe
    hLeC heLe hALe hAR₀ hRL9
  have hsyl := h27 e he hed _ hF
  rw [← hsyl.card_eq]
  exact hF81

theorem card_le_three_pow_of_isPGroup {C R : Subgroup G} (hRC : R ≤ C) (hR3 : IsPGroup 3 R) :
    Nat.card R ≤ 3 ^ (Nat.card C).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS, hRS⟩ := Item2119End5Proof.exists_isSylowOf_ge hRC hR3
  rw [← hS.card_eq]
  exact Subgroup.card_le_of_le hRS

end Item2119End6Proof

open Item2119End6Proof in
theorem item2127Q_of
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) :
    Item2127Q := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 h27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27A : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hfinA : Finite (MulAut A) :=
    Finite.of_injective (fun σ : MulAut A => (σ : A → A)) DFunLike.coe_injective
  set W := Subgroup.normalizer (A : Set G) with hW
  set ρ := A.normalizerMonoidHom with hρ
  set T := trivOnQuot A (Subgroup.zpowers d) ⊓ fixOn A (Subgroup.zpowers d) with hT
  have hTW : T ≤ wStar A := by
    refine inf_le_left.trans ?_
    rw [← h24]
    exact sup_le (starOf_le_wStar A X) (starOf_le_wStar A L)
  have hT3 : IsPGroup 3 T := fun τ =>
    ⟨1, Subtype.ext (by simpa using pow_three_eq_one_of_mem_tD hd3 τ.2)⟩
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, hw3, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    Item2119EndProof.zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  have hwc : Commute w c := Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL)
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  obtain ⟨x, hxN, hx3, hxd, hxA, hxc⟩ :=
    Item2119End5Proof.exists_mover h211 h2116 h45 h66 hE h23 hcA hcd
  have hconjT : ∀ (g : G) (hg : g ∈ W), g * d * g⁻¹ = d →
      (∀ y ∈ A, y⁻¹ * (g * y * g⁻¹) ∈ Subgroup.zpowers d) → ρ ⟨g, hg⟩ ∈ T := by
    intro g hg hgd hgA
    refine ⟨mem_trivOnQuot_iff.mpr fun y => hgA y y.2, mem_fixOn_iff.mpr fun y hy => ?_⟩
    apply Subtype.ext
    exact Item21LateProof.conj_eq_of_mem_zpowers hgd hy
  set wT := ρ ⟨w, hwN⟩ with hwT'
  set xT := ρ ⟨x, hxN⟩ with hxT'
  have hwT : wT ∈ T := hconjT w hwN hwd hwA
  have hxT : xT ∈ T := hconjT x hxN hxd hxA
  have hwx : wT * xT = xT * wT := by
    refine MulEquiv.ext fun z => Subtype.ext ?_
    have h1 := Item2119End4Proof.comm_of_trivOnQuot hcomm hdA hwA hwd hxA hxd z z.2
    change w * (x * z * x⁻¹) * w⁻¹ = x * (w * z * w⁻¹) * x⁻¹
    calc w * (x * z * x⁻¹) * w⁻¹ = (w * x) * z * (w * x)⁻¹ := by group
      _ = (x * w) * z * (x * w)⁻¹ := h1
      _ = x * (w * z * w⁻¹) * x⁻¹ := by group
  have hwT3 : wT ^ 3 = 1 := by
    rw [hwT', ← map_pow, show (⟨w, hwN⟩ : W) ^ 3 = 1 from Subtype.ext (by simpa using hw3),
      map_one]
  have hxT3 : xT ^ 3 = 1 := by
    rw [hxT', ← map_pow, show (⟨x, hxN⟩ : W) ^ 3 = 1 from Subtype.ext (by simpa using hx3),
      map_one]
  have hwT1 : wT ≠ 1 := by
    intro h
    obtain ⟨y, hyA, hy⟩ := hwmove
    apply hy
    have := congrArg (fun φ : MulAut A => ((φ ⟨y, hyA⟩ : A) : G)) h
    exact this
  have hxw : xT ∉ Subgroup.zpowers wT := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hxc
    have hwck : (wT ^ k) ⟨c, hcA⟩ = ⟨c, hcA⟩ := by
      rw [hwT', ← map_zpow]
      apply Subtype.ext
      change ((⟨w, hwN⟩ ^ k : W) : G) * c * ((⟨w, hwN⟩ ^ k : W) : G)⁻¹ = c
      rw [Subgroup.coe_zpow, (hwc.zpow_left k).eq, mul_inv_cancel_right]
    rw [hk] at hwck
    exact congrArg Subtype.val hwck
  have hT9 : 9 ≤ Nat.card T := by
    have h9 := Item21LateProof.card_zpowers_sup_zpowers hwx hwT3 hxT3 hwT1 hxw
    rw [← h9]
    exact Subgroup.card_le_of_le (sup_le (Subgroup.zpowers_le.mpr hwT)
      (Subgroup.zpowers_le.mpr hxT))
  set NT : Subgroup G := (T.comap ρ).map W.subtype with hNT
  have hNTW : NT ≤ W := Subgroup.map_subtype_le _
  have hρA : ∀ (y : G) (hy : y ∈ A), ρ ⟨y, Subgroup.le_normalizer hy⟩ = 1 := by
    intro y hy
    refine MulEquiv.ext fun z => Subtype.ext ?_
    change y * z * y⁻¹ = z
    rw [hcomm y hy z z.2, mul_inv_cancel_right]
  have hANT : A ≤ NT := by
    intro y hy
    refine ⟨⟨y, Subgroup.le_normalizer hy⟩, ?_, rfl⟩
    change ρ ⟨y, _⟩ ∈ T
    rw [hρA y hy]
    exact T.one_mem
  obtain ⟨P₁, hP₁, hAP₁⟩ := Item2119End5Proof.exists_isSylowOf_ge hANT hA3
  obtain ⟨P, hP, hP₁P⟩ :=
    Item2119End5Proof.exists_isSylowOf_ge (hP₁.le.trans hNTW) hP₁.isPGroup
  have hPW : P ≤ W := hP.le
  have hAP : A ≤ P := hAP₁.trans hP₁P
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hTP : T ≤ starOf A P := by
    let f : NT →* T := (ρ.comp (Subgroup.inclusion hNTW)).codRestrict T (fun g => by
      obtain ⟨w', hw', hwg⟩ := g.2
      have h1 : Subgroup.inclusion hNTW g = w' := Subtype.ext hwg.symm
      change ρ (Subgroup.inclusion hNTW g) ∈ T
      rw [h1]
      exact hw')
    have hf : Function.Surjective f := by
      rintro ⟨τ, hτ⟩
      obtain ⟨w', hw'⟩ := hTW hτ
      have hw'T : w' ∈ T.comap ρ := by
        change ρ w' ∈ T
        rw [hw']
        exact hτ
      refine ⟨⟨(w' : G), ⟨w', hw'T, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      change ρ (Subgroup.inclusion hNTW ⟨(w' : G), _⟩) = τ
      rw [← hw']
      rfl
    obtain ⟨Q, hQ⟩ := hP₁.exists_sylow_eq_subgroupOf
    have hQT : (Q : Subgroup NT).map f = ⊤ := by
      have h := ((Q.mapSurjective hf).is_maximal' (hT3.to_subgroup ⊤) le_top).symm
      rwa [Sylow.coe_mapSurjective] at h
    intro τ hτ
    have hmem : (⟨τ, hτ⟩ : T) ∈ (Q : Subgroup NT).map f := by
      rw [hQT]
      exact Subgroup.mem_top _
    obtain ⟨q, hq, hqτ⟩ := hmem
    have hqP₁ : (q : G) ∈ P₁ := by
      rw [hQ] at hq
      exact hq
    exact ⟨⟨(q : G), hNTW q.2⟩, Subgroup.mem_subgroupOf.mpr (hP₁P hqP₁),
      congrArg Subtype.val hqτ⟩
  set ψP := ρ.comp (Subgroup.inclusion hPW) with hψP
  have hrangeP : ψP.range = starOf A P := by
    rw [hψP, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hkerP : (ψP.ker).map P.subtype = P ⊓ Subgroup.centralizer (A : Set G) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have h1 : ρ (Subgroup.inclusion hPW p) = 1 := hp
      have h2 := congrArg (fun φ : MulAut A => ((φ ⟨z, hz⟩ : A) : G)) h1
      change (p : G) * z * (p : G)⁻¹ = z at h2
      calc z * p = (p : G) * z * (p : G)⁻¹ * p := by rw [h2]
        _ = p * z := by group
    · rintro ⟨hyP, hyC⟩
      refine ⟨⟨y, hyP⟩, ?_, rfl⟩
      change ρ (Subgroup.inclusion hPW ⟨y, hyP⟩) = 1
      refine MulEquiv.ext fun z => Subtype.ext ?_
      change y * z * y⁻¹ = z
      rw [← Subgroup.mem_centralizer_iff.mp hyC z z.2, mul_inv_cancel_right]
  have hcardP : Nat.card P =
      Nat.card (P ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) * Nat.card (starOf A P) := by
    rw [card_eq_card_ker_mul_card_range ψP, hrangeP, ← hkerP,
      Subgroup.card_map_of_injective P.subtype_injective]
  have hPd : ∀ p ∈ P, p * d * p⁻¹ = d := by
    intro p hp
    obtain ⟨k, hk⟩ := hP3 ⟨p, hp⟩
    have hpk : p ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact conj_eq_of_mem_zpowers_of_pow hd3 hd1 (hE.normal_d p (hPW hp)) hpk
  have hC81 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ R : Subgroup G,
      R ≤ Subgroup.centralizer ({e} : Set G) → IsPGroup 3 R → Nat.card R ≤ 81 :=
    fun e he hed R hR hR3 =>
      (card_le_three_pow_of_isPGroup hR hR3).trans (three_pow_le_81 h45 hE hLf h26 h27 he hed)
  obtain ⟨e₀, he₀A, he₀d, he₀⟩ := exists_fixed_coset hAe h27A hdA hd1 hP3 hPW hPd
  have hle3 := card_le_three_mul_card_centralizer hAe hdA hPd he₀
  have hP243 : Nat.card P ≤ 243 := by
    have := hC81 e₀ he₀A he₀d _ inf_le_right (hP3.to_le inf_le_left)
    omega
  have hACA : A ≤ P ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf hAP (fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => hcomm z hz y hy)
  have hPCA : 27 ≤ Nat.card (P ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
    h27A ▸ Subgroup.card_le_of_le hACA
  have hPstar : 9 ≤ Nat.card (starOf A P) := hT9.trans (Subgroup.card_le_of_le hTP)
  have hb : Nat.card (starOf A P) ≤ 9 := by
    have h1 : 27 * Nat.card (starOf A P) ≤ 243 :=
      (Nat.mul_le_mul_right _ hPCA).trans (hcardP ▸ hP243)
    omega
  have ha : Nat.card (P ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤ 27 := by
    have h1 : Nat.card (P ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) * 9 ≤ 243 :=
      (Nat.mul_le_mul_left _ hPstar).trans (hcardP ▸ hP243)
    omega
  have hPCAeq : A = P ⊓ Subgroup.centralizer (A : Set G) :=
    Subgroup.eq_of_le_of_card_ge hACA (by rw [h27A]; exact ha)
  have hstarT : T = starOf A P := Subgroup.eq_of_le_of_card_ge hTP (hb.trans hT9)
  set F : G → Subgroup G := fun e =>
    ((P ⊓ Subgroup.centralizer ({e} : Set G)) ⊓ Lf e) ⊔ Subgroup.zpowers e with hFdef
  have key : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e) ∧
      A ⊔ F e = P ⊓ Subgroup.centralizer ({e} : Set G) ∧
      Nat.card (A ⊔ F e : Subgroup G) = 81 ∧ ∀ y ∈ A ⊔ F e, y ^ 3 = 1 := by
    intro e he hed
    obtain ⟨⟨eLe⟩, hLeC, heLe, hALe, hCN, hdLe⟩ := facts_Le h45 hE hLf h26 he hed
    obtain ⟨τ, hτT, hτ1, hτe⟩ := exists_ne_one_fix_of_le_tD hAe hdA le_rfl hT9 ⟨e, he⟩
    obtain ⟨u, hu, rfl⟩ := hTP hτT
    have huP : (u : G) ∈ P := hu
    have hue : (u : G) * e * (u : G)⁻¹ = e := congrArg Subtype.val hτe
    have huA : (u : G) ∉ A := by
      intro huA
      apply hτ1
      refine MulEquiv.ext fun z => Subtype.ext ?_
      change (u : G) * z * (u : G)⁻¹ = z
      rw [hcomm _ huA z z.2, mul_inv_cancel_right]
    set R := P ⊓ Subgroup.centralizer ({e} : Set G) with hR
    have hR3 : IsPGroup 3 R := hP3.to_le inf_le_left
    have hAR : A ≤ R := le_inf hAP (fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy e he))
    have huR : (u : G) ∈ R := by
      refine ⟨huP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (u : G) * e = (u : G) * e * (u : G)⁻¹ * u := by group
        _ = e * u := by rw [hue]
    have hAuR : A ⊔ Subgroup.zpowers (u : G) ≤ R := sup_le hAR (Subgroup.zpowers_le.mpr huR)
    have hR81 : 81 ≤ Nat.card R := by
      have hlt : A < A ⊔ Subgroup.zpowers (u : G) := lt_of_le_of_ne le_sup_left (fun h =>
        huA ((SetLike.ext_iff.mp h (u : G)).mpr
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))))
      obtain ⟨m, hm⟩ := (hR3.to_le hAuR).exists_card_eq
      have h1 := Subgroup.card_lt_of_lt hlt
      rw [h27A, hm] at h1
      have hm4 : 4 ≤ m := by
        by_contra hm4
        have : 3 ^ m ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
        _ = Nat.card (A ⊔ Subgroup.zpowers (u : G) : Subgroup G) := hm.symm
        _ ≤ Nat.card R := Subgroup.card_le_of_le hAuR
    have hR81' : Nat.card R = 81 := le_antisymm (hC81 e he hed R inf_le_right hR3) hR81
    have hf81 : 3 ^ (Nat.card (Subgroup.centralizer ({e} : Set G))).factorization 3 = 81 := by
      have h1 : Nat.card R ≤ 3 ^ (Nat.card (Subgroup.centralizer ({e} : Set G))).factorization 3 :=
        card_le_three_pow_of_isPGroup (inf_le_right : R ≤ _) hR3
      have h2 := three_pow_le_81 h45 hE hLf h26 h27 he hed
      rw [hR81'] at h1
      omega
    have hRsyl : IsSylowOf 3 R (Subgroup.centralizer ({e} : Set G)) :=
      isSylowOf_of_card inf_le_right (by rw [hR81', hf81])
    have hRL : IsSylowOf 3 (R ⊓ Lf e) (Lf e) := hRsyl.inf_of_le_normalizer hLeC hCN
    have hRL9 : Nat.card (R ⊓ Lf e : Subgroup G) = 9 := by
      rw [hRL.card_eq, factorization_card_eq_two eLe]
      norm_num
    obtain ⟨hF, hFR, -, hFexp⟩ := isFOf2127_of_sylow hAe h27A he hdA hdLe hd1 hed eLe hLeC
      heLe hALe hAR hRL9
    have hsyl := h27 e he hed _ hF
    have hAF81 : Nat.card (A ⊔ F e : Subgroup G) = 81 := by rw [hsyl.card_eq, hf81]
    have hAFR : A ⊔ F e = R :=
      Subgroup.eq_of_le_of_card_ge hFR (by rw [hR81', hAF81])
    exact ⟨hF, hAFR, hAF81, hFexp⟩
  have hcov : ∀ y ∈ P, ∃ e ∈ A, e ∉ Subgroup.zpowers d ∧ y ∈ A ⊔ F e := by
    intro y hy
    have hyT : ρ ⟨y, hPW hy⟩ ∈ T := by
      rw [hstarT]
      exact ⟨⟨y, hPW hy⟩, hy, rfl⟩
    have hyA : ∀ z ∈ A, z⁻¹ * (y * z * y⁻¹) ∈ Subgroup.zpowers d := fun z hz =>
      (mem_trivOnQuot_iff.mp hyT.1) ⟨z, hz⟩
    obtain ⟨e, he, hed, hye⟩ := exists_fixed_of_trivOnQuot hAe h27A hdA (hPW hy) hyA
    refine ⟨e, he, hed, ?_⟩
    rw [(key e he hed).2.1]
    refine ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc y * e = y * e * y⁻¹ * y := by group
      _ = e * y := by rw [hye]
  have hQP : q2127Of A d F = P := by
    apply le_antisymm
    · refine iSup₂_le fun e he => ?_
      rw [(key e he.1 he.2).2.1]
      exact inf_le_left
    · intro y hy
      obtain ⟨e, he, hed, hye⟩ := hcov y hy
      exact (le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) =>
        A ⊔ F e) e ⟨he, hed⟩ le_rfl) hye
  refine ⟨F, fun e he hed => (key e he hed).1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQP]
    exact hP
  · rw [hQP]
    exact hPCAeq.symm
  · rw [hQP]
    exact hstarT.symm
  · intro y hy
    rw [hQP] at hy
    exact hcov y hy
  · intro e he hed
    exact ⟨(key e he hed).2.2.1, (key e he hed).2.2.2⟩

end CFSG.RankThree.PartTwo.Sec21
