module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GMod9Mat
public import CFSG.RankThree.PartTwo.Sec12.Hering129GMod9Grp
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item131bProofK
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
public import CFSG.RankThree.PartTwo.Sec12.Hering129Setup

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129G

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem exists_two_element_centralizing {N : Type} [Group N] [Finite N] (T : Subgroup N)
    [T.Normal] (hT3 : ¬ 3 ∣ Nat.card T) {F : Subgroup N} (hF : IsPGroup 3 F) {v : N ⧸ T}
    (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hFv : ∀ f ∈ F, (f : N ⧸ T) * v = v * (f : N ⧸ T)) :
    ∃ w : N, w ≠ 1 ∧ IsPGroup 2 (Subgroup.zpowers w) ∧ ∀ f ∈ F, f * w = w * f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective v
  let α : F →* MulAut N := (MulAut.conj : N →* MulAut N).comp F.subtype
  have hinv : ∀ (a : F) (x : N), g₀⁻¹ * x ∈ T → g₀⁻¹ * α a x ∈ T := by
    intro a x hx
    have h1 : (g₀ : N ⧸ T) = (x : N ⧸ T) := QuotientGroup.eq.mpr hx
    have h2 : (g₀ : N ⧸ T) = ((α a x : N) : N ⧸ T) := by
      change (g₀ : N ⧸ T) = (((a : N) * x * (a : N)⁻¹ : N) : N ⧸ T)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h1,
        eq_mul_inv_iff_mul_eq]
      exact (hFv a a.2).symm
    exact QuotientGroup.eq.mp h2
  obtain ⟨c', hc'T, hc'fix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3
    (A := F) (G := N) hF α T hT3 g₀).2 hinv
  have hmk : (c' : N ⧸ T) = (g₀ : N ⧸ T) := (QuotientGroup.eq.mpr hc'T).symm
  have hn : orderOf c' ≠ 0 := (orderOf_pos c').ne'
  obtain ⟨s, m, hm, hsm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  refine ⟨c' ^ m, ?_, ?_, ?_⟩
  · intro h1
    have h2 : ((c' ^ m : N) : N ⧸ T) = (g₀ : N ⧸ T) := by
      rw [QuotientGroup.mk_pow, hmk]
      obtain ⟨k, rfl⟩ := hm
      rw [pow_succ, pow_mul, hv2, one_pow, one_mul]
    rw [h1, QuotientGroup.mk_one] at h2
    exact hv1 h2.symm
  · have ho : orderOf (c' ^ m) = 2 ^ s := by
      rw [orderOf_pow_of_dvd hm0 (by rw [hsm]; exact Dvd.intro_left _ rfl), hsm,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    exact IsPGroup.of_card (n := s) (by rw [Nat.card_zpowers, ho])
  · intro f hf
    have h1 : α ⟨f, hf⟩ c' = c' := hc'fix ⟨f, hf⟩
    have h2 : f * c' = c' * f := by
      change f * c' * f⁻¹ = c' at h1
      calc f * c' = (f * c' * f⁻¹) * f := by group
        _ = c' * f := by rw [h1]
    exact (show Commute f c' from h2).pow_right m |>.eq

theorem false_of_two_slPi_mod_nine {G : Type} [Group G] [Finite G]
    (hF : partTwoF G = partTwoE G) {c : G} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    {L J : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c) (hJ : J ∈ thetaComponentsAt 3 c)
    (hLJ : L ≠ J) (hcL : c ∈ L) (hcJ : c ∈ J) {q : TauCeti.PrimePower}
    (hq : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card)
    (hJL : Nonempty (J ⧸ aschbacherSolvableCore 3 J ≃* L ⧸ aschbacherSolvableCore 3 L))
    (h9 : PiModNine q.card) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hNdef
  set T : Subgroup N := aschbacherSolvableCore 3 N with hTdef
  obtain ⟨π', K, hKfield, hKPi, hqPi, ⟨φ⟩⟩ : ∃ (π' : Bool) (K : Type) (_ : Field K),
      Sec4.PiField π' q.p q.exponent K ∧ Sec4.ModThree π' (q.p ^ q.exponent) ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Sec4.slPi π' 3 (q.p ^ q.exponent) K) := by
    obtain ⟨K, _, hfin, hcase⟩ := hq
    rw [TauCeti.PrimePower.card_def] at hcase
    rcases hcase with ⟨hK, hq3, ⟨e⟩⟩ | ⟨hK, hq3, ⟨e⟩⟩
    · exact ⟨true, K, inferInstance, ⟨q.prime_p, q.exponent_pos, hK⟩, hq3, ⟨e⟩⟩
    · exact ⟨false, K, inferInstance, ⟨q.prime_p, q.exponent_pos, hK⟩, hq3, ⟨e⟩⟩
  have h9' : 9 ∣ Sec4.qSubPi π' (q.p ^ q.exponent) := by
    rw [← TauCeti.PrimePower.card_def] at hqPi ⊢
    cases π'
    · change q.card % 3 = 2 at hqPi
      change 9 ∣ q.card + 1
      unfold PiModNine at h9
      omega
    · change q.card % 3 = 1 at hqPi
      change 9 ∣ q.card - 1
      unfold PiModNine at h9
      omega
  have hKfin : Finite K := hKPi.finite
  obtain ⟨δ, σ, u, z, hzc, hz1, hz3, hδ, hσ3, hσc, hσδ, hσδc, hu2, hu1, huδ⟩ :=
    exists_data_slPi hKPi h9'
  have hZL : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 :=
    card_center_eq_three_of_isSLThreePi ⟨q.card, hq⟩
  have hZ : Nat.card (Subgroup.center (Sec4.slPi π' 3 (q.p ^ q.exponent) K)) = 3 := by
    rw [← Subgroup.map_center_eq φ, Subgroup.card_map_of_injective φ.injective, hZL]
  obtain ⟨ηL, hηL⟩ := Sec13.exists_lBarEquiv hL
  obtain ⟨ηJ, hηJ⟩ := Sec13.exists_lBarEquiv hJ
  obtain ⟨ψ⟩ := hJL
  let eL : Sec4.slPi π' 3 (q.p ^ q.exponent) K ≃* Sec12.lBar c L := φ.symm.trans ηL
  let eJ : Sec4.slPi π' 3 (q.p ^ q.exponent) K ≃* Sec12.lBar c J :=
    (ψ.trans φ).symm.trans ηJ
  let ι₁ : Sec4.slPi π' 3 (q.p ^ q.exponent) K →* N ⧸ T :=
    (Sec12.lBar c L).subtype.comp eL.toMonoidHom
  let ι₂ : Sec4.slPi π' 3 (q.p ^ q.exponent) K →* N ⧸ T :=
    (Sec12.lBar c J).subtype.comp eJ.toMonoidHom
  have h₁ : Function.Injective ι₁ := Subtype.val_injective.comp eL.injective
  have h₂ : Function.Injective ι₂ := Subtype.val_injective.comp eJ.injective
  have hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a := fun a b =>
    Sec13.Item131bProof.lBar_commute_of_ne hL hJ hLJ (eL a).2 (eJ b).2
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hJc : J ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hcCL : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hcL hLc
  have hcCJ : c ∈ Sec4.thetaQuotCentralizer J := mem_thetaQuotCentralizer_of_central hcJ hJc
  have hne1 : ∀ (X : Subgroup G) (hcX : c ∈ X),
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨c, hcX⟩) ≠ 1 := by
    intro X hcX h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have hord : orderOf (⟨c, hcX⟩ : X) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hc3 hc1
    have hdvd := Subgroup.orderOf_dvd_natCard (aschbacherSolvableCore 3 X) h
    rw [hord] at hdvd
    exact three_not_dvd_card_aschbacherSolvableCore hdvd
  have hζLc : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
    mk_mem_center_of_mem_thetaQuotCentralizer (x := ⟨c, hcL⟩) hcCL
  have hζJc : QuotientGroup.mk' (aschbacherSolvableCore 3 J) ⟨c, hcJ⟩ ∈
      Subgroup.center (J ⧸ aschbacherSolvableCore 3 J) :=
    mk_mem_center_of_mem_thetaQuotCentralizer (x := ⟨c, hcJ⟩) hcCJ
  have hcenter : ∀ {A B : Type} [Group A] [Group B] (e : A ≃* B) {a : A},
      a ∈ Subgroup.center A → e a ∈ Subgroup.center B := by
    intro A B _ _ e a ha
    rw [Subgroup.mem_center_iff] at ha ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, ha g']
  have hζ₁c := hcenter φ hζLc
  have hζ₂c := hcenter (ψ.trans φ) hζJc
  have hζ₁1 : φ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩) ≠ 1 := fun h =>
    hne1 L hcL (φ.injective (h.trans (map_one φ).symm))
  have hζ : ι₁ (φ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩)) =
      ι₂ ((ψ.trans φ) (QuotientGroup.mk' (aschbacherSolvableCore 3 J) ⟨c, hcJ⟩)) := by
    change ((ηL (φ.symm (φ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩))) :
        Sec12.lBar c L) : N ⧸ T) = ((ηJ ((ψ.trans φ).symm ((ψ.trans φ)
          (QuotientGroup.mk' (aschbacherSolvableCore 3 J) ⟨c, hcJ⟩))) : Sec12.lBar c J) : N ⧸ T)
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact (hηL ⟨c, hcL⟩).trans (hηJ ⟨c, hcJ⟩).symm
  obtain ⟨R, F, v, hER, hEF, hFR, hFne, hF27, hv2, hv1, hFv⟩ :=
    exists_R_F_u ι₁ ι₂ h₁ h₂ hcomm hZ hzc hz1 hz3 hδ hσ3 hσc hσδ hσδc hu2 hu1 huδ hζ₁c hζ₂c
      hζ₁1 hζ
  have hRM : R ≤ (⊤ : Subgroup N).map (QuotientGroup.mk' T) := by
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T x
    exact ⟨y, Subgroup.mem_top y, rfl⟩
  obtain ⟨S, -, hSab, hScard, hSR⟩ := Sec13.exists_elemAbelian_map_eq (H := N) (M := ⊤) hER hRM
  have hSp : IsPGroup 3 S := fun x => ⟨1, Subtype.ext (by simpa using hSab.2 x x.2)⟩
  have hinj : Set.InjOn (QuotientGroup.mk' T) (S : Set N) :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hSp
  set F' : Subgroup N := S ⊓ F.comap (QuotientGroup.mk' T) with hF'
  have hF'map : F'.map (QuotientGroup.mk' T) = F := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs.2
    · intro hy
      have hyR : y ∈ R := hFR hy
      rw [← hSR] at hyR
      obtain ⟨s, hs, rfl⟩ := hyR
      exact ⟨s, ⟨hs, hy⟩, rfl⟩
  have hF'card : Nat.card F' = 27 := by
    rw [← hF27, ← hF'map]
    exact (Sec13.card_map_eq_of_injOn (QuotientGroup.mk' T)
      (hinj.mono (fun x hx => (Subgroup.mem_inf.mp hx).1))).symm
  have hF'ab : CFSG.Assembly.IsElemAbelian 3 F' := isElemAbelian_of_le_three hSab inf_le_left
  have hF'p : IsPGroup 3 F' := fun x => ⟨1, Subtype.ext (by simpa using hF'ab.2 x x.2)⟩
  have hT3 : ¬ 3 ∣ Nat.card T := three_not_dvd_card_aschbacherSolvableCore
  obtain ⟨w, hw1, hw2, hwc⟩ := exists_two_element_centralizing T hT3 hF'p hv2 hv1
    (fun f hf => hFv _ (hF'map ▸ Subgroup.mem_map_of_mem (QuotientGroup.mk' T) hf))
  set FG : Subgroup G := F'.map N.subtype with hFG
  set SG : Subgroup G := S.map N.subtype with hSG
  have hFGab : CFSG.Assembly.IsElemAbelian 3 FG :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 N.subtype F' hF'ab
  have hSGab : CFSG.Assembly.IsElemAbelian 3 SG :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 N.subtype S hSab
  have hFGcard : Nat.card FG = 27 := by
    rw [hFG, Subgroup.card_map_of_injective N.subtype_injective, hF'card]
  have hSGcard : Nat.card SG = Nat.card R := by
    rw [hSG, Subgroup.card_map_of_injective N.subtype_injective, hScard]
  have hFGS : FG ≤ SG := Subgroup.map_mono inf_le_left
  have hFGE : FG ∈ partTwoE G := by
    refine ⟨hFGab, hFGcard, (Subgroup.zpowers w).map N.subtype, ?_, hw2.map _, ?_⟩
    · intro hbot
      have hbot' := (Subgroup.map_eq_bot_iff_of_injective (Subgroup.zpowers w)
        N.subtype_injective).mp hbot
      have hwmem : w ∈ (⊥ : Subgroup N) := hbot' ▸ Subgroup.mem_zpowers w
      exact hw1 (Subgroup.mem_bot.mp hwmem)
    · intro g hg
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hg
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : w ^ k * f = f * w ^ k :=
        (Commute.zpow_left (show Commute w f from (hwc f hf).symm) k).eq
      exact congrArg Subtype.val hk
  obtain ⟨A, hSGA, hAmax⟩ :=
    Finite.exists_le_maximal (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hSGab
  have hAF : A ∈ partTwoF G :=
    ⟨hAmax.prop, fun B hB hAB => le_antisymm (hAmax.2 hB hAB) hAB, FG, hFGE, hFGS.trans hSGA⟩
  rw [hF] at hAF
  have h27 : Nat.card A = 27 := hAF.2.1
  have hcardR : 27 < Nat.card R := by
    by_contra hle
    push Not at hle
    exact hFne (Subgroup.eq_of_le_of_card_ge hFR (by omega))
  have := Subgroup.card_le_of_le hSGA
  omega

end CFSG.RankThree.PartTwo.Sec12.Hering129G

