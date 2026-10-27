module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35Conf
public import CFSG.RankThree.PartTwo.KFacts.KS163U35Klein
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35Facts
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Quasithin.Vol2.KGFact12614U35a
import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly.RankThreeEven (projSU)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y : Subgroup G}

namespace Conf684

private theorem exists_eq_conj_of_fix_of_card_nine {E : Subgroup Res3U35.PU5}
    (hEcard : Nat.card E = 9) {σ : MulAut Res3U35.PU5} (hσ : ∀ y ∈ E, σ y = y) :
    ∃ e ∈ E, σ = MulAut.conj e := by
  obtain ⟨g, hg⟩ := Res3U35.exists_conj_eq_E0 hEcard
  let β : MulAut Res3U35.PU5 := MulAut.conj (MulAut.conj g) σ
  have hβfix : ∀ y ∈ Res3U35.E0, β y = y := by
    intro y hy
    have hyE : g⁻¹ * y * g ∈ E := by
      rw [hg (g⁻¹ * y * g)]
      convert hy using 1 <;> group
    have h1 := hσ _ hyE
    change MulAut.conj (MulAut.conj g) σ y = y
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, MulAut.conj_symm_apply]
    rw [h1]
    group
  obtain ⟨B, τ, hBτ⟩ := KFacts.exists_psuConj_mul_psuField (h := Res3U35.hF) (by norm_num) β
  have hτ : τ = 1 := by
    refine CFSG.Quasithin.H13.U35A6.eq_one_of_fix_omega Res3U35.hF Res3U35.om_pow_three
      Res3U35.om_ne_one ?_
    exact CFSG.Quasithin.H13.U35A6.sigma_eq_of_fix Res3U35.hF Res3U35.om_pow_three B τ
      (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 1 0))
      (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 0 1))
  rw [hτ, map_one, mul_one] at hBτ
  obtain ⟨e, he, hβe⟩ := Res3U35.exists_eq_conj_of_fix B
    (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 1 0))
    (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 0 1))
  have hge : g⁻¹ * e * g ∈ E := by
    rw [hg (g⁻¹ * e * g)]
    convert he using 1 <;> group
  refine ⟨g⁻¹ * e * g, hge, ?_⟩
  have hβe' : β = MulAut.conj e := hBτ.trans hβe
  have hβeq : β = (MulAut.conj g) * σ * (MulAut.conj g)⁻¹ := MulAut.conj_apply _ _
  rw [hβe'] at hβeq
  calc σ = (MulAut.conj g)⁻¹ * ((MulAut.conj g) * σ * (MulAut.conj g)⁻¹) *
        MulAut.conj g := by group
    _ = (MulAut.conj g)⁻¹ * MulAut.conj e * MulAut.conj g := by rw [← hβeq]
    _ = MulAut.conj (g⁻¹ * e * g) := by
        rw [← map_inv, ← map_mul, ← map_mul]

theorem exists_eq_conj_of_fix (h : Conf684 A c L Y) (σ : MulAut ↥L)
    (hσ : ∀ l : ↥L, (l : G) ∈ A → σ l = l) :
    ∃ t : ↥L, (t : G) ∈ A ∧ σ = MulAut.conj t := by
  obtain ⟨hLs, -, -, -, -, hT9, -, -⟩ :=
    Res163U35Facts.facts h.sec15R h.mem_y h.case3
  obtain ⟨inst5, ⟨φU⟩⟩ := h.case3.1
  haveI := inst5
  have hUcard : Nat.card ↥(projSU 3 5 1) = 126000 := by
    rw [Nat.card_congr (Res3U35.equivPU).toEquiv, Res3U35.card_PU5]
  haveI : Finite ↥(projSU 3 5 1) :=
    Nat.finite_of_card_ne_zero (by rw [hUcard]; norm_num)
  haveI : Nontrivial ↥(projSU 3 5 1) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; norm_num)
  obtain ⟨ψL⟩ := Res163.nonempty_mulEquiv_of_isSimpleGroup hLs φU
  let ψ : ↥L ≃* Res3U35.PU5 := ψL.trans Res3U35.equivPU
  set T : Subgroup G := A ⊓ L with hTdef
  have hTL : T ≤ L := inf_le_right
  have hT9' : Nat.card T = 9 := hT9
  let E : Subgroup Res3U35.PU5 := (T.subgroupOf L).map ψ.toMonoidHom
  have hEcard : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hT9']
  have hσfixE : ∀ y ∈ E, (MulAut.congr ψ σ) y = y := by
    rintro _ ⟨t, ht, rfl⟩
    have htA : ((t : ↥L) : G) ∈ A :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1
    change ψ (σ (ψ.symm (ψ t))) = ψ t
    rw [MulEquiv.symm_apply_apply, hσ t htA]
  obtain ⟨e, he, heq⟩ := exists_eq_conj_of_fix_of_card_nine hEcard hσfixE
  refine ⟨ψ.symm e, ?_, ?_⟩
  · obtain ⟨x, hxE, hxeq⟩ := Subgroup.mem_map.mp (show e ∈ (T.subgroupOf L).map ψ.toMonoidHom
      from he)
    have ht : ψ.symm e = x := by
      rw [← hxeq]
      exact MulEquiv.symm_apply_apply ψ x
    rw [show ((ψ.symm e : ↥L) : G) = (x : G) from congrArg Subtype.val ht]
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxE)).1
  · apply (MulAut.congr ψ).injective
    change MulAut.congr ψ σ = MulAut.congr ψ (MulAut.conj (ψ.symm e))
    have hcj : MulAut.congr ψ (MulAut.conj (ψ.symm e)) = MulAut.conj e := by
      have h1 : ψ (ψ.symm e) = e := MulEquiv.apply_symm_apply ψ e
      rw [← h1]
      ext z
      simp [MulAut.congr, MulAut.conj_apply]
    rw [hcj]
    exact heq

private theorem eq_one_of_mem_inf_centralizer (h : Conf684 A c L Y) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hRc : R ≤ Subgroup.centralizer ({c} : Set G))
    {r : G} (hrR : r ∈ R) (hrCE : r ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) :
    r = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrN : r ∈ Subgroup.normalizer (L : Set G) :=
    Proof1613.centralizer_le_normalizer_L h.sec15R.toSec14Std (hRc hrR)
  have hσfix : ∀ l : ↥L, (l : G) ∈ A → (L.normalizerMonoidHom ⟨r, hrN⟩) l = l := by
    intro l hlA
    apply Subtype.ext
    change r * (l : G) * r⁻¹ = (l : G)
    have hlE : (l : G) ∈ A ⊓ L := ⟨hlA, l.2⟩
    have hcomm : (l : G) * r = r * (l : G) :=
      Subgroup.mem_centralizer_iff.mp hrCE (l : G) hlE
    rw [← hcomm]
    group
  obtain ⟨t, htA, hσeq⟩ := exists_eq_conj_of_fix h (L.normalizerMonoidHom ⟨r, hrN⟩) hσfix
  have hrt' : r * (t : G) * r⁻¹ = (t : G) := by
    have h1 : (L.normalizerMonoidHom ⟨r, hrN⟩) t = t := by
      rw [hσeq]
      simp [MulAut.conj_apply]
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  have hrt : r * (t : G) = (t : G) * r := by
    have h3 := congrArg (fun x : G => x * r) hrt'
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h3
  set z : G := (t : G)⁻¹ * r with hzdef
  have hcz : z ∈ Subgroup.centralizer ({c} : Set G) := by
    have hct : Commute c (t : G) :=
      h.sec15R.toSec13Data.commute h.sec15R.toSec13Data.mem_A htA
    have hcr : Commute c r := (Subgroup.mem_centralizer_singleton_iff.mp (hRc hrR)).symm
    rw [Subgroup.mem_centralizer_singleton_iff, hzdef]
    exact (hct.inv_right.mul_right hcr).eq.symm
  have hzL : z ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hlL
    have hrl : r * l * r⁻¹ = (t : G) * l * (t : G)⁻¹ := by
      have h1 : (L.normalizerMonoidHom ⟨r, hrN⟩) ⟨l, hlL⟩ =
          MulAut.conj t ⟨l, hlL⟩ := by rw [hσeq]
      have h2 := congrArg Subtype.val h1
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using h2
    have hzl : z * l * z⁻¹ = l := by
      calc z * l * z⁻¹ = (t : G)⁻¹ * (r * l * r⁻¹) * (t : G) := by rw [hzdef]; group
        _ = (t : G)⁻¹ * ((t : G) * l * (t : G)⁻¹) * (t : G) := by rw [hrl]
        _ = l := by group
    calc l * z = (z * l * z⁻¹) * z := by rw [hzl]
      _ = z * l := by group
  have hOdd : Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer (L : Set G))) := h.case3.2.2.2.2.2.2
  have hoddz : Odd (orderOf z) :=
    Odd.of_dvd_nat hOdd (Subgroup.orderOf_dvd_natCard _ ⟨hcz, hzL⟩)
  have ht3 : (t : G) ^ 3 = 1 :=
    h.sec15R.toSec13Data.isElemAbelian.2 (t : G) htA
  have hr_eq : (t : G) * z = r := by rw [hzdef]; group
  have hdiv : orderOf r ∣ orderOf (t : G) * orderOf z := by
    rw [← hr_eq]
    exact ((Commute.refl (t : G)).inv_right.mul_right hrt.symm).orderOf_mul_dvd_mul_orderOf
  have hodd_prod : Odd (orderOf (t : G) * orderOf z) :=
    (Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_iff_pow_eq_one.mpr ht3)).mul hoddz
  have hodd_r : Odd (orderOf r) := Odd.of_dvd_nat hodd_prod hdiv
  by_contra hr1
  have h2dvd : 2 ∣ orderOf r := by
    have hne : (⟨r, hrR⟩ : R) ≠ 1 := fun h1 => hr1 (congrArg Subtype.val h1)
    have h := hR2.dvd_orderOf hne
    rwa [Subgroup.orderOf_mk] at h
  exact (Nat.not_even_iff_odd.mpr hodd_r) (even_iff_two_dvd.mpr h2dvd)

theorem le_of_le_centralizer (h : Conf684 A c L Y) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRc : R ≤ Subgroup.centralizer ({c} : Set G))
    (hAR : A ⊓ L ≤ Subgroup.normalizer (R : Set G)) : R ≤ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE3 : IsPGroup 3 ↥(A ⊓ L) := fun x => ⟨1, Subtype.ext (by
    have h1 := h.sec15R.toSec13Data.isElemAbelian.2 (x : G) (Subgroup.mem_inf.mp x.2).1
    simpa using h1)⟩
  have hRN : R ≤ Subgroup.normalizer (L : Set G) :=
    hRc.trans (Proof1613.centralizer_le_normalizer_L h.sec15R.toSec14Std)
  have hbot : R ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) = ⊥ := by
    rw [← le_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_inf_centralizer h hR2 hRc hr.1 hr.2
  have h3R : ¬ 3 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := 2) (G := R) hR2
    rw [hn]
    intro hdvd
    have h3dvd2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h3dvd2
  have hfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (A ⊓ L) R hE3 h3R hAR
  have hReq : R = ⁅R, A ⊓ L⁆ := hfac.trans (by rw [hbot, sup_bot_eq])
  have hcomm : ⁅R, A ⊓ L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro r hr e he
    have heL : e ∈ L := (Subgroup.mem_inf.mp he).2
    have hre : r * e * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRN hr) e).mp heL
    have hmem := L.mul_mem hre (L.inv_mem heL)
    simpa [commutatorElement_def] using hmem
  rw [hReq]
  exact hcomm

private theorem exists_model_equiv (h : Conf684 A c L Y) :
    ∃ ψ : ↥L ≃* ↥(projSU 3 5 1),
      Nat.card (((A ⊓ L).subgroupOf L).map ψ.toMonoidHom) = 9 := by
  obtain ⟨hLs, -, -, -, -, hT9, -, -⟩ :=
    Res163U35Facts.facts h.sec15R h.mem_y h.case3
  obtain ⟨inst5, ⟨φU⟩⟩ := h.case3.1
  haveI := inst5
  have hUcard : Nat.card ↥(projSU 3 5 1) = 126000 := by
    rw [Nat.card_congr (Res3U35.equivPU).toEquiv, Res3U35.card_PU5]
  haveI : Finite ↥(projSU 3 5 1) :=
    Nat.finite_of_card_ne_zero (by rw [hUcard]; norm_num)
  haveI : Nontrivial ↥(projSU 3 5 1) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; norm_num)
  obtain ⟨ψ⟩ := Res163.nonempty_mulEquiv_of_isSimpleGroup hLs φU
  refine ⟨ψ, ?_⟩
  rw [Subgroup.card_map_of_injective ψ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hT9]

private theorem card_map_subgroupOf {ψ : ↥L ≃* ↥(projSU 3 5 1)} {U : Subgroup G}
    (hUL : U ≤ L) : Nat.card ((U.subgroupOf L).map ψ.toMonoidHom) = Nat.card U := by
  rw [Subgroup.card_map_of_injective ψ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv]

private theorem subgroupOf_le_normalizer {T V : Subgroup G} (hVL : V ≤ L)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    T.subgroupOf L ≤ Subgroup.normalizer (V.subgroupOf L) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hVL]
  intro x hx
  exact hTV hx

private theorem map_subgroupOf_le_normalizer {ψ : ↥L ≃* ↥(projSU 3 5 1)} {T V : Subgroup G}
    (hVL : V ≤ L) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    (T.subgroupOf L).map ψ.toMonoidHom ≤
      Subgroup.normalizer ((V.subgroupOf L).map ψ.toMonoidHom) :=
  (Subgroup.map_mono (subgroupOf_le_normalizer hVL hTV)).trans
    (Subgroup.le_normalizer_map ψ.toMonoidHom)

private theorem eq_of_map_subgroupOf_eq {ψ : ↥L ≃* ↥(projSU 3 5 1)} {U₁ U₂ : Subgroup G}
    (h₁ : U₁ ≤ L) (h₂ : U₂ ≤ L)
    (h : (U₁.subgroupOf L).map ψ.toMonoidHom = (U₂.subgroupOf L).map ψ.toMonoidHom) :
    U₁ = U₂ := by
  have h' : U₁.subgroupOf L = U₂.subgroupOf L := Subgroup.map_injective ψ.injective h
  rw [← Subgroup.map_subgroupOf_eq_of_le h₁, h', Subgroup.map_subgroupOf_eq_of_le h₂]

theorem card_eq_four_of_le (h : Conf684 A c L Y) (hK1 : KFacts.KS163U35InvTwo)
    {V : Subgroup G} (hVL : V ≤ L) (hV2 : IsPGroup 2 V)
    (hAV : A ⊓ L ≤ Subgroup.normalizer (V : Set G)) (hV1 : V ≠ ⊥) :
    Nat.card V = 4 ∧ ∀ W : Subgroup G, W ≤ V →
      A ⊓ L ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = V := by
  obtain ⟨ψ, hEcard₀⟩ := exists_model_equiv h
  let E : Subgroup ↥(projSU 3 5 1) := ((A ⊓ L).subgroupOf L).map ψ.toMonoidHom
  have hEcard : Nat.card E = 9 := hEcard₀
  set V' : Subgroup ↥(projSU 3 5 1) := (V.subgroupOf L).map ψ.toMonoidHom with hV'def
  have hV'2 : IsPGroup 2 V' := hV2.of_equiv
    ((Subgroup.subgroupOfEquivOfLe hVL).symm.trans
      (Subgroup.equivMapOfInjective _ _ ψ.injective))
  have hAV' : E ≤ Subgroup.normalizer (V' : Set ↥(projSU 3 5 1)) :=
    map_subgroupOf_le_normalizer hVL hAV
  have hV'1 : V' ≠ ⊥ := by
    intro hbot
    apply hV1
    have hc : Nat.card V = 1 := by
      rw [← card_map_subgroupOf (ψ := ψ) hVL,
        show (V.subgroupOf L).map ψ.toMonoidHom = V' from hV'def.symm, hbot,
        Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq V hc
  obtain ⟨hcardV', huniq'⟩ := hK1 ⟨Nat.prime_five⟩ E hEcard V' hV'2 hAV' hV'1
  refine ⟨?_, ?_⟩
  · rw [← card_map_subgroupOf (ψ := ψ) hVL,
      show (V.subgroupOf L).map ψ.toMonoidHom = V' from hV'def.symm]
    exact hcardV'
  · intro W hWV hAW
    have hWL : W ≤ L := hWV.trans hVL
    set W' : Subgroup ↥(projSU 3 5 1) := (W.subgroupOf L).map ψ.toMonoidHom with hW'def
    have hW'le : W' ≤ V' := by
      rw [hW'def, hV'def]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hWV)
    have hAW' : E ≤ Subgroup.normalizer (W' : Set ↥(projSU 3 5 1)) :=
      map_subgroupOf_le_normalizer hWL hAW
    rcases huniq' W' hW'le hAW' with hbot | htop
    · left
      have hc : Nat.card W = 1 := by
        rw [← card_map_subgroupOf (ψ := ψ) hWL,
          show (W.subgroupOf L).map ψ.toMonoidHom = W' from hW'def.symm, hbot,
          Subgroup.card_bot]
      exact Subgroup.eq_bot_of_card_eq W hc
    · right
      have hc : Nat.card W = Nat.card V := by
        rw [← card_map_subgroupOf (ψ := ψ) hWL, ← card_map_subgroupOf (ψ := ψ) hVL,
          show (W.subgroupOf L).map ψ.toMonoidHom = W' from hW'def.symm,
          show (V.subgroupOf L).map ψ.toMonoidHom = V' from hV'def.symm, htop]
      exact Subgroup.eq_of_le_of_card_ge hWV hc.ge

theorem nonempty_sup_mulEquiv (h : Conf684 A c L Y) (hK2 : KFacts.KS163U35KleinGen)
    {V₁ V₂ : Subgroup G} (hV₁L : V₁ ≤ L) (hV₂L : V₂ ≤ L) (hV₁2 : IsPGroup 2 V₁)
    (hV₂2 : IsPGroup 2 V₂) (hAV₁ : A ⊓ L ≤ Subgroup.normalizer (V₁ : Set G))
    (hAV₂ : A ⊓ L ≤ Subgroup.normalizer (V₂ : Set G)) (hV₁1 : V₁ ≠ ⊥) (hV₂1 : V₂ ≠ ⊥)
    (hne : V₁ ≠ V₂) : Nonempty (↥(V₁ ⊔ V₂) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨ψ, hEcard₀⟩ := exists_model_equiv h
  let E : Subgroup ↥(projSU 3 5 1) := ((A ⊓ L).subgroupOf L).map ψ.toMonoidHom
  have hEcard : Nat.card E = 9 := hEcard₀
  set V₁' : Subgroup ↥(projSU 3 5 1) := (V₁.subgroupOf L).map ψ.toMonoidHom with hV₁'def
  set V₂' : Subgroup ↥(projSU 3 5 1) := (V₂.subgroupOf L).map ψ.toMonoidHom with hV₂'def
  have hV₁'2 : IsPGroup 2 V₁' := hV₁2.of_equiv
    ((Subgroup.subgroupOfEquivOfLe hV₁L).symm.trans
      (Subgroup.equivMapOfInjective _ _ ψ.injective))
  have hV₂'2 : IsPGroup 2 V₂' := hV₂2.of_equiv
    ((Subgroup.subgroupOfEquivOfLe hV₂L).symm.trans
      (Subgroup.equivMapOfInjective _ _ ψ.injective))
  have hAV₁' : E ≤ Subgroup.normalizer (V₁' : Set ↥(projSU 3 5 1)) :=
    map_subgroupOf_le_normalizer hV₁L hAV₁
  have hAV₂' : E ≤ Subgroup.normalizer (V₂' : Set ↥(projSU 3 5 1)) :=
    map_subgroupOf_le_normalizer hV₂L hAV₂
  have hV₁'1 : V₁' ≠ ⊥ := by
    intro hbot
    apply hV₁1
    have hc : Nat.card V₁ = 1 := by
      rw [← card_map_subgroupOf (ψ := ψ) hV₁L,
        show (V₁.subgroupOf L).map ψ.toMonoidHom = V₁' from hV₁'def.symm, hbot,
        Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq V₁ hc
  have hV₂'1 : V₂' ≠ ⊥ := by
    intro hbot
    apply hV₂1
    have hc : Nat.card V₂ = 1 := by
      rw [← card_map_subgroupOf (ψ := ψ) hV₂L,
        show (V₂.subgroupOf L).map ψ.toMonoidHom = V₂' from hV₂'def.symm, hbot,
        Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq V₂ hc
  have hne' : V₁' ≠ V₂' := by
    intro heq
    exact hne (eq_of_map_subgroupOf_eq hV₁L hV₂L (by
      simpa only [hV₁'def, hV₂'def] using heq))
  have hmain : Nonempty (↥(V₁' ⊔ V₂') ≃* alternatingGroup (Fin 7)) :=
    hK2 ⟨Nat.prime_five⟩ E hEcard V₁' V₂' hV₁'2 hV₂'2 hAV₁' hAV₂' hV₁'1 hV₂'1 hne'
  have hsup' : ((V₁ ⊔ V₂).subgroupOf L).map ψ.toMonoidHom = V₁' ⊔ V₂' := by
    rw [Subgroup.subgroupOf_sup hV₁L hV₂L, Subgroup.map_sup, ← hV₁'def, ← hV₂'def]
  obtain ⟨e⟩ := hmain
  exact ⟨((Subgroup.subgroupOfEquivOfLe (sup_le hV₁L hV₂L)).symm.trans
    (Subgroup.equivMapOfInjective _ _ ψ.injective)).trans (hsup'.symm ▸ e)⟩

private theorem card_sup_of_inf_eq_bot {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hbot : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h := Sec6.card_sup_mul_card_inf hAB
  rw [hbot, Subgroup.card_bot, mul_one] at h
  exact h

theorem eq_of_le_normalizer (h : Conf684 A c L Y) {J₁ J₂ : Subgroup G} (hJ₁L : J₁ ≤ L)
    (hJ₂L : J₂ ≤ L) (hJ₁ : Nonempty (↥J₁ ≃* alternatingGroup (Fin 7)))
    (hJ₂ : Nonempty (↥J₂ ≃* alternatingGroup (Fin 7)))
    (hN : J₁ ≤ Subgroup.normalizer (J₂ : Set G)) : J₁ = J₂ := by
  obtain ⟨-, hLcard, -, -, -, -, -, -⟩ :=
    Res163U35Facts.facts h.sec15R h.mem_y h.case3
  have hcardA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hcardJ₁ : Nat.card J₁ = 2520 := by
    obtain ⟨e⟩ := hJ₁
    rw [Nat.card_congr e.toEquiv, hcardA7]
  have hcardJ₂ : Nat.card J₂ = 2520 := by
    obtain ⟨e⟩ := hJ₂
    rw [Nat.card_congr e.toEquiv, hcardA7]
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  haveI : IsSimpleGroup ↥J₁ := by
    obtain ⟨e⟩ := hJ₁
    exact e.isSimpleGroup
  have hnorm : ((J₁ ⊓ J₂).subgroupOf J₁).Normal := by
    have h1 : (J₂.subgroupOf J₁).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
    have hsub : J₂.subgroupOf J₁ = (J₁ ⊓ J₂).subgroupOf J₁ := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    rwa [hsub] at h1
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((J₁ ⊓ J₂).subgroupOf J₁) with hbot | htop
  · exfalso
    have hinf : J₁ ⊓ J₂ = ⊥ := by
      rw [← le_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.1⟩ : ↥J₁) ∈ (J₁ ⊓ J₂).subgroupOf J₁ :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot] at hx'
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hx')
    have hcard := card_sup_of_inf_eq_bot hN hinf
    have hle : Nat.card (J₁ ⊔ J₂ : Subgroup G) ≤ 126000 := by
      calc Nat.card (J₁ ⊔ J₂ : Subgroup G) ≤ Nat.card L :=
            Subgroup.card_le_of_le (sup_le hJ₁L hJ₂L)
        _ = 126000 := hLcard
    rw [hcard, hcardJ₁, hcardJ₂] at hle
    norm_num at hle
  · have hle : J₁ ≤ J₂ := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥J₁) ∈ (J₁ ⊓ J₂).subgroupOf J₁ := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx')).2
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardJ₂, hcardJ₁])

end Conf684

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
