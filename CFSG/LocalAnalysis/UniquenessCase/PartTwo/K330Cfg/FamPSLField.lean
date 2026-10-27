module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
import CFSG.LieType.SeitzGeneration.OuterLinearField
import CFSG.LieType.SeitzGeneration.OuterLinearLift
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open Matrix
open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy mem_fixedBy)
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.RankThree.PartOne.KCLinPlane
open CFSG.LieType.SeitzGeneration
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

private theorem k330c_fixedBy_map_congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (W : Subgroup (MulAut G)) :
    (fixedBy W).map e.toMonoidHom = fixedBy (W.map (MulAut.congr e).toMonoidHom) := by
  have hca : ∀ (f : MulAut G) (x : H), (MulAut.congr e f) x = e (f (e.symm x)) :=
    fun f x => rfl
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine (mem_fixedBy).mpr fun w' hw' => ?_
    rw [Subgroup.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    change (MulAut.congr e w) (e x) = e x
    rw [hca w (e x), e.symm_apply_apply, (mem_fixedBy.mp hx) w hw]
  · intro y hy
    refine ⟨e.symm y, (mem_fixedBy).mpr ?_, e.apply_symm_apply y⟩
    intro w hw
    have h1 := (mem_fixedBy.mp hy) (MulAut.congr e w) (Subgroup.mem_map_of_mem _ hw)
    have h1' : (MulAut.congr e w) y = y := h1
    apply e.injective
    change e (w (e.symm y)) = e (e.symm y)
    rw [← hca w y, h1', e.apply_symm_apply]

private theorem k330c_fixedBy_zpowers_congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (φ : MulAut G) :
    (fixedBy (Subgroup.zpowers φ)).map e.toMonoidHom =
      fixedBy (Subgroup.zpowers (MulAut.congr e φ)) := by
  rw [show Subgroup.zpowers (MulAut.congr e φ) =
      (Subgroup.zpowers φ).map (MulAut.congr e).toMonoidHom from
        (MonoidHom.map_zpowers (MulAut.congr e).toMonoidHom φ).symm]
  exact k330c_fixedBy_map_congr e (Subgroup.zpowers φ)

private theorem k330c_mem_fixedBy_zpowers_iff {J : Type*} [Group J] (f : MulAut J) (x : J) :
    x ∈ fixedBy (Subgroup.zpowers f) ↔ f x = x := by
  rw [mem_fixedBy]
  refine ⟨fun h => h f (Subgroup.mem_zpowers f), fun h w hw => ?_⟩
  have h1 : w • x = x :=
    smul_eq_self_of_mem_zpowers hw (by simpa [MulAut.smul_def] using h)
  simpa [MulAut.smul_def] using h1

private theorem k330c_fieldRigid_congr_fwd {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {φ : MulAut G} (h : FieldRigid φ) : FieldRigid (MulAut.congr e φ) := by
  have hca : ∀ (f : MulAut G) (x : H), (MulAut.congr e f) x = e (f (e.symm x)) :=
    fun f x => rfl
  have hca' : ∀ (f : MulAut H) (x : G), (MulAut.congr e.symm f) x = e.symm (f (e x)) :=
    fun f x => rfl
  have hFχ : ∀ ψ : MulAut H, MulAut.congr e (MulAut.congr e.symm ψ) = ψ := by
    intro ψ
    ext x
    rw [hca (MulAut.congr e.symm ψ) x, hca' ψ (e.symm x)]
    simp
  intro α hα
  set β : MulAut G := MulAut.congr e.symm α with hβ
  have hβfix : ∀ x ∈ fixedBy (Subgroup.zpowers φ), β x = x := by
    intro x hx
    have hx' : e x ∈ fixedBy (Subgroup.zpowers (MulAut.congr e φ)) := by
      rw [← k330c_fixedBy_zpowers_congr e φ]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx
    have h1 := hα (e x) hx'
    rw [hβ, hca' α x, h1, e.symm_apply_apply]
  have hmem : β ∈ Subgroup.zpowers φ := h β hβfix
  have hβ' : MulAut.congr e β = α := by rw [hβ, hFχ α]
  have hmem' : MulAut.congr e β ∈ (Subgroup.zpowers φ).map (MulAut.congr e).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hmem
  rw [hβ', MonoidHom.map_zpowers] at hmem'
  exact hmem'

private theorem k330c_map_conj_fixedBy_congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (φ : MulAut G) (n : H) :
    (fixedBy (Subgroup.zpowers (MulAut.congr e φ))).map (MulAut.conj n).toMonoidHom =
      ((fixedBy (Subgroup.zpowers φ)).map (MulAut.conj (e.symm n)).toMonoidHom).map
        e.toMonoidHom := by
  rw [← k330c_fixedBy_zpowers_congr e φ]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem k330c_fieldPair_congr_fwd {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {φ : MulAut G} (h : FieldPair φ) : FieldPair (MulAut.congr e φ) := by
  intro n hn
  have hne : (fixedBy (Subgroup.zpowers φ)).map (MulAut.conj (e.symm n)).toMonoidHom ≠
      fixedBy (Subgroup.zpowers φ) := by
    intro heq
    apply hn
    have h2 := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) heq
    rw [← k330c_map_conj_fixedBy_congr e φ n, k330c_fixedBy_zpowers_congr e φ] at h2
    exact h2
  have hsup := h (e.symm n) hne
  have h4 := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) hsup
  rw [Subgroup.map_sup, k330c_fixedBy_zpowers_congr e φ,
    ← k330c_map_conj_fixedBy_congr e φ n,
    Subgroup.map_top_of_surjective _ e.surjective] at h4
  exact h4

private theorem k330c_hasFieldRP_of_mulEquiv {J T : Type} [Group J] [Finite J] [Group T]
    [Finite T] (e : J ≃* T) {Q : ℕ} {B : ℕ → ℕ} (h : HasFieldRP T Q B) :
    HasFieldRP J Q B := by
  intro W hW h7
  set F : MulAut J ≃* MulAut T := MulAut.congr e with hF
  have hW' : Nat.card (W.map F.toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective F.injective, hW]
  have h7' : ¬ 7 ∣ Nat.card T := by
    rw [← Nat.card_congr e.toEquiv]
    exact h7
  obtain ⟨g, φ, hφ, hWφ, hrig, hpair, k, hk, hbd⟩ := h (W.map F.toMonoidHom) hW' h7'
  have hca : ∀ (f : MulAut J) (x : T), (MulAut.congr e f) x = e (f (e.symm x)) :=
    fun f x => rfl
  have hca' : ∀ (f : MulAut T) (x : J), (MulAut.congr e.symm f) x = e.symm (f (e x)) :=
    fun f x => rfl
  have hχ : ∀ f : MulAut J, MulAut.congr e.symm (MulAut.congr e f) = f := by
    intro f
    ext x
    rw [hca' (MulAut.congr e f) x, hca f (e x)]
    simp
  refine ⟨MulAut.congr e.symm g, MulAut.congr e.symm φ, ?_, ?_, ?_, ?_, k, hk, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hφ
  · have hW1 : (W.map F.toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = W := by
      rw [Subgroup.map_map]
      rw [show (MulAut.congr e.symm).toMonoidHom.comp F.toMonoidHom = MonoidHom.id _ from by
        ext x
        simpa [hF] using hχ x]
      exact Subgroup.map_id W
    have hW2 : (((Subgroup.zpowers φ).map (MulAut.conj g).toMonoidHom).map
        (MulAut.congr e.symm).toMonoidHom) =
        (Subgroup.zpowers (MulAut.congr e.symm φ)).map
          (MulAut.conj (MulAut.congr e.symm g)).toMonoidHom := by
      rw [Subgroup.map_map, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      congr 1
      ext y
      simp [MulAut.conj_apply]
    have hcongr := congrArg (fun S : Subgroup (MulAut T) =>
      S.map (MulAut.congr e.symm).toMonoidHom) hWφ
    rw [hW1, hW2] at hcongr
    exact hcongr
  · exact k330c_fieldRigid_congr_fwd e.symm hrig
  · exact k330c_fieldPair_congr_fwd e.symm hpair
  · have hcard : Nat.card (fixedBy (Subgroup.zpowers (MulAut.congr e.symm φ))) =
        Nat.card (fixedBy (Subgroup.zpowers φ)) := by
      rw [← k330c_fixedBy_zpowers_congr e.symm φ]
      exact Subgroup.card_map_of_injective e.symm.injective
    rw [hcard]
    exact hbd

private theorem k330c_seven_dvd_card_projectiveSL {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (h7 : 7 ∣ Nat.card K) : 7 ∣ Nat.card (projectiveSL n K) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hN : 1 ≤ n * (n - 1) / 2 := by
    rw [Nat.one_le_div_iff (by norm_num)]
    have : 2 ≤ n - 1 ∨ n = 2 := by omega
    rcases this with h | rfl
    · nlinarith
    · norm_num
  have hSL := card_SL_eq (K := K) (n := n) (by omega)
  have hsplit := (scalars n K).card_eq_card_quotient_mul_card_subgroup
  have hZ := card_scalars_dvd (K := K) (n := n) (by omega)
  have hrSL : 7 ∣ Nat.card (SpecialLinearGroup (Fin n) K) := by
    rw [hSL]
    exact Dvd.dvd.mul_right (h7.trans (dvd_pow_self _ (by omega))) _
  have hcop : Nat.Coprime 7 (Nat.card (scalars n K)) := by
    have h1 : Nat.Coprime 7 (Nat.card K - 1) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr fun hd => ?_
      have : 7 ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h7 hd
      rw [Nat.sub_sub_self hq1.le] at this
      exact Nat.prime_seven.one_lt.ne' (Nat.dvd_one.mp this)
    exact Nat.Coprime.coprime_dvd_right hZ h1
  rw [hsplit] at hrSL
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop hrSL

private theorem k330c_card_projectiveSL_le_sltBound {n : ℕ} (hn : n = 4 ∨ n = 5)
    {K : Type} [Field K] [Finite K] :
    Nat.card (projectiveSL n K) ≤ sltBound n (Nat.card K) := by
  have hn1 : 1 ≤ n := by omega
  have h1 : Nat.card (projectiveSL n K) ≤ Nat.card (SpecialLinearGroup (Fin n) K) := by
    rw [card_projectiveSL]
    exact Nat.div_le_self _ _
  refine h1.trans ?_
  rw [card_SL_eq hn1]
  rcases hn with rfl | rfl
  · rw [sltBound]
    have hprod : (∏ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1)) ≤
        Nat.card K ^ (∑ j ∈ Finset.Icc 2 4, j) := by
      rw [← Finset.prod_pow_eq_pow_sum (Finset.Icc 2 4) (fun j => j) (Nat.card K)]
      exact Finset.prod_le_prod fun j _ => Nat.sub_le _ _
    have hsum : (∑ j ∈ Finset.Icc 2 4, j) = 9 := by decide +kernel
    rw [hsum] at hprod
    calc Nat.card K ^ (4 * (4 - 1) / 2) * ∏ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1)
        ≤ Nat.card K ^ 6 * Nat.card K ^ 9 := by
          rw [show 4 * (4 - 1) / 2 = 6 by norm_num]
          exact Nat.mul_le_mul_left _ hprod
      _ = Nat.card K ^ (4 ^ 2 - 1) := by
          rw [show 4 ^ 2 - 1 = 6 + 9 by norm_num, ← pow_add]
  · rw [sltBound]
    have hprod : (∏ j ∈ Finset.Icc 2 5, (Nat.card K ^ j - 1)) ≤
        Nat.card K ^ (∑ j ∈ Finset.Icc 2 5, j) := by
      rw [← Finset.prod_pow_eq_pow_sum (Finset.Icc 2 5) (fun j => j) (Nat.card K)]
      exact Finset.prod_le_prod fun j _ => Nat.sub_le _ _
    have hsum : (∑ j ∈ Finset.Icc 2 5, j) = 14 := by decide +kernel
    rw [hsum] at hprod
    calc Nat.card K ^ (5 * (5 - 1) / 2) * ∏ j ∈ Finset.Icc 2 5, (Nat.card K ^ j - 1)
        ≤ Nat.card K ^ 10 * Nat.card K ^ 14 := by
          rw [show 5 * (5 - 1) / 2 = 10 by norm_num]
          exact Nat.mul_le_mul_left _ hprod
      _ = Nat.card K ^ (5 ^ 2 - 1) := by
          rw [show 5 ^ 2 - 1 = 10 + 14 by norm_num, ← pow_add]

private theorem k330c_fixedBy_sup_conj_eq_top {n : ℕ}
    {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K}
    (hfix : fixedBy (Subgroup.zpowers (fieldAut n K σ)) =
      (linearSubfieldInclusion n k).range)
    (hn : 3 ≤ n) (hK : Nat.card K = Nat.card k ^ 7) (x : projectiveSL n K)
    (hne : (fixedBy (Subgroup.zpowers (fieldAut n K σ))).map (MulAut.conj x).toMonoidHom ≠
      fixedBy (Subgroup.zpowers (fieldAut n K σ))) :
    fixedBy (Subgroup.zpowers (fieldAut n K σ)) ⊔
      (fixedBy (Subgroup.zpowers (fieldAut n K σ))).map (MulAut.conj x).toMonoidHom = ⊤ := by
  obtain ⟨g, hg⟩ := proj_surjective n K x
  set M : GL (Fin n) K := SpecialLinearGroup.toGL g with hM
  have hconj : MulAut.conj x = conjAut n K M := by
    rw [hM, ← hg]
    exact (CFSG.LieType.SeitzGeneration.conjAut_toGL g).symm
  have hmap : (fixedBy (Subgroup.zpowers (fieldAut n K σ))).map
        (MulAut.conj x).toMonoidHom =
      ((slSub n k).map (slConjugation n K M).toMonoidHom).map (proj n K) := by
    rw [hfix, hconj]
    exact map_conjAut_range_linearSubfieldInclusion k M
  have hne' : (slSub n k).map (slConjugation n K M).toMonoidHom ≠ slSub n k := by
    intro h
    apply hne
    rw [hmap, h, ← range_linearSubfieldInclusion_eq_map, ← hfix]
  have hgen := pairSL_closure Nat.prime_seven (by norm_num) hK hn M hne'
  have h4 := congrArg (Subgroup.map (proj n K)) hgen
  rw [map_closure_union, Subgroup.map_top_of_surjective _ (proj_surjective n K)] at h4
  rw [hmap, hfix, range_linearSubfieldInclusion_eq_map]
  rw [← Subgroup.sup_eq_closure] at h4
  exact h4

private theorem k330c_hasFieldRP_projectiveSL {n : ℕ}
    (hn : n = 4 ∨ n = 5) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    HasFieldRP (projectiveSL n K) (p ^ f) (sltBound n) := by
  have hn3 : 3 ≤ n := by omega
  intro W hW h7
  have hcyc : IsCyclic ↥W := isCyclic_of_prime_card hW
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hordg : orderOf g = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hW]
  set a : MulAut (projectiveSL n K) := (g : MulAut (projectiveSL n K)) with ha
  have haord : orderOf a = 7 := by rw [ha, Subgroup.orderOf_coe, hordg]
  have ha7 : a ^ 7 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
  have hWz : W = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le, ha]
      exact g.2
    · rw [hW, Nat.card_zpowers, haord]
  have haE : a ∈ semilinearAutGroup n K :=
    mem_semilinearAutGroup_of_pow_eq_one hn3 Nat.prime_seven (by norm_num) ha7
  have hcop7 : Nat.Coprime 7 (Nat.gcd n (Nat.card K - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr fun hd => ?_
    have h7n : 7 ∣ n := hd.trans (Nat.gcd_dvd_left n _)
    rcases hn with rfl | rfl <;> norm_num at h7n
  have haD : a ∉ linearAutGroup n K := by
    intro hD
    obtain ⟨t, ht⟩ := KCLinPlane.inner_of_mem_linearAut_of_pow_eq_one hn3 hcop7 hD ha7
    have hdvd : 7 ∣ Nat.card (projectiveSL n K) := by
      rw [← haord, ← ht]
      exact (orderOf_map_dvd (MulAut.conj :
        projectiveSL n K →* MulAut (projectiveSL n K)) t).trans (orderOf_dvd_natCard t)
    exact h7 hdvd
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨f', hℓ, hcardf'⟩ := FiniteField.card K (ringChar K)
  have hf' : 1 ≤ (f' : ℕ) := f'.pos
  have hK' : Nat.card K = ringChar K ^ (f' : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf']
  have hp7 : p ≠ 7 := by
    intro hp7
    apply h7
    have h7K : 7 ∣ Nat.card K := by
      rw [hK, hp7]; exact dvd_pow_self 7 (by omega)
    exact k330c_seven_dvd_card_projectiveSL (n := n) (by omega) h7K
  have hchar : ringChar K = p := by
    have hp_dvd' : p ∣ ringChar K ^ (f' : ℕ) := by
      rw [← hK', hK]; exact dvd_pow_self p (by omega)
    exact ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hp_dvd')).symm
  have hne7 : (7 : ℕ) ≠ ringChar K := by
    rw [hchar]; exact fun h => hp7 h.symm
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    (K := K) (n := n) (ℓ := ringChar K) (f := (f' : ℕ)) hℓ hf' hn3 hK'
  obtain ⟨h7f, σ, hσ, ⟨h, _hhD, haeq⟩, hfix⟩ :=
    hdesc.2.2.2.2.2.2.2 7 Nat.prime_seven hne7 a haE haD haord
  set kq : Subfield K := semilinearFixedSubfield σ with hkq
  have hcopn : Nat.Coprime n 7 := by
    rcases hn with rfl | rfl <;> norm_num
  have hcentral := higher_linear_prime_subfield_fixed_group_and_full_centralizer hℓ
    Nat.prime_seven hne7 hf' hn3 hcopn hK' σ hσ
  have hfixedeq : {x : projectiveSL n K | fieldAut n K σ x = x} =
      ((linearSubfieldInclusion n kq).range : Set (projectiveSL n K)) := hcentral.2.1
  have hfixing : fixingSubgroup (MulAut (projectiveSL n K))
      ((linearSubfieldInclusion n kq).range : Set (projectiveSL n K)) =
      Subgroup.zpowers (fieldAut n K σ) := hcentral.2.2.1
  have hF : fixedBy (Subgroup.zpowers (fieldAut n K σ)) =
      (linearSubfieldInclusion n kq).range := by
    ext x
    rw [k330c_mem_fixedBy_zpowers_iff]
    exact Set.ext_iff.mp hfixedeq x
  have hrig : FieldRigid (fieldAut n K σ) := by
    intro α hα
    rw [← hfixing, mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ fixedBy (Subgroup.zpowers (fieldAut n K σ)) := by rw [hF]; exact hy
    simpa [MulAut.smul_def] using hα y hy'
  have hKk : Nat.card K = Nat.card kq ^ 7 := by
    rw [hkq, hfix, ← pow_mul, Nat.div_mul_cancel h7f]
    exact hK'
  have hpair : FieldPair (fieldAut n K σ) := by
    intro x hne
    exact k330c_fixedBy_sup_conj_eq_top hF hn3 hKk x hne
  have hk7 : Nat.card kq ^ 7 = p ^ f := by rw [← hKk, hK]
  have hbound : Nat.card (fixedBy (Subgroup.zpowers (fieldAut n K σ))) ≤
      sltBound n (Nat.card kq) := by
    have hcardrange : Nat.card (fixedBy (Subgroup.zpowers (fieldAut n K σ))) =
        Nat.card (projectiveSL n kq) := by
      rw [hF, MonoidHom.range_eq_map,
        Subgroup.card_map_of_injective (linearSubfieldInclusion_injective (by omega) kq),
        Subgroup.card_top]
    rw [hcardrange]
    exact k330c_card_projectiveSL_le_sltBound hn
  refine ⟨h, fieldAut n K σ, ?_, ?_, hrig, hpair, Nat.card kq, hk7, hbound⟩
  · rw [orderOf_fieldAut hn3 σ, hσ]
  · rw [hWz, haeq, MonoidHom.map_zpowers]
    rfl

theorem hasFieldRP_PSL (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type}
    [Group J] [Finite J] {p f : ℕ} (e : LieModel J .PSL n p f) :
    HasFieldRP J (p ^ f) (sltBound n) := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eiso⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel e
  have hadm := e.admissible
  obtain ⟨hp, hf, -⟩ := hadm
  haveI := hKfin
  exact k330c_hasFieldRP_of_mulEquiv eiso (k330c_hasFieldRP_projectiveSL hn hp hf hKcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
