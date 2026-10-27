module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeTypes
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeOddAct
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeHyp
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSimple
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.GroupTheory.TwoElementSquare
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2Odd
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.GH74.GLS.IVK.L2.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

namespace AscBridge

variable {G : Type} [Group G] [Finite G]
variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P X : Subgroup G}

theorem mk_mem_normalizer_rAlpha {u : ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))}
    (hu : (u : G) ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) : Set G)) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))
      u ∈ Subgroup.normalizer (SetLike.coe (rAlpha M X T c)) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨r, hr, rfl⟩ := hz
  refine ⟨u * r * u⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hu r).mp (Subgroup.mem_subgroupOf.mp hr)

theorem kAlpha_inf_rAlpha_eq_bot_of_isSimpleGroup (hset : Setting204 G A M L N c T i j P)
    (hKY : kTwenty M c ≤ yTwenty X c)
    [IsSimpleGroup ↥(kToYAlpha (T := T) hKY).range]
    (hnab : ∃ a b : ↥(kToYAlpha (T := T) hKY).range, a * b ≠ b * a) :
    kAlpha M X T c ⊓ rAlpha M X T c = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := kToYAlpha (T := T) hKY with hψ
  set ι : ↥ψ.range →* _ := (yAlpha M X T c).subtype.comp ψ.range.subtype with hι
  have hι_inj : Function.Injective ι :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hιrange : ι.range = kAlpha M X T c := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype, map_range_kToYAlpha]
  have hKR : kTwenty M c ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  set W := (rAlpha M X T c).comap ι with hWdef
  have hWn : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    rw [hWdef, Subgroup.mem_comap] at hw ⊢
    have hg : ι g ∈ kAlpha M X T c := hιrange ▸ ⟨g, rfl⟩
    obtain ⟨k, hk, hkg⟩ := hg
    have hgN : ι g ∈ Subgroup.normalizer (SetLike.coe (rAlpha M X T c)) := by
      rw [← hkg]
      exact mk_mem_normalizer_rAlpha (hKR (Subgroup.mem_subgroupOf.mp hk))
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hw
  have hR2 : IsPGroup 2 (rAlpha M X T c) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype
      (K := yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map _
  have hW2 : IsPGroup 2 W := hR2.comap_of_injective ι hι_inj
  have hWbot := CFSG.eq_bot_of_normal_isPGroup_of_isSimpleGroup hnab hW2
  rw [eq_bot_iff]
  rintro z ⟨hzK, hzR⟩
  rw [← hιrange] at hzK
  obtain ⟨w, rfl⟩ := hzK
  have hw : w ∈ W := hzR
  rw [hWbot, Subgroup.mem_bot] at hw
  rw [hw, map_one]
  exact Subgroup.one_mem _

theorem five_or_seven_of_mul_sq_sub_one {q : ℕ} :
    (q * (q ^ 2 - 1) = 120 → q = 5) ∧ (q * (q ^ 2 - 1) = 336 → q = 7) := by
  have hle : ∀ n, n * (n ^ 2 - 1) ≤ 336 → n ≤ 7 := by
    intro n hn
    by_contra h
    push Not at h
    have h8 : 8 * (8 ^ 2 - 1) ≤ n * (n ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    norm_num at h8
    omega
  constructor
  · intro h
    have := hle q (by omega)
    interval_cases q <;> simp_all
  · intro h
    have := hle q (by omega)
    interval_cases q <;> simp_all

section Rank


theorem le_two_of_yAlpha_mulEquiv_L2 (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 1 ≤ e)
    (eY : ↥(yAlpha M X T c) ≃* projSL 2 (GaloisField p e)) : e ≤ 2 := by
  have hp := (Fact.out : p.Prime)
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 2 p e := by
    refine ⟨hp, he, le_rfl, fun h => ?_, fun h => ?_⟩
    · have h2 : p ^ e = 2 := congrArg Prod.snd h
      have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
      omega
    · have h3 : p ^ e = 3 := congrArg Prod.snd h
      have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
      omega
  have hmod := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm eY
  have hrk := pRank_yAlpha_le_two hset hX hnab hp hp5
  obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank (by omega) hmod
  rcases h with ⟨-, ⟨-, h⟩ | ⟨h3, -⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  · omega
  · omega
  · omega
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · omega

end Rank

end AscBridge

section Main


open AscBridge L2OddGroup CFSG.GH74.GLS.IVK in
theorem step204AscL2Odd_holds : Step204AscL2Odd := by
  intro G _ _ A M L N c T i j P hset X hX _ hm _ hYK ⟨p, e, hpF, hp2, hp3, he, ⟨eY⟩⟩
  have hp : p.Prime := hpF.out
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    push Not at h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  obtain ⟨hs, hnab⟩ := isSimpleGroup_yAlpha hset hX hm
  haveI := hs
  haveI := yAlpha_normal hX
  have hinj := conjNormal_yAlpha_injective hX hnab
  have he2 := le_two_of_yAlpha_mulEquiv_L2 hset hX hnab hp5 he eY
  have hFcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hF : L2Field (GaloisField p e) := by
    refine ⟨?_, ?_⟩
    · rw [hFcard]
      exact (hp.odd_of_ne_two hp2).pow
    · rw [hFcard]
      have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
      omega
  set eL : ↥(yAlpha M X T c) ≃* L2 (GaloisField p e) :=
    eY.trans ((Sec4.projSLEquivPSL (GaloisField p e)).trans
      (L2.equivPSL (GaloisField p e)).symm) with heL
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKY : kTwenty M c ≤ yTwenty X c :=
    Res6.kTwenty_le_yTwenty hset (le_sup_left.trans hKTX)
  set ψ := kToYAlpha (T := T) hKY with hψ
  have hKperf := isPerfect_range_kToYAlpha hset hKY
  have hK1 := range_kToYAlpha_ne_bot hset hKY
  obtain ⟨φ, hφ⟩ := exists_surjective_kBar hset hKY
  obtain ⟨hKs, -, hKcard⟩ :=
    isSimpleGroup_and_card_of_surjective hF eL hKperf hK1 φ hφ hset.kType.symm
  have hKnab : ∃ a b : ↥ψ.range, a * b ≠ b * a := by
    obtain ⟨k, hk⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK1
    haveI := hKperf
    exact exists_mul_ne_mul_of_isPerfect (MonoidHom.id _) hk
  haveI := hKs
  have hKR := kAlpha_inf_rAlpha_eq_bot_of_isSimpleGroup hset hKY hKnab
  have hcomm := commute_of_kAlpha_inf_rAlpha_eq_bot hset hKR
  have hfix := range_le_fixedSubgroup_of_commute hKY hcomm
  have hR2 : IsPGroup 2 (rAlpha M X T c) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype
      (K := yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map _
  have hD : rAlpha M X T c ⊓ yAlpha M X T c = ⊥ := by
    by_contra hne
    have hD2 : IsPGroup 2 ↥(rAlpha M X T c ⊓ yAlpha M X T c) := hR2.to_inf_left
    haveI : Nontrivial ↥(rAlpha M X T c ⊓ yAlpha M X T c) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    obtain ⟨n, hn, hcard⟩ := hD2.nontrivial_iff_card.mp inferInstance
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(rAlpha M X T c ⊓
      yAlpha M X T c)) 2 (hcard ▸ dvd_pow_self 2 hn.ne')
    set u := Subtype.val x with hudef
    have huR : u ∈ rAlpha M X T c := (Subgroup.mem_inf.mp x.2).1
    have huY : u ∈ yAlpha M X T c := (Subgroup.mem_inf.mp x.2).2
    have hu2 : orderOf u = 2 := by
      rw [hudef, Subgroup.orderOf_coe]
      exact hx
    have hv := conjNormal_eq_conj (⟨u, huY⟩ : ↥(yAlpha M X T c))
    have hvi : MulAut.conjNormal (H := yAlpha M X T c) u ∈ innDiagSub eL := by
      rw [hv]
      exact innAut_le_innDiagSub eL ⟨_, rfl⟩
    have hv2 : orderOf (MulAut.conjNormal (H := yAlpha M X T c) u) = 2 := by
      rw [orderOf_injective _ hinj u]
      exact hu2
    exact hK1 (eq_bot_of_isPerfect_of_le_fixedSubgroup hF eL hvi hv2 hKperf
      (hfix _ ⟨u, huR, rfl⟩))
  set R' := (rAlpha M X T c).map (MulAut.conjNormal (H := yAlpha M X T c)) with hR'def
  have hR'inn := rAut_inf_innAut_eq_bot hX hnab hD
  have hR'2 : IsPGroup 2 R' := hR2.map _
  obtain ⟨hR'diag, hR'cyc, hR'dvd⟩ :=
    isCyclic_of_fixes_isPerfect hF eL hR'2 hR'inn hKperf hK1 hfix
  obtain ⟨-, -, -, -, hGal, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp he
      hFcard
  rw [hGal] at hR'dvd
  have hR'1 : R' ≠ ⊥ := by
    intro h
    apply rAlpha_ne_bot hset hX hYK
    rwa [hR'def, Subgroup.map_eq_bot_iff_of_injective _ hinj] at h
  obtain ⟨k, hk⟩ := hR'2.exists_card_eq
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exfalso
        apply hR'1
        rw [pow_zero] at hk
        exact Subgroup.card_eq_one.mp hk
      · rfl
    · exfalso
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have := Nat.le_of_dvd (by omega) (hk ▸ hR'dvd)
      omega
  subst hk1
  have he' : e = 2 := by
    have := hk ▸ hR'dvd
    rw [pow_one] at this
    omega
  have hR'card : Nat.card R' = 2 := by rw [hk, pow_one]
  haveI : Nontrivial ↥R' := (Subgroup.nontrivial_iff_ne_bot _).mpr hR'1
  obtain ⟨⟨u, huR'⟩, hu1⟩ := exists_ne (1 : ↥R')
  have hu2 : orderOf u = 2 := by
    have hdvd : orderOf (⟨u, huR'⟩ : ↥R') ∣ 2 := by
      have h := orderOf_dvd_natCard (⟨u, huR'⟩ : ↥R')
      rwa [hR'card] at h
    rw [Subgroup.orderOf_mk] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      apply hu1
      rw [orderOf_eq_one_iff] at h
      exact Subtype.ext h
    · exact h
  have hud : u ∉ innDiagSub eL := by
    intro h
    have h' : u ∈ R' ⊓ innDiagSub eL := ⟨huR', h⟩
    rw [hR'diag, Subgroup.mem_bot] at h'
    exact hu1 (Subtype.ext h')
  obtain ⟨r, hr, rfl⟩ := huR'
  have hr2 : orderOf r = 2 := by
    rw [← orderOf_injective _ hinj r]
    exact hu2
  have hRgen : Subgroup.zpowers r = rAlpha M X T c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hr) ?_
    rw [Nat.card_zpowers, hr2, ← Subgroup.card_map_of_injective hinj]
    exact hR'card.le
  have hn : ∀ y ∈ CFSG.GH74.GLS.fixedSubgroup ↥(yAlpha M X T c)
      (MulAut.conjNormal (H := yAlpha M X T c) r), ∀ l ∈ ψ.range, y * l * y⁻¹ ∈ ψ.range := by
    intro y hy l hl
    have hry := commute_of_mem_fixedSubgroup hy
    have hyN : Subtype.val y ∈ Subgroup.normalizer (SetLike.coe (rAlpha M X T c)) := by
      rw [← hRgen]
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hc : Commute (Subtype.val y) r := hry.symm
      rw [(hc.zpow_right n).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers r n
    have hyK := normalizer_rAlpha_le_normalizer_kAlpha hset hX hyN
    have hlK : Subtype.val l ∈ kAlpha M X T c := by
      rw [← map_range_kToYAlpha hKY]
      exact ⟨l, hl, rfl⟩
    have hmem := (Subgroup.mem_normalizer_iff.mp hyK _).mp hlK
    rw [← map_range_kToYAlpha hKY] at hmem
    obtain ⟨l', hl', hl'e⟩ := hmem
    have hl'eq : l' = y * l * y⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hl'e)
    rw [← hl'eq]
    exact hl'
  have h2card := two_mul_card_of_isPerfect_of_normal_fixedSubgroup hF eL hp
    (hFcard.trans (by rw [he'])) hu2 hud hKperf hK1 (hfix _ ⟨r, hr, rfl⟩) hn
  have hp57 : p = 5 ∨ p = 7 := by
    have harith := @five_or_seven_of_mul_sq_sub_one p
    rcases hKcard with h | h
    · exact Or.inl (harith.1 (by rw [← h2card, h]))
    · exact Or.inr (harith.2 (by rw [← h2card, h]))
  subst he'
  obtain ⟨G₀, hG₀⟩ := exists_minimal_coverYR M X T c
  obtain ⟨hhyp, Ψ, hS, hL⟩ := hyp1411_of_simple hset hX hnab hG₀
  have hLiso : Nonempty ((perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) ≃*
      projSL 2 (GaloisField p 2)) :=
    ⟨(Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      ((MulEquiv.subgroupCongr hL).trans eY)⟩
  have hRcyc : IsCyclic ↥(rAlpha M X T c) := by
    have e₂ : ↥(rAlpha M X T c) ≃* ↥R' :=
      Subgroup.equivMapOfInjective _ (MulAut.conjNormal (H := yAlpha M X T c)) hinj
    exact isCyclic_of_surjective e₂.symm.toMonoidHom e₂.symm.surjective
  have hScyc : IsCyclic ↥(((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))) := by
    have e₁ := (Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      (MulEquiv.subgroupCongr hS)
    exact isCyclic_of_surjective e₁.symm.toMonoidHom e₁.symm.surjective
  obtain ⟨i₁, i₂, h12, h1, h2, hn1, hn2⟩ := asc82Item1411_L2_25_49 ↥G₀ _ _ hhyp hp57 hLiso hScyc
  exact covered_of_fourChar_normal hset hX
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1 hG₀ h12 h1 h2 hn1 hn2

end Main

end CFSG.RankThree.PartTwo.Sec20
