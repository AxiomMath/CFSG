module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKFacts
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCentralizer
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ChevTwoL2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GorensteinWalter
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)

theorem conj_injective_of_center_eq_bot {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) : Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyc : y ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut X => φ g) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rw [hZ, Subgroup.mem_bot] at hyc
  exact hyc

theorem card_psl2_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (PSL2 F) = 6 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by
    simpa [Nat.card_eq_fintype_card] using hF)
  have hneg : (-1 : F) = 1 := by
    apply (neg_eq_iff_add_eq_zero).2
    have h2 : (1 : F) + 1 = 0 := by
      rw [show (1 : F) + 1 = 2 by norm_num]
      exact CharP.cast_eq_zero F 2
    exact h2
  have h := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hneg, hF] at h
  simpa using h

theorem isCyclic_of_two_pow_card_dvd_six {G : Type*} [Group G] [Finite G] {k : ℕ}
    (hk : Nat.card G = 2 ^ k) (hd : Nat.card G ∣ 6) : IsCyclic G := by
  have hcard : Nat.card G = 1 ∨ Nat.card G = 2 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> simp [hk]
    · exfalso
      have h4 : 4 ∣ Nat.card G := by
        rw [hk]
        exact (by norm_num : (4 : ℕ) = 2 ^ 2) ▸ pow_dvd_pow 2 hk2
      have h46 := Nat.dvd_trans h4 hd
      norm_num at h46
  rcases hcard with h1 | h2
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

theorem eqLocus_mulEquiv_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) :
    Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id X) ≃*
      (MulAut.congr e α).toMonoidHom.eqLocus (MonoidHom.id Y)) := by
  set β := MulAut.congr e α with hβ
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id X)).map e.toMonoidHom =
      β.toMonoidHom.eqLocus (MonoidHom.id Y) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : α y = y := hy
      show e (α (e.symm (e y))) = e y
      rw [MulEquiv.symm_apply_apply, hy']
    · intro hz
      have hz' : e (α (e.symm z)) = z := hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      show α (e.symm z) = e.symm z
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact hz'
  exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)⟩

theorem isCyclic_of_le_centralizer_psl2 {X : Type} [Group X] [Finite X] {K : Type} [Field K]
    [Finite K] {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (e : X ≃* PSL2 K) {x : X}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {U : Subgroup X} (hU : ∀ u ∈ U, x * u = u * x) :
    IsCyclic U := by
  have hne : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  have hpow : (e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (e x) = 3 := orderOf_eq_prime hpow hne
  have hodd : Odd (orderOf (e x)) := by rw [hord]; exact ⟨1, rfl⟩
  have hcyc := (CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_odd_element_full_centralizer
    m hm hK (e x) hne hodd).1
  have hle : U.map e.toMonoidHom ≤ Subgroup.centralizer ({e x} : Set (PSL2 K)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show e x * e u = e u * e x
    rw [← map_mul e, ← map_mul e, hU u hu]
  haveI : IsCyclic (U.map e.toMonoidHom) := Subgroup.isCyclic_of_le hle
  exact isCyclic_of_injective (U.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    (U.equivMapOfInjective e.toMonoidHom e.injective).injective

theorem subsingleton_of_quasisimple_centralizer {X : Type} [Group X] (C R U : Subgroup X)
    (hQ : CFSG.IsQuasisimple C) (hZ : Subgroup.center C = ⊥) (hRC : R ≤ C)
    (hRnorm : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R) (hUR : U ≤ R)
    (h3C : 3 ∣ Nat.card C) (hdivR : ¬ 3 ∣ Nat.card R) : Subsingleton U := by
  have hN : (R.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hRnorm g g.2 n hn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hN with htop | hle
  · exfalso
    have hCR : C ≤ R := fun c hc => by
      have hmem : (⟨c, hc⟩ : C) ∈ R.subgroupOf C := by rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    exact hdivR (dvd_trans h3C (Subgroup.card_dvd_of_le hCR))
  · have hu : ∀ u : U, (u : X) = 1 := by
      intro u
      have hmem : (⟨u, hRC (hUR u.2)⟩ : C) ∈ R.subgroupOf C :=
        Subgroup.mem_subgroupOf.mpr (hUR u.2)
      have h1 := hle hmem
      rw [hZ, Subgroup.mem_bot] at h1
      simpa using congrArg Subtype.val h1
    exact ⟨fun a b => Subtype.ext (by rw [hu a, hu b])⟩

theorem kChevTwoCentralizer_psl2 (m : ℕ) (hm : 1 ≤ m) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      Nonempty (X ≃* projSL 2 (GaloisField 2 m)) →
        ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ _ ⟨e0⟩ β hβ hdef
  obtain ⟨W, V, _, hW3, hWinn, hβW, hnorm, hVW, hV2, hVnc⟩ := hdef
  classical
  have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  let e : X ≃* PSL2 (GaloisField 2 m) :=
    e0.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 m))
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e (psl2_center_eq_bot _)
  have hinj := conj_injective_of_center_eq_bot hZ
  have hβ3 : β ^ 3 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  set R : Subgroup X := W.comap (MulAut.conj : X →* MulAut X) with hRdef
  set U : Subgroup X := V.comap (MulAut.conj : X →* MulAut X) with hUdef
  have hUR : U ≤ R := by
    intro u hu
    have hu' : MulAut.conj u ∈ V := hu
    exact hVW hu'
  have hVrange : V ≤ (MulAut.conj : X →* MulAut X).range := fun v hv => hWinn (hVW hv)
  obtain ⟨hUV⟩ : Nonempty (U ≃* V) := by
    have h : U.map (MulAut.conj : X →* MulAut X) = V := by
      rw [hUdef, Subgroup.map_comap_eq, inf_eq_right.mpr hVrange]
    exact ⟨(U.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr h)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
  have hUk : Nat.card U = 2 ^ k := by rw [Nat.card_congr hUV.toEquiv]; exact hk
  suffices hUcyc : IsCyclic U by
    haveI := hUcyc
    exact hVnc (isCyclic_of_injective hUV.symm.toMonoidHom hUV.symm.injective)
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  ·
    obtain rfl : m = 1 := by omega
    have hF : Nat.card (GaloisField 2 1) = 2 :=
      (GaloisField.card 2 1 (by norm_num)).trans (by norm_num)
    have hX6 : Nat.card X = 6 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_psl2_of_card_two hF
    have hdvd : Nat.card U ∣ 6 := by
      rw [← hX6]; exact Subgroup.card_subgroup_dvd_card U
    exact isCyclic_of_two_pow_card_dvd_six hUk hdvd
  · by_cases hin : IsInnerAut β
    ·
      obtain ⟨x, hx⟩ := hin
      have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hx, hβ3, map_one])
      have hx1 : x ≠ 1 := by
        intro h1
        rw [h1, map_one] at hx
        rw [← hx, orderOf_one] at hβ
        norm_num at hβ
      have hU : ∀ u ∈ U, x * u = u * x := by
        intro u hu
        have hu' : MulAut.conj u ∈ V := hu
        have h1 := hβW _ (hVW hu')
        rw [← hx, ← map_mul, ← map_mul] at h1
        exact hinj h1
      exact isCyclic_of_le_centralizer_psl2 hm2 hK e hx3 hx1 hU
    ·
      set C : Subgroup X := β.toMonoidHom.eqLocus (MonoidHom.id X) with hCdef
      have hβ' : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
      have hout' : ¬ IsInnerAut (MulAut.congr e β) := by rwa [isInnerAut_congr]
      obtain ⟨σ, hσ3, ⟨f0⟩⟩ := exists_eqLocus_mulEquiv_psl2 hβ' hout'
      have hFq : Nat.card (GH74.GLS.IVK.fixedField σ) ^ 3 = 2 ^ m := by
        have h := GH74.GLS.IVK.fixedField_card_pow σ
        rw [hσ3, hK] at h
        exact h
      obtain ⟨eC⟩ := eqLocus_mulEquiv_congr e β
      have hCcard : Nat.card C = Nat.card (PSL2 (GH74.GLS.IVK.fixedField σ)) :=
        (Nat.card_congr eC.toEquiv).trans (Nat.card_congr f0.toEquiv)
      have hRC : R ≤ C := by
        intro r hr
        have hr' : MulAut.conj r ∈ W := hr
        have h2 : β * MulAut.conj r * β⁻¹ = MulAut.conj r := by
          rw [hβW _ hr', mul_inv_cancel_right]
        rw [mul_mulAutConj_mul_inv] at h2
        exact hinj h2
      have hRnorm : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
        intro c hc r hr
        have hc' : β c = c := hc
        have hr' : MulAut.conj r ∈ W := hr
        have h := hnorm c hc' _ hr'
        rw [← map_inv, ← map_mul, ← map_mul] at h
        exact h
      have hRW : Nat.card R ∣ Nat.card W := by
        have hmapR : R.map (MulAut.conj : X →* MulAut X) ≤ W := Subgroup.map_comap_le _ _
        rw [← Subgroup.card_map_of_injective hinj]
        exact Subgroup.card_dvd_of_le hmapR
      have hdivR : ¬ 3 ∣ Nat.card R := fun h => hW3 (dvd_trans h hRW)
      have hq1 : 1 < Nat.card (GH74.GLS.IVK.fixedField σ) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have hdvd2 : Nat.card (GH74.GLS.IVK.fixedField σ) ∣ 2 ^ m := by
        rw [← hFq]; exact dvd_pow_self _ (by norm_num)
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · interval_cases i
        · simp at hi
          omega
        · have hq2 : Nat.card (GH74.GLS.IVK.fixedField σ) = 2 := by simpa using hi
          have hC6 : Nat.card C = 6 := by rw [hCcard]; exact card_psl2_of_card_two hq2
          have hdvd : Nat.card U ∣ 6 := by
            rw [← hC6]; exact Subgroup.card_dvd_of_le (hUR.trans hRC)
          exact isCyclic_of_two_pow_card_dvd_six hUk hdvd
      · have h4 : 4 ≤ Nat.card (GH74.GLS.IVK.fixedField σ) := by
          have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi2
          rw [← hi] at h
          norm_num at h
          omega
        have hK' : Nat.card (GaloisField 2 m) = Nat.card (GH74.GLS.IVK.fixedField σ) ^ 3 := by
          rw [hK, hFq]
        obtain ⟨hZC, hQC, h3C, -⟩ := fixedPoints_facts_of_mulEquiv_psl2 e h4 hK' hβ3 hin
        have hsub := subsingleton_of_quasisimple_centralizer C R U hQC hZC hRC hRnorm hUR h3C hdivR
        haveI := hsub
        infer_instance

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ChevTwoL2

end
