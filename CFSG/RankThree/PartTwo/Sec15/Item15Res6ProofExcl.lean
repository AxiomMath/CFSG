module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofMem
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Aut
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Orders
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec15.Item15No135

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement Pointwise

@[expose] noncomputable def Y4CoreExclSL25HJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ M ∈ scriptY2 A,
      generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        J ∈ thetaComponentsIn M → J = delta A (lB A) J → IsSL25Case J →
          IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)

namespace Proof15Res6

section OTwoF

variable {T : Type*} [Group T]

theorem oTwoFitting_characteristic : (Sec4.oTwoFitting T).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro σ
  set O := CFSG.pCore 2 T with hO
  have hOσ : O.map σ.toMonoidHom = O := CFSG.pCore_map_iso 2 σ
  set σ' : T ⧸ O ≃* T ⧸ O := QuotientGroup.congr O O σ hOσ with hσ'
  have hcomm : ∀ x : T, QuotientGroup.mk' O (σ x) = σ' (QuotientGroup.mk' O x) := fun x => rfl
  have hP : (fittingSubgroup (T ⧸ O)).comap σ'.toMonoidHom = fittingSubgroup (T ⧸ O) :=
    Subgroup.characteristic_iff_comap_eq.mp inferInstance σ'
  ext x
  change QuotientGroup.mk' O (σ x) ∈ fittingSubgroup (T ⧸ O) ↔
    QuotientGroup.mk' O x ∈ fittingSubgroup (T ⧸ O)
  rw [hcomm]
  conv_rhs => rw [← hP]
  rfl

end OTwoF

theorem kSL2AutThree_of_five_le (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := SL(2, ZMod p)
  have hEinn : E ≤ (MulAut.conj : S →* MulAut S).range := by
    intro φ hφ
    obtain ⟨s, hs⟩ := exists_eq_conj_of_pow_three_SL2 hp5 (hE.2 φ hφ)
    exact ⟨s, hs.symm⟩
  set Ehat := E.comap (MulAut.conj : S →* MulAut S) with hEhat
  set f : Ehat →* E := ((MulAut.conj : S →* MulAut S).comp Ehat.subtype).codRestrict E
    (fun x => x.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨s, rfl⟩ := hEinn hφ
    exact ⟨⟨s, hφ⟩, rfl⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 Ehat) := inferInstance
  have hTE : (T : Subgroup Ehat).map f = ⊤ := by
    have hEtop : IsPGroup 3 (⊤ : Subgroup E) := hE3.of_equiv Subgroup.topEquiv.symm
    have h := ((T.mapSurjective hfs).is_maximal' hEtop le_top).symm
    rwa [Sylow.coe_mapSurjective] at h
  have hTinj : Set.InjOn f ((T : Subgroup Ehat) : Set Ehat) := by
    intro x hx y hy hxy
    have hTxy : x⁻¹ * y ∈ (T : Subgroup Ehat) := mul_mem (inv_mem hx) hy
    have hf1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hcen : ((x⁻¹ * y : Ehat) : S) ∈ Subgroup.center S := by
      have h2 : MulAut.conj ((x⁻¹ * y : Ehat) : S) = 1 := congrArg Subtype.val hf1
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun τ : MulAut S => τ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨x⁻¹ * y, hTxy⟩
    have hord3 : orderOf (x⁻¹ * y : Ehat) ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact congrArg Subtype.val hk
    have hord2 : orderOf ((x⁻¹ * y : Ehat) : S) ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center S) hcen
      rwa [Sec4.Census.card_center_SL2 (by omega)] at this
    rw [Subgroup.orderOf_coe] at hord2
    have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
    have hord1 : orderOf (x⁻¹ * y : Ehat) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hord3 hord2
    rw [Nat.dvd_one, orderOf_eq_one_iff, inv_mul_eq_one] at hord1
    exact hord1
  have hcardT : Nat.card (T : Subgroup Ehat) = Nat.card E := by
    rw [← Sec13.card_map_eq_of_injOn f hTinj, hTE, Subgroup.card_top]
  set T' : Subgroup S := (T : Subgroup Ehat).map Ehat.subtype with hT'
  have hT'3 : IsPGroup 3 T' := T.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hT'3.exists_le_sylow
  have hQc : IsCyclic (Q : Subgroup S) :=
    Sec4.Census.isCyclic_sylow_SL2 (p := p) (r := 3) (by norm_num) (by omega) Q
  have hT'c : IsCyclic T' := by
    have : IsCyclic (T'.subgroupOf (Q : Subgroup S)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQ).surjective
  have hTc : IsCyclic (T : Subgroup Ehat) := by
    have e := (T : Subgroup Ehat).equivMapOfInjective Ehat.subtype Ehat.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (T : Subgroup Ehat))
  have hog : orderOf g = Nat.card (T : Subgroup Ehat) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    refine hTinj (pow_mem g.2 3) (one_mem _) ?_
    rw [map_pow, OneMemClass.coe_one, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hE.2 _ (f (g : Ehat)).2)
  rw [← hcardT, ← hog]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)

variable {G : Type} [Group G] [Finite G]

theorem exists_hyperplane_of_autBound {T : Type*} [Group T]
    (hbound : ∀ E : Subgroup (MulAut T), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 3)
    {A X : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (N : Subgroup X) [N.Normal] [N.Characteristic] (e : X ⧸ N ≃* T) :
    ∃ B : Subgroup G, IsHyperplane A B ∧ IsPGroup 3 B ∧
      ∀ x ∈ X, ∀ b ∈ B, ⁅x, b⁆ ∈ N.map X.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : A →* MulAut (X ⧸ N) :=
    (quotMulAut N).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX)) with hρ
  have hAtop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup A) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a _ => Subtype.ext (hA.2 a a.2)⟩
    exact congrArg Subtype.val (hA.1.is_comm.comm (a : A) (b : A))
  have hEab : CFSG.Assembly.IsElemAbelian 3
      (((⊤ : Subgroup A).map ρ).map (MulAut.congr e).toMonoidHom) :=
    isElemAbelian_map_hom (isElemAbelian_map_hom hAtop ρ) _
  have hcardE := hbound _ hEab
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, ← MonoidHom.range_eq_map]
    at hcardE
  have hcard : Nat.card ρ.range * Nat.card ρ.ker = 27 := by
    rw [← hA27, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker).symm
  have hker9 : 3 ^ 2 ∣ Nat.card ρ.ker := by
    have hr0 : 0 < Nat.card ρ.range := Nat.card_pos
    interval_cases h : Nat.card ρ.range <;> omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hker9
  set B : Subgroup G := (K.map ρ.ker.subtype).map A.subtype with hB
  have hBcard : Nat.card B = 9 := by
    rw [hB, Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective ρ.ker.subtype_injective, hK]
    norm_num
  refine ⟨B, ⟨Subgroup.map_subtype_le _, by rw [hA27, hBcard]⟩,
    IsPGroup.of_card (n := 2) (by rw [hBcard]; norm_num), ?_⟩
  rintro x hx _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hρk : ρ (k : A) = 1 := k.2
  set x' : X := ⟨x, hx⟩ with hx'
  set b : A := (k : A) with hbdef
  have hbX : (b : G) ∈ Subgroup.normalizer (X : Set G) := hAX b.2
  set σ := X.normalizerMonoidHom ⟨(b : G), hbX⟩ with hσ
  have h1 : ((x'⁻¹ : X) : X ⧸ N) = ((σ x'⁻¹ : X) : X ⧸ N) := by
    have h2 := congrArg (fun τ : MulAut (X ⧸ N) => τ ((x'⁻¹ : X) : X ⧸ N)) hρk
    simp only [MulAut.one_apply] at h2
    exact h2.symm
  rw [QuotientGroup.eq, inv_inv] at h1
  refine ⟨x' * σ x'⁻¹, h1, ?_⟩
  change (x : G) * (b * x⁻¹ * (b : G)⁻¹) = ⁅x, (b : G)⁆
  rw [commutatorElement_def]
  group

omit [Finite G] in
theorem not_three_dvd_card_quot_of_le_sup [Finite G] {X Q₀ : Subgroup G} (N : Subgroup X)
    [N.Normal] (hQX : Q₀ ≤ X) (hQ3 : ¬ 3 ∣ Nat.card Q₀) (hX : X ≤ Q₀ ⊔ N.map X.subtype) :
    ¬ 3 ∣ Nat.card (X ⧸ N) := by
  set N' := N.map X.subtype with hN'
  have hN'X : X ≤ Subgroup.normalizer (N' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · rintro ⟨n₀, hn₀, rfl⟩
      refine ⟨⟨x, hx⟩ * n₀ * ⟨x, hx⟩⁻¹, (inferInstance : N.Normal).conj_mem _ hn₀ _, ?_⟩
      simp
    · rintro ⟨n₀, hn₀, hn⟩
      have hnX : n ∈ X := by
        have : x * n * x⁻¹ ∈ X := hn ▸ n₀.2
        simpa [mul_assoc] using X.mul_mem (X.mul_mem (X.inv_mem hx) this) hx
      refine ⟨⟨n, hnX⟩, ?_, rfl⟩
      have h1 : (⟨x, hx⟩ : X)⁻¹ * n₀ * (⟨x, hx⟩ : X)⁻¹⁻¹ ∈ N :=
        (inferInstance : N.Normal).conj_mem _ hn₀ _
      have h2 : (⟨x, hx⟩ : X)⁻¹ * n₀ * (⟨x, hx⟩ : X)⁻¹⁻¹ = ⟨n, hnX⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [show (n₀ : G) = x * n * x⁻¹ from hn]
        group
      rwa [h2] at h1
  set φ : Q₀ →* X ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hQX) with hφ
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx' : x ∈ (N' : Set G) * (Q₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N' Q₀ (hQX.trans hN'X)]
      have h1 := hX hx
      rw [sup_comm] at h1
      exact h1
    obtain ⟨n, hn, q, hq, rfl⟩ := hx'
    obtain ⟨n₀, hn₀, rfl⟩ := hn
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hmem := (inferInstance : N.Normal).conj_mem _ hn₀ (Subgroup.inclusion hQX ⟨q, hq⟩)⁻¹
    convert hmem using 1
    apply Subtype.ext
    simp [mul_assoc]
  intro h3
  exact hQ3 (h3.trans (Subgroup.card_dvd_of_surjective (f := φ) hφs))

theorem false_of_sl2_nhj (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (hNHJ : ¬ AllPointsHJ A) {X : Subgroup G}
    (hΔ : X = delta A (lB A) X) (hAX : A ≤ Subgroup.normalizer (X : Set G)) {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (N : Subgroup X) [N.Normal] [N.Characteristic]
    (e : X ⧸ N ≃* SL(2, ZMod p)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, hB, hB3, hBX⟩ := exists_hyperplane_of_autBound (kSL2AutThree_of_five_le p hp5)
    h.isElemAbelian h.card_eq hAX N e
  have hLB : lB A B = ⊥ := lB_eq_bot_of_not_allPointsHJ' h134 h48 h.toSec14Std hNHJ hB
  have hle := le_qBound_sup_of_eq_delta hΔ hB hB3 hBX
  have hndvd : ∀ K : Subgroup G, ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 K) := fun K =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hq3 : ¬ 3 ∣ Nat.card (qBound A (lB A) B) := by
    rw [qBound, hLB, sup_bot_eq]
    exact not_three_dvd_card_sup
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1)) (hndvd _)
      (hndvd _)
  have hQ3 : ¬ 3 ∣ Nat.card (X ⊓ qBound A (lB A) B : Subgroup G) := fun h3 =>
    hq3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hX3 := not_three_dvd_card_quot_of_le_sup N inf_le_left hQ3 hle
  apply hX3
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_SL2 (p := p) (by omega)

end Proof15Res6

open Proof15Res6

theorem y4CoreMemExclR_of (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (hSL25 : Y4CoreExclSL25HJR) : Y4CoreMemExclR := by
  intro G _ _ A c L h M hM hF J hJ hAJ hJM hΔ hcase
  have h14 := h.toSec14Std
  have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJM
  have hJq := isQuasisimple_theta_of_mem_thetaComponentsIn hJM
  have hJM' : J ≤ M := le_of_mem_thetaComponentsIn hJM
  have hJtop : J ≠ ⊤ := fun h' => hM.1.1 (top_le_iff.mp (h' ▸ hJM'))
  have hJY : J ∈ scriptY A := ⟨hJtop, hAJ⟩
  rcases hcase with h2 | ⟨p, hp, hp3, he⟩ | h4
  ·
    by_cases hHJ : AllPointsHJ A
    · exact hSL25 G A c L h hHJ M hM hF J hJ hAJ hJM hΔ (Or.inl h2)
    · exfalso
      obtain ⟨e⟩ := h2
      have : (Sec4.oTwoFitting ↥J).Characteristic := oTwoFitting_characteristic
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ (p := 5) le_rfl (Sec4.oTwoFitting ↥J) e
  ·
    have : Fact p.Prime := ⟨hp⟩
    have : (Sec4.oTwoP p ↥J).Characteristic := oTwoP_characteristic p
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h5 | h5
      · interval_cases p
        exact absurd hp (by norm_num)
      · exact h5
    by_cases hHJ : AllPointsHJ A
    · rcases Nat.lt_or_ge 5 p with hp5' | hp5'
      ·
        exfalso
        obtain ⟨e⟩ := he
        have hΔ0 : J = deltaZero A (lB A) J :=
          eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
            Sec4.Sporadic.rank3II_4_15
            (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) h14 hAJ hJ.2 hΔ
        have he' : letI := ker148_normal hAJ
            Nonempty (↥(img148 A J (deltaZero A (lB A) J)) ≃* PSL(2, ZMod p)) := by
          let := ker148_normal hAJ
          rw [← hΔ0]
          obtain ⟨φ⟩ := nonempty_img148_equiv hAJ
          obtain ⟨ψ⟩ := nonempty_quotient_pPrimeCore_equiv_psl hp5' e
          exact ⟨φ.trans ψ⟩
        exact false_of_img148_psl2 (h148 G A c L h) hJY h.isElemAbelian.1 hHJ h.chosen136
          kSL2pNotList148 hp5' he'
      ·
        have hp5'' : p = 5 := le_antisymm hp5' hp5
        subst hp5''
        exact hSL25 G A c L h hHJ M hM hF J hJ hAJ hJM hΔ (Or.inr he)
    · exfalso
      obtain ⟨e⟩ := he
      exact false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ hp5 (Sec4.oTwoP p ↥J) e
  ·
    exact isQuasisimple_of_case444 hJp hJq h4

theorem y4CoreMemR_of_excl (h149 : Sec16.Item149S14)
    (hS : Y4CoreMemSolvR) (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (hSL25 : Y4CoreExclSL25HJR) : Y4CoreMemR :=
  y4CoreMemR_of_parts h149 hS (y4CoreMemExclR_of h134 h48 h148 hSL25)

end CFSG.RankThree.PartTwo.Sec15
