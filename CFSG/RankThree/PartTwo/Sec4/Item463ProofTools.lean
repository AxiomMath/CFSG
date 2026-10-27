module

import CFSG.RankThree.PartTwo.Sec10.Item10Std
import CFSG.RankThree.PartTwo.Sec11.Item116EiiCoprime
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item463Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem exists_isPGroup_two_le_commutator {G : Type} [Group G] [Finite G] {A H : Subgroup G}
    (hA : IsPGroup 3 A) (hH3 : ¬ 3 ∣ Nat.card H) (hHs : Group.IsSolvable H)
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (h2 : 2 ∣ Nat.card (⁅H, A⁆ : Subgroup G)) :
    ∃ U : Subgroup G, U ≤ ⁅H, A⁆ ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      A ≤ Subgroup.normalizer (U : Set G) ∧ ⁅U, A⁆ = U := by
  have hbotN : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro hh
      have h' : h = x⁻¹ * (x * h * x⁻¹) * x := by group
      rw [h', hh]
      group
  obtain ⟨S, hS, -, hAS⟩ := Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three
    Nat.prime_two hA hH3 hAH bot_le IsPGroup.of_bot hbotN
  have hSA : ⁅S, A⁆ ≠ ⊥ := by
    intro hbot
    have hodd := Sec11.Eii.odd_card_of_le_oddCoreOf
      (Sec11.Eii.commutator_le_oddCoreOf hA hH3 hHs hAH hS hbot)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hS3 : ¬ 3 ∣ Nat.card S := fun h => hH3 (h.trans (Subgroup.card_dvd_of_le hS.1))
  refine ⟨⁅S, A⁆, Subgroup.commutator_mono hS.1 le_rfl, ?_, hSA,
    Sec6.le_normalizer_commutator_right S A, ?_⟩
  · exact hS.2.1.to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hAS)
  · exact RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three A S
      hA hS3 hAS

theorem sylow_normal_of_le_center {P : Type*} [Group P] [Finite P] {Z : Subgroup P} [Z.Normal]
    (hZc : Z ≤ Subgroup.center P) (h2 : IsPGroup 2 (P ⧸ Z)) (S : Sylow 2 P) :
    (S : Subgroup P).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have htop : (S : Subgroup P) ⊔ Z = ⊤ := by
    have h1 : ((S : Subgroup P) ⊔ Z).index ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.index_dvd_of_le le_sup_right
    have h3 : ¬ 2 ∣ ((S : Subgroup P) ⊔ Z).index := fun h =>
      S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_left))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rw [← Subgroup.index_eq_one, hj]
    rcases j with _ | j
    · rfl
    · exact absurd (hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) h3
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ (S : Subgroup P) ⊔ Z := htop ▸ Subgroup.mem_top g
  obtain ⟨s, hs, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hzc := Subgroup.mem_center_iff.mp (hZc hz)
  have h : s * z * n * (s * z)⁻¹ = s * n * s⁻¹ := by
    rw [mul_inv_rev, show s * z * n * (z⁻¹ * s⁻¹) = s * (z * n * z⁻¹) * s⁻¹ by group,
      ← hzc n, mul_inv_cancel_right]
  rw [h]
  exact (S : Subgroup P).mul_mem ((S : Subgroup P).mul_mem hs hn) ((S : Subgroup P).inv_mem hs)

theorem ker_conj_eq_center {Q : Type*} [Group Q] :
    (MulAut.conj : Q →* MulAut Q).ker = Subgroup.center Q := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun σ : MulAut Q => σ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group

theorem conj_apply_eq {Q : Type*} [Group Q] (σ : MulAut Q) (x : Q) :
    MulAut.conj (σ x) = σ * MulAut.conj x * σ⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulEquiv.apply_symm_apply,
    MulAut.inv_apply]

theorem exists_twoSubgroup_of_le_range_conj {Q : Type*} [Group Q] [Finite Q]
    {R : Subgroup (MulAut Q)} (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) (hRi : R ≤ (MulAut.conj : Q →* MulAut Q).range) :
    ∃ T : Subgroup Q, IsPGroup 2 T ∧ T ≠ ⊥ ∧
      ∀ σ : MulAut Q, (∀ ρ ∈ R, σ * ρ * σ⁻¹ ∈ R) → T.map (σ : Q →* Q) ≤ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := R.comap (MulAut.conj : Q →* MulAut Q) with hPdef
  set f : P →* R := (MulAut.conj.comp P.subtype).codRestrict R (fun x => x.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨ρ, hρ⟩
    obtain ⟨x, rfl⟩ := hRi hρ
    exact ⟨⟨x, hρ⟩, rfl⟩
  have hker : f.ker = (Subgroup.center Q).subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← ker_conj_eq_center, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have h2 : IsPGroup 2 (P ⧸ f.ker) :=
    hR2.of_equiv (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm
  have hZc : f.ker ≤ Subgroup.center P := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx y)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 P))
  have hSn := sylow_normal_of_le_center hZc h2 S
  have hSu : Unique (Sylow 2 P) := Sylow.unique_of_normal S hSn
  refine ⟨(S : Subgroup P).map P.subtype, S.isPGroup'.map _, ?_, fun σ hσ => ?_⟩
  ·
    have hcardR : 2 ∣ Nat.card R := by
      obtain ⟨j, hj⟩ := hR2.exists_card_eq
      rcases j with _ | j
      · exact absurd (Subgroup.eq_bot_of_card_eq R (by rw [hj, pow_zero])) hR1
      · rw [hj]
        exact dvd_pow_self 2 (Nat.succ_ne_zero j)
    have hcardP : 2 ∣ Nat.card P := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv]
      exact dvd_mul_of_dvd_left hcardR _
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective]
    exact S.ne_bot_of_dvd_card hcardP
  ·
    have hTP : ((S : Subgroup P).map P.subtype).map (σ : Q →* Q) ≤ P := by
      rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      change MulAut.conj (σ (x : Q)) ∈ R
      rw [conj_apply_eq]
      exact hσ _ x.2
    set W := (((S : Subgroup P).map P.subtype).map (σ : Q →* Q)).subgroupOf P with hW
    have hW2 : IsPGroup 2 W := by
      have h := (S.isPGroup'.map P.subtype).map (σ : Q →* Q)
      exact h.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm
    obtain ⟨S', hS'⟩ := hW2.exists_le_sylow
    have hS'S : S' = S := Subsingleton.elim _ _
    rw [hS'S] at hS'
    intro y hy
    have hyW : (⟨y, hTP hy⟩ : P) ∈ W := Subgroup.mem_subgroupOf.mpr hy
    exact ⟨_, hS' hyW, rfl⟩

theorem exists_invariant_twoSubgroup_of_le_sup {G : Type} [Group G] [Finite G]
    {A U L : Subgroup G} (hA : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUN : U ≤ Subgroup.normalizer (L : Set G))
    (hU2 : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hUs : U ≤ L ⊔ thetaQuotCentralizer L) (hUC : ¬ U ≤ thetaQuotCentralizer L) :
    ∃ V ∈ invariantPiSubgroups L A (piOf 2), V ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := L ⧸ aschbacherSolvableCore 3 L with hQdef
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set φ : N →* MulAut Q := (thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  set R := (U.subgroupOf N).map φ with hR
  have hR2 : IsPGroup 2 R := (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm).map φ
  have hφC : ∀ g : N, (g : G) ∈ thetaQuotCentralizer L → φ g = 1 := by
    rintro g ⟨y, hy, hyg⟩
    have : y = g := Subtype.ext hyg
    rw [← this]
    exact hy
  have hφL : ∀ (g : N) (hgL : (g : G) ∈ L), φ g = MulAut.conj ((⟨g, hgL⟩ : L) : Q) := by
    intro g hgL
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [hφ, MonoidHom.comp_apply, thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
  have hRi : R ≤ (MulAut.conj : Q →* MulAut Q).range := by
    rintro _ ⟨u, hu, rfl⟩
    set M : Subgroup G := (((MulAut.conj : Q →* MulAut Q).range).comap φ).map N.subtype
      with hM
    have hLM : L ≤ M := fun l hl =>
      ⟨⟨l, Subgroup.le_normalizer hl⟩, by
        show φ _ ∈ (MulAut.conj : Q →* MulAut Q).range
        rw [hφL _ hl]
        exact ⟨_, rfl⟩, rfl⟩
    have hCM : thetaQuotCentralizer L ≤ M := fun c hc =>
      ⟨⟨c, Sec6.thetaQuotCentralizer_le_normalizer L hc⟩, by
        show φ _ ∈ (MulAut.conj : Q →* MulAut Q).range
        rw [hφC _ hc]
        exact Subgroup.one_mem _, rfl⟩
    obtain ⟨v, hv, hvu⟩ := (sup_le hLM hCM) (hUs (Subgroup.mem_subgroupOf.mp hu))
    have : v = u := Subtype.ext hvu
    rw [← this]
    exact hv
  have hR1 : R ≠ ⊥ := by
    intro hbot
    apply hUC
    intro u hu
    have hφu : φ ⟨u, hUN hu⟩ = 1 := by
      have hmem : φ ⟨u, hUN hu⟩ ∈ R := ⟨⟨u, hUN hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact ⟨⟨u, hUN hu⟩, hφu, rfl⟩
  obtain ⟨T, hT2, hT1, hTinv⟩ := exists_twoSubgroup_of_le_range_conj hR2 hR1 hRi
  have hAV' : A ≤ Subgroup.normalizer ((Sec10.thetaPreimage L T : Subgroup G) : Set G) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun y hy v hv => ?_
    obtain ⟨hvL, hvT⟩ := Sec10.mem_thetaPreimage_iff.mp hv
    have hyN : y ∈ N := hAL hy
    have hyv : y * v * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN v).mp hvL
    refine Sec10.mem_thetaPreimage_iff.mpr ⟨hyv, ?_⟩
    have himg : ((⟨y * v * y⁻¹, hyv⟩ : L) : Q) = φ ⟨y, hyN⟩ ((⟨v, hvL⟩ : L) : Q) := by
      rw [hφ, MonoidHom.comp_apply, thetaQuotMulAut_mk]
      rfl
    rw [himg]
    refine hTinv (φ ⟨y, hyN⟩) ?_ (Subgroup.mem_map_of_mem _ hvT)
    rintro _ ⟨u, hu, rfl⟩
    have hyu : (⟨y, hyN⟩ : N) * u * (⟨y, hyN⟩ : N)⁻¹ ∈ U.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hAU hy) u).mp (Subgroup.mem_subgroupOf.mp hu)
    exact ⟨_, hyu, by rw [map_mul, map_mul, map_inv]⟩
  obtain ⟨V, hVV', hV1, hV2, hAV⟩ := Sec10.exists_pGroup_le_normalizer (p := 3) (q := 2) hA
    (Sec10.not_three_dvd_card_thetaPreimage hT2) (Sec10.two_dvd_card_thetaPreimage hT2 hT1) hAV'
  exact ⟨V, (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
    ⟨hVV'.trans Sec10.thetaPreimage_le, hV2, hAV⟩, hV1⟩

end CFSG.RankThree.PartTwo.Sec4.Item463Proof
