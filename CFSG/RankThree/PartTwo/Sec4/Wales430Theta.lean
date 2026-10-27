module

public import CFSG.RankThree.PartTwo.Sec4.Statements430
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Sec21 Sec21.Item211Proof

namespace Wales430Theta

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

theorem maximal_of_mem_partTwoE_quotX (hEF : partTwoE G = partTwoF G)
    {E₀ : Subgroup (QuotX L A)} (hE₀ : E₀ ∈ partTwoE (QuotX L A)) :
    ∀ B : Subgroup (QuotX L A), CFSG.Assembly.IsElemAbelian 3 B → E₀ ≤ B → B = E₀ := by
  obtain ⟨hE₀e, hE₀card, T, hT1, hT2, hE₀T⟩ := hE₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E'', -, hE''map, hE''card, hE''e⟩ := exists_lift_of_le (L := L) (A := A) (T := ⊥)
    IsPGroup.of_bot hE₀e (by rw [Subgroup.map_bot]; exact bot_le)
  have hE''p : IsPGroup 3 E'' := fun x => ⟨1, Subtype.ext (by simpa using hE''e.2 x x.2)⟩
  set N := aschbacherSolvableCore 3 ↥(L ⊔ A) with hN
  set D : Subgroup ↥(L ⊔ A) := T.comap (piX L A) with hD
  have hDcard : Nat.card D = Nat.card N * Nat.card T :=
    QuotientGroup.card_preimage_mk N (T : Set (QuotX L A))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hT1 (Subgroup.card_eq_one.mp hk)
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hDcard, hk]
    exact Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        three_not_dvd_card_aschbacherSolvableCore)
      (Nat.Coprime.pow_right k (by norm_num))
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hE''D : E'' ≤ Subgroup.normalizer (D : Set ↥(L ⊔ A)) := by
    intro x hx
    have hxE : piX L A x ∈ E₀ := by
      rw [← hE''map]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.le_normalizer_comap (piX L A) (hE₀T hxE)
  obtain ⟨Q, hQN, hQ1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E'' D hE''p hE''D hcop h2
  set U₁ : Subgroup G := ((Q : Subgroup D).map D.subtype).map (L ⊔ A).subtype with hU₁
  have hE₂ : E''.map (L ⊔ A).subtype ∈ partTwoE G := by
    refine ⟨isElemAbelian_map_subtype hE''e, ?_, U₁, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, hE''card, hE₀card]
    · intro h0
      apply hQ1
      rwa [hU₁, Subgroup.map_eq_bot_iff_of_injective _ (L ⊔ A).subtype_injective] at h0
    · exact (Q.isPGroup'.map D.subtype).map (L ⊔ A).subtype
    · exact (Subgroup.map_mono hQN).trans (Subgroup.le_normalizer_map _)
  have hF₂ : E''.map (L ⊔ A).subtype ∈ partTwoF G := by
    rw [← hEF]
    exact hE₂
  intro B hB hE₀B
  obtain ⟨S, hE''S, -, hScard, hSe⟩ :=
    exists_lift_of_le hE''p hB (by rw [hE''map]; exact hE₀B)
  have heq := hF₂.2.1 _ (isElemAbelian_map_subtype hSe) (Subgroup.map_mono hE''S)
  have hcard : Nat.card B = Nat.card E₀ := by
    rw [← hScard, ← Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, heq,
      Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, hE''card]
  exact (Subgroup.eq_of_le_of_card_ge hE₀B (by rw [hcard])).symm

theorem partTwoE_quotX_eq (hEF : partTwoE G = partTwoF G) :
    partTwoE (QuotX L A) = partTwoF (QuotX L A) := by
  ext E₀
  constructor
  · intro hE₀
    exact ⟨hE₀.1, maximal_of_mem_partTwoE_quotX hEF hE₀, E₀, hE₀, le_rfl⟩
  · rintro ⟨hA₀e, -, E₁, hE₁, hE₁A₀⟩
    rw [maximal_of_mem_partTwoE_quotX hEF hE₁ E₀ hA₀e hE₁A₀]
    exact hE₁

theorem normalizer_aOne_le_normalizer_map (hA : IsPGroup 3 A) {P : Subgroup G} (hPA : P ≤ A)
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer ((aOne L A : Subgroup (QuotX L A)) : Set (QuotX L A)) ≤
      Subgroup.normalizer
        (((P.subgroupOf (L ⊔ A)).map (piX L A) : Subgroup (QuotX L A)) : Set (QuotX L A)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 (A.subgroupOf (L ⊔ A))) := ⟨isPGroup_subgroupOf (L := L) hA⟩
  have hcop : Nat.Coprime 3 (Nat.card (aschbacherSolvableCore 3 ↥(L ⊔ A))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr three_not_dvd_card_aschbacherSolvableCore
  have hNorm : Subgroup.normalizer ((aOne L A : Subgroup (QuotX L A)) : Set (QuotX L A)) =
      (Subgroup.normalizer ((A.subgroupOf (L ⊔ A) : Subgroup ↥(L ⊔ A)) : Set ↥(L ⊔ A))).map
        (piX L A) :=
    CFSG.normalizer_map_quotient_eq_map_normalizer 3 (A.subgroupOf (L ⊔ A))
      (aschbacherSolvableCore 3 ↥(L ⊔ A)) inferInstance hcop
  rw [hNorm]
  rintro _ ⟨n, hn, rfl⟩
  refine Subgroup.le_normalizer_map (piX L A) ⟨n, ?_, rfl⟩
  rw [← Subgroup.subgroupOf_normalizer_eq (le_sup_right : A ≤ L ⊔ A)] at hn
  rw [← Subgroup.subgroupOf_normalizer_eq (hPA.trans (le_sup_right : A ≤ L ⊔ A))]
  exact Subgroup.mem_subgroupOf.mpr (hN (Subgroup.mem_subgroupOf.mp hn))

omit [Finite G] in
theorem map_zpowers_subgroupOf {c : G} (hc : c ∈ L ⊔ A) :
    ((Subgroup.zpowers c).subgroupOf (L ⊔ A)).map (piX L A) =
      Subgroup.zpowers (piX L A ⟨c, hc⟩) := by
  have h1 : (Subgroup.zpowers c).subgroupOf (L ⊔ A) =
      Subgroup.zpowers (⟨c, hc⟩ : ↥(L ⊔ A)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp⟩
  rw [h1, MonoidHom.map_zpowers]

omit [Finite G] in
theorem map_subgroupOf_sup {P Q : Subgroup G} (hP : P ≤ L ⊔ A) (hQ : Q ≤ L ⊔ A) :
    (P.subgroupOf (L ⊔ A)).map (piX L A) ⊔ (Q.subgroupOf (L ⊔ A)).map (piX L A) =
      ((P ⊔ Q).subgroupOf (L ⊔ A)).map (piX L A) := by
  rw [Subgroup.subgroupOf_sup hP hQ, Subgroup.map_sup]

theorem map_subgroupOf_inf_eq_bot (hA : IsPGroup 3 A) {P Q : Subgroup G} (hP : P ≤ A)
    (hQ : Q ≤ A) (h : P ⊓ Q = ⊥) :
    (P.subgroupOf (L ⊔ A)).map (piX L A) ⊓ (Q.subgroupOf (L ⊔ A)).map (piX L A) = ⊥ := by
  have hinj := injOn_mk_of_isPGroup Nat.prime_three (isPGroup_subgroupOf (L := L) hA)
  rw [eq_bot_iff]
  rintro _ ⟨⟨y, hy, rfl⟩, ⟨z, hz, hzy⟩⟩
  have hyA : y ∈ A.subgroupOf (L ⊔ A) :=
    Subgroup.mem_subgroupOf.mpr (hP (Subgroup.mem_subgroupOf.mp hy))
  have hzA : z ∈ A.subgroupOf (L ⊔ A) :=
    Subgroup.mem_subgroupOf.mpr (hQ (Subgroup.mem_subgroupOf.mp hz))
  have hzy' : z = y := hinj hzA hyA hzy
  have hy1 : (y : G) ∈ P ⊓ Q :=
    ⟨Subgroup.mem_subgroupOf.mp hy, hzy' ▸ Subgroup.mem_subgroupOf.mp hz⟩
  rw [h, Subgroup.mem_bot] at hy1
  have hy1' : y = 1 := Subtype.ext hy1
  rw [hy1', map_one]
  exact Subgroup.one_mem _

theorem piX_not_mem_zpowers (hA : IsPGroup 3 A) {a c : G} (haA : a ∈ A) (hcA : c ∈ A)
    (hca : c ∉ Subgroup.zpowers a) :
    piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ∉
      Subgroup.zpowers (piX L A ⟨a, Subgroup.mem_sup_right haA⟩) := by
  have hinj := injOn_mk_of_isPGroup Nat.prime_three (isPGroup_subgroupOf (L := L) hA)
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply hca
  have hakA : (⟨a, Subgroup.mem_sup_right haA⟩ : ↥(L ⊔ A)) ^ k ∈ A.subgroupOf (L ⊔ A) :=
    Subgroup.zpow_mem _ (Subgroup.mem_subgroupOf.mpr haA) k
  have hcA' : (⟨c, Subgroup.mem_sup_right hcA⟩ : ↥(L ⊔ A)) ∈ A.subgroupOf (L ⊔ A) :=
    Subgroup.mem_subgroupOf.mpr hcA
  have heq := hinj hakA hcA' (by rw [map_zpow]; exact hk)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val heq⟩

theorem map_mem_invariantPiSubgroups_lOne {R : Subgroup G}
    (hR : R ∈ invariantPiSubgroups L A (piOf 2)) :
    (R.subgroupOf (L ⊔ A)).map (piX L A) ∈
      invariantPiSubgroups (lOne L A) (aOne L A) (piOf 2) := by
  obtain ⟨hRL, hR2, hAR⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hR
  have hAMN : A.subgroupOf (L ⊔ A) ≤
      Subgroup.normalizer ((R.subgroupOf (L ⊔ A) : Subgroup ↥(L ⊔ A)) : Set ↥(L ⊔ A)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hAR (Subgroup.mem_subgroupOf.mp hx)) y
  exact (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
    ⟨Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (hRL (Subgroup.mem_subgroupOf.mp hx)),
      (hR2.comap_of_injective (L ⊔ A).subtype (L ⊔ A).subtype_injective).map _,
      (Subgroup.map_mono hAMN).trans (Subgroup.le_normalizer_map _)⟩

theorem map_subgroupOf_ne_bot (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {R : Subgroup G} (hRL : R ≤ L) (hR : ¬ R ≤ thetaQuotCentralizer L) :
    (R.subgroupOf (L ⊔ A)).map (piX L A) ≠ ⊥ := by
  intro h0
  apply hR
  intro r hr
  have hr' : (⟨r, Subgroup.mem_sup_left (hRL hr)⟩ : ↥(L ⊔ A)) ∈ (piX L A).ker :=
    ((Subgroup.map_eq_bot_iff _).mp h0) (Subgroup.mem_subgroupOf.mpr hr)
  rw [QuotientGroup.ker_mk'] at hr'
  have h1 : r ∈ inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) := ⟨_, hr', rfl⟩
  rw [inSubgroup_theta_sup hA hAL] at h1
  exact Sec6.theta_le_thetaQuotCentralizer L h1

omit [Finite G] in
theorem map_commutator_zpowers {R : Subgroup G} {c : G} (hRLA : R ≤ L ⊔ A) (hc : c ∈ L ⊔ A)
    (hRc : ⁅R, Subgroup.zpowers c⁆ = R) :
    ⁅(R.subgroupOf (L ⊔ A)).map (piX L A), Subgroup.zpowers (piX L A ⟨c, hc⟩)⁆ =
      (R.subgroupOf (L ⊔ A)).map (piX L A) := by
  have hcLA : Subgroup.zpowers c ≤ L ⊔ A := Subgroup.zpowers_le.mpr hc
  have h1 : ⁅R.subgroupOf (L ⊔ A), (Subgroup.zpowers c).subgroupOf (L ⊔ A)⁆ =
      R.subgroupOf (L ⊔ A) := by
    apply Subgroup.map_injective (L ⊔ A).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRLA, inf_eq_left.mpr hcLA, hRc]
  rw [← map_zpowers_subgroupOf hc, ← Subgroup.map_commutator, h1]

end Wales430Theta

@[expose] def Item4_30Theta :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K A : Subgroup G) (a c : G) (B R : Subgroup G),
    SectionFourHyp ↥(K ⊔ A) → partTwoE G = partTwoF G →
    Group.IsPerfect K → IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) →
    Late.IsE27 A → A ≤ Subgroup.normalizer (K : Set G) →
    Maximal (fun X : Subgroup G => CFSG.Assembly.IsElemAbelian 3 X) A →
    A ⊓ thetaQuotCentralizer K = Subgroup.zpowers a → orderOf a = 3 →
    c ∈ A → c ∉ Subgroup.zpowers a → Subgroup.zpowers c ⊔ B = A →
    Subgroup.zpowers c ⊓ B = ⊥ →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G) →
    R ∈ invariantPiSubgroups K A (piOf 2) → ¬ R ≤ thetaQuotCentralizer K →
    ⁅R, Subgroup.zpowers c⁆ = R →
      (∃ x ∈ A, KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) ∨
        Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* Blueprint.NativeSporadic.M12) ∨
        Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* Blueprint.NativeSporadic.J2)

theorem item4_30Theta_of
    (h430 : Item4_30) (h41 : Item4_1LargePrime) : Item4_30Theta := by
  intro G _ _ K A a c B R hΛ hEF _ hq hA27 hAL _ hCA ha3 hcA hca hsup hinf hWc hWB hR hRθ hRc
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA27.1
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have haA : a ∈ A :=
    (show a ∈ A ⊓ thetaQuotCentralizer K from hCA ▸ Subgroup.mem_zpowers a).1
  have hBA : B ≤ A := hsup ▸ le_sup_right
  have hcLA : c ∈ K ⊔ A := Subgroup.mem_sup_right hcA
  have hzc : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  obtain ⟨hRK, -, -⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hR
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hX : SectionFourHyp (QuotX K A) := sectionFourHyp_quotX h41 hΛ hAp hAL Φ₀ hq
  have hθX : aschbacherSolvableCore 3 (QuotX K A) = ⊥ :=
    (theta_quotient_core_and_ranks (G := ↥(K ⊔ A))).1
  have hEFX : partTwoE (QuotX K A) = partTwoF (QuotX K A) :=
    Wales430Theta.partTwoE_quotX_eq (L := K) (A := A) hEF
  have hE27₁ : Late.IsE27 (aOne K A) := by
    refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨x, rfl⟩ := (aEquiv (L := K) hAp).surjective x
      obtain ⟨y, rfl⟩ := (aEquiv (L := K) hAp).surjective y
      rw [← map_mul, ← map_mul, hAe.1.is_comm.comm x y]
    · obtain ⟨x, hx, rfl⟩ := hx
      rw [← map_pow]
      have h3 : x ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))
      rw [h3, map_one]
    · rw [← Nat.card_congr (aEquiv (L := K) hAp).toEquiv, hA27.2]
  have hCA₁ : aOne K A ⊓ Subgroup.centralizer (lOne K A : Set (QuotX K A)) =
      Subgroup.zpowers (piX K A ⟨a, Subgroup.mem_sup_right haA⟩) :=
    aOne_inf_centralizer hAp hAL haA hCA
  have ha₁ : orderOf (piX K A ⟨a, Subgroup.mem_sup_right haA⟩) = 3 := by
    have h1 : (piX K A ⟨a, Subgroup.mem_sup_right haA⟩) =
        ((aEquiv (L := K) hAp ⟨a, haA⟩ : aOne K A) : QuotX K A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact ha3
  have hc₁a : piX K A ⟨c, hcLA⟩ ∉ Subgroup.zpowers (piX K A ⟨a, Subgroup.mem_sup_right haA⟩) :=
    Wales430Theta.piX_not_mem_zpowers hAp haA hcA hca
  have hsup₁ : Subgroup.zpowers (piX K A ⟨c, hcLA⟩) ⊔ (B.subgroupOf (K ⊔ A)).map (piX K A) =
      aOne K A := by
    rw [← Wales430Theta.map_zpowers_subgroupOf hcLA,
      Wales430Theta.map_subgroupOf_sup (hzc.trans le_sup_right) (hBA.trans le_sup_right), hsup]
  have hinf₁ : Subgroup.zpowers (piX K A ⟨c, hcLA⟩) ⊓ (B.subgroupOf (K ⊔ A)).map (piX K A) =
      ⊥ := by
    rw [← Wales430Theta.map_zpowers_subgroupOf hcLA]
    exact Wales430Theta.map_subgroupOf_inf_eq_bot hAp hzc hBA hinf
  have hWc₁ : Subgroup.normalizer ((aOne K A : Subgroup (QuotX K A)) : Set (QuotX K A)) ≤
      Subgroup.normalizer
        ((Subgroup.zpowers (piX K A ⟨c, hcLA⟩) : Subgroup (QuotX K A)) : Set (QuotX K A)) := by
    rw [← Wales430Theta.map_zpowers_subgroupOf hcLA]
    exact Wales430Theta.normalizer_aOne_le_normalizer_map hAp hzc hWc
  have hWB₁ := Wales430Theta.normalizer_aOne_le_normalizer_map (L := K) hAp hBA hWB
  have hR₁ := Wales430Theta.map_mem_invariantPiSubgroups_lOne (L := K) (A := A) hR
  have hR₁1 := Wales430Theta.map_subgroupOf_ne_bot hAp hAL hRK hRθ
  have hR₁c := Wales430Theta.map_commutator_zpowers (hRK.trans le_sup_left) hcLA hRc
  rcases h430 (QuotX K A) hX hEFX hθX (aOne K A) hE27₁ (lOne K A)
      (isComponent_lOne hAL Φ₀ hq) (piX K A ⟨a, Subgroup.mem_sup_right haA⟩) hCA₁ ha₁
      (piX K A ⟨c, hcLA⟩) (piX_mem_aOne hcA) hc₁a ((B.subgroupOf (K ⊔ A)).map (piX K A))
      hsup₁ hinf₁ hWc₁ hWB₁ ((R.subgroupOf (K ⊔ A)).map (piX K A)) hR₁ hR₁1 hR₁c with
    ⟨x, hx, hk⟩ | e | e
  · obtain ⟨a', ha'A, rfl⟩ := exists_eq_piX_of_mem_aOne hx
    exact Or.inl ⟨a', ha'A, hk.imp (inducesStdKind_of_lOne hAL hΦ₀ ha'A)
      (inducesStdKind_of_lOne hAL hΦ₀ ha'A)⟩
  · exact Or.inr (Or.inl (e.map Φ₀.trans))
  · exact Or.inr (Or.inr (e.map Φ₀.trans))

end CFSG.RankThree.PartTwo.Sec4
