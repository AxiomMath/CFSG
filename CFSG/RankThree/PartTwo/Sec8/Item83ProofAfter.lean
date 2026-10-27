module

public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec10.Item10Std
public import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.RankThree.Asc83Table.E9
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian p A)
    (hBA : B ≤ A) : CFSG.Assembly.IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hA hBA

theorem card_closure_triple {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) {c a d : G}
    (hc : c ∈ A) (ha : a ∈ A) (hd : d ∈ A)
    (hca : Nat.card (Subgroup.closure ({c, a} : Set G)) = 9)
    (hdca : d ∉ Subgroup.closure ({c, a} : Set G)) :
    Nat.card (Subgroup.closure ({c, a, d} : Set G)) = 27 := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCA : Subgroup.closure ({c, a} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hc
    · exact ha
  have hd1 : d ≠ 1 := fun h1 => hdca (h1 ▸ one_mem _)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.2 d hd) hd1
  have hset : ({c, a, d} : Set G) = {c, a} ∪ {d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  have hN : Subgroup.zpowers d ≤
      Subgroup.normalizer (Subgroup.closure ({c, a} : Set G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    exact hcomm y (hCA hy) d hd
  have hdisj : Disjoint (Subgroup.closure ({c, a} : Set G)) (Subgroup.zpowers d) := by
    rw [Subgroup.disjoint_def]
    intro x hx hxd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxd
    by_contra hx1
    apply hdca
    have h1 : Subgroup.zpowers (d ^ k) = Subgroup.zpowers d := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers d k))
      rw [Nat.card_zpowers, Nat.card_zpowers, hd3]
      have h2 : orderOf (d ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA.2 d hd, one_zpow])
      rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h3 | h3
      · exact absurd (orderOf_eq_one_iff.mp h3) hx1
      · omega
    have h3 : d ∈ Subgroup.zpowers (d ^ k) := h1 ▸ Subgroup.mem_zpowers d
    exact Subgroup.zpowers_le.mpr hx h3
  rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj, hca,
    Nat.card_zpowers, hd3]

theorem exists_twoGroup_le_of_imageModTheta {L K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (ha3 : a ^ 3 = 1) {X : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hX1 : X ≠ ⊥)
    (hX2 : IsPGroup 2 X)
    (hXK : X ≤ imageModTheta L K)
    (hXa : ∀ τ ∈ autThetaQuot (Subgroup.zpowers a) L, ∀ x ∈ X, τ x ∈ X) :
    ∃ T : Subgroup G, T ≤ K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ a ∈ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y' : Subgroup L := K.subgroupOf L ⊓ X.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))
    with hY'
  set φ : Y' →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp Y'.subtype with hφ
  have hrange : φ.range = X := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact y.2.2
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := hXK hx
      exact ⟨⟨k, hk, hx⟩, rfl⟩
  have hker : Nat.card φ.ker ∣ Nat.card (aschbacherSolvableCore 3 L) := by
    have hle : φ.ker.map Y'.subtype ≤ aschbacherSolvableCore 3 L := by
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
      rw [← QuotientGroup.ker_mk' (aschbacherSolvableCore 3 L), MonoidHom.mem_ker]
      exact hy
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective Y'.subtype_injective] at h1
  have hcard : Nat.card Y' = Nat.card φ.ker * Nat.card X := by
    rw [← hrange]
    exact (Subgroup.card_ker_mul_card_range φ).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX2
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hX1
    rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq X hk
  have hY3 : ¬ 3 ∣ Nat.card Y' := by
    rw [hcard, hk]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · exact not_three_dvd_card_aschbacherSolvableCore L (h3.trans hker)
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  have hY2 : 2 ∣ Nat.card Y' := by
    rw [hcard, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hfwd : ∀ g ∈ Subgroup.zpowers a, ∀ y ∈ Y'.map L.subtype,
      g * y * g⁻¹ ∈ Y'.map L.subtype := by
    intro g hg y hy
    have hgN : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr ha hg
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr haK hg
    obtain ⟨ℓ, ⟨hℓK, hℓX⟩, rfl⟩ := hy
    have hτ : thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hgN⟩) ∈
        autThetaQuot (Subgroup.zpowers a) L := mem_autThetaQuot_iff.mpr ⟨g, hgN, hg, rfl⟩
    refine ⟨L.normalizerMonoidHom ⟨g, hgN⟩ ℓ, ⟨?_, ?_⟩, rfl⟩
    · change g * (ℓ : G) * g⁻¹ ∈ K
      exact (Subgroup.mem_normalizer_iff.mp hgK ℓ).mp hℓK
    · change QuotientGroup.mk' (aschbacherSolvableCore 3 L) (L.normalizerMonoidHom ⟨g, hgN⟩ ℓ) ∈ X
      rw [QuotientGroup.mk'_apply, ← thetaQuotMulAut_mk]
      exact hXa _ hτ _ hℓX
  have hEY : Subgroup.zpowers a ≤
      Subgroup.normalizer ((Y'.map L.subtype : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd g hg y, fun hy => ?_⟩
    have h1 := hfwd g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using h1
  have hA3 : IsPGroup 3 (Subgroup.zpowers a) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (orderOf_dvd_of_pow_eq_one (show a ^ 3 ^ 1 = 1 by rw [pow_one]; exact ha3))
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨T, hTY, hT1, hT2, hTa⟩ := CFSG.RankThree.PartTwo.Sec10.exists_pGroup_le_normalizer
    (p := 3) (q := 2) hA3 (by rwa [Subgroup.card_map_of_injective L.subtype_injective])
    (by rwa [Subgroup.card_map_of_injective L.subtype_injective]) hEY
  refine ⟨T, fun t ht => ?_, hT1, hT2, hTa (Subgroup.mem_zpowers a)⟩
  obtain ⟨ℓ, ⟨hℓK, -⟩, rfl⟩ := hTY ht
  exact hℓK

theorem mem_partTwoF_of_card (h611 : Sec6.Item6_11_1) (hG : PartTwoStanding G)
    {A₀ E : Subgroup G} (hA₀ : CFSG.Assembly.IsElemAbelian 3 A₀) (h81 : Nat.card A₀ = 81)
    (hE : E ∈ partTwoE G) (hEA : E ≤ A₀) : A₀ ∈ partTwoF G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hA₀, fun B hB hAB => ?_, E, hE, hEA⟩
  obtain ⟨A₁, hBA₁, hmax⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hB
  have hA₁F : A₁ ∈ partTwoF G :=
    ⟨hmax.prop, fun B' hB' hA₁B' => le_antisymm (hmax.2 hB' hA₁B') hA₁B', E, hE,
      hEA.trans (hAB.trans hBA₁)⟩
  have hrank := h611 G hG A₁ hA₁F
  have hA₁p : IsPGroup 3 A₁ := fun g => ⟨1, Subtype.ext (by simpa using hmax.prop.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA₁p
  have hk4 : k ≤ CFSG.Open.pRank 3 A₁ :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three A₁)
      ⟨A₁, le_rfl, hmax.prop, hk⟩
  have hcard : Nat.card A₁ ≤ 81 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 81 := by norm_num
  have hA₀A₁ : A₀ = A₁ := Subgroup.eq_of_le_of_card_ge (hAB.trans hBA₁) (by omega)
  exact le_antisymm (hA₀A₁ ▸ hBA₁) hAB

section Inputs


@[expose] def KF83KBarTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (A₀ : Subgroup G) (d : G) (n : ℕ), Hyp81 G A c L a → 27 < Nat.card A →
      Data83 G c L a A₀ d n →
        ∃ X : Subgroup (L ⧸ aschbacherSolvableCore 3 L), X ≠ ⊥ ∧ IsPGroup 2 X ∧
          X ≤ imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ∧
          ∀ τ ∈ Sec4.autThetaQuot (Subgroup.zpowers a) L, ∀ x ∈ X, τ x ∈ X

@[expose] def KF83Indep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (A₀ : Subgroup G) (d : G) (n : ℕ), Hyp81 G A c L a → 27 < Nat.card A →
      Data83 G c L a A₀ d n → d ∉ Subgroup.closure ({c, a} : Set G)

@[expose] def KF83D4Distinct : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), Odd n → IsoTrialityD4 X n →
    ¬ IsoReeF4 X (3 * n) ∧ ¬ IsoSUThree X (2 ^ (3 * n)) ∧ IsEmpty (X ≃* projSU 3 2 (3 * n)) ∧
      IsEmpty (X ≃* projSp 2 (GaloisField 2 (3 * n)))

end Inputs

section After


theorem item83After_of_distinct (h611 : Sec6.Item6_11_1) (hKB : KF83KBarTwo) (hInd : KF83Indep)
    (hDist : KF83D4Distinct) : Item83After := by
  intro G _ _ A c L a h hA A₀ d n hd
  have hA₀e := hd.isElemAbelian
  have hcomm : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA₀e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := hA₀e.2 a hd.a_mem
  have hc3 : c ^ 3 = 1 := hA₀e.2 c hd.c_mem
  have hca : c * a = a * c := hcomm c hd.c_mem a hd.a_mem
  have hcL : L ≤ Subgroup.centralizer {c} := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcy y hy).symm)
  have hac : a ∉ Subgroup.zpowers c := by
    intro h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply h.not_isInnerAut_induced
    have hk' : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ k :=
      Subtype.ext (by simp [hk])
    rw [hk', map_zpow, map_zpow, thetaQuotMulAut_compAction_eq_one hcN hcy, one_zpow]
    exact ⟨1, map_one _⟩
  have hca9 := CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 ha3 hca h.ne_one hac
  have hEA₀ : Subgroup.closure ({c, a, d} : Set G) ≤ A₀ := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact hd.c_mem
    · exact hd.a_mem
    · exact hd.d_mem
  have hE27 := card_closure_triple hA₀e hd.c_mem hd.a_mem hd.d_mem hca9
    (hInd G A c L a A₀ d n h hA hd)
  have hEe := isElemAbelian_of_le hA₀e hEA₀
  obtain ⟨X, hX1, hX2, hXK, hXa⟩ := hKB G A c L a A₀ d n h hA hd
  have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≤ L :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hKd : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≤
      Subgroup.centralizer {d} := (Subgroup.map_subtype_le _).trans inf_le_right
  have hda : d * a = a * d := hcomm d hd.d_mem a hd.a_mem
  have haLd : a ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
    have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hda.symm)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp ha y),
      (Subgroup.mem_normalizer_iff.mp haC y)]
  have haK : a ∈ Subgroup.normalizer
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ haLd
  obtain ⟨T, hTK, hT1, hT2, hTa⟩ := exists_twoGroup_le_of_imageModTheta ha haK ha3 hX1 hX2 hXK hXa
  have hET : Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
      exact (hcy t (hKL (hTK ht))).symm
    · exact hTa
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKd (hTK ht))
  have hEmem : Subgroup.closure ({c, a, d} : Set G) ∈ partTwoE G := ⟨hEe, hE27, T, hT1, hT2, hET⟩
  have hTmem : T ∈ invariantPiSubgroups L (Subgroup.closure ({c, a, d} : Set G)) (piOf 2) :=
    ⟨hTK.trans hKL, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2, hET⟩
  have hA₀F := mem_partTwoF_of_card h611 h.toPartTwoStanding hA₀e hd.card_eq hEmem hEA₀
  have hHyp : ∀ a' ∈ A₀, a' ≠ 1 →
      (InducesStdKind L a' .field ∨ InducesStdKind L a' .graphField) → Hyp81 G A₀ c L a' :=
    fun a' ha' ha'1 hkind =>
      { toPartTwoStanding := h.toPartTwoStanding
        mem_partTwoF := hA₀F
        mem_A := hd.c_mem
        ne_one := h.ne_one
        mem_thetaComponentsAt := h.mem_thetaComponentsAt
        sectionCentralizer_eq := hd.sectionCentralizer_eq
        a_mem := ha'
        a_ne_one := ha'1
        inducesStdKind := hkind
        exists_invariant_two := fun _ => ⟨_, hEmem, hEA₀, T, hTmem, hT1⟩
        partTwoE_eq := fun h27 => absurd (h27.symm.trans hd.card_eq) (by norm_num) }
  refine ⟨hEmem, hA₀F, ?_⟩
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hd.odd
    omega
  have hG2 : IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
      IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n := by
    rintro ⟨K, _, _, hK, ⟨e⟩⟩
    obtain ⟨-, k', hk', hk'', hC⟩ := barCentralizer_mulEquiv_g2 hn0 hK ha3 h.inducesOuterTheta e
    exact ⟨k', hk', hk'', hC⟩
  have hA := hDist (L ⧸ aschbacherSolvableCore 3 L) n hd.odd
  rcases hd.cases with ⟨hL1, hKbar, hC | ⟨hD4, hPGU, a₀, ha₀A, ha₀1, ha₀k, hC₀⟩⟩ | hc2 | hc3 | hc4 |
    hc5
  · exact ⟨a, hd.a_mem, hHyp a hd.a_mem h.a_ne_one h.inducesStdKind, hd, fun _ => hC⟩
  · refine ⟨a₀, ha₀A, hHyp a₀ ha₀A ha₀1 (Or.inr ha₀k), ?_, fun _ => hC₀⟩
    exact ⟨hd.le_normalizer, hd.c_mem, ha₀A, hd.isElemAbelian, hd.card_eq,
      hd.sectionCentralizer_eq, hd.d_mem, hd.d_ne_one, hd.innerDiag, hd.odd, hd.ne_bot,
      Or.inl ⟨hL1, hKbar, Or.inl hC₀⟩⟩
  · refine ⟨a, hd.a_mem, hHyp a hd.a_mem h.a_ne_one h.inducesStdKind, hd, ?_⟩
    rintro (hD4 | hG)
    · exact absurd hc2.1 (hA hD4).1
    · exact hG2 hG
  · refine ⟨a, hd.a_mem, hHyp a hd.a_mem h.a_ne_one h.inducesStdKind, hd, ?_⟩
    rintro (hD4 | hG)
    · exact absurd hc3.1 (hA hD4).2.1
    · exact hG2 hG
  · refine ⟨a, hd.a_mem, hHyp a hd.a_mem h.a_ne_one h.inducesStdKind, hd, ?_⟩
    rintro (hD4 | hG)
    · exact ((hA hD4).2.2.1.false hc4.1.some).elim
    · exact hG2 hG
  · refine ⟨a, hd.a_mem, hHyp a hd.a_mem h.a_ne_one h.inducesStdKind, hd, ?_⟩
    rintro (hD4 | hG)
    · exact ((hA hD4).2.2.2.false hc5.1.some).elim
    · exact hG2 hG

end After

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
