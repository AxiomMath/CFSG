module

public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofL34
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
public import CFSG.RankThree.PartTwo.Sec18.Item181b
public import CFSG.RankThree.PartTwo.Sec18.Item184a

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Item18ResProof

theorem exists_psi {Y : Type} [Group Y] {X : Subgroup Y} (hX : Sec4.IsZ3L34OrHeisSL34 X)
    {L : Subgroup Y} (hL : L = ⁅X, X⁆) :
    ∃ _ : L ⧸ Subgroup.center L ≃* projectiveSL 3 (GaloisField 2 2),
      commutator L = ⊤ ∧
      (∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c) ∧
      ¬ 2 ∣ Nat.card (Subgroup.center L) := by
  have hk : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
  rcases hX with he | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩
  ·
    obtain ⟨e⟩ := he
    set e' := e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with he'
    have hLeq : L = (KFacts.KS18.inrY e').range := hL.trans (KFacts.KS18.commutator_eq_range e')
    let φ : L ≃* projectiveSL 3 (GaloisField 2 2) :=
      (MulEquiv.subgroupCongr hLeq).trans
        (MonoidHom.ofInjective (KFacts.KS18.inrY_injective e')).symm
    have hZ : Subgroup.center L = ⊥ := by
      have h := Subgroup.map_center_eq φ
      rw [LinearThreeFourOuter.center_projectiveSL_three_eq_bot hk] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans φ),
      ?_, ?_, ?_⟩
    · have := KFacts.KS18.isPerfect_projectiveSL (GaloisField 2 2)
      have : Group.IsPerfect L :=
        Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      exact Group.IsPerfect.commutator_eq_top
    · intro x hx
      obtain ⟨p, z, rfl⟩ := KFacts.KS18.exists_eq_inrY_mul_inlY e' hx
      exact ⟨KFacts.KS18.inrY e' p, hLeq ▸ ⟨p, rfl⟩, KFacts.KS18.inlY e' z,
        hLeq ▸ KFacts.KS18.inlY_mem_centralizer e' z, rfl⟩
    · rw [hZ, Subgroup.card_bot]
      norm_num
  ·
    have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3
    have hLV : L = V.map X.subtype := by
      rw [hL, ← Subgroup.map_subtype_commutator, hcomm]
    let φ : L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
      (MulEquiv.subgroupCongr hLV).trans
        ((V.equivMapOfInjective X.subtype X.subtype_injective).symm.trans eV)
    refine ⟨QuotientGroup.congr (Subgroup.center L) (scalars 3 (GaloisField 2 2)) φ
      ((Subgroup.map_center_eq φ).trans (scalars_eq_center 3 (GaloisField 2 2)).symm),
      ?_, ?_, ?_⟩
    · have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
        CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
      have : Group.IsPerfect L :=
        Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      exact Group.IsPerfect.commutator_eq_top
    · intro x hx
      obtain ⟨u, hu, v, hv, huv⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hsup hUV ⟨x, hx⟩
      refine ⟨v, by rw [hLV]; exact ⟨v, hv, rfl⟩, u, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        rw [hLV] at hl
        obtain ⟨w, hw, rfl⟩ := hl
        exact congrArg Subtype.val (hUV u hu w hw).symm
      · have h1 : x = (u : Y) * (v : Y) := (congrArg Subtype.val huv).symm
        rw [h1]
        exact congrArg Subtype.val (hUV u hu v hv)
    · rw [KFacts.L34.card_center_of_mulEquiv φ]
      norm_num

theorem le_pCoreOf_of_le_normalizer
    (h1812 : Item181_2)
    {G : Type} [Group G] [Finite G] {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) {Q : Subgroup G} (hQL : Q ≤ inSubgroup perfectResidual H)
    (hQ2 : IsPGroup 2 Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    Q ≤ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  set Qc := CFSG.pCore 2 H with hQc
  set π : H →* H ⧸ Qc := QuotientGroup.mk' Qc with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set L := inSubgroup perfectResidual H with hLdef
  set Lb : Subgroup (H ⧸ Qc) := (perfectResidual H).map π with hLb
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hQc, mem_pCore_iff_mem_pCoreOf]
  have hLbn : Lb.Normal := by
    have hc := CFSG.perfect_residual_characterization (G := H)
    have : (perfectResidual H).Characteristic := hc.2.1
    exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective Qc)
  obtain ⟨s, ⟨hsS, -, -, hsH, Xb, hXbn, hXb, hXbt, -⟩, -, -⟩ := h1812 G A M h H hH
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have ht2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsH⟩)) := by
    have hT2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf H) := hS2.comap_subtype
    refine (hT2.map π).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hq2 : IsPGroup 2 ((H ⧸ Qc) ⧸ Xb) := by
    have h1 := ht2.map (QuotientGroup.mk' Xb)
    have h2 : (Subgroup.zpowers (π ⟨s, hsH⟩)).map (QuotientGroup.mk' Xb) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' Xb)
        (QuotientGroup.mk'_surjective Xb), ← hXbt, Subgroup.map_sup,
        (QuotientGroup.map_mk'_self Xb), bot_sup_eq]
    rw [h2] at h1
    exact h1.of_equiv Subgroup.topEquiv
  have hqs : Group.IsSolvable ((H ⧸ Qc) ⧸ Xb) := by
    have := hq2.isNilpotent
    infer_instance
  have hAX : ∀ a (ha : a ∈ H), a ∈ A → π ⟨a, ha⟩ ∈ Xb := by
    intro a ha haA
    refine mem_of_isPGroup_quotient hq2 (k := 1) ?_
    rw [pow_one, ← map_pow]
    have : (⟨a, ha⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 a haA)
    rw [this, map_one]
  have hLbXX : Lb = ⁅Xb, Xb⁆ := by
    have hXXp : ⁅⁅Xb, Xb⁆, ⁅Xb, Xb⁆⁆ = ⁅Xb, Xb⁆ := by
      rcases hXb with he | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩
      · obtain ⟨e⟩ := he
        set e' := e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
          (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with he'
        rw [KFacts.KS18.commutator_eq_range e']
        have := KFacts.KS18.isPerfect_projectiveSL (GaloisField 2 2)
        rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
          Group.IsPerfect.commutator_eq_top]
      · have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3
        have hXX : ⁅Xb, Xb⁆ = V.map Xb.subtype := by
          rw [← Subgroup.map_subtype_commutator, hcomm]
        have : Group.IsPerfect V := by
          have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
            CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
          exact Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
        rw [hXX, ← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator,
          Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hLb, map_perfectResidual_eq (QuotientGroup.mk'_surjective Qc)]
    exact perfectResidual_eq_commutator hqs hXXp
  obtain ⟨ψ, hLp, hXLC, hZodd⟩ := exists_psi hXb hLbXX
  set f : A.subgroupOf H →* H ⧸ Qc := π.comp (A.subgroupOf H).subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, hmemR] at ha
    have hbot := inf_eq_bot_of_elemAbelian_three hA.1 hR2
    have : ((a : H) : G) ∈ A ⊓ R := ⟨Subgroup.mem_subgroupOf.mp a.2, ha⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext this))
  set Ab := f.range with hAb
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, ← hA.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hAexp : ∀ a : A.subgroupOf H, a ^ 3 = 1 := fun a =>
    Subtype.ext (by simpa using (isE27_subgroupOf hA hAH).1.2 (a : H) a.2)
  have hAb3 : IsPGroup 3 Ab := by
    rintro ⟨_, a, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one]; simp [← map_pow, hAexp a])⟩
  have hAbX : Ab ≤ Xb := by
    rintro _ ⟨a, rfl⟩
    exact hAX _ (a : H).2 (Subgroup.mem_subgroupOf.mp a.2)
  have hRL : R ⊓ L ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hx), Subgroup.le_normalizer hx⟩)
      (hR2.to_le inf_le_left)
  have hEC : Nat.card ↥(Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Qc))) ≤ 3 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := (hAb3.to_le (inf_le_left :
      Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Qc)) ≤ Ab)).exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra hn'
      interval_cases n <;> simp_all
    have hdvd : 3 ^ 2 ∣ Nat.card ↥(Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Qc))) :=
      hn ▸ pow_dvd_pow 3 hn2
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    set K' : Subgroup (H ⧸ Qc) := K.map (Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Qc))).subtype
    have hK'9 : Nat.card K' = 9 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
      norm_num
    have hK'le : K' ≤ Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Qc)) := Subgroup.map_subtype_le K
    set B : Subgroup G := ((K'.comap f).map (A.subgroupOf H).subtype).map H.subtype with hB
    have hBA : B ≤ A := by
      rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mp a.2
    have hB9 : Nat.card B = 9 := by
      rw [hB, Subgroup.card_map_of_injective H.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      have h1 : (K'.comap f).map f = K' :=
        Subgroup.map_comap_eq_self (hK'le.trans inf_le_left)
      rw [← Subgroup.card_map_of_injective hfinj, h1, hK'9]
    have hBcomm : ∀ l ∈ L, ∀ b ∈ B, l * b * l⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      rintro l hl _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have haC : f a ∈ Subgroup.centralizer (Lb : Set (H ⧸ Qc)) := (hK'le ha).2
      have hlLb : π ⟨l, hLH hl⟩ ∈ Lb := by
        obtain ⟨l', hl', hl'l⟩ := hl
        refine ⟨l', hl', ?_⟩
        congr 1
        exact Subtype.ext hl'l
      have hc := Subgroup.mem_centralizer_iff.mp haC _ hlLb
      have h1 : π (⟨l, hLH hl⟩ * (a : H) * ⟨l, hLH hl⟩⁻¹ * (a : H)⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [show π (a : H) = f a from rfl, hc]
        group
      have h2 := (hmemR _).mp h1
      have hlN : (a : H).1 ∈ Subgroup.normalizer (L : Set G) :=
        le_normalizer_inSubgroup_perfectResidual H (a : H).2
      have h3 : l * ((a : H) : G) * l⁻¹ * ((a : H) : G)⁻¹ ∈ L := by
        have h4 : ((a : H) : G) * l⁻¹ * ((a : H) : G)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp hlN _).mp (L.inv_mem hl)
        have := L.mul_mem hl h4
        simpa only [mul_assoc] using this
      exact hRL ⟨by simpa using h2, h3⟩
    have hBe : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le hA.1 hBA
    have hLM : L ≤ M :=
      le_of_commutator_le_of_gamma_le hA (fun x hx => h.mem_scriptM.2 hx) hBA
        (two_le_pRank_of_elemAbelian hBe hB9.ge) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
        (hAH.trans ((le_normalizer_inSubgroup_perfectResidual H).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hBcomm
    exact perfectResidual_not_le_of_mem_scriptH h hH hLM
  obtain ⟨E9, hE9, hE9act⟩ := KFacts.KS18.exists_E9 ψ hk hLp hXLC hAbX hAb3 hAb27 hEC
  set Qb : Subgroup (H ⧸ Qc) := (Q.subgroupOf H).map π with hQb
  have hQbLb : Qb ≤ Lb := by
    rintro _ ⟨x, hx, rfl⟩
    have hxL : (x : G) ∈ L := hQL (Subgroup.mem_subgroupOf.mp hx)
    obtain ⟨y, hy, hyx⟩ := hxL
    refine ⟨y, hy, ?_⟩
    congr 1
    exact Subtype.ext hyx
  have hQb2 : IsPGroup 2 Qb := (hQ2.comap_subtype (K := H)).map π
  have hAbQb : ∀ y ∈ Ab, ∀ q ∈ Qb, y * q * y⁻¹ ∈ Qb := by
    rintro _ ⟨a, rfl⟩ _ ⟨x, hx, rfl⟩
    have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    have haQ := hAQ (Subgroup.mem_subgroupOf.mp a.2)
    refine ⟨(a : H) * x * (a : H)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp haQ _).mp hxQ
    · simp [hf]
  set ρ : Lb →* projectiveSL 3 (GaloisField 2 2) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Lb)) with hρ
  set Qt : Subgroup (projectiveSL 3 (GaloisField 2 2)) := (Qb.subgroupOf Lb).map ρ with hQt
  have hQt2 : IsPGroup 2 Qt := (hQb2.comap_subtype (K := Lb)).map ρ
  have hconjQt : ∀ g ∈ E9, ∀ x ∈ Qt, g * x * g⁻¹ ∈ Qt := by
    rintro g hg _ ⟨q, hq, rfl⟩
    obtain ⟨y, hy, hyg⟩ := hE9act g hg
    have h1 := KFacts.KS18.actOn_apply Lb ψ y q
    rw [hyg, MulAut.conj_apply] at h1
    have h2 : g * ρ q * g⁻¹ = ρ (MulAut.conjNormal y q) := h1
    rw [h2]
    refine ⟨MulAut.conjNormal y q, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    rw [MulAut.conjNormal_apply]
    exact hAbQb y hy _ (Subgroup.mem_subgroupOf.mp hq)
  have hE9Qt : E9 ≤ Subgroup.normalizer (Qt : Set (projectiveSL 3 (GaloisField 2 2))) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjQt g hg x, fun hx => ?_⟩
    have := hconjQt g⁻¹ (E9.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hQtbot : Qt = ⊥ := l34_eq_bot_of_le_normalizer hk hE9 hQt2 hE9Qt
  have hQbZ : Qb.subgroupOf Lb ≤ Subgroup.center Lb := by
    intro q hq
    have h1 : ρ q ∈ Qt := ⟨q, hq, rfl⟩
    rw [hQtbot, Subgroup.mem_bot] at h1
    have h2 : QuotientGroup.mk' (Subgroup.center Lb) q = 1 := by
      have := ψ.injective (h1.trans (map_one ψ).symm)
      exact this
    exact (QuotientGroup.eq_one_iff q).mp h2
  have hQbbot : Qb = ⊥ := by
    have h2 : IsPGroup 2 (Qb.subgroupOf Lb) := hQb2.comap_subtype
    have hdvd : Nat.card (Qb.subgroupOf Lb) ∣ Nat.card (Subgroup.center Lb) :=
      Subgroup.card_dvd_of_le hQbZ
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    have hm0 : m = 0 := by
      by_contra hm0
      apply hZodd
      rw [hm] at hdvd
      exact (dvd_pow_self 2 hm0).trans hdvd
    have h1 : Qb.subgroupOf Lb = ⊥ := by
      rw [hm0, pow_zero] at hm
      exact Subgroup.eq_bot_of_card_eq _ hm
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hQbLb hx⟩ : Lb) ∈ Qb.subgroupOf Lb := Subgroup.mem_subgroupOf.mpr hx
    rw [h1, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  intro x hx
  have hxH : x ∈ H := hLH (hQL hx)
  have h1 : π ⟨x, hxH⟩ ∈ Qb := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [hQbbot, Subgroup.mem_bot] at h1
  exact hRL ⟨(hmemR _).mp h1, hQL hx⟩

end Item18ResProof

end CFSG.RankThree.PartTwo.Sec18
