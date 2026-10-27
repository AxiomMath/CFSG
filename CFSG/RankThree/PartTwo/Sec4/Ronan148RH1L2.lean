module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL264Tools
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKChevTwoL2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.GorensteinWalter CFSG.Open
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)
open CFSG.Assembly.RankThreeEven (projSL)

section General

variable {S : Type} [Group S]

theorem good427_of_comm [Finite S] {C : Subgroup S} (h : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) :
    Good427 C := by
  intro K hKC hKq _ _
  haveI : Group.IsPerfect K := hKq.1
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hab : ⁅K, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact h y (hKC hy) x (hKC hx)
  rw [Subgroup.commutator_eq_self] at hab
  exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt hab

theorem autFix_conj (x : S) : Sec4.autFix (MulAut.conj x) = Subgroup.centralizer ({x} : Set S) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  show x * y * x⁻¹ = y ↔ y * x = x * y
  constructor
  · intro h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h
    rw [← h]
    group

theorem autFix_eq_signalizerFixedSubgroup (α : MulAut S) :
    Sec4.autFix α = signalizerFixedSubgroup α := by
  ext y
  rfl

theorem autFix_conj_eq_map (g σ : MulAut S) :
    Sec4.autFix (g * σ * g⁻¹) = (Sec4.autFix σ).map g.toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨g⁻¹ x, ?_, ?_⟩
    · show σ (g⁻¹ x) = g⁻¹ x
      have h : (g * σ * g⁻¹) x = x := hx
      rw [MulAut.mul_apply, MulAut.mul_apply] at h
      have h2 := congrArg (fun y => g⁻¹ y) h
      simpa only [MulAut.inv_apply_self] using h2
    · show g (g⁻¹ x) = x
      exact MulAut.apply_inv_self _ g x
  · rintro ⟨y, hy, rfl⟩
    have hy' : σ y = y := hy
    show (g * σ * g⁻¹) (g y) = g y
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy']

end General

section PSL2

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem good427_psl2_inner (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {x : PSL2 F} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : Good427 (Subgroup.centralizer ({x} : Set (PSL2 F))) := by
  have hcyc : IsCyclic (Subgroup.centralizer ({x} : Set (PSL2 F))) :=
    Item462AltProof.ChevTwoL2.isCyclic_of_le_centralizer_psl2 hn hF (MulEquiv.refl _) hx3 hx1
      fun u hu => (Subgroup.mem_centralizer_singleton_iff.mp hu).symm
  refine good427_of_comm fun a ha b hb => ?_
  exact congrArg Subtype.val ((IsCyclic.isMulCommutative
    (α := Subgroup.centralizer ({x} : Set (PSL2 F)))).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem good427_psl2_field (hn : 1 ≤ n) (h6 : n ≠ 6) (hF : Nat.card F = 2 ^ n) {τ : F ≃+* F}
    (hτ : orderOf τ = 3) : Good427 (signalizerFixedSubgroup (psl2FieldAut F τ)) := by
  obtain ⟨e1⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut
    (by decide : Odd 3) hτ
  have hk := CFSG.RankThree.LinearTwo.card_fixedSubfield Nat.prime_two hn hF τ
  rw [hτ] at hk
  obtain ⟨h3n, hcard⟩ := hk
  obtain ⟨j, rfl⟩ := h3n
  have hj : 3 * j / 3 = j := by omega
  rw [hj] at hcard
  have hj0 : j ≠ 0 := by
    rintro rfl
    omega
  have hj2 : j ≠ 2 := by
    rintro rfl
    exact h6 rfl
  set C := signalizerFixedSubgroup (psl2FieldAut F τ)
  rcases Nat.lt_or_ge j 2 with hj1 | hj3
  ·
    have hj1' : j = 1 := by omega
    subst hj1'
    refine good427_of_not_five_dvd ?_
    rw [Nat.card_congr e1.toEquiv,
      Item462AltProof.ChevTwoL2.card_psl2_of_card_two (by rw [hcard]; norm_num)]
    norm_num
  ·
    have hj3' : 3 ≤ j := by omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h4 : 4 ≤ Nat.card (fixedSubfield F τ) := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hsimp, hsolv⟩ :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable h4
    haveI : IsSimpleGroup C := (MulEquiv.isSimpleGroup_congr e1).mpr hsimp
    have hna : ∃ a b : C, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      apply hsolv
      haveI : IsMulCommutative C := ⟨⟨hcon⟩⟩
      have : Group.IsSolvable C := inferInstance
      exact (Group.isSolvable_of_surjective (f := (e1 : C →* _)) e1.surjective)
    let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedSubfield F τ) 2 j
      (by omega) hcard
    have hcardC : Nat.card C = 2 ^ j * ((2 ^ j) ^ 2 - 1) := by
      rw [Nat.card_congr (e1.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF
        (Fin 2))).toEquiv, CFSG.Walter.psl2_even_card hj0]
    have h60 : Nat.card C ≠ 60 := by
      rw [hcardC]
      intro h
      have h8 : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3'
      have h64 : 64 ≤ (2 ^ j) ^ 2 := by nlinarith
      have : 8 * 63 ≤ 2 ^ j * ((2 ^ j) ^ 2 - 1) :=
        Nat.mul_le_mul (by simpa using h8) (by omega)
      omega
    exact good427_of_le_simple le_rfl hna h60 fun K hKC _ => hKC

theorem noCfgS427_psl2 (hn : 2 ≤ n) (h6 : n ≠ 6) (hF : Nat.card F = 2 ^ n) :
    NoCfgS427 (PSL2 F) := by
  intro σ h3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  by_cases hD : σ ∈ (pglAction F).range
  · obtain ⟨x, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three hD h3
    have hinj := Item434SmallTwoOther.L264.conj_injective_psl2 F
    have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact h3)
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact h1 (map_one _)
    rw [autFix_conj]
    exact good427_psl2_inner hn hF hx3 hx1
  · obtain ⟨τ, hτ, g, hg⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three σ hord hD
    rw [hg, autFix_conj_eq_map, autFix_eq_signalizerFixedSubgroup]
    exact Good427.map_mulEquiv _ (good427_psl2_field (by omega) h6 hF hτ)

end PSL2

section Transfer




theorem row427_of_noCfg_cent
    {S : Type} [Group S] [Finite S]
    (h : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → NoCfgS427 S')
    (hc : ∀ y : S, y ≠ 1 → y ^ 3 = 1 → ∀ a ∈ Subgroup.centralizer ({y} : Set S),
      ∀ b ∈ Subgroup.centralizer ({y} : Set S), a * b = b * a) :
    Row427 S := by
  intro G _ _ hG A hA _ hθ L hL ⟨e⟩ d hdA hd1 _ hLd K hK htype
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL) hdA
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hσ3 : descAut L ⟨d, hdN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hσ1 : descAut L ⟨d, hdN⟩ ≠ 1 := by
    intro h1
    apply hLd
    have hdC := (descAut_eq_one_iff hL.1.1 ⟨d, hdN⟩).mp h1
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdC l hl
  have hle := map_le_autFix hdN (hK'M.trans inf_le_right)
  rcases htype with ⟨⟨φ⟩⟩ | ⟨hdK, -⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have eKL : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
    have hK₁q : IsQuasisimple (K'.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eKL.symm hK'q
    have hZK : Subgroup.center (K'.subgroupOf L ⧸ CFSG.pCore 2 (K'.subgroupOf L)) = ⊥ := by
      haveI := (isA5Type_quot_congr eKL hT).isSimpleGroup
      haveI : Group.IsPerfect (K'.subgroupOf L) := hK₁q.1
      exact center_eq_bot_of_isSimpleGroup_of_isPerfect
    have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ :=
      inf_eq_bot_of_center_eq_bot hK₁q hZK le_rfl hZ3
    have eB := equivBar hK'L hinf
    have hsn := isSubnormal_bar hdN hK'M hK'sn
    exact (h (L ⧸ Subgroup.center L) ⟨e⟩) _ hσ3 hσ1 _ hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn (isA5Type_quot_congr eB.symm hT)
  ·
    have hdK' : d ∈ K' := hK' ▸ hdK
    have hdL : d ∈ L := hK'L hdK'
    set y : L ⧸ Subgroup.center L := ((⟨d, hdL⟩ : L) : L ⧸ Subgroup.center L) with hy
    have hσ : descAut L ⟨d, hdN⟩ = MulAut.conj y := Ronan148S.descAut_eq_conj hdL
    have hy1 : y ≠ 1 := by
      intro h1
      apply hσ1
      rw [hσ, h1, map_one]
    have hy3 : y ^ 3 = 1 := by
      rw [hy, ← QuotientGroup.mk_pow]
      have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, QuotientGroup.mk_one]
    set K₁ : Subgroup L := K'.subgroupOf L with hK₁
    set Kb : Subgroup (L ⧸ Subgroup.center L) := K₁.map (QuotientGroup.mk' (Subgroup.center L))
      with hKb
    have hKbC : Kb ≤ Subgroup.centralizer ({y} : Set (L ⧸ Subgroup.center L)) := by
      rw [← autFix_conj, ← hσ]
      exact hle
    have hcomm : ∀ a ∈ Kb, ∀ b ∈ Kb, a * b = b * a := by
      intro a ha b hb
      have hmem : ∀ x ∈ Kb, e x ∈ Subgroup.centralizer ({e y} : Set S) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.mp (hKbC hx)
        rw [← map_mul, ← map_mul, this]
      have h1 : e y ≠ 1 := by
        rw [Ne, map_eq_one_iff e e.injective]
        exact hy1
      have h3 : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
      have := hc (e y) h1 h3 (e a) (hmem a ha) (e b) (hmem b hb)
      apply e.injective
      rw [map_mul, map_mul, this]
    have eKL : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
    haveI : Group.IsPerfect K' := hK'q.1
    haveI : Group.IsPerfect K₁ := Group.IsPerfect.ofSurjective (f := (eKL.symm : K' →* K₁))
      eKL.symm.surjective
    haveI : Group.IsPerfect Kb := Group.IsPerfect.map _
    haveI : IsMulCommutative Kb := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    have hKb1 : ∀ x ∈ Kb, x = 1 := fun x hx =>
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Kb) 1)
    have hK'Z : ∀ k ∈ K', ∀ l ∈ L, k * l = l * k := by
      intro k hk l hl
      have hkL : k ∈ L := hK'L hk
      have hmk : QuotientGroup.mk' (Subgroup.center L) (⟨k, hkL⟩ : L) = 1 :=
        hKb1 _ ⟨⟨k, hkL⟩, hk, rfl⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmk ⟨l, hl⟩).symm
    haveI : Nontrivial K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'q
    haveI : IsMulCommutative K' :=
      ⟨⟨fun a b => Subtype.ext (hK'Z a a.2 b (hK'L b.2))⟩⟩
    exact Group.IsPerfect.not_isMulCommutative K' inferInstance

end Transfer

section Rows

theorem false_of_simple_psl2_two {S : Type} [Group S] [Finite S] [hs : IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (h6 : Nat.card S = 6) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 1) (by rw [h6]; norm_num)
  rw [pow_one] at hP
  have hidx : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hP, h6] at h
    omega
  haveI := Subgroup.normal_of_index_eq_two hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
  · rw [hb, Subgroup.card_bot] at hP
    omega
  · rw [ht, Subgroup.card_top, h6] at hP
    omega

theorem statedScalars_subgroupOf_statedSL2_eq_bot {F : Type} [Field F] [CharP F 2] :
    (CFSG.Open.StatedScalars (Fin 2) F).subgroupOf (CFSG.Open.StatedSL 2 F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hdet : Matrix.GeneralLinearGroup.det (x : GL (Fin 2) F) = 1 :=
    MonoidHom.mem_ker.mp ((CFSG.Open.StatedAPI.statedSL_eq_ker_det 2 F).le x.2)
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc2 : ((c : F)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hdet, Units.val_one]
  have hc1 : c = 1 := Units.ext (CharTwo.sq_injective (by simpa using hc2))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem center_eq_bot_of_psl2_even
    {F : Type} [Field F] [Finite F] [CharP F 2] {L : Type} [Group L]
    [Finite L] (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* projSL 2 F) : Subgroup.center L = ⊥ := by
  haveI : Group.IsPerfect L := hL.1
  have hodd : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨φ, -, -, hD⟩ := CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map
    (K := F) (n := 2) le_rfl hodd (e.trans (CFSG.PGLModel.projSLEquivStatedProj 2 F))
  rw [← hD, statedScalars_subgroupOf_statedSL2_eq_bot, Subgroup.map_bot]




theorem rowOf427_sl2_of_ne_six
    {n : ℕ} (hn : 1 ≤ n) (h6 : n ≠ 6) :
    RowOf427 (projSL 2 (GaloisField 2 n)) := by
  intro S _ _ hs hna ⟨eSX⟩
  set F := GaloisField 2 n
  have hF : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  let eP : S ≃* PSL2 F := eSX.trans (projSLEquivPSL F)
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · exfalso
    have hn1' : n = 1 := by omega
    have hF2 : Nat.card F = 2 := by rw [hF, hn1']; norm_num
    exact false_of_simple_psl2_two hna
      (by rw [Nat.card_congr eP.toEquiv,
        Item462AltProof.ChevTwoL2.card_psl2_of_card_two hF2])
  refine row427_of_noCfg_cent (fun S' _ _ ⟨e'⟩ =>
    NoCfgS427.of_mulEquiv (e'.trans eP) (noCfgS427_psl2 hn2 h6 hF)) ?_
  intro y hy1 hy3 a ha b hb
  have hcyc : IsCyclic (Subgroup.centralizer ({y} : Set S)) :=
    Item462AltProof.ChevTwoL2.isCyclic_of_le_centralizer_psl2 hn2 hF eP hy3 hy1
      fun u hu => (Subgroup.mem_centralizer_singleton_iff.mp hu).symm
  exact congrArg Subtype.val ((IsCyclic.isMulCommutative
    (α := Subgroup.centralizer ({y} : Set S))).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
