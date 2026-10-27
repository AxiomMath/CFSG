module

public import CFSG.Quasithin.EmptyFaithful.S153D54

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.S1417
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G]

@[expose] def IsRankTwoListType (L : Subgroup G) : Prop :=
  IsAltBlockType L 6 ∨ IsAltBlockType L 7 ∨ IsHatA6Block L ∨ IsExcA7Block L ∨ IsG2Block L ∨
    IsSp4Quot L ∨ IsLnTwoQuot L 4 ∨ IsLnTwoQuot L 5

end Vocabulary

@[expose] def ThreeRankBlocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      CFSG.Open.pRank 3 L = 1) ∧
    (∀ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n →
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) →
      (Odd n → CFSG.Open.pRank 3 L = 1) ∧ (Even n → CFSG.Open.pRank 3 L = 2)) ∧
    (IsSp4Quot L ∨ IsLnTwoQuot L 4 ∨ IsLnTwoQuot L 5 → CFSG.Open.pRank 3 L = 2)

@[expose] def SolvOvergroupsThreePrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ X : Subgroup G),
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Odd n ∧ 3 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∨
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)))) →
    IsSylowTwoOf S₀ L → S₀ ≤ X → X ≤ L → Group.IsSolvable ↥X → ¬ 3 ∣ Nat.card ↥X

@[expose] def ThetaEqComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I L : Subgroup G), SQTKGroup ↥I → L ∈ cComp I →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → CFSG.Open.pRank 3 L = 2 → IsRankTwoListType L →
      thetaOf I = L

namespace S153F

open CFSG.Quasithin.S153D

section Helpers

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem isPGroup_three_OTwoQuot_Yp (hF : Facts15311 T M V₁ Yp I) : IsPGroup 3 (OTwoQuot Yp) := by
  rcases hF.struct_Yp with he | ⟨-, hcard, -⟩
  · obtain ⟨e⟩ := he
    have h3 : ∀ m : Multiplicative (Fin 2 → ZMod 3), m ^ 3 ^ 1 = 1 := by
      intro m
      apply Multiplicative.toAdd.injective
      funext i
      have h1 : ∀ a : ZMod 3, 3 • a = 0 := by decide
      simpa [toAdd_pow] using h1 (Multiplicative.toAdd m i)
    intro x
    refine ⟨1, ?_⟩
    apply e.injective
    rw [map_pow, map_one]
    exact h3 _
  · exact IsPGroup.of_card (n := 3) hcard

theorem exists_orderOf_eq_three_pow (hF : Facts15311 T M V₁ Yp I) {x : G} (hx : x ∈ Yp)
    (hodd : Odd (orderOf x)) : ∃ k : ℕ, orderOf x = 3 ^ k := by
  have hP := isPGroup_three_OTwoQuot_Yp hF
  let y : ↥Yp := ⟨x, hx⟩
  obtain ⟨k, hk⟩ := hP (QuotientGroup.mk y : OTwoQuot Yp)
  have hmem : y ^ 3 ^ k ∈ CFSG.Open.pCore 2 ↥Yp := by
    have : (QuotientGroup.mk (y ^ 3 ^ k) : OTwoQuot Yp) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hk
    exact (QuotientGroup.eq_one_iff _).mp this
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
    IsPGroup 2 (CFSG.Open.pCore 2 ↥Yp)) ⟨y ^ 3 ^ k, hmem⟩
  have hpow : y ^ (3 ^ k * 2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa [pow_mul] using this
  have hord : orderOf y ∣ 3 ^ k * 2 ^ j := orderOf_dvd_of_pow_eq_one hpow
  have hx' : orderOf y = orderOf x := Subgroup.orderOf_mk x hx
  have hodd' : Odd (orderOf y) := hx' ▸ hodd
  have hcop : Nat.Coprime (orderOf y) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd')
  have h3 : orderOf y ∣ 3 ^ k := hcop.dvd_of_dvd_mul_right hord
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
  exact ⟨i, hx' ▸ hi⟩

theorem exists_solvable_overgroup_three (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) :
    ∃ X : Subgroup G, Sgp153 T V₁ ⊓ L ≤ X ∧ X ≤ L ∧ Group.IsSolvable ↥X ∧ 3 ∣ Nat.card ↥X := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, -, -, -, -, -⟩ := c.conc
  have hSY : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (Yp : Set G) :=
    inf_le_left.trans (Sgp153_le_normalizer_Yp hh)
  have hSn : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (YL153 Yp L : Set G) :=
    (F7.le_normalizer_inf hSY (inf_le_right.trans Subgroup.le_normalizer)).trans
      (normalizer_le_normalizer_oTwoUpper _)
  have hYLle : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
  have hYsolv : Group.IsSolvable ↥Yp := isSolvable_Yp hF
  have hYLsolv : Group.IsSolvable ↥(YL153 Yp L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (hYLle.trans inf_le_left)) (Subgroup.inclusion_injective _)
  have hSLsolv : Group.IsSolvable ↥(Sgp153 T V₁ ⊓ L) := by
    have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
      isSylowTwoOf_inf_of_isSubnormal
        (subnormal_of_mem_cComp (mem_cComp_of_mem_cComp_thompsonJ hLc)) hF.sylow
    exact F1.isSolvable_of_isPGroup_two hSL.2.1
  refine ⟨YL153 Yp L ⊔ (Sgp153 T V₁ ⊓ L), le_sup_right,
    sup_le (hYLle.trans inf_le_right) inf_le_right,
    F1.isSolvable_sup_of_le_normalizer hYLsolv hSLsolv hSn, ?_⟩
  obtain ⟨x, hxY, hxo, hx1⟩ : ∃ x ∈ Yp ⊓ L, Odd (orderOf x) ∧ x ≠ 1 := by
    by_contra hno
    push Not at hno
    apply c.c16.YL_ne
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, ho⟩
    exact Subgroup.mem_bot.mpr (hno x hx ho)
  obtain ⟨k, hk⟩ := exists_orderOf_eq_three_pow hF hxY.1 hxo
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have h3 : 3 ∣ orderOf x := by
    rw [hk]
    exact dvd_pow_self 3 hk1
  have hxYL : x ∈ YL153 Yp L := mem_oTwoUpper_of_odd hxY hxo
  have hz : orderOf (x ^ (orderOf x / 3)) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' h3
  have hzX : x ^ (orderOf x / 3) ∈ YL153 Yp L ⊔ (Sgp153 T V₁ ⊓ L) :=
    (le_sup_left : YL153 Yp L ≤ _) (Subgroup.pow_mem _ hxYL _)
  have := Subgroup.orderOf_dvd_natCard _ hzX
  rwa [hz] at this

omit [Finite G] in
theorem sl2_two_of_altBlockTypeWith_five {L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin 5)} (h : IsAltBlockTypeWith L 5 α) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Even n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨hs, hk, -⟩ := h
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_surjective α hs hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ := nonempty_SL_two_four_equiv_alt_five (K := GaloisField 2 2) hcard
  refine ⟨2, GaloisField 2 2, inferInstance, inferInstance, ⟨1, rfl⟩, ?_, ⟨e.trans e'.symm⟩⟩
  rw [← Nat.card_eq_fintype_card, hcard]
  norm_num

end Helpers


section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input15317_of_named_inputs (hcover : AsA36NoOddCover)
    (kR : Input21Rank) (kL : ThreeRankBlocks) (kB : SolvOvergroupsThreePrime)
    (kT : ThetaEqComponent) : Input15317 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  classical
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, -, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLI) hF.sylow
  have hsqI : SQTKGroup ↥I := (lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts).sqtk
  have hY : Yp ≤ thetaOf I :=
    calc Yp = thetaOf (M ⊓ I) := hF.theta
      _ ≤ thetaOf I := Subgroup.closure_mono (fun x hx => ⟨hx.1.2, hx.2⟩)
  have mk1 : CFSG.Open.pRank 3 L = 1 →
      ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Even n ∧ Fintype.card F = 2 ^ n ∧
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        IsLnTwoQuot L 3) → Concl15317 T V₁ Yp I L := fun hr h => Or.inl ⟨hr, h⟩
  have mk2 : CFSG.Open.pRank 3 L = 2 → IsRankTwoListType L → Concl15317 T V₁ Yp I L :=
    fun hr hty => Or.inr (Or.inl ⟨hr, hY, kT G I L hsqI hLI hLq hr hty⟩)
  have r6 : IsAltBlockType L 6 → Concl15317 T V₁ Yp I L := fun h =>
    mk2 (kR G L (Or.inl h)) (Or.inl h)
  have r7 : IsAltBlockType L 7 → Concl15317 T V₁ Yp I L := fun h =>
    mk2 (kR G L (Or.inr (Or.inr (Or.inr (Or.inl h))))) (Or.inr (Or.inl h))
  have rHat : IsHatA6Block L → Concl15317 T V₁ Yp I L := fun h =>
    mk2 (kR G L (Or.inr (Or.inr (Or.inl h)))) (Or.inr (Or.inr (Or.inl h)))
  have rExc : IsExcA7Block L → Concl15317 T V₁ Yp I L := fun h =>
    mk2 (kR G L (Or.inr (Or.inr (Or.inr (Or.inr h))))) (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have rG2 : IsG2Block L → Concl15317 T V₁ Yp I L := fun h =>
    mk2 (kR G L (Or.inr (Or.inl h))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have rSp4 : IsSp4Quot L → Concl15317 T V₁ Yp I L := fun h =>
    mk2 ((kL G L).2.2 (Or.inl h)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  have rL4 : IsLnTwoQuot L 4 → Concl15317 T V₁ Yp I L := fun h =>
    mk2 ((kL G L).2.2 (Or.inr (Or.inl h)))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have rL5 : IsLnTwoQuot L 5 → Concl15317 T V₁ Yp I L := fun h =>
    mk2 ((kL G L).2.2 (Or.inr (Or.inr h)))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  have noOdd : ∀ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Odd n → 3 ≤ n →
      Fintype.card F = 2 ^ n →
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∨
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) → False := by
    intro n F hF hFin hodd hn3 hcard hq
    obtain ⟨X, hSX, hXL, hXs, hX3⟩ := exists_solvable_overgroup_three c
    exact kB G L (Sgp153 T V₁ ⊓ L) X ⟨n, F, hF, hFin, hodd, hn3, hcard, hq⟩ hSL hSX hXL hXs hX3
  obtain ⟨h1c, -, h3⟩ := c.c16.desc
  rcases h3 with ⟨hchi, ⟨hi, -, -⟩ | ⟨hA5, -, -, -⟩ | ⟨hA7, -, -⟩ | ⟨hA7', -, -⟩⟩ |
      ⟨⟨n, α, h5, h8, hshort, hα, -⟩, -⟩ | ⟨hHat, -, -⟩ | ⟨hExc, -⟩ | ⟨hA6 | hSp4, -⟩ |
      ⟨hG2, -, -⟩ | ⟨⟨n, F, hF', hFin, hn1, hcard, ⟨e⟩⟩, -, -⟩ | ⟨hh | hh, -, -⟩
  ·
    obtain ⟨n, hn1, F, hF', hFin, hcard, α, hαs, hαk, -⟩ := hi
    obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_surjective α hαs hαk
    have hrk := (kL G L).1 ⟨n, F, hF', hFin, hcard, ⟨e⟩⟩
    have hev : Even n := by
      by_contra hno
      have hodd : Odd n := Nat.not_even_iff_odd.mp hno
      obtain ⟨k, hk⟩ := hodd
      exact noOdd n F hF' hFin ⟨k, hk⟩ (by omega) hcard (Or.inl ⟨e⟩)
    exact mk1 hrk (Or.inl ⟨n, F, hF', hFin, hev, hcard, ⟨e⟩⟩)
  ·
    obtain ⟨α, hα⟩ := (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 5)).mp hA5
    obtain ⟨n, F, hF', hFin, hev, hcard, he⟩ := sl2_two_of_altBlockTypeWith_five hα
    exact mk1 ((kL G L).1 ⟨n, F, hF', hFin, hcard, he⟩) (Or.inl ⟨n, F, hF', hFin, hev, hcard, he⟩)
  ·
    obtain ⟨⟨hshort, -, -⟩, -⟩ := hchi
    exact r7 ⟨hshort, (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).mp hA7⟩
  ·
    obtain ⟨⟨hshort, -, -⟩, -⟩ := hchi
    exact r7 ⟨hshort, (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).mp hA7'⟩
  ·
    interval_cases n
    · obtain ⟨n, F, hF', hFin, hev, hcard, he⟩ := sl2_two_of_altBlockTypeWith_five hα
      exact mk1 ((kL G L).1 ⟨n, F, hF', hFin, hcard, he⟩)
        (Or.inl ⟨n, F, hF', hFin, hev, hcard, he⟩)
    · exact r6 ⟨hshort, α, hα⟩
    · exact r7 ⟨hshort, α, hα⟩
    · exact rL4 (isLnTwoQuot_four_of_altBlockTypeWith_eight hα)
  · exact rHat hHat
  · exact rExc hExc
  · exact r6 hA6
  · exact rSp4 (isSp4Quot_of_isSp4Block hSp4)
  · exact rG2 hG2
  ·
    have hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) :=
      Or.inl ⟨n, F, hF', Finite.of_fintype F, by rw [Nat.card_eq_fintype_card]; exact hcard, ⟨e⟩⟩
    obtain ⟨e'⟩ := quot_equiv_autOn_of_ctx hcover c hH
    have hqe : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :=
      ⟨e'.trans e⟩
    rcases Nat.even_or_odd n with hev | hod
    · exact Or.inr (Or.inr ⟨((kL G L).2.1 n F hF' hFin hcard hqe).2 hev, n, F, hF', hFin, hev, hcard,
        ⟨e⟩⟩)
    · have hrk := ((kL G L).2.1 n F hF' hFin hcard hqe).1 hod
      by_cases hn3 : 3 ≤ n
      · exact (noOdd n F hF' hFin hod hn3 hcard (Or.inr hqe)).elim
      · have hn1' : n = 1 := by
          obtain ⟨k, hk⟩ := hod
          omega
        subst hn1'
        obtain ⟨e''⟩ := nonempty_statedSL_equiv_zmod_two (F := F) (by simpa using hcard) 3
        exact mk1 hrk (Or.inr ⟨(e'.trans e).trans e''⟩)
  ·
    have hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) :=
      Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, hh⟩)
    obtain ⟨e'⟩ := quot_equiv_autOn_of_ctx hcover c hH
    obtain ⟨e⟩ := hh
    exact rL4 ⟨e'.trans e⟩
  ·
    have hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) :=
      Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, hh⟩)
    obtain ⟨e'⟩ := quot_equiv_autOn_of_ctx hcover c hH
    obtain ⟨e⟩ := hh
    exact rL5 ⟨e'.trans e⟩

end Main

end S153F

end CFSG.Quasithin
