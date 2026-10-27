module

public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G]

@[expose] def InducesInnerModO2153 (Yp L : Subgroup G) : Prop :=
  ∀ y ∈ Yp, ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ pCoreOf 2 L

end Vocabulary

@[expose] def Input15337OneList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) → CFSG.Open.pRank 3 L = 1 →
      ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
        (∃ n : ℕ, Even n ∧ IsPSU 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
        IsPSL 3 2 1 (↥L ⧸ Subgroup.center ↥L)) ∧ InducesInnerModO2153 Yp L

@[expose] def Input15312Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → CFSG.Open.pRank 3 L = 1 → InducesInnerModO2153 Yp L →
      Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) ∧
        padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ L))) = 1 ∧
        padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))) = 1 ∧
        IsElemAbelianOfRank 3 2 (OTwoQuot Yp)

@[expose] def Input15337RankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) → CFSG.Open.pRank 3 L = 2 →
      Yp ≤ L ∨
        (((∃ n : ℕ, Even n ∧ IsPSL 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
            IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L)) ∧
          oTwoUpper (Yp ⊓ L) ≠ ⊥ ∧
          ∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
            Yp = oTwoUpper (Yp ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Yp)

namespace S153I

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

theorem concl15337_one_of_ne (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h122 : Lemma122A)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hne : L ≠ conjClosure L (Sgp153 T V₁)) :
    Yp ≤ conjClosure L (Sgp153 T V₁) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hLI : L ∈ cComp I := c.c33.mem
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  obtain ⟨s, hs, z, hz, hsz⟩ : ∃ s ∈ Sgp153 T V₁, ∃ z ∈ L, s * z * s⁻¹ ∉ L := by
    by_contra hno
    push Not at hno
    exact hne (le_antisymm (le_conjClosure _ _) (conjClosure_le hno))
  set L'' := L.map (MulAut.conj s).toMonoidHom with hL''
  have hL''mem : L'' ∈ conjSubgroupsBy I L := ⟨s, hSI hs, rfl⟩
  have hLmem : L ∈ conjSubgroupsBy I L := ⟨1, I.one_mem, by ext x; simp⟩
  have hLne : L ≠ L'' := by
    intro h
    apply hsz
    have : s * z * s⁻¹ ∈ L'' := by
      rw [hL'', A38.mem_map_conj]
      have e : s⁻¹ * (s * z * s⁻¹) * s = z := by group
      rw [e]
      exact hz
    rwa [← h] at this
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 c.inH.1.2 hLI with hn | ⟨hcard, -⟩
  · exact absurd (((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn (hSI hs) z).mp hz) hsz
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp hcard
  have hmem : ∀ K ∈ conjSubgroupsBy I L, K = L ∨ K = L'' := by
    intro K hK
    have hK' := hK
    have h1 := hLmem
    have h2 := hL''mem
    rw [hset] at hK' h1 h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK' h1 h2
    rcases hK' with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first | exact Or.inl h1.symm | exact Or.inr h2.symm | (exfalso; exact hLne (h1.trans h2.symm))
  have hcc : conjClosure L I ≤ conjClosure L (Sgp153 T V₁) := by
    refine conjClosure_le fun g hg l hl => ?_
    have hK : L.map (MulAut.conj g).toMonoidHom ∈ conjSubgroupsBy I L := ⟨g, hg, rfl⟩
    have hgl : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
    rcases hmem _ hK with h | h
    · rw [h] at hgl
      exact le_conjClosure _ _ hgl
    · rw [h] at hgl
      obtain ⟨l', hl', hl'e⟩ := hgl
      have : (MulAut.conj s) l' = g * l * g⁻¹ := hl'e
      rw [← this]
      simpa [MulAut.conj_apply] using mem_conjClosure hs hl'
  have hdvd : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have hr := pRank_modO2_eq L Nat.prime_three (by norm_num)
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
      (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
    have h3 : 3 ∣ Nat.card E := by
      rw [hE, hr]
      exact dvd_pow_self 3 (by have := c.c34.rank; omega)
    exact h3.trans (Subgroup.card_subgroup_dvd_card E)
  have h122' := h122 G hq.simple hq.qtke hq.nonabelian I L c.inH.1.2 hLI 3 Nat.prime_three
    (by norm_num) hcard hdvd
  have hYle : Yp ≤ Subgroup.closure {x : G | x ∈ I ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    calc Yp = oTwoUpper Yp := hh.oTwoUpper_eq.symm
      _ ≤ _ := by
        rw [oTwoUpper, Subgroup.closure_le]
        rintro x ⟨hx, hodd⟩
        exact Subgroup.subset_closure ⟨hYI hx, exists_orderOf_eq_three_pow c.facts11 hx hodd⟩
  exact hYle.trans (h122'.le.trans hcc)

theorem input15337_of_named_inputs (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h122 : Lemma122A)
    (kList : Input15337OneList) (k12 : Input15312Two) (kTwo : Input15337RankTwo) :
    Input15337 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  by_cases hL0 : L = conjClosure L (Sgp153 T V₁)
  · have hq := c.hyp.hyp.qtfe
    have h1 : 1 ≤ CFSG.Open.pRank 3 L := c.c34.rank
    have h2 : CFSG.Open.pRank 3 L ≤ 2 :=
      (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) (le_of_mem_cComp c.c33.mem)).trans
        (pRank_le_two_of_pCoreOf_ne_bot hq.qtke c.inH.1.2 Nat.prime_three (by norm_num))
    rcases (by omega : CFSG.Open.pRank 3 L = 1 ∨ CFSG.Open.pRank 3 L = 2) with hr | hr
    · obtain ⟨hlist, hinner⟩ := kList G T Mc M V₁ V₂ Yp I L t c hL0 hr
      obtain ⟨hdec, h3a, h3b, hE⟩ := k12 G T Mc M V₁ V₂ Yp I L t c hr hinner
      exact Or.inr (Or.inl ⟨hL0, hlist, hdec, h3a, h3b, hE⟩)
    · rcases kTwo G T Mc M V₁ V₂ Yp I L t c hL0 hr with hY | h3
      · exact Or.inl (hY.trans (le_conjClosure _ _))
      · exact Or.inr (Or.inr ⟨hL0, h3⟩)
  · exact Or.inl (concl15337_one_of_ne h37 h38 h122 c hL0)

end S153I

end CFSG.Quasithin
