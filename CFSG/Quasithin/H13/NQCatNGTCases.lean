module

public import CFSG.Quasithin.H13.NQCatNGTRed
public import CFSG.Quasithin.H13.NQCatNGTOrd
public import CFSG.Quasithin.H13.NQCatNGTQuasi
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.FFC4Ext
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

local notation "StSL" => CFSG.Assembly.LowTwoRank.StatedSL

local notation "StSp" => CFSG.Assembly.LowTwoRank.StatedSp

section Orders

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) :
    1 ≤ a := by
  have h := Finite.one_lt_card (α := K)
  rw [hK] at h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · norm_num at h
  · exact ha

theorem card_sl4_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StSL 4 K) = 20160 := by
  rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK]
  decide

theorem card_sl5_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StSL 5 K) = 9999360 := by
  rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK]
  decide

theorem card_sl3_two : Nat.card ↥(StSL 3 (ZMod 2)) = 168 := by
  rw [card_sl3_form (a := 1) (by rw [Nat.card_zmod]; norm_num)]
  norm_num [sl3Form]

theorem ge_of_card {m n : ℕ} (hn : 2 ≤ n) (h : m = sl3Form n ∨ m = sp4Form n) : 60480 ≤ m := by
  rcases h with rfl | rfl
  · exact sl3Form_ge hn
  · exact (by norm_num : 60480 ≤ 979200).trans (sp4Form_ge hn)

theorem two_le_of_sl3 {m n a : ℕ} (hn : 2 ≤ n) (h : m = sl3Form n ∨ m = sp4Form n)
    (ha : m = sl3Form a) : 2 ≤ a := by
  have := ge_of_card hn h
  by_contra h'
  push Not at h'
  interval_cases a <;> norm_num [sl3Form] at ha <;> omega

theorem two_le_of_sp4 {m n a : ℕ} (hn : 2 ≤ n) (h : m = sl3Form n ∨ m = sp4Form n)
    (ha : m = sp4Form a) : 2 ≤ a := by
  have := ge_of_card hn h
  by_contra h'
  push Not at h'
  interval_cases a <;> norm_num [sp4Form] at ha <;> omega

end Orders

section Basic

variable {V : Type} [CommGroup V]

theorem finite_mulAut (V : Type) [CommGroup V] [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun (h : MulAut V) (v : V) => h v) fun _ _ hab =>
    MulEquiv.ext (congrFun hab)

theorem card_eq_of_realizesVia {L : Subgroup (MulAut V)} {U Z : Subgroup V} {D : FFModel}
    (hD : D.Faithful) {π : D.Gam →* ↥L} (h : D.RealizesVia L U Z π) :
    Nat.card L = Nat.card D.Gam :=
  (Nat.card_congr (Equiv.ofBijective π ⟨FFC.injective_of_faithful_sec hD h, h.1⟩)).symm

theorem isQuasisimple_of_equiv_stSL3 {Y : Type*} [Group Y] {K : Type} [Field K] [Finite K]
    (e : Y ≃* ↥(StSL 3 K)) : CFSG.IsQuasisimple Y :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).trans e.symm)
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 K
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))

theorem isQuasisimple_of_equiv_stSL2 {Y : Type*} [Group Y] {K : Type} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) (e : Y ≃* ↥(StSL 2 K)) : CFSG.IsQuasisimple Y :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).trans e.symm)
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl
      (Or.inr (by omega)) (Or.inr (by omega)))

open scoped Pointwise in
theorem card_sup_le_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer (B : Set G)
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm)
  have h := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  calc Nat.card ↥(A ⊔ B) = Nat.card ↑((A : Set G) * (B : Set G)) := by rw [← h]; rfl
    _ ≤ Nat.card A * Nat.card B := Set.natCard_mul_le

theorem iSup_fin_two_eq (I : Fin 2 → Subgroup V) : (⨆ i, I i) = I 0 ⊔ I 1 := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem inf_eq_of_directSum {I : Fin 2 → Subgroup V} {C : Subgroup V} (hC : ∀ i, C ≤ I i)
    (hind : ∀ i, I i ⊓ (C ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = C) : I 0 ⊓ I 1 = C := by
  refine le_antisymm ?_ (le_inf (hC 0) (hC 1))
  calc I 0 ⊓ I 1 ≤ I 0 ⊓ (C ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) :=
        inf_le_inf_left _ (le_sup_of_le_right
          (le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide) le_rfl))
    _ = C := hind 0

end Basic

section Excl

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}

theorem excl_l45 (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hcard : Nat.card L = Nat.card ↥(StSL d K)) : False := by
  have h3 := ge_of_card hn hL
  rcases hd with rfl | rfl
  · rw [card_sl4_two hK] at hcard
    omega
  · rw [card_sl5_two hK] at hcard
    rcases hL with h | h
    · exact sl3Form_ne_l5 n (h.symm.trans hcard)
    · exact sp4Form_ne_l5 n (h.symm.trans hcard)

theorem excl_sl2 (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {a : ℕ}
    (h : BinaryNaturalSL L U Z 2 a) : False := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hcard : Nat.card L = Nat.card ↥(StSL 2 K) :=
    card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
  rw [card_sl2_form hK] at hcard
  have ha := one_le_of_card_field hK
  rcases hL with h | h
  · exact sl3Form_ne_sl2Form ha (by omega) (h.symm.trans hcard)
  · exact sp4Form_ne_sl2Form ha (by omega) (h.symm.trans hcard)

theorem excl_g2 (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {a : ℕ}
    (h : G2Natural L U Z a) : False := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have ha := one_le_of_card_field hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      ha hK
  have hcard : Nat.card L = Nat.card ↥(CFSG.Open.quasithinG2 K) :=
    card_eq_of_realizesVia (FFC.zornQ_faithful _ le_rfl) hπ
  rw [card_g2_form hK] at hcard
  rcases hL with h | h
  · exact sl3Form_ne_g2Form ha (by omega) (h.symm.trans hcard)
  · exact sp4Form_ne_g2Form ha (by omega) (h.symm.trans hcard)

theorem excl_g2der (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n)
    (h : G2NaturalDerived L U Z 1) : False := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hK
  have hG := card_g2_form hK
  have : Finite ↥(CFSG.Open.quasithinG2 K) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num [g2Form])
  have : Finite ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective (Subgroup.commutator_le_self _))
  have h1 : Nat.card L ≤ Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    Nat.card_le_card_of_surjective (α := ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆)
      π hπ.1
  have h2 := Subgroup.card_le_of_le (Subgroup.commutator_le_self (CFSG.Open.quasithinG2 K))
  rw [hG] at h2
  have h3 := ge_of_card hn hL
  norm_num [g2Form] at h2
  omega

theorem excl_alt (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {m : ℕ}
    (hm : 2 ≤ m) (hm8 : m ≤ 8) (h : AlternatingNatural L U Z m) : False := by
  obtain ⟨π, hπ⟩ := h
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  have h1 : Nat.card L ≤ Nat.card ↥(alternatingGroup (Fin m)) :=
    Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin m))) π hπ.1
  rw [nat_card_alternatingGroup, Nat.card_fin] at h1
  have h2 : m.factorial / 2 ≤ 20160 := by
    interval_cases m <;> decide
  have h3 := ge_of_card hn hL
  omega

theorem excl_sym5 (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n)
    (h : SymmetricNatural L U Z 5) : False := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card L ≤ Nat.card (Equiv.Perm (Fin 5)) :=
    Nat.card_le_card_of_surjective (α := Equiv.Perm (Fin 5)) π hπ.1
  rw [Nat.card_perm, Nat.card_fin] at h1
  have h3 := ge_of_card hn hL
  have : Nat.factorial 5 = 120 := by decide
  omega

theorem excl_a7four (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n)
    (h : A7Four L U Z) : False := by
  obtain ⟨α, π, hπ⟩ := h
  have h1 : Nat.card L ≤ Nat.card ↥(alternatingGroup (Fin 7)) :=
    Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 7))) π hπ.1
  rw [nat_card_alternatingGroup, Nat.card_fin] at h1
  have h3 := ge_of_card hn hL
  have : Nat.factorial 7 / 2 = 2520 := by decide
  omega

theorem excl_triple (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n)
    (h : TripleA6Six L U Z) : False := by
  obtain ⟨K, _, _, Γ₀, -, -, ⟨-, hc, ⟨e⟩⟩, -, π, hπ⟩ := h
  have h0 : Nat.card ↥Γ₀ = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Γ₀),
      Nat.card_congr e.toEquiv, hc, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have : Finite ↥Γ₀ := Nat.finite_of_card_ne_zero (by rw [h0]; norm_num)
  have h1 : Nat.card L ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective (α := ↥Γ₀) π hπ.1
  have h3 := ge_of_card hn hL
  omega

theorem excl_binSL (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {d : ℕ}
    (hd : d = 4 ∨ d = 5) (h : BinaryNaturalSL L U Z d 1) : False := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  exact excl_l45 hn hL (by rw [hK, pow_one]) hd
    (card_eq_of_realizesVia (FFModel.nat_faithful _) hπ)

theorem excl_ext (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {d : ℕ}
    (hd : d = 4 ∨ d = 5) (h : SLExteriorTwo L U Z d) : False := by
  obtain ⟨π, hπ⟩ := h
  exact excl_l45 hn hL (Nat.card_zmod 2) hd
    (card_eq_of_realizesVia (FFC.extSq_faithful (by rcases hd with rfl | rfl <;> norm_num)) hπ)

theorem excl_le_sl2 [Finite V] {X G : Subgroup (MulAut V)} (hXG : X ≤ G)
    (hXn : ∀ y ∈ G, ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hXq : CFSG.IsQuasisimple ↥X) (hn : 2 ≤ n)
    (hcard : Nat.card X = sl3Form n ∨ Nat.card X = sp4Form n) {K : Type} [Field K] [Finite K]
    {a : ℕ} (hK : Nat.card K = 2 ^ a) (e : ↥G ≃* ↥(StSL 2 K)) : False := by
  have hG : Nat.card G = sl2Form a := (Nat.card_congr e.toEquiv).trans (card_sl2_form hK)
  have ha := one_le_of_card_field hK
  have hge := ge_of_card hn hcard
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have : Finite (MulAut V) := finite_mulAut V
    have h1 := Subgroup.card_le_of_le hXG
    obtain rfl : a = 1 := by omega
    rw [hG] at h1
    norm_num [sl2Form] at h1
    omega
  · have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
    have hXG' := eq_of_normal_quasisimple hXG hXn hXq (isQuasisimple_of_equiv_stSL2 hK4 e)
    rw [hXG', hG] at hcard
    rcases hcard with h | h
    · exact sl3Form_ne_sl2Form ha (by omega) h.symm
    · exact sp4Form_ne_sl2Form ha (by omega) h.symm

end Excl

section Data

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
  {n : ℕ}

theorem data_sl3 (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {a : ℕ}
    (h : BinaryNaturalSL L U Z 3 a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
      ∃ π : ↥(StSL 3 K) →* ↥L, NatTransfer L U Z (StSL 3 K) π := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hcard : Nat.card L = Nat.card ↥(StSL 3 K) :=
    card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
  rw [card_sl3_form hK] at hcard
  exact ⟨K, inferInstance, inferInstance, a, hK, two_le_of_sl3 hn hL hcard, π,
    natTransfer_of_realizes hπ⟩

theorem data_sp4 (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {a : ℕ}
    (h : BinaryNaturalSp4 L U Z a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
      ∃ π : ↥(StSp 2 K) →* ↥L, NatTransfer L U Z (StSp 2 K) π := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hcard : Nat.card L = Nat.card ↥(StSp 2 K) :=
    card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
  rw [card_sp4_form hK] at hcard
  exact ⟨K, inferInstance, inferInstance, a, hK, two_le_of_sp4 hn hL hcard, π,
    natTransfer_of_realizes hπ⟩

theorem data_sum (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n)
    {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a)
    {I : Fin 2 → Subgroup V} {π : ↥(StSL 3 K) →* ↥L}
    (hI : ∀ i, (FFModel.nat (StSL 3 K)).RealizesVia L (I i) Z π) (hU : I 0 ⊔ I 1 = U)
    (hind : I 0 ⊓ I 1 = Z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
      ∃ π : ↥(StSL 3 K) →* ↥L, NatTransfer L U Z (StSL 3 K) π := by
  have hcard : Nat.card L = Nat.card ↥(StSL 3 K) :=
    card_eq_of_realizesVia (FFModel.nat_faithful _) (hI 0)
  rw [card_sl3_form hK] at hcard
  exact ⟨K, inferInstance, inferInstance, a, hK, two_le_of_sl3 hn hL hcard, π,
    natTransfer_of_sum hI hU hind⟩

theorem sec_of_pair (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n)
    (h : B42ModulePair L U Z) :
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
        ∃ π : ↥(StSL 3 K) →* ↥L, NatTransfer L U Z (StSL 3 K) π) ∨
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
        ∃ π : ↥(StSp 2 K) →* ↥L, NatTransfer L U Z (StSp 2 K) π := by
  rcases h with ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact (excl_sl2 hn hL h).elim
  · exact Or.inl (data_sl3 hn hL h)
  · exact Or.inr (data_sp4 hn hL h)
  · exact (excl_g2 hn hL h).elim
  · exact (excl_g2der hn hL h).elim
  · exact (excl_alt hn hL (by norm_num) (by norm_num) h).elim
  · exact (excl_alt hn hL (by norm_num) (by norm_num) h).elim
  · exact (excl_alt hn hL (by norm_num) (by norm_num) h).elim
  · exact (excl_a7four hn hL h).elim
  · exact (excl_triple hn hL h).elim
  · exact (excl_binSL hn hL (Or.inl rfl) h).elim
  · exact (excl_binSL hn hL (Or.inr rfl) h).elim
  · exact (excl_ext hn hL (Or.inl rfl) h).elim
  · exact (excl_ext hn hL (Or.inr rfl) h).elim

end Data

section Cases

variable {V : Type} [CommGroup V] [Finite V] {J X : Subgroup (MulAut V)} {n : ℕ}

theorem sec_case1 (h : B56Case1 J) (hXJ : X ≤ J) (hXn : ∀ y ∈ J, ∀ x ∈ X, y * x * y⁻¹ ∈ X)
    (hXq : CFSG.IsQuasisimple ↥X) (hn : 2 ≤ n)
    (hcard : Nat.card X = sl3Form n ∨ Nat.card X = sp4Form n) {g : MulAut V}
    (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    ∃ U Z : Subgroup V, U.map g.toMonoidHom = U ∧ Z.map g.toMonoidHom = Z ∧
      ((∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
          ∃ π : ↥(StSL 3 K) →* ↥X, NatTransfer X U Z (StSL 3 K) π) ∨
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
          ∃ π : ↥(StSp 2 K) →* ↥X, NatTransfer X U Z (StSp 2 K) π) := by
  obtain ⟨hq, hB, -⟩ := h
  have hXL : X = quasithinGenFitting J :=
    eq_of_normal_quasisimple (le_quasithinGenFitting hXJ hXn hXq)
      (fun l hl x hx => hXn l (quasithinGenFitting_le J hl) x hx) hXq hq
  rw [← hXL] at hB
  obtain ⟨⟨-, hB⟩, -⟩ := hB
  have hgU := map_commV_eq hgX
  rcases hB with ⟨-, hpair, -⟩ | ⟨-, a, K, _, _, hK, I, π, hind, hsup, hI, -, -⟩ |
      ⟨d, -, hd, π, U₁, U₂, -, h₁, -⟩ | ⟨-, d, hd, k, hk, -, I, π, -, -, -, hI⟩
  · refine ⟨commV X, fixV X ⊓ commV X, hgU, ?_, sec_of_pair hn hcard hpair⟩
    rw [Subgroup.map_inf_eq _ _ _ g.injective, map_fixV_eq hgX, hgU]
  · refine ⟨commV X, ⊥, hgU, Subgroup.map_bot _, Or.inl ?_⟩
    have hd : Disjoint (I 0) (I 1) := hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)
    exact data_sum hn hcard hK hI ((iSup_fin_two_eq I).symm.trans hsup) (disjoint_iff.1 hd)
  · exact (excl_l45 hn hcard (Nat.card_zmod 2) hd
      (card_eq_of_realizesVia (FFModel.nat_faithful _) h₁)).elim
  · exact (excl_l45 hn hcard (Nat.card_zmod 2) hd
      (card_eq_of_realizesVia (FFModel.nat_faithful _) (hI ⟨0, by omega⟩))).elim

theorem sec_case3 {G : Subgroup (MulAut V)} {W : Subgroup V} (hXG : X ≤ G) (hGJ : G ≤ J)
    (hXn : ∀ y ∈ J, ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hXq : CFSG.IsQuasisimple ↥X) (hn : 2 ≤ n)
    (hcard : Nat.card X = sl3Form n ∨ Nat.card X = sp4Form n) (hF : B56FactorList ↥G)
    (hP : B56Piece G W (fixV J)) {g : MulAut V}
    (hgJ : g ∈ Subgroup.normalizer (J : Set (MulAut V)))
    (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    ∃ U Z : Subgroup V, U.map g.toMonoidHom = U ∧ Z.map g.toMonoidHom = Z ∧
      ((∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
          ∃ π : ↥(StSL 3 K) →* ↥X, NatTransfer X U Z (StSL 3 K) π) ∨
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
          ∃ π : ↥(StSp 2 K) →* ↥X, NatTransfer X U Z (StSp 2 K) π) := by
  have hge := ge_of_card hn hcard
  have hXn' : ∀ y ∈ G, ∀ x ∈ X, y * x * y⁻¹ ∈ X := fun y hy => hXn y (hGJ hy)
  have hXG' : X = G := by
    rcases hF with ⟨a, K, _, _, -, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨a, K, _, _, -, -, -, ⟨e⟩⟩
    · exact (excl_le_sl2 hXG hXn' hXq hn hcard hK e).elim
    · have : Finite (MulAut V) := finite_mulAut V
      have h1 := Subgroup.card_le_of_le hXG
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at h1
      have : Nat.factorial 5 = 120 := by decide
      omega
    · exact eq_of_normal_quasisimple hXG hXn' hXq (isQuasisimple_of_equiv_stSL3 e)
  subst hXG'
  have hgC := map_fixV_eq hgJ
  have hgW : (commV X ⊔ fixV J).map g.toMonoidHom = commV X ⊔ fixV J := by
    rw [Subgroup.map_sup, map_commV_eq hgX, hgC]
  rcases hP with ⟨hW, ⟨a, h⟩ | h | ⟨a, h⟩⟩ | ⟨hW, m, K, _, _, hK, I, π, hC, hind, hsup, hI⟩ |
      ⟨⟨e⟩, -⟩
  · exact (excl_sl2 hn hcard h).elim
  · exact (excl_sym5 hn hcard h).elim
  · subst hW
    exact ⟨_, _, hgW, hgC, Or.inl (data_sl3 hn hcard h)⟩
  · subst hW
    rw [iSup_fin_two_eq I, ← sup_assoc, sup_eq_right.2 (hC 0)] at hsup
    exact ⟨_, _, hgW, hgC, Or.inl (data_sum hn hcard hK hI hsup (inf_eq_of_directSum hC hind))⟩
  · have := (Nat.card_congr e.toEquiv).trans card_sl3_two
    omega

end Cases

theorem sections_holds : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ J X : Subgroup (MulAut V), B53Hyp J →
    (B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) → X ≤ J →
    (∀ y ∈ J, ∀ x ∈ X, y * x * y⁻¹ ∈ X) → CFSG.IsQuasisimple ↥X →
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    (Nonempty (↥X ≃* ↥(StSL 3 F)) ∨ Nonempty (↥X ≃* ↥(StSp 2 F))) →
    ∀ g : MulAut V, g ∈ Subgroup.normalizer (J : Set (MulAut V)) →
      g ∈ Subgroup.normalizer (X : Set (MulAut V)) →
      ∃ U Z : Subgroup V, U.map g.toMonoidHom = U ∧ Z.map g.toMonoidHom = Z ∧
        ((∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
            ∃ π : ↥(StSL 3 K) →* ↥X, NatTransfer X U Z (StSL 3 K) π) ∨
          ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
            ∃ π : ↥(StSp 2 K) →* ↥X, NatTransfer X U Z (StSp 2 K) π) := by
  intro V _ _ _ J X _ hcases hXJ hXn hXq F _ _ n hn hF hXiso g hgJ hgX
  have hcard : Nat.card X = sl3Form n ∨ Nat.card X = sp4Form n := by
    rcases hXiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ((Nat.card_congr e.toEquiv).trans (card_sl3_form hF))
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans (card_sp4_form hF))
  have hge := ge_of_card hn hcard
  have : Finite (MulAut V) := finite_mulAut V
  rcases hcases with h | ⟨⟨e⟩, -, -⟩ | ⟨G₁, G₂, hJ, -, hc, hF₁, hF₂, W₁, W₂, -, -, -, -, -, -, hP₁,
      hP₂⟩ | ⟨G₁, G₂, t, hJ, -, hc, ⟨e₁⟩, h₂, -, -, -, -, -, ht₁, ht₂, -, -⟩ |
      ⟨G₁, G₂, hJ, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  ·
    exact sec_case1 h hXJ hXn hXq hn hcard hgX
  ·
    have h1 := Subgroup.card_le_of_le hXJ
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at h1
    have : Nat.factorial 3 = 6 := by decide
    omega
  ·
    have hG₁J : G₁ ≤ J := hJ ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hJ ▸ le_sup_right
    rcases le_or_le_of_commute hJ hc hXJ hXn hXq with h | h
    · exact sec_case3 h hG₁J hXn hXq hn hcard hF₁ hP₁ hgJ hgX
    · exact sec_case3 h hG₂J hXn hXq hn hcard hF₂ hP₂ hgJ hgX
  ·
    have ht : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      Subgroup.inf_normalizer_le_normalizer_sup G₁ G₂ (Subgroup.mem_inf.2 ⟨ht₁, ht₂⟩)
    have hXN := le_of_sup_zpowers ht (hXJ.trans hJ.le) hXq
    have h₁ : Nat.card G₁ = 360 := by
      rw [Nat.card_congr e₁.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hN := card_sup_le_of_commute hc
    rw [h₁, h₂] at hN
    have := Subgroup.card_le_of_le hXN
    omega
  ·
    have hG₂J : G₂ ≤ J := hJ ▸ le_sup_right
    rcases le_or_le_of_commute hJ hc hXJ hXn hXq with h | h
    · have := Subgroup.card_le_of_le h
      rw [Nat.card_congr e₁.toEquiv, card_sl3_two] at this
      omega
    · rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨a, K, _, _, hK, π, hπ⟩
      · have := Subgroup.card_le_of_le h
        rw [Nat.card_congr e₂.toEquiv, card_sl3_two] at this
        omega
      · have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
        exact (excl_le_sl2 h (fun y hy => hXn y (hG₂J hy)) hXq hn hcard hK
          (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm).elim

theorem factNoGraphTwist_holds :
    H13.A5.FactNoGraphTwist :=
  factNoGraphTwist_of_sections sections_holds

end CFSG.Quasithin.H13.NQCat.NGT
