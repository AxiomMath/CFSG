module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Props
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Avg
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Factors

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace C421

theorem two_dvd_card_of_isQuasisimple {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : 2 ∣ Nat.card Q := by
  by_contra h
  have hodd : Odd (Nat.card Q) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  have : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard Q hodd
  have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem exists_sq_eq_one {Q : Type} [Group Q] [Finite Q] (h : 2 ∣ Nat.card Q) :
    ∃ x : Q, x ^ 2 = 1 ∧ x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
  refine ⟨x, by rw [← hx, pow_orderOf_eq_one], fun h1 => ?_⟩
  rw [h1, orderOf_one] at hx
  omega

theorem center_statedSL_two_eq_bot (K : Type) [Field K] [CharP K 2] :
    Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  set e := specialLinearGroupEquivStatedSL 2 K
  have hB : e.symm A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff] at hA ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hA (e g)
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hB
  rw [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hr0 : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
  have hr1 : r = 1 := by
    have h := pow_eq_zero_iff (two_ne_zero) |>.mp hr0
    have : r = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq]
  rw [hr1, map_one] at hrA
  have h1 : e.symm A = 1 := Subtype.ext hrA.symm
  rw [Subgroup.mem_bot, ← e.apply_symm_apply A, h1, map_one]

variable {G : Type} [Group G] [Finite G]

section Conj

variable {I V : Subgroup G} (hV : IsElemAbelian 2 V) (hIV : I ≤ Subgroup.normalizer (V : Set G))

@[expose] noncomputable def conjI : ↥I →* ↥(autI hV I) :=
  (convHom hV I hIV).codRestrict (autI hV I) fun k => convI_mem_autI hV k.2 (hIV k.2)

omit [Finite G] in
theorem conjI_apply (k : ↥I) :
    ((conjI hV hIV k : ↥(autI hV I)) : MulAut (IntMod V hV)) = convI hV ⟨k, hIV k.2⟩ := rfl

omit [Finite G] in
theorem conjI_surjective : Function.Surjective (conjI hV hIV) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

omit [Finite G] in
theorem conjI_eq_one_iff (k : ↥I) :
    conjI hV hIV k = 1 ↔ (k : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    exact (convI_eq_one_iff hV ⟨k, hIV k.2⟩).1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((convI_eq_one_iff hV ⟨k, hIV k.2⟩).2 h)

end Conj

section Psi

variable {I V : Subgroup G} (hV : IsElemAbelian 2 V) (hIV : I ≤ Subgroup.normalizer (V : Set G))
  (hC : I ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 I)

omit [Finite G] in
theorem mem_pCore_iff {k : ↥I} : k ∈ Open.pCore 2 ↥I ↔ (k : G) ∈ pCoreOf 2 I := by
  constructor
  · intro h
    exact ⟨k, h, rfl⟩
  · rintro ⟨k', hk', he⟩
    have : k' = k := Subtype.ext he
    rwa [← this]

include hC in
omit [Finite G] in
theorem conjI_eq_one_iff_mem (k : ↥I) : conjI hV hIV k = 1 ↔ k ∈ Open.pCore 2 ↥I := by
  rw [conjI_eq_one_iff, mem_pCore_iff, ← hC]
  exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩

include hC in
theorem ker_conjI_le : (conjI hV hIV).ker ≤ CFSG.pPrimeCore 3 ↥I := fun k hk =>
  F6.pCore_le_pPrimeCore ((conjI_eq_one_iff_mem hV hIV hC k).mp hk)

@[expose] noncomputable def psi : ↥(autI hV I) →* ↥I ⧸ CFSG.pPrimeCore 3 ↥I :=
  (QuotientGroup.map _ _ (MonoidHom.id ↥I) (ker_conjI_le hV hIV hC)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _ (conjI_surjective hV hIV)).symm.toMonoidHom

theorem psi_conjI (k : ↥I) :
    psi hV hIV hC (conjI hV hIV k) = (k : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _ (conjI_surjective hV hIV)).symm
      (conjI hV hIV k) = (k : ↥I ⧸ (conjI hV hIV).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.map _ _ (MonoidHom.id ↥I) (ker_conjI_le hV hIV hC)
    ((QuotientGroup.quotientKerEquivOfSurjective _ (conjI_surjective hV hIV)).symm
      (conjI hV hIV k)) = _
  rw [h]
  rfl

theorem psi_surjective : Function.Surjective (psi hV hIV hC) := by
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨conjI hV hIV k, psi_conjI hV hIV hC k⟩

theorem psi_eq_one_iff (k : ↥I) :
    psi hV hIV hC (conjI hV hIV k) = 1 ↔ k ∈ CFSG.pPrimeCore 3 ↥I := by
  rw [psi_conjI]
  exact QuotientGroup.eq_one_iff k

theorem psi_ne_one_of_cube {x : ↥(autI hV I)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    psi hV hIV hC x ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, rfl⟩ := conjI_surjective hV hIV x
  intro h
  have hk := (psi_eq_one_iff hV hIV hC k).mp h
  have h1 : orderOf (conjI hV hIV k) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf (conjI hV hIV k) ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥I) := by
    refine (orderOf_map_dvd (conjI hV hIV) k).trans ?_
    have := orderOf_dvd_natCard (⟨k, hk⟩ : ↥(CFSG.pPrimeCore 3 ↥I))
    rwa [Subgroup.orderOf_mk] at this
  have h3 := Nat.eq_one_of_dvd_coprimes (CFSG.pPrimeCore_coprime_card (p := 3)) h1 h2
  exact hx1 (orderOf_eq_one_iff.mp h3)

theorem psi_ne_one_of_sq {G₁ G₂ : Subgroup G} (htr : F6.IsGoldschmidtTripleIn I G₁ G₂)
    {x : ↥(autI hV I)} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : psi hV hIV hC x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := conjI_surjective hV hIV x
  intro h
  have hk := (psi_eq_one_iff hV hIV hC k).mp h
  set P := Open.pCore 2 ↥I with hPdef
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hk2 : k ^ 2 ∈ P := by
    rw [← conjI_eq_one_iff_mem hV hIV hC, map_pow, hx2]
  obtain ⟨m, hm⟩ := hP2 ⟨k ^ 2, hk2⟩
  have hkm : k ^ 2 ^ (m + 1) = 1 := by
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_succ, mul_comm, pow_mul]
    exact this
  have hZ2 : IsPGroup 2 ↥(Subgroup.zpowers k) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨m + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hkm,
      _root_.one_zpow]
  have hS2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers k) :=
    IsPGroup.to_sup_of_normal_left' hP2 hZ2
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hPn).ge)
  have hsyl := htr.isSylowTwoOf_pCore_pPrimeCore
  have heq := inf_eq_of_isSylowTwoOf_of_le hsyl hS2 le_sup_left
  have hkP : k ∈ P := by
    have h1 : k ∈ (P ⊔ Subgroup.zpowers k) ⊓ CFSG.pPrimeCore 3 ↥I :=
      ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers k), hk⟩
    rw [heq] at h1
    exact h1
  exact hx1 ((conjI_eq_one_iff_mem hV hIV hC k).mpr hkP)

theorem isComponent_map_psi {G₁ G₂ : Subgroup G} (htr : F6.IsGoldschmidtTripleIn I G₁ G₂)
    {K : Subgroup ↥(autI hV I)} (hK : CFSG.IsComponent K) :
    CFSG.IsComponent (K.map (psi hV hIV hC)) := by
  obtain ⟨x, hx2, hx1⟩ := exists_sq_eq_one (two_dvd_card_of_isQuasisimple hK.1)
  refine ⟨CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (φ := (psi hV hIV hC).subgroupMap K) hK.1 ((psi hV hIV hC).subgroupMap_surjective K)
    ⟨x, fun h => ?_⟩, hK.2.map (psi_surjective hV hIV hC)⟩
  have h1 : psi hV hIV hC (x : ↥(autI hV I)) = 1 := congrArg Subtype.val h
  refine psi_ne_one_of_sq hV hIV hC htr (x := (x : ↥(autI hV I))) ?_ ?_ h1
  · rw [← Subgroup.coe_pow, hx2, Subgroup.coe_one]
  · exact fun h0 => hx1 (Subtype.ext h0)

theorem psi_injective_of_ker {G₁ G₂ : Subgroup G} (htr : F6.IsGoldschmidtTripleIn I G₁ G₂)
    {K : Subgroup ↥(autI hV I)} (hK : CFSG.IsComponent K)
    (hker : ((psi hV hIV hC).subgroupMap K).ker = ⊥ ∨
      ((psi hV hIV hC).subgroupMap K).ker = ⊤) :
    Function.Injective ((psi hV hIV hC).subgroupMap K) := by
  rcases hker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨x, hx2, hx1⟩ := exists_sq_eq_one (two_dvd_card_of_isQuasisimple hK.1)
    have hx : x ∈ ((psi hV hIV hC).subgroupMap K).ker := h ▸ Subgroup.mem_top x
    have h1 : psi hV hIV hC (x : ↥(autI hV I)) = 1 := congrArg Subtype.val hx
    refine psi_ne_one_of_sq hV hIV hC htr (x := (x : ↥(autI hV I))) ?_ ?_ h1
    · rw [← Subgroup.coe_pow, hx2, Subgroup.coe_one]
    · exact fun h0 => hx1 (Subtype.ext h0)

end Psi

section Inspection

variable {I V G₁ G₂ : Subgroup G} (hV : IsElemAbelian 2 V)
  (hIV : I ≤ Subgroup.normalizer (V : Set G))
  (hC : I ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 I)
  (hI : CFSG.SectionRank.IsSQTKCat ↥I) (htr : F6.IsGoldschmidtTripleIn I G₁ G₂)
  (ham : IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
    ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))))
  (hF618 : F6.TheoremF618Cat) (hA : F618ComponentInspection)

include hI ham hF618 hA in
theorem inspection {M : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)} (hM : CFSG.IsComponent M) :
    (∀ (K : Type) [Field K] [Finite K] [CharP K 2],
      ¬ Nonempty (↥M ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))) ∧
      Odd (Nat.card ↥(Subgroup.centralizer (M : Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)))) ∧
      (Nonempty (↥M ≃* ↥(alternatingGroup (Fin 6))) →
        Subgroup.centralizer (M : Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) = ⊥) := by
  have hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty ((↥I ⧸ CFSG.pPrimeCore 3 ↥I) ≃* X ⧸ CFSG.pPrimeCore 3 X) :=
    ⟨↥I, inferInstance, inferInstance, hI, ⟨MulEquiv.refl _⟩⟩
  exact hA _ _ _ ham.toIsGoldschmidtTriple hX
    (hF618 _ _ _ ham.toIsGoldschmidtTriple hX) M hM

include hIV hC hI ham hF618 hA htr in
theorem false_of_commute_sq {K : Subgroup ↥(autI hV I)} (hK : CFSG.IsComponent K)
    {x : ↥(autI hV I)} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxK : ∀ k ∈ K, k * x = x * k) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := isComponent_map_psi hV hIV hC htr hK
  obtain ⟨-, hodd, -⟩ := inspection hI ham hF618 hA hM
  have hmem : psi hV hIV hC x ∈ Subgroup.centralizer
      ((K.map (psi hV hIV hC) : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) :
        Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hxK k hk]
  have hord : orderOf (psi hV hIV hC x) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hx2, map_one]) (psi_ne_one_of_sq hV hIV hC htr hx2 hx1)
  have h2 := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥(Subgroup.centralizer
      ((K.map (psi hV hIV hC) : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) :
        Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I))))
  rw [Subgroup.orderOf_mk, hord] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

include hIV hC hI ham hF618 hA htr in
theorem false_of_commute_cube {K : Subgroup ↥(autI hV I)} (hK : CFSG.IsComponent K)
    (e : ↥K ≃* ↥(alternatingGroup (Fin 6))) {y : ↥(autI hV I)} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hyK : ∀ k ∈ K, k * y = y * k) : False := by
  have hM := isComponent_map_psi hV hIV hC htr hK
  obtain ⟨-, -, h6⟩ := inspection hI ham hF618 hA hM
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥K := e.isSimpleGroup
  have hinj := psi_injective_of_ker hV hIV hC htr hK
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _)
  let e' : ↥(K.map (psi hV hIV hC)) ≃* ↥(alternatingGroup (Fin 6)) :=
    (MulEquiv.ofBijective _ ⟨hinj, (psi hV hIV hC).subgroupMap_surjective K⟩).symm.trans e
  have hC1 := h6 ⟨e'⟩
  have hmem : psi hV hIV hC y ∈ Subgroup.centralizer
      ((K.map (psi hV hIV hC) : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) :
        Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hyK k hk]
  rw [hC1, Subgroup.mem_bot] at hmem
  exact psi_ne_one_of_cube hV hIV hC hy3 hy1 hmem

include hIV hC hI ham hF618 hA htr in
theorem false_of_mulEquiv_sl2 {F : Subgroup ↥(autI hV I)} (hFn : F.Normal)
    (hFq : CFSG.IsQuasisimple ↥F) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ↥F ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : False := by
  have hFc : CFSG.IsComponent F := ⟨hFq, hFn.isSubnormal⟩
  have hM := isComponent_map_psi hV hIV hC htr hFc
  obtain ⟨h1, -, -⟩ := inspection hI ham hF618 hA hM
  have hZ : Subgroup.center ↥F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hx y]
    rw [center_statedSL_two_eq_bot K, Subgroup.mem_bot] at hex
    rw [Subgroup.mem_bot]
    exact e.injective (hex.trans (map_one e).symm)
  have hinj := psi_injective_of_ker hV hIV hC htr hFc (by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hFq
      (MonoidHom.normal_ker ((psi hV hIV hC).subgroupMap F)) with h | h
    · exact Or.inr h
    · left
      rw [hZ] at h
      exact le_bot_iff.mp h)
  exact h1 K ⟨(MulEquiv.ofBijective _ ⟨hinj, (psi hV hIV hC).subgroupMap_surjective F⟩).symm.trans
    e⟩

end Inspection

theorem exists_centralizer_of_fix {K TK W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hTKK : TK ≤ K) (hTK : ¬ 2 ∣ TK.relIndex K)
    {k₀ : G} (hk₀K : k₀ ∈ K) (hk₀ : ∀ n : ℕ, k₀ ^ 2 ^ n ≠ 1)
    (hfix : ∀ w ∈ ⁅W, K⁆, (∀ t ∈ TK, t * w = w * t) →
      k₀ * w * k₀⁻¹ * w⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    ∃ k ∈ K, (∀ n : ℕ, k ^ 2 ^ n ≠ 1) ∧
      ∀ z ∈ W, (∀ t ∈ TK, t * z = z * t) → z * k = k * z := by
  set U := ⁅W, K⁆ with hUdef
  have hUV : U ≤ W := commutator_le_of_le_normalizer hKW
  have hVc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ v ∈ W, v * v = 1 := fun v hv => by rw [← sq]; exact hW.2 v hv
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := fun k hk =>
    A4.mem_normalizer_commutator (hKW hk) (Subgroup.le_normalizer hk)
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k₀).ne'
  refine ⟨k₀ ^ 2 ^ a, K.pow_mem hk₀K _,
    fun n hn => hk₀ (a + n) (by rw [pow_add, pow_mul]; exact hn), fun z hzW hzT => ?_⟩
  set k := k₀ ^ 2 ^ a with hkdef
  have hkK : k ∈ K := K.pow_mem hk₀K _
  have hδ : ∀ k' ∈ K, k' * z * k'⁻¹ * z⁻¹ ∈ U := by
    intro k' hk'
    have h := Subgroup.commutator_mem_commutator hk' hzW
    rw [Subgroup.commutator_comm] at h
    simpa [commutatorElement_def] using h
  obtain ⟨w, hwU, hw⟩ := L15420.exists_mul_mem_centralizer hTK
    (fun a ha b hb => hVc a (hUV ha) b (hUV hb)) (fun u hu => hV2 u (hUV hu)) hKU hzT hδ
  have hwT : ∀ t ∈ TK, t * w = w * t := by
    intro t ht
    have h1 := hw t (hTKK ht)
    have h2 := hzT t ht
    have e : w = z * (w⁻¹ * z)⁻¹ := by group
    rw [e]
    calc t * (z * (w⁻¹ * z)⁻¹) = (t * z) * (w⁻¹ * z)⁻¹ := by group
      _ = z * (t * (w⁻¹ * z)⁻¹) := by rw [h2]; group
      _ = z * ((w⁻¹ * z)⁻¹ * t) := by
        congr 1
        calc t * (w⁻¹ * z)⁻¹ = (w⁻¹ * z)⁻¹ * ((w⁻¹ * z) * t) * (w⁻¹ * z)⁻¹ := by group
          _ = (w⁻¹ * z)⁻¹ * (t * (w⁻¹ * z)) * (w⁻¹ * z)⁻¹ := by rw [h1]
          _ = (w⁻¹ * z)⁻¹ * t := by group
      _ = z * (w⁻¹ * z)⁻¹ * t := by group
  set cc := k₀ * w * k₀⁻¹ * w⁻¹ with hccdef
  have hccC := hfix w hwU hwT
  have hwV : w ∈ W := hUV hwU
  have hccV : cc ∈ W := W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKW hk₀K) w).mp hwV)
    (W.inv_mem hwV)
  have hkw : k * w = w * k := by
    refine L15420.pow_mul_comm_of_conj_eq (c := cc) (by rw [hccdef]; group) ?_
      (hV2 cc hccV) hm hN
    exact (Subgroup.mem_centralizer_iff.mp hccC k₀ hk₀K).symm
  have hkc := hw k hkK
  calc z * k = (w * (w⁻¹ * z)) * k := by group
    _ = w * ((w⁻¹ * z) * k) := by group
    _ = w * (k * (w⁻¹ * z)) := by rw [hkc]
    _ = (k * w) * (w⁻¹ * z) := by rw [hkw]; group
    _ = k * z := by group

end C421

end CFSG.Quasithin.EmptyFaithfulMultiple
