module

public import CFSG.Quasithin.Background.C2Nine
import CFSG.Quasithin.Background.A3StructureBasic
import CFSG.Quasithin.Background.B6Basic
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace C2Six

section NoFinite

variable {G : Type} [Group G] {H R M : Subgroup G}

theorem mem_oTwoFIn {g : G} : g ∈ oTwoFIn H ↔
    ∃ hg : g ∈ H, (QuotientGroup.mk (⟨g, hg⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
      CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := by
  unfold oTwoFIn preimageModTwoCore
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, hmem⟩
    exact ⟨⟨g, hg⟩, hmem, rfl⟩

theorem mem_oTwoFIn_iff {y : ↥H} : (y : G) ∈ oTwoFIn H ↔
    (QuotientGroup.mk y : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
      CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  ⟨fun h => (mem_oTwoFIn.mp h).2, fun h => mem_oTwoFIn.mpr ⟨y.2, h⟩⟩

theorem oTwoFIn_le : oTwoFIn H ≤ H := Subgroup.map_subtype_le _

theorem oTwoFIn_subgroupOf : (oTwoFIn H).subgroupOf H =
    (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  unfold oTwoFIn preimageModTwoCore Subgroup.subgroupOf
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem normal_oTwoFIn_subgroupOf : ((oTwoFIn H).subgroupOf H).Normal := by
  rw [oTwoFIn_subgroupOf]
  exact Subgroup.Normal.comap inferInstance _

theorem le_normalizer_oTwoFIn : H ≤ Subgroup.normalizer (oTwoFIn H : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoFIn_le).mp normal_oTwoFIn_subgroupOf

theorem pCoreOf_le_oTwoFIn : pCoreOf 2 H ≤ oTwoFIn H := by
  rintro _ ⟨y, hy, rfl⟩
  refine mem_oTwoFIn_iff.mpr ?_
  have hy' : y ∈ CFSG.pCore 2 ↥H := by assumption
  have : (QuotientGroup.mk y : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hy'
  rw [this]
  exact one_mem _

theorem mem_pCore_two_iff {L : Subgroup G} {y : ↥L} :
    y ∈ CFSG.pCore 2 ↥L ↔ (y : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff y).symm

theorem exists_pow_mem_oTwoFIn_of_mem_sup (hRH : R ≤ H) (hR : IsPGroup 2 R) {x : G}
    (hx : x ∈ oTwoFIn H ⊔ R) : ∃ k : ℕ, x ^ 2 ^ k ∈ oTwoFIn H := by
  have hnorm : R ≤ Subgroup.normalizer (oTwoFIn H : Set G) := hRH.trans le_normalizer_oTwoFIn
  have hxset : x ∈ ((oTwoFIn H ⊔ R : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hxset
  obtain ⟨y, hy, r, hr, rfl⟩ := hxset
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  refine ⟨k, ?_⟩
  have := normal_oTwoFIn_subgroupOf (H := H)
  have hyH : y ∈ H := oTwoFIn_le hy
  have hrH : r ∈ H := hRH hr
  have hrk : (⟨r, hrH⟩ : ↥H) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ (oTwoFIn H).subgroupOf H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hy
  have h2 : (⟨y * r, H.mul_mem hyH hrH⟩ : ↥H) ^ 2 ^ k ∈ (oTwoFIn H).subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have : (⟨y * r, H.mul_mem hyH hrH⟩ : ↥H) = ⟨y, hyH⟩ * ⟨r, hrH⟩ := rfl
    rw [this, QuotientGroup.mk_mul, h1, one_mul, ← QuotientGroup.mk_pow, hrk, QuotientGroup.mk_one]
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa using h3

theorem le_oTwoFIn_of_isShort2 (hRH : R ≤ H) (hR : IsPGroup 2 R) {L : Subgroup G}
    (hL : IsShort2 L) (hLX : L ≤ oTwoFIn H ⊔ R) : L ≤ oTwoFIn H := by
  have hXH : oTwoFIn H ⊔ R ≤ H := sup_le oTwoFIn_le hRH
  let N : Subgroup ↥L := (oTwoFIn H).subgroupOf L
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgH : (g : G) ∈ H := hXH (hLX g.2)
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoFIn hgH) (n : G)).mp
      (Subgroup.mem_subgroupOf.mp hn)
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using this
  have hpg : IsPGroup 2 (↥L ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoFIn_of_mem_sup hRH hR (hLX g.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  have hNtop : N = ⊤ := hL.1 N hpg
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ N := by rw [hNtop]; trivial
  exact Subgroup.mem_subgroupOf.mp this

theorem natCard_pCore_quotient_of_isAltType_three {L : Subgroup G} (h : IsAltType L 3) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
  obtain ⟨α, hα, hker, -⟩ := h
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem not_isBorelOfBlock_self {L : Subgroup G} (hL3 : IsAltType L 3) : ¬ IsBorelOfBlock L L := by
  intro hB
  have hcard := natCard_pCore_quotient_of_isAltType_three hL3
  simp only [IsBorelOfBlock, hcard, ↓reduceIte] at hB
  have htop : CFSG.pCore 2 ↥L = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact mem_pCore_two_iff.mpr (hB y.2)
  have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
    rw [htop]
    exact Subgroup.index_top
  omega

end NoFinite

section Finite

variable {G : Type} [Group G] [Finite G] {H R M : Subgroup G}

theorem not_two_dvd_card_fitting (H : Subgroup G) :
    ¬ 2 ∣ Nat.card (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hp : CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ := pCore_two_quotient_pCore_two ↥H
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := inferInstance
  obtain ⟨S⟩ : Nonempty (Sylow 2 (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H))) := inferInstance
  have hS : S.map (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)).subtype ≤
      CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) :=
    Sylow.map_le_pCore inferInstance hnil 2 S
  rw [hp, le_bot_iff] at hS
  have hS1 : (S : Subgroup (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H))) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _
      (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)).subtype_injective).1 hS
  have hcard : Nat.card S = 1 := by rw [hS1]; exact Subgroup.card_bot
  have hS2 : 2 ∣ Nat.card S := Sylow.dvd_card_of_dvd_card S hdvd
  rw [hcard] at hS2
  exact Nat.prime_two.one_lt.ne' (Nat.dvd_one.1 hS2)

theorem mem_pCoreOf_of_pow_eq_one {x : G} (hx : x ∈ oTwoFIn H) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ pCoreOf 2 H := by
  obtain ⟨hxH, hxF⟩ := mem_oTwoFIn.mp hx
  set F := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hF
  set z : ↥F := ⟨(QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H), hxF⟩ with hz
  have hz1 : z ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have : (⟨x, hxH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    simp only [hz, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz1
  have h2 : orderOf z ∣ Nat.card F := orderOf_dvd_natCard z
  have hcop : Nat.Coprime (2 ^ k) (Nat.card F) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (not_two_dvd_card_fitting H))
  have h3 : orderOf z = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have h4 : z = 1 := orderOf_eq_one_iff.mp h3
  have h5 : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := by
    have := congrArg Subtype.val h4
    simpa [hz] using this
  have h6 : (⟨x, hxH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h5
  exact (mem_pCore_two_iff (L := H) (y := ⟨x, hxH⟩)).mp h6

theorem isSylowTwoOf_oTwoFIn_sup (hRH : R ≤ H) (hR : IsPGroup 2 R) (hP : pCoreOf 2 H ≤ R) :
    IsSylowTwoOf R (oTwoFIn H ⊔ R) := by
  have hnorm : R ≤ Subgroup.normalizer (oTwoFIn H : Set G) := hRH.trans le_normalizer_oTwoFIn
  refine A4.isSylowTwoOf_iff_maximal.mpr ⟨le_sup_right, hR, fun Q hQ hQp hRQ => ?_⟩
  intro q hq
  have hqYR : q ∈ ((oTwoFIn H ⊔ R : Subgroup G) : Set G) := hQ hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hqYR
  obtain ⟨y, hy, r, hr, rfl⟩ := hqYR
  have hyQ : y ∈ Q := by
    have : y * r * r⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem (hRQ hr))
    simpa using this
  have hyP : y ∈ pCoreOf 2 H := by
    obtain ⟨k, hk⟩ := hQp ⟨y, hyQ⟩
    exact mem_pCoreOf_of_pow_eq_one hy (k := k) (by
      have := congrArg Subtype.val hk
      simpa using this)
  exact R.mul_mem (hP hyP) hr

theorem charTwo_oTwoFIn_sup (hRH : R ≤ H) (hR : IsPGroup 2 R) (hF : CharTwo (oTwoFIn H)) :
    CharTwo (oTwoFIn H ⊔ R) := by
  set Y := oTwoFIn H with hY
  set X := Y ⊔ R with hX
  have hXnormY : X ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer (hRH.trans le_normalizer_oTwoFIn)
  have hWy : pCoreOf 2 Y ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 _)
    exact hXnormY.trans (normalizer_le_normalizer_pCoreOf 2 _)
  intro z hz
  obtain ⟨hzX, hzC⟩ := hz
  set Z : Subgroup G := X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) with hZ
  have hZnorm : X ≤ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hg
    have h2 : g ∈ Subgroup.normalizer (Subgroup.centralizer (pCoreOf 2 X : Set G) : Set G) :=
      B6.le_normalizer_centralizer (le_normalizer_pCoreOf 2 X) hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  have hZp : IsPGroup 2 Z := by
    intro g
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoFIn_of_mem_sup hRH hR (g.2.1 : (g : G) ∈ X)
    have hgk : (g : G) ^ 2 ^ k ∈ Z := Z.pow_mem g.2 _
    have hgkY : (g : G) ^ 2 ^ k ∈ pCoreOf 2 Y := by
      refine hF ⟨hk, ?_⟩
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWy) hgk.2
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 Y) ⟨_, hgkY⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hZW : Z ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 inf_le_left hZnorm hZp
  exact hZW ⟨hzX, hzC⟩

theorem mem_pCore_of_sq_mem {L : Subgroup G} (hLY : L ≤ oTwoFIn H) {ℓ : ↥L}
    (hℓ : ℓ ^ 2 ∈ CFSG.pCore 2 ↥L) : ℓ ∈ CFSG.pCore 2 ↥L := by
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (G := ↥L) (p := 2) ⟨ℓ ^ 2, hℓ⟩
  have h1 : ℓ ^ 2 ^ (k + 1) = 1 := by
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_succ', pow_mul]
    exact this
  have h2 : (ℓ : G) ^ 2 ^ (k + 1) = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  have hP : (ℓ : G) ∈ pCoreOf 2 H := mem_pCoreOf_of_pow_eq_one (hLY ℓ.2) h2
  have hLH : L ≤ H := hLY.trans oTwoFIn_le
  have hPL : pCoreOf 2 H ⊓ L ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 H (hLH hg), Subgroup.le_normalizer hg⟩
  exact mem_pCore_two_iff.mpr (hPL ⟨hP, ℓ.2⟩)

theorem eq_one_of_mul_self_eq_one {L : Subgroup G} (hLY : L ≤ oTwoFIn H) {K : Type*} [Group K]
    (α : ↥L →* K) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    {g : K} (hg : g * g = 1) : g = 1 := by
  obtain ⟨ℓ, rfl⟩ := hα g
  have h1 : α (ℓ ^ 2) = 1 := by rw [pow_two, map_mul]; exact hg
  have h2 : ℓ ^ 2 ∈ CFSG.pCore 2 ↥L := by rw [← hker]; exact h1
  have h3 := mem_pCore_of_sq_mem hLY h2
  rw [← hker] at h3
  exact h3

theorem not_isLin2Type {L : Subgroup G} (hLY : L ≤ oTwoFIn H) {n : ℕ} (hn : 1 ≤ n) :
    ¬ IsLin2Type L n := by
  rintro ⟨F, hFf, hFfin, hcard, α, hα, hker, -⟩
  let _ := hFf
  let _ := hFfin
  have hchar : (2 : F) = 0 := by
    have h2 : ringChar F = 2 := by
      refine FiniteField.even_card_iff_char_two.mpr ?_
      rw [hcard]
      exact Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have : CharP F 2 := ringChar.eq_iff.mp h2
    simpa using CharP.cast_eq_zero F 2
  let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hg1 : g ≠ 1 := by
    intro h
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [g] at this
  have hgg : g * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two]
    rw [one_add_one_eq_two]
    exact hchar
  exact hg1 (eq_one_of_mul_self_eq_one hLY α hα hker hgg)

theorem not_isAltType_five {L : Subgroup G} (hLY : L ≤ oTwoFIn H) : ¬ IsAltType L 5 := by
  rintro ⟨α, hα, hker, -⟩
  let g : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [alternatingGroup, MonoidHom.mem_ker, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
      rfl⟩
  have hg1 : g ≠ 1 := by decide
  have hgg : g * g = 1 := by decide
  exact hg1 (eq_one_of_mul_self_eq_one hLY α hα hker hgg)

theorem isAltType_three_of_isChi0Block {X L : Subgroup G} (hL : IsChi0Block X L)
    (hLY : L ≤ oTwoFIn H) : IsAltType L 3 := by
  rcases hL.2 with ⟨n, hn, hlin⟩ | h3 | h5
  · exact absurd hlin (not_isLin2Type hLY hn.le)
  · exact h3
  · exact absurd h5 (not_isAltType_five hLY)

end Finite

end C2Six

section Main

variable {G : Type} [Group G] [Finite G] {H R M : Subgroup G}

theorem c2_5 (hC129 : ASC129Statement G) (h : HypC23 H R M) (hR : IsSylowTwoOf R H)
    (hF : CharTwo H) :
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G), (∀ i, IsChi0Block H (Lb i)) ∧
      ∀ x ∈ H, ∃ m ∈ M, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧ x = m * (List.ofFn y).prod := by
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 H R M h.sqtk hF hR h.cgs h.le
  exact ⟨r, Lb, fun i => (hLb i).1, hprod⟩

theorem c2_6_one (h : HypC23 H R M) : IsSylowTwoOf R (oTwoFIn H ⊔ R) :=
  C2Six.isSylowTwoOf_oTwoFIn_sup h.radical.1 h.radical.isPGroup (c2_1_pCore_le h.radical)

theorem c2_6_two (hC129 : ASC129Statement G) (h : HypC23 H R M) (hF : CharTwo (oTwoFIn H))
    (_hnot : ¬ oTwoFIn H ≤ M) :
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G),
      (∀ i, IsBlock2 (oTwoFIn H) (Lb i) ∧ IsAltType (Lb i) 3 ∧ ¬ Lb i ≤ M) ∧
      ∀ x ∈ oTwoFIn H, ∃ m ∈ M ⊓ oTwoFIn H, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧
        x = m * (List.ofFn y).prod := by
  have hRH : R ≤ H := h.radical.1
  have hRp : IsPGroup 2 R := h.radical.isPGroup
  have hXH : oTwoFIn H ⊔ R ≤ H := sup_le C2Six.oTwoFIn_le hRH
  have hYX : oTwoFIn H ≤ oTwoFIn H ⊔ R := le_sup_left
  have hcgs : cgsIn (oTwoFIn H ⊔ R) R ≤ M ⊓ (oTwoFIn H ⊔ R) :=
    le_inf ((C2Nine.cgsIn_mono_left hXH R).trans h.cgs) (cgsIn_le _ R)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 (oTwoFIn H ⊔ R) R (M ⊓ (oTwoFIn H ⊔ R))
    (h.sqtk.mono hXH) (C2Six.charTwo_oTwoFIn_sup hRH hRp hF) (c2_6_one h) hcgs inf_le_right
  have hLY : ∀ i, Lb i ≤ oTwoFIn H := fun i =>
    C2Six.le_oTwoFIn_of_isShort2 hRH hRp (hLb i).1.1.1 (hLb i).1.1.2.1
  refine ⟨r, Lb, fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨hchi, hBor, -⟩ := hLb i
    have hLX : Lb i ≤ oTwoFIn H ⊔ R := hchi.1.2.1
    have hA3 : IsAltType (Lb i) 3 := C2Six.isAltType_three_of_isChi0Block hchi (hLY i)
    refine ⟨⟨hchi.1.1, hLY i, ?_⟩, hA3, fun hLM => ?_⟩
    · have hsub : IsSubnormal (Lb i) (oTwoFIn H ⊔ R) := IsBlock2.isSubnormal hchi.1
      exact (isSubnormal_iff_subgroupOf (hLY i)).mp (A3.subnormal_of_le_of_le hsub (hLY i) hYX)
    · apply C2Six.not_isBorelOfBlock_self hA3
      have : Lb i ⊓ (M ⊓ (oTwoFIn H ⊔ R)) = Lb i := inf_eq_left.mpr (le_inf hLM hLX)
      rwa [this] at hBor
  · obtain ⟨m, hm, y, hy, hxy⟩ := hprod x (hYX hx)
    have hprodY : (List.ofFn y).prod ∈ oTwoFIn H := by
      refine Subgroup.list_prod_mem _ fun z hz => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hLY i (hy i)
    have hmY : m ∈ oTwoFIn H := by
      have : m = x * ((List.ofFn y).prod)⁻¹ := by rw [hxy]; group
      rw [this]
      exact (oTwoFIn H).mul_mem hx ((oTwoFIn H).inv_mem hprodY)
    exact ⟨m, ⟨hm.1, hmY⟩, y, hy, hxy⟩

end Main

end CFSG.Quasithin
