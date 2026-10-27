module

public import CFSG.Quasithin.H13.L32AC47j
public import CFSG.Quasithin.H13.U3L139F
public import CFSG.Quasithin.H13.A5F91
public import CFSG.Quasithin.H13.L32AC47c
public import CFSG.Quasithin.H13.L32AC47h
public import CFSG.Quasithin.H13.L32ACSk3

public section

namespace CFSG.Quasithin.H13.L32A.C

open scoped Pointwise
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd_of_eq_mul {H K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {x a o : G} (hx : x ∈ H) (ha : a ∈ K)
    (ho : o ∈ H) (hxao : x = a * o) {n : ℕ} (hon : o ^ 2 ^ n = 1) (hodd : Odd (orderOf x)) :
    x ∈ K := by
  have hK'n : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hq : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) =
      QuotientGroup.mk (⟨o, ho⟩ : ↥H) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show x⁻¹ * o ∈ K
    rw [hxao, mul_inv_rev]
    have := (Subgroup.mem_normalizer_iff.mp (hKn ((H.inv_mem ho))) a⁻¹).mp (K.inv_mem ha)
    simpa using this
  have hd1 : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨o, ho⟩ : ↥H) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hon)
    rw [hq, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have hd2 : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) ∣ orderOf x := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_map_dvd (QuotientGroup.mk' (K.subgroupOf H)) _
  have hcop : Nat.Coprime (orderOf x) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  have hmk := orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1)
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
  exact hmk

theorem oTwoUpper_le_of_mem {X H K : Subgroup G}
    (h3 : (pCoreOf 2 (oTwoUpper X)).relIndex (oTwoUpper X) = 3) (hXH : oTwoUpper X ≤ H)
    (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {u : G} (hu : u ∈ oTwoUpper X)
    (huK : u ∈ K) (hu2 : u ∉ pCoreOf 2 (oTwoUpper X)) : oTwoUpper X ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := oTwoUpper X with hN
  set P := (pCoreOf 2 N).subgroupOf N with hP
  have hPn : P.Normal := by
    rw [hP, subgroupOf_pCoreOf_eq_pCore]
    exact CFSG.pCore_normal
  have hcard : Nat.card (↥N ⧸ P) = 3 := h3
  have hu1 : (QuotientGroup.mk (⟨u, hu⟩ : ↥N) : ↥N ⧸ P) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, hP, Subgroup.mem_subgroupOf]
    exact hu2
  have hgen := zpowers_eq_top_of_prime_card hcard hu1
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  have hxN : x ∈ N := Subgroup.subset_closure hx
  obtain ⟨i, hi⟩ : (QuotientGroup.mk (⟨x, hxN⟩ : ↥N) : ↥N ⧸ P) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨u, hu⟩ : ↥N) : ↥N ⧸ P) := hgen ▸ Subgroup.mem_top _
  have ho : ((⟨u, hu⟩ : ↥N) ^ i)⁻¹ * ⟨x, hxN⟩ ∈ P := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
    exact hi
  rw [hP, Subgroup.mem_subgroupOf] at ho
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) ⟨_, ho⟩
  have hon : ((u ^ i)⁻¹ * x) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine mem_of_odd_of_eq_mul hKH hKn (hXH hxN) (K.zpow_mem huK i)
    (H.mul_mem (H.inv_mem (H.zpow_mem (hXH hu) i)) (hXH hxN)) (by group) hon hx.2

@[expose] def IsTwoThree (n : ℕ) : Prop := ∃ a b : ℕ, n = 2 ^ a * 3 ^ b

theorem IsTwoThree.mul {m n : ℕ} (hm : IsTwoThree m) (hn : IsTwoThree n) : IsTwoThree (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a + c, b + d, by ring⟩

theorem IsTwoThree.of_dvd {m n : ℕ} (hn : IsTwoThree n) (h : m ∣ n) : IsTwoThree m := by
  obtain ⟨a, b, rfl⟩ := hn
  obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h₂
  exact ⟨i, j, rfl⟩

theorem isTwoThree_two_pow (a : ℕ) : IsTwoThree (2 ^ a) := ⟨a, 0, by ring⟩

theorem isTwoThree_three : IsTwoThree 3 := ⟨0, 1, by ring⟩

theorem isSolvable_of_isTwoThree {X : Type*} [Group X] [Finite X] (h : IsTwoThree (Nat.card X)) :
    Group.IsSolvable X := by
  obtain ⟨a, b, hab⟩ := h
  have := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hab])

omit [Finite G] in
theorem relIndex_sup_eq {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    A.relIndex (B ⊔ A) = A.relIndex B := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h).toEquiv.symm

omit [Finite G] in
theorem card_sup_eq {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(B ⊔ A) = A.relIndex B * Nat.card A := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := B ⊔ A)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_eq h] at h1
  exact h1.symm

theorem isTwoThree_card_sup {N T : Subgroup G} (h3 : (pCoreOf 2 N).relIndex N = 3)
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (N : Set G)) :
    IsTwoThree (Nat.card ↥(T ⊔ N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_sup_eq hTN]
  have hN : Nat.card N = 3 * Nat.card (pCoreOf 2 N) := by
    have hle : pCoreOf 2 N ≤ N := Subgroup.map_subtype_le _
    have := Subgroup.relIndex_mul_card (H := pCoreOf 2 N) (K := N)
    rw [inf_eq_left.mpr hle, h3] at this
    exact this.symm
  obtain ⟨e, he⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).exists_card_eq
  obtain ⟨t, ht⟩ := hT2.exists_card_eq
  refine IsTwoThree.mul ((isTwoThree_two_pow t).of_dvd ?_) ?_
  · rw [← ht]
    exact Subgroup.index_dvd_card _
  · rw [hN, he]
    exact isTwoThree_three.mul (isTwoThree_two_pow e)

theorem exists_conj_map_eq_of_sylow {K X : Type*} [Group K] [Group X] [Finite K] [Finite X]
    (π₀ : K →* X) (hπ₀ : Function.Surjective π₀) {S : Subgroup K} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) {D : Subgroup X} (hD2 : IsPGroup 2 D) (hDi : ¬ 2 ∣ D.index) :
    ∃ h : X, (S.map π₀).map (MulAut.conj h⁻¹).toMonoidHom = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (S.map π₀) := hS2.map π₀
  have h2 : ¬ 2 ∣ (S.map π₀).index := fun h => hSi (h.trans (Subgroup.index_map_dvd S hπ₀))
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq X (hD2.toSylow hDi) (h1.toSylow h2)
  have key : ∀ x : X, x ∈ S.map π₀ ↔ h⁻¹ * x * h ∈ D := by
    intro x
    change x ∈ ((h1.toSylow h2 : Sylow 2 X) : Subgroup X) ↔ _
    rw [← hh]
    simp only [Sylow.smul_def]
    change x ∈ (MulAut.conj h • ((hD2.toSylow hDi : Sylow 2 X) : Subgroup X)) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  refine ⟨h, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (key y).mp hy
    simpa [MulAut.conj_apply] using this
  · intro hx
    refine ⟨h * x * h⁻¹, (key _).mpr (by simpa [mul_assoc] using hx), ?_⟩
    simp [mul_assoc]

end Generic

section Setting

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem T_le_normalizer_l1 (h1332 : Stmt13_3_2) (S : Setting147 G T L V H) :
    T ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := S.hyp.normalizes (stmt13_3_2_two_of h1332)
  have h := A5.le_normalizer_oTwoRes_of_le_normalizer (F7.le_normalizer_inf hTL
    ((U3.T_le_normalizer_fsuV1 T V).trans Subgroup.le_normalizer))
  rwa [oTwoRes_eq_oTwoUpper] at h

theorem sl3_conj_injective :
    Function.Injective (MulAut.conj : A6.SL3.S →* MulAut A6.SL3.S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← sl3_center_eq_bot, Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun α : MulAut A6.SL3.S => α x) (MonoidHom.mem_ker.mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * g = g * x * g⁻¹ * g := by rw [this]
    _ = g * x := by group

theorem sl3_pow_four_of_two_pow {w : A6.SL3.S} {n : ℕ} (hw : w ^ 2 ^ n = 1) : w ^ 4 = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hw)
  have h168 : 2 ^ j ∣ 168 := by
    have := orderOf_dvd_natCard w
    rw [A6.SL3.card_S, hj] at this
    exact this
  have hj3 : j ≤ 3 := by
    by_contra hj3
    push Not at hj3
    have := (Nat.pow_dvd_pow 2 hj3).trans h168
    norm_num at this
  apply sl3_two_elt
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact Nat.pow_dvd_pow 2 hj3

theorem sl3_pow_21_of_odd {g : A6.SL3.S} (hg : Odd (orderOf g)) : g ^ 21 = 1 := by
  have h168 : orderOf g ∣ 21 * 8 := by
    have := orderOf_dvd_natCard g
    rw [A6.SL3.card_S] at this
    exact this
  have hcop : Nat.Coprime (orderOf g) 8 :=
    (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hg) : Nat.Coprime _ (2 ^ 3))
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h168)

theorem lemma14_7_47_l32_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h29 : Thm14_7_29) (h32 : Lemma14_7_32)
    (hMod : Lemma14_7_47_L32Mod) : Lemma14_7_47_L32 := by
  intro G _ _ T L V H S K hK hH hP
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK := h32 G T L V H S K hK
  have hKn := le_normalizer_of_setting h37 h38 S hK hTK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hL3 := relIndex_l1 h1222 h1332 h1334 S.hyp
  have hTl1 := T_le_normalizer_l1 h1332 S
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  set π₀ : ↥K →* A6.SL3.S := φ.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTsylH hKH hKn
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hTsylH.2.1.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := Subgroup.inf_subgroupOf_right T K ▸ hTsyl.2.2
  obtain ⟨h, hhD⟩ := exists_conj_map_eq_of_sylow π₀ hπ₀ hS2 hSi A6.SL3.P0_sylow.1
    A6.SL3.P0_sylow.2
  set π : ↥K →* A6.SL3.S := (MulAut.conj h⁻¹).toMonoidHom.comp π₀ with hπdef
  have hπ : Function.Surjective π := (MulAut.conj h⁻¹).surjective.comp hπ₀
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]
  have hD : (T.subgroupOf K).map π = A6.SL3.P0 := by
    rw [← hhD, Subgroup.map_map]
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN
  have hgen : ∀ y (hy : y ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ∧ Odd (orderOf y)),
      β ⟨y, hl1H (Subgroup.subset_closure hy)⟩ = 1 := by
    intro y hy
    have hyl1 : y ∈ l1 T L V := Subgroup.subset_closure hy
    have hyH : y ∈ H := hl1H hyl1
    have hodd : Odd (orderOf (β ⟨y, hyH⟩)) :=
      Odd.of_dvd_nat (by rw [Subgroup.orderOf_mk]; exact hy.2) (orderOf_map_dvd β _)
    obtain ⟨g, hg⟩ := mem_inner_of_odd_orderOf sl3_outer hodd
    by_contra hne
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hne (by rw [← hg, map_one])
    have hog : orderOf g = orderOf (β ⟨y, hyH⟩) := by
      rw [← hg, orderOf_injective _ sl3_conj_injective]
    obtain ⟨s, hs, hw⟩ := sl3_comm_fact g hg1 (sl3_pow_21_of_odd (hog ▸ hodd))
    have hsP : s ∈ (T.subgroupOf K).map π := hD ▸ A6.SL3.P0list_mem le_rfl s hs
    obtain ⟨s', hs'T, rfl⟩ := hsP
    have hs'T' : (s' : G) ∈ T := hs'T
    set yH : ↥H := ⟨y, hyH⟩ with hyHdef
    set s₀ : G := (s' : G) with hs₀
    have huK : y⁻¹ * (s₀ * y * s₀⁻¹) ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hKn (H.inv_mem hyH)) s₀).mp s'.2
      have e : y⁻¹ * (s₀ * y * s₀⁻¹) = (y⁻¹ * s₀ * y⁻¹⁻¹) * s₀⁻¹ := by group
      rw [e]
      exact K.mul_mem h1 (K.inv_mem s'.2)
    have hul1 : y⁻¹ * (s₀ * y * s₀⁻¹) ∈ l1 T L V :=
      (l1 T L V).mul_mem ((l1 T L V).inv_mem hyl1)
        ((Subgroup.mem_normalizer_iff.mp (hTl1 hs'T') y).mp hyl1)
    have hπu : π ⟨_, huK⟩ = g⁻¹ * π s' * g * (π s')⁻¹ := by
      have e1 : (⟨y⁻¹ * (s₀ * y * s₀⁻¹), huK⟩ : ↥K) = conjK (hKn yH⁻¹.2) s' * s'⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply, hyHdef, hs₀]
        group
      rw [e1, map_mul, map_inv, ← hβ, map_inv, ← hg]
      simp [mul_assoc]
    have hu2 : y⁻¹ * (s₀ * y * s₀⁻¹) ∉ pCoreOf 2 (l1 T L V) := by
      intro hmem
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l1 T L V)) ⟨_, hmem⟩
      have hun : (⟨_, huK⟩ : ↥K) ^ 2 ^ n = 1 := Subtype.ext (by
        have := congrArg Subtype.val hn
        simpa using this)
      have hπn : (π ⟨_, huK⟩) ^ 2 ^ n = 1 := by rw [← map_pow, hun, map_one]
      exact hw (hπu ▸ sl3_pow_four_of_two_pow hπn)
    exact hnot (oTwoUpper_le_of_mem hL3 hl1H hKH hKn hul1 huK hu2)
  have hL1β : ∀ x (hx : x ∈ l1 T L V), β ⟨x, hl1H hx⟩ = 1 := by
    have hle : l1 T L V ≤ β.ker.map H.subtype :=
      (Subgroup.closure_le _).2 fun y hy =>
        ⟨⟨y, hl1H (Subgroup.subset_closure hy)⟩, hgen y hy, rfl⟩
    intro x hx
    obtain ⟨x', hx'k, hx'⟩ := hle hx
    have e : (⟨x, hl1H hx⟩ : ↥H) = x' := Subtype.ext hx'.symm
    rw [e]
    exact hx'k
  have hcomm : ∀ x ∈ l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro x hx k hk
    have h1 := hβ ⟨x, hl1H hx⟩ ⟨k, hk⟩
    rw [hL1β x hx, MulAut.one_apply] at h1
    have h2 : π (conjK (hKn (hl1H hx)) ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) ((hker _).mp h2)
  by_cases hout : ∃ t ∈ T, ∀ k ∈ K, ∃ x ∈ K,
      t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K
  · obtain ⟨t, ht, hto⟩ := hout
    exact hMod G T L V H S K hK hH hP hnot hcomm t ht hto
  push Not at hout
  have hTin : ∀ t (ht : t ∈ T), β ⟨t, hTH ht⟩ ∈ inner A6.SL3.S := by
    intro t ht
    obtain ⟨k, hk, hkx⟩ := hout t ht
    refine ⟨π ⟨k, hk⟩, ?_⟩
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    have h1 := hkx (k * x * k⁻¹) (K.mul_mem (K.mul_mem hk x.2) (K.inv_mem hk))
    have e : t * k⁻¹ * (k * x * k⁻¹) * (t * k⁻¹)⁻¹ * (k * x * k⁻¹)⁻¹ =
        (t * x * t⁻¹) * (k * x * k⁻¹)⁻¹ := by group
    rw [e] at h1
    have h2 : π (conjK (hKn (hTH ht)) x * (⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹) = 1 := by
      refine (hker _).mpr ?_
      have e3 : ((conjK (hKn (hTH ht)) x * (⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹ : ↥K) : G) =
          (t * x * t⁻¹) * (k * x * k⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply]
      rw [e3]
      exact h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2.symm
  have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = MulAut.conj (π ⟨k, hk⟩) := by
    intro k hk
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hInn : ∀ y : ↥H, β y ∈ inner A6.SL3.S := by
    have hle : K ⊔ (l1 T L V ⊔ T) ≤ ((inner A6.SL3.S).comap β).map H.subtype := by
      refine sup_le (fun k hk => ⟨⟨k, hKH hk⟩, ⟨π ⟨k, hk⟩, (hKin k hk).symm⟩, rfl⟩)
        (sup_le (fun x hx => ⟨⟨x, hl1H hx⟩, ?_, rfl⟩) (fun t ht => ⟨⟨t, hTH ht⟩, hTin t ht, rfl⟩))
      show β ⟨x, hl1H hx⟩ ∈ inner A6.SL3.S
      rw [hL1β x hx]
      exact (inner A6.SL3.S).one_mem
    rw [← hH] at hle
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have e : y = y' := Subtype.ext hyy'.symm
    rw [e]
    exact hy'
  let e := MonoidHom.ofInjective sl3_conj_injective
  set ψ : ↥H →* A6.SL3.S := e.symm.toMonoidHom.comp (β.codRestrict _ hInn) with hψdef
  have hψ : ∀ y : ↥H, MulAut.conj (ψ y) = β y := by
    intro y
    have := congrArg Subtype.val (e.apply_symm_apply (β.codRestrict _ hInn y))
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = π ⟨k, hk⟩ := fun k hk =>
    sl3_conj_injective (by rw [hψ, hKin])
  have hψs : Function.Surjective ψ := fun g => by
    obtain ⟨k, rfl⟩ := hπ g
    exact ⟨⟨k, hKH k.2⟩, hψK k k.2⟩
  have hψl1 : ∀ x (hx : x ∈ l1 T L V), ψ ⟨x, hl1H hx⟩ = 1 := fun x hx =>
    sl3_conj_injective (by rw [hψ, hL1β x hx, map_one])
  have hψT : ∀ t (ht : t ∈ T), ψ ⟨t, hTH ht⟩ ∈ A6.SL3.P0 := by
    intro t ht
    refine sl3_normalizer_P0 _ fun p hp => ?_
    have hpP : p ∈ (T.subgroupOf K).map π := hD ▸ A6.SL3.P0list_mem le_rfl p hp
    obtain ⟨s, hsT, rfl⟩ := hpP
    have e1 : ψ ⟨t, hTH ht⟩ * π s * (ψ ⟨t, hTH ht⟩)⁻¹ = π (conjK (hKn (hTH ht)) s) := by
      rw [← MulAut.conj_apply, hψ, hβ]
    rw [e1]
    have hmem : π (conjK (hKn (hTH ht)) s) ∈ A6.SL3.P0 := by
      rw [← hD]
      refine ⟨_, ?_, rfl⟩
      show ((conjK (hKn (hTH ht)) s : ↥K) : G) ∈ T
      rw [conjK_apply]
      exact T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht)
    exact hmem
  obtain ⟨c, hc⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
  have hcK : Nat.card K = 168 * 2 ^ c := by
    have hle : pCoreOf 2 K ≤ K := Subgroup.map_subtype_le _
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 K).subgroupOf K),
      Nat.card_congr φ.toEquiv, A6.SL3.card_S,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hc]
  have hJK : l1 T L V ⊔ T ≤ Subgroup.normalizer (K : Set G) := (sup_le hl1H hTH).trans hKn
  have hidx : IsTwoThree (K.relIndex H) := by
    have h1 : K.relIndex H = K.relIndex (l1 T L V ⊔ T) := by
      rw [hH, sup_comm, relIndex_sup_eq hJK]
    rw [h1]
    have h2 := isTwoThree_card_sup hL3 hTsylH.2.1 hTl1
    rw [sup_comm] at h2
    exact h2.of_dvd (Subgroup.index_dvd_card _)
  have hcH : Nat.card H = K.relIndex H * (168 * 2 ^ c) := by
    have := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [inf_eq_left.mpr hKH, hcK] at this
    exact this.symm
  have hparab : ∀ X : Subgroup A6.SL3.S, Nat.card X = 24 → A6.SL3.P0 ≤ X →
      (X.comap ψ).map H.subtype ≤ Subgroup.normalizer (L : Set G) := by
    intro X hX24 hPX
    have hXidx : X.index = 7 := by
      have := X.card_mul_index
      rw [hX24, A6.SL3.card_S] at this
      omega
    have hcP : Nat.card ((X.comap ψ).map H.subtype) = K.relIndex H * (24 * 2 ^ c) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      have h1 := (X.comap ψ).card_mul_index
      rw [Subgroup.index_comap_of_surjective X hψs, hXidx, hcH] at h1
      have h2 : Nat.card (X.comap ψ) * 7 = K.relIndex H * (24 * 2 ^ c) * 7 := by
        rw [h1]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
    have hsolv : Group.IsSolvable ↥((X.comap ψ).map H.subtype) := by
      refine isSolvable_of_isTwoThree ?_
      rw [hcP]
      exact hidx.mul (⟨3 + c, 1, by ring⟩ : IsTwoThree (24 * 2 ^ c))
    refine h29 G T L V S.hyp _ (sup_le ?_ ?_) ((Subgroup.map_subtype_le _).trans S.hz.2.1)
      hsolv
    · intro x hx
      refine ⟨⟨x, hl1H hx⟩, ?_, rfl⟩
      show ψ ⟨x, hl1H hx⟩ ∈ X
      rw [hψl1 x hx]
      exact X.one_mem
    · intro t ht
      exact ⟨⟨t, hTH ht⟩, hPX (hψT t ht), rfl⟩
  have hM1 := hparab A6.SL3.X1 A6.SL3.card_X1 inf_le_left
  have hM2 := hparab A6.SL3.X2 A6.SL3.card_X2 inf_le_right
  apply S.hz.2.2
  have htop : (⊤ : Subgroup ↥H) = A6.SL3.X1.comap ψ ⊔ A6.SL3.X2.comap ψ := by
    rw [Subgroup.comap_sup_eq ψ _ _ hψs, sl3_sup_X, Subgroup.comap_top]
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥H) ∈ A6.SL3.X1.comap ψ ⊔ A6.SL3.X2.comap ψ :=
    htop ▸ Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem H.subtype hy'
  rw [Subgroup.map_sup] at this
  exact sup_le hM1 hM2 this

end Setting

end CFSG.Quasithin.H13.L32A.C
