module

public import CFSG.GH74.M12.Statements
public import CFSG.Quasithin.EmptyFaithful.S1422Extra
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.M12AmalInst

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12Amal CFSG.Sporadic.Bridge

section General

theorem sylow_three_of_element {H : Type*} [Group H] [Finite H] (x₀ : H) (hx₀ : orderOf x₀ = 3)
    (hc : ∀ q ∈ CFSG.pCore 2 H, x₀ * q = q * x₀ → ∀ y ∈ CFSG.pCore 2 H, q * y = y * q) :
    ∀ X : Sylow 3 H, ∀ q ∈ CFSG.pCore 2 H, (∀ x ∈ X, x * q = q * x) →
      ∀ y ∈ CFSG.pCore 2 H, q * y = y * q := by
  intro X q hq hX y hy
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀]; simp)
  obtain ⟨X', hX'⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H X' X
  have hgX : g * x₀ * g⁻¹ ∈ X := by
    have h1 : ((g • X' : Sylow 3 H) : Subgroup H) = (X : Subgroup H) := by rw [hg]
    show g * x₀ * g⁻¹ ∈ (X : Subgroup H)
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x₀, hX' (Subgroup.mem_zpowers x₀), by simp [MulAut.conj_apply]⟩
  have : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hnorm : ∀ p ∈ CFSG.pCore 2 H, g⁻¹ * p * g ∈ CFSG.pCore 2 H := by
    intro p hp
    have := (inferInstance : (CFSG.pCore 2 H).Normal).conj_mem p hp g⁻¹
    simpa using this
  have hq' : g⁻¹ * q * g ∈ CFSG.pCore 2 H := hnorm q hq
  have hcomm : x₀ * (g⁻¹ * q * g) = (g⁻¹ * q * g) * x₀ := by
    have := hX _ hgX
    calc x₀ * (g⁻¹ * q * g) = g⁻¹ * ((g * x₀ * g⁻¹) * q) * g := by group
      _ = g⁻¹ * (q * (g * x₀ * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * q * g) * x₀ := by group
  have h2 := hc _ hq' hcomm (g⁻¹ * y * g) (hnorm y hy)
  calc q * y = g * ((g⁻¹ * q * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * q * g)) * g⁻¹ := by rw [h2]
    _ = y * q := by group

theorem pCoreOf_le_T {H : Subgroup M12G} (hH : m12Data.T ≤ H) :
    CFSG.Open.pCoreOf 2 H ≤ m12Data.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 M12G := m12_syl.1.toSylow m12_syl.2
  have hP : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnorm : m12Data.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set M12G) :=
    hH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hsup : IsPGroup 2 (CFSG.Open.pCoreOf 2 H ⊔ m12Data.T : Subgroup M12G) :=
    hP.to_sup_of_normal_left' m12_syl.1 hnorm
  have h1 : CFSG.Open.pCoreOf 2 H ⊔ m12Data.T = (S : Subgroup M12G) :=
    S.is_maximal' hsup le_sup_right
  have h2 : (S : Subgroup M12G) = m12Data.T := rfl
  rw [h2] at h1
  exact le_sup_left.trans h1.le

theorem conj_mem_pCoreOf {H : Subgroup M12G} {g : M12G} (hg : g ∈ H) {p : M12G}
    (hp : p ∈ CFSG.Open.pCoreOf 2 H) :
    g * p * g⁻¹ ∈ CFSG.Open.pCoreOf 2 H ∧ g⁻¹ * p * g ∈ CFSG.Open.pCoreOf 2 H := by
  refine ⟨(Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) p).1 hp, ?_⟩
  have h2 := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hg)) p).1 hp
  simpa using h2

theorem core_tel {H : Subgroup M12G} (hH : m12Data.T ≤ H) {q : M12G}
    (hq : q ∈ CFSG.Open.pCoreOf 2 H) : ∃ i : Fin 64, telG i = q :=
  (m12Data.mem_T_iff q).1 (pCoreOf_le_T hH hq)

theorem closure_le_normalizer_of_conj {G : Type*} [Group G] (S : Set G) (K : Subgroup G)
    (h : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K ∧ s⁻¹ * k * s ∈ K) :
    Subgroup.closure S ≤ Subgroup.normalizer (K : Set G) := by
  refine (Subgroup.closure_le _).2 fun s hs => ?_
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => (h s hs k hk).1, fun hk => ?_⟩
  have := (h s hs _ hk).2
  have e : s⁻¹ * (s * k * s⁻¹) * s = k := by group
  rwa [e] at this

theorem map_map_symm_eq {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (M : Subgroup G) :
    (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

end General

theorem m12_pair_iso {T' M₁ M₂ : Subgroup M12G} (h : IsYAmalgamPair T' M₁ M₂) :
    Nonempty (↥M₁ ≃* ↥m12Data.A) ∨ Nonempty (↥M₁ ≃* ↥m12Data.B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsyl, hne, hiff⟩ := h
  obtain ⟨hM₁, hN₁⟩ := (hiff M₁).2 (Or.inl rfl)
  obtain ⟨-, hp', hidx'⟩ := hsyl
  have e1 : (T'.subgroupOf ⊤).index = T'.index := Subgroup.relIndex_top_right T'
  have hidx : ¬ 2 ∣ T'.index := by rwa [e1] at hidx'
  let S : Sylow 2 M12G := m12_syl.1.toSylow m12_syl.2
  let S' : Sylow 2 M12G := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M12G S S'
  have hk' : MulAut.conj k • m12Data.T = T' := by
    have h1 := congrArg (fun P : Sylow 2 M12G => (P : Subgroup M12G)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hT'map : T' = m12Data.T.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : M12G ≃* M12G := (MulAut.conj k).symm
  have hT'φ : T'.map φ.toMonoidHom = m12Data.T := by
    rw [hT'map]
    exact map_map_symm_eq (MulAut.conj k) m12Data.T
  have hM : IsMaximalTwoLocal (M₁.map φ.toMonoidHom) := isMaximalTwoLocal_map φ hM₁
  have hTle : m12Data.T ≤ M₁.map φ.toMonoidHom := by
    rw [← hT'φ]
    exact Subgroup.map_mono (Subgroup.le_normalizer.trans hN₁)
  rcases m12Extra.eq_A_or_B_of_maxTwoLocal hM hTle with hA | hB
  · exact Or.inl ⟨(Subgroup.equivMapOfInjective M₁ φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hA)⟩
  · exact Or.inr ⟨(Subgroup.equivMapOfInjective M₁ φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hB)⟩

theorem LAp_of_mem_core {i : Fin 64} (hq : telG i ∈ CFSG.Open.pCoreOf 2 m12Data.A) : LAp i := by
  obtain ⟨h1, h2⟩ := conj_mem_pCoreOf m12Data.x_mem_A hq
  obtain ⟨j₁, hj₁⟩ := core_tel m12Data.T_le_A h1
  obtain ⟨j₂, hj₂⟩ := core_tel m12Data.T_le_A h2
  have hj₁' : telG j₁ = genG 3 * telG i * (genG 3)⁻¹ := hj₁
  have hj₂' : telG j₂ = (genG 3)⁻¹ * telG i * genG 3 := hj₂
  have r1 : ReprG (compL (compL (gl 3) (tl i)) (gil 3)) (genG 3 * telG i * (genG 3)⁻¹) :=
    reprG_mul (reprG_mul (reprG_gen 3 (by norm_num)) (reprG_tel i i.2))
      (reprG_inv_gen 3 (by norm_num))
  have r2 : ReprG (compL (compL (gil 3) (tl i)) (gl 3)) ((genG 3)⁻¹ * telG i * genG 3) :=
    reprG_mul (reprG_mul (reprG_inv_gen 3 (by norm_num)) (reprG_tel i i.2))
      (reprG_gen 3 (by norm_num))
  rw [← hj₁'] at r1
  rw [← hj₂'] at r2
  refine ⟨?_, ?_⟩
  · rw [repL_unique r1 (reprG_tel j₁ j₁.2)]
    exact tl_mem_chk j₁ j₁.2
  · rw [repL_unique r2 (reprG_tel j₂ j₂.2)]
    exact tl_mem_chk j₂ j₂.2

theorem A_core_central {q y : M12G} (hq : q ∈ CFSG.Open.pCoreOf 2 m12Data.A)
    (hy : y ∈ CFSG.Open.pCoreOf 2 m12Data.A) (hqx : q * genG 3 = genG 3 * q) :
    q * y = y * q := by
  obtain ⟨i, rfl⟩ := core_tel m12Data.T_le_A hq
  obtain ⟨j, rfl⟩ := core_tel m12Data.T_le_A hy
  have hLi := LAp_of_mem_core hq
  have hLj := LAp_of_mem_core hy
  have r1 := reprG_mul (reprG_tel i i.2) (reprG_gen 3 (by norm_num))
  have r2 := reprG_mul (reprG_gen 3 (by norm_num)) (reprG_tel i i.2)
  rw [hqx] at r1
  have hc : compL (tl i) (gl 3) = compL (gl 3) (tl i) := repL_unique r1 r2
  have hl := A_central_chk i i.2 j j.2 hLi hLj hc
  refine eq_of_reprG (reprG_mul (reprG_tel i i.2) (reprG_tel j j.2)) ?_
  show ReprG (compL (tl i) (tl j)) (telG j * telG i)
  rw [hl]
  exact reprG_mul (reprG_tel j j.2) (reprG_tel i i.2)

theorem A_elt : ∃ x₀ : ↥m12Data.A, orderOf x₀ = 3 ∧
    ∀ q ∈ CFSG.pCore 2 ↥m12Data.A, x₀ * q = q * x₀ →
      ∀ y ∈ CFSG.pCore 2 ↥m12Data.A, q * y = y * q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : genG 3 ≠ 1 := ne_of_reprG (reprG_gen 3 (by norm_num)) reprG_one x_ne_one_chk
  refine ⟨⟨genG 3, m12Data.x_mem_A⟩, orderOf_eq_prime (Subtype.ext genG_orders.2.2.2.1)
    (fun h => hx1 (congrArg Subtype.val h)), ?_⟩
  intro q hq hqx y hy
  have hq' : ((q : ↥m12Data.A) : M12G) ∈ CFSG.Open.pCoreOf 2 m12Data.A :=
    (pCoreEquiv m12Data.A ⟨q, hq⟩).2
  have hy' : ((y : ↥m12Data.A) : M12G) ∈ CFSG.Open.pCoreOf 2 m12Data.A :=
    (pCoreEquiv m12Data.A ⟨y, hy⟩).2
  have hqx' : (q : M12G) * genG 3 = genG 3 * (q : M12G) := (congrArg Subtype.val hqx).symm
  exact Subtype.ext (A_core_central hq' hy' hqx')

theorem eq_of_compL_eq {i j k : ℕ} (hi : i < 64) (hj : j < 64) (hk : k < 64)
    (h : compL (tl i) (tl j) = tl k) : telG i * telG j = telG k :=
  eq_of_reprG (reprG_mul (reprG_tel i hi) (reprG_tel j hj))
    (show ReprG (compL (tl i) (tl j)) (telG k) by rw [h]; exact reprG_tel k hk)

@[expose] def K0 : Subgroup M12G where
  carrier := {g | ∃ i ∈ KIdx, g = telG i}
  one_mem' := ⟨0, by simp [KIdx], tel_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    obtain ⟨k, hk, hkl⟩ := K_mul_chk i hi j hj
    exact ⟨k, hk, eq_of_compL_eq (K_lt_chk i hi) (K_lt_chk j hj) (K_lt_chk k hk) hkl⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨k, hk, hkl⟩ := K_inv_chk i hi
    refine ⟨k, hk, ?_⟩
    have h1 : telG i * telG k = 1 :=
      eq_of_reprG (reprG_mul (reprG_tel i (K_lt_chk i hi)) (reprG_tel k (K_lt_chk k hk)))
        (show ReprG (compL (tl i) (tl k)) 1 by rw [hkl]; exact reprG_one)
    exact inv_eq_of_mul_eq_one_right h1

theorem K0_le_T : K0 ≤ m12Data.T := by
  rintro _ ⟨i, hi, rfl⟩
  exact m12Data.Tel_mem_T ⟨i, K_lt_chk i hi⟩

theorem K0_normal_gen : ∀ s ∈ ({genG 0, genG 1, genG 2, genG 3} : Set M12G), ∀ k ∈ K0,
    s * k * s⁻¹ ∈ K0 ∧ s⁻¹ * k * s ∈ K0 := by
  intro s hs k hk
  obtain ⟨i, hi, rfl⟩ := hk
  have hi64 := K_lt_chk i hi
  have key : ∀ g : ℕ, g < 4 → s = genG g →
      s * telG i * s⁻¹ ∈ K0 ∧ s⁻¹ * telG i * s ∈ K0 := by
    intro g hg hsg
    subst hsg
    obtain ⟨⟨k₁, hk₁, hl₁⟩, ⟨k₂, hk₂, hl₂⟩⟩ := K_norm_chk g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) i hi
    have hg4 : g < 5 := by omega
    have r1 : ReprG (compL (compL (gl g) (tl i)) (gil g)) (genG g * telG i * (genG g)⁻¹) :=
      reprG_mul (reprG_mul (reprG_gen g hg4) (reprG_tel i hi64)) (reprG_inv_gen g hg4)
    have r2 : ReprG (compL (compL (gil g) (tl i)) (gl g)) ((genG g)⁻¹ * telG i * genG g) :=
      reprG_mul (reprG_mul (reprG_inv_gen g hg4) (reprG_tel i hi64)) (reprG_gen g hg4)
    refine ⟨⟨k₁, hk₁, eq_of_reprG r1 (by rw [hl₁]; exact reprG_tel k₁ (K_lt_chk k₁ hk₁))⟩,
      ⟨k₂, hk₂, eq_of_reprG r2 (by rw [hl₂]; exact reprG_tel k₂ (K_lt_chk k₂ hk₂))⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h
  · exact key 0 (by norm_num) h
  · exact key 1 (by norm_num) h
  · exact key 2 (by norm_num) h
  · exact key 3 (by norm_num) h

theorem A_le_normalizer_K0 : m12Data.A ≤ Subgroup.normalizer (K0 : Set M12G) :=
  closure_le_normalizer_of_conj _ K0 K0_normal_gen

@[expose] def q8Hom : QuaternionGroup 2 →* M12G where
  toFun g := telG (q8Idx g)
  map_one' := by rw [q8_one_chk]; exact tel_zero
  map_mul' g h := by
    have hg := K_lt_chk _ (q8_mem_chk g)
    have hh := K_lt_chk _ (q8_mem_chk h)
    have hgh := K_lt_chk _ (q8_mem_chk (g * h))
    exact (eq_of_compL_eq hg hh hgh (q8_mul_chk g h)).symm

theorem q8Hom_injective : Function.Injective q8Hom := by
  intro g h hgh
  have h1 : telG (q8Idx g) = telG (q8Idx h) := hgh
  have hg := K_lt_chk _ (q8_mem_chk g)
  have hh := K_lt_chk _ (q8_mem_chk h)
  exact q8_inj_chk g h (tl_inj_chk _ hg _ hh
    (repL_unique (reprG_tel _ hg) (h1 ▸ reprG_tel _ hh)))

theorem q8Hom_range : q8Hom.range = K0 := by
  ext g
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q8Idx q, q8_mem_chk q, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨q, hq⟩ := q8_surj_chk i hi
    exact ⟨q, by simp only [q8Hom, MonoidHom.coe_mk, OneHom.coe_mk, hq]⟩

noncomputable def K0Equiv : K0 ≃* QuaternionGroup 2 :=
  ((MonoidHom.ofInjective q8Hom_injective).trans (MulEquiv.subgroupCongr q8Hom_range)).symm

theorem A_exists_q8_normal :
    ∃ K ∈ CFSG.GH74.M12.q8Subgroups (CFSG.pCore 2 ↥m12Data.A), K.Normal := by
  have hK0A : K0 ≤ m12Data.A := K0_le_T.trans m12Data.T_le_A
  have hnormal : (K0.subgroupOf m12Data.A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK0A).2 A_le_normalizer_K0
  have h2 : IsPGroup 2 (K0.subgroupOf m12Data.A) :=
    (m12_syl.1.to_le K0_le_T).of_equiv (Subgroup.subgroupOfEquivOfLe hK0A).symm
  refine ⟨K0.subgroupOf m12Data.A, ⟨?_, ⟨((Subgroup.subgroupOfEquivOfLe hK0A).trans K0Equiv)⟩⟩,
    hnormal⟩
  exact le_sSup ⟨hnormal, h2⟩

theorem PB_le_T : m12Extra.PB ≤ m12Data.T := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact m12Data.Tel_mem_T (4 : Fin 64)
  · exact m12Data.Tel_mem_T (8 : Fin 64)
  · exact m12Data.Tel_mem_T (29 : Fin 64)

theorem PB_le_core : m12Extra.PB ≤ CFSG.Open.pCoreOf 2 m12Data.B :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (PB_le_T.trans m12Data.T_le_B)
    m12Extra.PB_norm m12Extra.PB_p

theorem telG_mem_PB (i : ℕ) (hi : i ∈ [4, 8, 29]) : telG i ∈ m12Extra.PB := by
  apply Subgroup.subset_closure
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp

theorem LBp_of_mem_core {i : Fin 64} (hq : telG i ∈ CFSG.Open.pCoreOf 2 m12Data.B) : LBp i := by
  obtain ⟨h1, h2⟩ := conj_mem_pCoreOf m12Data.y_mem_B hq
  obtain ⟨j₁, hj₁⟩ := core_tel m12Data.T_le_B h1
  obtain ⟨j₂, hj₂⟩ := core_tel m12Data.T_le_B h2
  have hj₁' : telG j₁ = genG 4 * telG i * (genG 4)⁻¹ := hj₁
  have hj₂' : telG j₂ = (genG 4)⁻¹ * telG i * genG 4 := hj₂
  have r1 : ReprG (compL (compL (gl 4) (tl i)) (gil 4)) (genG 4 * telG i * (genG 4)⁻¹) :=
    reprG_mul (reprG_mul (reprG_gen 4 (by norm_num)) (reprG_tel i i.2))
      (reprG_inv_gen 4 (by norm_num))
  have r2 : ReprG (compL (compL (gil 4) (tl i)) (gl 4)) ((genG 4)⁻¹ * telG i * genG 4) :=
    reprG_mul (reprG_mul (reprG_inv_gen 4 (by norm_num)) (reprG_tel i i.2))
      (reprG_gen 4 (by norm_num))
  rw [← hj₁'] at r1
  rw [← hj₂'] at r2
  refine ⟨?_, ?_⟩
  · rw [repL_unique r1 (reprG_tel j₁ j₁.2)]
    exact tl_mem_chk j₁ j₁.2
  · rw [repL_unique r2 (reprG_tel j₂ j₂.2)]
    exact tl_mem_chk j₂ j₂.2

theorem B_core_central {p : M12G} (hp : p ∈ CFSG.Open.pCoreOf 2 m12Data.B) :
    telG 4 * p = p * telG 4 ∧ telG 8 * p = p * telG 8 := by
  obtain ⟨i, rfl⟩ := core_tel m12Data.T_le_B hp
  obtain ⟨h4, h8⟩ := B_central_chk i i.2 (LBp_of_mem_core hp)
  refine ⟨?_, ?_⟩
  · refine eq_of_reprG (reprG_mul (reprG_tel 4 (by norm_num)) (reprG_tel i i.2)) ?_
    show ReprG (compL (tl 4) (tl i)) (telG i * telG 4)
    rw [h4]
    exact reprG_mul (reprG_tel i i.2) (reprG_tel 4 (by norm_num))
  · refine eq_of_reprG (reprG_mul (reprG_tel 8 (by norm_num)) (reprG_tel i i.2)) ?_
    show ReprG (compL (tl 8) (tl i)) (telG i * telG 8)
    rw [h8]
    exact reprG_mul (reprG_tel i i.2) (reprG_tel 8 (by norm_num))

theorem eq_of_centerOrderTwo {P : Type*} [Group P] (h : CenterOrderTwo P) {u v : P}
    (hu : ∀ y, u * y = y * u) (hv : ∀ y, v * y = y * v) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  obtain ⟨w, -, -, hall⟩ := h
  exact ((hall u hu).resolve_left hu1).trans ((hall v hv).resolve_left hv1).symm

theorem false_of_isQ8Sq_pCoreOf_B (h : IsQ8Sq ↥(CFSG.Open.pCoreOf 2 m12Data.B)) : False := by
  have hT4 : telG 4 ∈ CFSG.Open.pCoreOf 2 m12Data.B := PB_le_core (telG_mem_PB 4 (by simp))
  have hT8 : telG 8 ∈ CFSG.Open.pCoreOf 2 m12Data.B := PB_le_core (telG_mem_PB 8 (by simp))
  have h4 : telG 4 ≠ 1 := telG_ne_one (by norm_num) z_ne_one_chk
  have h8 : telG 8 ≠ 1 := telG_ne_one (by norm_num) u8_ne_one_chk
  have hc : CenterOrderTwo ↥(CFSG.Open.pCoreOf 2 m12Data.B) := centerOrderTwo_of_isQ8Sq h
  have hu : ∀ y : ↥(CFSG.Open.pCoreOf 2 m12Data.B),
      (⟨telG 4, hT4⟩ : ↥(CFSG.Open.pCoreOf 2 m12Data.B)) * y = y * ⟨telG 4, hT4⟩ :=
    fun y => Subtype.ext (B_core_central y.2).1
  have hv : ∀ y : ↥(CFSG.Open.pCoreOf 2 m12Data.B),
      (⟨telG 8, hT8⟩ : ↥(CFSG.Open.pCoreOf 2 m12Data.B)) * y = y * ⟨telG 8, hT8⟩ :=
    fun y => Subtype.ext (B_core_central y.2).2
  have hu1 : (⟨telG 4, hT4⟩ : ↥(CFSG.Open.pCoreOf 2 m12Data.B)) ≠ 1 := by
    intro h1
    apply h4
    have := congrArg Subtype.val h1
    exact this
  have hv1 : (⟨telG 8, hT8⟩ : ↥(CFSG.Open.pCoreOf 2 m12Data.B)) ≠ 1 := by
    intro h1
    apply h8
    have := congrArg Subtype.val h1
    exact this
  have key := eq_of_centerOrderTwo hc hu hv hu1 hv1
  have key' := congrArg Subtype.val key
  exact ne_of_reprG (reprG_tel 4 (by norm_num)) (reprG_tel 8 (by norm_num)) z_ne_u8_chk key'

theorem isQ8Sq_pCoreOf_of_mulEquiv {G K : Type*} [Group G] [Group K] (H : Subgroup G)
    (L : Subgroup K) (e : ↥H ≃* ↥L) (h : IsQ8Sq ↥(CFSG.Open.pCoreOf 2 H)) :
    IsQ8Sq ↥(CFSG.Open.pCoreOf 2 L) := by
  have h1 : IsQ8Sq ↥(CFSG.pCore 2 ↥H) := IsQ8Sq.of_mulEquiv (pCoreEquiv H).symm h
  have h2 : ↥(CFSG.pCore 2 ↥H) ≃* ↥(CFSG.pCore 2 ↥L) :=
    (e.subgroupMap (CFSG.pCore 2 ↥H)).trans (MulEquiv.subgroupCongr (CFSG.pCore_map_iso 2 e))
  exact IsQ8Sq.of_mulEquiv (pCoreEquiv L) (IsQ8Sq.of_mulEquiv h2 h1)

theorem exists_q8_normal_of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : ∃ K ∈ CFSG.GH74.M12.q8Subgroups (CFSG.pCore 2 H), K.Normal) :
    ∃ K' ∈ CFSG.GH74.M12.q8Subgroups (CFSG.pCore 2 H'), K'.Normal := by
  obtain ⟨K, ⟨hle, ⟨iso⟩⟩, hnorm⟩ := h
  refine ⟨K.map e.toMonoidHom, ⟨?_, ⟨(e.subgroupMap K).symm.trans iso⟩⟩,
    hnorm.map _ e.surjective⟩
  rw [← CFSG.pCore_map_iso 2 e]
  exact Subgroup.map_mono hle

theorem facts_of_mulEquiv_A {Hh : Type*} [Group Hh] (e : Hh ≃* ↥m12Data.A) :
    (∀ X : Sylow 3 Hh, ∀ q ∈ CFSG.pCore 2 Hh, (∀ x ∈ X, x * q = q * x) →
      ∀ y ∈ CFSG.pCore 2 Hh, q * y = y * q) ∧
    ∃ K ∈ CFSG.GH74.M12.q8Subgroups (CFSG.pCore 2 Hh), K.Normal := by
  have : Finite Hh := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨?_, exists_q8_normal_of_mulEquiv e.symm A_exists_q8_normal⟩
  obtain ⟨x₀, hx₀, hc⟩ := A_elt
  have hmap : (CFSG.pCore 2 Hh).map e.toMonoidHom = CFSG.pCore 2 ↥m12Data.A :=
    CFSG.pCore_map_iso 2 e
  refine sylow_three_of_element (e.symm x₀) (by rw [MulEquiv.orderOf_eq]; exact hx₀) ?_
  intro q hq hqx y hy
  have hq' : e q ∈ CFSG.pCore 2 ↥m12Data.A := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hq
  have hy' : e y ∈ CFSG.pCore 2 ↥m12Data.A := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hy
  have hqx' : x₀ * e q = e q * x₀ := by
    apply e.symm.injective
    simpa using hqx
  apply e.injective
  rw [map_mul, map_mul]
  exact hc _ hq' hqx' _ hy'

theorem m12AmalgamFacts_unfolded :
    ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂)
        (fun Y _ => Nonempty (Y ≃* quasithinM12)) →
      IsL2Quot 1 (oTwoQuot ↥H₁) → IsQ8Sq ↥(pCoreOf 2 H₁) → IsL2Quot 1 (oTwoQuot ↥H₂) →
      Nat.card (pCoreOf 2 H₂) = 2 ^ 5 →
      (∀ X : Sylow 3 ↥H₁, ∀ q ∈ CFSG.pCore 2 ↥H₁, (∀ x ∈ X, x * q = q * x) →
        ∀ y ∈ CFSG.pCore 2 ↥H₁, q * y = y * q) ∧
      ∃ K ∈ CFSG.GH74.M12.q8Subgroups (CFSG.pCore 2 ↥H₁), K.Normal := by
  intro G _ _ H₁ H₂ hAm _ hQ8 _ _
  obtain ⟨Y, _, hP, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hAm
  obtain ⟨eY⟩ := hP
  have hpair' := IsYAmalgamPair.map eY hpair
  have e1 : ↥H₁ ≃* ↥(M₁.map eY.toMonoidHom) :=
    iso.φ1.trans (Subgroup.equivMapOfInjective M₁ eY.toMonoidHom eY.injective)
  rcases m12_pair_iso hpair' with ⟨⟨e2⟩⟩ | ⟨⟨e2⟩⟩
  · exact facts_of_mulEquiv_A (e1.trans e2)
  · exact (false_of_isQ8Sq_pCoreOf_B
      (isQ8Sq_pCoreOf_of_mulEquiv H₁ m12Data.B (e1.trans e2) hQ8)).elim

end CFSG.Quasithin
