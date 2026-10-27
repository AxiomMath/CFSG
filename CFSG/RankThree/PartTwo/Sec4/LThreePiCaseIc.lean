module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIb

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

section Elementary

theorem exists_mul_pow_eq_cube {M : Type*} [CommGroup M] [IsCyclic M] (α : M) {β : M}
    (hβ : ∀ μ : M, μ ^ 3 ≠ β) : ∃ k : ℕ, ∃ μ : M, α * β ^ k = μ ^ 3 := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := M)
  obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hω α)
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hω β)
  have hs : ¬ (3 : ℤ) ∣ s := by
    rintro ⟨m, rfl⟩
    exact hβ (ω ^ m) (by rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm]; norm_num)
  have key : ∀ k : ℕ, (3 : ℤ) ∣ t + k * s → ∃ μ : M, ω ^ t * (ω ^ s) ^ k = μ ^ 3 := by
    rintro k ⟨m, hm⟩
    refine ⟨ω ^ m, ?_⟩
    have e1 : ω ^ t * (ω ^ s) ^ k = ω ^ (t + k * s) := by
      rw [_root_.zpow_add, mul_comm (k : ℤ) s, _root_.zpow_mul, zpow_natCast]
    have e2 : (ω ^ m) ^ 3 = ω ^ (3 * m) := by
      rw [mul_comm, _root_.zpow_mul]
      norm_num
    rw [e1, e2, hm]
  by_cases h0 : (3 : ℤ) ∣ t
  · exact ⟨0, key 0 (by simpa using h0)⟩
  by_cases h1 : (3 : ℤ) ∣ t + s
  · exact ⟨1, key 1 (by simpa using h1)⟩
  · refine ⟨2, key 2 ?_⟩
    push_cast
    have ht : t % 3 = 1 ∨ t % 3 = 2 := by omega
    have hs' : s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases ht with ht | ht <;> rcases hs' with hs' | hs' <;> omega

theorem eq_nine_of_dvd {n : ℕ} (h1 : n ∣ 27) (h2 : 9 ∣ n) (h3 : n ≠ 27) : n = 9 := by
  have hle : n ≤ 27 := Nat.le_of_dvd (by norm_num) h1
  obtain ⟨k, rfl⟩ := h2
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · exact absurd h1 (by decide)
  · rfl
  · exact absurd h1 (by decide)
  · exact absurd rfl h3

variable {G : Type*} [Group G]

theorem eq_or_eq_inv_of_mem_zpowers {c d : G} (hc3 : orderOf c = 3)
    (hd : d ∈ Subgroup.zpowers c) (hd1 : d ≠ 1) : d = c ∨ d = c⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  rw [← zpow_mod_orderOf, hc3] at hd1 ⊢
  have hc : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  rcases (show k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 by omega)
    with h | h | h <;> rw [h] at hd1 ⊢
  · exact absurd (zpow_zero c) hd1
  · left; exact zpow_one c
  · right
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact hc

theorem commutator_inv_eq {u a c : G} (hcu : c * u = u * c)
    (h : u * a * u⁻¹ * a⁻¹ = c⁻¹) : u⁻¹ * a * u⁻¹⁻¹ * a⁻¹ = c := by
  have h1 : u * a * u⁻¹ = c⁻¹ * a := by rw [← h]; group
  have hcu' : u⁻¹ * c⁻¹ = c⁻¹ * u⁻¹ := by rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hcu]
  have h2 : a = c⁻¹ * (u⁻¹ * a * u) := by
    calc a = u⁻¹ * (u * a * u⁻¹) * u := by group
      _ = u⁻¹ * (c⁻¹ * a) * u := by rw [h1]
      _ = (u⁻¹ * c⁻¹) * a * u := by group
      _ = (c⁻¹ * u⁻¹) * a * u := by rw [hcu']
      _ = _ := by group
  have h3 : u⁻¹ * a * u = c * a := by
    calc u⁻¹ * a * u = c * (c⁻¹ * (u⁻¹ * a * u)) := by group
      _ = c * a := by rw [← h2]
  rw [inv_inv, h3]
  group

theorem closure_pair_eq (x y : G) :
    Subgroup.closure {x, y} = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    ← Set.insert_eq]

theorem le_of_card_eq_nine [Finite G] {A B H : Subgroup G} (hA : Nat.card A = 27) (hBA : B ≤ A)
    (hB : Nat.card B = 9) {a : G} (ha : a ∈ A) (haB : a ∉ B) (hBH : B ≤ H) (haH : a ∈ H) :
    A ≤ H := by
  have hM : B ≤ A ⊓ H := le_inf hBA hBH
  have h1 : Nat.card (A ⊓ H : Subgroup G) ∣ 27 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : 9 ∣ Nat.card (A ⊓ H : Subgroup G) := hB ▸ Subgroup.card_dvd_of_le hM
  by_cases h27 : Nat.card (A ⊓ H : Subgroup G) = 27
  · have : A ⊓ H = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA])
    rw [← this]
    exact inf_le_right
  · have h9 := eq_nine_of_dvd h1 h2 h27
    have : B = A ⊓ H := Subgroup.eq_of_le_of_card_ge hM (by rw [h9, hB])
    exact absurd (by rw [this]; exact Subgroup.mem_inf.mpr ⟨ha, haH⟩) haB

end Elementary

section Transport

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem isSLThreePi_of_equiv {X : Type} [Group X] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (e : X ≃* slPi π 3 (p ^ f) K) : IsSLThreePi X := by
  have := hK.finite
  cases π
  · exact ⟨p ^ f, K, inferInstance, inferInstance, Or.inr ⟨hK.card, hq, ⟨e⟩⟩⟩
  · exact ⟨p ^ f, K, inferInstance, inferInstance, Or.inl ⟨hK.card, hq, ⟨e⟩⟩⟩

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]

theorem inducesTypeOnSL_of (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {a : G} {y : GL (Fin 3) K} (hy : IsPGLAt e a y) {k : ℕ}
    (hk : Type123 π (p ^ f) K y k) : InducesTypeOnSL L a k := by
  refine ⟨mem_normalizer_of_normal a, π, p, f, K, inferInstance, hK, hq, e, y, hy.1, hk,
    fun z => ?_⟩
  have := hy.2 (e z)
  rw [slAct_apply, MulEquiv.symm_apply_apply] at this
  exact this

theorem isSLThreePiTwo_of (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {X : Subgroup G} (hLX : L ≤ X) {u a : G} (huX : u ∈ X)
    (haX : a ∈ X) (huC : u ∈ Subgroup.centralizer (L : Set G)) (huL : u ∉ L)
    (hu3 : orderOf u = 3) (ha3 : a ^ 3 = 1) (hX : X = L ⊔ Subgroup.closure {u, a})
    (h1 : u * a * u⁻¹ * a⁻¹ ≠ 1)
    (hZ : u * a * u⁻¹ * a⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set G)) {y : GL (Fin 3) K}
    (hy : IsPGLAt e a y) (hy3 : Type123 π (p ^ f) K y 3) : IsSLThreePiTwo ↥X := by
  let e' : L.subgroupOf X ≃* slPi π 3 (p ^ f) K := (Subgroup.subgroupOfEquivOfLe hLX).trans e
  refine ⟨L.subgroupOf X, inferInstance, ⟨u, huX⟩, ⟨a, haX⟩, isSLThreePi_of_equiv hK hq e', ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, π, p, f, K, inferInstance, hK, hq, e', y, hy.1, hy3, fun z => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp huC) g hg)
  · rw [Subgroup.mem_subgroupOf]
    exact huL
  · rw [Subgroup.orderOf_mk]
    exact hu3
  · exact Subtype.ext (by simp [ha3])
  · apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLX,
      MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hX.symm
  · intro h
    apply h1
    have := congrArg Subtype.val h
    simpa using this
  · rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    refine ⟨hZ.1, fun g hg => Subtype.ext ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hZ.2) g hg
  · have h := hy.2 (e' z)
    rw [coe_slAct_eq] at h
    rw [← h]
    simp only [e', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl

end Transport

section AltThree

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit [Finite G] in
theorem not_mem_sup_centralizer_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {a : G} {y : GL (Fin 3) K} (hy : IsPGLAt e a y)
    (h3 : Type123 π (p ^ f) K y 3) : a ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  intro haLC
  obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp haLC
  have hlu := isPGLAt_mul e (isPGLAt_of_mem e hπ hl) (isPGLAt_of_mem_centralizer e hu)
  rw [mul_one] at hlu
  refine not_inner_of_type3 hK hq hy.1 h3 ⟨_, (e ⟨l, hl⟩).2, fun m hm => ?_⟩
  have h1 := hy.2 ⟨m, hm⟩
  have h2 := hlu.2 ⟨m, hm⟩
  rw [h1] at h2
  exact h2

omit [Finite G] in
theorem commutator_mem_inf {u a b v : G} (hvL : v ∈ L) (hu : u = b * v⁻¹) (hab : a * b = b * a)
    (huC : u ∈ Subgroup.centralizer (L : Set G)) :
    u * a * u⁻¹ * a⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hba : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hab]
    have e1 : u * a * u⁻¹ * a⁻¹ = b * (v⁻¹ * (a * v * a⁻¹)) * b⁻¹ := by
      rw [hu]
      calc b * v⁻¹ * a * (b * v⁻¹)⁻¹ * a⁻¹ = b * v⁻¹ * a * v * (b⁻¹ * a⁻¹) := by group
        _ = b * v⁻¹ * a * v * (a⁻¹ * b⁻¹) := by rw [hba]
        _ = _ := by group
    rw [e1]
    exact hLn.conj_mem _ (mul_mem (inv_mem hvL) (hLn.conj_mem _ hvL a)) b
  · have hC : (Subgroup.centralizer (L : Set G)).Normal := inferInstance
    have e1 : u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) := by group
    rw [e1]
    exact mul_mem huC (hC.conj_mem _ (inv_mem huC) a)

omit [Finite G] in
theorem mem_statedScalars_of_commute_lifts (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {A : Subgroup G} {hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y}
    {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    {r : GL (Fin 3) K} (hr : ∀ a ∈ A, ∃ z, IsPGLAt e a z ∧ r * z = z * r) :
    r ∈ StatedScalars (Fin 3) K := by
  have h3 := hK.three_ne_zero hq
  have hcomm : ∀ {w : GL (Fin 3) K}, (w : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHom hK hq A hpgl).range → r * w = w * r := by
    intro w hw
    obtain ⟨⟨a, ha⟩, hpa⟩ := hw
    obtain ⟨z, hz, hrz⟩ := hr a ha
    rw [pglHom_apply (⟨a, ha⟩ : A) hz, QuotientGroup.eq] at hpa
    obtain ⟨t, ht⟩ := hpa
    have hwz : w = z * GeneralLinearGroup.scalar (Fin 3) t := by rw [ht]; group
    have hct := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t r
    rw [hwz]
    calc r * (z * GeneralLinearGroup.scalar (Fin 3) t) =
        z * r * GeneralLinearGroup.scalar (Fin 3) t := by rw [← mul_assoc, hrz]
      _ = z * (GeneralLinearGroup.scalar (Fin 3) t * r) := by rw [mul_assoc, hct.eq]
      _ = _ := by group
  exact mem_statedScalars_of_commute_heis h3 hζ1 (pow_three_eq_one_of_conj_eq_scalar_mul hζ) hζ
    (hcomm hy₁) (hcomm hy₂)

theorem alt411_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) (hAL : A ⊓ L ≤ Subgroup.zpowers c)
    {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    {a : G} (ha : a ∈ A) {y : GL (Fin 3) K} (hy : IsPGLAt e a y)
    (hy3 : Type123 π (p ^ f) K y 3) :
    Nat.card A = 27 ∧ IsSLThreePiTwo ↥(A ⊔ L) ∧ ∃ a ∈ A, InducesTypeOnSL L a 3 ∧
      ∃ u v : G, u ∈ Subgroup.centralizer (L : Set G) ∧ u ∉ L ∧ v ∈ L ∧
        v ∉ Subgroup.centralizer (L : Set G) ∧ orderOf u = 3 ∧ orderOf v = 3 ∧
        A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) = Subgroup.closure {c, u * v} ∧
        A ⊔ L = L ⊔ Subgroup.closure {u, a} ∧ u * a * u⁻¹ * a⁻¹ = c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hA27', -⟩ := card_eq_of_pgl hK hq hA hA27 hc3 hAc hpgl
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have ha3 : a ^ 3 = 1 := hA.1.2 a ha
  have haLC := not_mem_sup_centralizer_of_type3 hK hq hy hy3
  have haC : a ∉ Subgroup.centralizer (L : Set G) := fun h => haLC (Subgroup.mem_sup_right h)
  have hac : a ∉ Subgroup.zpowers c := by
    intro h
    have : a ∈ A ⊓ Subgroup.centralizer (L : Set G) := by rw [hAc]; exact h
    exact haC this.2
  have hca9 := card_zpowers_sup_zpowers ha3 hc3 hac (hAcomm a ha c hcAC.1)
  obtain ⟨x, hxA, hxca⟩ : ∃ x ∈ A, x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers a := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers a from
      fun x hx => hne x hx)
    omega
  obtain ⟨z, hz⟩ := hpgl x hxA
  have hdz := det_mem_rootsOfUnity hK hz.1
  have hdy := det_mem_rootsOfUnity hK hy.1
  have hnc : ∀ μ : rootsOfUnity (qSubPi π (p ^ f)) K,
      μ ^ 3 ≠ ⟨GeneralLinearGroup.det y, hdy⟩ := by
    intro μ hμ
    apply not_inner_of_type3 hK hq hy.1 hy3
    have h1 : ((μ : Kˣ) : K) ^ 3 = (y : Matrix (Fin 3) (Fin 3) K).det := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hμ]
      rfl
    obtain ⟨l, hl, -, hyl⟩ := exists_inner_of_det_eq_cube hK hy.1
      ((scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) h1.symm
    exact ⟨l, hl, fun m _ => hyl m⟩
  obtain ⟨k, μ, hkμ⟩ := exists_mul_pow_eq_cube (⟨GeneralLinearGroup.det z, hdz⟩ :
    rootsOfUnity (qSubPi π (p ^ f)) K) hnc
  have hwH : z * y ^ k ∈ glPi π 3 (p ^ f) K := mul_mem hz.1 (pow_mem hy.1 k)
  have hwdet : ((z * y ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((μ : Kˣ) : K) ^ 3 := by
    have h1 := congrArg (fun t : rootsOfUnity (qSubPi π (p ^ f)) K => ((t : Kˣ) : K)) hkμ
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      GeneralLinearGroup.val_det_apply] at h1
    rw [Units.val_mul, Matrix.det_mul, Units.val_pow_eq_pow_val, Matrix.det_pow]
    exact h1
  obtain ⟨l, hl, -, hwl⟩ := exists_inner_of_det_eq_cube hK hwH
    ((scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) hwdet
  obtain ⟨b, hbd⟩ : ∃ b, b = x * a ^ k := ⟨_, rfl⟩
  have hw : IsPGLAt e b (z * y ^ k) := by
    rw [hbd]
    exact isPGLAt_mul e hz (isPGLAt_pow hy k)
  have hbA : b ∈ A := by rw [hbd]; exact mul_mem hxA (pow_mem ha k)
  have hbc : b ∉ Subgroup.zpowers c := by
    intro hb
    apply hxca
    have : x = b * (a ^ k)⁻¹ := by rw [hbd]; group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hb)
      (Subgroup.mem_sup_right (inv_mem (pow_mem (Subgroup.mem_zpowers a) k)))
  have hbC : b ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    apply hbc
    rw [← hAc]
    exact ⟨hbA, h⟩
  have hb1 : Type123 π (p ^ f) K (z * y ^ k) 1 := by
    rcases type13_of_heis hK hq hAcomm hy₁ hy₂ hζ1 hζ hbA hbC (hA.1.2 b hbA) hw with h | h
    · exact h
    · exact absurd ⟨l, hl, fun m _ => hwl m⟩ (not_inner_of_type3 hK hq hwH h)
  obtain ⟨v, hv3, hbv, hbvC, μ', hev⟩ := exists_inner_decomp hK hq hw hb1
  obtain ⟨u, hu⟩ : ∃ u, u = b * (v : G)⁻¹ := ⟨_, rfl⟩
  have huC : u ∈ Subgroup.centralizer (L : Set G) := hu ▸ hbvC
  have hbuv : b = u * v := by rw [hu]; group
  have huv : u * v = v * u := ((Subgroup.mem_centralizer_iff.mp huC) v v.2).symm
  have huL : u ∉ L := fun h => hbc (hAL ⟨hbA, by rw [hbuv]; exact mul_mem h v.2⟩)
  have hvC : (v : G) ∉ Subgroup.centralizer (L : Set G) := fun h =>
    hbC (by rw [hbuv]; exact mul_mem huC h)
  have hu3 : orderOf u = 3 := by
    refine orderOf_eq_prime ?_ fun h => huL (h ▸ Subgroup.one_mem _)
    have hc : Commute b (v : G)⁻¹ := (show Commute b (v : G) from hbv).inv_right
    rw [hu, hc.mul_pow, hA.1.2 b hbA, inv_pow, hv3, inv_one, one_mul]
  have hv3o : orderOf (v : G) = 3 :=
    orderOf_eq_prime hv3 fun h => hvC (h ▸ Subgroup.one_mem _)
  have hbLC : b ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
    rw [hbuv]
    exact mul_mem (Subgroup.mem_sup_right huC) (Subgroup.mem_sup_left v.2)
  have hcb9 := card_zpowers_sup_zpowers (hA.1.2 b hbA) hc3 hbc (hAcomm b hbA c hcAC.1)
  have hcbB : Subgroup.zpowers c ⊔ Subgroup.zpowers b ≤
      A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hcAC.1, Subgroup.mem_sup_right hcAC.2⟩)
      (Subgroup.zpowers_le.mpr ⟨hbA, hbLC⟩)
  have haB : a ∉ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) := fun h =>
    haLC (Subgroup.mem_inf.mp h).2
  have hB : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) =
      Subgroup.zpowers c ⊔ Subgroup.zpowers b := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hcbB
    have h1 : Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) ∣ 27 :=
      hA27' ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : 9 ∣ Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) :=
      hcb9 ▸ Subgroup.card_dvd_of_le hcbB
    have h3 : Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) ≠ 27 := by
      intro h27
      have := Subgroup.eq_of_le_of_card_ge
        (inf_le_left : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ≤ A) (by rw [h27, hA27'])
      exact haB (by rw [this]; exact ha)
    rw [eq_nine_of_dvd h1 h2 h3, hcb9]
  have hB9 : Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) = 9 := by
    rw [hB]
    exact hcb9
  have hZ := commutator_mem_inf v.2 hu (hAcomm a ha b hbA) huC
  have hcomm : u * a * u⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := hLC ▸ hZ
  have hne : u * a * u⁻¹ * a⁻¹ ≠ 1 := by
    intro h1
    have hua : u * a = a * u := by
      calc u * a = u * a * u⁻¹ * a⁻¹ * (a * u) := by group
        _ = a * u := by rw [h1, one_mul]
    have hva : (v : G) * a = a * v := by
      have hv : (v : G) = u⁻¹ * b := by rw [hbuv]; group
      have hua' : u⁻¹ * a = a * u⁻¹ := by
        calc u⁻¹ * a = u⁻¹ * (a * u) * u⁻¹ := by group
          _ = u⁻¹ * (u * a) * u⁻¹ := by rw [hua]
          _ = a * u⁻¹ := by group
      rw [hv]
      calc u⁻¹ * b * a = u⁻¹ * (a * b) := by rw [mul_assoc, hAcomm a ha b hbA]
        _ = (u⁻¹ * a) * b := by group
        _ = a * (u⁻¹ * b) := by rw [hua']; group
    have hyw : y * (z * y ^ k) = z * y ^ k * y := by
      have h3 : slAct e ⟨a, mem_normalizer_of_normal a⟩ (e v) = e v := by
        rw [slAct_apply, MulEquiv.symm_apply_apply]
        congr 1
        apply Subtype.ext
        change a * (v : G) * a⁻¹ = v
        rw [← hva, mul_inv_cancel_right]
      have h2 := hy.2 (e v)
      rw [h3, hev] at h2
      have hcs := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ' y
      have h4 : y * (z * y ^ k * GeneralLinearGroup.scalar (Fin 3) μ') =
          z * y ^ k * GeneralLinearGroup.scalar (Fin 3) μ' * y := by
        calc y * (z * y ^ k * GeneralLinearGroup.scalar (Fin 3) μ') =
            y * (z * y ^ k * GeneralLinearGroup.scalar (Fin 3) μ') * y⁻¹ * y := by group
          _ = _ := by rw [← h2]
      apply mul_right_cancel (b := GeneralLinearGroup.scalar (Fin 3) μ')
      calc y * (z * y ^ k) * GeneralLinearGroup.scalar (Fin 3) μ' =
          y * (z * y ^ k * GeneralLinearGroup.scalar (Fin 3) μ') := by group
        _ = z * y ^ k * GeneralLinearGroup.scalar (Fin 3) μ' * y := h4
        _ = z * y ^ k * (GeneralLinearGroup.scalar (Fin 3) μ' * y) := by group
        _ = z * y ^ k * (y * GeneralLinearGroup.scalar (Fin 3) μ') := by rw [← hcs.eq]
        _ = _ := by group
    let H : Subgroup G :=
      { carrier := {g | g ∈ A ∧ ∃ t, IsPGLAt e g t ∧ y * t = t * y}
        mul_mem' := by
          rintro g g' ⟨hg, t, ht, hyt⟩ ⟨hg', t', ht', hyt'⟩
          refine ⟨mul_mem hg hg', t * t', isPGLAt_mul e ht ht', ?_⟩
          rw [← mul_assoc, hyt, mul_assoc, hyt', ← mul_assoc]
        one_mem' := ⟨Subgroup.one_mem _, 1,
          isPGLAt_of_mem_centralizer e (Subgroup.one_mem _), by rw [mul_one, one_mul]⟩
        inv_mem' := by
          rintro g ⟨hg, t, ht, hyt⟩
          have hg2 : g ^ 2 = g⁻¹ := by
            apply eq_inv_of_mul_eq_one_left
            rw [← pow_succ]
            exact hA.1.2 g hg
          refine ⟨inv_mem hg, t ^ 2, hg2 ▸ isPGLAt_pow ht 2, ?_⟩
          exact (Commute.pow_right (show Commute y t from hyt) 2).eq }
    have hBH : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ≤ H := by
      rw [hB]
      refine sup_le (Subgroup.zpowers_le.mpr ⟨hcAC.1, 1, isPGLAt_of_mem_centralizer e hcAC.2,
        by rw [mul_one, one_mul]⟩) (Subgroup.zpowers_le.mpr ⟨hbA, _, hw, hyw⟩)
    have hAH := le_of_card_eq_nine hA27' inf_le_left hB9 ha haB hBH ⟨ha, y, hy, rfl⟩
    have hys := mem_statedScalars_of_commute_lifts hK hq hy₁ hy₂ hζ1 hζ
      (fun g hg => (hAH hg).2)
    exact haC (mem_centralizer_of_isPGLAt_scalar hy hys)
  have huAL : u ∈ A ⊔ L := by
    rw [hu]
    exact mul_mem (Subgroup.mem_sup_left hbA) (Subgroup.mem_sup_right (inv_mem v.2))
  have hgen : ∀ u' : G, Subgroup.zpowers u' = Subgroup.zpowers u → u' ∈ A ⊔ L →
      A ⊔ L = L ⊔ Subgroup.closure {u', a} := by
    intro u' hu' hu'AL
    apply le_antisymm
    · refine sup_le ?_ le_sup_left
      refine le_of_card_eq_nine hA27' inf_le_left hB9 ha haB ?_
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      rw [hB]
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcL))
        (Subgroup.zpowers_le.mpr ?_)
      have hu'' : u ∈ Subgroup.closure {u', a} := by
        rw [closure_pair_eq, hu']
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
      rw [hbuv]
      exact mul_mem (Subgroup.mem_sup_right hu'') (Subgroup.mem_sup_left v.2)
    · refine sup_le le_sup_right ((Subgroup.closure_le _).mpr ?_)
      intro g hg
      rcases hg with rfl | rfl
      · exact hu'AL
      · exact Subgroup.mem_sup_left ha
  have hAL' := hgen u rfl huAL
  refine ⟨hA27', isSLThreePiTwo_of hK hq e le_sup_right huAL (Subgroup.mem_sup_left ha) huC
    huL hu3 ha3 hAL' hne hZ hy hy3, a, ha, inducesTypeOnSL_of hK hq e hy hy3, ?_⟩
  rcases eq_or_eq_inv_of_mem_zpowers hc3 hcomm hne with hpos | hneg
  · refine ⟨u, v, huC, huL, v.2, hvC, hu3, hv3o, ?_, hAL', hpos⟩
    rw [hB, ← hbuv, closure_pair_eq]
  · have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp huC) c hcL
    refine ⟨u⁻¹, (v : G)⁻¹, inv_mem huC, fun h => huL (by simpa using inv_mem h),
      inv_mem v.2, fun h => hvC (by simpa using inv_mem h), by rw [orderOf_inv]; exact hu3,
      by rw [orderOf_inv]; exact hv3o, ?_,
      hgen u⁻¹ Subgroup.zpowers_inv (inv_mem huAL), commutator_inv_eq hcu hneg⟩
    have : u⁻¹ * (v : G)⁻¹ = b⁻¹ := by rw [hbuv, huv, _root_.mul_inv_rev]
    rw [hB, this, closure_pair_eq, Subgroup.zpowers_inv]

theorem alt411_of_pgl (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) : Alt411 L A c := by
  classical
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, hE9⟩ := card_eq_of_pgl hK hq hA hA27 hc3 hAc hpgl
  by_cases hb : ∃ b ∈ A, b ∈ L ∧ b ∉ Subgroup.zpowers c
  · obtain ⟨b, hbA, hbL, hbc⟩ := hb
    exact Or.inl (alt411_one_of_pgl hK hq e hA hA27 hc3 hAc hpgl hbA hbL hbc)
  have hAL : A ⊓ L ≤ Subgroup.zpowers c := by
    intro b hb'
    by_contra hbc
    exact hb ⟨b, (Subgroup.mem_inf.mp hb').1, (Subgroup.mem_inf.mp hb').2, hbc⟩
  rcases frame_or_heis h3 hτ hτ1 (pglHom hK hq A hpgl).range (range_pglHom_comm hAcomm)
      (range_pglHom_pow hA.1.2) (by omega) with
    ⟨b, hb, hframe, z, hz, d, hd, hzb⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  · exact (false_of_frame hK hq e hA hc3 hAc hpgl hAL hb hframe hz hd hzb).elim
  by_cases h1 : ∀ a ∈ A, a ∉ Subgroup.centralizer (L : Set G) → ∀ y, IsPGLAt e a y →
      Type123 π (p ^ f) K y 1
  · exact Or.inr (Or.inl (alt411_two hK hq e hA hA27 hc3 hAc hpgl hAL hy₁ hy₂ hζ1 hζ h1))
  push Not at h1
  obtain ⟨a, ha, haC, y, hy, hy1⟩ := h1
  have hy3 := (type13_of_heis hK hq hAcomm hy₁ hy₂ hζ1 hζ ha haC (hA.1.2 a ha) hy).resolve_left
    hy1
  exact Or.inr (Or.inr (Or.inl
    (alt411_three hK hq e hA hA27 hc3 hAc hpgl hAL hy₁ hy₂ hζ1 hζ ha hy hy3)))

end AltThree

end CFSG.RankThree.PartTwo.Sec4
