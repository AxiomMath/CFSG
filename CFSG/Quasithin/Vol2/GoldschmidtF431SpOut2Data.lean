module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2X

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

universe u

namespace SpOut2

section Ctx

variable {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type u} [Group H] [Finite H]

structure OutCtx (m : ℕ) (Φ : antiSp F →* H) (ψ : H) (k₀ : ℕ) (U : Subgroup (antiSp F))
    (R : Fin 2 → Subgroup (antiSp F)) (i : Fin 3 → antiSp F) (N : Fin 2 → Subgroup H) :
    Prop where
  hm : 1 ≤ m
  P : OutProps Φ ψ k₀
  hD : SpDData U R i
  X : SpOutXData m U R i
  hN : ∀ j, N j = Subgroup.normalizer ((R j).map Φ : Set H)

variable {m : ℕ} {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ} {U : Subgroup (antiSp F)}
  {R : Fin 2 → Subgroup (antiSp F)} {i : Fin 3 → antiSp F} {N : Fin 2 → Subgroup H}

omit [Finite H] in
theorem OutCtx.hn (C : OutCtx m Φ ψ k₀ U R i N) : 2 ≤ 2 * m := by
  have := C.hm
  omega

omit [Finite H] in
theorem OutCtx.hF (C : OutCtx m Φ ψ k₀ U R i N) : Nat.card F = 2 ^ (2 * m) := C.X.card_F

omit [Finite H] in
theorem OutCtx.hcore (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    pCoreOf 2 (Subgroup.normalizer (R j : Set (antiSp F))) = R j := by
  fin_cases j
  · exact C.hD.borel.core₁
  · exact C.hD.borel.core₂

theorem OutCtx.sylow (C : OutCtx m Φ ψ k₀ U R i N) : IsSylowTwoOf (spT Φ ψ U) ⊤ :=
  C.P.isSylowTwoOf_spT (by have := C.hm; omega) C.hF C.X.U_fr C.hD.borel.sylow

omit [Finite H] in
theorem OutCtx.T_le (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) : spT Φ ψ U ≤ N j := by
  rw [C.hN j]
  unfold spT
  refine sup_le ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact map_mem_normalizer_map Φ (C.hD.shape.Q_norm j hu)
  · rw [Subgroup.zpowers_le]
    exact C.P.psi2_mem_normalizer_map (C.X.R_fr j)

theorem OutCtx.sylow_N (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    IsSylowTwoOf (spT Φ ψ U) (N j) :=
  F7.isSylowTwoOf_mono_right C.sylow (C.T_le j) le_top

theorem OutCtx.pCore_le_T (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    pCoreOf 2 (N j) ≤ spT Φ ψ U :=
  F7.isSylowTwoOf_pCoreOf_le (C.sylow_N j)

theorem OutCtx.pCore_le_range (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    pCoreOf 2 (N j) ≤ Φ.range := by
  intro y hy
  obtain ⟨u, hu, s, rfl⟩ := (C.P.mem_spT_iff C.X.U_fr).mp (C.pCore_le_T j hy)
  have htorus : frobAut F ^ (k₀ * (oddPart ψ * s)) = 1 := by
    refine C.X.torus j (k₀ * (oddPart ψ * s)) u hu ?_
    intro x hx
    have hxN : Φ x ∈ N j := by
      rw [C.hN j]
      exact map_mem_normalizer_map Φ hx
    have hc1 := pCoreOf_conj_mem hxN hy
    have hc2 := Subgroup.mul_mem _ hc1 (Subgroup.inv_mem _ hy)
    have h3 := C.P.act_psi2_pow s x⁻¹
    simp only [map_inv] at h3
    have e : Φ x * (Φ u * psi2 ψ ^ s) * (Φ x)⁻¹ * (Φ u * psi2 ψ ^ s)⁻¹ =
        Φ (x * u * ((frobAut F ^ (k₀ * (oddPart ψ * s))) x)⁻¹ * u⁻¹) := by
      calc Φ x * (Φ u * psi2 ψ ^ s) * (Φ x)⁻¹ * (Φ u * psi2 ψ ^ s)⁻¹
          = Φ x * Φ u * (psi2 ψ ^ s * (Φ x)⁻¹ * (psi2 ψ ^ s)⁻¹) * (Φ u)⁻¹ := by group
        _ = Φ (x * u * ((frobAut F ^ (k₀ * (oddPart ψ * s))) x)⁻¹ * u⁻¹) := by
          rw [h3]
          simp only [map_mul, map_inv]
    rw [e] at hc2
    have hxn : x ∈ Subgroup.normalizer (R j : Set (antiSp F)) := hx
    have hzN : x * u * ((frobAut F ^ (k₀ * (oddPart ψ * s))) x)⁻¹ * u⁻¹ ∈
        Subgroup.normalizer (R j : Set (antiSp F)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxn
        (C.hD.shape.Q_norm j hu)) (Subgroup.inv_mem _
        ((normalizer_stable (C.X.R_fr j _) x).mpr hxn))) (Subgroup.inv_mem _
        (C.hD.shape.Q_norm j hu))
    refine mem_of_map_mem_pCoreOf Φ C.P.inj (C.hcore j) hzN ?_
    rw [← C.hN j]
    exact hc2
  have h1 : psi2 ψ ^ s = 1 := by
    rw [psi2_pow_eq, C.P.pow_eq_one_iff]
    exact htorus
  rw [h1, mul_one]
  exact ⟨u, rfl⟩

theorem OutCtx.pCore_eq (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    pCoreOf 2 (N j) = (R j).map Φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨z, rfl⟩ := C.pCore_le_range j hy
    refine ⟨z, ?_, rfl⟩
    have hzN : z ∈ Subgroup.normalizer (R j : Set (antiSp F)) := by
      have h1 : Φ z ∈ N j := pCoreOf_le 2 (N j) hy
      rw [C.hN j] at h1
      have h2 : Φ z ∈ Subgroup.normalizer ((R j).map Φ : Set H) ⊓ Φ.range := ⟨h1, z, rfl⟩
      rw [normalizer_map_inf_range Φ C.P.inj (R j)] at h2
      obtain ⟨w, hw, hwz⟩ := h2
      rwa [← C.P.inj hwz]
    refine mem_of_map_mem_pCoreOf Φ C.P.inj (C.hcore j) hzN ?_
    rw [← C.hN j]
    exact hy
  · refine le_pCoreOf 2 ?_ ?_ ?_
    · rw [C.hN j]
      exact Subgroup.le_normalizer
    · exact Subgroup.normal_subgroupOf_of_le_normalizer (by rw [C.hN j])
    · exact (C.hD.borel.sylow.2.1.to_le (C.hD.shape.Q_le j)).map Φ

omit [Finite H] in
theorem OutCtx.spN_eq (j : Fin 2) : spN (N 0) (N 1) j = N j := by
  fin_cases j <;> rfl

theorem OutCtx.spQ_eq (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    spQ (N 0) (N 1) j = (R j).map Φ := by
  unfold spQ
  rw [OutCtx.spN_eq j]
  exact C.pCore_eq j

omit [Finite H] in
theorem OutCtx.N_inf_range (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    N j ⊓ Φ.range = (Subgroup.normalizer (R j : Set (antiSp F))).map Φ := by
  rw [C.hN j]
  exact normalizer_map_inf_range Φ C.P.inj (R j)

omit [Finite H] in
theorem OutCtx.spZ_eq (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) :
    spZ (N 0) (N 1) j = (spZc R j).map Φ := by
  unfold spZ spZc
  rw [OutCtx.spN_eq j, C.P.perfectCore_eq_inf_range, C.N_inf_range j,
    perfectCore_map_of_injective Φ C.P.inj, centerOf_map_of_injective Φ C.P.inj]

omit [Finite H] in
theorem spZc_stable {X : Type} [Group X] {R : Fin 2 → Subgroup X} (θ : MulAut X)
    (hR : ∀ j x, θ x ∈ R j ↔ x ∈ R j) (j : Fin 2) (x : X) :
    θ x ∈ spZc R j ↔ x ∈ spZc R j := by
  have hM : ∀ x, θ x ∈ Subgroup.normalizer (R j : Set X) ↔ x ∈ Subgroup.normalizer (R j : Set X) :=
    normalizer_stable (hR j)
  have h1 : (Subgroup.normalizer (R j : Set X)).map θ.toMonoidHom =
      Subgroup.normalizer (R j : Set X) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hM z).mpr hz
    · intro hy
      refine ⟨θ⁻¹ y, (hM _).mp ?_, by simp⟩
      simpa using hy
  have h2 : (perfectCore (Subgroup.normalizer (R j : Set X))).map θ.toMonoidHom =
      perfectCore (Subgroup.normalizer (R j : Set X)) := by
    rw [← perfectCore_map_of_injective θ.toMonoidHom θ.injective, h1]
  have h3 : (spZc R j).map θ.toMonoidHom = spZc R j := by
    unfold spZc
    rw [← centerOf_map_of_injective θ.toMonoidHom θ.injective, h2]
  constructor
  · intro hx
    rw [← h3] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := θ.injective hzx
    rwa [← this]
  · intro hx
    rw [← h3]
    exact ⟨x, hx, rfl⟩

theorem spZc_cls {X : Type} [Group X] [Finite X] {U : Subgroup X} {R : Fin 2 → Subgroup X}
    {i : Fin 3 → X} (hD : SpDData U R i) (j : Fin 2) {x y : X} (hx : x ∈ spZc R j)
    (hy : y ∈ centerOf U) (h : IsConj x y) : y ∈ spZc R j := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨n, hn, hnx⟩ := exists_normalizer_conj_of_central hD.borel.sylow (hD.Z_le j hx) hy hg
  have hnN : n ∈ Subgroup.normalizer (R j : Set X) := hD.shape.normalizer_le hD.borel.sylow hn j
  rw [← hnx]
  exact conj_mem_centerOf_perfectCore (M := Subgroup.normalizer (R j : Set X)) hnN hx

omit [Finite H] in
theorem OutCtx.Z_cls (C : OutCtx m Φ ψ k₀ U R i N) (j : Fin 2) {x y : H}
    (hx : x ∈ spZ (N 0) (N 1) j) (hy : y ∈ centerOf (U.map Φ)) (h : IsConj x y) :
    y ∈ spZ (N 0) (N 1) j := by
  rw [C.spZ_eq j] at hx ⊢
  rw [centerOf_map_of_injective Φ C.P.inj] at hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨a, s, rfl⟩ := C.P.gen g
  have e : Φ a * ψ ^ s * Φ x₀ * (Φ a * ψ ^ s)⁻¹ =
      Φ (a * (frobAut F ^ (k₀ * s)) x₀ * a⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← C.P.act_pow s x₀]
    group
  rw [e] at hg
  have hy0 : a * (frobAut F ^ (k₀ * s)) x₀ * a⁻¹ = y₀ := C.P.inj hg
  refine ⟨y₀, ?_, rfl⟩
  refine spZc_cls C.hD j (x := (frobAut F ^ (k₀ * s)) x₀) ?_ hy₀ ?_
  · exact (spZc_stable _ (fun j' x => C.X.R_fr j' _ x) j x₀).mpr hx₀
  · exact isConj_iff.mpr ⟨a, hy0⟩

open scoped Classical in
@[expose] noncomputable def spI (Φ : antiSp F →* H) (i : Fin 3 → antiSp F) : Finset H :=
  Finset.univ.image (fun k : Fin 3 => Φ (i k))

omit [Finite F] [CharP F 2] [Finite H] in
theorem mem_spI {x : H} : x ∈ spI Φ i ↔ ∃ k : Fin 3, Φ (i k) = x := by
  classical
  unfold spI
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

omit [Finite H] in
theorem OutProps.psi2_pow_commute (P : OutProps Φ ψ k₀) {a : antiSp F}
    (ha : ∀ k : ℕ, (frobAut F ^ k) a = a) (s : ℕ) : psi2 ψ ^ s * Φ a = Φ a * psi2 ψ ^ s := by
  have h := P.act_psi2_pow s a
  rw [ha] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem OutCtx.I_center (C : OutCtx m Φ ψ k₀ U R i N) {x : H} (hx : x ∈ spI Φ i) :
    x ∈ centerOf (spT Φ ψ U) := by
  obtain ⟨k, rfl⟩ := mem_spI.mp hx
  obtain ⟨hik, hcomm⟩ := mem_centerOf_iff.mp (C.hD.i_mem k)
  refine mem_centerOf_iff.mpr ⟨(C.P.mem_spT_iff C.X.U_fr).mpr ⟨i k, hik, 0, by simp⟩, ?_⟩
  intro t ht
  obtain ⟨u, hu, s, rfl⟩ := (C.P.mem_spT_iff C.X.U_fr).mp ht
  calc Φ u * psi2 ψ ^ s * Φ (i k) = Φ u * (psi2 ψ ^ s * Φ (i k)) := mul_assoc _ _ _
    _ = Φ u * (Φ (i k) * psi2 ψ ^ s) := by rw [C.P.psi2_pow_commute (C.X.i_fr · k) s]
    _ = Φ (u * i k) * psi2 ψ ^ s := by rw [map_mul, mul_assoc]
    _ = Φ (i k * u) * psi2 ψ ^ s := by rw [hcomm u hu]
    _ = Φ (i k) * (Φ u * psi2 ψ ^ s) := by rw [map_mul, mul_assoc]

omit [Finite H] in
theorem OutCtx.I_le_S (C : OutCtx m Φ ψ k₀ U R i N) {x : H} (hx : x ∈ spI Φ i) :
    x ∈ U.map Φ := by
  obtain ⟨k, rfl⟩ := mem_spI.mp hx
  exact Subgroup.mem_map_of_mem Φ (mem_centerOf_iff.mp (C.hD.i_mem k)).1

omit [Finite H] in
theorem OutCtx.order_two (C : OutCtx m Φ ψ k₀ U R i N) {x : H} (hx : x ∈ spI Φ i) :
    orderOf x = 2 := by
  obtain ⟨k, rfl⟩ := mem_spI.mp hx
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, C.hD.i_sq k, map_one]
  · intro h
    exact C.hD.i_ne k (C.P.inj (by rw [h, map_one]))

omit [Finite H] in
theorem OutCtx.nonconj (C : OutCtx m Φ ψ k₀ U R i N) {k k' : Fin 3}
    (h : IsConj (Φ (i k)) (Φ (i k'))) : k = k' := by
  have hmem : ∀ (j : Fin 2) (x : antiSp F), Φ x ∈ spZ (N 0) (N 1) j ↔ x ∈ spZc R j := by
    intro j x
    rw [C.spZ_eq j]
    exact Subgroup.mem_map_iff_mem C.P.inj
  have hiS : ∀ k, Φ (i k) ∈ centerOf (U.map Φ) := fun k => by
    rw [centerOf_map_of_injective Φ C.P.inj]
    exact Subgroup.mem_map_of_mem Φ (C.hD.i_mem k)
  have hiZ0 : Φ (i 0) ∈ spZ (N 0) (N 1) 0 := (hmem 0 _).mpr C.hD.i0
  have hiZ1 : Φ (i 1) ∈ spZ (N 0) (N 1) 1 := (hmem 1 _).mpr C.hD.i1
  have hi2Z0 : Φ (i 2) ∉ spZ (N 0) (N 1) 0 := fun h => C.hD.i2.1 ((hmem 0 _).mp h)
  have hi2Z1 : Φ (i 2) ∉ spZ (N 0) (N 1) 1 := fun h => C.hD.i2.2 ((hmem 1 _).mp h)
  have hi1Z0 : Φ (i 1) ∉ spZ (N 0) (N 1) 0 := fun h =>
    C.hD.i_ne 1 (C.hD.Z_inf _ ((hmem 0 _).mp h) C.hD.i1)
  have hi0Z1 : Φ (i 0) ∉ spZ (N 0) (N 1) 1 := fun h =>
    C.hD.i_ne 0 (C.hD.Z_inf _ C.hD.i0 ((hmem 1 _).mp h))
  by_contra hne
  fin_cases k <;> fin_cases k'
  · exact hne rfl
  · exact hi1Z0 (C.Z_cls 0 hiZ0 (hiS 1) h)
  · exact hi2Z0 (C.Z_cls 0 hiZ0 (hiS 2) h)
  · exact hi0Z1 (C.Z_cls 1 hiZ1 (hiS 0) h)
  · exact hne rfl
  · exact hi2Z1 (C.Z_cls 1 hiZ1 (hiS 2) h)
  · exact hi2Z0 (C.Z_cls 0 hiZ0 (hiS 2) h.symm)
  · exact hi2Z1 (C.Z_cls 1 hiZ1 (hiS 2) h.symm)
  · exact hne rfl

omit [Finite H] in
theorem OutCtx.fusion (C : OutCtx m Φ ψ k₀ U R i N) {x : H} (hx : x ∈ U.map Φ)
    (hxo : orderOf x = 2) : ∃ y ∈ spI Φ i,
      (∃ g ∈ N 0, g * x * g⁻¹ = y) ∨ (∃ g ∈ N 1, g * x * g⁻¹ = y) := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hxo
    exact absurd hxo (by norm_num)
  have hu2 : u ^ 2 = 1 := C.P.inj (by
    rw [map_pow, map_one]
    exact hxo ▸ pow_orderOf_eq_one _)
  obtain ⟨k, j, g, hg, hgu⟩ := C.hD.fus u hu hu1 hu2
  refine ⟨Φ (i k), mem_spI.mpr ⟨k, rfl⟩, ?_⟩
  have hgN : Φ g ∈ N j := by
    rw [C.hN j]
    exact map_mem_normalizer_map Φ hg
  have e : Φ g * Φ u * (Φ g)⁻¹ = Φ (i k) := by
    rw [← map_inv, ← map_mul, ← map_mul, hgu]
  fin_cases j
  · exact Or.inl ⟨Φ g, hgN, e⟩
  · exact Or.inr ⟨Φ g, hgN, e⟩

omit [Finite H] in
theorem OutCtx.rep (C : OutCtx m Φ ψ k₀ U R i N) {x : H} (hx : x ∈ U.map Φ)
    (hxo : orderOf x = 2) : ∃! y, y ∈ spI Φ i ∧ IsConj y x := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hxo
    exact absurd hxo (by norm_num)
  have hu2 : u ^ 2 = 1 := C.P.inj (by
    rw [map_pow, map_one]
    exact hxo ▸ pow_orderOf_eq_one _)
  obtain ⟨k, j, g, hg, hgu⟩ := C.hD.fus u hu hu1 hu2
  have hconj : IsConj (Φ (i k)) (Φ u) := by
    refine isConj_iff.mpr ⟨Φ g⁻¹, ?_⟩
    have e : g⁻¹ * i k * g⁻¹⁻¹ = u := by rw [← hgu]; group
    rw [← map_inv, ← map_mul, ← map_mul, e]
  refine ⟨Φ (i k), ⟨mem_spI.mpr ⟨k, rfl⟩, hconj⟩, ?_⟩
  rintro y ⟨hyI, hyc⟩
  obtain ⟨k', rfl⟩ := mem_spI.mp hyI
  rw [C.nonconj (hyc.trans hconj.symm)]

@[expose] noncomputable def spf (ψ : H) : H := psi2 ψ ^ 2 ^ (twoExp ψ - 1)

omit [Finite F] [CharP F 2] [Finite H] in
theorem spf_mem (ψ : H) : spf ψ ∈ Subgroup.zpowers (psi2 ψ) :=
  Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem spf_sq {ψ : H} (hev : Even (orderOf ψ)) : spf ψ ^ 2 = 1 := by
  unfold spf
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (twoExp_pos hev)]
  exact psi2_pow_two_exp ψ

theorem spf_ne_one {ψ : H} (hev : Even (orderOf ψ)) : spf ψ ≠ 1 := by
  unfold spf
  refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero) ?_
  rw [orderOf_psi2]
  exact Nat.pow_lt_pow_right (by norm_num) (by have := twoExp_pos hev; omega)

theorem OutProps.spf_not_mem_range {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hev : Even (orderOf ψ)) : spf ψ ∉ Φ.range := by
  intro h
  exact spf_ne_one hev ((P.psi2_pow_mem_range_iff hn hF _).mp h)

omit [Finite H] in
theorem OutProps.act_spf (P : OutProps Φ ψ k₀) (x : antiSp F) :
    spf ψ * Φ x * (spf ψ)⁻¹ =
      Φ ((frobAut F ^ (k₀ * (oddPart ψ * 2 ^ (twoExp ψ - 1)))) x) :=
  P.act_psi2_pow _ x

theorem OutProps.spf_act_ne_one (P : OutProps Φ ψ k₀) (hev : Even (orderOf ψ)) :
    frobAut F ^ (k₀ * (oddPart ψ * 2 ^ (twoExp ψ - 1))) ≠ 1 := by
  intro h
  apply spf_ne_one hev
  unfold spf
  rw [psi2_pow_eq, P.pow_eq_one_iff]
  exact h

theorem OutCtx.phi0_eq (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) :
    frobAut F ^ (k₀ * (oddPart ψ * 2 ^ (twoExp ψ - 1))) = frobAut F ^ m := by
  have hn1 : 1 ≤ 2 * m := by have := C.hm; omega
  set c := k₀ * (oddPart ψ * 2 ^ (twoExp ψ - 1)) with hc
  have hne : frobAut F ^ c ≠ 1 := C.P.spf_act_ne_one hev
  have h2 : frobAut F ^ (2 * c) = 1 := by
    have h := spf_sq hev
    unfold spf at h
    rw [← pow_mul, psi2_pow_eq, C.P.pow_eq_one_iff] at h
    rw [← h]
    congr 1
    rw [hc]
    ring
  rw [frobAut_pow_eq_one_iff hn1 C.hF] at h2
  rw [Ne, frobAut_pow_eq_one_iff hn1 C.hF] at hne
  have hmc : m ∣ c := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
    (by rw [show 2 * m = 2 * m from rfl]; simpa [mul_comm] using h2)
  obtain ⟨q, hq⟩ := hmc
  have hqodd : Odd q := by
    rcases Nat.even_or_odd q with ⟨r, hr⟩ | h
    · exfalso
      apply hne
      exact ⟨r, by rw [hq, hr]; ring⟩
    · exact h
  obtain ⟨r, hr⟩ := hqodd
  have : c = 2 * m * r + m := by rw [hq, hr]; ring
  rw [this, pow_add, pow_mul, frobAut_pow_card C.hF, one_pow, one_mul]

theorem OutCtx.spf_conj (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) (x : antiSp F) :
    spf ψ * Φ x = Φ ((frobAut F ^ m) x) * spf ψ := by
  have h := C.P.act_spf x
  rw [C.phi0_eq hev] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem OutCtx.mem_spTf_iff (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) {y : H} :
    y ∈ spTf (spT Φ ψ U) (spf ψ) ↔ ∃ u ∈ (U ⊓ fixedSubgroup (frobAut F ^ m) :
      Subgroup (antiSp F)), ∃ s : ℕ, y = Φ u * psi2 ψ ^ s := by
  have hcomm : ∀ s : ℕ, spf ψ * psi2 ψ ^ s = psi2 ψ ^ s * spf ψ := fun s => by
    unfold spf
    exact (Commute.pow_pow_self (psi2 ψ) _ s).eq
  unfold spTf
  constructor
  · rintro ⟨hyT, hyC⟩
    obtain ⟨u, hu, s, rfl⟩ := (C.P.mem_spT_iff C.X.U_fr).mp hyT
    refine ⟨u, ⟨hu, ?_⟩, s, rfl⟩
    have key : Φ u * psi2 ψ ^ s * spf ψ = spf ψ * (Φ u * psi2 ψ ^ s) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyC
    have key2 : Φ u * psi2 ψ ^ s * spf ψ = Φ ((frobAut F ^ m) u) * psi2 ψ ^ s * spf ψ := by
      rw [key, ← mul_assoc, C.spf_conj hev u, mul_assoc, hcomm s, mul_assoc]
    have key3 := mul_right_cancel key2
    have key4 : Φ u = Φ ((frobAut F ^ m) u) := mul_right_cancel key3
    exact (C.P.inj key4).symm
  · rintro ⟨u, ⟨hu, hfix⟩, s, rfl⟩
    refine ⟨(C.P.mem_spT_iff C.X.U_fr).mpr ⟨u, hu, s, rfl⟩, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hfix' : (frobAut F ^ m) u = u := hfix
    calc Φ u * psi2 ψ ^ s * spf ψ = Φ u * (psi2 ψ ^ s * spf ψ) := mul_assoc _ _ _
      _ = Φ u * (spf ψ * psi2 ψ ^ s) := by rw [hcomm s]
      _ = (Φ u * spf ψ) * psi2 ψ ^ s := (mul_assoc _ _ _).symm
      _ = (spf ψ * Φ u) * psi2 ψ ^ s := by
        congr 1
        have := C.spf_conj hev u
        rw [hfix'] at this
        exact this.symm
      _ = spf ψ * (Φ u * psi2 ψ ^ s) := mul_assoc _ _ _

omit [Finite H] in
theorem OutCtx.frobAut_pow_m_ne_one (C : OutCtx m Φ ψ k₀ U R i N) : frobAut F ^ m ≠ 1 := by
  intro h
  have hn1 : 1 ≤ 2 * m := by have := C.hm; omega
  rw [frobAut_pow_eq_one_iff hn1 C.hF] at h
  have := Nat.le_of_dvd C.hm h
  have := C.hm
  omega

theorem OutCtx.f_not_central (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) :
    spf ψ ∉ centerOf (spT Φ ψ U) := by
  intro h
  obtain ⟨u, hu, hmove⟩ := C.X.moves m C.frobAut_pow_m_ne_one
  have hT : Φ u ∈ spT Φ ψ U := (C.P.mem_spT_iff C.X.U_fr).mpr ⟨u, hu, 0, by simp⟩
  have h1 := (mem_centerOf_iff.mp h).2 _ hT
  rw [C.spf_conj hev u] at h1
  exact hmove (C.P.inj (mul_right_cancel h1)).symm

omit [Finite H] in
theorem OutCtx.frobPow_U0 (C : OutCtx m Φ ψ k₀ U R i N) (k : ℕ) (x : antiSp F) :
    (frobAut F ^ k) x ∈ (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) ↔
      x ∈ (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) := by
  have hfix : (frobAut F ^ m) ((frobAut F ^ k) x) = (frobAut F ^ k) x ↔
      (frobAut F ^ m) x = x := by
    have : (frobAut F ^ m) ((frobAut F ^ k) x) = (frobAut F ^ k) ((frobAut F ^ m) x) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm]
    rw [this]
    exact ⟨fun h => (frobAut F ^ k).injective h, fun h => by rw [h]⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(C.X.U_fr k x).mp h1, hfix.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(C.X.U_fr k x).mpr h1, hfix.mpr h2⟩

theorem OutCtx.W_le (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) :
    spWf (spT Φ ψ U) (spf ψ) ≤ centerOf (U.map Φ) := by
  rintro y ⟨hyZ, hyC⟩
  have hyT := (mem_centerOf_iff.mp hyZ).1
  obtain ⟨u, hu, s, rfl⟩ := (C.mem_spTf_iff hev).mp hyT
  have hrange : Φ u * psi2 ψ ^ s ∈ Φ.range := by
    have h1 : ⁅spTf (spT Φ ψ U) (spf ψ), spTf (spT Φ ψ U) (spf ψ)⁆ ≤ Φ.range := by
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      rw [commutatorElement_def]
      exact C.P.commutator_mem_range a b
    exact h1 hyC
  have hs : psi2 ψ ^ s = 1 := by
    have : psi2 ψ ^ s ∈ Φ.range := by
      obtain ⟨g, hg⟩ := hrange
      refine ⟨u⁻¹ * g, ?_⟩
      rw [map_mul, map_inv, hg]
      group
    exact (C.P.psi2_pow_mem_range_iff (by have := C.hm; omega) C.hF s).mp this
  rw [hs, mul_one] at hyZ ⊢
  obtain ⟨a, d, ha, hd, hafix, hdfix, hgen⟩ := C.X.gens
  have hcomm : ∀ t : antiSp F, t ∈ (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) →
      t * u = u * t := by
    intro t ht
    have hT : Φ t ∈ spTf (spT Φ ψ U) (spf ψ) :=
      (C.mem_spTf_iff hev).mpr ⟨t, ht, 0, by simp⟩
    have := (mem_centerOf_iff.mp hyZ).2 _ hT
    exact C.P.inj (by rw [map_mul, map_mul]; exact this)
  have hu0 : u ∈ centerOf U := by
    refine hgen u hu.1 ?_ ?_
    · exact (hcomm a ⟨ha, hafix m⟩).symm
    · exact (hcomm d ⟨hd, hdfix m⟩).symm
  rw [centerOf_map_of_injective Φ C.P.inj]
  exact Subgroup.mem_map_of_mem Φ hu0

theorem OutProps.index_range {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : Φ.range.index = orderOf ψ := by
  have h := Subgroup.card_mul_index Φ.range
  rw [P.card_eq hn hF, Nat.card_congr (MonoidHom.ofInjective P.inj).toEquiv.symm] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem twoPart_le_mul {G : Type u} [Group G] [Finite G] (M Inn : Subgroup G) [Inn.Normal]
    {a : ℕ} (ha : Inn.index.factorization 2 ≤ a) :
    twoPart M ≤ twoPart (M ⊓ Inn) * 2 ^ a := by
  obtain ⟨k, hk, hMk⟩ := exists_card_eq_inf_mul Inn M
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hMk
    exact Nat.card_pos.ne' hMk
  have hidx : Inn.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfk : k.factorization 2 ≤ a :=
    ((Nat.factorization_le_iff_dvd hk0 hidx).mpr hk 2).trans ha
  unfold twoPart
  rw [hMk, Nat.factorization_mul Nat.card_pos.ne' hk0, Finsupp.add_apply, pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hfk)

theorem twoPart_map_of_injective {G G' : Type*} [Group G] [Group G'] (Φ : G →* G')
    (hΦ : Function.Injective Φ) (V : Subgroup G) : twoPart (V.map Φ) = twoPart V := by
  unfold twoPart
  rw [Subgroup.card_map_of_injective hΦ]

theorem OutCtx.Sylow_Tf (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) (j : Fin 2) :
    IsSylowTwoOf (spTf (spT Φ ψ U) (spf ψ))
      (Subgroup.centralizer ({spf ψ} : Set H) ⊓ spN (N 0) (N 1) j) := by
  rw [OutCtx.spN_eq j]
  have hn1 : 1 ≤ 2 * m := by have := C.hm; omega
  set Tf := spTf (spT Φ ψ U) (spf ψ) with hTf
  set M := Subgroup.centralizer ({spf ψ} : Set H) ⊓ N j with hM
  have hle : Tf ≤ M := fun y hy => ⟨hy.2, C.T_le j hy.1⟩
  have hp : IsPGroup 2 Tf := C.sylow.2.1.to_le inf_le_left
  refine isSylowTwoOf_of_card_eq hle hp (le_antisymm (card_le_twoPart hle hp) ?_)
  have h1 : Nat.card (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) * 2 ^ twoExp ψ ≤
      Nat.card Tf := by
    rw [← C.P.card_spT hn1 C.hF (C.frobPow_U0)]
    refine Subgroup.card_le_of_le ?_
    intro y hy
    obtain ⟨u, hu, s, rfl⟩ := (C.P.mem_spT_iff C.frobPow_U0).mp hy
    exact (C.mem_spTf_iff hev).mpr ⟨u, hu, s, rfl⟩
  have h2 : twoPart M ≤ 2 ^ (4 * m) * 2 ^ twoExp ψ := by
    have h3 : twoPart M ≤ twoPart (M ⊓ Φ.range) * 2 ^ twoExp ψ := by
      have := C.P.range_normal
      refine twoPart_le_mul M Φ.range ?_
      rw [C.P.index_range hn1 C.hF]
      exact le_rfl
    refine h3.trans (Nat.mul_le_mul_right _ ?_)
    have h4 : M ⊓ Φ.range ≤ (fixedSubgroup (frobAut F ^ m)).map Φ := by
      rintro _ ⟨⟨hC, -⟩, x, rfl⟩
      refine ⟨x, ?_, rfl⟩
      have h5 := Subgroup.mem_centralizer_singleton_iff.mp hC
      show (frobAut F ^ m) x = x
      have := C.spf_conj hev x
      rw [← h5] at this
      exact (C.P.inj (mul_right_cancel this)).symm
    calc twoPart (M ⊓ Φ.range) ≤ twoPart ((fixedSubgroup (frobAut F ^ m)).map Φ) :=
          twoPart_mono h4
      _ = twoPart (fixedSubgroup (frobAut F ^ m)) := twoPart_map_of_injective Φ C.P.inj _
      _ = 2 ^ (4 * m) := C.X.fix_two
  calc twoPart M ≤ 2 ^ (4 * m) * 2 ^ twoExp ψ := h2
    _ ≤ Nat.card (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) * 2 ^ twoExp ψ :=
        Nat.mul_le_mul_right _ C.X.U0_ge
    _ ≤ Nat.card Tf := h1

theorem OutCtx.comap_le_U (C : OutCtx m Φ ψ k₀ U R i N) {B : Subgroup H}
    (hBT : B ≤ spT Φ ψ U) (hBr : B ≤ Φ.range) : B.comap Φ ≤ U := by
  intro x hx
  have h : Φ x ∈ spT Φ ψ U ⊓ Φ.range := ⟨hBT hx, hBr hx⟩
  rw [C.P.spT_inf_range (by have := C.hm; omega) C.hF C.X.U_fr] at h
  obtain ⟨u, hu, hux⟩ := h
  rwa [← C.P.inj hux]

omit [Finite H] in
theorem OutCtx.card_comap (C : OutCtx m Φ ψ k₀ U R i N) {B : Subgroup H} (hBr : B ≤ Φ.range) :
    Nat.card (B.comap Φ) = Nat.card B := by
  have hmap : (B.comap Φ).map Φ = B := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hBr
  conv_rhs => rw [← hmap]
  rw [Subgroup.card_map_of_injective C.P.inj]

omit [Finite H] in
theorem OutCtx.orderOf_le (C : OutCtx m Φ ψ k₀ U R i N) : orderOf ψ ≤ 2 * m := by
  have hn1 : 1 ≤ 2 * m := by have := C.hm; omega
  have : ψ ^ (2 * m) = 1 := by
    rw [C.P.pow_eq_one_iff, mul_comm, pow_mul, frobAut_pow_card C.hF, one_pow]
  exact Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one this)

theorem OutCtx.A_eq (C : OutCtx m Φ ψ k₀ U R i N) {A : Subgroup H} (hAT : A ≤ spT Φ ψ U)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcard : Nat.card A = Nat.card (spQ (N 0) (N 1) 0)) :
    A = spQ (N 0) (N 1) 0 ∨ A = spQ (N 0) (N 1) 1 := by
  have hn1 : 1 ≤ 2 * m := by have := C.hm; omega
  have hq4 : 4 ≤ Nat.card F := by
    rw [C.hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqpos : 0 < Nat.card F := by omega
  rw [C.spQ_eq 0, Subgroup.card_map_of_injective C.P.inj, C.X.card_R 0] at hcard
  rw [C.spQ_eq 0, C.spQ_eq 1]
  by_cases hA : A ≤ Φ.range
  ·
    have hA' : A.comap Φ ≤ U := C.comap_le_U hAT hA
    have hcA : Nat.card (A.comap Φ) = Nat.card F ^ 3 := by rw [C.card_comap hA, hcard]
    have hmapA : (A.comap Φ).map Φ = A := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hA
    have hab' : ∀ x ∈ A.comap Φ, ∀ y ∈ A.comap Φ, x * y = y * x := by
      intro x hx y hy
      have := hab _ hx _ hy
      exact C.P.inj (by rw [map_mul, map_mul]; exact this)
    by_cases hnon : ∃ x ∈ A.comap Φ, x * x ≠ 1
    · exfalso
      have h1 := C.X.noninv (A.comap Φ) hA' hab' hnon
      rw [hcA] at h1
      have h2 : Nat.card F ^ 2 * Nat.card F ≤ Nat.card F ^ 2 * 2 := by
        calc Nat.card F ^ 2 * Nat.card F = Nat.card F ^ 3 := by ring
          _ ≤ 2 * Nat.card F ^ 2 := h1
          _ = Nat.card F ^ 2 * 2 := by ring
      have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
      omega
    · push Not at hnon
      rcases C.X.elem_le (A.comap Φ) hA' hnon with h | h
      · left
        have heq : A.comap Φ = R 0 :=
          Subgroup.eq_of_le_of_card_ge h (by rw [hcA, C.X.card_R 0])
        rw [← hmapA, heq]
      · right
        have heq : A.comap Φ = R 1 :=
          Subgroup.eq_of_le_of_card_ge h (by rw [hcA, C.X.card_R 1])
        rw [← hmapA, heq]
  ·
    exfalso
    obtain ⟨y, hyA, hyR⟩ : ∃ y ∈ A, y ∉ Φ.range := by
      by_contra hcon
      push Not at hcon
      exact hA hcon
    obtain ⟨u₀, hu₀, s, rfl⟩ := (C.P.mem_spT_iff C.X.U_fr).mp (hAT hyA)
    have hs1 : psi2 ψ ^ s ≠ 1 := by
      intro h
      apply hyR
      rw [h, mul_one]
      exact ⟨u₀, rfl⟩
    have hω : frobAut F ^ (k₀ * (oddPart ψ * s)) ≠ 1 := by
      intro h
      apply hs1
      rw [psi2_pow_eq, C.P.pow_eq_one_iff]
      exact h
    set B : Subgroup H := A ⊓ Φ.range with hB
    have hBT : B ≤ spT Φ ψ U := inf_le_left.trans hAT
    have hBr : B ≤ Φ.range := inf_le_right
    have hfix : ∀ b ∈ B.comap Φ,
        u₀ * (frobAut F ^ (k₀ * (oddPart ψ * s))) b * u₀⁻¹ = b := by
      intro b hb
      have hbA : Φ b ∈ A := hb.1
      have h1 := hab _ hbA _ hyA
      have h2 := C.P.act_psi2_pow s b
      have h3 : psi2 ψ ^ s * Φ b = Φ ((frobAut F ^ (k₀ * (oddPart ψ * s))) b) * psi2 ψ ^ s :=
        mul_inv_eq_iff_eq_mul.mp h2
      have h4 : Φ (b * u₀) * psi2 ψ ^ s =
          Φ (u₀ * (frobAut F ^ (k₀ * (oddPart ψ * s))) b) * psi2 ψ ^ s := by
        calc Φ (b * u₀) * psi2 ψ ^ s = Φ b * (Φ u₀ * psi2 ψ ^ s) := by rw [map_mul, mul_assoc]
          _ = Φ u₀ * psi2 ψ ^ s * Φ b := h1
          _ = Φ u₀ * (psi2 ψ ^ s * Φ b) := mul_assoc _ _ _
          _ = Φ u₀ * (Φ ((frobAut F ^ (k₀ * (oddPart ψ * s))) b) * psi2 ψ ^ s) := by rw [h3]
          _ = Φ (u₀ * (frobAut F ^ (k₀ * (oddPart ψ * s))) b) * psi2 ψ ^ s := by
            rw [map_mul, mul_assoc]
      have h5 := C.P.inj (mul_right_cancel h4)
      rw [← h5]
      group
    have hbound := C.X.cent_bound _ hω u₀ hu₀ (B.comap Φ) (C.comap_le_U hBT hBr) hfix
    rw [C.card_comap hBr] at hbound
    have : Φ.range.Normal := C.P.range_normal
    obtain ⟨k, hk, hAk⟩ := exists_card_eq_inf_mul Φ.range A
    have hkle : k ≤ 2 * m := by
      rw [C.P.index_range hn1 C.hF] at hk
      exact (Nat.le_of_dvd (orderOf_pos ψ) hk).trans C.orderOf_le
    have h6 : Nat.card F ^ 3 ≤ Nat.card F ^ 2 * (2 * m) := by
      calc Nat.card F ^ 3 = Nat.card A := hcard.symm
        _ = Nat.card B * k := hAk
        _ ≤ Nat.card F ^ 2 * (2 * m) := Nat.mul_le_mul hbound hkle
    have h7 : Nat.card F ^ 2 * Nat.card F ≤ Nat.card F ^ 2 * (2 * m) := by
      calc Nat.card F ^ 2 * Nat.card F = Nat.card F ^ 3 := by ring
        _ ≤ _ := h6
    have h8 := Nat.le_of_mul_le_mul_left h7 (by positivity)
    have h9 : 2 * m < 2 ^ (2 * m) := Nat.lt_two_pow_self
    rw [← C.hF] at h9
    omega

theorem OutCtx.core (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) :
    F431SpOutCore (spT Φ ψ U) (U.map Φ) (spf ψ) (N 0) (N 1) (spI Φ i) where
  sylow := C.sylow
  T_le₁ := C.T_le 0
  T_le₂ := C.T_le 1
  Q_abel := by
    intro j x hx y hy
    rw [C.spQ_eq j] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul, C.hD.shape.Q_abel j a ha b hb]
  Q_card := by
    rw [C.spQ_eq 0, C.spQ_eq 1, Subgroup.card_map_of_injective C.P.inj,
      Subgroup.card_map_of_injective C.P.inj, C.X.card_R 0, C.X.card_R 1]
  A_eq := fun A hAT hab hcard => C.A_eq hAT hab hcard
  S_le := le_sup_left
  S_norm := by
    refine sup_le Subgroup.le_normalizer ?_
    exact C.P.zpowers_psi2_le_normalizer C.X.U_fr
  cyc := ⟨psi2 ψ, rfl⟩
  I_center := fun _ hx => C.I_center hx
  I_le_S := fun _ hx => C.I_le_S hx
  order_two := fun _ hx => C.order_two hx
  rep := fun _ hx hxo => C.rep hx hxo
  fusion := fun _ hx hxo => C.fusion hx hxo
  f_mem := Subgroup.mem_sup_right (spf_mem ψ)
  f_not := by
    rintro ⟨u, -, hu⟩
    exact C.P.spf_not_mem_range (by have := C.hm; omega) C.hF hev ⟨u, hu⟩
  f_sq := spf_sq hev
  f_not_central := C.f_not_central hev
  Z_sq := by
    intro j x hx
    rw [C.spZ_eq j] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← map_pow, C.hD.shape.Z_sq z (C.hD.Z_le j hz), map_one]
  Z_cls := fun j _ hx _ hy h => C.Z_cls j hx hy h
  W_le := C.W_le hev
  Sylow_Tf := fun j => C.Sylow_Tf hev j

theorem OutCtx.W_ne (C : OutCtx m Φ ψ k₀ U R i N) (hev : Even (orderOf ψ))
    (hcomm : ∀ k, i k ∈ ⁅(U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)),
      (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆) :
    ∃ j, ∃ x ∈ spWf (spT Φ ψ U) (spf ψ), x ∈ spZ (N 0) (N 1) j ∧ x ≠ 1 := by
  have hiU : ∀ k, i k ∈ (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)) := by
    intro k
    exact ⟨(mem_centerOf_iff.mp (C.hD.i_mem k)).1, C.X.i_fr m k⟩
  refine ⟨0, Φ (i 0), ⟨?_, ?_⟩, ?_, ?_⟩
  · refine mem_centerOf_iff.mpr ⟨(C.mem_spTf_iff hev).mpr ⟨i 0, hiU 0, 0, by simp⟩, ?_⟩
    intro t ht
    exact (mem_centerOf_iff.mp (C.I_center (mem_spI.mpr ⟨0, rfl⟩))).2 t ht.1
  · have h1 : ⁅(U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F)),
        (U ⊓ fixedSubgroup (frobAut F ^ m) : Subgroup (antiSp F))⁆.map Φ ≤
        ⁅spTf (spT Φ ψ U) (spf ψ), spTf (spT Φ ψ U) (spf ψ)⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_ <;>
      · rintro _ ⟨u, hu, rfl⟩
        exact (C.mem_spTf_iff hev).mpr ⟨u, hu, 0, by simp⟩
    exact h1 (Subgroup.mem_map_of_mem Φ (hcomm 0))
  · rw [C.spZ_eq 0]
    exact Subgroup.mem_map_of_mem Φ C.hD.i0
  · intro h
    exact C.hD.i_ne 0 (C.P.inj (by rw [h, map_one]))

end Ctx

end SpOut2

end CFSG.Quasithin.H13.F431
