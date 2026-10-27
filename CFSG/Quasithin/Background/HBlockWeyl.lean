module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InSL2
public import CFSG.Quasithin.Background.HA5Weyl
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H.BlkW

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 Matrix MatrixGroups
  CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.H.A5W

variable {G : Type} [Group G]

structure WeylData (K S : Subgroup G) (y w : G) : Prop where
  y_mem : y ∈ K
  y_norm : y ∈ Subgroup.normalizer (S : Set G)
  y_odd : Odd (orderOf y)
  y_three : 3 ≤ orderOf y
  w_mem : w ∈ K
  w_not : w ∉ Subgroup.normalizer (S : Set G)
  inv : ∀ j : ℕ, w * y ^ j * w⁻¹ * y ^ j ∈ pCoreOf 2 K

theorem exists_odd_pow [Finite G] (x : G) : ∃ k : ℕ, Odd (orderOf (x ^ 2 ^ k)) := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x) (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  rw [orderOf_pow' x (by positivity), hn, Nat.gcd_mul_right_left,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

section SL2

@[expose] def diagHom (F : Type) [Field F] : Fˣ →* SL(2, F) where
  toFun c := ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    show !![((1 : Fˣ) : F), 0; 0, (((1 : Fˣ)⁻¹ : Fˣ) : F)] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' c d := by
    apply Subtype.ext
    show !![((c * d : Fˣ) : F), 0; 0, (((c * d)⁻¹ : Fˣ) : F)] =
      !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] * !![(d : F), 0; 0, ((d⁻¹ : Fˣ) : F)]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem diagHom_val {F : Type} [Field F] (c : Fˣ) :
    (diagHom F c : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] := rfl

@[expose] def weylSL (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem weylSL_val {F : Type} [Field F] :
    (weylSL F : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem weylSL_conj_diag {F : Type} [Field F] (c : Fˣ) :
    weylSL F * diagHom F c * (weylSL F)⁻¹ = diagHom F c⁻¹ := by
  apply Subtype.ext
  show (weylSL F : Matrix (Fin 2) (Fin 2) F) * (diagHom F c : Matrix (Fin 2) (Fin 2) F) *
    (((weylSL F)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = (diagHom F c⁻¹ : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.coe_inv, weylSL_val, diagHom_val, diagHom_val,
    Matrix.adjugate_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagHom_injective {F : Type} [Field F] : Function.Injective (diagHom F) := by
  intro c d h
  have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [diagHom_val] at h1
  exact Units.ext (by simpa using h1)

end SL2

section Lin2

variable [Finite G]

theorem exists_weylData_lin2 {K S : Subgroup G} {n : ℕ} (hn : 1 < n) (h : IsLin2Type K n)
    (hS : IsSylowTwoOf S K) : ∃ y w : G, WeylData K S y w ∧ 2 ^ n - 1 ≤ orderOf y := by
  classical
  obtain ⟨F, hF, hFt, ⟨A⟩⟩ := Lin2.exists_adapted (by omega) h hS
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hoa : orderOf a = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_eq_fintype_card, Fintype.card_units,
      A.card_eq]
  have hodd_a : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Nat.odd_iff, pow_succ]
    omega
  obtain ⟨ℓ, hℓ⟩ := A.α_surj (diagHom F a)
  obtain ⟨ω, hω⟩ := A.α_surj (weylSL F)
  obtain ⟨k, hk⟩ := exists_odd_pow (ℓ : G)
  set ℓ' : ↥K := ℓ ^ 2 ^ k with hℓ'
  have hℓ'v : (ℓ' : G) = (ℓ : G) ^ 2 ^ k := by rw [hℓ', SubgroupClass.coe_pow]
  have hαℓ' : A.α ℓ' = diagHom F (a ^ 2 ^ k) := by rw [hℓ', map_pow, hℓ, map_pow]
  refine ⟨ℓ', ω, ⟨ℓ'.2, ?_, ?_, ?_, ω.2, ?_, ?_⟩, ?_⟩
  · rw [A.normalizer_iff ℓ', hαℓ', diagHom_val]
    rfl
  · rw [hℓ'v]
    exact hk
  · have h1 : orderOf (A.α ℓ') ∣ orderOf (ℓ' : G) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_map_dvd _ _
    have h2 : orderOf (A.α ℓ') = 2 ^ n - 1 := by
      rw [hαℓ', orderOf_injective _ diagHom_injective, orderOf_pow' a (by positivity), hoa,
        (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd_a)).gcd_eq_one, Nat.div_one]
    have h3 : 3 ≤ 2 ^ n - 1 := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    exact h3.trans (h2 ▸ Nat.le_of_dvd (orderOf_pos _) h1)
  · intro hN
    have h1 := (A.normalizer_iff ω).1 hN
    rw [hω] at h1
    simp [weylSL] at h1
  · intro j
    set x : ↥K := ω * ℓ' ^ j * ω⁻¹ * ℓ' ^ j with hx
    have hxv : (x : G) = (ω : G) * (ℓ' : G) ^ j * (ω : G)⁻¹ * (ℓ' : G) ^ j := by
      rw [hx]
      simp
    rw [← hxv, A.mem_pCoreOf_iff x, hx, map_mul, map_mul, map_mul, map_inv, map_pow, hω, hαℓ',
      ← map_pow, weylSL_conj_diag, ← map_mul, inv_mul_cancel, map_one]
  · have h1 : orderOf (A.α ℓ') ∣ orderOf (ℓ' : G) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_map_dvd _ _
    have h2 : orderOf (A.α ℓ') = 2 ^ n - 1 := by
      rw [hαℓ', orderOf_injective _ diagHom_injective, orderOf_pow' a (by positivity), hoa,
        (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd_a)).gcd_eq_one, Nat.div_one]
    exact h2 ▸ Nat.le_of_dvd (orderOf_pos _) h1

omit [Finite G] in
theorem mem_pCoreOf_of_comm_lin2 {K : Subgroup G} {n : ℕ} (h : IsLin2Type K n) {s : G}
    (hs : s ∈ K) (hc : ∀ u ∈ blockU K, s * u * s⁻¹ * u⁻¹ ∈ blockZ K) : s ∈ pCoreOf 2 K := by
  obtain ⟨F, hF, hFt, -, α, -, hαk, β, hβs, hβk, hβe⟩ := h
  have hsU : ∀ u ∈ blockU K, s * u * s⁻¹ ∈ blockU K := by
    intro u hu
    have h1 := hc u hu
    have h2 : s * u * s⁻¹ = (s * u * s⁻¹ * u⁻¹) * u := by group
    rw [h2]
    exact (blockU K).mul_mem ((inf_le_left : blockZ K ≤ blockU K) h1) hu
  have hfix : ∀ v : Fin 2 → F, (α ⟨s, hs⟩ : Matrix (Fin 2) (Fin 2) F).mulVec v = v := by
    intro v
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
    have hv := hβe ⟨s, hs⟩ u ⟨_, hsU u u.2⟩ rfl
    have hker : β ⟨_, hsU u u.2⟩ = β u := by
      have h1 : (⟨_, hsU u u.2⟩ : ↥(blockU K)) * u⁻¹ ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact hc u u.2
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    rw [hker, hu] at hv
    exact hv.symm
  have hα1 : α ⟨s, hs⟩ = 1 := by
    apply Subtype.ext
    ext i j
    have h2 : (α ⟨s, hs⟩ : Matrix (Fin 2) (Fin 2) F) i j = (Pi.single j (1 : F) : Fin 2 → F) i := by
      have := congrFun (hfix (Pi.single j 1)) i
      rwa [Matrix.mulVec_single_one] at this
    rw [h2]
    show (Pi.single j (1 : F) : Fin 2 → F) i = (1 : Matrix (Fin 2) (Fin 2) F) i j
    rw [Matrix.one_apply, Pi.single_apply]
  have hker : (⟨s, hs⟩ : ↥K) ∈ α.ker := hα1
  rw [hαk] at hker
  exact ⟨⟨s, hs⟩, by assumption, rfl⟩

omit [Finite G] in
theorem card_blockU_lin2 {K : Subgroup G} {n : ℕ} (h : IsLin2Type K n) :
    Nat.card (blockU K) = 4 ^ n * Nat.card (blockZ K) := by
  obtain ⟨F, hF, hFt, hcard, -, -, -, β, hβs, hβk, -⟩ := h
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rw [hβk] at h1
  have h2 : Nat.card ((blockZ K).subgroupOf (blockU K)) = Nat.card (blockZ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : Nat.card (Multiplicative (Fin 2 → F)) = 4 ^ n := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ _),
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hcard, ← pow_mul,
      mul_comm, pow_mul]
    norm_num
  rw [h2, h3] at h1
  rw [← h1, mul_comm]

theorem not_le_pCoreOf_lin2 {K S : Subgroup G} {n : ℕ} (hn : 0 < n) (h : IsLin2Type K n)
    (hS : IsSylowTwoOf S K) : ¬ S ≤ pCoreOf 2 K := by
  classical
  intro hle
  obtain ⟨F, hF, hFt, ⟨A⟩⟩ := Lin2.exists_adapted hn h hS
  obtain ⟨ℓ, hℓ⟩ := A.α_surj (slUpper (1 : F))
  have hℓS : (ℓ : G) ∈ S := (A.mem_P ℓ).2 (hℓ ▸ (mem_slUni).2 ⟨1, rfl⟩)
  have h1 := (A.mem_pCoreOf_iff ℓ).1 (hle hℓS)
  rw [hℓ] at h1
  have h2 := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  simp [slUpper_val] at h2

end Lin2

section Alt5

variable [Finite G]

omit [Finite G] in
theorem mem_normalizer_iff_of_surjective {X : Type*} [Group X] {K S : Subgroup G}
    (hSK : S ≤ K) (α : ↥K →* X) (hα : Function.Surjective α)
    (hker : ∀ k : ↥K, α k = 1 → (k : G) ∈ S) (ℓ : ↥K) :
    (ℓ : G) ∈ Subgroup.normalizer (S : Set G) ↔
      α ℓ ∈ Subgroup.normalizer ((S.subgroupOf K).map α : Set X) := by
  have hmem : ∀ k : ↥K, (k : G) ∈ S ↔ α k ∈ (S.subgroupOf K).map α := by
    intro k
    refine ⟨fun hk => ⟨k, hk, rfl⟩, ?_⟩
    rintro ⟨k', hk', he⟩
    have h1 : α (k'⁻¹ * k) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h2 := S.mul_mem (Subgroup.mem_subgroupOf.mp hk') (hker _ h1)
    simpa using h2
  have hconj : ∀ k : ↥K, α (ℓ * k * ℓ⁻¹) = α ℓ * α k * (α ℓ)⁻¹ := fun k => by
    rw [map_mul, map_mul, map_inv]
  constructor
  · intro hN
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain ⟨k, rfl⟩ := hα z
    rw [← hmem, ← hconj, ← hmem]
    exact Subgroup.mem_normalizer_iff.mp hN (k : G)
  · intro hN
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ K
    · have h1 := Subgroup.mem_normalizer_iff.mp hN (α ⟨g, hg⟩)
      rw [← hconj, ← hmem, ← hmem] at h1
      exact h1
    · have hg' : (ℓ : G) * g * (ℓ : G)⁻¹ ∉ K := by
        intro hh
        apply hg
        have := K.mul_mem (K.mul_mem (K.inv_mem ℓ.2) hh) ℓ.2
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd (hSK h) hg, fun h => absurd (hSK h) hg'⟩

omit [Finite G] in
theorem eq_one_of_odd_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      hodd.not_two_dvd_nat)).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk'))

theorem y5_mem_normalizer :
    (⟨y5, y5_alt⟩ : Alt5) ∈ Subgroup.normalizer (kleinStd : Set Alt5) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hy3 : (⟨y5, y5_alt⟩ : Alt5) ^ 3 = 1 := Subtype.ext y5_pow_three
  have hinv : (⟨y5, y5_alt⟩ : Alt5)⁻¹ = ⟨y5, y5_alt⟩ * ⟨y5, y5_alt⟩ := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_three', hy3]
  have hfwd : ∀ x : Alt5, x ∈ kleinStd → ⟨y5, y5_alt⟩ * x * ⟨y5, y5_alt⟩⁻¹ ∈ kleinStd :=
    fun x hx => y5_norm _ hx
  refine ⟨hfwd z, fun h => ?_⟩
  have h2 := hfwd _ (hfwd _ h)
  have e : (⟨y5, y5_alt⟩ : Alt5) * (⟨y5, y5_alt⟩ * (⟨y5, y5_alt⟩ * z * ⟨y5, y5_alt⟩⁻¹) *
      ⟨y5, y5_alt⟩⁻¹) * ⟨y5, y5_alt⟩⁻¹ = z := by
    have : (⟨y5, y5_alt⟩ : Alt5) * ⟨y5, y5_alt⟩ * ⟨y5, y5_alt⟩ = 1 := by rw [← pow_three', hy3]
    calc (⟨y5, y5_alt⟩ : Alt5) * (⟨y5, y5_alt⟩ * (⟨y5, y5_alt⟩ * z * ⟨y5, y5_alt⟩⁻¹) *
          ⟨y5, y5_alt⟩⁻¹) * ⟨y5, y5_alt⟩⁻¹
        = (⟨y5, y5_alt⟩ * ⟨y5, y5_alt⟩ * ⟨y5, y5_alt⟩) * z *
          (⟨y5, y5_alt⟩ * ⟨y5, y5_alt⟩ * ⟨y5, y5_alt⟩)⁻¹ := by group
      _ = z := by rw [this, one_mul, inv_one, mul_one]
  rwa [e] at h2

theorem w5_not_mem_normalizer :
    (⟨w5, w5_alt⟩ : Alt5) ∉ Subgroup.normalizer (kleinStd : Set Alt5) := by
  intro h
  obtain ⟨x, hx, hxw⟩ := w5_not_norm
  have hxA : x ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; exact kleinSet_alt x hx
  have h1 := (Subgroup.mem_normalizer_iff.mp h ⟨x, hxA⟩).mp hx
  exact hxw h1

theorem card_map_sylow_alt5 {K S : Subgroup G} (α : ↥K →* Alt5) (hαs : Function.Surjective α)
    (hS : IsSylowTwoOf S K) : Nat.card ((S.subgroupOf K).map α) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := RankOneRecog.isSylowTwoOf_iff_exists.mp hS
  have hPS : (P : Subgroup ↥K) = S.subgroupOf K := by
    rw [← hP]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hf : (Nat.card Alt5).factorization 2 = 2 := by
    rw [a5_card]; decide +kernel
  have h1 : Nat.card ((P : Subgroup ↥K).map α) = 2 ^ (Nat.card Alt5).factorization 2 :=
    Sylow.card_eq_multiplicity (Sylow.mapSurjective hαs P)
  rw [hPS, hf] at h1
  rw [h1]
  norm_num

theorem exists_weylData_alt5 {K S : Subgroup G} (h : IsAltType K 5) (hS : IsSylowTwoOf S K) :
    ∃ y w : G, WeylData K S y w ∧ orderOf y = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hαs, hαk, -⟩ := h
  have hSK : S ≤ K := hS.1
  have hpK : ∀ k : ↥K, α k = 1 → (k : G) ∈ pCoreOf 2 K := fun k hk => by
    have h1 : k ∈ α.ker := hk
    rw [hαk] at h1
    exact ⟨k, by assumption, rfl⟩
  have hker : ∀ k : ↥K, α k = 1 → (k : G) ∈ S := fun k hk => hS.pCoreOf_le (hpK k hk)
  set Q : Subgroup Alt5 := (S.subgroupOf K).map α with hQ
  have hQ4 : Nat.card Q = 4 := card_map_sylow_alt5 α hαs hS
  obtain ⟨g, hg⟩ := exists_conj_kleinStd Q hQ4
  set y₀ : Alt5 := g * ⟨y5, y5_alt⟩ * g⁻¹ with hy₀
  set w₀ : Alt5 := g * ⟨w5, w5_alt⟩ * g⁻¹ with hw₀
  have hNQ : ∀ σ : Alt5, g * σ * g⁻¹ ∈ Subgroup.normalizer (Q : Set Alt5) ↔
      σ ∈ Subgroup.normalizer (kleinStd : Set Alt5) := by
    intro σ
    simp only [Subgroup.mem_normalizer_iff, hg]
    constructor
    · intro h z
      have := h (g * z * g⁻¹)
      have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      have e2 : g⁻¹ * (g * σ * g⁻¹ * (g * z * g⁻¹) * (g * σ * g⁻¹)⁻¹) * g = σ * z * σ⁻¹ := by
        group
      rwa [e1, e2] at this
    · intro h z
      have := h (g⁻¹ * z * g)
      have e2 : g⁻¹ * (g * σ * g⁻¹ * z * (g * σ * g⁻¹)⁻¹) * g = σ * (g⁻¹ * z * g) * σ⁻¹ := by
        group
      rwa [e2]
  have hy₀N : y₀ ∈ Subgroup.normalizer (Q : Set Alt5) := (hNQ _).2 y5_mem_normalizer
  have hw₀N : w₀ ∉ Subgroup.normalizer (Q : Set Alt5) := fun h =>
    w5_not_mem_normalizer ((hNQ _).1 h)
  have hy₀3 : y₀ ^ 3 = 1 := by
    rw [hy₀, conj_pow, show (⟨y5, y5_alt⟩ : Alt5) ^ 3 = 1 from Subtype.ext y5_pow_three, mul_one,
      mul_inv_cancel]
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    apply y5_ne_one
    have : (⟨y5, y5_alt⟩ : Alt5) = 1 := by
      have e : (⟨y5, y5_alt⟩ : Alt5) = g⁻¹ * y₀ * g := by rw [hy₀]; group
      rw [e, h1, mul_one, inv_mul_cancel]
    exact congrArg Subtype.val this
  have hw₀y₀ : w₀ * y₀ * w₀⁻¹ = y₀⁻¹ := by
    have h1 : (⟨w5, w5_alt⟩ : Alt5) * ⟨y5, y5_alt⟩ * (⟨w5, w5_alt⟩ : Alt5)⁻¹ =
        (⟨y5, y5_alt⟩ : Alt5)⁻¹ := Subtype.ext w5_inv
    calc w₀ * y₀ * w₀⁻¹ = g * ((⟨w5, w5_alt⟩ : Alt5) * ⟨y5, y5_alt⟩ *
          (⟨w5, w5_alt⟩ : Alt5)⁻¹) * g⁻¹ := by rw [hw₀, hy₀]; group
      _ = y₀⁻¹ := by rw [h1, hy₀]; group
  obtain ⟨ℓ, hℓ⟩ := hαs y₀
  obtain ⟨ω, hω⟩ := hαs w₀
  obtain ⟨k, hk⟩ := exists_odd_pow (ℓ : G)
  set ℓ' : ↥K := ℓ ^ 2 ^ k with hℓ'
  have hℓ'v : (ℓ' : G) = (ℓ : G) ^ 2 ^ k := by rw [hℓ', SubgroupClass.coe_pow]
  have hαℓ' : α ℓ' = y₀ ^ 2 ^ k := by rw [hℓ', map_pow, hℓ]
  have hodd' : Odd (orderOf (ℓ' : G)) := hℓ'v ▸ hk
  have hcop3 : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hord : orderOf (ℓ' : G) = 3 := by
    have h3 : (ℓ' : G) ^ 3 = 1 := by
      have hα3 : α (ℓ' ^ 3) = 1 := by
        rw [map_pow, hαℓ', ← pow_mul, mul_comm, pow_mul, hy₀3, one_pow]
      have hmem := hpK _ hα3
      rw [SubgroupClass.coe_pow] at hmem
      exact eq_one_of_odd_of_mem (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hmem
        (Odd.of_dvd_nat hodd' (orderOf_pow_dvd 3))
    have hne : (ℓ' : G) ≠ 1 := by
      intro h1
      have hα1 : α ℓ' = 1 := by
        have : ℓ' = 1 := Subtype.ext h1
        rw [this, map_one]
      rw [hαℓ'] at hα1
      apply hy₀1
      have : y₀ ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hα1, hy₀3⟩
      rwa [hcop3.gcd_eq_one, pow_one] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have e : ∀ m : ℕ, w₀ * y₀ ^ m * w₀⁻¹ * y₀ ^ m = 1 := fun m => by
    rw [← conj_pow, hw₀y₀, inv_pow, inv_mul_cancel]
  refine ⟨ℓ', ω, ⟨ℓ'.2, ?_, hodd', hord.symm ▸ le_rfl, ω.2, ?_, ?_⟩, hord⟩
  · rw [mem_normalizer_iff_of_surjective hSK α hαs hker ℓ', hαℓ']
    exact Subgroup.pow_mem _ hy₀N _
  · intro hN
    rw [mem_normalizer_iff_of_surjective hSK α hαs hker ω, hω] at hN
    exact hw₀N hN
  · intro j
    set x : ↥K := ω * ℓ' ^ j * ω⁻¹ * ℓ' ^ j with hx
    have hxv : (x : G) = (ω : G) * (ℓ' : G) ^ j * (ω : G)⁻¹ * (ℓ' : G) ^ j := by
      rw [hx]
      simp
    rw [← hxv]
    apply hpK
    rw [hx, map_mul, map_mul, map_mul, map_inv, map_pow, hω, hαℓ', ← pow_mul]
    exact e _

omit [Finite G] in
theorem mem_pCoreOf_of_comm_alt5 {K : Subgroup G} (h : IsAltType K 5) {s : G}
    (hs : s ∈ K) (hc : ∀ u ∈ blockU K, s * u * s⁻¹ * u⁻¹ ∈ blockZ K) : s ∈ pCoreOf 2 K := by
  obtain ⟨α, -, hαk, β, hβs, hβk, hβe⟩ := h
  have hsU : ∀ u ∈ blockU K, s * u * s⁻¹ ∈ blockU K := by
    intro u hu
    have h1 := hc u hu
    have h2 : s * u * s⁻¹ = (s * u * s⁻¹ * u⁻¹) * u := by group
    rw [h2]
    exact (blockU K).mul_mem ((inf_le_left : blockZ K ≤ blockU K) h1) hu
  have hfix : ∀ x : Fin 5 → ZMod 2, isEven x → pact (α ⟨s, hs⟩ : Equiv.Perm (Fin 5)) x = x := by
    intro x hx
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd ⟨x, hx⟩)
    have hv := hβe ⟨s, hs⟩ u ⟨_, hsU u u.2⟩ rfl
    have hker : β ⟨_, hsU u u.2⟩ = β u := by
      have h1 : (⟨_, hsU u u.2⟩ : ↥(blockU K)) * u⁻¹ ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact hc u u.2
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    funext i
    have := hv i
    rw [hker, hu] at this
    exact this.symm
  have hα1 : α ⟨s, hs⟩ = 1 := Subtype.ext (pact_faithful _ hfix)
  have hker : (⟨s, hs⟩ : ↥K) ∈ α.ker := hα1
  rw [hαk] at hker
  exact ⟨⟨s, hs⟩, by assumption, rfl⟩

omit [Finite G] in
theorem card_blockU_alt5 {K : Subgroup G} (h : IsAltType K 5) :
    Nat.card (blockU K) = 16 * Nat.card (blockZ K) := by
  obtain ⟨-, -, -, β, hβs, hβk, -⟩ := h
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rw [hβk] at h1
  have h2 : Nat.card ((blockZ K).subgroupOf (blockU K)) = Nat.card (blockZ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : Nat.card (Multiplicative (evenWeight 5)) = 16 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ _),
      card_evenWeight5]
  rw [h2, h3] at h1
  rw [← h1, mul_comm]

theorem not_le_pCoreOf_alt5 {K S : Subgroup G} (h : IsAltType K 5) (hS : IsSylowTwoOf S K) :
    ¬ S ≤ pCoreOf 2 K := by
  intro hle
  obtain ⟨α, hαs, hαk, -⟩ := h
  have h4 := card_map_sylow_alt5 α hαs hS
  have hbot : (S.subgroupOf K).map α = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : (k : G) ∈ pCoreOf 2 K := hle (Subgroup.mem_subgroupOf.mp hk)
    obtain ⟨k', hk', hkk'⟩ := h1
    have e : k' = k := Subtype.ext hkk'
    subst e
    have : k' ∈ α.ker := by rw [hαk]; assumption
    exact this
  rw [hbot, Subgroup.card_bot] at h4
  omega

end Alt5

end CFSG.Quasithin.H.BlkW
