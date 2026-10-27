module

public import CFSG.GH74.GLS.IVK.L2.BorelMatrices
public import CFSG.CharacterTheory.PSL2Table.Tori
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.L21521

open CFSG.PSL2Table CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups Pointwise

variable {K : Type} [Field K]

theorem mk_unip_eq_mk_unip_iff' (s t : K) : mk (unip s) = mk (unip t) ↔ s = t := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro (h | h)
    · have h01 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simpa using h01.symm
    · have h00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
      have h01 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp only [coe_unip, neg_apply_SL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01
      linear_combination (-1 : K) * h01 + s * h00
  · rintro rfl
    exact Or.inl rfl

noncomputable def unipHom (K : Type) [Field K] : Multiplicative K →* PSL(2, K) where
  toFun t := mk (unip (Multiplicative.toAdd t))
  map_one' := by simp [unip_zero]
  map_mul' s t := by simp [unip_add]

theorem unipHom_injective : Function.Injective (unipHom K) := fun _ _ h =>
  Multiplicative.toAdd.injective ((mk_unip_eq_mk_unip_iff' _ _).mp h)

theorem range_unipHom : (unipHom K).range = unipotent K := by
  ext x
  rw [MonoidHom.mem_range, mem_unipotent_iff_exists]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem card_unipotent' : Nat.card (unipotent K) = Nat.card K := by
  rw [← range_unipHom]
  exact (Nat.card_congr (MonoidHom.ofInjective (unipHom_injective (K := K))).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)


theorem exists_unit_sq_ne_one [Finite K] (h2 : (2 : K) = 0) (h4 : 4 ≤ Nat.card K) :
    ∃ a : Kˣ, (a : K) ^ 2 ≠ 1 := by
  have hcard : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a, ha⟩ := exists_ne (1 : Kˣ)
  refine ⟨a, fun h => ha ?_⟩
  have h1 : ((a : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (a : K)) * h2
  have h3 : (a : K) - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  exact Units.ext (sub_eq_zero.mp h3)

theorem diag_pow (a : Kˣ) (m : ℕ) : diag (a ^ m) = (diag a) ^ m := by
  induction m with
  | zero => simp [diag_one]
  | succ m ih => rw [pow_succ, diag_mul, ih, pow_succ]

theorem odd_orderOf_mk_diag (hodd : Odd (Nat.card Kˣ)) (a : Kˣ) : Odd (orderOf (mk (diag a))) := by
  have h1 : (mk (diag a)) ^ Nat.card Kˣ = 1 := by
    rw [← map_pow, ← diag_pow, pow_card_eq_one', diag_one, map_one]
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem mk_diag_conj_mem (a : Kˣ) {x : PSL(2, K)} (hx : x ∈ unipotent K) :
    mk (diag a) * x * (mk (diag a))⁻¹ ∈ unipotent K := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  rw [← map_inv, ← map_mul, ← map_mul, diag_conj_unip]
  exact mk_unip_mem_unipotent _

theorem mk_diag_mem_normalizer (a : Kˣ) :
    mk (diag a) ∈ Subgroup.normalizer (unipotent K : Set PSL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨mk_diag_conj_mem a, fun hx => ?_⟩
  have h := mk_diag_conj_mem a⁻¹ hx
  have hinv : mk (diag a⁻¹) = (mk (diag a))⁻¹ := by rw [← diag_inv, map_inv]
  rw [hinv] at h
  simpa [mul_assoc] using h

theorem mk_unip_mem_normalizer (s : K) :
    mk (unip s) ∈ Subgroup.normalizer (unipotent K : Set PSL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hc : ∀ y ∈ unipotent K, mk (unip s) * y * (mk (unip s))⁻¹ = y := fun y hy => by
    rw [unipotent_mul_comm (mk_unip_mem_unipotent s) hy]
    group
  constructor
  · intro hx
    rw [hc x hx]
    exact hx
  · intro hx
    have hu : mk (unip s) ∈ unipotent K := mk_unip_mem_unipotent s
    have := (unipotent K).mul_mem ((unipotent K).mul_mem ((unipotent K).inv_mem hu) hx) hu
    simpa [mul_assoc] using this

theorem odd_two_pow_sub_one' {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h2 : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one

theorem card_psl2_char_two [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card PSL(2, K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have h := CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num)
  rw [hK] at h
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one' hn)
  rw [h, hg, Nat.div_one]
  simp

theorem factorization_card_psl2 [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    (Nat.card PSL(2, K)).factorization 2 = n := by
  rw [card_psl2_char_two hn hK]
  have hpos : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 ^ n) ^ 2 := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      nlinarith
    omega
  rw [Nat.factorization_mul (by positivity) hpos, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have h2 : Even ((2 ^ n) ^ 2) :=
      (Nat.even_pow' (by norm_num)).mpr ((Nat.even_pow' (by omega)).mpr even_two)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) h2 odd_one
  have hnd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := fun h => by
    have := Nat.odd_iff.mp hodd
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hnd]
  rfl

theorem psl2FieldAut_mk_unip' (σ : K ≃+* K) (t : K) :
    psl2FieldAut K σ (mk (unip t)) = mk (unip (σ t)) := by
  have h : Matrix.SpecialLinearGroup.map σ.toRingHom (unip t) = unip (σ t) := by
    apply SL_ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (unip t)) =
    QuotientGroup.mk' (Subgroup.center _) (unip (σ t))
  rw [psl2RingEquiv_mk, h]

theorem exists_eq_conj_of_forall_unipotent' [Finite K] (α : MulAut PSL(2, K))
    (hα : ∀ u ∈ unipotent K, α u = u) : ∃ u ∈ unipotent K, α = MulAut.conj u := by
  obtain ⟨x, rfl⟩ := (semilinearEquivAut K).surjective α
  have hx : semilinearEquivAut K x = pglAction K x.left * psl2FieldAut K x.right := by
    change semilinearAction K x = _
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  rw [hx] at hα ⊢
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL (hα _ (mk_unip_mem_unipotent 1))
  rw [MulAut.mul_apply, psl2FieldAut_mk_unip', map_one, toPGL_pglAction] at h1
  obtain ⟨c, hc⟩ := GH74.GLS.IVK.L2Borel.exists_eq_toPGL_of_commute one_ne_zero
    (mul_inv_eq_iff_eq_mul.mp h1)
  have hg : pglAction K x.left = MulAut.conj (mk (unip c)) := by rw [hc, pglAction_toPGL]
  have hσ : x.right = 1 := by
    ext t
    have ht := hα _ (mk_unip_mem_unipotent t)
    rw [MulAut.mul_apply, psl2FieldAut_mk_unip', hg, MulAut.conj_apply,
      unipotent_mul_comm (mk_unip_mem_unipotent c) (mk_unip_mem_unipotent _),
      mul_inv_cancel_right, mk_unip_eq_mk_unip_iff'] at ht
    exact ht
  refine ⟨mk (unip c), mk_unip_mem_unipotent c, ?_⟩
  rw [hg, hσ, map_one, mul_one]


theorem unip_mul_diag_mul_unip_inv (a : Kˣ) (c : K) :
    unip c * diag a * (unip c)⁻¹ = diag a * unip (((a⁻¹ : Kˣ) : K) ^ 2 * c - c) := by
  rw [unip_neg]
  apply SL_ext <;> simp [mul_apply_SL]
  field_simp
  ring

theorem eq_one_of_forall_unipotent_diag [Finite K] {a : Kˣ} (ha : (a : K) ^ 2 ≠ 1)
    (α : MulAut PSL(2, K)) (hu : ∀ u ∈ unipotent K, α u = u)
    (hd : α (mk (diag a)) = mk (diag a)) : α = 1 := by
  obtain ⟨u, hu', rfl⟩ := exists_eq_conj_of_forall_unipotent' α hu
  obtain ⟨c, rfl⟩ := (mem_unipotent_iff_exists u).mp hu'
  rw [MulAut.conj_apply] at hd
  have key : mk (unip c) * mk (diag a) * (mk (unip c))⁻¹ =
      mk (diag a) * mk (unip (((a⁻¹ : Kˣ) : K) ^ 2 * c - c)) := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, unip_mul_diag_mul_unip_inv]
  rw [key] at hd
  have h2 : mk (unip (((a⁻¹ : Kˣ) : K) ^ 2 * c - c)) = 1 := by
    have := mul_left_cancel (a := mk (diag a)) (hd.trans (mul_one _).symm)
    exact this
  have h3 : ((a⁻¹ : Kˣ) : K) ^ 2 * c - c = 0 :=
    (mk_unip_eq_mk_unip_iff' _ 0).mp (by rw [h2, unip_zero, map_one])
  have ha' : ((a⁻¹ : Kˣ) : K) ^ 2 - 1 ≠ 0 := by
    intro h
    apply ha
    have h1 : ((a⁻¹ : Kˣ) : K) ^ 2 = 1 := sub_eq_zero.mp h
    have hinv : ((a⁻¹ : Kˣ) : K) = (a : K)⁻¹ := by simp
    rw [hinv, inv_pow, inv_eq_one] at h1
    exact h1
  have hc : c = 0 := by
    have : (((a⁻¹ : Kˣ) : K) ^ 2 - 1) * c = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left ha'
  subst hc
  rw [unip_zero, map_one]
  exact map_one _


theorem unip_eq_diag_mul (a : Kˣ) (ha : (a : K) ^ 2 ≠ 1) (t : K) :
    unip t = diag a * (unip (t / ((a : K) ^ 2 - 1)) * (diag a)⁻¹ *
      (unip (t / ((a : K) ^ 2 - 1)))⁻¹) := by
  have hne : (a : K) ^ 2 - 1 ≠ 0 := fun h => ha (sub_eq_zero.mp h)
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  rw [unip_neg, diag_inv]
  apply SL_ext <;> simp [mul_apply_SL]
  field_simp
  ring


theorem eq_one_of_fixes_odd_normalizer [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (Q : Sylow 2 PSL(2, K)) (β : MulAut PSL(2, K))
    (hβ : ∀ z ∈ Subgroup.normalizer ((Q : Subgroup PSL(2, K)) : Set PSL(2, K)),
      Odd (orderOf z) → β z = z) : β = 1 := by
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨a, ha⟩ := exists_unit_sq_ne_one h2 h4
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact odd_two_pow_sub_one' (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U₀ : Sylow 2 PSL(2, K) := Sylow.ofCard (unipotent K) (by
    rw [card_unipotent', hK, factorization_card_psl2 (by omega) hK])
  have hU₀ : (U₀ : Subgroup PSL(2, K)) = unipotent K := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, K) U₀ Q
  have hmem : ∀ x, x ∈ (Q : Subgroup PSL(2, K)) ↔ g⁻¹ * x * g ∈ unipotent K := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * (g * y * g⁻¹) * g ∈ _
      simpa [mul_assoc] using hy
    · intro h
      refine ⟨g⁻¹ * x * g, h, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  set β' : MulAut PSL(2, K) := (MulAut.conj g)⁻¹ * β * MulAut.conj g with hβ'
  have hfix : ∀ z ∈ Subgroup.normalizer (unipotent K : Set PSL(2, K)), Odd (orderOf z) →
      β' z = z := by
    intro z hz hzo
    have hzN : g * z * g⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup PSL(2, K)) : Set PSL(2, K)) := by
      rw [Subgroup.mem_normalizer_iff] at hz ⊢
      intro x
      rw [hmem x, hmem (g * z * g⁻¹ * x * (g * z * g⁻¹)⁻¹)]
      have e : g⁻¹ * (g * z * g⁻¹ * x * (g * z * g⁻¹)⁻¹) * g = z * (g⁻¹ * x * g) * z⁻¹ := by
        group
      rw [e]
      exact hz _
    have hord : Odd (orderOf (g * z * g⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hzo
    have h1 := hβ _ hzN hord
    have e1 : β' z = (MulAut.conj g)⁻¹ (β (MulAut.conj g z)) := rfl
    rw [e1, MulAut.conj_apply, h1]
    simp [MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc]
  have hdiag : β' (mk (diag a)) = mk (diag a) :=
    hfix _ (mk_diag_mem_normalizer a) (odd_orderOf_mk_diag hodd a)
  have hunip : ∀ u ∈ unipotent K, β' u = u := by
    intro u hu
    obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists u).mp hu
    set s : K := t / ((a : K) ^ 2 - 1) with hs
    have hdec : mk (unip t) = mk (diag a) *
        (mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹) := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← unip_eq_diag_mul a ha t]
    have hy : β' (mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹) =
        mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹ := by
      refine hfix _ ?_ ?_
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mk_unip_mem_normalizer s)
          (Subgroup.inv_mem _ (mk_diag_mem_normalizer a)))
          (Subgroup.inv_mem _ (mk_unip_mem_normalizer s))
      · have : mk (unip s) * (mk (diag a))⁻¹ * (mk (unip s))⁻¹ =
            (MulAut.conj (mk (unip s))) (mk (diag a))⁻¹ := by
          rw [MulAut.conj_apply]
        rw [this, MulEquiv.orderOf_eq, orderOf_inv]
        exact odd_orderOf_mk_diag hodd a
    rw [hdec, map_mul, hdiag, hy]
  have hone : β' = 1 :=
    eq_one_of_forall_unipotent_diag ha β' hunip hdiag
  calc β = MulAut.conj g * β' * (MulAut.conj g)⁻¹ := by rw [hβ']; group
    _ = 1 := by rw [hone]; group


theorem centralizes_of_centralizes_borel_psl2 {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    {n : ℕ} (hn : 2 ≤ n) (hL : IsPSL 2 2 n ↥L) (hP : CFSG.QuasithinUnique.IsSylowTwoOf P L)
    {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) :
    ∀ l ∈ L, v * l = l * v := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  let φ : ↥L ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 PSL(2, K) := (A4.toSylow hP).mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hQ : (Q : Subgroup PSL(2, K)) = (P.subgroupOf L).map φ.toMonoidHom := rfl
  let α : MulAut ↥L := conjAct L ⟨v, hv⟩
  let β : MulAut PSL(2, K) := MulAut.congr φ α
  have hβ : ∀ z ∈ Subgroup.normalizer ((Q : Subgroup PSL(2, K)) : Set PSL(2, K)),
      Odd (orderOf z) → β z = z := by
    intro z hz hzo
    set z' : ↥L := φ.symm z with hz'
    have hzz' : φ z' = z := by simp [hz']
    have hz'N : ∀ x : ↥L, x ∈ P.subgroupOf L ↔ z' * x * z'⁻¹ ∈ P.subgroupOf L := by
      intro x
      have h := Subgroup.mem_normalizer_iff.mp hz (φ x)
      rw [hQ, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h
      simpa [hz', map_mul, map_inv] using h
    have hz'G : (z' : G) ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have hgL : g ∈ L := hP.1 hg
        have := (hz'N ⟨g, hgL⟩).mp hg
        simpa [Subgroup.mem_subgroupOf] using this
      · intro hg
        have hgL : (z' : G) * g * (z' : G)⁻¹ ∈ L := hP.1 hg
        have hgL' : g ∈ L := by
          have h1 : (z' : G)⁻¹ * ((z' : G) * g * (z' : G)⁻¹) * (z' : G) ∈ L :=
            L.mul_mem (L.mul_mem (L.inv_mem z'.2) hgL) z'.2
          simpa [mul_assoc] using h1
        exact (Subgroup.mem_subgroupOf.mp ((hz'N ⟨g, hgL'⟩).mpr (by
          simpa [Subgroup.mem_subgroupOf] using hg)))
    have hzo' : Odd (orderOf (z' : G)) := by
      rw [Subgroup.orderOf_coe, hz', MulEquiv.orderOf_eq]
      exact hzo
    have hmem : (z' : G) ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)) :=
      mem_oTwoUpper_of_odd ⟨z'.2, hz'G⟩ hzo'
    have hcomm := hc _ hmem
    have hαz : α z' = z' := by
      apply Subtype.ext
      change v * (z' : G) * v⁻¹ = (z' : G)
      rw [hcomm]
      group
    change φ (α (φ.symm z)) = z
    rw [← hz', hαz, hzz']
  have hβ1 : β = 1 := eq_one_of_fixes_odd_normalizer hn hK Q β hβ
  intro l hl
  have h1 : α ⟨l, hl⟩ = ⟨l, hl⟩ := by
    have := congrArg (fun γ : MulAut PSL(2, K) => φ.symm (γ (φ ⟨l, hl⟩))) hβ1
    simpa [β, MulAut.congr] using this
  have h2 := congrArg (fun x : ↥L => (x : G)) h1
  have h3 : v * l * v⁻¹ = l := h2
  calc v * l = (v * l * v⁻¹) * v := by group
    _ = l * v := by rw [h3]

end CFSG.Quasithin.L21521
