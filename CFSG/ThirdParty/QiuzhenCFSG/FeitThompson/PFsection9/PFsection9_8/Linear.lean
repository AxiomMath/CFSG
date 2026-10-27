module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.Reducible

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

@[expose] public def H0CLinearCandidateXmuDmuData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
    let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    ∃ θ : ι → Section1.ClassFunction Dm,
      ∃ ψ : ι → Section1.ClassFunction HCm,
        Function.Injective θ ∧
          u * Fintype.card ι = (p - 1) ^ q ∧
          (∀ i : ι,
            Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
              ¬ Section1.subgroupInKernel' (θ i) MFD ∧
              Section1.subgroupInKernel' (θ i) H0CD ∧
              Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
              Section1.degree (ψ i) = (1 : ℂ) ∧
              θ i =
                Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))) ∧
          ∃ Xmu : Finset ι,
            Xmu.card = p - 1 ∧
              (∀ i : ι, i ∈ Xmu →
                Section1.inducedCF Dm (θ i) ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
              (∀ χ : Section1.ClassFunction M,
                χ ∈ reducibleCharacterFilter_sec9 M SH0C →
                  ∃ i : ι, i ∈ Xmu ∧ χ = Section1.inducedCF Dm (θ i)) ∧
              ∀ i : ι, i ∈ Xmu →
                ∀ j : ι, j ∉ Xmu →
                  Section1.inducedCF Dm (θ i) ≠ Section1.inducedCF Dm (θ j)

@[expose] public def H0CLinearCandidateXmuResidualData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ μ : Type u, ∃ instFintype : Fintype μ, ∃ instDecidableEq : DecidableEq μ,
    letI : Fintype μ := instFintype
    letI : DecidableEq μ := instDecidableEq
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let hDnormal : Dm.Normal := by
      simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
    letI : Dm.Normal := hDnormal
    let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
    let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    ∃ θ : μ → Section1.ClassFunction Dm,
      Fintype.card μ = p - 1 ∧
        Function.Injective (fun i : μ => Section1.inducedCF Dm (θ i)) ∧
          (∀ i : μ,
            Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
              ¬ Section1.subgroupInKernel' (θ i) MFD ∧
              Section1.subgroupInKernel' (θ i) H0CD ∧
              Section1.inertiaSubgroup Dm (θ i) = ⊤ ∧
              Section1.inducedCF Dm (θ i) ∈
                reducibleCharacterFilter_sec9 M SH0C) ∧
          ∀ χ : Section1.ClassFunction M,
            χ ∈ reducibleCharacterFilter_sec9 M SH0C →
              ∃ i : μ, χ = Section1.inducedCF Dm (θ i)

@[expose] public def H0CLinearCandidateXmuFinalImageData_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  ∃ Xmu : Finset ι,
    Xmu.card = p - 1 ∧
      (∀ i : ι, i ∈ Xmu →
        Section1.inducedCF Dm (θ i) ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
      (∀ χ : Section1.ClassFunction M,
        χ ∈ reducibleCharacterFilter_sec9 M SH0C →
          ∃ i : ι, i ∈ Xmu ∧ χ = Section1.inducedCF Dm (θ i)) ∧
      ∀ i : ι, i ∈ Xmu →
        ∀ j : ι, j ∉ Xmu →
          Section1.inducedCF Dm (θ i) ≠ Section1.inducedCF Dm (θ j)


public theorem quotientBarUCardinality_pos_sec9
    {G : Type u} [Group G] [Finite G]
    (U C : Subgroup G) (u : ℕ) :
    quotientBarUCardinality U C u →
      0 < u := by
  intro hBarU
  rcases hBarU with ⟨_hCU, hnormal, hcard⟩
  letI : (C.subgroupOf U).Normal := hnormal
  rw [← hcard]
  exact Nat.card_pos

public theorem card_eq_div_of_left_mul_card_eq_sec9
    {u n m : ℕ} :
    0 < u →
      u * n = m →
        n = m / u := by
  intro hu hmul
  rw [← hmul]
  exact (Nat.mul_div_right n hu).symm

public theorem card_eq_mul_card_of_fiber_card_sec9
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (n : ℕ)
    (hfiber : ∀ b : β, Fintype.card {a : α // f a = b} = n) :
    Fintype.card α = n * Fintype.card β := by
  classical
  let e : α ≃ Σ b : β, {a : α // f a = b} :=
    { toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := by
        intro a
        rfl
      right_inv := by
        intro p
        rcases p with ⟨b, a, ha⟩
        dsimp at ha ⊢
        subst ha
        rfl }
  calc
    Fintype.card α = Fintype.card (Σ b : β, {a : α // f a = b}) :=
      Fintype.card_congr e
    _ = ∑ b : β, Fintype.card {a : α // f a = b} := Fintype.card_sigma
    _ = ∑ _b : β, n := by simp [hfiber]
    _ = n * Fintype.card β := by simp [Nat.mul_comm]

public theorem freeAction_orbitQuotient_fiber_natCard_sec9
    {A : Type u} {κ : Type v} [Group A] [Finite A] [MulAction A κ] [Finite κ]
    (hstab : ∀ x : κ, MulAction.stabilizer A x = ⊥) :
    ∀ q : Quotient (MulAction.orbitRel A κ),
      Nat.card {x : κ // (Quotient.mk'' x : Quotient (MulAction.orbitRel A κ)) = q} =
        Nat.card A := by
  classical
  intro q
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype κ := Fintype.ofFinite κ
  let f : A → {x : κ // (Quotient.mk'' x : Quotient (MulAction.orbitRel A κ)) = q} :=
    fun a => ⟨a • Quotient.out q, by
      calc
        (Quotient.mk'' (a • Quotient.out q) :
            Quotient (MulAction.orbitRel A κ)) =
            Quotient.mk'' (Quotient.out q) := by
              exact Quotient.sound ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit _ _))
        _ = q := Quotient.out_eq' q⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hsmul : a • Quotient.out q = b • Quotient.out q := by
      exact congrArg
        (fun x : {x : κ // (Quotient.mk'' x : Quotient (MulAction.orbitRel A κ)) = q} =>
          (x : κ)) hab
    have hstabmem : a⁻¹ * b ∈ MulAction.stabilizer A (Quotient.out q) := by
      rw [MulAction.mem_stabilizer_iff]
      calc
        (a⁻¹ * b) • Quotient.out q = a⁻¹ • (b • Quotient.out q) := by rw [mul_smul]
        _ = a⁻¹ • (a • Quotient.out q) := by rw [hsmul]
        _ = Quotient.out q := by rw [inv_smul_smul]
    have hbot : a⁻¹ * b ∈ (⊥ : Subgroup A) := by
      simpa [hstab (Quotient.out q)] using hstabmem
    have hab1 : a⁻¹ * b = 1 := by simpa using hbot
    exact inv_mul_eq_one.mp hab1
  have hf_surj : Function.Surjective f := by
    intro x
    have hxq : (Quotient.mk'' (x : κ) : Quotient (MulAction.orbitRel A κ)) =
        Quotient.mk'' (Quotient.out q) := by
      exact x.property.trans (Quotient.out_eq' q).symm
    have hrel : MulAction.orbitRel A κ (x : κ) (Quotient.out q) :=
      Quotient.exact hxq
    have hmem : (x : κ) ∈ MulAction.orbit A (Quotient.out q) := by
      exact (MulAction.orbitRel_apply).1 hrel
    rcases MulAction.mem_orbit_iff.mp hmem with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext
    exact ha
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

public theorem theorem_9_8_Ftheta_raw_choice_card_sec9
    (p q : ℕ) :
    Fintype.card (ULift.{u, 0} (Fin q → Fin (p - 1))) = (p - 1) ^ q := by
  rw [Fintype.card_ulift]
  simp

public theorem theorem_9_8_H0C_linear_candidate_count_ne_arithmetic_core_sec9
    {p q u : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp_even_sub_one : Even (p - 1)) (huodd : Odd u)
    (hdiv : u ∣ (p - 1) ^ (q - 1)) :
    ((p - 1) ^ q) / u ≠ p - 1 := by
  intro hcount
  let b := p - 1
  let e := q - 1
  have hb_pos : 0 < b := by
    dsimp [b]
    exact Nat.sub_pos_of_lt hp.one_lt
  have hq_pos : 0 < q := Nat.Prime.pos hq
  have hq_eq : q = e + 1 := by
    dsimp [e]
    exact (Nat.sub_add_cancel hq_pos).symm
  have hbe_dvd_bq : u ∣ b ^ q := by
    rcases hdiv with ⟨t, ht⟩
    refine ⟨t * b, ?_⟩
    dsimp [b, e] at ht ⊢
    rw [hq_eq]
    calc
      (p - 1) ^ (e + 1) = (p - 1) ^ e * (p - 1) := by rw [pow_succ]
      _ = (u * t) * (p - 1) := by rw [ht]
      _ = u * (t * (p - 1)) := by ac_rfl
  have hm_eq : b ^ q = u * b :=
    Nat.eq_mul_of_div_eq_right hbe_dvd_bq (by simpa [b] using hcount)
  rcases hdiv with ⟨t, ht⟩
  have hm_eq2 : b ^ q = u * (t * b) := by
    rw [hq_eq]
    calc
      b ^ (e + 1) = b ^ e * b := by rw [pow_succ]
      _ = (u * t) * b := by rw [ht]
      _ = u * (t * b) := by ac_rfl
  have ht_cancel : b = t * b := by
    have hu_pos : 0 < u := Nat.pos_of_ne_zero (fun hu0 => by simp [hu0] at huodd)
    exact Nat.mul_left_cancel hu_pos (by simpa [hm_eq] using hm_eq2)
  have ht_one : t = 1 :=
    Nat.mul_right_cancel hb_pos (by simpa [Nat.mul_comm] using ht_cancel.symm)
  have hu_eq : u = b ^ e := by
    rw [ht_one, Nat.mul_one] at ht
    exact ht.symm
  have hb_even : Even b := by
    simpa [b] using hp_even_sub_one
  have he_pos : 0 < e := by
    dsimp [e]
    exact Nat.sub_pos_of_lt hq.one_lt
  have hbe_even : Even (b ^ e) :=
    Even.pow_of_ne_zero hb_even (Nat.ne_of_gt he_pos)
  have hu_even : Even u := by
    simpa [hu_eq] using hbe_even
  exact (Nat.not_odd_iff_even.mpr hu_even) huodd

public theorem theorem_9_8_H0C_linear_candidate_count_ne_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((p - 1) ^ q) / u ≠ p - 1 := by
  intro hcase hBarU
  have hqprime : Nat.Prime q := case_9_7_a_q_prime_sec9 hcase
  have hcard : Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q :=
    case_9_7_a_quotient_cardinality_sec9 hcase
  have hUodd : Odd (Nat.card U) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card U)
  have huodd : Odd u := by
    rcases hBarU with ⟨_hCU, hnormal, hbarCard⟩
    letI : (C.subgroupOf U).Normal := hnormal
    have hquot_dvd : Nat.card (U ⧸ C.subgroupOf U) ∣ Nat.card U :=
      Subgroup.card_quotient_dvd_card (C.subgroupOf U)
    have hquot_odd : Odd (Nat.card (U ⧸ C.subgroupOf U)) :=
      Odd.of_dvd_nat hUodd hquot_dvd
    simpa [hbarCard] using hquot_odd
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hp_dvd_quot : p ∣ Nat.card (MF ⧸ H0.subgroupOf MF) := by
    simpa [hcard] using dvd_pow_self p (Nat.pos_iff_ne_zero.mp hqprime.pos)
  have hp_dvd_G : p ∣ Nat.card G := by
    exact hp_dvd_quot.trans <|
      (Subgroup.card_quotient_dvd_card (H0.subgroupOf MF)).trans
        (Subgroup.card_subgroup_dvd_card MF)
  have hp_ne_two : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hp_even_sub_one : Even (p - 1) :=
    hpprime.even_sub_one hp_ne_two
  have hdiv : u ∣ (p - 1) ^ (q - 1) :=
    theorem_9_7_case_a_barU_card_dvd_p_minus_one_pow_sec9 M MF U W1 W2 H0 C p q a u
      hcase hBarU
  exact theorem_9_8_H0C_linear_candidate_count_ne_arithmetic_core_sec9
    hpprime hqprime hp_even_sub_one huodd hdiv

@[expose] public noncomputable def piLinearCharacter_sec9
    {ι : Type v} [Fintype ι]
    (H : ι → Type u) [∀ i, Group (H i)]
    (χ : ∀ i, H i →* ℂˣ) : ((i : ι) → H i) →* ℂˣ where
  toFun x := ∏ i, χ i (x i)
  map_one' := by simp
  map_mul' x := by
    intro y
    simp [Finset.prod_mul_distrib]

public theorem piLinearCharacter_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (H : ι → Type u) [∀ i, Group (H i)]
    (χ : ∀ i, H i →* ℂˣ) (i : ι) (x : H i) :
    piLinearCharacter_sec9 H χ (Pi.mulSingle i x) = χ i x := by
  change (∏ j, χ j (Pi.mulSingle i x j)) = χ i x
  have hfun : (fun j => χ j (Pi.mulSingle i x j)) = Pi.mulSingle i (χ i x) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.mulSingle_eq_of_ne hji]
  rw [hfun]
  simp

@[expose] public noncomputable def finiteInternalProductMulEquiv_sec9
    {ι : Type v} [Fintype ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤) :
    ((i : ι) → H i) ≃* G := by
  classical
  let φ : ((i : ι) → H i) →* G := Subgroup.noncommPiCoprod (H := H) hcomm
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := H) (hcomm := hcomm) hind
  have hφrange : φ.range = ⊤ := by
    calc
      φ.range = iSup H := by
        simpa [φ] using Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm)
      _ = ⊤ := hsup
  have hφsurj : Function.Surjective φ := by
    intro g
    have hg : g ∈ φ.range := by
      rw [hφrange]
      trivial
    rcases hg with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  exact MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩

public theorem finiteInternalProductMulEquiv_apply_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (i : ι) (x : H i) :
    finiteInternalProductMulEquiv_sec9 H hcomm hind hsup (Pi.mulSingle i x) = x := by
  change (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).toMonoidHom
    (Pi.mulSingle i x) = x
  change (Subgroup.noncommPiCoprod hcomm) (Pi.mulSingle i x) = x
  exact Subgroup.noncommPiCoprod_mulSingle i x

set_option maxHeartbeats 800000 in
public theorem theorem_9_8_iSup_split_base_internalDirectProduct_sec9
    {ι : Type v} {G : Type u} [Group G] [IsMulCommutative G]
    (H : ι → Subgroup G) (b : ι)
    (hind : iSupIndep H) (hsup : iSup H = ⊤) :
    let Hrest : Subgroup G := ⨆ i, ⨆ _ : i ≠ b, H i
    Section2.IsInternalDirectProduct (⊤ : Subgroup G) Hrest (H b) := by
  classical
  let Hrest : Subgroup G := ⨆ i, ⨆ _ : i ≠ b, H i
  have hinf : Hrest ⊓ H b = ⊥ := by
    change (⨆ i, ⨆ _ : i ≠ b, H i) ⊓ H b = ⊥
    exact disjoint_iff.mp ((iSupIndep_def.mp hind b).symm)
  have hmul : ∀ c ∈ (⊤ : Subgroup G), ∃ h ∈ Hrest, ∃ k ∈ H b, c = h * k := by
    intro c _hc
    have hcTop : c ∈ iSup H := by
      rw [hsup]
      trivial
    have hle : iSup H ≤ Hrest ⊔ H b := by
      refine iSup_le ?_
      intro i
      by_cases hib : i = b
      · subst i
        exact le_sup_right
      · have hi_le_Hrest : H i ≤ Hrest :=
          le_iSup_of_le i (le_iSup_of_le hib le_rfl)
        exact hi_le_Hrest.trans le_sup_left
    have hcSup : c ∈ Hrest ⊔ H b := hle hcTop
    rcases (Subgroup.mem_sup_of_normal_left (s := Hrest) (t := H b) (x := c)).1
        hcSup with
      ⟨h, hh, k, hk, hhk⟩
    exact ⟨h, hh, k, hk, hhk.symm⟩
  exact
    { left_le := le_top
      right_le := le_top
      commute := by
        intro h _hh k _hk
        exact mul_comm h k
      inf_eq_bot := hinf
      mul_surjective := hmul }

public theorem internalDirectProduct_comap_mulEquiv_top_sec9
    {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) {H K : Subgroup B}
    (h : Section2.IsInternalDirectProduct (⊤ : Subgroup B) H K) :
    Section2.IsInternalDirectProduct (⊤ : Subgroup A)
      (H.comap e.toMonoidHom) (K.comap e.toMonoidHom) := by
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro a _ha
    trivial
  · intro a _ha
    trivial
  · intro a ha b hb
    apply e.injective
    rw [map_mul, map_mul]
    exact h.commute (e a) ha (e b) hb
  · ext a
    constructor
    · intro ha
      have hea : e a ∈ H ⊓ K := ⟨ha.1, ha.2⟩
      have hebot : e a ∈ (⊥ : Subgroup B) := by
        simpa [h.inf_eq_bot] using hea
      have heq : e a = 1 := by
        simpa using hebot
      have haeq : a = 1 := by
        apply e.injective
        simpa using heq
      simp [haeq]
    · intro ha
      have haeq : a = 1 := by simpa using ha
      simp [haeq]
  · intro a _ha
    rcases h.mul_surjective (e a) (by trivial) with ⟨h0, hh0, k0, hk0, heq⟩
    refine ⟨e.symm h0, ?_, e.symm k0, ?_, ?_⟩
    · simpa using hh0
    · simpa using hk0
    · apply e.injective
      simpa [map_mul] using heq

public theorem internalDirectProduct_map_subtype_top_sec9
    {G : Type u} [Group G] {C : Subgroup G} {H K : Subgroup C}
    (h : Section2.IsInternalDirectProduct (⊤ : Subgroup C) H K) :
    Section2.IsInternalDirectProduct C (H.map C.subtype) (K.map C.subtype) := by
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    rcases hx with ⟨h0, _hh0, rfl⟩
    exact h0.property
  · intro x hx
    rcases hx with ⟨k0, _hk0, rfl⟩
    exact k0.property
  · intro x hx y hy
    rcases hx with ⟨h0, hh0, rfl⟩
    rcases hy with ⟨k0, hk0, rfl⟩
    exact congrArg Subtype.val (h.commute h0 hh0 k0 hk0)
  · apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨h0, hh0, hhx⟩
      rcases hx.2 with ⟨k0, hk0, hkx⟩
      have hhk : h0 = k0 := by
        apply Subtype.ext
        exact hhx.trans hkx.symm
      have h0inf : h0 ∈ H ⊓ K := by
        exact ⟨hh0, by simpa [hhk] using hk0⟩
      have h0bot : h0 ∈ (⊥ : Subgroup C) := by
        simpa [h.inf_eq_bot] using h0inf
      have h0one : h0 = 1 := by
        simpa using h0bot
      have hxone : x = 1 := by
        rw [← hhx]
        exact congrArg Subtype.val h0one
      simp [hxone]
    · exact bot_le
  · intro c hc
    rcases h.mul_surjective ⟨c, hc⟩ (by trivial) with ⟨h0, hh0, k0, hk0, hprod⟩
    refine ⟨(h0 : C), ⟨h0, hh0, rfl⟩, (k0 : C), ⟨k0, hk0, rfl⟩, ?_⟩
    exact congrArg Subtype.val hprod

public theorem internalDirectProduct_sup_of_commute_inf_eq_bot_sec9
    {G : Type u} [Group G] (H K : Subgroup G)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    (hinf : H ⊓ K = ⊥) :
    Section2.IsInternalDirectProduct (H ⊔ K) H K := by
  classical
  refine
    { left_le := le_sup_left
      right_le := le_sup_right
      commute := hcomm
      inf_eq_bot := hinf
      mul_surjective := ?_ }
  intro c hc
  have hH_norm_K : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hkh : h * k * h⁻¹ = k := by
        calc
          h * k * h⁻¹ = k * h * h⁻¹ := by
            rw [hcomm h hh k hk]
          _ = k := by simp [mul_assoc]
      simpa [hkh] using hk
    · intro hk
      have hhk : k = h⁻¹ * (h * k * h⁻¹) * h := by
        group
      have hback : h⁻¹ * (h * k * h⁻¹) * h = h * k * h⁻¹ := by
        calc
          h⁻¹ * (h * k * h⁻¹) * h =
              (h * k * h⁻¹) * h⁻¹ * h := by
                rw [hcomm h⁻¹ (H.inv_mem hh) (h * k * h⁻¹) hk]
          _ = h * k * h⁻¹ := by simp [mul_assoc]
      rw [hhk, hback]
      exact hk
  let HS : Subgroup ↥(H ⊔ K) := H.subgroupOf (H ⊔ K)
  let KS : Subgroup ↥(H ⊔ K) := K.subgroupOf (H ⊔ K)
  have hKS_normal : KS.Normal := by
    simpa [KS] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := H) (N := K) hH_norm_K)
  letI : KS.Normal := hKS_normal
  have hHSKS_top : HS ⊔ KS = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := H) (A' := K) (B := H ⊔ K)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcTop : (⟨c, hc⟩ : ↥(H ⊔ K)) ∈ HS ⊔ KS := by
    rw [hHSKS_top]
    trivial
  rcases (Subgroup.mem_sup_of_normal_right (s := HS) (t := KS)
      (x := (⟨c, hc⟩ : ↥(H ⊔ K)))).1 hcTop with
    ⟨h0, hh0, k0, hk0, hprod⟩
  refine ⟨(h0 : G), ?_, (k0 : G), ?_, ?_⟩
  · simpa [HS, Subgroup.mem_subgroupOf] using hh0
  · simpa [KS, Subgroup.mem_subgroupOf] using hk0
  · exact (congrArg Subtype.val hprod).symm

@[expose] public noncomputable def finiteInternalProductMulAut_sec9
    {ι : Type v} [Fintype ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (α : ∀ i, MulAut (H i)) : MulAut G :=
  (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).symm.trans
    ((MulEquiv.piCongrRight fun i => (α i : H i ≃* H i)).trans
      (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup))

public theorem finiteInternalProductMulAut_apply_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (α : ∀ i, MulAut (H i)) (i : ι) (x : H i) :
    finiteInternalProductMulAut_sec9 H hcomm hind hsup α
        (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup (Pi.mulSingle i x)) =
      finiteInternalProductMulEquiv_sec9 H hcomm hind hsup (Pi.mulSingle i (α i x)) := by
  have hpi :
      (MulEquiv.piCongrRight fun i => (α i : H i ≃* H i)) (Pi.mulSingle i x) =
        Pi.mulSingle i (α i x) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.mulSingle, hji]
  simp [finiteInternalProductMulAut_sec9, hpi]

@[expose] public noncomputable def finiteInternalProductLinearCharacter_sec9
    {ι : Type v} [Fintype ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) : G →* ℂˣ :=
  (piLinearCharacter_sec9 (fun i => H i) χ).comp
    (finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).symm.toMonoidHom

public theorem finiteInternalProductLinearCharacter_comp_mulSingle_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) (i : ι) :
    (finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup χ).comp
      ((finiteInternalProductMulEquiv_sec9 H hcomm hind hsup).toMonoidHom.comp
        (MonoidHom.mulSingle (fun i => H i) i)) = χ i := by
  ext x
  simp [finiteInternalProductLinearCharacter_sec9, piLinearCharacter_mulSingle_sec9]


public theorem monoidHom_ext_of_iSup_eq_top_sec9
    {ι : Sort v} {G : Type u} {A : Type w}
    [Group G] [Group A]
    (H : ι → Subgroup G)
    (hsup : iSup H = ⊤)
    (f g : G →* A)
    (hfg : ∀ i, ∀ x : H i, f x = g x) :
    f = g := by
  let E : Subgroup G :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change f (x * y) = g (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change f x⁻¹ = g x⁻¹
        rw [map_inv, map_inv, hx] }
  apply MonoidHom.ext
  intro x
  have htop : (⊤ : Subgroup G) ≤ E := by
    rw [← hsup]
    exact iSup_le fun i x hx => hfg i ⟨x, hx⟩
  exact htop (Subgroup.mem_top x)

public theorem finiteInternalProductLinearCharacter_apply_subgroup_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) (i : ι) (x : H i) :
    finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup χ x = χ i x := by
  have hcomp :=
    congrFun
      (congrArg DFunLike.coe
        (finiteInternalProductLinearCharacter_comp_mulSingle_sec9
          H hcomm hind hsup χ i)) x
  simpa [MonoidHom.comp_apply,
    finiteInternalProductMulEquiv_apply_mulSingle_sec9 H hcomm hind hsup i x]
    using hcomp

public theorem finiteInternalProductLinearCharacter_comp_mulAut_sec9
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H)
    (hsup : iSup H = ⊤)
    (χ : ∀ i, H i →* ℂˣ) (α : ∀ i, MulAut (H i)) :
    finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup
        (fun i => (χ i).comp (α i).symm.toMonoidHom) =
      (finiteInternalProductLinearCharacter_sec9 H hcomm hind hsup χ).comp
        (finiteInternalProductMulAut_sec9 H hcomm hind hsup α).symm.toMonoidHom := by
  ext y
  simp [finiteInternalProductLinearCharacter_sec9, finiteInternalProductMulAut_sec9,
    piLinearCharacter_sec9]

public theorem internalSemidirectProduct_mul_unique_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by
        simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by
        rw [hmul]
      _ = k₂ * k₁⁻¹ := by
        simp
  have hmemH : h₂⁻¹ * h₁ ∈ H :=
    H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K :=
      Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by
    simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by
        simp
      _ = h₂ := by
        simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

@[expose] public noncomputable def internalSemidirectLeftComponent_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) : H := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  exact ⟨Classical.choose hs, (Classical.choose_spec hs).1⟩

@[expose] public noncomputable def internalSemidirectRightComponent_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) : K := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact ⟨Classical.choose hk, (Classical.choose_spec hk).1⟩

public theorem internalSemidirectLeft_mul_rightComponent_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) :
    (internalSemidirectLeftComponent_sec9 h c : G) *
        (internalSemidirectRightComponent_sec9 h c : G) = c := by
  classical
  dsimp [internalSemidirectLeftComponent_sec9, internalSemidirectRightComponent_sec9]
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact (Classical.choose_spec hk).2.symm

public theorem internalSemidirectRightComponent_of_mul_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K)
    {h₀ k₀ : G} (hh₀ : h₀ ∈ H) (hk₀ : k₀ ∈ K) :
    internalSemidirectRightComponent_sec9 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩ =
      ⟨k₀, hk₀⟩ := by
  apply Subtype.ext
  have hdec :=
    internalSemidirectLeft_mul_rightComponent_sec9 h
      ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩
  exact
    (internalSemidirectProduct_mul_unique_sec9 h
      (internalSemidirectLeftComponent_sec9 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hh₀
      (internalSemidirectRightComponent_sec9 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hk₀ hdec).2

@[expose] public noncomputable def internalSemidirectRightProjection_sec9
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) : C →* K where
  toFun := internalSemidirectRightComponent_sec9 h
  map_one' := by
    apply Subtype.ext
    have hdec := internalSemidirectLeft_mul_rightComponent_sec9 h (1 : C)
    exact
      (internalSemidirectProduct_mul_unique_sec9 h
        (internalSemidirectLeftComponent_sec9 h (1 : C)).2 H.one_mem
        (internalSemidirectRightComponent_sec9 h (1 : C)).2 K.one_mem
        (by simpa using hdec)).2
  map_mul' := by
    intro c d
    apply Subtype.ext
    let lc := internalSemidirectLeftComponent_sec9 h c
    let rc := internalSemidirectRightComponent_sec9 h c
    let ld := internalSemidirectLeftComponent_sec9 h d
    let rd := internalSemidirectRightComponent_sec9 h d
    have hdec_c : (lc : G) * (rc : G) = (c : G) :=
      internalSemidirectLeft_mul_rightComponent_sec9 h c
    have hdec_d : (ld : G) * (rd : G) = (d : G) :=
      internalSemidirectLeft_mul_rightComponent_sec9 h d
    have hleft_mem : (lc : G) * Section2.conjBy (rc : G) (ld : G) ∈ H :=
      H.mul_mem lc.2 (h.right_normalizes_left (rc : G) rc.2 (ld : G) ld.2)
    have hright_mem : (rc : G) * (rd : G) ∈ K :=
      K.mul_mem rc.2 rd.2
    have hprod :
        ((lc : G) * Section2.conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
          ((c : G) * (d : G)) := by
      calc
        ((lc : G) * Section2.conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
            ((lc : G) * (rc : G)) * ((ld : G) * (rd : G)) := by
              simp [Section2.conjBy, mul_assoc]
        _ = (c : G) * (d : G) := by
              rw [hdec_c, hdec_d]
    have hdec_cd :=
      internalSemidirectLeft_mul_rightComponent_sec9 h (c * d)
    exact
      (internalSemidirectProduct_mul_unique_sec9 h
        (internalSemidirectLeftComponent_sec9 h (c * d)).2 hleft_mem
        (internalSemidirectRightComponent_sec9 h (c * d)).2 hright_mem
        (by simpa [hprod] using hdec_cd)).2

@[expose] public noncomputable def internalSemidirectRightProjectionTop_sec9
    {G : Type u} [Group G] {H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) H K) :
    G →* K :=
  (internalSemidirectRightProjection_sec9 h).comp
    (Subgroup.topEquiv.symm.toMonoidHom : G →* (⊤ : Subgroup G))

@[expose] public noncomputable def semidirectProductOfInternalDirectProductLinearCharacter_sec9
    {G : Type u} [Group G] {N W1 W2 W : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W)
    (hprod : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) : G →* ℂˣ :=
  (Section3.internalDirectProductLinearCharacter hprod χ η).comp
    (internalSemidirectRightProjectionTop_sec9 hsemi)

public theorem internalSemidirectRightProjectionTop_apply_right_sec9
    {G : Type u} [Group G] {N W : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W) (w : W) :
    internalSemidirectRightProjectionTop_sec9 h (w : G) = w := by
  apply Subtype.ext
  change
    (internalSemidirectRightComponent_sec9 h
        ⟨(w : G), Subgroup.mem_top (w : G)⟩ : G) = (w : G)
  have hright :=
    internalSemidirectRightComponent_of_mul_sec9 h
      (h₀ := (1 : G)) (k₀ := (w : G)) N.one_mem w.2
  simpa using congrArg Subtype.val hright

public theorem internalSemidirectRightProjectionTop_apply_left_sec9
    {G : Type u} [Group G] {N W : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W) (n : N) :
    internalSemidirectRightProjectionTop_sec9 h (n : G) = 1 := by
  apply Subtype.ext
  change
    (internalSemidirectRightComponent_sec9 h
        ⟨(n : G), Subgroup.mem_top (n : G)⟩ : G) = (1 : G)
  have hright :=
    internalSemidirectRightComponent_of_mul_sec9 h
      (h₀ := (n : G)) (k₀ := (1 : G)) n.2 W.one_mem
  simpa using congrArg Subtype.val hright

public theorem semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
    {G : Type u} [Group G] {N W1 W2 W : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W)
    (hprod : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η).comp
      W1.subtype = χ := by
  ext w
  have hproj :
      internalSemidirectRightProjectionTop_sec9 hsemi (w : G) =
        (⟨(w : G), hprod.left_le w.2⟩ : W) := by
    simpa using
      internalSemidirectRightProjectionTop_apply_right_sec9 hsemi
        (⟨(w : G), hprod.left_le w.2⟩ : W)
  calc
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η
        ((W1.subtype) w) : ℂ) =
        (Section3.internalDirectProductLinearCharacter hprod χ η
          (⟨(w : G), hprod.left_le w.2⟩ : W) : ℂ) := by
          simp [semidirectProductOfInternalDirectProductLinearCharacter_sec9, hproj]
    _ = (χ w : ℂ) := by
          have hcomp :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inl W1 W2) w)) : ℂ) = (χ w : ℂ) := by
            simpa [MonoidHom.comp_apply] using
              congrArg (fun z : ℂˣ => (z : ℂ))
                (congrArg (fun f : W1 →* ℂˣ => f w)
                  (Section3.internalDirectProductLinearCharacter_comp_left hprod χ η))
          have happ :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inl W1 W2) w)) : ℂ) =
                (Section3.internalDirectProductLinearCharacter hprod χ η
                  (⟨(w : G), hprod.left_le w.2⟩ : W) : ℂ) := by
            simpa using congrArg
              (fun z : W =>
                (Section3.internalDirectProductLinearCharacter hprod χ η z : ℂ))
              (Section3.internalDirectProductMulEquiv_apply_inl hprod w)
          exact happ.symm.trans hcomp

public theorem semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
    {G : Type u} [Group G] {N W1 W2 W : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup G) N W)
    (hprod : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η).comp
      W2.subtype = η := by
  ext w
  have hproj :
      internalSemidirectRightProjectionTop_sec9 hsemi (w : G) =
        (⟨(w : G), hprod.right_le w.2⟩ : W) := by
    simpa using
      internalSemidirectRightProjectionTop_apply_right_sec9 hsemi
        (⟨(w : G), hprod.right_le w.2⟩ : W)
  calc
    (semidirectProductOfInternalDirectProductLinearCharacter_sec9 hsemi hprod χ η
        ((W2.subtype) w) : ℂ) =
        (Section3.internalDirectProductLinearCharacter hprod χ η
          (⟨(w : G), hprod.right_le w.2⟩ : W) : ℂ) := by
          simp [semidirectProductOfInternalDirectProductLinearCharacter_sec9, hproj]
    _ = (η w : ℂ) := by
          have hcomp :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inr W1 W2) w)) : ℂ) = (η w : ℂ) := by
            simpa [MonoidHom.comp_apply] using
              congrArg (fun z : ℂˣ => (z : ℂ))
                (congrArg (fun f : W2 →* ℂˣ => f w)
                  (Section3.internalDirectProductLinearCharacter_comp_right hprod χ η))
          have happ :
              ((Section3.internalDirectProductLinearCharacter hprod χ η)
                (Section3.internalDirectProductMulEquiv hprod
                  ((MonoidHom.inr W1 W2) w)) : ℂ) =
                (Section3.internalDirectProductLinearCharacter hprod χ η
                  (⟨(w : G), hprod.right_le w.2⟩ : W) : ℂ) := by
            simpa using congrArg
              (fun z : W =>
                (Section3.internalDirectProductLinearCharacter hprod χ η z : ℂ))
              (Section3.internalDirectProductMulEquiv_apply_inr hprod w)
          exact happ.symm.trans hcomp


@[reducible, expose] public noncomputable def linearCharacterMulAction_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q]
    (ρ : A →* MulAut Q) :
    MulAction A (Q →* ℂˣ) := by
  classical
  let F : A →* Function.End (Q →* ℂˣ) :=
    { toFun := fun a χ => χ.comp (ρ a).symm.toMonoidHom
      map_one' := by
        funext χ
        apply MonoidHom.ext
        intro x
        rw [map_one]
        change χ ((1 : MulAut Q).symm x) = χ x
        rfl
      map_mul' := by
        intro a b
        funext χ
        apply MonoidHom.ext
        intro x
        rw [map_mul]
        rfl }
  exact MulAction.ofEndHom F

public theorem linearCharacterMulAction_spec_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q]
    (ρ : A →* MulAut Q) (a : A) (χ : Q →* ℂˣ) :
    letI : MulAction A (Q →* ℂˣ) := linearCharacterMulAction_sec9 ρ
    a • χ = χ.comp (ρ a).symm.toMonoidHom := by
  rfl

@[expose] public noncomputable def mulAutHomInvOfCommDomain_sec9
    {A : Type v} {Q : Type u} [Group A] [IsMulCommutative A] [Group Q]
    (φ : A →* MulAut Q) : A →* MulAut Q where
  toFun a := (φ a).symm
  map_one' := by
    ext x
    rw [map_one]
    rfl
  map_mul' := by
    intro a b
    ext x
    apply (φ (a * b)).injective
    simp only [MulEquiv.apply_symm_apply]
    have hcomm : φ (a * b) = φ (b * a) := by
      exact congrArg φ (mul_comm a b)
    rw [hcomm, map_mul]
    simp

public theorem kernelQuotientConjQuotientAction_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal] :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    letI : MulDistribMulAction G K :=
      MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
    MulAction.QuotientAction G Hsub := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  refine ⟨?_⟩
  intro g a a' h
  change ((g • a)⁻¹ * (g • a') : K) ∈ Hsub
  change ((((g • a)⁻¹ * (g • a') : K) : G)) ∈ N
  have hN : (((a⁻¹ * a' : K) : G)) ∈ N := by
    simpa [Hsub, Subgroup.mem_subgroupOf] using h
  have hgN := (inferInstance : N.Normal).conj_mem (((a⁻¹ * a' : K) : G)) hN g
  convert hgN using 1
  change ((g • a : K) : G)⁻¹ * ((g • a' : K) : G) =
    g * (((a⁻¹ * a' : K) : G)) * g⁻¹
  change ((ConjAct.toConjAct g • a : K) : G)⁻¹ *
      ((ConjAct.toConjAct g • a' : K) : G) =
    g * (((a⁻¹ * a' : K) : G)) * g⁻¹
  rw [ConjAct.Subgroup.val_conj_smul, ConjAct.Subgroup.val_conj_smul]
  simp [ConjAct.toConjAct_smul]
  group

@[reducible, expose] public noncomputable def kernelQuotientConjMulDistribMulAction_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal] :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    MulDistribMulAction G (K ⧸ Hsub) := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  letI : MulAction.QuotientAction G Hsub :=
    kernelQuotientConjQuotientAction_sec9 f N
  exact
    { (inferInstance : MulAction G (K ⧸ Hsub)) with
      smul_mul := by
        intro g q r
        refine Quotient.inductionOn₂' q r ?_
        intro x y
        change g • (((x * y : K) : K ⧸ Hsub)) =
          (((g • x : K) : K ⧸ Hsub)) * (((g • y : K) : K ⧸ Hsub))
        rw [MulAction.Quotient.smul_coe]
        change (((g • (x * y) : K) : K ⧸ Hsub)) =
          ((((g • x) * (g • y) : K) : K ⧸ Hsub))
        rw [smul_mul']
      smul_one := by
        intro g
        change g • (((1 : K) : K ⧸ Hsub)) = (((1 : K) : K ⧸ Hsub))
        rw [MulAction.Quotient.smul_coe]
        simp }

@[expose] public noncomputable def kernelQuotientConjHomFromDomain_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal] :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    G →* MulAut (K ⧸ Hsub) := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G (K ⧸ Hsub) :=
    kernelQuotientConjMulDistribMulAction_sec9 f N
  exact MulDistribMulAction.toMulAut G (K ⧸ Hsub)

public theorem kernelQuotientConjHomFromDomain_ker_le_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal]
    (hcomm :
      let K : Subgroup G := f.ker
      let Hsub : Subgroup K := N.subgroupOf K
      letI : K.Normal := inferInstance
      letI : Hsub.Normal := inferInstance
      IsMulCommutative (K ⧸ Hsub)) :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    K ≤ (kernelQuotientConjHomFromDomain_sec9 f N).ker := by
  classical
  dsimp only
  intro k hk
  rw [MonoidHom.mem_ker]
  ext q
  refine Quotient.inductionOn' q ?_
  intro x
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  letI : MulAction.QuotientAction G Hsub :=
    kernelQuotientConjQuotientAction_sec9 f N
  letI : MulDistribMulAction G (K ⧸ Hsub) :=
    kernelQuotientConjMulDistribMulAction_sec9 f N
  haveI : IsMulCommutative (K ⧸ Hsub) := hcomm
  letI : CommGroup (K ⧸ Hsub) := IsMulCommutative.instCommGroup
  let kk : K := ⟨k, hk⟩
  have hconj :
      (⟨k * (x : G) * k⁻¹, (inferInstance : K.Normal).conj_mem
          (x : G) x.property k⟩ : K) =
        kk * x * kk⁻¹ := by
    ext
    simp [kk, mul_assoc]
  change k • (((x : K) : K ⧸ Hsub)) = (((x : K) : K ⧸ Hsub))
  rw [MulAction.Quotient.smul_coe]
  change QuotientGroup.mk' Hsub
      (⟨k * (x : G) * k⁻¹, (inferInstance : K.Normal).conj_mem
          (x : G) x.property k⟩ : K) =
    QuotientGroup.mk' Hsub x
  rw [hconj]
  simp [mul_assoc, mul_comm, mul_left_comm]


@[expose] public noncomputable def kernelQuotientConjHomOfSurjective_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal]
    (hcomm :
      let K : Subgroup G := f.ker
      let Hsub : Subgroup K := N.subgroupOf K
      letI : K.Normal := inferInstance
      letI : Hsub.Normal := inferInstance
      IsMulCommutative (K ⧸ Hsub))
    (hf : Function.Surjective f) :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    A →* MulAut (K ⧸ Hsub) := by
  classical
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  let ψ : G →* MulAut (K ⧸ Hsub) :=
    kernelQuotientConjHomFromDomain_sec9 f N
  let ψbar : G ⧸ K →* MulAut (K ⧸ Hsub) :=
    QuotientGroup.lift K ψ (by
      simpa [K, ψ] using kernelQuotientConjHomFromDomain_ker_le_sec9 f N hcomm)
  exact ψbar.comp (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom

public theorem kernelQuotientConjHomOfSurjective_apply_mk_sec9
    {G : Type u} {A : Type v} [Group G] [Group A]
    (f : G →* A) (N : Subgroup G) [N.Normal]
    (hcomm :
      let K : Subgroup G := f.ker
      let Hsub : Subgroup K := N.subgroupOf K
      letI : K.Normal := inferInstance
      letI : Hsub.Normal := inferInstance
      IsMulCommutative (K ⧸ Hsub))
    (hf : Function.Surjective f) (g : G) :
    let K : Subgroup G := f.ker
    let Hsub : Subgroup K := N.subgroupOf K
    letI : K.Normal := inferInstance
    letI : Hsub.Normal := inferInstance
    ∀ x : K,
      kernelQuotientConjHomOfSurjective_sec9 f N hcomm hf (f g)
          (QuotientGroup.mk' Hsub x) =
        QuotientGroup.mk' Hsub
          (⟨g * (x : G) * g⁻¹,
            (inferInstance : K.Normal).conj_mem (x : G) x.property g⟩ : K) := by
  classical
  dsimp only
  let K : Subgroup G := f.ker
  let Hsub : Subgroup K := N.subgroupOf K
  letI : K.Normal := inferInstance
  letI : Hsub.Normal := inferInstance
  intro x
  let ψ : G →* MulAut (K ⧸ Hsub) :=
    kernelQuotientConjHomFromDomain_sec9 f N
  let ψbar : G ⧸ K →* MulAut (K ⧸ Hsub) :=
    QuotientGroup.lift K ψ (by
      simpa [K, Hsub, ψ] using
        kernelQuotientConjHomFromDomain_ker_le_sec9 f N hcomm)
  have hsymm :
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g) =
        QuotientGroup.mk' K g := by
    apply (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
    rw [MulEquiv.apply_symm_apply]
    change f g = QuotientGroup.kerLift f (QuotientGroup.mk' K g)
    exact (QuotientGroup.kerLift_mk f g).symm
  change
      (ψbar.comp (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom)
          (f g) (QuotientGroup.mk' Hsub x) =
        QuotientGroup.mk' Hsub
          (⟨g * (x : G) * g⁻¹,
            (inferInstance : K.Normal).conj_mem (x : G) x.property g⟩ : K)
  rw [MonoidHom.comp_apply]
  have hsymm' :
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom (f g) =
        QuotientGroup.mk' K g := by
    simpa using hsymm
  rw [hsymm']
  change ψbar (QuotientGroup.mk' K g) (QuotientGroup.mk' Hsub x) = _
  simp [ψbar, ψ, kernelQuotientConjHomFromDomain_sec9]
  letI : MulDistribMulAction G K :=
    MulDistribMulAction.compHom K ConjAct.toConjAct.toMonoidHom
  letI : MulAction.QuotientAction G Hsub :=
    kernelQuotientConjQuotientAction_sec9 f N
  letI : MulDistribMulAction G (K ⧸ Hsub) :=
    kernelQuotientConjMulDistribMulAction_sec9 f N
  change g • ((x : K) : K ⧸ Hsub) =
    QuotientGroup.mk' Hsub
      (⟨g * (x : G) * g⁻¹,
        (inferInstance : K.Normal).conj_mem (x : G) x.property g⟩ : K)
  rw [MulAction.Quotient.smul_coe]
  rfl


public theorem nonprincipalLinearCharacter_card_eq_pred_sec9
    (Q : Type u) [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p) :
    Nat.card {χ : Q →* ℂˣ // χ ≠ 1} = p - 1 := by
  classical
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  letI : Fintype (Q →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype {χ : Q →* ℂˣ // χ ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hcompl := Fintype.card_subtype_compl (fun χ : Q →* ℂˣ => χ = 1)
  rw [hcompl]
  have hone : Fintype.card {χ : Q →* ℂˣ // χ = 1} = 1 :=
    Fintype.card_ofSubsingleton ⟨1, rfl⟩
  rw [hone]
  have hlin : Fintype.card (Q →* ℂˣ) = p := by
    rw [← Nat.card_eq_fintype_card]
    calc
      Nat.card (Q →* ℂˣ) = Nat.card Q := by
        exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
      _ = p := hcard
  rw [hlin]

@[expose] public noncomputable def nonprincipalLinearCharacterEquivFin_sec9
    (Q : Type u) [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p) :
    Fin (p - 1) ≃ {χ : Q →* ℂˣ // χ ≠ 1} := by
  classical
  letI : Fintype {χ : Q →* ℂˣ // χ ≠ 1} := Fintype.ofFinite _
  have hcard_nonprincipal :
      Fintype.card {χ : Q →* ℂˣ // χ ≠ 1} = p - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact nonprincipalLinearCharacter_card_eq_pred_sec9 Q p hcard
  exact (Fintype.equivFinOfCardEq hcard_nonprincipal).symm

public theorem case_9_7_a_quotient_isElementaryAbelian_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ∃ hnormal : (H0.subgroupOf MF).Normal,
        letI : (H0.subgroupOf MF).Normal := hnormal
        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := by
  intro hcase
  rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, hp_eq, hho⟩
  rcases hho with
    ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0lt, hElem, _hrest⟩
  rcases hElem with ⟨hnormal, hElem⟩
  subst hp_eq
  exact ⟨hnormal, hElem⟩

@[expose] public noncomputable def componentProductLinearCharacter_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Fin (p - 1)) : G →* ℂˣ := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  exact finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
    (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1)

public theorem componentProductLinearCharacter_apply_subgroup_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Fin (p - 1)) (i : Fin q) (x : H i) :
    componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f x =
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 x := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  simpa [componentProductLinearCharacter_sec9, hcomm] using
    finiteInternalProductLinearCharacter_apply_subgroup_sec9 H hcomm hHindep hHsup
      (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1)
      i x

public theorem componentProductLinearCharacter_injective_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤) :
    Function.Injective (componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup) := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  intro f g hfg
  funext i
  have hcoord := congrArg
    (fun lam : G →* ℂˣ => lam.comp
      ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
        (MonoidHom.mulSingle (fun i => H i) i))) hfg
  have hchars :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 =
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (g i)).1 := by
    calc
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 =
          (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
            (fun i => ((nonprincipalLinearCharacterEquivFin_sec9
              (H i) p (hHcard i)) (f i)).1)).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        exact (finiteInternalProductLinearCharacter_comp_mulSingle_sec9 H hcomm
          hHindep hHsup
          (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (f i)).1) i).symm
      _ = (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
            (fun i => ((nonprincipalLinearCharacterEquivFin_sec9
              (H i) p (hHcard i)) (g i)).1)).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        simpa [componentProductLinearCharacter_sec9, hcomm] using hcoord
      _ = ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (g i)).1 :=
        finiteInternalProductLinearCharacter_comp_mulSingle_sec9 H hcomm hHindep hHsup
          (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (g i)).1) i
  have hsub :
      (nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i) =
        (nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (g i) :=
    Subtype.ext hchars
  exact (nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)).injective hsub

public theorem componentProductLinearCharacter_ne_one_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Fin (p - 1)) (i : Fin q) :
    componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f ≠ 1 := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  intro htrivial
  have hcoord := congrArg
    (fun lam : G →* ℂˣ => lam.comp
      ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
        (MonoidHom.mulSingle (fun i => H i) i))) htrivial
  have hchar :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 = 1 := by
    calc
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).1 =
          (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
            (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
              (f i)).1)).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        exact (finiteInternalProductLinearCharacter_comp_mulSingle_sec9 H hcomm
          hHindep hHsup
          (fun i => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (f i)).1) i).symm
      _ = (1 : G →* ℂˣ).comp
            ((finiteInternalProductMulEquiv_sec9 H hcomm hHindep hHsup).toMonoidHom.comp
              (MonoidHom.mulSingle (fun i => H i) i)) := by
        simpa [componentProductLinearCharacter_sec9, hcomm] using hcoord
      _ = 1 := by
        ext x
        rfl
  exact ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) (f i)).2 hchar

/-- Component-product linear character allowing principal components.  A value
`none` chooses the principal character on that component; `some k` chooses the
`k`th nonprincipal character.  This is the source shape used in PF `(9.11.2)`,
where only two components are nonprincipal. -/
@[expose] public noncomputable def componentProductOptionalLinearCharacter_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) : G →* ℂˣ := by
  classical
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  exact finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
    (fun i =>
      match f i with
      | none => 1
      | some k => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1)

public theorem componentProductOptionalLinearCharacter_apply_subgroup_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) (i : Fin q) (x : H i) :
    componentProductOptionalLinearCharacter_sec9 p q H hHcard hHindep hHsup f x =
      (match f i with
      | none => (1 : H i →* ℂˣ)
      | some k => ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1) x := by
  classical
  unfold componentProductOptionalLinearCharacter_sec9
  apply finiteInternalProductLinearCharacter_apply_subgroup_sec9

public theorem componentProductOptionalLinearCharacter_ne_one_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) (i : Fin q) (k : Fin (p - 1))
    (hf : f i = some k) :
    componentProductOptionalLinearCharacter_sec9 p q H hHcard hHindep hHsup f ≠ 1 := by
  classical
  intro htrivial
  have hchar :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1 = 1 := by
    ext x
    have hxone :
        componentProductOptionalLinearCharacter_sec9 p q H hHcard hHindep hHsup f
            (x : G) = 1 := by
      simpa using congrArg
        (fun lam : G →* ℂˣ => lam (x : G)) htrivial
    have happly :=
      componentProductOptionalLinearCharacter_apply_subgroup_sec9
        p q H hHcard hHindep hHsup f i x
    rw [hf] at happly
    exact congrArg Units.val (happly.symm.trans hxone)
  exact ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).2 hchar

public theorem componentProductOptionalLinearCharacter_not_le_ker_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (f : Fin q → Option (Fin (p - 1))) (i : Fin q) (k : Fin (p - 1))
    (hf : f i = some k) :
    ¬ H i ≤ (componentProductOptionalLinearCharacter_sec9
      p q H hHcard hHindep hHsup f).ker := by
  classical
  intro hker
  have hchar :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).1 = 1 := by
    ext x
    have hxker :
        (componentProductOptionalLinearCharacter_sec9
          p q H hHcard hHindep hHsup f) (x : G) = 1 := by
      have hxmem : (x : G) ∈ H i := x.property
      simpa [MonoidHom.mem_ker] using hker hxmem
    have happly :=
      componentProductOptionalLinearCharacter_apply_subgroup_sec9
        p q H hHcard hHindep hHsup f i x
    rw [hf] at happly
    exact congrArg Units.val (happly.symm.trans hxker)
  exact ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)) k).2 hchar

@[expose] public noncomputable def nonprincipalLinearCharacterDualEquiv_sec9
    {Q : Type u} [Group Q]
    (α : MulAut Q) :
    {χ : Q →* ℂˣ // χ ≠ 1} ≃ {χ : Q →* ℂˣ // χ ≠ 1} where
  toFun χ := ⟨χ.1.comp α.symm.toMonoidHom, by
    intro hχ
    apply χ.2
    ext x
    have hval := congrArg (fun ψ : Q →* ℂˣ => ψ (α x)) hχ
    simpa using hval⟩
  invFun χ := ⟨χ.1.comp α.toMonoidHom, by
    intro hχ
    apply χ.2
    ext x
    have hval := congrArg (fun ψ : Q →* ℂˣ => ψ (α.symm x)) hχ
    simpa using hval⟩
  left_inv χ := by
    apply Subtype.ext
    ext x
    simp [MonoidHom.comp_apply]
  right_inv χ := by
    apply Subtype.ext
    ext x
    simp [MonoidHom.comp_apply]

public theorem nonprincipalLinearCharacterDualEquiv_one_sec9
    {Q : Type u} [Group Q]
    (χ : {χ : Q →* ℂˣ // χ ≠ 1}) :
    nonprincipalLinearCharacterDualEquiv_sec9 (1 : MulAut Q) χ = χ := by
  apply Subtype.ext
  ext x
  rfl

public theorem nonprincipalLinearCharacterDualEquiv_mul_sec9
    {Q : Type u} [Group Q]
    (α β : MulAut Q) (χ : {χ : Q →* ℂˣ // χ ≠ 1}) :
    nonprincipalLinearCharacterDualEquiv_sec9 (α * β) χ =
      nonprincipalLinearCharacterDualEquiv_sec9 α
        (nonprincipalLinearCharacterDualEquiv_sec9 β χ) := by
  apply Subtype.ext
  ext x
  rfl

public theorem nonprincipalLinearCharacter_injective_of_prime_card_sec9
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} (hcard : Nat.card Q = p) (hp : Nat.Prime p)
    (χ : {χ : Q →* ℂˣ // χ ≠ 1}) :
    Function.Injective χ.1 := by
  classical
  have htopcard : Nat.card (⊤ : Subgroup Q) = p := by
    simpa using hcard
  have hnotle : ¬ (⊤ : Subgroup Q) ≤ χ.1.ker := by
    intro hle
    apply χ.2
    ext x
    have hx : x ∈ χ.1.ker := hle (Subgroup.mem_top x)
    simpa [MonoidHom.mem_ker] using hx
  have hinjTop :
      Function.Injective fun x : (⊤ : Subgroup Q) => χ.1 (x : Q) :=
    injective_on_prime_card_subgroup_of_not_le_ker_sec9 χ.1 htopcard hp hnotle
  intro x y hxy
  have hsub :
      (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup Q)) =
        ⟨y, Subgroup.mem_top y⟩ :=
    hinjTop hxy
  exact congrArg Subtype.val hsub

public theorem mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} (hcard : Nat.card Q = p) (hp : Nat.Prime p)
    (α : MulAut Q) (χ : {χ : Q →* ℂˣ // χ ≠ 1})
    (hfixed : nonprincipalLinearCharacterDualEquiv_sec9 α χ = χ) :
    α = 1 := by
  classical
  have hχinj : Function.Injective χ.1 :=
    nonprincipalLinearCharacter_injective_of_prime_card_sec9 hcard hp χ
  have hsymm_one : α.symm = 1 := by
    ext x
    apply hχinj
    have hval := congrArg (fun ψ : {χ : Q →* ℂˣ // χ ≠ 1} => ψ.1 x) hfixed
    simpa [nonprincipalLinearCharacterDualEquiv_sec9, MonoidHom.comp_apply] using hval
  ext x
  have hval := congrArg (fun β : MulAut Q => β (α x)) hsymm_one
  simpa using hval.symm

@[reducible, expose] public noncomputable def nonprincipalLinearCharacterIndexMulAction_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p)
    (ρ : A →* MulAut Q) :
    MulAction A (Fin (p - 1)) := by
  classical
  let e := nonprincipalLinearCharacterEquivFin_sec9 Q p hcard
  let F : A →* Function.End (Fin (p - 1)) :=
    { toFun := fun a i => e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ a) (e i))
      map_one' := by
        funext i
        apply e.injective
        dsimp
        calc
          e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ 1) (e i))) =
              nonprincipalLinearCharacterDualEquiv_sec9 (ρ 1) (e i) := by
                exact e.apply_symm_apply _
          _ = nonprincipalLinearCharacterDualEquiv_sec9 (1 : MulAut Q) (e i) := by
                rw [map_one]
          _ = e i := nonprincipalLinearCharacterDualEquiv_one_sec9 (e i)
      map_mul' := by
        intro a b
        funext i
        apply e.injective
        dsimp
        calc
          e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ (a * b)) (e i))) =
              nonprincipalLinearCharacterDualEquiv_sec9 (ρ (a * b)) (e i) := by
                exact e.apply_symm_apply _
          _ = nonprincipalLinearCharacterDualEquiv_sec9 (ρ a * ρ b) (e i) := by
                rw [map_mul]
          _ = nonprincipalLinearCharacterDualEquiv_sec9 (ρ a)
                (nonprincipalLinearCharacterDualEquiv_sec9 (ρ b) (e i)) :=
                nonprincipalLinearCharacterDualEquiv_mul_sec9 (ρ a) (ρ b) (e i)
          _ = e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ a)
                (e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ b) (e i)))))) := by
                simp }
  exact MulAction.ofEndHom F

public theorem nonprincipalLinearCharacterIndexMulAction_spec_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hcard : Nat.card Q = p)
    (ρ : A →* MulAut Q)
    (a : A) (i : Fin (p - 1)) :
    letI : MulAction A (Fin (p - 1)) :=
      nonprincipalLinearCharacterIndexMulAction_sec9 p hcard ρ
    ((nonprincipalLinearCharacterEquivFin_sec9 Q p hcard) (a • i)).1 =
      (((nonprincipalLinearCharacterEquivFin_sec9 Q p hcard) i).1.comp
        (ρ a).symm.toMonoidHom) := by
  classical
  letI : MulAction A (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p hcard ρ
  let e := nonprincipalLinearCharacterEquivFin_sec9 Q p hcard
  change (e (e.symm (nonprincipalLinearCharacterDualEquiv_sec9 (ρ a) (e i)))).1 =
    ((e i).1.comp (ρ a).symm.toMonoidHom)
  simp [e, nonprincipalLinearCharacterDualEquiv_sec9]

public theorem nonprincipalIndexAction_fixed_eq_one_data_sec9
    {A : Type v} {Q : Type u} [Group A] [Group Q] [Finite Q] [IsMulCommutative Q]
    (p : ℕ) (hp : Nat.Prime p)
    (hcard : Nat.card Q = p)
    (ρ : A →* MulAut Q) :
    ∃ instAction : MulAction A (Fin (p - 1)),
      letI : MulAction A (Fin (p - 1)) := instAction
      ∀ a : A, ∀ i : Fin (p - 1), a • i = i → ρ a = 1 := by
  classical
  let instAction : MulAction A (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p hcard ρ
  refine ⟨instAction, ?_⟩
  letI : MulAction A (Fin (p - 1)) := instAction
  intro a i hfix
  let e := nonprincipalLinearCharacterEquivFin_sec9 Q p hcard
  have hcharfixed :
      nonprincipalLinearCharacterDualEquiv_sec9 (ρ a) (e i) = e i := by
    apply Subtype.ext
    have hspec :=
      nonprincipalLinearCharacterIndexMulAction_spec_sec9 p hcard ρ a i
    have hleft : (e (a • i)).1 = (e i).1 :=
      congrArg Subtype.val (congrArg e hfix)
    exact hspec.symm.trans hleft
  exact
    mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
      hcard hp (ρ a) (e i) hcharfixed

@[reducible, expose] public noncomputable def rawCoordinateMulAction_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, A →* MulAut (H i)) :
    MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) := by
  classical
  let F : A →* Function.End (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    { toFun := fun a f =>
        ULift.up fun i =>
          letI : MulAction A (Fin (p - 1)) :=
            nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
          a • f.down i
      map_one' := by
        funext f
        rcases f with ⟨down⟩
        apply ULift.ext
        funext i
        letI : MulAction A (Fin (p - 1)) :=
          nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
        change (1 : A) • down i = down i
        rw [one_smul]
      map_mul' := by
        intro a b
        funext f
        rcases f with ⟨down⟩
        apply ULift.ext
        funext i
        letI : MulAction A (Fin (p - 1)) :=
          nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
        change (a * b) • down i = a • b • down i
        rw [mul_smul] }
  exact MulAction.ofEndHom F

public theorem rawCoordinateMulAction_down_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, A →* MulAut (H i))
    (a : A) (f : ULift.{u, 0} (Fin q → Fin (p - 1))) (i : Fin q) :
    letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    (a • f).down i =
      letI : MulAction A (Fin (p - 1)) :=
        nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
      a • f.down i := by
  rfl

public theorem rawCoordinateMulAction_component_eq_one_of_fixed_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ) (hp : Nat.Prime p)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, A →* MulAut (H i))
    (a : A) (f : ULift.{u, 0} (Fin q → Fin (p - 1))) :
    letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    a • f = f →
      ∀ i, ρ i a = 1 := by
  classical
  letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  intro hfix i
  letI : MulAction A (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p (hHcard i) (ρ i)
  let e := nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i)
  have hcoord : a • f.down i = f.down i := by
    have hdown := congrArg (fun z : ULift.{u, 0} (Fin q → Fin (p - 1)) =>
      z.down i) hfix
    simpa [rawCoordinateMulAction_down_sec9] using hdown
  have hcharfixed :
      nonprincipalLinearCharacterDualEquiv_sec9 (ρ i a) (e (f.down i)) =
        e (f.down i) := by
    apply Subtype.ext
    have hspec :=
      nonprincipalLinearCharacterIndexMulAction_spec_sec9
        p (hHcard i) (ρ i) a (f.down i)
    have hleft :
        (e (a • f.down i)).1 = (e (f.down i)).1 := by
      exact congrArg Subtype.val (congrArg e hcoord)
    exact hspec.symm.trans hleft
  exact
    mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
      (hHcard i) hp (ρ i a) (e (f.down i)) hcharfixed

public theorem componentProductLinearCharacter_rawCoordinateMulAction_sec9
    {A : Type v} {G : Type u} [Group A] [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, A →* MulAut (H i))
    (a : A) (f : ULift.{u, 0} (Fin q → Fin (p - 1))) :
    letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
        (a • f).down =
      (componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
        f.down).comp
        (finiteInternalProductMulAut_sec9 H
          (by
            intro _i _j _hij x y _hx _hy
            exact mul_comm x y)
          hHindep hHsup (fun i => ρ i a)).symm.toMonoidHom := by
  classical
  letI : MulAction A (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  let hcomm : Pairwise fun i j : Fin q =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  change finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
      (fun i =>
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
          ((a • f).down i)).1) =
    (finiteInternalProductLinearCharacter_sec9 H hcomm hHindep hHsup
      (fun i =>
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
          (f.down i)).1)).comp
      (finiteInternalProductMulAut_sec9 H hcomm hHindep hHsup
        (fun i => ρ i a)).symm.toMonoidHom
  have hχ :
      (fun i =>
        ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
          ((a • f).down i)).1) =
        (fun i =>
          (((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
            (f.down i)).1).comp (ρ i a).symm.toMonoidHom) := by
    funext i
    ext x
    have hspec :=
      nonprincipalLinearCharacterIndexMulAction_spec_sec9 p (hHcard i) (ρ i)
        a (f.down i)
    exact congrArg Units.val <| by
      simpa [rawCoordinateMulAction_down_sec9] using
        congrFun (congrArg DFunLike.coe hspec) x
  rw [hχ]
  exact finiteInternalProductLinearCharacter_comp_mulAut_sec9 H hcomm hHindep hHsup
    (fun i =>
      ((nonprincipalLinearCharacterEquivFin_sec9 (H i) p (hHcard i))
        (f.down i)).1)
    (fun i => ρ i a)

public theorem mulAut_eq_of_eq_on_iSup_eq_top_sec9
    {ι : Sort v} {G : Type u} [Group G]
    (H : ι → Subgroup G)
    (hHsup : iSup H = ⊤)
    (α β : MulAut G)
    (hfix : ∀ i, ∀ x : G, x ∈ H i → α x = β x) :
    α = β := by
  ext x
  let K : Subgroup G :=
    { carrier := {x | α x = β x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change α (x * y) = β (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change α x⁻¹ = β x⁻¹
        rw [map_inv, map_inv, hx] }
  have htop_le : (⊤ : Subgroup G) ≤ K := by
    rw [← hHsup]
    exact iSup_le fun i => by
      intro x hx
      exact hfix i x hx
  exact htop_le (Subgroup.mem_top x)

public theorem finiteInternalProductMulAut_eq_quotientConjAction_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G}
    {q : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hqpos : 0 < q)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x) :
    ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
      ∀ h : MF,
        finiteInternalProductMulAut_sec9 H
            (by
              intro _i _j _hij y z _hy _hz
              exact mul_comm y z)
            hHindep hHsup (fun i => ρ i x)
          (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
  classical
  let hcommPair : Pairwise fun i j : Fin q =>
      ∀ y z : MF ⧸ H0.subgroupOf MF, y ∈ H i → z ∈ H j → Commute y z := by
    intro _i _j _hij y z _hy _hz
    exact mul_comm y z
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H hcommPair hHindep hHsup (fun i => ρ i x)
  let i0 : Fin q := ⟨0, hqpos⟩
  rcases hHnorm i0 u with ⟨hconjMF0, action0, haction0, _hmap0⟩
  have hαeq : α = action0 := by
    apply mulAut_eq_of_eq_on_iSup_eq_top_sec9 H hHsup
    intro i y hy
    let yH : H i := ⟨y, hy⟩
    have hαy : α y = (ρ i x yH : MF ⧸ H0.subgroupOf MF) := by
      have hsingle :=
        finiteInternalProductMulAut_apply_mulSingle_sec9 H hcommPair hHindep hHsup
          (fun i => ρ i x) i yH
      simpa [α, yH,
        finiteInternalProductMulEquiv_apply_mulSingle_sec9 H hcommPair hHindep hHsup]
        using hsingle
    rcases hHnorm i u with ⟨hconjMFi, actioni, hactioni, _hmapi⟩
    have haction_eq : actioni = action0 := by
      ext z
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) z with ⟨t, rfl⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) t) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFi t⟩ := hactioni t
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMF0 t⟩ := by
              congr 1
        _ = action0 (QuotientGroup.mk' (H0.subgroupOf MF) t) :=
              (haction0 t).symm
    have hactiony : action0 y = (ρ i x yH : MF ⧸ H0.subgroupOf MF) := by
      rw [← haction_eq]
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) y with ⟨t, rfl⟩
      rcases hρaction i x u hux with ⟨hconjMFρ, hρ_apply⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) t) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFi t⟩ := hactioni t
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFρ t⟩ := by
              congr 1
        _ = (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) t, hy⟩ :
                MF ⧸ H0.subgroupOf MF) := (hρ_apply t hy).symm
    exact hαy.trans hactiony.symm
  refine ⟨hconjMF0, ?_⟩
  intro h
  calc
    finiteInternalProductMulAut_sec9 H
        (by
          intro _i _j _hij y z _hy _hz
          exact mul_comm y z)
        hHindep hHsup (fun i => ρ i x)
        (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        α (QuotientGroup.mk' (H0.subgroupOf MF) h) := by
          rfl
    _ = action0 (QuotientGroup.mk' (H0.subgroupOf MF) h) := by
          rw [hαeq]
    _ = QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF0 h⟩ := haction0 h

public theorem finiteInternalProductMulAut_symm_eq_quotientConjAction_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G}
    {q : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hqpos : 0 < q)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x) :
    ∃ hconjMF : ∀ h : MF, (u : G) * (h : G) * (u : G)⁻¹ ∈ MF,
      ∀ h : MF,
        (finiteInternalProductMulAut_sec9 H
            (by
              intro _i _j _hij y z _hy _hz
              exact mul_comm y z)
            hHindep hHsup (fun i => ρ i x)).symm
          (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G) * (h : G) * (u : G)⁻¹, hconjMF h⟩ := by
  classical
  let hcommPair : Pairwise fun i j : Fin q =>
      ∀ y z : MF ⧸ H0.subgroupOf MF, y ∈ H i → z ∈ H j → Commute y z := by
    intro _i _j _hij y z _hy _hz
    exact mul_comm y z
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H hcommPair hHindep hHsup (fun i => ρ i x)
  rcases finiteInternalProductMulAut_eq_quotientConjAction_sec9
      H hHnorm hHindep hHsup ρ hρaction hqpos x u hux with
    ⟨hconjMFminus, hα_apply⟩
  let uinv : U := ⟨(u : G)⁻¹, U.inv_mem u.property⟩
  have huinvx :
      QuotientGroup.mk' (C.subgroupOf U) uinv = x⁻¹ := by
    calc
      QuotientGroup.mk' (C.subgroupOf U) uinv =
          (QuotientGroup.mk' (C.subgroupOf U) u)⁻¹ := by rfl
      _ = x⁻¹ := by rw [hux]
  rcases finiteInternalProductMulAut_eq_quotientConjAction_sec9
      H hHnorm hHindep hHsup ρ hρaction hqpos x⁻¹ uinv huinvx with
    ⟨hconjMFplus, _hconj_apply_inv⟩
  refine ⟨?_, ?_⟩
  · intro h
    simpa [uinv, mul_assoc] using hconjMFplus h
  · intro h
    have hmem : (u : G) * (h : G) * (u : G)⁻¹ ∈ MF := by
      simpa [uinv, mul_assoc] using hconjMFplus h
    let hplus : MF := ⟨(u : G) * (h : G) * (u : G)⁻¹, hmem⟩
    have hα_hplus :
        α (QuotientGroup.mk' (H0.subgroupOf MF) hplus) =
          QuotientGroup.mk' (H0.subgroupOf MF) h := by
      calc
        α (QuotientGroup.mk' (H0.subgroupOf MF) hplus) =
            finiteInternalProductMulAut_sec9 H hcommPair hHindep hHsup (fun i => ρ i x)
              (QuotientGroup.mk' (H0.subgroupOf MF) hplus) := by
              rfl
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (hplus : G) * (u : G), hconjMFminus hplus⟩ :=
              hα_apply hplus
        _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
              congr 1
              ext
              simp [hplus, mul_assoc]
    have htarget :
        α.symm (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF) hplus := by
      apply α.injective
      calc
        α (α.symm (QuotientGroup.mk' (H0.subgroupOf MF) h)) =
            QuotientGroup.mk' (H0.subgroupOf MF) h := by simp
        _ = α (QuotientGroup.mk' (H0.subgroupOf MF) hplus) := hα_hplus.symm
    simpa [α, hplus] using htarget

public theorem quotient_commutator_mem_of_mk_conj_eq_self_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    {u : G}
    (hconjMF : ∀ h : MF, u⁻¹ * (h : G) * u ∈ MF)
    (hfix : ∀ h : MF,
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨u⁻¹ * (h : G) * u, hconjMF h⟩ =
        QuotientGroup.mk' (H0.subgroupOf MF) h) :
    ∀ h : G, h ∈ MF → ⁅u⁻¹, h⁆ ∈ H0 := by
  classical
  intro h hhMF
  let hMF : MF := ⟨h, hhMF⟩
  have hq :
      QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨u⁻¹ * (hMF : G) * u, hconjMF hMF⟩ =
        QuotientGroup.mk' (H0.subgroupOf MF) hMF :=
    hfix hMF
  have hdiv :
      (⟨u⁻¹ * (hMF : G) * u, hconjMF hMF⟩ / hMF : MF) ∈
        H0.subgroupOf MF :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have hval :
      (((⟨u⁻¹ * (hMF : G) * u, hconjMF hMF⟩ / hMF : MF) : G)) =
        ⁅u⁻¹, h⁆ := by
    simp [hMF, div_eq_mul_inv, commutatorElement_def, mul_assoc]
  simpa [Subgroup.mem_subgroupOf, hval] using hdiv

public theorem mulAut_fixed_of_iSup_eq_top_sec9
    {G : Type u} [Group G]
    {ι : Sort v} (H : ι → Subgroup G)
    (hHsup : iSup H = ⊤)
    (α : MulAut G)
    (hfix : ∀ i, ∀ x : G, x ∈ H i → α x = x) :
    ∀ x : G, α x = x := by
  let K : Subgroup G :=
    { carrier := {x | α x = x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change α (x * y) = x * y
        rw [map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change α x⁻¹ = x⁻¹
        rw [map_inv, hx] }
  have htop_le : (⊤ : Subgroup G) ≤ K := by
    rw [← hHsup]
    exact iSup_le fun i => by
      intro x hx
      exact hfix i x hx
  intro x
  exact htop_le (Subgroup.mem_top x)

public theorem rawCoordinateMulAction_quotient_eq_one_of_fixed_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (x : U ⧸ C.subgroupOf U)
    (f : ULift.{u, 0} (Fin q → Fin (p - 1))) :
    letI : MulAction (U ⧸ C.subgroupOf U)
        (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    x • f = f →
      x = 1 := by
  classical
  letI : MulAction (U ⧸ C.subgroupOf U)
      (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  intro hfix
  have hρone : ∀ i, ρ i x = 1 :=
    rawCoordinateMulAction_component_eq_one_of_fixed_sec9
      p q (case_9_7_a_p_prime_sec9 hcase) H hHcard ρ x f hfix
  rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  let i0 : Fin q := ⟨0, hqpos⟩
  rcases hHnorm i0 u with ⟨hconjMF0, action0, haction0, _hmap0⟩
  have haction0_fix :
      ∀ y : MF ⧸ H0.subgroupOf MF, action0 y = y := by
    apply mulAut_fixed_of_iSup_eq_top_sec9 H hHsup action0
    intro i y hy
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) y with ⟨h, rfl⟩
    rcases hHnorm i u with ⟨hconjMFi, actioni, hactioni, _hmapi⟩
    have haction_eq : actioni = action0 := by
      ext z
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) z with ⟨t, rfl⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) t) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMFi t⟩ := hactioni t
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (t : G) * (u : G), hconjMF0 t⟩ := by
              congr 1
        _ = action0 (QuotientGroup.mk' (H0.subgroupOf MF) t) :=
              (haction0 t).symm
    have hactioni_fix :
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF) h := by
      rcases hρaction i (QuotientGroup.mk' (C.subgroupOf U) u) u rfl with
        ⟨hconjMFρ, hρ_apply⟩
      calc
        actioni (QuotientGroup.mk' (H0.subgroupOf MF) h) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMFi h⟩ := hactioni h
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMFρ h⟩ := by
              congr 1
        _ = (ρ i (QuotientGroup.mk' (C.subgroupOf U) u)
              ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hy⟩ :
                MF ⧸ H0.subgroupOf MF) := (hρ_apply h hy).symm
        _ = ((1 : MulAut (H i))
              ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hy⟩ :
                MF ⧸ H0.subgroupOf MF) := by
              have hρid :=
                congrFun (congrArg DFunLike.coe (hρone i))
                  ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hy⟩
              exact congrArg Subtype.val hρid
        _ = QuotientGroup.mk' (H0.subgroupOf MF) h := rfl
    simpa [haction_eq] using hactioni_fix
  have huInvC : (u : G)⁻¹ ∈ C := by
    have huInvU : (u : G)⁻¹ ∈ U := by
      exact U.inv_mem u.property
    rw [(case_9_7_a_quotientCentralizerIn_sec9 hcase).2 ((u : G)⁻¹) huInvU]
    intro h hhMF
    have hfix_mk : ∀ z : MF,
        QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(u : G)⁻¹ * (z : G) * (u : G), hconjMF0 z⟩ =
          QuotientGroup.mk' (H0.subgroupOf MF) z := by
      intro z
      exact (haction0 z).symm.trans
        (haction0_fix (QuotientGroup.mk' (H0.subgroupOf MF) z))
    exact quotient_commutator_mem_of_mk_conj_eq_self_sec9 hconjMF0 hfix_mk h hhMF
  have huC : (u : G) ∈ C := by
    simpa using C.inv_mem huInvC
  exact (QuotientGroup.eq_one_iff (N := C.subgroupOf U) (x := u)).2
    (by simpa [Subgroup.mem_subgroupOf] using huC)

public theorem rawCoordinateMulAction_stabilizer_eq_bot_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHsup : iSup H = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) :
    letI : MulAction (U ⧸ C.subgroupOf U)
        (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    ∀ k : ULift.{u, 0} (Fin q → Fin (p - 1)),
      MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥ := by
  classical
  letI : MulAction (U ⧸ C.subgroupOf U)
      (ULift.{u, 0} (Fin q → Fin (p - 1))) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  intro k
  ext x
  constructor
  · intro hx
    rw [MulAction.mem_stabilizer_iff] at hx
    have hxone :
        x = (1 : U ⧸ C.subgroupOf U) :=
      rawCoordinateMulAction_quotient_eq_one_of_fixed_sec9
        hcase H hHcard hHnorm hHsup ρ hρaction x k hx
    rw [hxone]
    exact Subgroup.mem_bot.2 rfl
  · intro hx
    have hxone : x = (1 : U ⧸ C.subgroupOf U) := by
      simpa using (Subgroup.mem_bot.mp hx)
    rw [MulAction.mem_stabilizer_iff, hxone, one_smul]



end CFSG.Section9
