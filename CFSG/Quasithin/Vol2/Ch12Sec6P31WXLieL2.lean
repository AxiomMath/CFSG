module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXLie
public import CFSG.Milestones.ASVolI.A3Aut.L2

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.GorensteinWalter CFSG.ASVolI CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

noncomputable def l2DiagHom (K : Type) [Field K] : Kˣ →* PSL2 K :=
  (psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K)

theorem l2DiagHom_mem_borel (K : Type) [Field K] (l : Kˣ) : l2DiagHom K l ∈ psl2Borel K :=
  burnsideAut_psl2Diag_le_borel (MonoidHom.mem_range.mpr ⟨l, rfl⟩)

theorem l2DiagHom_comm (K : Type) [Field K] (l l' : Kˣ) :
    l2DiagHom K l * l2DiagHom K l' = l2DiagHom K l' * l2DiagHom K l := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem l2_conj_mem_of_borel {K : Type} [Field K] {x n : PSL2 K} (hx : x ∈ psl2Borel K)
    (hn : n ∈ psl2UpperUnipotentSubgroup K) : x * n * x⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  have hN : x ∈ Subgroup.normalizer (psl2UpperUnipotentSubgroup K : Set (PSL2 K)) := by
    rw [psl2UpperUnipotent_normalizer_eq_borel]
    exact hx
  exact (Subgroup.mem_normalizer_iff.mp hN n).1 hn

theorem l2_borel_decomp {K : Type} [Field K] {b : PSL2 K} (hb : b ∈ psl2Borel K) :
    ∃ u ∈ psl2UpperUnipotentSubgroup K, ∃ l : Kˣ, b = u * l2DiagHom K l := by
  rw [psl2Borel_eq_map] at hb
  obtain ⟨A, hA, rfl⟩ := hb
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).1 hA
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  have ha : A.val 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  set a : Kˣ := Units.mk0 (A.val 0 0) ha with haDef
  have hinv : ((a⁻¹ : Kˣ) : K) = A.val 1 1 := by
    rw [Units.val_inv_eq_inv_val, haDef, Units.val_mk0]
    exact inv_eq_of_mul_eq_one_right hdet
  have hAeq : A = sl2UpperUnipotent (A.val 0 1 * A.val 0 0) * burnsideAut_sl2DiagHom K a := by
    apply Subtype.ext
    change A.val = (!![1, A.val 0 1 * A.val 0 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]
    rw [Matrix.mul_fin_two, hinv]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [haDef]
    · have h3 : A.val 0 1 * A.val 0 0 * A.val 1 1 = A.val 0 1 := by rw [mul_assoc, hdet, mul_one]
      simp [h3]
    · simp [h10]
    · simp
  refine ⟨psl2QuotientMap K (sl2UpperUnipotent (A.val 0 1 * A.val 0 0)),
    (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨_, rfl⟩, a, ?_⟩
  show psl2QuotientMap K A = psl2QuotientMap K (sl2UpperUnipotent (A.val 0 1 * A.val 0 0)) *
    psl2QuotientMap K (burnsideAut_sl2DiagHom K a)
  rw [← map_mul, ← hAeq]

theorem l2_borel_comm {K : Type} [Field K] {a b : PSL2 K} (ha : a ∈ psl2Borel K)
    (hb : b ∈ psl2Borel K) : a * b * a⁻¹ * b⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  obtain ⟨u, hu, l, rfl⟩ := l2_borel_decomp ha
  obtain ⟨u', hu', l', rfl⟩ := l2_borel_decomp hb
  have hc := l2DiagHom_comm K l l'
  have hdd : l2DiagHom K l' * (l2DiagHom K l)⁻¹ = (l2DiagHom K l)⁻¹ * l2DiagHom K l' := by
    calc l2DiagHom K l' * (l2DiagHom K l)⁻¹
        = (l2DiagHom K l)⁻¹ * (l2DiagHom K l * l2DiagHom K l') * (l2DiagHom K l)⁻¹ := by group
      _ = (l2DiagHom K l)⁻¹ * (l2DiagHom K l' * l2DiagHom K l) * (l2DiagHom K l)⁻¹ := by rw [hc]
      _ = (l2DiagHom K l)⁻¹ * l2DiagHom K l' := by group
  have h1 : l2DiagHom K l * u' * (l2DiagHom K l)⁻¹ ∈ psl2UpperUnipotentSubgroup K :=
    l2_conj_mem_of_borel (l2DiagHom_mem_borel K l) hu'
  have h2 : l2DiagHom K l' * u⁻¹ * (l2DiagHom K l')⁻¹ ∈ psl2UpperUnipotentSubgroup K :=
    l2_conj_mem_of_borel (l2DiagHom_mem_borel K l') (inv_mem hu)
  have key : u * l2DiagHom K l * (u' * l2DiagHom K l') * (u * l2DiagHom K l)⁻¹ *
      (u' * l2DiagHom K l')⁻¹ = u * (l2DiagHom K l * u' * (l2DiagHom K l)⁻¹) *
        (l2DiagHom K l' * u⁻¹ * (l2DiagHom K l')⁻¹) * u'⁻¹ := by
    calc u * l2DiagHom K l * (u' * l2DiagHom K l') * (u * l2DiagHom K l)⁻¹ *
          (u' * l2DiagHom K l')⁻¹
        = u * l2DiagHom K l * u' * (l2DiagHom K l' * (l2DiagHom K l)⁻¹) * u⁻¹ *
            (l2DiagHom K l')⁻¹ * u'⁻¹ := by group
      _ = u * l2DiagHom K l * u' * ((l2DiagHom K l)⁻¹ * l2DiagHom K l') * u⁻¹ *
            (l2DiagHom K l')⁻¹ * u'⁻¹ := by rw [hdd]
      _ = u * (l2DiagHom K l * u' * (l2DiagHom K l)⁻¹) *
            (l2DiagHom K l' * u⁻¹ * (l2DiagHom K l')⁻¹) * u'⁻¹ := by group
  rw [key]
  exact mul_mem (mul_mem (mul_mem hu h1) h2) (inv_mem hu')

theorem l2_pow_mod {K : Type} [Field K] {u : PSL2 K} (hu : u ∈ psl2UpperUnipotentSubgroup K)
    (l : Kˣ) (n : ℕ) :
    ∃ v ∈ psl2UpperUnipotentSubgroup K, (u * l2DiagHom K l) ^ n = v * l2DiagHom K l ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨v, hv, hvn⟩ := ih
    refine ⟨v * (l2DiagHom K l ^ n * u * (l2DiagHom K l ^ n)⁻¹), mul_mem hv ?_, ?_⟩
    · exact l2_conj_mem_of_borel (pow_mem (l2DiagHom_mem_borel K l) n) hu
    · rw [pow_succ, hvn, pow_succ]
      group

theorem l2_center_sl2_eq_bot (K : Type) [Field K] [CharP K 2] :
    Subgroup.center (SL(2, K)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  have hc := Subgroup.mem_center_iff.mp hA
  have hE : (!![(1 : K), 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * !![(1 : K), 1; 0, 1] :=
    congrArg Subtype.val (hc ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩)
  have hF : (!![(1 : K), 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * !![(1 : K), 0; 1, 1] :=
    congrArg Subtype.val (hc ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩)
  obtain ⟨a, b, c, d, hAm⟩ : ∃ a b c d : K, (A : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h := A.property
    rw [hAm, Matrix.det_fin_two_of] at h
    exact h
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [hAm] at hE hF
  have hE00 := congrFun (congrFun hE 0) 0
  have hE01 := congrFun (congrFun hE 0) 1
  have hF00 := congrFun (congrFun hF 0) 0
  simp [Matrix.mul_fin_two] at hE00 hE01 hF00
  have hc0 : c = 0 := by linear_combination hE00
  have hb0 : b = 0 := by linear_combination hF00
  have had : d = a := by linear_combination hE01
  have hsq : a * a = 1 := by
    rw [hb0, hc0, had] at hdet
    linear_combination hdet
  have hsq1 : (a - 1) * (a - 1) = 0 := by linear_combination hsq + (1 - a) * h2
  have ha1 : a = 1 := by
    have := mul_self_eq_zero.mp hsq1
    linear_combination this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, hAm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha1, hb0, hc0, had]

noncomputable def l2SL2Equiv (K : Type) [Field K] [CharP K 2] : SL(2, K) ≃* PSL2 K :=
  MulEquiv.ofBijective (psl2QuotientMap K) (by
    refine ⟨?_, psl2QuotientMap_surjective⟩
    rw [← MonoidHom.ker_eq_bot_iff]
    change MonoidHom.ker (QuotientGroup.mk' (Subgroup.center (SL(2, K)))) = ⊥
    rw [QuotientGroup.ker_mk', l2_center_sl2_eq_bot K])

theorem l2_psl2_card (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card (PSL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [← CFSG.GorensteinWalter.sl2_card_formula K]
  exact Nat.card_congr (l2SL2Equiv K).symm.toEquiv

theorem l2_psl2Borel_isCoatom (K : Type) [Field K] [CharP K 2] :
    IsCoatom (psl2Borel K) := by
  have h : IsCoatom (sl2Borel K) :=
    CFSG.QuasithinUnique.Setup.SL2Modules.isCoatom_stabilizer_projective
      (psl2ProjectiveInfinity K)
  rw [psl2Borel_eq_map]
  exact (OrderIso.isCoatom_iff (l2SL2Equiv K).mapSubgroup (sl2Borel K)).2 h

theorem l2_psl2Borel_card (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card (psl2Borel K) = Nat.card K * (Nat.card K - 1) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hinj : Function.Injective (psl2QuotientMap K) := (l2SL2Equiv K).injective
  have hB : Nat.card (sl2Borel K) = Nat.card K * (Nat.card K - 1) := by
    have h := CFSG.QuasithinUnique.Setup.SL2Modules.natCard_borel (F := K)
    rw [Nat.card_eq_fintype_card (α := K)]
    exact h
  rw [psl2Borel_eq_map, Subgroup.card_map_of_injective hinj]
  exact hB

theorem l2_fieldAut_diag {K : Type} [Field K] (σ : K ≃+* K) (j : ℕ)
    (hj : ∀ x : K, σ x = x ^ 2 ^ j) (l : Kˣ) :
    psl2FieldAut K σ (l2DiagHom K l) = l2DiagHom K l ^ 2 ^ j := by
  rw [← map_pow (l2DiagHom K) l (2 ^ j)]
  have hu : Units.map (σ : K →* K) l = l ^ 2 ^ j := by
    apply Units.ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hj _
  show psl2FieldAut K σ (psl2QuotientMap K (burnsideAut_sl2DiagHom K l)) =
    psl2QuotientMap K (burnsideAut_sl2DiagHom K (l ^ 2 ^ j))
  rw [burnsideAut_psl2FieldAut_diag, hu]

theorem l2_ringEquiv_pow {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ∃ j : ℕ, ∀ x : K, σ x = x ^ 2 ^ j := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ x : ZMod 2, σ (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod 2) K))
      (algebraMap (ZMod 2) K)) x
  let f : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv hcomm
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).2 f
  refine ⟨n, fun x => ?_⟩
  have h1 : ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (n : ℕ)) x = f x :=
    DFunLike.congr_fun hn x
  have h2 : ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (n : ℕ)) x =
      x ^ 2 ^ (n : ℕ) := by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  exact (h2.symm.trans h1).symm

theorem l2_model_action {K : Type} [Field K] [Finite K] [CharP K 2] (α : MulAut (PSL2 K))
    (hα : (psl2UpperUnipotentSubgroup K).map α.toMonoidHom = psl2UpperUnipotentSubgroup K) :
    ∃ j : ℕ, ∀ b ∈ psl2Borel K, α b * (b ^ 2 ^ j)⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  haveI := burnsideAut_inn_normal (PSL2 K)
  obtain ⟨c, hc, f, hf, hcf⟩ := Subgroup.mem_sup_of_normal_left.mp
    (burnsideAut_psl2_aut_mem α)
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hc
  obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hf
  subst hcf
  obtain ⟨j, hj⟩ := l2_ringEquiv_pow σ
  have hfU : (psl2UpperUnipotentSubgroup K).map (psl2FieldAut K σ).toMonoidHom =
      psl2UpperUnipotentSubgroup K := burnsideAut_map_psl2FieldAut_upper σ
  have hxU : (psl2UpperUnipotentSubgroup K).map (MulAut.conj x).toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
    calc (psl2UpperUnipotentSubgroup K).map (MulAut.conj x).toMonoidHom
        = ((psl2UpperUnipotentSubgroup K).map (psl2FieldAut K σ).toMonoidHom).map
            (MulAut.conj x).toMonoidHom := by rw [hfU]
      _ = (psl2UpperUnipotentSubgroup K).map
            ((MulAut.conj x).toMonoidHom.comp (psl2FieldAut K σ).toMonoidHom) :=
          Subgroup.map_map _ _ _
      _ = psl2UpperUnipotentSubgroup K := hα
  have hxB : x ∈ psl2Borel K := by
    rw [← psl2UpperUnipotent_normalizer_eq_borel]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxU
  refine ⟨j, fun b hb => ?_⟩
  obtain ⟨u, hu, l, rfl⟩ := l2_borel_decomp hb
  have hfu : psl2FieldAut K σ u ∈ psl2UpperUnipotentSubgroup K := by
    rw [← hfU]
    exact Subgroup.mem_map_of_mem _ hu
  have hfD : psl2FieldAut K σ (l2DiagHom K l) = l2DiagHom K l ^ 2 ^ j :=
    l2_fieldAut_diag σ j hj l
  have hc' : psl2FieldAut K σ u * l2DiagHom K l ^ 2 ^ j ∈ psl2Borel K :=
    mul_mem (psl2UpperUnipotent_le_borel hfu) (pow_mem (l2DiagHom_mem_borel K l) _)
  have hαb : (MulAut.conj x * psl2FieldAut K σ) (u * l2DiagHom K l) =
      x * (psl2FieldAut K σ u * l2DiagHom K l ^ 2 ^ j) * x⁻¹ := by
    show x * psl2FieldAut K σ (u * l2DiagHom K l) * x⁻¹ = _
    rw [map_mul, hfD]
  obtain ⟨v, hv, hvb⟩ := l2_pow_mod hu l (2 ^ j)
  have hw := l2_borel_comm hxB hc'
  rw [hαb, hvb]
  have key : x * (psl2FieldAut K σ u * l2DiagHom K l ^ 2 ^ j) * x⁻¹ *
      (v * l2DiagHom K l ^ 2 ^ j)⁻¹ = x * (psl2FieldAut K σ u * l2DiagHom K l ^ 2 ^ j) * x⁻¹ *
        (psl2FieldAut K σ u * l2DiagHom K l ^ 2 ^ j)⁻¹ * psl2FieldAut K σ u * v⁻¹ := by
    group
  rw [key]
  exact mul_mem (mul_mem hw hfu) (inv_mem hv)

theorem l2_borel_cyclic (K : Type) [Field K] [Finite K] :
    ∃ g ∈ psl2Borel K, ∀ b ∈ psl2Borel K,
      ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ psl2UpperUnipotentSubgroup K := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨l2DiagHom K γ, l2DiagHom_mem_borel K γ, fun b hb => ?_⟩
  obtain ⟨u, hu, l, rfl⟩ := l2_borel_decomp hb
  have hl : l ∈ Submonoid.powers γ := mem_powers_iff_mem_zpowers.mpr (hγ l)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff l γ).mp hl
  refine ⟨k, ?_⟩
  have hgk : l2DiagHom K γ ^ k = l2DiagHom K l := by rw [← hk, map_pow]
  rw [hgk]
  have h := l2_conj_mem_of_borel (inv_mem (l2DiagHom_mem_borel K l)) hu
  rw [inv_inv] at h
  rwa [← mul_assoc]

theorem l2_sylow_iso {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) {Y : Type} [Group Y] {X U : Subgroup Y}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U X)
    (e₀ : ↥X ≃* StatedProj (StatedSL 2 K)) :
    ∃ e : ↥X ≃* PSL2 K, (U.subgroupOf X).map e.toMonoidHom = psl2UpperUnipotentSubgroup K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (U.subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm
    · have h1 : ((U.subgroupOf X).subgroupOf ⊤).index = (U.subgroupOf X).index := by
        change (U.subgroupOf X).relIndex ⊤ = _
        exact Subgroup.relIndex_top_right _
      rw [h1]
      exact hU.2.2
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K hK
  have hR : CFSG.QuasithinUnique.IsSylowTwoOf (psl2UpperUnipotentSubgroup K) ⊤ := by
    rw [← hQ]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Q
  exact burnsideAut_exists_equiv_sylow
    (e₀.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm) hS hR

theorem l2_main_of_iso {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) {Y : Type} [Group Y] {X U : Subgroup Y}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U X) (e : ↥X ≃* PSL2 K)
    (he : (U.subgroupOf X).map e.toMonoidHom = psl2UpperUnipotentSubgroup K) :
    Nat.card ↥X = 2 ^ m * (4 ^ m - 1) ∧ Nat.card ↥U = 2 ^ m ∧
      Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) = 2 ^ m * (2 ^ m - 1) ∧
      IsCoatom ((X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X) ∧
      (∀ a ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        a * b * a⁻¹ * b⁻¹ ∈ U) ∧
      (∃ g ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ U) ∧
      ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y),
        ∃ j : ℕ, ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
          r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
  set S : Subgroup ↥X := U.subgroupOf X with hSdef
  set N : Subgroup ↥X := Subgroup.normalizer (S : Set ↥X) with hNdef
  set B : Subgroup Y := X ⊓ Subgroup.normalizer (U : Set Y) with hBdef
  have hBX : ∀ {b : Y}, b ∈ B → b ∈ X := fun hb => (Subgroup.mem_inf.mp hb).1
  have hBU : ∀ {b : Y}, b ∈ B → b ∈ Subgroup.normalizer (U : Set Y) :=
    fun hb => (Subgroup.mem_inf.mp hb).2
  have hsub : B.subgroupOf X = N := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : Y) ∈ Subgroup.normalizer (U : Set Y) := hBU hx
      rw [Subgroup.mem_normalizer_iff] at hx'
      rw [hNdef, Subgroup.mem_normalizer_iff]
      intro h
      rw [hSdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hx' (h : Y)
    · intro hx
      have hxN : x ∈ Subgroup.normalizer (S : Set ↥X) := hx
      have hx' : (x : Y) ∈ Subgroup.normalizer (U : Set Y) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        by_cases hh : h ∈ X
        · have key := (Subgroup.mem_normalizer_iff.mp hxN) ⟨h, hh⟩
          rw [hSdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
          simpa using key
        · have h1 : h ∉ U := fun h' => hh (hU.1 h')
          have h2 : (x : Y) * h * (x : Y)⁻¹ ∉ U := by
            intro h'
            apply hh
            have h'' : (x : Y) * h * (x : Y)⁻¹ ∈ X := hU.1 h'
            have hm := X.mul_mem (X.inv_mem x.2) (X.mul_mem h'' x.2)
            simpa [mul_assoc] using hm
          exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
      exact ⟨x.2, hx'⟩
  have hNB : N.map e.toMonoidHom = psl2Borel K := by
    rw [hNdef, Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) S e.bijective, he,
      psl2UpperUnipotent_normalizer_eq_borel]
  have hmemS : ∀ g : ↥X, g ∈ S ↔ e g ∈ psl2UpperUnipotentSubgroup K := by
    intro g
    rw [← he]
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
  have hmemN : ∀ g : ↥X, g ∈ N ↔ e g ∈ psl2Borel K := by
    intro g
    rw [← hNB]
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
  have hBN : ∀ g : ↥X, (g : Y) ∈ B ↔ g ∈ N := by
    intro g
    rw [← hsub]
    exact Subgroup.mem_subgroupOf.symm
  have hYU : ∀ g : ↥X, (g : Y) ∈ U ↔ e g ∈ psl2UpperUnipotentSubgroup K := by
    intro g
    rw [← hmemS]
    exact Subgroup.mem_subgroupOf.symm
  have hcardX : Nat.card ↥X = 2 ^ m * (4 ^ m - 1) := by
    have h4 : (4 : ℕ) ^ m = (2 ^ m) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [Nat.card_congr e.toEquiv, l2_psl2_card K, hK, h4]
  have hcardU : Nat.card ↥U = 2 ^ m := by
    have h1 : Nat.card ↥S = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv
    have h2 : Nat.card ↥(S.map e.toMonoidHom) = Nat.card ↥S :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [← h1, ← h2, he, psl2UpperUnipotentSubgroup_card, hK]
  have hcardB : Nat.card ↥B = 2 ^ m * (2 ^ m - 1) := by
    have h1 : Nat.card ↥(B.subgroupOf X) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ≤ X)).toEquiv
    have h2 : Nat.card ↥(N.map e.toMonoidHom) = Nat.card ↥N :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [← h1, hsub, ← h2, hNB, l2_psl2Borel_card K, hK]
  have hcoat : IsCoatom (B.subgroupOf X) := by
    rw [hsub]
    have h : IsCoatom (N.map e.toMonoidHom) := by
      rw [hNB]
      exact l2_psl2Borel_isCoatom K
    exact (OrderIso.isCoatom_iff e.mapSubgroup N).1 h
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ U := by
    intro a ha b hb
    have haX : a ∈ X := hBX ha
    have hbX : b ∈ X := hBX hb
    have hA : e ⟨a, haX⟩ ∈ psl2Borel K := (hmemN ⟨a, haX⟩).1 ((hBN ⟨a, haX⟩).1 ha)
    have hB' : e ⟨b, hbX⟩ ∈ psl2Borel K := (hmemN ⟨b, hbX⟩).1 ((hBN ⟨b, hbX⟩).1 hb)
    have hc := l2_borel_comm hA hB'
    have hmem : e (⟨a, haX⟩ * ⟨b, hbX⟩ * ⟨a, haX⟩⁻¹ * ⟨b, hbX⟩⁻¹) ∈
        psl2UpperUnipotentSubgroup K := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hc
    have := (hYU _).2 hmem
    simpa using this
  have hcyc : ∃ g ∈ B, ∀ b ∈ B, ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ U := by
    obtain ⟨g₀, hg₀, hcyc⟩ := l2_borel_cyclic K
    obtain ⟨g', hg'⟩ : ∃ g' : ↥X, e g' = g₀ := ⟨e.symm g₀, MulEquiv.apply_symm_apply e g₀⟩
    have hg'N : g' ∈ N := (hmemN g').2 (by rw [hg']; exact hg₀)
    refine ⟨(g' : Y), (hBN g').2 hg'N, fun b hb => ?_⟩
    obtain ⟨k, hk⟩ := hcyc (e ⟨b, hBX hb⟩) ((hmemN ⟨b, hBX hb⟩).1 ((hBN ⟨b, hBX hb⟩).1 hb))
    refine ⟨k, ?_⟩
    have hmem : e ((g' ^ k)⁻¹ * ⟨b, hBX hb⟩) ∈ psl2UpperUnipotentSubgroup K := by
      rw [map_mul, map_inv, map_pow, hg']
      exact hk
    have := (hYU _).2 hmem
    simpa using this
  have hconj : ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y),
      ∃ j : ℕ, ∀ b ∈ B, r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
    rintro r ⟨hrX, hrU⟩
    have hrX' : X.map (MulAut.conj r).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hrX
    let θ : ↥X ≃* ↥X :=
      (MulEquiv.subgroupMap (MulAut.conj r) X).trans (MulEquiv.subgroupCongr hrX')
    have hθ : ∀ x : ↥X, ((θ x : ↥X) : Y) = r * (x : Y) * r⁻¹ := fun x => rfl
    let α : MulAut (PSL2 K) := (e.symm.trans θ).trans e
    have hα : (psl2UpperUnipotentSubgroup K).map α.toMonoidHom = psl2UpperUnipotentSubgroup K := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨p, hp, rfl⟩
        have hs : e.symm p ∈ S := (hmemS (e.symm p)).2 (by rw [MulEquiv.apply_symm_apply]; exact hp)
        have hsU : ((e.symm p : ↥X) : Y) ∈ U := Subgroup.mem_subgroupOf.mp hs
        have hθU : ((θ (e.symm p) : ↥X) : Y) ∈ U := by
          rw [hθ]
          exact (Subgroup.mem_normalizer_iff.mp hrU _).1 hsU
        exact (hYU (θ (e.symm p))).1 hθU
      · exact le_of_eq (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).symm
    obtain ⟨j, hj⟩ := l2_model_action α hα
    refine ⟨j, fun b hb => ?_⟩
    have hb'N : (⟨b, hBX hb⟩ : ↥X) ∈ N := (hBN ⟨b, hBX hb⟩).1 hb
    have hmem := hj (e ⟨b, hBX hb⟩) ((hmemN ⟨b, hBX hb⟩).1 hb'N)
    have key : α (e ⟨b, hBX hb⟩) * (e ⟨b, hBX hb⟩ ^ 2 ^ j)⁻¹ =
        e (θ ⟨b, hBX hb⟩ * (⟨b, hBX hb⟩ ^ 2 ^ j)⁻¹) := by
      show e (θ (e.symm (e ⟨b, hBX hb⟩))) * (e ⟨b, hBX hb⟩ ^ 2 ^ j)⁻¹ = _
      rw [MulEquiv.symm_apply_apply, map_mul, map_inv, map_pow]
    rw [key] at hmem
    have h2 := (hYU _).2 hmem
    convert h2 using 1
    simp [hθ]
  exact ⟨hcardX, hcardU, hcardB, hcoat, hcomm, hcyc, hconj⟩

theorem l2BorelFacts_holds : L2BorelFacts := by
  intro m hm Y _ _ X U hX hU
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hX
  haveI : CharP K 2 := burnsideA26_charP_two hK
  obtain ⟨e, he⟩ := l2_sylow_iso hK hU e₀
  exact l2_main_of_iso hK hU e he

end CFSG.Quasithin.H13.P31X
