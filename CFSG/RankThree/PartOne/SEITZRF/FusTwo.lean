module

public import CFSG.RankThree.PartOne.SEITZRF.Defs
public import Certificates.Certificate14948
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
import CFSG.RankThree.SteinbergR3ELargeReeOrder

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Chevalley.RootOps (orbitCertRoot)

namespace FusTwo

section Bits

variable {K : Type} [Field K]

variable (K) in
@[expose] def castBits (l : List Bool) : Fin 12 → K := fun i => if bit l i then 1 else 0

theorem monoEval_bits (l : List Bool) (m : Mono) :
    monoEval (fun v => if varBit l v then (1 : K) else 0) m =
      if m.all (varBit l) then 1 else 0 := by
  induction m with
  | nil => simp [monoEval_nil]
  | cons v m ih =>
    rw [monoEval_cons, ih, List.all_cons]
    cases varBit l v <;> cases m.all (varBit l) <;> simp

theorem polyBit_cons (l : List Bool) (m : Mono) (p : Poly) :
    polyBit l (m :: p) = if m.all (varBit l) then !polyBit l p else polyBit l p := by
  unfold polyBit
  rw [List.filter_cons]
  by_cases h : m.all (varBit l) = true
  · simp only [h, ite_true, List.length_cons]
    rcases Nat.mod_two_eq_zero_or_one (p.filter fun m => m.all (varBit l)).length with h0 | h0
    · simp [Nat.add_mod, h0]
    · simp [Nat.add_mod, h0]
  · simp [h]

theorem polyEval_bits [CharP K 2] (l : List Bool) (p : Poly) :
    polyEval (fun v => if varBit l v then (1 : K) else 0) p = if polyBit l p then 1 else 0 := by
  induction p with
  | nil => simp [polyEval_nil, polyBit]
  | cons m p ih =>
    rw [polyEval_cons, ih, monoEval_bits, polyBit_cons]
    cases m.all (varBit l) <;> cases polyBit l p <;> simp [CharTwo.add_self_eq_zero]

end Bits

section Coord

variable {K : Type} [Field K]

omit [Field K] in
theorem largeReeSigma_ite {K : Type} [Field K] (m : ℕ) (b : Bool) :
    largeReeSigma m (if b then (1 : K) else 0) = if b then 1 else 0 := by
  cases b <;> simp [largeReeSigma_zero, largeReeSigma_one]

theorem coordVal_castBits (m : ℕ) (l : List Bool) :
    coordVal m (castBits K l 0) (castBits K l 1) (castBits K l 2) (castBits K l 3)
      (castBits K l 4) (castBits K l 5) (castBits K l 6) (castBits K l 7) (castBits K l 8)
      (castBits K l 9) (castBits K l 10) (castBits K l 11) =
      fun v => if varBit l v then (1 : K) else 0 := by
  funext v
  by_cases hv : v < 24
  · interval_cases v <;> simp [coordVal, varBit, castBits, bit, largeReeSigma_ite]
  · obtain ⟨k, rfl⟩ : ∃ k, v = k + 24 := ⟨v - 24, by omega⟩
    have h1 : varBit l (k + 24) = false := by simp [varBit]
    have h2 : coordVal m (castBits K l 0) (castBits K l 1) (castBits K l 2) (castBits K l 3)
        (castBits K l 4) (castBits K l 5) (castBits K l 6) (castBits K l 7) (castBits K l 8)
        (castBits K l 9) (castBits K l 10) (castBits K l 11) (k + 24) = 0 := rfl
    rw [h1, h2]
    simp

variable [CharP K F4.prime] {a : ℕ}

theorem sylowVec_castBits (l : List Bool) :
    sylowVec a K (castBits K l) = wordEval K (fun _ => 0) (vWord l) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [vWord, wordEval_filter]
  change sylowV a K (castBits K l 0) (castBits K l 1) (castBits K l 2) (castBits K l 3)
    (castBits K l 4) (castBits K l 5) (castBits K l 6) (castBits K l 7) (castBits K l 8)
    (castBits K l 9) (castBits K l 10) (castBits K l 11) = _
  rw [sylowV_eq_wordEval, coordVal_castBits]
  simp only [wordEval, List.map_map]
  congr 1
  refine List.map_congr_left fun f _ => ?_
  have h0 : ∀ b : Bool, polyEval (fun _ : ℕ => (0 : K)) (constPoly b) = if b then 1 else 0 := by
    intro b
    cases b <;> simp [constPoly, polyEval, monoEval]
  simp only [Function.comp_apply, h0, polyEval_bits]

end Coord

section Collect

variable {R : Type} [CommRing R] [CharP R 2]

theorem wordEval_eq_of_collEq {w w' : Word} (h : collEq w w' = true) (x : ℕ → R) :
    wordEval R x w = wordEval R x w' := by
  simp only [collEq, posOK, Bool.and_eq_true, List.all_eq_true, Nat.ble_eq, beq_iff_eq] at h
  obtain ⟨⟨hw, hw'⟩, hc⟩ := h
  have h1 := wordEval_collect x 500 [] w (by simp) hw
  have h2 := wordEval_collect x 500 [] w' (by simp) hw'
  rw [List.reverse_nil, List.nil_append] at h1 h2
  rw [← h1, ← h2, hc]

end Collect

theorem mem_of_lookup {pairs : List (ℕ × ℕ)} {r r' : ℕ} (h : pairs.lookup r = some r') :
    (r, r') ∈ pairs := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

section Edges

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime] in
theorem conj_wordEval (n : ModGL F4.tag K) (pairs : List (ℕ × ℕ))
    (hn : ∀ r r', pairs.lookup r = some r' → ∀ c : K,
      n * sylowX K r c * n⁻¹ = sylowX K r' c) (x : ℕ → K) :
    ∀ w : Word, (∀ f ∈ w, (pairs.lookup f.1).isSome = true) →
      n * wordEval K x w * n⁻¹ = wordEval K x (relabel pairs w)
  | [], _ => by simp [wordEval_nil, relabel]
  | f :: w, h => by
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (h f List.mem_cons_self)
    have ih := conj_wordEval n pairs hn x w (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hx := hn f.1 r' hr' (polyEval x f.2)
    have e : relabel pairs (f :: w) = (r', f.2) :: relabel pairs w := by
      simp [relabel, hr']
    rw [e, wordEval_cons, wordEval_cons]
    have e2 : n * (pinnedX F4.tag K (orbitCertRoot F4.tag f.1) (polyEval x f.2) *
        wordEval K x w) * n⁻¹ = (n * sylowX K f.1 (polyEval x f.2) * n⁻¹) *
          (n * wordEval K x w * n⁻¹) := by
      simp only [sylowX]
      group
    rw [e2, hx, ih]
    rfl

variable (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)

include hK in
theorem sylowVec_castBits_mem_Rf (l : List Bool) : sylowVec a K (castBits K l) ∈ Rf K a β := by
  refine (sylowVec_mem_Rf_iff hK β _).2 fun i => ?_
  unfold castBits
  split_ifs <;> simp

include hK in
theorem edgeCheck_sound {e : Edge} (h : edgeCheck e = true) :
    ∃ g ∈ Rf K a β, sylowVec a K (castBits K e.1) =
      g * sylowVec a K (castBits K e.2.1) * g⁻¹ := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨c, p, i⟩ := e
  simp only [edgeCheck] at h
  split_ifs at h with h1 h2 h3
  · refine ⟨sylowVec a K (castBits K (unitBits i)), sylowVec_castBits_mem_Rf hK β _, ?_⟩
    have h4 := wordEval_eq_of_collEq (R := K) h (fun _ => 0)
    rw [wordEval_append, wordEval_append, ← sylowVec_castBits, ← sylowVec_castBits,
      ← sylowVec_castBits] at h4
    exact eq_mul_inv_of_mul_eq h4
  · obtain ⟨h4, h5⟩ := Bool.and_eq_true_iff.1 h
    refine ⟨weylOne K, weylOne_mem_Rf β, ?_⟩
    have h6 := conj_wordEval (weylOne K) pairsOne
      (fun r r' hr c => weylOne_conj_sylowX (mem_of_lookup hr) c) (fun _ => 0) (vWord p)
      (List.all_eq_true.1 h4)
    have h7 := wordEval_eq_of_collEq (R := K) h5 (fun _ => 0)
    simp only at h6 h7 ⊢
    rw [sylowVec_castBits, sylowVec_castBits, h6, h7]
  · obtain ⟨h4, h5⟩ := Bool.and_eq_true_iff.1 h
    refine ⟨weylTwo K, weylTwo_mem_Rf β, ?_⟩
    have h6 := conj_wordEval (weylTwo K) pairsTwo
      (fun r r' hr c => weylTwo_conj_sylowX (mem_of_lookup hr) c) (fun _ => 0) (vWord p)
      (List.all_eq_true.1 h4)
    have h7 := wordEval_eq_of_collEq (R := K) h5 (fun _ => 0)
    simp only at h6 h7 ⊢
    rw [sylowVec_castBits, sylowVec_castBits, h6, h7]

variable (K a) in
@[expose] def Fusible (β : K ≃+* K) (l : List Bool) : Prop :=
  ∃ r ∈ Rf K a β, r * sylowVec a K (castBits K l) * r⁻¹ = centralZ K a 1 ∨
    r * sylowVec a K (castBits K l) * r⁻¹ = sylowL a K 1

include hK in
theorem forestCheck_fusible : ∀ (es : List Edge) (known : List (List Bool)),
    forestCheck es known = true → (∀ k ∈ known, Fusible K a β k) →
      ∀ e ∈ es, Fusible K a β e.1
  | [], _, _, _, e, he => absurd he List.not_mem_nil
  | e :: es, known, h, hknown, e', he' => by
    simp only [forestCheck, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨g, hg, hge⟩ := edgeCheck_sound hK β h2
    obtain ⟨r, hr, hrz⟩ := hknown e.2.1 (List.mem_of_elem_eq_true h1)
    have hfe : Fusible K a β e.1 := by
      refine ⟨r * g⁻¹, (Rf K a β).mul_mem hr ((Rf K a β).inv_mem hg), ?_⟩
      have e1 : r * g⁻¹ * sylowVec a K (castBits K e.1) * (r * g⁻¹)⁻¹ =
          r * sylowVec a K (castBits K e.2.1) * r⁻¹ := by
        rw [hge]
        group
      rw [e1]
      exact hrz
    have ih := forestCheck_fusible es (e.1 :: known) h3 (by
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hfe
      · exact hknown k hk)
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hfe
    · exact ih e' he'

end Edges

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [CharP K F4.prime] in
theorem fixed_eq_zero_or_one {β : K ≃+* K} (hk : Nat.card (fixSubfield β) = 2) {c : K}
    (hc : β c = c) : c = 0 ∨ c = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  have : Finite (fixSubfield β) := Subtype.finite
  let f : Fin 3 → fixSubfield β := ![0, 1, ⟨c, (mem_fixSubfield (σ := β)).2 hc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢
    all_goals first | exact absurd hij.symm h0 | exact absurd hij h0 | exact absurd hij.symm h1 |
      exact absurd hij h1
  have := Nat.card_le_card_of_injective f hf
  rw [hk] at this
  simp at this

variable (K a) in
@[expose] def Ssub (β : K ≃+* K) : Subgroup (ModGL F4.tag K) :=
  Rf K a β ⊓ F4.reeFixedPosUnipotent K a

@[expose] def toSsub (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    (ξ : Fin 12 → fixSubfield β) : Ssub K a β :=
  ⟨sylowVec a K (fun i => (ξ i : K)),
    ⟨(sylowVec_mem_Rf_iff hK β _).2 fun i => (mem_fixSubfield (σ := β)).1 (ξ i).2,
      (bijOn_sylowVec hK).1 (Set.mem_univ _)⟩⟩

theorem coe_toSsub (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    (ξ : Fin 12 → fixSubfield β) :
    (toSsub hK β ξ : ModGL F4.tag K) = sylowVec a K (fun i => (ξ i : K)) :=
  rfl

theorem card_Ssub (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    (hk : Nat.card (fixSubfield β) = 2) : Nat.card (Ssub K a β) = 2 ^ 12 := by
  have : Finite (fixSubfield β) := Subtype.finite
  have hf : Function.Bijective (toSsub hK β) := by
    constructor
    · intro ξ ξ' h
      have h0 := congrArg Subtype.val h
      rw [coe_toSsub, coe_toSsub] at h0
      have h1 := (bijOn_sylowVec hK).injOn (Set.mem_univ (fun i => (ξ i : K)))
        (Set.mem_univ (fun i => (ξ' i : K))) h0
      funext i
      exact Subtype.ext (congrFun h1 i)
    · rintro ⟨s, hsR, hsU⟩
      obtain ⟨ξ, -, hξ⟩ := (bijOn_sylowVec hK).2.2 hsU
      have hfix := (sylowVec_mem_Rf_iff hK β ξ).1 (hξ ▸ hsR)
      exact ⟨fun i => ⟨ξ i, (mem_fixSubfield (σ := β)).2 (hfix i)⟩, Subtype.ext hξ⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hf), Nat.card_fun, hk, Nat.card_eq_fintype_card,
    Fintype.card_fin]

omit [CharP K F4.prime] [Finite K] in
theorem factorization_two_card : (2 ^ 12 * 8775 : ℕ).factorization 2 = 12 := by
  rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 8775)]

theorem exists_conj_mem_Ssub (β : K ≃+* K) (hcard : Nat.card (Rf K a β) = 2 ^ 12 * 8775)
    (hS : Nat.card (Ssub K a β) = 2 ^ 12) {x : ModGL F4.tag K} (hx : x ∈ Rf K a β)
    (hx2 : x ^ 2 = 1) : ∃ g ∈ Rf K a β, g⁻¹ * x * g ∈ Ssub K a β := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Ssub K a β ≤ Rf K a β := inf_le_left
  have : Finite ↥(Rf K a β) := Subtype.finite
  have hS' : Nat.card ((Ssub K a β).subgroupOf (Rf K a β)) =
      2 ^ (Nat.card ↥(Rf K a β)).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hS, hcard,
      factorization_two_card]
  let P0 : Sylow 2 ↥(Rf K a β) := Sylow.ofCard _ hS'
  let x' : ↥(Rf K a β) := ⟨x, hx⟩
  have hx'2 : x' ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  have hP : IsPGroup 2 (Subgroup.zpowers x') := by
    rintro ⟨y, hy⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h : (x' ^ m) ^ (2 ^ 1) = 1 := by
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'2, one_zpow]
    simpa using h
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Rf K a β) P0 Q
  have hxQ : x' ∈ (Q : Subgroup ↥(Rf K a β)) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  refine ⟨g, g.2, ?_⟩
  have h1 : g⁻¹ * x' * g ∈ (P0 : Subgroup ↥(Rf K a β)) := by
    simpa [MulAut.conj_apply] using hxQ
  have h2 := (Subgroup.mem_subgroupOf).1 h1
  simpa using h2

end Sylow

section Order

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem card_Rf_two_odd (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hβ : orderOf β = p) (hk : Nat.card (fixSubfield β) = 2) :
    Nat.card (Rf K a β) = 2 ^ 12 * 8775 := by
  obtain ⟨b, -, hb, hfix⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 β hβ
  have hb0 : b = 0 := by
    rw [hk] at hb
    have h1 := Nat.pow_right_injective (le_refl 2) (hb.symm.trans (pow_one 2).symm)
    omega
  subst hb0
  have : Finite (fixSubfield β) := Subtype.finite
  have : CharP (fixSubfield β) F4.prime := by
    have : Fintype (fixSubfield β) := Fintype.ofFinite _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hk]; rfl)
  have hSe : CFSG.RankThree.PartOne.CTP.fixedSubgroup (F4.reeGammaFieldAut K a β) =
      (F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  have hRcard : Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup
      (F4.reeGammaFieldAut K a β)) = Nat.card (F4.reeGamma (fixSubfield β) 0) := by
    rw [← Subgroup.card_map_of_injective (f := (F4.reeGamma K a).subtype) Subtype.val_injective,
      ← Subgroup.card_map_of_injective (f := baseChangeGL (fixSubfield β).subtype)
        (K := F4.reeGamma (fixSubfield β) 0) (baseChangeGL_injective _), hSe, hfix]
  have hRf : Nat.card (Rf K a β) = Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup
      (F4.reeGammaFieldAut K a β)) := by
    rw [← map_fixedSubgroup_eq_Rf]
    exact Subgroup.card_map_of_injective Subtype.val_injective
  have horder :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      0 (fixSubfield β) hk).1
  rw [hRf, hRcard, horder]
  norm_num

end Order

section Roots

variable {K : Type} [Field K] [CharP K F4.prime] {a : ℕ}

omit [CharP K F4.prime] in
theorem centralZ_one_eq_sylowVec : centralZ K a 1 = sylowVec a K (Pi.single 8 1) := by
  rw [← sylowH_zero_eq_centralZ]
  simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

omit [CharP K F4.prime] in
theorem sylowL_one_eq_sylowVec : sylowL a K 1 = sylowVec a K (Pi.single 11 1) := by
  simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowX,
    largeReeSigma_zero, pinnedX_zero]

omit [CharP K F4.prime] in
theorem sylowVec_zero_eq_one : sylowVec a K 0 = 1 := by
  simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

omit [CharP K F4.prime] in
theorem castBits_zBits : castBits K zBits = Pi.single 8 1 := by
  funext i
  fin_cases i <;> simp [castBits, zBits, unitBits, bit]

omit [CharP K F4.prime] in
theorem castBits_tBits : castBits K tBits = Pi.single 11 1 := by
  funext i
  fin_cases i <;> simp [castBits, tBits, unitBits, bit]

end Roots

theorem mem_bitLists : ∀ (n : ℕ) (l : List Bool), l.length = n → l ∈ bitLists n
  | 0, [], _ => by simp [bitLists]
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, b :: l, h => by
    have := mem_bitLists n l (by simpa using h)
    simp only [bitLists, List.mem_flatMap]
    exact ⟨l, this, by cases b <;> simp⟩

end FusTwo

open FusTwo in
theorem exists_conj_of_involution_Rf_two_odd
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hβ : orderOf β = p)
    (hk : Nat.card (CFSG.LieType.Chevalley.fixSubfield β) = 2) {x : ModGL F4.tag K}
    (hx : x ∈ Rf K a β) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ r ∈ Rf K a β, r * x * r⁻¹ = centralZ K a 1 ∨ r * x * r⁻¹ = sylowL a K 1 := by
  classical
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨g, hg, hgS⟩ := exists_conj_mem_Ssub β (card_Rf_two_odd hK β hp hp2 hβ hk)
    (card_Ssub hK β hk) hx hx2
  set y : ModGL F4.tag K := g⁻¹ * x * g with hy
  have hy2 : y ^ 2 = 1 := by
    have h : y ^ 2 = g⁻¹ * x ^ 2 * g := by
      rw [hy]
      simp only [pow_two]
      group
    rw [h, hx2]
    group
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    have h' : x = g * y * g⁻¹ := by rw [hy]; group
    rw [h', h]
    group
  obtain ⟨hyR, hyU⟩ := Subgroup.mem_inf.1 hgS
  obtain ⟨ξ, -, hξ⟩ := (bijOn_sylowVec hK).2.2 hyU
  have hfix := (sylowVec_mem_Rf_iff hK β ξ).1 (hξ ▸ hyR)
  let l : List Bool := List.ofFn fun i : Fin 12 => decide (ξ i = 1)
  have hbit : ∀ i : Fin 12, bit l i = decide (ξ i = 1) := fun i => by
    fin_cases i <;> rfl
  have hξl : ξ = castBits K l := by
    funext i
    unfold castBits
    rw [hbit i]
    rcases fixed_eq_zero_or_one hk (hfix i) with h | h <;> simp [h]
  have hsq : sylowVec a K (castBits K l) ^ 2 = 1 := by rw [← hξl, hξ]; exact hy2
  have hinv : isInvol l = true := by
    have h24 := (sylowV_sq_eq_one_iff (m := a) (castBits K l 0) (castBits K l 1) (castBits K l 2)
      (castBits K l 3) (castBits K l 4) (castBits K l 5) (castBits K l 6) (castBits K l 7)
      (castBits K l 8) (castBits K l 9) (castBits K l 10) (castBits K l 11)).1 hsq
    rw [coordVal_castBits] at h24
    unfold isInvol
    rw [List.all_eq_true]
    intro n hn
    have h25 := h24 ⟨n, List.mem_range.1 hn⟩
    rw [polyEval_bits] at h25
    cases hb : polyBit l (sqCoords.getD n []) <;> simp_all
  have hl0 : (l.all fun b => b == false) = false := by
    by_contra h
    simp only [Bool.not_eq_false] at h
    have h0 : castBits K l = 0 := by
      funext i
      have hb : bit l i = false := by
        unfold bit
        rw [List.getD_eq_getElem?_getD]
        cases hli : l[(i : ℕ)]? with
        | none => rfl
        | some b =>
          have hmem : b ∈ l := List.mem_of_getElem? hli
          have := (List.all_eq_true.1 h) b hmem
          simpa using this
      simp [castBits, hb]
    apply hy1
    rw [← hξ, hξl, h0]
    exact sylowVec_zero_eq_one
  have hz : Fusible K a β zBits := ⟨1, (Rf K a β).one_mem, Or.inl (by
    rw [castBits_zBits, ← centralZ_one_eq_sylowVec]; group)⟩
  have ht : Fusible K a β tBits := ⟨1, (Rf K a β).one_mem, Or.inr (by
    rw [castBits_tBits, ← sylowL_one_eq_sylowVec]; group)⟩
  have hroots : ∀ k ∈ [zBits, tBits], Fusible K a β k := by
    intro k hk'
    rcases List.mem_cons.1 hk' with rfl | hk'
    · exact hz
    · rcases List.mem_cons.1 hk' with rfl | hk'
      · exact ht
      · exact absurd hk' List.not_mem_nil
  obtain ⟨hforest, hcover⟩ := Certificates.certificate14948
  have hfus : Fusible K a β l := by
    have hl12 : l ∈ bitLists 12 := mem_bitLists 12 l (by simp [l])
    have hc := List.all_eq_true.1 hcover l hl12
    simp only [hinv, hl0, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
      List.any_eq_true] at hc
    rcases hc with (hc | hc) | ⟨e, he, hel⟩
    · exact hc ▸ hz
    · exact hc ▸ ht
    · exact hel ▸ forestCheck_fusible hK β fusEdges [zBits, tBits] hforest hroots e he
  obtain ⟨r, hr, hrz⟩ := hfus
  refine ⟨r * g⁻¹, (Rf K a β).mul_mem hr ((Rf K a β).inv_mem hg), ?_⟩
  have e : r * g⁻¹ * x * (r * g⁻¹)⁻¹ = r * sylowVec a K (castBits K l) * r⁻¹ := by
    rw [← hξl, hξ, hy]
    group
  rw [e]
  exact hrz

end CFSG.RankThree.PartOne.SEITZRF