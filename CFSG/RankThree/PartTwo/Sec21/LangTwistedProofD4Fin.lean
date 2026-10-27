module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Rot
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Weyl
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Polynomial IntermediateField

theorem exists_finite_subfield_card_modEq_one {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k]
    [IsAlgClosed k] [CharP k p] (E : Finset k)
    (hE : letI := ZMod.algebra k p; ∀ x ∈ E, IsAlgebraic (ZMod p) x) {m : ℕ} (hm0 : 0 < m)
    (hm : p.Coprime m) :
    ∃ K : Subfield k, Finite K ∧ (E : Set k) ⊆ K ∧ Nat.card K ≡ 1 [MOD m] := by
  let := ZMod.algebra k p
  have hfix : ∀ x ∈ E, ∃ n, 0 < n ∧ x ^ p ^ n = x := by
    intro x hx
    have hint := (hE x hx).isIntegral
    have := IntermediateField.adjoin.finiteDimensional hint
    have : Finite (ZMod p)⟮x⟯ := Module.finite_of_finite (ZMod p)
    let : Fintype (ZMod p)⟮x⟯ := Fintype.ofFinite _
    refine ⟨Module.finrank (ZMod p) (ZMod p)⟮x⟯, Module.finrank_pos, ?_⟩
    have h1 := FiniteField.pow_card
      (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : (ZMod p)⟮x⟯)
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card] at h1
    simpa using congrArg Subtype.val h1
  choose! n hn0 hn using hfix
  set N := Nat.totient m * ∏ x ∈ E, n x with hN
  have hN0 : 0 < N := Nat.mul_pos (Nat.totient_pos.2 hm0)
    (Finset.prod_pos fun x hx => hn0 x hx)
  set q := p ^ N with hq
  have hq1 : 1 < q := Nat.one_lt_pow hN0.ne' hp.out.one_lt
  have hiter : ∀ (y : k) (a b : ℕ), y ^ p ^ a = y → y ^ p ^ (a * b) = y := by
    intro y a b h
    induction b with
    | zero => simp
    | succ b ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]
  set K : Subfield k := (iterateFrobenius k p N).eqLocusField (RingHom.id k) with hK
  have hmem : ∀ y, y ∈ K ↔ y ^ q = y := fun y => by
    change iterateFrobenius k p N y = y ↔ _
    rw [iterateFrobenius_def]
  have hroot : ∀ y : k, y ∈ (X ^ q - X : k[X]).rootSet k ↔ y ^ q = y := by
    intro y
    rw [mem_rootSet]
    simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
    exact ⟨fun h => h.2, fun h => ⟨FiniteField.X_pow_card_sub_X_ne_zero k hq1, h⟩⟩
  have hset : (K : Set k) = (X ^ q - X : k[X]).rootSet k :=
    Set.ext fun y => (hmem y).trans (hroot y).symm
  have hcard : Nat.card K = q := by
    have hsep : (X ^ q - X : k[X]).Separable := galois_poly_separable p q (dvd_pow_self p hN0.ne')
    have h1 := card_rootSet_eq_natDegree (K := k) hsep (IsAlgClosed.splits _)
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hq1] at h1
    rw [← h1, ← Nat.card_eq_fintype_card]
    change Nat.card ↥(K : Set k) = _
    rw [hset]
  refine ⟨K, Nat.finite_of_card_ne_zero (by omega), fun x hx => ?_, ?_⟩
  · rw [SetLike.mem_coe, hmem, hq, hN]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hx
    rw [hc, mul_left_comm]
    exact hiter x (n x) _ (hn x hx)
  · rw [hcard, hq, hN, pow_mul]
    simpa using (Nat.ModEq.pow_totient hm).pow (∏ x ∈ E, n x)

section TorusRot

variable {G : Type*} [Group G]

theorem pow_conj_mem {T : Subgroup G} {m : G} (hmT : ∀ t ∈ T, m * t * m⁻¹ ∈ T) (j : ℕ) {t : G}
    (ht : t ∈ T) : m ^ j * t * (m ^ j)⁻¹ ∈ T := by
  induction j generalizing t with
  | zero => simpa using ht
  | succ j ih =>
    have e : m ^ (j + 1) * t * (m ^ (j + 1))⁻¹ = m ^ j * (m * t * m⁻¹) * (m ^ j)⁻¹ := by
      rw [pow_succ]
      group
    rw [e]
    exact ih (hmT t ht)

@[expose] def torusRotSubgroup (T : Subgroup G) (m : G) (hm3 : m ^ 3 = 1)
    (hmT : ∀ t ∈ T, m * t * m⁻¹ ∈ T) : Subgroup G where
  carrier := {g | ∃ t ∈ T, ∃ j : ℕ, g = t * m ^ j}
  mul_mem' := by
    rintro _ _ ⟨t, ht, j, rfl⟩ ⟨t', ht', k, rfl⟩
    refine ⟨t * (m ^ j * t' * (m ^ j)⁻¹), mul_mem ht (pow_conj_mem hmT j ht'), j + k, ?_⟩
    rw [pow_add]
    group
  one_mem' := ⟨1, T.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨t, ht, j, rfl⟩
    refine ⟨m ^ (2 * j) * t⁻¹ * (m ^ (2 * j))⁻¹, pow_conj_mem hmT (2 * j) (inv_mem ht), 2 * j,
      ?_⟩
    have hmj : (m ^ j)⁻¹ = m ^ (2 * j) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hm3,
        one_pow]
    rw [mul_inv_rev, hmj]
    group

theorem eq_of_pow_mul_inv_mem {T : Subgroup G} {m : G} (hm1 : m ∉ T) (hm2 : m ^ 2 ∉ T)
    {i i' : ℕ} (hi : i < 3) (hi' : i' < 3) (h : m ^ i * (m ^ i')⁻¹ ∈ T) : i = i' := by
  interval_cases i <;> interval_cases i'
  · rfl
  · rw [pow_zero, pow_one, one_mul] at h
    exact absurd (inv_mem_iff.1 h) hm1
  · rw [pow_zero, one_mul] at h
    exact absurd (inv_mem_iff.1 h) hm2
  · rw [pow_zero, inv_one, mul_one, pow_one] at h
    exact absurd h hm1
  · rfl
  · have e : m ^ 1 * (m ^ 2)⁻¹ = m⁻¹ := by group
    rw [e] at h
    exact absurd (inv_mem_iff.1 h) hm1
  · rw [pow_zero, inv_one, mul_one] at h
    exact absurd h hm2
  · have e : m ^ 2 * (m ^ 1)⁻¹ = m := by group
    rw [e] at h
    exact absurd h hm1
  · rfl

theorem card_torusRotSubgroup (T : Subgroup G) (m : G) (hm3 : m ^ 3 = 1)
    (hmT : ∀ t ∈ T, m * t * m⁻¹ ∈ T) (hm1 : m ∉ T) (hm2 : m ^ 2 ∉ T) :
    Nat.card (torusRotSubgroup T m hm3 hmT) = 3 * Nat.card T := by
  let f : T × Fin 3 → torusRotSubgroup T m hm3 hmT := fun p =>
    ⟨p.1 * m ^ (p.2 : ℕ), p.1, p.1.2, p.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, i⟩ ⟨t', i'⟩ h
      have h' : (t : G) * m ^ (i : ℕ) = t' * m ^ (i' : ℕ) := congrArg Subtype.val h
      have hmem : m ^ (i : ℕ) * (m ^ (i' : ℕ))⁻¹ ∈ T := by
        have e : m ^ (i : ℕ) * (m ^ (i' : ℕ))⁻¹ = (t : G)⁻¹ * t' := by
          calc m ^ (i : ℕ) * (m ^ (i' : ℕ))⁻¹ =
              (t : G)⁻¹ * ((t : G) * m ^ (i : ℕ)) * (m ^ (i' : ℕ))⁻¹ := by group
            _ = (t : G)⁻¹ * ((t' : G) * m ^ (i' : ℕ)) * (m ^ (i' : ℕ))⁻¹ := by rw [h']
            _ = (t : G)⁻¹ * t' := by group
        rw [e]
        exact mul_mem (inv_mem t.2) t'.2
      have hii : i = i' := Fin.ext (eq_of_pow_mul_inv_mem hm1 hm2 i.2 i'.2 hmem)
      subst hii
      exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
    · rintro ⟨g, t, ht, j, rfl⟩
      refine ⟨(⟨t, ht⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩
      change t * m ^ (j % 3) = t * m ^ j
      conv_rhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, hm3, one_pow, mul_one]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, mul_comm]

theorem exists_fixed_of_iterate_three {α : Type*} [Finite α] {f : α → α}
    (hf : ∀ a, f (f (f a)) = a) (h3 : ¬ 3 ∣ Nat.card α) : ∃ a, f a = a := by
  set σ : Equiv.Perm α := ⟨f, f ∘ f, fun a => hf a, fun a => hf a⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    ext a
    simp [pow_succ, hσ, hf a]
  have hpg : IsPGroup 3 (Subgroup.zpowers σ) := by
    rintro ⟨g, j, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (σ ^ j) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3, one_zpow]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card α h3
  exact ⟨a, ha ⟨σ, Subgroup.mem_zpowers σ⟩⟩

end TorusRot

section Field

variable {K : Type} [Field K]

theorem d4RotElt_mem_normalizer :
    d4RotElt K ∈ Subgroup.normalizer
      (torusGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) := by
  have hn : ∀ w : WeylGroup TwistTag.D4.tag, canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈
      Subgroup.normalizer (torusGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) :=
    fun w => canonicalRep_mem_normalizer w
  have hs : ∀ i, weylElt TwistTag.D4.tag K i 1 ∈
      Subgroup.normalizer (torusGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) := by
    intro i
    rw [← canonicalRep_simple (coxeterSystem TwistTag.D4.tag) K i]
    exact hn _
  exact mul_mem (mul_mem (hn weylV) (mul_mem (hs 0) (hs 2))) (inv_mem (hn weylV))

theorem mapsRootLines_d4RotElt_pow (j : ℕ) : MapsRootLines (d4RotElt K ^ j) (weylU ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact mapsRootLines_one
  | succ j ih => rw [pow_succ, pow_succ]; exact ih.mul mapsRootLines_d4RotElt

theorem d4RotElt_pow_not_mem_torusGroup {j : ℕ} (hj : j = 1 ∨ j = 2) :
    d4RotElt K ^ j ∉ torusGroup TwistTag.D4.tag K := by
  intro hmem
  have hu := (mapsRootLines_d4RotElt_pow (K := K) j).unique (mapsRootLines_of_mem_torusGroup hmem)
  have h := congrArg (fun w => w⁻¹ • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ)) hu
  rcases hj with rfl | rfl
  · simp only [pow_one, weylU_inv_smul, inv_one, one_smul] at h
    exact absurd h (by decide)
  · simp only [pow_two, mul_inv_rev, mul_smul, weylU_inv_smul, inv_one, one_smul] at h
    exact absurd h (by decide)

theorem baseChangeGL_d4RotElt {L : Type} [Field L] (ι : K →+* L) :
    baseChangeGL ι (d4RotElt K) = d4RotElt L := by
  rw [d4RotElt, d4RotElt, map_mul, map_mul, map_mul, map_inv, baseChangeGL_canonicalRep,
    baseChangeGL_weylElt_one, baseChangeGL_weylElt_one]

theorem baseChangeGL_mem_torusGroup {L : Type} [Field L] (ι : K →+* L)
    {g : ModGL TwistTag.D4.tag K} (hg : g ∈ torusGroup TwistTag.D4.tag K) :
    baseChangeGL ι g ∈ torusGroup TwistTag.D4.tag L := by
  have hle : (torusGroup TwistTag.D4.tag K).map (baseChangeGL ι) ≤
      torusGroup TwistTag.D4.tag L := by
    rw [torusGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨⟨i, u⟩, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, baseChangeGL_torusElt]
    exact Subgroup.subset_closure ⟨(i, _), rfl⟩
  exact hle ⟨g, hg, rfl⟩

end Field

theorem exists_conj_torus_rot {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {x : ModGL TwistTag.D4.tag L} (hx : x ∈ adjointGroup TwistTag.D4.tag L)
    (h3 : (x * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1) :
    ∃ z ∈ adjointGroup TwistTag.D4.tag L, ∃ h ∈ torusGroup TwistTag.D4.tag L, ∃ j < 3,
      z * (x * (diagramMap TwistTag.D4 L)⁻¹) * z⁻¹ =
        h * (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹) := by
  classical
  let := ZMod.algebra L 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE⟩ := exists_finset_descent hx
  obtain ⟨K, hKfin, hEK, hKq⟩ := exists_finite_subfield_card_modEq_one (p := 2) E
    (fun z _ => Algebra.IsAlgebraic.isAlgebraic z) (m := 9) (by norm_num) (by norm_num)
  obtain ⟨y, hyC, hyx⟩ := hE K hEK
  set ι := K.subtype with hι
  have h2K : (2 : K) = 0 := by
    apply K.subtype_injective
    rw [map_ofNat, map_zero]
    exact CharP.cast_eq_zero L 2
  set P := diagramMap TwistTag.D4 K with hP
  have hP3 : P ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hy3 : (y * P⁻¹) ^ 3 = 1 := by
    apply baseChangeGL_injective ι
    rw [map_pow, map_mul, map_inv, hyx, hP, baseChangeGL_diagramMap, h3, map_one]
  set C := adjointGroup TwistTag.D4.tag K with hC
  set T := torusGroup TwistTag.D4.tag K with hT
  set m := d4RotElt K with hm
  have hmT : ∀ t ∈ T, m * t * m⁻¹ ∈ T := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 d4RotElt_mem_normalizer t).1 ht
  have hm3 : m ^ 3 = 1 := d4RotElt_pow_three h2K
  set N := torusRotSubgroup T m hm3 hmT with hN
  have hTC : T ≤ C :=
    (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
  have hmC : m ∈ C := d4RotElt_mem_adjointGroup
  have hNC : N ≤ C := by
    rintro _ ⟨t, ht, j, rfl⟩
    exact mul_mem (hTC ht) (pow_mem hmC j)
  have hm1 : m ∉ T := by
    have := d4RotElt_pow_not_mem_torusGroup (K := K) (j := 1) (Or.inl rfl)
    rwa [pow_one] at this
  have hm2 : m ^ 2 ∉ T := d4RotElt_pow_not_mem_torusGroup (K := K) (Or.inr rfl)
  have hcardN : Nat.card N = 3 * Nat.card T := card_torusRotSubgroup T m hm3 hmT hm1 hm2
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  set NC := N.subgroupOf C with hNCdef
  have hidx : ¬ 3 ∣ Nat.card (C ⧸ NC) := by
    set q := Nat.card K with hqdef
    set R := {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α}.ncard
    set S := ∑ᶠ w : WeylGroup TwistTag.D4.tag, q ^ (coxeterSystem TwistTag.D4.tag).length w
      with hS
    have h1 := Subgroup.card_mul_index NC
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, hcardN, card_adjointGroup]
      at h1
    have hT0 : 0 < Nat.card T := Nat.card_pos
    have h1' : 3 * Nat.card T * NC.index = Nat.card T * q ^ R * S := h1
    have hrel : 3 * NC.index = q ^ R * S := by
      apply Nat.eq_of_mul_eq_mul_left hT0
      rw [show Nat.card T * (3 * NC.index) = 3 * Nat.card T * NC.index by ring, h1']
      ring
    have hQI : Nat.card (C ⧸ NC) = NC.index := rfl
    rw [hQI]
    intro h3dvd
    have h9 : 9 ∣ q ^ R * S := by
      rw [← hrel]
      exact Nat.mul_dvd_mul_left 3 h3dvd
    have hcop : Nat.Coprime 9 (q ^ R) := by
      apply Nat.Coprime.pow_right
      have hq9 : q % 9 = 1 := hKq
      rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hq9]
      exact Nat.gcd_one_left 9
    have h9S : 9 ∣ S := hcop.dvd_of_dvd_mul_left h9
    have hSW : S ≡ Nat.card (WeylGroup TwistTag.D4.tag) [MOD 9] := by
      rw [← ZMod.natCast_eq_natCast_iff, hS, finsum_eq_sum_of_fintype, Nat.cast_sum]
      have hq1 : (q : ZMod 9) = 1 := by
        rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact hKq
      simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, Nat.card_eq_fintype_card]
    exact not_nine_dvd_card_weylGroup_D4 ((hSW.dvd_iff (dvd_refl 9)).1 h9S)
  have hPC : ∀ z ∈ C, P⁻¹ * z * P ∈ C := by
    intro z hz
    have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.D4 K (-1)) z hz
    rwa [zpow_neg_one, inv_inv] at hQ
  have hPT : ∀ t ∈ T, P⁻¹ * t * P ∈ T := by
    intro t ht
    have hmap := map_conj_diagramMap_torusGroup (k := K) TwistTag.D4
    have ht2 : t ∈ (torusGroup TwistTag.D4.tag K).map (MulAut.conj P).toMonoidHom := by
      rw [hmap]
      exact ht
    obtain ⟨t', ht', rfl⟩ := ht2
    have e : P⁻¹ * ((MulAut.conj P).toMonoidHom t') * P = t' := by
      change P⁻¹ * (P * t' * P⁻¹) * P = t'
      group
    rw [e]
    exact ht'
  have hPm : ∀ j : ℕ, P⁻¹ * m ^ j * P = m ^ j := by
    intro j
    have hc : P * m = m * P := diagramMap_commute_d4RotElt h2K
    have hcj : P * m ^ j = m ^ j * P := ((Commute.pow_right hc j)).eq
    calc P⁻¹ * m ^ j * P = P⁻¹ * (m ^ j * P) := by group
      _ = P⁻¹ * (P * m ^ j) := by rw [hcj]
      _ = m ^ j := by group
  let γ : C → C := fun z => ⟨P⁻¹ * (z : ModGL TwistTag.D4.tag K) * P, hPC z z.2⟩
  have hγ : ∀ z : C, ((γ z : C) : ModGL TwistTag.D4.tag K) = P⁻¹ * z * P := fun z => rfl
  have hγmul : ∀ a b : C, γ (a * b) = γ a * γ b := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, hγ, hγ, hγ, Subgroup.coe_mul]
    group)
  have hγinv : ∀ a : C, γ a⁻¹ = (γ a)⁻¹ := fun a => Subtype.ext (by
    rw [Subgroup.coe_inv, hγ, hγ, Subgroup.coe_inv]
    group)
  have hγN : ∀ a : C, a ∈ NC → γ a ∈ NC := by
    intro a ha
    rw [hNCdef, Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨t, ht, j, hj⟩ := ha
    refine ⟨P⁻¹ * t * P, hPT t ht, j, ?_⟩
    rw [hγ, hj]
    calc P⁻¹ * (t * m ^ j) * P = (P⁻¹ * t * P) * (P⁻¹ * m ^ j * P) := by group
      _ = _ := by rw [hPm]
  set y' : C := ⟨y, hyC⟩ with hy'
  have hy'c : (y' : ModGL TwistTag.D4.tag K) = y := rfl
  let Φ : C ⧸ NC → C ⧸ NC := Quotient.map' (fun z => y' * γ z) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← hγinv, ← hγmul]
    exact hγN _ hab)
  have hΦ : ∀ z : C, Φ (z : C ⧸ NC) = ((y' * γ z : C) : C ⧸ NC) := fun z => rfl
  have hγ3 : ∀ z : C, γ (γ (γ z)) = z := fun z => Subtype.ext (by
    rw [hγ, hγ, hγ]
    calc P⁻¹ * (P⁻¹ * (P⁻¹ * (z : ModGL TwistTag.D4.tag K) * P) * P) * P =
        (P ^ 3)⁻¹ * z * P ^ 3 := by rw [pow_three]; group
      _ = z := by rw [hP3, inv_one, one_mul, mul_one])
  have hyγ : y' * γ y' * γ (γ y') = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hγ, hγ, hγ, Subgroup.coe_one, hy'c]
    calc y * (P⁻¹ * y * P) * (P⁻¹ * (P⁻¹ * y * P) * P) =
        (y * P⁻¹) ^ 3 * P ^ 3 := by rw [pow_three, pow_three]; group
      _ = 1 := by rw [hy3, hP3, one_mul])
  have hΦ3 : ∀ q, Φ (Φ (Φ q)) = q := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hΦ, hΦ, hΦ, hγmul, hγmul, hγmul, hγ3]
    congr 1
    calc y' * (γ y' * (γ (γ y') * z)) = (y' * γ y' * γ (γ y')) * z := by group
      _ = z := by rw [hyγ, one_mul]
  obtain ⟨q, hq⟩ := exists_fixed_of_iterate_three hΦ3 hidx
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  rw [hΦ, QuotientGroup.eq] at hq
  have hzN : z⁻¹ * (y' * γ z) ∈ NC := by
    have := inv_mem hq
    rwa [mul_inv_rev, inv_inv] at this
  rw [hNCdef, Subgroup.mem_subgroupOf] at hzN
  obtain ⟨t, ht, j, hj⟩ := hzN
  have hj' : (z : ModGL TwistTag.D4.tag K)⁻¹ * (y * P⁻¹) * z = t * (m ^ (j % 3) * P⁻¹) := by
    have hmj : m ^ (j % 3) = m ^ j := by
      conv_rhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, hm3, one_pow, mul_one]
    have e : ((z⁻¹ * (y' * γ z) : C) : ModGL TwistTag.D4.tag K) =
        (z : ModGL TwistTag.D4.tag K)⁻¹ * y * (P⁻¹ * z * P) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hγ, hy'c]
      group
    rw [e] at hj
    rw [hmj]
    calc (z : ModGL TwistTag.D4.tag K)⁻¹ * (y * P⁻¹) * z =
        ((z : ModGL TwistTag.D4.tag K)⁻¹ * y * (P⁻¹ * z * P)) * P⁻¹ := by group
      _ = t * (m ^ j * P⁻¹) := by rw [hj]; group
  refine ⟨baseChangeGL ι (z : ModGL TwistTag.D4.tag K)⁻¹,
    baseChangeGL_mem_adjointGroup ι (inv_mem z.2), baseChangeGL ι t,
    baseChangeGL_mem_torusGroup ι ht, j % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  have hL := congrArg (baseChangeGL ι) hj'
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hyx, hP,
    baseChangeGL_diagramMap, hm, baseChangeGL_d4RotElt] at hL
  rw [← hL, map_inv, inv_inv]

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
