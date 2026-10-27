module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofWeyl
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofOutWeyl

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_prime_pow_of_card_eq_cube {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 3) : ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ q = ℓ ^ f := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hq : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q (by norm_num)
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hq
  refine ⟨ringChar K, f, hp, ?_, hf⟩
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · exfalso
    rw [h0, pow_zero] at hf
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hK, hf] at h2
    norm_num at h2
  · exact h0

theorem prime_pow_cases {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h3 : ¬ 3 ∣ ℓ ^ f) :
    ℓ ^ f = 2 ∨ ℓ ^ f = 4 ∨ ℓ ^ f = 5 ∨ 7 ≤ ℓ ^ f := by
  have h2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have h6 : ℓ ^ f ≠ 6 := by
    intro h
    have h2d : 2 ∣ ℓ ^ f := by rw [h]; norm_num
    have h3d : 3 ∣ ℓ ^ f := by rw [h]; norm_num
    exact h3 h3d
  have h3' : ℓ ^ f ≠ 3 := fun h => h3 (by rw [h])
  omega

theorem eq_or_eq_of_pow_three {G : Type*} [Group G] [Finite G] [IsCyclic G] {σ δ : G}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hδ3 : δ ^ 3 = 1) : δ = 1 ∨ δ = σ ∨ δ = σ ^ 2 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hσ2 : σ ^ 2 ≠ 1 := by
    intro h
    apply hσ1
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ3, h]; group
  have hσσ2 : σ ≠ σ ^ 2 := by
    intro h
    apply hσ1
    calc σ = σ ^ 2 * σ⁻¹ := by group
      _ = 1 := by rw [← h]; group
  have hsub : ({1, σ, σ ^ 2, δ} : Finset G) ⊆ Finset.univ.filter fun a => a ^ 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
    · exact hδ3
  have hA : (1 : G) ∉ ({σ, σ ^ 2, δ} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσ1 h.symm, fun h => hσ2 h.symm, fun h => h1 h.symm⟩
  have hB : σ ∉ ({σ ^ 2, δ} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hσσ2, fun h => h2 h.symm⟩
  have hC : σ ^ 2 ≠ δ := fun h => h3 h.symm
  have hcard : ({1, σ, σ ^ 2, δ} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB, Finset.card_pair hC]
  have hle := Finset.card_le_card hsub
  have hcyc := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  omega

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def hoElt (σ : K ≃+* K) (u : Kˣ) : ModGL TwistTag.D4.tag K :=
  torusElt TwistTag.D4.tag K n0 u * torusElt TwistTag.D4.tag K n1
    (Units.map σ.toRingHom.toMonoidHom u) * torusElt TwistTag.D4.tag K n3
      (Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom u))

theorem hoElt_mem_torusGroup (σ : K ≃+* K) (u : Kˣ) :
    hoElt σ u ∈ torusGroup TwistTag.D4.tag K :=
  mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
    (torusElt_mem_torusGroup _ _)

theorem entrywise_hoElt (σ δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c)) (u : Kˣ) :
    Units.map (entrywiseHom δ.toRingHom) (hoElt σ u) =
      hoElt σ (Units.map δ.toRingHom.toMonoidHom u) := by
  have e1 : Units.map δ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom u) =
      Units.map σ.toRingHom.toMonoidHom (Units.map δ.toRingHom.toMonoidHom u) :=
    Units.ext (by simp [hδσ])
  have e2 : Units.map δ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom
      (Units.map σ.toRingHom.toMonoidHom u)) = Units.map σ.toRingHom.toMonoidHom
        (Units.map σ.toRingHom.toMonoidHom (Units.map δ.toRingHom.toMonoidHom u)) :=
    Units.ext (by simp [hδσ])
  rw [hoElt, map_mul, map_mul, LieType.Chevalley.entrywise_torusElt,
    LieType.Chevalley.entrywise_torusElt, LieType.Chevalley.entrywise_torusElt, hoElt]
  change torusElt TwistTag.D4.tag K n0 (Units.map δ.toRingHom.toMonoidHom u) *
      torusElt TwistTag.D4.tag K n1 (Units.map δ.toRingHom.toMonoidHom
        (Units.map σ.toRingHom.toMonoidHom u)) *
      torusElt TwistTag.D4.tag K n3 (Units.map δ.toRingHom.toMonoidHom
        (Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom u))) = _
  rw [e1, e2]

theorem hoElt_eq_rootDiagUnit (σ : K ≃+* K) (u : Kˣ) :
    hoElt σ u = rootDiagUnit TwistTag.D4.tag (fun j => u ^ TwistTag.D4.tag.cartan n0 j *
      Units.map σ.toRingHom.toMonoidHom u ^ TwistTag.D4.tag.cartan n1 j *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom u) ^
        TwistTag.D4.tag.cartan n3 j) := by
  rw [hoElt, LieType.Chevalley.torusElt_eq_rootDiagUnit,
    LieType.Chevalley.torusElt_eq_rootDiagUnit, LieType.Chevalley.torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rfl

theorem hoElt_eq_rootDiagUnit_pow (σ : K ≃+* K) {q : ℕ} (hσ : ∀ c, σ c = c ^ q) (u : Kˣ) :
    hoElt σ u = rootDiagUnit TwistTag.D4.tag (fun j => u ^ shortExp (q : ℤ) j) := by
  rw [hoElt_eq_rootDiagUnit]
  congr 1
  funext j
  have e1 : Units.map σ.toRingHom.toMonoidHom u = u ^ q := Units.ext (by simp [hσ])
  have e2 : Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom u) =
      u ^ (q ^ 2) := by
    rw [e1]
    refine Units.ext ?_
    simp [hσ, ← pow_mul, sq]
  rw [e2, e1]
  simp only [shortExp, zpow_add, zpow_mul, zpow_natCast, ← Nat.cast_pow]

end Torus


section Short

variable {K : Type} [Field K]

theorem mem_orbitField_outer {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (c : K) :
    c ∈ orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer := by
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    have := congrArg (fun φ : K ≃+* K => φ c) hσ3
    simpa [pow_succ] using this
  have := orbitField_D4_zero_eq_top σ h3
  change c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
  rw [this]
  exact Subfield.mem_top c

@[expose] noncomputable def outerUnit {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (u : Kˣ) :
    (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer)ˣ where
  val := ⟨u, mem_orbitField_outer hσ3 _⟩
  inv := ⟨(u⁻¹ : Kˣ), mem_orbitField_outer hσ3 _⟩
  val_inv := Subtype.ext (Units.mul_inv u)
  inv_val := Subtype.ext (Units.inv_mul u)


theorem orbitRankOneHom_HSL_outer {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (u : Kˣ) :
    orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer (HSL (outerUnit hσ3 u)) =
      hoElt σ u := by
  rw [orbitRankOneHom_HSL, coe_orbitH]
  have hc : (TwistTag.D4.orbit KS11Lie4Proof.d4Outer).card = 3 := by decide
  have hm : TwistTag.D4.orbitMin KS11Lie4Proof.d4Outer = n0 := by decide
  have hp1 : (TwistTag.D4.perm ^ 1) n0 = n1 := by decide
  have hp2 : (TwistTag.D4.perm ^ 2) n0 = n3 := by decide
  rw [hc, hm, show List.range 3 = [0, 1, 2] by rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
    hp1, hp2]
  rw [hoElt, mul_assoc]
  congr 2

theorem hoElt_mem {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (u : Kˣ) :
    hoElt σ u ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  rw [← orbitRankOneHom_HSL_outer hσ3]
  exact range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    KS11Lie4Proof.d4Outer ⟨_, rfl⟩

theorem hoElt_mem_d4ShortSL2 {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (u : Kˣ) :
    (⟨hoElt σ u, hoElt_mem hσ3 u⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
      KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
  ⟨HSL (outerUnit hσ3 u), orbitRankOneHom_HSL_outer hσ3 u⟩

end Short

section NoConj

variable
  {K : Type} [Field K]

theorem rootChar_pow_tuple (u : Kˣ) (e : Fin TwistTag.D4.tag.rank → ℤ)
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (fun j => u ^ e j) v = u ^ ∑ j, v j * e j := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_mul, mul_comm]

theorem not_conj_hoElt {σ : K ≃+* K} {q : ℕ} (hσ : ∀ c, σ c = c ^ q)
    (hq : q = 2 ∨ q = 4 ∨ q = 5 ∨ 7 ≤ q) {u : Kˣ}
    (hu : orderOf u = q ^ 3 - 1) {s : ℕ} (hs : s = 1 ∨ s = 2) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ adjointGroup TwistTag.D4.tag K) :
    g * hoElt σ (u ^ (q ^ s)) * g⁻¹ ≠ hoElt σ u := by
  intro hconj
  have ha := hoElt_mem_torusGroup σ u
  have hb := hoElt_mem_torusGroup σ (u ^ (q ^ s))
  simp only [hoElt_eq_rootDiagUnit_pow σ hσ] at ha hb hconj
  obtain ⟨w, hw⟩ := exists_weyl_of_conj_rootDiagUnit ha hb hg hconj
  have hq1 : 1 ≤ q := by
    rcases hq with h | h | h | h <;> omega
  have hN : ((orderOf u : ℕ) : ℤ) = (q : ℤ) ^ 3 - 1 := by
    rw [hu, Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one]
  refine not_short_weyl (q := (q : ℤ)) (by rcases hq with h | h | h | h <;> [left; (right; left);
    (right; right; left); (right; right; right)] <;> omega) hs w⁻¹ fun i => ?_
  have hi := congrFun hw i
  simp only [weylTuple] at hi
  have e1 : (fun j => (u ^ q ^ s) ^ shortExp (q : ℤ) j) =
      fun j => u ^ ((q : ℤ) ^ s * shortExp (q : ℤ) j) := by
    funext j
    rw [← zpow_natCast, ← zpow_mul]
    push_cast
    ring_nf
  rw [e1, rootChar_pow_tuple] at hi
  have hsum : (q : ℤ) ^ s * shortVal (q : ℤ) (w⁻¹ • (Pi.single i 1 :
      Fin TwistTag.D4.tag.rank → ℤ)) = ∑ j, (w⁻¹ • (Pi.single i 1 :
        Fin TwistTag.D4.tag.rank → ℤ)) j * ((q : ℤ) ^ s * shortExp (q : ℤ) j) := by
    rw [shortVal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hi' : u ^ ((q : ℤ) ^ s * shortVal (q : ℤ) (w⁻¹ • (Pi.single i 1 :
      Fin TwistTag.D4.tag.rank → ℤ)) - shortExp (q : ℤ) i) = 1 := by
    rw [zpow_sub, hsum, hi, mul_inv_cancel]
  rw [← hN]
  exact orderOf_dvd_iff_zpow_eq_one.2 hi'

end NoConj

section Main


theorem triality_normal_form {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    (∀ (δ : K ≃+* K) (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ((fieldActor σ δ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = Units.map (entrywiseHom δ.toRingHom) g) ∧
    (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        α = MulAut.conj g * fieldActor σ δ) ∧
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) ∧
    IsCyclic (K ≃+* K) := by
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  · obtain ⟨h1, h2, ⟨Θ, hΘ, -, hker, -⟩, hcyc, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    refine ⟨h1, fun α => ?_, ⟨Θ, hΘ, hker⟩, hcyc⟩
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := h2 α
    exact ⟨g, δ, hgδ⟩
  · obtain ⟨h1, h2, ⟨Θ, hΘ, -, hker, -⟩, hcyc, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
    refine ⟨h1, fun α => ?_, ⟨Θ, hΘ, hker⟩, hcyc⟩
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := h2 α
    exact ⟨g, δ, hgδ⟩

theorem exists_pow_order_three {G : Type*} [Group G] {δ : G} {k : ℕ} (hk : δ ^ 3 ^ k = 1)
    (hδ : δ ≠ 1) : ∃ j : ℕ, (δ ^ 3 ^ j) ^ 3 = 1 ∧ δ ^ 3 ^ j ≠ 1 := by
  classical
  have hex : ∃ m, δ ^ 3 ^ m = 1 := ⟨k, hk⟩
  set m := Nat.find hex with hm
  have hm1 : δ ^ 3 ^ m = 1 := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hm1
    exact hδ hm1
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  refine ⟨j, ?_, Nat.find_min hex (by omega)⟩
  rw [← pow_mul, ← pow_succ, ← hj]
  exact hm1

theorem d4ShortOut_holds : KS11Lie4Proof.D4ShortOut := by
  intro K _ _ q σ hK hσ h3 β hβ hβS
  classical
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := exists_prime_pow_of_card_eq_cube hK
  obtain ⟨hact, hex, ⟨Θ, hΘ, hker⟩, hcyc⟩ := triality_normal_form hℓ hf K hK σ hσ
  by_contra hin
  set δ := Θ β with hδdef
  have hδ1 : δ ≠ 1 := fun h => hin (hker ▸ (MonoidHom.mem_ker.2 h))
  obtain ⟨k, hk⟩ := hβ
  have hδk : δ ^ 3 ^ k = 1 := by rw [hδdef, ← map_pow, hk, map_one]
  obtain ⟨j, hj3, hj1⟩ := exists_pow_order_three hδk hδ1
  set β' := β ^ 3 ^ j with hβ'def
  obtain ⟨g, δ', hβ'⟩ := hex β'
  have hδ' : δ' = δ ^ 3 ^ j := by rw [← hΘ _ _ _ hβ', hβ'def, map_pow]
  set q := ℓ ^ f with hqdef
  have hq2 : 2 ≤ q := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf u = q ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, hK]
  have hσ1 : σ ≠ 1 := by
    intro h
    have hu1 : u ^ (q - 1) = 1 := by
      have h1 : (u : K) ^ q = u := by
        have := congrArg (fun φ : K ≃+* K => φ (u : K)) h
        change σ (u : K) = (u : K) at this
        rw [← hσ, this]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have hu0 : (u : K) ≠ 0 := u.ne_zero
      have h2 : (u : K) ^ (q - 1) * u = 1 * u := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega), h1]
      exact mul_right_cancel₀ hu0 h2
    have hdvd := orderOf_dvd_of_pow_eq_one hu1
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    have : q < q ^ 3 := by
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hδ'3 : δ' ^ 3 = 1 := by rw [hδ', hj3]
  have hδ'1 : δ' ≠ 1 := by rw [hδ']; exact hj1
  obtain ⟨s, hs, hδ's⟩ : ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ ∀ c : K, δ' c = c ^ (q ^ s) := by
    rcases eq_or_eq_of_pow_three hσ3 hσ1 hδ'3 with h | h | h
    · exact absurd h hδ'1
    · exact ⟨1, Or.inl rfl, fun c => by rw [h, pow_one, hσ c]⟩
    · refine ⟨2, Or.inr rfl, fun c => ?_⟩
      rw [h]
      change σ (σ c) = _
      rw [hσ, hσ, ← pow_mul, sq]
  have hδ'σ : ∀ c, δ' (σ c) = σ (δ' c) := fun c => by
    rw [hδ's, hσ, hσ, hδ's, pow_right_comm]
  set x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨hoElt σ u, hoElt_mem hσ3 u⟩
  have hxS := hoElt_mem_d4ShortSL2 hσ3 u
  have hfix : ∀ n : ℕ, (β ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hβS x hxS, ih]
  have h1 := hfix (3 ^ j)
  rw [← hβ'def, hβ', MulAut.mul_apply, MulAut.conj_apply] at h1
  have h2 := congrArg (fun y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
    (y : ModGL TwistTag.D4.tag K)) h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hact] at h2
  change (g : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom δ'.toRingHom) (hoElt σ u) *
    (g : ModGL TwistTag.D4.tag K)⁻¹ = hoElt σ u at h2
  rw [entrywise_hoElt σ δ' hδ'σ] at h2
  have hδu : Units.map δ'.toRingHom.toMonoidHom u = u ^ (q ^ s) := Units.ext (by simp [hδ's])
  rw [hδu] at h2
  have hgC : (g : ModGL TwistTag.D4.tag K) ∈ adjointGroup TwistTag.D4.tag K :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ g.2)).1
  exact not_conj_hoElt hσ (prime_pow_cases hℓ hf h3) hord hs hgC h2

end Main

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
