module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityModel

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

theorem card_le_of_forall_pow_eq_self (F : Type) [Field F] [Finite F] (m : ℕ) (hm : 2 ≤ m)
    (h : ∀ c : F, c ^ m = c) : Nat.card F ≤ m := by
  classical
  haveI := Fintype.ofFinite F
  have hdeg : (Polynomial.X ^ m - Polynomial.X : Polynomial F).natDegree = m := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      (by simp only [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; omega),
      Polynomial.natDegree_X_pow]
  have hne : (Polynomial.X ^ m - Polynomial.X : Polynomial F) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ m - Polynomial.X : Polynomial F).roots := by
    intro x _
    rw [Polynomial.mem_roots hne]
    simp [h x]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, hdeg] at hle
  rw [Nat.card_eq_fintype_card]
  exact hle

theorem mem_of_cube_eq_one_cyclic {G : Type} [Group G] [Finite G] [IsCyclic G] (σ : G)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 ≠ 1) (ψ : G) (hψ : ψ ^ 3 = 1) :
    ψ = 1 ∨ ψ = σ ∨ ψ = σ ^ 2 := by
  classical
  haveI := Fintype.ofFinite G
  have hle : (Finset.univ.filter fun a : G => a ^ 3 = 1).card ≤ 3 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hsub : ({1, σ, σ ^ 2} : Finset G) ⊆ Finset.univ.filter fun a : G => a ^ 3 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [← pow_mul, show (2 : ℕ) * 3 = 3 * 2 by norm_num, pow_mul, hσ3, one_pow]
  have hne : σ ≠ σ ^ 2 := by
    intro h
    apply hσ1
    rw [pow_two] at h
    exact mul_left_cancel (a := σ) (by rw [mul_one]; exact h.symm)
  have hcard3 : ({1, σ, σ ^ 2} : Finset G).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, σ, σ ^ 2, fun h => hσ1 h.symm, fun h => hσ2 h.symm, hne, rfl⟩
  have heq : ({1, σ, σ ^ 2} : Finset G) = Finset.univ.filter fun a : G => a ^ 3 = 1 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard3]; exact hle)
  have hmem : ψ ∈ Finset.univ.filter fun a : G => a ^ 3 = 1 :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hψ⟩
  rw [← heq] at hmem
  simpa using hmem

theorem nf1_pow_apply {X : Type} [Field X] (σ : X ≃+* X) (q : ℕ) (hq : ∀ c : X, σ c = c ^ q)
    (k : ℕ) (c : X) : (σ ^ k) c = c ^ (q ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show σ ^ (k + 1) = σ * σ ^ k from pow_succ' σ k]
    show σ ((σ ^ k) c) = c ^ (q ^ (k + 1))
    rw [ih, map_pow, hq, ← pow_mul, pow_succ, mul_comm (q ^ k) q]

theorem nf1_sigma_pow_three {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (n : ℕ)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) : σ ^ 3 = 1 := by
  classical
  haveI := Fintype.ofFinite X
  refine RingEquiv.ext fun c => ?_
  show (σ ^ 3) c = c
  rw [nf1_pow_apply σ (2 ^ n) hσ 3 c, ← hX, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem nf1_lt_pow_three {q : ℕ} (hq : 2 ≤ q) : q < q ^ 3 := by
  have h2 : 2 * 2 ≤ q * q := Nat.mul_le_mul hq hq
  have h3 : q * (2 * 2) ≤ q * (q * q) := Nat.mul_le_mul (le_refl q) h2
  have e : q ^ 3 = q * (q * q) := by ring
  rw [e]
  linarith

theorem nf1_sigma_ne_one {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (n : ℕ) (hn : 1 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) : σ ≠ 1 := by
  intro h1
  have key : ∀ c : X, c ^ (2 ^ n) = c := fun c => by
    have h := hσ c
    rw [h1] at h
    exact h.symm
  have h2 : 2 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (show 2 > 0 by norm_num) hn
  have hle : Nat.card X ≤ 2 ^ n := card_le_of_forall_pow_eq_self X (2 ^ n) h2 key
  rw [hX] at hle
  exact absurd hle (not_le.2 (nf1_lt_pow_three h2))

theorem nf1_sq_ne_one {G : Type} [Group G] (s : G) (h3 : s ^ 3 = 1) (h1 : s ≠ 1) :
    s ^ 2 ≠ 1 := by
  intro h2
  apply h1
  have e : s ^ 3 = s ^ 2 * s := pow_succ s 2
  rw [h2, one_mul] at e
  exact e.symm.trans h3

theorem nf1_four_le_card {G : Type} [Group G] (H : Subgroup G) [Finite H] {x y z w : G}
    (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H) (hw : w ∈ H)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    4 ≤ Nat.card H := by
  have hv : Function.Injective (![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, ⟨w, hw⟩] : Fin 4 → H) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | simp [hxy, hxz, hxw, hyz, hyw, hzw, hxy.symm, hxz.symm, hxw.symm, hyz.symm, hyw.symm,
          hzw.symm] at hij
  simpa using Nat.card_le_card_of_injective _ hv

theorem nf1_closure_pair_eq {G : Type} [Group G] (E : Subgroup G) [Finite E]
    (hE : Nat.card E = 3 ^ 2) {a b : G} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2) :
    E = Subgroup.closure ({a, b} : Set G) := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤ E := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ha, hb⟩
  haveI : Finite (Subgroup.closure ({a, b} : Set G)) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hdvd : Nat.card (Subgroup.closure ({a, b} : Set G)) ∣ 3 ^ 2 := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le hle
  have ha2 : a ^ 2 ≠ 1 := fun h => ha1 (by
    have e : a ^ 3 = a ^ 2 * a := pow_succ a 2
    rw [h, one_mul] at e
    exact e.symm.trans ha3)
  have ha_sq : a ≠ a ^ 2 := fun h => ha1 (mul_left_cancel (a := a) (by
    rw [mul_one, ← pow_two]
    exact h.symm))
  have hmem_a : a ∈ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert a _)
  have hmem_b : b ∈ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b))
  have h4 : 4 ≤ Nat.card (Subgroup.closure ({a, b} : Set G)) :=
    nf1_four_le_card (Subgroup.closure ({a, b} : Set G)) (one_mem _) hmem_a
      (pow_mem hmem_a 2) hmem_b (Ne.symm ha1) (Ne.symm ha2) (Ne.symm hb1) ha_sq
      (Ne.symm hba) (Ne.symm hba2)
  have hcl : Nat.card (Subgroup.closure ({a, b} : Set G)) = 3 ^ 2 := by
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · rw [pow_zero] at hieq
      exfalso
      omega
    · rw [pow_one] at hieq
      exfalso
      omega
    · exact hieq
  exact (Subgroup.eq_of_le_of_card_ge hle (hE.trans hcl.symm).le).symm

theorem nf1_conj_injective {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥) :
    Function.Injective (MulAut.conj : H →* MulAut H) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut H => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem outer_plane_shape (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ ∀ φ ∈ E, ∃ g : C0 σ, φ = MulAut.conj g) :
    ∃ x : C0 σ, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∃ g : C0 σ, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1 ∧
      Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e) ∧
      E = Subgroup.closure {MulAut.conj x, MulAut.conj g * tauAut σ ^ e} := by
  classical
  obtain ⟨-, hdec, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard3, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form hn X hX σ hσ
  haveI : Finite (X ≃+* X) := Nat.finite_of_card_ne_zero (by rw [hcard3]; omega)
  have hσ3 : σ ^ 3 = 1 := nf1_sigma_pow_three σ n hX hσ
  have hσ1 : σ ≠ 1 := nf1_sigma_ne_one σ n hn hX hσ
  have hσ2 : σ ^ 2 ≠ 1 := nf1_sq_ne_one σ hσ3 hσ1
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hsc : (Finset.univ : Finset E).card = 3 ^ 2 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hlt : ({1, σ, σ ^ 2} : Finset (X ≃+* X)).card < (Finset.univ : Finset E).card := by
    rw [hsc]
    exact lt_of_le_of_lt Finset.card_le_three (by norm_num)
  have hmaps0 : ∀ a : E, Θ (a : MulAut (C0 σ)) ∈ ({1, σ, σ ^ 2} : Finset (X ≃+* X)) := by
    intro a
    have ha3 : (a : MulAut (C0 σ)) ^ 3 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) (a : MulAut (C0 σ)) a.2
    have hψ : Θ (a : MulAut (C0 σ)) ^ 3 = 1 := by
      rw [← map_pow Θ, ha3, map_one]
    rcases mem_of_cube_eq_one_cyclic σ hσ3 hσ1 hσ2 _ hψ with h | h | h <;> rw [h] <;> simp
  obtain ⟨a, -, b, -, hab, hΘab0⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := fun a : E => Θ (a : MulAut (C0 σ))) fun a _ => Finset.mem_coe.2 (hmaps0 a)
  have hΘab : Θ (a : MulAut (C0 σ)) = Θ (b : MulAut (C0 σ)) := hΘab0
  obtain ⟨γ, hγE, hγ1, hγΘ⟩ : ∃ γ ∈ E, γ ≠ 1 ∧ Θ γ = 1 := by
    refine ⟨(a : MulAut (C0 σ)) * (b : MulAut (C0 σ))⁻¹,
      E.mul_mem a.2 (E.inv_mem b.2), fun h => hab (Subtype.ext (mul_inv_eq_one.1 h)), ?_⟩
    rw [map_mul, map_inv, hΘab, mul_inv_cancel]
  have hγker : γ ∈ Θ.ker := MonoidHom.mem_ker.2 hγΘ
  rw [hker] at hγker
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hγker
  have hγ3 : γ ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) γ hγE
  have hcx : MulAut.conj x ∈ E := by rw [hx]; exact hγE
  have hcx3 : MulAut.conj x ^ 3 = 1 := by rw [hx]; exact hγ3
  have hcx1 : MulAut.conj x ≠ 1 := by rw [hx]; exact hγ1
  have hx3 : x ^ 3 = 1 := nf1_conj_injective hZ (by rw [map_pow, hx, hγ3, map_one])
  have hx1 : x ≠ 1 := fun h => hcx1 (by rw [h, map_one])
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, ∀ g : C0 σ, β ≠ MulAut.conj g := by
    push_neg at hout
    exact hout
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) β hβE
  have hβΘ3 : Θ β ^ 3 = 1 := by rw [← map_pow Θ, hβ3, map_one]
  have hβ1 : Θ β ≠ 1 := by
    intro h
    have hmem : β ∈ Θ.ker := MonoidHom.mem_ker.2 h
    rw [hker] at hmem
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hmem
    exact hβout g hg.symm
  obtain ⟨e, he12, hΘe⟩ : ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Θ β = σ ^ e := by
    rcases mem_of_cube_eq_one_cyclic σ hσ3 hσ1 hσ2 _ hβΘ3 with h | h | h
    · exact absurd h hβ1
    · exact ⟨1, Or.inl rfl, by rw [h, pow_one]⟩
    · exact ⟨2, Or.inr rfl, h⟩
  obtain ⟨⟨g, δ⟩, hgδ⟩ := (hdec β).exists
  have hδ : δ = σ ^ e := (hΘ β g δ hgδ).symm.trans hΘe
  have hpow : fieldActor (t := TwistTag.D4) σ (σ ^ e) = tauAut σ ^ e :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ e
  have hβeq : β = MulAut.conj g * tauAut σ ^ e := by
    rw [← hpow, ← hδ]
    exact hgδ
  have hcomm : ∀ u v : E, u * v = v * u := isMulCommutative_iff.1 inferInstance
  have hcomm' : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcomm ⟨u, hu⟩ ⟨v, hv⟩)
  have hβ1' : β ≠ 1 := fun h =>
    hβout 1 (h.trans (map_one (MulAut.conj : C0 σ →* MulAut (C0 σ))).symm)
  have hβx : β ≠ MulAut.conj x := hβout x
  have hβx2 : β ≠ MulAut.conj x ^ 2 := fun h =>
    hβout (x ^ 2) (h.trans (map_pow (MulAut.conj : C0 σ →* MulAut (C0 σ)) x 2).symm)
  have hclos : E = Subgroup.closure ({MulAut.conj x, β} : Set (MulAut (C0 σ))) :=
    nf1_closure_pair_eq E hcard hcx hβE hcx1 hcx3 hβ1' hβx hβx2
  refine ⟨x, hx3, hx1, g, e, he12, ?_, ?_, ?_⟩
  · rw [← hβeq]
    exact hβ3
  · rw [← hβeq]
    exact hcomm' _ hcx _ hβE
  · rw [← hβeq]
    exact hclos

end Model

end CFSG.RankThree.PartTwo.Sec19
