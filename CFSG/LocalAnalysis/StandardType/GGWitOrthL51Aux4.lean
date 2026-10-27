module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthL51Aux3
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassCrAux

public section

namespace CFSG.StandardType.ZS

open QuadraticMap

def owL5_T {K : Type*} {U : Type*} [Field K] [AddCommGroup U] [Module K U]
    (a u u' : U) : Set U :=
  {v : U | ∃ (ε y z : K), (ε = 1 ∨ ε = -1) ∧ v = ε • a + y • u + z • u'}

theorem owL5_T_invariant {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) {a u u' : U}
    (ha : Q a ≠ 0) (hu : Q u = 0) (hu' : Q u' = 0) (hau : polarBilin Q u a = 0)
    (hau' : polarBilin Q u' a = 0) (huu' : polarBilin Q u' u = 0)
    (hbu : Q (a - u) ≠ 0) (hbu' : Q (a - u') ≠ 0) :
    ∀ h ∈ Subgroup.closure ({owCr_orthRefl Q a ha, owCr_orthRefl Q (a - u) hbu,
      owCr_orthRefl Q (a - u') hbu'} : Set (U ≃ₗ[K] U)),
      ∀ v ∈ owL5_T (K := K) a u u', h v ∈ owL5_T (K := K) a u u' ∧ h⁻¹ v ∈ owL5_T (K := K) a u u' := by
  have h0 : owCr_orthRefl Q a ha * owCr_orthRefl Q a ha = 1 :=
    owCc_orthRefl_mul_self Q a ha
  have h1 : owCr_orthRefl Q (a - u) hbu * owCr_orthRefl Q (a - u) hbu = 1 :=
    owCc_orthRefl_mul_self Q (a - u) hbu
  have h2 : owCr_orthRefl Q (a - u') hbu' * owCr_orthRefl Q (a - u') hbu' = 1 :=
    owCc_orthRefl_mul_self Q (a - u') hbu'
  have hinv0 : (owCr_orthRefl Q a ha)⁻¹ = owCr_orthRefl Q a ha :=
    inv_eq_of_mul_eq_one_right h0
  have hinv1 : (owCr_orthRefl Q (a - u) hbu)⁻¹ = owCr_orthRefl Q (a - u) hbu :=
    inv_eq_of_mul_eq_one_right h1
  have hinv2 : (owCr_orthRefl Q (a - u') hbu')⁻¹ = owCr_orthRefl Q (a - u') hbu' :=
    inv_eq_of_mul_eq_one_right h2
  have hmem : ∀ v : U, v ∈ owL5_T (K := K) a u u' ↔
      ∃ (ε y z : K), (ε = 1 ∨ ε = -1) ∧ v = ε • a + y • u + z • u' := fun v => Iff.rfl
  have hgen : ∀ g ∈ ({owCr_orthRefl Q a ha, owCr_orthRefl Q (a - u) hbu,
        owCr_orthRefl Q (a - u') hbu'} : Set (U ≃ₗ[K] U)),
      ∀ v ∈ owL5_T (K := K) a u u', g v ∈ owL5_T (K := K) a u u' ∧ g⁻¹ v ∈ owL5_T (K := K) a u u' := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    obtain ⟨ε, y, z, hε, rfl⟩ := hv
    have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with hε | hε <;> rw [hε] <;> simp
    rcases hg with rfl | rfl | rfl
    · have hf : owCr_orthRefl Q a ha (ε • a + y • u + z • u')
          = (-ε) • a + y • u + z • u' :=
        owL5_form_a Q ha hu hu' hau hau' huu' ε y z
      exact ⟨⟨-ε, y, z, hε', hf⟩, by rw [hinv0]; exact ⟨-ε, y, z, hε', hf⟩⟩
    · have hf : owCr_orthRefl Q (a - u) hbu (ε • a + y • u + z • u')
          = (-ε) • a + (y + 2 * ε) • u + z • u' :=
        owL5_form_au Q ha hu hu' hau hau' huu' hbu ε y z
      exact ⟨⟨-ε, y + 2 * ε, z, hε', hf⟩,
        by rw [hinv1]; exact ⟨-ε, y + 2 * ε, z, hε', hf⟩⟩
    · have hf : owCr_orthRefl Q (a - u') hbu' (ε • a + y • u + z • u')
          = (-ε) • a + y • u + (z + 2 * ε) • u' :=
        owL5_form_au' Q ha hu hu' hau hau' huu' hbu' ε y z
      exact ⟨⟨-ε, y, z + 2 * ε, hε', hf⟩,
        by rw [hinv2]; exact ⟨-ε, y, z + 2 * ε, hε', hf⟩⟩
  apply Subgroup.closure_induction
  · exact hgen
  · intro v hv; exact ⟨hv, hv⟩
  · intro x y hx hy ix iy v hv
    obtain ⟨hyv, hyiv⟩ := iy v hv
    obtain ⟨hxyv, _⟩ := ix (y v) hyv
    obtain ⟨_, hxiv⟩ := ix v hv
    obtain ⟨_, hyi⟩ := iy (x⁻¹ v) hxiv
    exact ⟨hxyv, by rw [mul_inv_rev, LinearEquiv.mul_apply]; exact hyi⟩
  · intro x hx ix v hv
    obtain ⟨hxv, hxiv⟩ := ix v hv
    exact ⟨hxiv, by rw [inv_inv]; exact hxv⟩

theorem owL5_T_subset_orbit {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) {a u u' : U}
    (ha : Q a ≠ 0) (hu : Q u = 0) (hu' : Q u' = 0) (hau : polarBilin Q u a = 0)
    (hau' : polarBilin Q u' a = 0) (huu' : polarBilin Q u' u = 0)
    (hbu : Q (a - u) ≠ 0) (hbu' : Q (a - u') ≠ 0)
    (hsurj : ∀ y : K, ∃ i : ℕ, (i : K) = y) :
    owL5_T (K := K) a u u' ⊆ MulAction.orbit (Subgroup.closure
      ({owCr_orthRefl Q a ha, owCr_orthRefl Q (a - u) hbu,
        owCr_orthRefl Q (a - u') hbu'} : Set (U ≃ₗ[K] U))) a := by
  classical
  intro v hv
  obtain ⟨ε, y, z, hε, rfl⟩ := hv
  have h2ne : (2 : K) ≠ 0 := owL5_two_ne_zero (K := K)
  have hg1 : ∀ x y z : K, (owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u) hbu)
      (x • a + y • u + z • u') = x • a + (y + 2 * x) • u + z • u' := by
    intro x y z
    rw [LinearEquiv.mul_apply, owL5_form_au Q ha hu hu' hau hau' huu' hbu x y z,
      owL5_form_a Q ha hu hu' hau hau' huu' (-x) (y + 2 * x) z]
    simp
  have hg2 : ∀ x y z : K, (owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u') hbu')
      (x • a + y • u + z • u') = x • a + y • u + (z + 2 * x) • u' := by
    intro x y z
    rw [LinearEquiv.mul_apply, owL5_form_au' Q ha hu hu' hau hau' huu' hbu' x y z,
      owL5_form_a Q ha hu hu' hau hau' huu' (-x) y (z + 2 * x)]
    simp
  have hpow1 : ∀ i : ℕ, ((owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u) hbu) ^ i) a
      = a + (2 * (i : K)) • u := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih]
      rw [show a + (2 * (i : K)) • u = (1 : K) • a + (2 * (i : K)) • u + (0 : K) • u' by
        rw [one_smul, zero_smul, add_zero], hg1]
      simp only [one_smul, zero_smul, add_zero, mul_one]
      congr 1
      rw [Nat.cast_succ]; ring_nf
  have hpow2 : ∀ (c : K) (j : ℕ),
      ((owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u') hbu') ^ j) (a + c • u)
      = a + c • u + (2 * (j : K)) • u' := by
    intro c j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih]
      rw [show a + c • u + (2 * (j : K)) • u' = (1 : K) • a + c • u + (2 * (j : K)) • u' by
        rw [one_smul], hg2]
      simp only [one_smul, zero_smul, add_zero, mul_one]
      congr 1
      rw [Nat.cast_succ]; ring_nf
  obtain ⟨i, hi⟩ := hsurj (y / 2)
  obtain ⟨j, hj⟩ := hsurj (z / 2)
  have hiy : (2 : K) * (i : K) = y := by
    rw [hi, mul_comm, div_mul_cancel₀ y h2ne]
  have hiz : (2 : K) * (j : K) = z := by
    rw [hj, mul_comm, div_mul_cancel₀ z h2ne]
  have hval : ((owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u') hbu') ^ j
      * (owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u) hbu) ^ i) a
      = a + y • u + z • u' := by
    rw [LinearEquiv.mul_apply, hpow1, hpow2, hiy, hiz]
  have hmem1 : ((owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u') hbu') ^ j
      * (owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u) hbu) ^ i) ∈
      Subgroup.closure ({owCr_orthRefl Q a ha, owCr_orthRefl Q (a - u) hbu,
        owCr_orthRefl Q (a - u') hbu'} : Set (U ≃ₗ[K] U)) :=
    Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]))
        (Subgroup.subset_closure (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]))) j)
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]))
        (Subgroup.subset_closure (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]))) i)
  rcases hε with hε | hε
  · subst hε
    refine ⟨⟨_, hmem1⟩, ?_⟩
    show ((owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u') hbu') ^ j
      * (owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u) hbu) ^ i) a = _
    rw [hval]; simp
  · subst hε
    refine ⟨⟨owCr_orthRefl Q a ha * ((owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u') hbu') ^ j
      * (owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u) hbu) ^ i),
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hmem1⟩, ?_⟩
    show owCr_orthRefl Q a ha (((owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u') hbu') ^ j
      * (owCr_orthRefl Q a ha * owCr_orthRefl Q (a - u) hbu) ^ i) a) = _
    rw [hval, show a + y • u + z • u' = (1 : K) • a + y • u + z • u' by rw [one_smul],
      owL5_form_a Q ha hu hu' hau hau' huu' 1 y z]

theorem owL5_hcoeff {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] {a u u' : U}
    (hind : LinearIndependent K ![a, u, u']) :
    ∀ x y z : K, x • a + y • u + z • u' = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  intro x y z h
  have h' := (Fintype.linearIndependent_iff.mp hind) ![x, y, z] (by
    simpa [Fin.sum_univ_three] using h)
  have h0 := h' 0
  have h1 := h' 1
  have h2 := h' 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem owL5_T_card {K : Type*} [Field K] [CharP K 3] [Finite K] {U : Type}
    [AddCommGroup U] [Module K U] (hK3 : Nat.card K = 3) {a u u' : U}
    (hind : LinearIndependent K ![a, u, u']) :
    Nat.card (owL5_T (K := K) a u u') = 18 := by
  classical
  have hcoeff := owL5_hcoeff (K := K) (a := a) (u := u) (u' := u') hind
  have h1ne : (1 : K) ≠ -1 := by
    intro h
    have h2 : (2 : K) = 0 := by
      rw [show (2 : K) = 1 - (-1) by ring]
      exact sub_eq_zero.mpr h
    exact owL5_two_ne_zero (K := K) h2
  have h1ne' : (-1 : K) ≠ 1 := fun h => h1ne h.symm
  have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hsub2 : Nat.card {b : K // b = 1 ∨ b = -1} = 2 := by
    let e : Bool ≃ {b : K // b = 1 ∨ b = -1} :=
      { toFun := fun t => if t then ⟨1, Or.inl rfl⟩ else ⟨-1, Or.inr rfl⟩
        invFun := fun b => if (b : K) = 1 then true else false
        left_inv := by intro t; cases t <;> simp [h1ne']
        right_inv := by
          intro b
          obtain ⟨b, hb⟩ := b
          rcases hb with rfl | rfl
          · simp
          · simp [h1ne'] }
    rw [← Nat.card_congr e, hbool]
  let φ : {b : K // b = 1 ∨ b = -1} × K × K → U := fun t =>
    (t.1 : K) • a + t.2.1 • u + t.2.2 • u'
  have hφinj : Function.Injective φ := by
    rintro ⟨b, y, z⟩ ⟨b', y', z'⟩ h
    have hz : ((b : K) - (b' : K)) • a + (y - y') • u + (z - z') • u' = 0 := by
      have hsub : φ (b, y, z) - φ (b', y', z') = 0 := sub_eq_zero.mpr h
      rw [show ((b : K) - (b' : K)) • a + (y - y') • u + (z - z') • u'
            = φ (b, y, z) - φ (b', y', z') by
        simp only [φ, sub_smul]; abel]
      exact hsub
    obtain ⟨hb, hy, hz'⟩ := hcoeff _ _ _ hz
    have hbb' : b = b' := Subtype.ext (sub_eq_zero.mp hb)
    have hyy' : y = y' := sub_eq_zero.mp hy
    have hzz' : z = z' := sub_eq_zero.mp hz'
    subst hbb'; subst hyy'; subst hzz'; rfl
  have hrange : owL5_T (K := K) a u u' = Set.range φ := by
    ext v
    simp only [owL5_T, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨ε, y, z, hε, rfl⟩
      exact ⟨(⟨ε, hε⟩, y, z), rfl⟩
    · rintro ⟨⟨⟨b, hb⟩, y, z⟩, rfl⟩
      exact ⟨b, y, z, hb, rfl⟩
  have hcard : Nat.card (Set.range φ) = Nat.card ({b : K // b = 1 ∨ b = -1} × K × K) :=
    (Nat.card_congr (Equiv.ofInjective φ hφinj)).symm
  rw [hrange, hcard, Nat.card_prod, Nat.card_prod, hsub2, hK3]

theorem owL5_orbit_card_nine_aux {K : Type*} [Field K] [CharP K 3] [Finite K]
    {U : Type} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (hK3 : Nat.card K = 3) (hsurj : ∀ y : K, ∃ i : ℕ, (i : K) = y)
    (Q : QuadraticForm K U) {a u u' : U}
    (ha : Q a ≠ 0) (hu : Q u = 0) (hu' : Q u' = 0) (hau : polarBilin Q u a = 0)
    (hau' : polarBilin Q u' a = 0) (huu' : polarBilin Q u' u = 0)
    (hind : LinearIndependent K ![a, u, u'])
    (hbu : Q (a - u) ≠ 0) (hbu' : Q (a - u') ≠ 0) :
    9 ∣ Nat.card (Subgroup.closure ({owCr_orthRefl Q a ha, owCr_orthRefl Q (a - u) hbu,
      owCr_orthRefl Q (a - u') hbu'} : Set (U ≃ₗ[K] U))) := by
  classical
  set H : Subgroup (U ≃ₗ[K] U) := Subgroup.closure ({owCr_orthRefl Q a ha,
    owCr_orthRefl Q (a - u) hbu, owCr_orthRefl Q (a - u') hbu'} : Set (U ≃ₗ[K] U)) with hH
  have hstab := owL5_T_invariant Q ha hu hu' hau hau' huu' hbu hbu'
  have hsub := owL5_T_subset_orbit Q ha hu hu' hau hau' huu' hbu hbu' hsurj
  have haT : a ∈ owL5_T (K := K) a u u' := by
    exact ⟨1, 0, 0, Or.inl rfl, by
      rw [one_smul, zero_smul, zero_smul, add_zero, add_zero]⟩
  have horbit : MulAction.orbit H a = owL5_T (K := K) a u u' := by
    apply Set.Subset.antisymm
    · rintro v ⟨h, rfl⟩
      show h.1 a ∈ owL5_T (K := K) a u u'
      exact (hstab h.1 (hH ▸ h.2) a haT).1
    · exact hsub
  have hT : Nat.card (owL5_T (K := K) a u u') = 18 := owL5_T_card hK3 hind
  have horbcard : Nat.card (MulAction.orbit H a) = 18 := by rw [horbit, hT]
  haveI : Finite U := Module.finite_of_finite K
  haveI : Fintype U := Fintype.ofFinite U
  haveI : Fintype (U ≃ₗ[K] U) :=
    Fintype.ofInjective (fun f : U ≃ₗ[K] U => (f : U → U)) DFunLike.coe_injective
  haveI : Finite H := Subtype.finite
  haveI : Fintype H := Fintype.ofFinite H
  have horbcard' : Fintype.card (MulAction.orbit H a) = 18 := by
    rw [← Nat.card_eq_fintype_card]; exact horbcard
  have hdiv : Fintype.card (MulAction.orbit H a) ∣ Nat.card H := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Fintype.card (MulAction.stabilizer H a),
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := H) a).symm⟩
  exact dvd_trans (by rw [horbcard']; norm_num) hdiv

theorem owL5_wit_orth_l51 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (hp3 : p = 3) (hd : 6 ≤ Module.finrank (ZMod p) U)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ IsIsom p Q g) :
    ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  subst p
  intro r hrA hr
  obtain ⟨a, ha, rfl⟩ :=
    owCr_refl_form Q hQ (owL5_two_ne_zero (K := ZMod 3)) hr.1 hr.2 ((hA r).mp hrA)
  intro r₂ hr₂A hr₂ hord
  obtain ⟨b, hb, rfl⟩ :=
    owCr_refl_form Q hQ (owL5_two_ne_zero (K := ZMod 3)) hr₂.1 hr₂.2 ((hA r₂).mp hr₂A)
  have hra2 : owCr_orthRefl Q a ha * owCr_orthRefl Q a ha = 1 := hr.1
  have hrb2 : owCr_orthRefl Q b hb * owCr_orthRefl Q b hb = 1 := hr₂.1
  obtain ⟨u, b', hb', hu0, huQ, huB, hb'eq, hrb_eq⟩ :=
    owL5_exists_u (fun x hx => owL5_zmod3_sq x hx) Q ha hb hra2 hrb2 hord
  subst b'
  have hodd : Odd (Nat.card (ZMod 3)) := by rw [Nat.card_zmod]; decide
  obtain ⟨u', hu'0, hu'Q, hu'a, hu'u, hu'span⟩ :=
    owL5_exists_second_isotropic hodd (owL5_two_ne_zero (K := ZMod 3)) Q hQ hd ha huQ huB hu0
  have hbu' : Q (a - u') ≠ 0 := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q a (-u') (owL5_Q_neg Q hu'Q)
      (by rw [polarBilin_apply_apply, polar_neg_left, ← polarBilin_apply_apply, hu'a]; ring)]
    exact ha
  have hbm : Q ((2 : ZMod 3) • a - u') ≠ 0 := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q ((2 : ZMod 3) • a) (-u') (owL5_Q_neg Q hu'Q)
      (by rw [polarBilin_apply_apply, polar_neg_left, polar_smul_right,
        ← polarBilin_apply_apply, hu'a]; ring)]
    rw [QuadraticMap.map_smul, smul_eq_mul]
    rw [show (2 : ZMod 3) * 2 * Q a = Q a by
      rw [show (2 : ZMod 3) * 2 = 1 by decide +kernel, one_mul]]
    exact ha
  refine ⟨owCr_orthRefl Q ((2 : ZMod 3) • a - u') hbm,
    (hA _).mpr (owCr_orthRefl_isIsom Q ((2 : ZMod 3) • a - u') hbm), ?_, ?_⟩
  · rw [owL5_conj Q ha hu'Q hu'a hbu' hbm]
    intro hcomm
    exact owL5_not_commute Q ha hu'0 hu'Q hu'a hbu' hcomm.1
  · rw [owL5_conj Q ha hu'Q hu'a hbu' hbm, hrb_eq]
    have hnine := owL5_orbit_card_nine_aux (Nat.card_zmod 3)
      (fun y => ZMod.natCast_zmod_surjective y) Q ha huQ hu'Q huB hu'a hu'u
      (owL5_linearIndependent Q ha huQ hu'Q huB hu'a hu'u hu0 hu'span) hb' hbu'
    intro hdvd
    have h948 : 9 ∣ 48 := dvd_trans hnine hdvd
    norm_num at h948

end CFSG.StandardType.ZS

end
