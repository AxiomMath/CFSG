module

public import CFSG.RankThree.PartOne.CTP.SeitzDiag
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.CTP.SeitzToral

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] {n : ℕ}

theorem diag_entry_ne_zero {x : GL (Fin n) F}
    (hx : ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) F) i j = 0) (i : Fin n) :
    (x : Matrix (Fin n) (Fin n) F) i i ≠ 0 := by
  have hd : (x : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun k => (x : Matrix (Fin n) (Fin n) F) k k) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · simp [hx a b h, Matrix.diagonal_apply_ne _ h]
  have hdet : (x : Matrix (Fin n) (Fin n) F).det ≠ 0 := x.det.ne_zero
  rw [hd, Matrix.det_diagonal] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)

theorem diag_mul_entry {A B : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, i ≠ j → A i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb; rw [hA i b (Ne.symm hb), zero_mul]
  · simp


@[expose] noncomputable def diagRatio (D : Subgroup (GL (Fin n) F)) (hD : ∀ x ∈ D, ∀ i j, i ≠ j →
    (x : Matrix (Fin n) (Fin n) F) i j = 0) (i j : Fin n) : D →* Fˣ where
  toFun x := Units.mk0
    ((x.1 : Matrix (Fin n) (Fin n) F) i i * ((x.1 : Matrix (Fin n) (Fin n) F) j j)⁻¹)
    (mul_ne_zero (diag_entry_ne_zero (hD x.1 x.2) i)
      (inv_ne_zero (diag_entry_ne_zero (hD x.1 x.2) j)))
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
    rw [diag_mul_entry (hD x.1 x.2), diag_mul_entry (hD x.1 x.2)]
    have hxj := diag_entry_ne_zero (hD x.1 x.2) j
    have hyj := diag_entry_ne_zero (hD y.1 y.2) j
    field_simp

theorem exists_ne_one_diag_eq (D : Subgroup (GL (Fin n) F)) [Finite D]
    (hD : ∀ x ∈ D, ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) F) i j = 0) (hnc : ¬ IsCyclic D)
    (i j : Fin n) :
    ∃ x ∈ D, x ≠ 1 ∧ (x : Matrix (Fin n) (Fin n) F) i i = (x : Matrix (Fin n) (Fin n) F) j j := by
  by_contra hcon
  push Not at hcon
  apply hnc
  have hinj : Function.Injective ((Units.coeHom F).comp (diagRatio D hD i j)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hne
    have hx1 : (x : GL (Fin n) F) ≠ 1 := fun h => hne (Subtype.ext h)
    apply hcon x.1 x.2 hx1
    have h1 : (x.1 : Matrix (Fin n) (Fin n) F) i i *
        ((x.1 : Matrix (Fin n) (Fin n) F) j j)⁻¹ = 1 := by
      simpa [diagRatio] using hx
    have hj := diag_entry_ne_zero (hD x.1 x.2) j
    field_simp at h1
    exact h1
  exact isCyclic_of_injective_ringHom _ hinj


theorem transvection_commute_of_diag_eq {x : Matrix (Fin n) (Fin n) F}
    (hx : ∀ i j, i ≠ j → x i j = 0) {i j : Fin n} (hij : i ≠ j) (hxij : x i i = x j j) (c : F) :
    Matrix.transvection i j c * x = x * Matrix.transvection i j c := by
  obtain ⟨d, rfl⟩ : ∃ d : Fin n → F, x = Matrix.diagonal d := by
    refine ⟨fun k => x k k, ?_⟩
    ext a b
    by_cases h : a = b
    · subst h; simp
    · simp [hx a b h, Matrix.diagonal_apply_ne _ h]
  simp only [Matrix.diagonal_apply_eq] at hxij
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hxij, mul_comm]
  · have h' : ¬ (i = a ∧ j = b) := fun h2 => h ⟨h2.1.symm, h2.2.symm⟩
    by_cases hab : a = b
    · subst hab; simp [h']
    · simp [h', hab]

theorem closure_centralizer_diag_eq_top (D : Subgroup (GL (Fin n) F)) [Finite D]
    (hD : ∀ x ∈ D, ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) F) i j = 0) (hnc : ¬ IsCyclic D) :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin n) F | ∃ x ∈ D, x ≠ 1 ∧
      (g : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) =
        (x : Matrix (Fin n) (Fin n) F) * g} = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin n) (K := F), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  apply Subgroup.subset_closure
  obtain ⟨x, hxD, hx1, hxeq⟩ := exists_ne_one_diag_eq D hD hnc t.i t.j
  refine ⟨x, hxD, hx1, ?_⟩
  exact transvection_commute_of_diag_eq (hD x hxD) t.hij hxeq t.c


theorem exists_lift_of_coprime_ker {G Q : Type*} [Group G] [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) {p : ℕ} [Fact p.Prime] [Finite G]
    (hcop : ¬ p ∣ Nat.card π.ker) (E : Subgroup Q) (hE : IsPGroup p E) :
    ∃ E' : Subgroup G, E'.map π = E ∧ Disjoint E' π.ker := by
  classical
  have : Finite Q := Finite.of_surjective π hπ
  set Et : Subgroup G := E.comap π with hEt
  have hker_le : π.ker ≤ Et := fun z hz => by
    rw [hEt, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]; exact E.one_mem
  set N : Subgroup Et := π.ker.subgroupOf Et with hN
  have hNcard : Nat.card N = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  let φ : Et →* E := (π.comp Et.subtype).codRestrict E (fun g => g.2)
  have hφsurj : Function.Surjective φ := fun e => by
    obtain ⟨g, hg⟩ := hπ (e : Q)
    exact ⟨⟨g, by simp [hEt, hg]⟩, Subtype.ext hg⟩
  have hφker : φ.ker = N := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have : N.Normal := by rw [← hφker]; infer_instance
  have hindex : N.index = Nat.card E := by
    rw [← hφker, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
    rfl
  have hcoprime : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hindex]
    obtain ⟨k, hk⟩ := hE.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hcop).symm
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcoprime
  refine ⟨H'.map Et.subtype, ?_, ?_⟩
  · ext e
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact (φ h).2
    · intro he
      obtain ⟨g, hg⟩ := hφsurj ⟨e, he⟩
      obtain ⟨⟨⟨n, hn⟩, ⟨h, hh⟩⟩, hnh⟩ := hH'.2 g
      refine ⟨(h : G), ⟨h, hh, rfl⟩, ?_⟩
      have hn1 : φ n = 1 := by rw [← MonoidHom.mem_ker, hφker]; exact hn
      have : φ g = φ h := by
        rw [← hnh]
        simp only [map_mul, hn1, one_mul]
      have h2 : (φ g : Q) = e := by rw [hg]
      rw [← h2, this]
      rfl
  · rw [Subgroup.disjoint_def]
    rintro x ⟨h, hh, rfl⟩ hx
    have hxN : h ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact hx
    have hdis := hH'.disjoint
    have : h = 1 := by
      exact Subgroup.disjoint_def.mp hdis hxN hh
    rw [this]
    simp


theorem conj_mul_conj {G Gi : Matrix (Fin n) (Fin n) F} (hg : Gi * G = 1)
    (A B : Matrix (Fin n) (Fin n) F) : (G * A * Gi) * (G * B * Gi) = G * (A * B) * Gi := by
  calc (G * A * Gi) * (G * B * Gi) = G * A * (Gi * G) * B * Gi := by simp only [Matrix.mul_assoc]
    _ = G * (A * B) * Gi := by rw [hg, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem conj_cancel {G Gi : Matrix (Fin n) (Fin n) F} (hg : Gi * G = 1)
    (M : Matrix (Fin n) (Fin n) F) : Gi * (G * M * Gi) * G = M := by
  calc Gi * (G * M * Gi) * G = (Gi * G) * M * (Gi * G) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [hg]; simp

theorem unit_inv_mul (g : GL (Fin n) F) :
    ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem unit_mul_inv (g : GL (Fin n) F) :
    (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conj_comm_transfer {G Gi X H : Matrix (Fin n) (Fin n) F} (hgi : Gi * G = 1)
    (h : H * (G * X * Gi) = (G * X * Gi) * H) :
    (Gi * H * G) * X = X * (Gi * H * G) := by
  have hL1 : ∀ M : Matrix (Fin n) (Fin n) F, Gi * (G * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
  have hR1 : ∀ M : Matrix (Fin n) (Fin n) F, M * Gi * G = M := fun M => by
    rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
  have h' := congrArg (fun M => Gi * M * G) h
  simp only [Matrix.mul_assoc, hL1, hgi, Matrix.mul_one] at h'
  simpa only [Matrix.mul_assoc] using h'

@[expose] noncomputable def conjSL (g : GL (Fin n) F) : Matrix.SpecialLinearGroup (Fin n) F →*
    Matrix.SpecialLinearGroup (Fin n) F where
  toFun h := ⟨(g : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), by
    rw [Matrix.det_mul, Matrix.det_mul, h.2, mul_one, ← Matrix.det_mul, unit_mul_inv,
      Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    show (g : Matrix (Fin n) (Fin n) F) * ((a * b : Matrix.SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : Matrix (Fin n) (Fin n) F) * (a : Matrix (Fin n) (Fin n) F) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        ((g : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    rw [conj_mul_conj (unit_inv_mul g), Matrix.SpecialLinearGroup.coe_mul]

theorem conjSL_coe (g : GL (Fin n) F) (h : Matrix.SpecialLinearGroup (Fin n) F) :
    ((conjSL g h : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl

theorem conjSL_injective (g : GL (Fin n) F) : Function.Injective (conjSL g) := by
  intro a b hab
  have h := congrArg (fun h : Matrix.SpecialLinearGroup (Fin n) F =>
    ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F)) hab
  simp only [conjSL_coe, conj_cancel (unit_inv_mul g)] at h
  exact Subtype.ext h


theorem closure_centralizers_sl_toral [Finite F] {p : ℕ} [Fact p.Prime]
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p) (E' : Subgroup (Matrix.SpecialLinearGroup (Fin n) F))
    (hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a) (hE'exp : ∀ a ∈ E', a ^ p = 1)
    (hnc : ¬ IsCyclic E') :
    Subgroup.closure {h : Matrix.SpecialLinearGroup (Fin n) F | ∃ x ∈ E', x ≠ 1 ∧
      h * x = x * h} = ⊤ := by
  classical
  let E'' : Subgroup (GL (Fin n) F) := E'.map Matrix.SpecialLinearGroup.toGL
  have hE''comm : ∀ x ∈ E'', ∀ y ∈ E'', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE'comm a ha b hb]
  have hE''exp : ∀ x ∈ E'', x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE'exp a ha, map_one]
  obtain ⟨g, hg⟩ := exists_conj_diagonal_of_exponent_prime hζ E'' hE''comm hE''exp
  let D : Subgroup (GL (Fin n) F) := E''.map (MulAut.conj g).toMonoidHom
  have hDdiag : ∀ x ∈ D, ∀ i j : Fin n, i ≠ j → (x : Matrix (Fin n) (Fin n) F) i j = 0 := by
    rintro _ ⟨y, hy, rfl⟩ i j hij
    exact hg y hy i j hij
  have : Finite D := by
    have : Finite (GL (Fin n) F) := inferInstance
    infer_instance
  let f : E' →* D :=
    (((MulAut.conj g).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL).comp E'.subtype).codRestrict
      D (fun x => ⟨_, ⟨x.1, x.2, rfl⟩, rfl⟩)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : (g * Matrix.SpecialLinearGroup.toGL x.1 * g⁻¹ : GL (Fin n) F) =
        g * Matrix.SpecialLinearGroup.toGL y.1 * g⁻¹ := by
      exact congrArg Subtype.val hxy
    have h2 : Matrix.SpecialLinearGroup.toGL x.1 = Matrix.SpecialLinearGroup.toGL y.1 := by
      simpa using h1
    exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective h2)
  have hDnc : ¬ IsCyclic D := by
    intro hDc
    exact hnc (isCyclic_of_injective f hfinj)
  have hD := closure_centralizer_diag_eq_top D hDdiag hDnc
  set SE' : Set (Matrix.SpecialLinearGroup (Fin n) F) :=
    {h | ∃ x ∈ E', x ≠ 1 ∧ h * x = x * h} with hSE'
  have hsub : {h : Matrix.SpecialLinearGroup (Fin n) F | ∃ x ∈ D, x ≠ 1 ∧
      (h : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) =
        (x : Matrix (Fin n) (Fin n) F) * h} ⊆ (conjSL g) '' SE' := by
    rintro h' ⟨y, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, hy1, hcomm'⟩
    have hc : (h' : Matrix (Fin n) (Fin n) F) * ((g : Matrix (Fin n) (Fin n) F) *
        (x : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
        ((g : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * h' := hcomm'
    refine ⟨(conjSL g⁻¹) h', ⟨x, hx, ?_, ?_⟩, ?_⟩
    · intro hx1
      apply hy1
      rw [hx1]
      simp
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, conjSL_coe,
        inv_inv]
      exact conj_comm_transfer (unit_inv_mul g) hc
    · apply Subtype.ext
      rw [conjSL_coe, conjSL_coe, inv_inv]
      exact conj_cancel (G := ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        (Gi := (g : Matrix (Fin n) (Fin n) F)) (unit_mul_inv g) _
  have hmap : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) ≤
      (Subgroup.closure SE').map (conjSL g) := by
    rw [← hD, Subgroup.closure_le]
    intro h' hh'
    exact (MonoidHom.map_closure (conjSL g) SE' ▸ Subgroup.subset_closure (hsub hh'))
  rw [eq_top_iff]
  intro h _
  obtain ⟨c, hc, hch⟩ := hmap (Subgroup.mem_top (conjSL g h))
  rw [← conjSL_injective g hch]
  exact hc


theorem closure_centralizers_psl_of_lift [Finite F] {p : ℕ} [Fact p.Prime]
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)))
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hSL : ∀ E' : Subgroup (Matrix.SpecialLinearGroup (Fin n) F),
      (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) → (∀ a ∈ E', a ^ p = 1) →
      Nat.card E' = Nat.card E → (IsCyclic E' → IsCyclic E) →
      Subgroup.closure {h : Matrix.SpecialLinearGroup (Fin n) F | ∃ x ∈ E', x ≠ 1 ∧
        h * x = x * h} = ⊤) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have hfin : Finite (Matrix.SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (Subtype.val : Matrix.SpecialLinearGroup (Fin n) F →
      Matrix (Fin n) (Fin n) F) Subtype.val_injective
  let π : Matrix.SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) :=
    QuotientGroup.ker_mk' _
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ := exists_lift_of_coprime_ker π hπ (by rwa [hker]) E hEp
  have hE'mem : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcomm _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hexp _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  let fπ : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => hE'mem x.1 x.2)
  have hfπsurj : Function.Surjective fπ := by
    intro e
    have : (e : ProjectiveSpecialLinearGroup (Fin n) F) ∈ E'.map π := hE'map ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hfπinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  have htop := hSL E' hE'comm hE'exp hcard fun hc => isCyclic_of_surjective fπ hfπsurj
  rw [eq_top_iff]
  have : (Subgroup.closure {h : Matrix.SpecialLinearGroup (Fin n) F | ∃ x ∈ E', x ≠ 1 ∧
      h * x = x * h}).map π ≤ Subgroup.closure
      {k : ProjectiveSpecialLinearGroup (Fin n) F | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨h, ⟨x, hx, hx1, hxc⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π x, hE'mem x hx, ?_, by rw [← map_mul, ← map_mul, hxc]⟩
    intro hπx
    exact hx1 (Subgroup.disjoint_def.mp hE'dis hx (by rwa [MonoidHom.mem_ker]))
  rw [htop, Subgroup.map_top_of_surjective π hπ] at this
  exact this

theorem closure_centralizers_psl_eq_top [Finite F] {p : ℕ} [Fact p.Prime]
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)))
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p)
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1) (hnc : ¬ IsCyclic E) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ :=
  closure_centralizers_psl_of_lift hZ E hcomm hexp fun E' hc he _ hcyc =>
    closure_centralizers_sl_toral hζ E' hc he fun h => hnc (hcyc h)

end CFSG.RankThree.PartOne.CTP.SeitzToral
