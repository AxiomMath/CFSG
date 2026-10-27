module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Module Module.End Subgroup

theorem perm_fin_pow_eq_one {n : ℕ} (hn : n ≤ 4) (τ : Equiv.Perm (Fin n)) :
    τ ^ 1 = 1 ∨ τ ^ 2 = 1 ∨ τ ^ 3 = 1 ∨ τ ^ 4 = 1 := by
  interval_cases n <;> revert τ <;> decide

theorem exists_perm_pow_eq_one {S : Type*} [Fintype S] (hS : Fintype.card S ≤ 4)
    (σ : Equiv.Perm S) : ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ σ ^ k = 1 := by
  set e := (Fintype.equivFin S).permCongrHom
  have h : ∀ k, e σ ^ k = 1 → σ ^ k = 1 := fun k hk => by
    rw [← map_pow, map_eq_one_iff _ e.injective] at hk
    exact hk
  rcases perm_fin_pow_eq_one hS (e σ) with h1 | h1 | h1 | h1
  · exact ⟨1, le_rfl, by norm_num, h 1 h1⟩
  · exact ⟨2, by norm_num, by norm_num, h 2 h1⟩
  · exact ⟨3, by norm_num, by norm_num, h 3 h1⟩
  · exact ⟨4, by norm_num, le_rfl, h 4 h1⟩

variable {F : Type*} [Field F]

@[expose] noncomputable def glEnd (K : Type*) [Field K] [Algebra F K] (n : ℕ) :
    GL (Fin n) F →* Module.End K (Fin n → K) :=
  (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv.toMonoidHom.comp
    ((algebraMap F K).mapMatrix.toMonoidHom.comp (Units.coeHom _))

theorem glEnd_injective (K : Type*) [Field K] [Algebra F K] (n : ℕ) :
    Function.Injective (glEnd (F := F) K n) := by
  intro a b h
  apply Units.ext
  have h1 : (a : Matrix (Fin n) (Fin n) F).map (algebraMap F K) =
      (b : Matrix (Fin n) (Fin n) F).map (algebraMap F K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective h
  exact Matrix.map_injective (algebraMap F K).injective h1

theorem exists_pow_commute_of_mem_normalizer {A : Subgroup (GL (Fin 4) F)} [Finite A]
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hcard : (Nat.card A : F) ≠ 0)
    {g : GL (Fin 4) F} (hg : g ∈ normalizer A) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ ∀ a ∈ A, g ^ k * a = a * g ^ k := by
  classical
  let K := AlgebraicClosure F
  let φ := glEnd (F := F) K 4
  let f : A → Module.End K (Fin 4 → K) := fun a => φ a
  have hcK : ((Nat.card A : ℕ) : K) ≠ 0 := by
    rw [← map_natCast (algebraMap F K)]
    exact (map_ne_zero _).mpr hcard
  have hss : ∀ a : A, (f a).IsFinitelySemisimple := by
    intro a
    apply Module.End.IsSemisimple.isFinitelySemisimple
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : K) hcK one_ne_zero).squarefree
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one, sub_eq_zero]
    change (φ a) ^ Nat.card A = 1
    rw [← map_pow, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one, map_one]
  have hc : ∀ a b : A, Commute (f a) (f b) := fun a b => by
    change φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, hA a a.2 b b.2]
  set W : (A → K) → Submodule K (Fin 4 → K) := fun χ => ⨅ a, (f a).eigenspace (χ a) with hWdef
  have hWmax : ∀ χ : A → K, ⨅ a, (f a).maxGenEigenspace (χ a) = W χ := fun χ => by
    simp only [hWdef, (hss _).maxGenEigenspace_eq_eigenspace]
  have htop : ⨆ χ, W χ = ⊤ := by
    have := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun a b _ => hc a b) (fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a))
    simpa only [hWmax] using this
  have hind : iSupIndep W := by
    have := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ)
    simpa only [hWmax] using this
  let : Fintype {χ // W χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  have hS : Fintype.card {χ // W χ ≠ ⊥} ≤ 4 := by
    have := hind.subtype_ne_bot_le_finrank
    simpa using this
  have hg' : g⁻¹ ∈ normalizer A := inv_mem hg
  have hcA : ∀ a ∈ A, g⁻¹ * a * g ∈ A := fun a ha => by
    have := (mem_normalizer_iff.mp hg' a).mp ha
    rwa [inv_inv] at this
  let c : A → A := fun a => ⟨g⁻¹ * a * g, hcA a a.2⟩
  have hcsurj : Function.Surjective c := fun a =>
    ⟨⟨g * a * g⁻¹, (mem_normalizer_iff.mp hg a).mp a.2⟩, Subtype.ext (by simp [c, mul_assoc])⟩
  let T : (A → K) → (A → K) := fun χ => χ ∘ c
  have hTinj : Function.Injective T := fun χ χ' h => by
    funext a
    obtain ⟨b, rfl⟩ := hcsurj a
    exact congrFun h b
  have hmaps : ∀ χ, ∀ v ∈ W χ, φ g v ∈ W (T χ) := by
    intro χ v hv
    simp only [hWdef, Submodule.mem_iInf] at hv ⊢
    intro a
    rw [Module.End.mem_eigenspace_iff]
    have h1 := Module.End.mem_eigenspace_iff.mp (hv (c a))
    have h2 : (a : GL (Fin 4) F) * g = g * (g⁻¹ * a * g) := by group
    change φ a (φ g v) = _
    rw [← Module.End.mul_apply, ← map_mul, h2, map_mul, Module.End.mul_apply]
    change φ g (f (c a) v) = _
    rw [h1, map_smul]
    rfl
  have hinj : ∀ v, φ g v = 0 → v = 0 := fun v hv => by
    have h1 : φ g⁻¹ (φ g v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hv, map_zero]
  have hTS : ∀ χ, W χ ≠ ⊥ → W (T χ) ≠ ⊥ := by
    intro χ hχ hb
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    have := hmaps χ v hv
    rw [hb, Submodule.mem_bot] at this
    exact hv0 (hinj v this)
  let σ₀ : {χ // W χ ≠ ⊥} → {χ // W χ ≠ ⊥} := fun s => ⟨T s.1, hTS s.1 s.2⟩
  have hσ₀ : Function.Injective σ₀ := fun s t h =>
    Subtype.ext (hTinj (congrArg Subtype.val h))
  let σ : Equiv.Perm {χ // W χ ≠ ⊥} :=
    Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hσ₀)
  obtain ⟨k, hk1, hk4, hk⟩ := exists_perm_pow_eq_one hS σ
  have hσk : ∀ j (s : {χ // W χ ≠ ⊥}), ((σ ^ j) s).1 = T^[j] s.1 := by
    intro j
    induction j with
    | zero => intro s; rfl
    | succ j ih =>
      intro s
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply', ← ih]
      rfl
  have hTk : ∀ j (χ : A → K) (a : A), T^[j] χ a = χ (c^[j] a) := by
    intro j
    induction j with
    | zero => intro χ a; rfl
    | succ j ih =>
      intro χ a
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply']
      rfl
  have hck : ∀ j (a : A), ((c^[j] a : A) : GL (Fin 4) F) = (g ^ j)⁻¹ * a * g ^ j := by
    intro j
    induction j with
    | zero => intro a; simp
    | succ j ih =>
      intro a
      rw [Function.iterate_succ_apply', pow_succ]
      change g⁻¹ * ((c^[j] a : A) : GL (Fin 4) F) * g = _
      rw [ih]
      group
  have hfix : ∀ χ, W χ ≠ ⊥ → ∀ a, χ (c^[k] a) = χ a := by
    intro χ hχ a
    have h1 := hσk k ⟨χ, hχ⟩
    rw [hk, Equiv.Perm.one_apply] at h1
    rw [← hTk k χ a, ← h1]
  refine ⟨k, hk1, hk4, fun a ha => ?_⟩
  have hfa : f (c^[k] ⟨a, ha⟩) = f ⟨a, ha⟩ := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ ⨆ χ, W χ := htop ▸ Submodule.mem_top
    refine Submodule.iSup_induction W (motive := fun v => f (c^[k] ⟨a, ha⟩) v = f ⟨a, ha⟩ v)
      hv ?_ ?_ ?_
    · intro χ w hw
      by_cases hχ : W χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hw
        rw [hw, map_zero, map_zero]
      · have h1 := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hw (c^[k] ⟨a, ha⟩))
        have h2 := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hw ⟨a, ha⟩)
        rw [h1, h2, hfix χ hχ]
    · rw [map_zero, map_zero]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  have h1 : (g ^ k)⁻¹ * a * g ^ k = a := by
    have h2 : ((c^[k] ⟨a, ha⟩ : A) : GL (Fin 4) F) = (g ^ k)⁻¹ * a * g ^ k := hck k ⟨a, ha⟩
    rw [← h2]
    exact glEnd_injective K 4 hfa
  calc g ^ k * a = g ^ k * ((g ^ k)⁻¹ * a * g ^ k) := by rw [h1]
    _ = a * g ^ k := by group

theorem mul_comm_of_mem_closure_pair {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    {x y : G} (hx : x ∈ closure ({a, b} : Set G)) (hy : y ∈ closure ({a, b} : Set G)) :
    x * y = y * x := by
  have hcen : closure ({a, b} : Set G) ≤ centralizer (closure ({a, b} : Set G)) := by
    rw [closure_le]
    intro u hu
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro v hv
    induction hv using closure_induction with
    | mem w hw =>
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · rfl
      · exact hab.symm
      · exact hab
      · rfl
    | one => rw [one_mul, mul_one]
    | mul v w _ _ hv hw => rw [mul_assoc, hw, ← mul_assoc, hv, mul_assoc]
    | inv v _ hv =>
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hv, mul_assoc, mul_inv_cancel, mul_one]
  exact mem_centralizer_iff.mp (hcen hy) x hx

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer H := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let c : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hc : Function.Injective c := fun y₁ y₂ e => by
    have h1 := congrArg Subtype.val e
    simp only [c, mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hc) ⟨g * x * g⁻¹, hx⟩
  have h1 := congrArg Subtype.val hy
  simp only [c, mul_left_inj, mul_right_inj] at h1
  exact h1 ▸ y.2

theorem commute_of_isPGroup {r : ℕ} [hr : Fact r.Prime] (hr5 : 5 ≤ r) (hrF : (r : F) ≠ 0)
    {Q : Subgroup (GL (Fin 4) F)} [Finite Q] (hQ : IsPGroup r Q) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  by_contra hne
  push Not at hne
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hne
  have hZ : center Q ≠ ⊤ := by
    intro h
    have h1 := mem_center_iff.mp (h ▸ mem_top (⟨a₀, ha₀⟩ : Q)) ⟨b₀, hb₀⟩
    exact hab (congrArg Subtype.val h1).symm
  have : Nontrivial (Q ⧸ center Q) := QuotientGroup.nontrivial_iff.mpr hZ
  have : Nontrivial (center (Q ⧸ center Q)) := (hQ.to_quotient (center Q)).center_nontrivial
  obtain ⟨xb, hxb⟩ := exists_ne (1 : center (Q ⧸ center Q))
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (xb : Q ⧸ center Q)
  have hxZ : x ∉ center Q := by
    intro h
    apply hxb
    apply Subtype.ext
    rw [← hx, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
    exact h
  obtain ⟨y, hy⟩ : ∃ y : Q, y * x ≠ x * y := by
    by_contra h
    push Not at h
    exact hxZ (mem_center_iff.mpr h)
  set z : Q := y * x * y⁻¹ * x⁻¹ with hzdef
  have hzZ : z ∈ center Q := by
    rw [← QuotientGroup.eq_one_iff, hzdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hx,
      mem_center_iff.mp xb.2 (y : Q ⧸ center Q)]
    group
  have hz1 : z ≠ 1 := by
    intro h
    apply hy
    rw [hzdef, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  set X : GL (Fin 4) F := (x : GL (Fin 4) F) with hX
  set Y : GL (Fin 4) F := (y : GL (Fin 4) F) with hY
  set Z : GL (Fin 4) F := (z : GL (Fin 4) F) with hZdef
  have hZc : ∀ q ∈ Q, Z * q = q * Z := fun q hq =>
    congrArg Subtype.val (mem_center_iff.mp hzZ ⟨q, hq⟩).symm
  have hYX : Y * X = Z * X * Y := by
    rw [hY, hX, hZdef, hzdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hZ1 : Z ≠ 1 := fun h => hz1 (Subtype.ext h)
  set A := closure ({X, Z} : Set (GL (Fin 4) F)) with hAdef
  have hAQ : A ≤ Q := by
    rw [hAdef, closure_le]
    rintro _ (rfl | rfl)
    · exact x.2
    · exact z.2
  have : Finite A := Finite.of_injective (Subgroup.inclusion hAQ) (Subgroup.inclusion_injective hAQ)
  have hXZ : X * Z = Z * X := (hZc X x.2).symm
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    mul_comm_of_mem_closure_pair hXZ ha hb
  have hcardA : (Nat.card A : F) ≠ 0 := by
    obtain ⟨m, hm⟩ := hQ.exists_card_eq
    obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hAQ
    intro h0
    apply pow_ne_zero m hrF
    rw [← Nat.cast_pow, ← hm, hd, Nat.cast_mul, h0, zero_mul]
  have hconj : ∀ u ∈ A, Y * u * Y⁻¹ ∈ A := by
    intro u hu
    rw [hAdef] at hu
    induction hu using closure_induction with
    | mem w hw =>
      rcases hw with rfl | rfl
      · rw [hYX, mul_inv_cancel_right]
        exact mul_mem (subset_closure (Set.mem_insert_of_mem _ rfl))
          (subset_closure (Set.mem_insert _ _))
      · rw [← hZc Y y.2, mul_inv_cancel_right]
        exact subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul v w _ _ hv hw =>
      have : Y * (v * w) * Y⁻¹ = (Y * v * Y⁻¹) * (Y * w * Y⁻¹) := by group
      rw [this]
      exact mul_mem hv hw
    | inv v _ hv =>
      have : Y * v⁻¹ * Y⁻¹ = (Y * v * Y⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hv
  obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_commute_of_mem_normalizer hAcomm hcardA
    (mem_normalizer_of_forall_conj_mem hconj)
  have hYk : ∀ j : ℕ, Y ^ j * X = Z ^ j * X * Y ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hYZ : Y * Z ^ j = Z ^ j * Y := (Commute.pow_left (hZc Y y.2) j).eq.symm
      calc Y ^ (j + 1) * X = Y * (Y ^ j * X) := by rw [pow_succ', mul_assoc]
        _ = Y * Z ^ j * X * Y ^ j := by rw [ih]; simp only [mul_assoc]
        _ = Z ^ j * (Y * X) * Y ^ j := by rw [hYZ]; simp only [mul_assoc]
        _ = Z ^ (j + 1) * X * Y ^ (j + 1) := by
          rw [hYX, pow_succ Z j, pow_succ' Y j]; simp only [mul_assoc]
  have hZk : Z ^ k = 1 := by
    have h1 := hk X (subset_closure (Set.mem_insert _ _))
    rw [hYk k] at h1
    have h2 : Z ^ k * X * Y ^ k = 1 * X * Y ^ k := by rw [h1, one_mul]
    exact mul_right_cancel (mul_right_cancel h2)
  have hzQ : (⟨Z, z.2⟩ : Q) ≠ 1 := fun h => hZ1 (congrArg Subtype.val h)
  obtain ⟨j, hj⟩ := hQ ⟨Z, z.2⟩
  have hdvd : orderOf Z ∣ r ^ j := by
    rw [← Subgroup.orderOf_mk Z z.2]
    exact orderOf_dvd_of_pow_eq_one hj
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr.out).mp hdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hi
    exact hZ1 hi
  have hrk : r ∣ k := by
    have := orderOf_dvd_of_pow_eq_one hZk
    rw [hi] at this
    exact (dvd_pow_self r hi0).trans this
  have := Nat.le_of_dvd (by omega) hrk
  omega

end CFSG.RankThree.PartTwo.Sec4.Census
