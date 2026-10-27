module

public import CFSG.Quasithin.Vol2.F134LieOddModel
public import CFSG.Quasithin.Vol2.F134LieOddMatrix

public section

namespace CFSG.Quasithin.F134.LieOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem torus3_mono {M₁ M₂ : Subgroup Kˣ} (h : M₁ ≤ M₂) : torus3 M₁ ≤ torus3 M₂ := by
  intro x hx
  obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M₁).1 hx
  exact (mem_torus3 M₂).2 ⟨d, fun i => h (hdM i), hd, rfl⟩

@[expose] noncomputable def cubeScalar (M : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) where
  carrier := {y | y ∈ torus3 M ∧ ∃ c : Kˣ, y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c}
  mul_mem' := by
    rintro y z ⟨hy, c, hc⟩ ⟨hz, c', hc'⟩
    refine ⟨mul_mem hy hz, c * c', ?_⟩
    rw [Commute.mul_pow (torus3_comm M hy hz), hc, hc', map_mul]
  one_mem' := ⟨one_mem _, 1, by rw [one_pow, map_one]⟩
  inv_mem' := by
    rintro y ⟨hy, c, hc⟩
    exact ⟨inv_mem hy, c⁻¹, by rw [inv_pow, hc, map_inv]⟩

theorem card_cubeScalar_le [Finite K] (M : Subgroup Kˣ) : Nat.card (cubeScalar M) ≤ 27 :=
  card_le_of_le_torus3_of_cube (fun _ hy => hy.1) (fun _ hy => hy.2)

theorem diagHom_pow (d : Fin 3 → Kˣ) (n : ℕ) : diagHom 3 d ^ n = diagHom 3 (d ^ n) :=
  (map_pow _ _ _).symm

variable {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

namespace OddModel

variable (h : OddModel H M)
include h

theorem torus3_three_le : torus3 (rootsOfUnity 3 K) ≤ torus3 M :=
  torus3_mono fun c hc => h.mu3 c ((mem_rootsOfUnity _ _).1 hc)

theorem torus3_three_le_cubeScalar : torus3 (rootsOfUnity 3 K) ≤ cubeScalar M := by
  intro y hy
  refine ⟨h.torus3_three_le hy, 1, ?_⟩
  obtain ⟨d, hdM, -, rfl⟩ := (mem_torus3 _).1 hy
  rw [map_one, diagHom_pow]
  have : d ^ 3 = 1 := funext fun i => (mem_rootsOfUnity _ _).1 (hdM i)
  rw [this, map_one]

theorem card_torus3_three [Finite K] : Nat.card (torus3 (rootsOfUnity 3 K)) = 9 := by
  rw [card_torus3, h.card_rootsOfUnity_three]
  norm_num

theorem mem_torus3_of_isDiag3 {g : GL (Fin 3) K} (hg : g ∈ H)
    (hd : IsDiag3 (g : Matrix (Fin 3) (Fin 3) K)) : g ∈ torus3 M := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := h.mono.det_eq_one g hg
  have hdiag := hd.eq_diagonal
  rw [hdiag, det_diagonal, Fin.prod_univ_three] at hdet
  have hne : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    have h2 := right_ne_zero_of_mul_eq_one hdet
    have h01 := left_ne_zero_of_mul_eq_one hdet
    intro i
    fin_cases i
    exacts [left_ne_zero_of_mul h01, right_ne_zero_of_mul h01, h2]
  set d : Fin 3 → Kˣ := fun i => Units.mk0 _ (hne i)
  have hgd : g = diagHom 3 d := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [coe_diagHom, hdiag]
    rfl
  have hprod : d 0 * d 1 * d 2 = 1 := Units.ext (by simpa [d] using hdet)
  rw [hgd] at hg ⊢
  exact (mem_torus3 M).2 ⟨d, h.diag d hg, hprod, rfl⟩

omit h in
theorem commute_diag_of_centralizes {P : Subgroup (StatedProj H)} {g : H}
    (hg : ∀ y ∈ P, proj H g * y = y * proj H g) {x : H} (hx : proj H x ∈ P) {d : Fin 3 → Kˣ}
    (hxd : (x : GL (Fin 3) K) = diagHom 3 d) (htr : (d 0 : K) + d 1 + d 2 ≠ 0) :
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => (d i : K)) =
      diagonal (fun i => (d i : K)) * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨c, hc⟩ := mem_scal_iff.1 (commutator_mem_scal (hg _ hx))
  have hgl : (g : GL (Fin 3) K) * diagHom 3 d * (g : GL (Fin 3) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * diagHom 3 d := by
    rw [← hxd, ← hc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hmat : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => (d i : K)) *
      (((g : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • diagonal (fun i => (d i : K)) := by
    have := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hgl
    simp only [Units.val_mul, coe_diagHom, GeneralLinearGroup.coe_scalar] at this
    rw [this, smul_eq_diagonal_mul]
    rfl
  have hc1 : (c : K) = 1 := eq_one_of_conj_eq_smul (by simp)
    (by rw [trace_diagonal, Fin.sum_univ_three]; exact htr) hmat
  rw [show c = 1 from Units.ext hc1, map_one, one_mul] at hgl
  have hgl' : (g : GL (Fin 3) K) * diagHom 3 d = diagHom 3 d * (g : GL (Fin 3) K) := by
    rw [← mul_inv_eq_iff_eq_mul, hgl]
  have := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hgl'
  simpa only [Units.val_mul, coe_diagHom] using this

section Toral

variable [Finite K] {P : Subgroup (StatedProj H)} (hP : Nat.card P = 9)
  (hexp : ∀ x ∈ P, x ^ 3 = 1) (htor : ∀ x : H, proj H x ∈ P → (x : GL (Fin 3) K) ∈ torus3 M)
include hP hexp htor

theorem toral_eq_cubeScalar : (P.comap (proj H)).map H.subtype = cubeScalar M := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨htor x hx, ?_⟩
    have h3 : x ^ 3 ∈ scal H := proj_eq_one_iff.1 (by rw [map_pow]; exact hexp _ hx)
    obtain ⟨c, hc⟩ := mem_scal_iff.1 h3
    exact ⟨c, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hc]⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, h.card_comap, hP]
    exact card_cubeScalar_le M

theorem exists_nine : ∃ a : Kˣ, a ∈ M ∧ a ^ 9 = 1 ∧ a ^ 3 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle : cubeScalar M ≤ torus3 (rootsOfUnity 3 K) := by
    rintro y ⟨hy, c, hc⟩
    obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M).1 hy
    rw [diagHom_pow, scalar_eq_diagHom] at hc
    have hdc : ∀ i, d i ^ 3 = c := fun i => congrFun (diagHom_injective 3 hc) i
    have hc3 : c ^ 3 = 1 := by
      calc c ^ 3 = d 0 ^ 3 * d 1 ^ 3 * d 2 ^ 3 := by rw [hdc 0, hdc 1, hdc 2, pow_three']
        _ = (d 0 * d 1 * d 2) ^ 3 := by rw [mul_pow, mul_pow]
        _ = 1 := by rw [hd, one_pow]
    refine (mem_torus3 _).2 ⟨d, fun i => (mem_rootsOfUnity _ _).2 (hcon (d i) (hdM i) ?_), hd, rfl⟩
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hdc i, hc3]
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_torus3_three, ← h.toral_eq_cubeScalar hP hexp htor,
    Subgroup.card_map_of_injective H.subtype_injective, h.card_comap, hP] at h1
  omega

theorem exists_lift_diag {a : Kˣ} {d : Fin 3 → Kˣ} (hdM : ∀ i, d i ∈ M)
    (hd : d 0 * d 1 * d 2 = 1) (hd3 : ∀ i, d i ^ 3 = a ^ 3) :
    ∃ x : H, proj H x ∈ P ∧ (x : GL (Fin 3) K) = diagHom 3 d := by
  have hmem : diagHom 3 d ∈ cubeScalar M := by
    refine ⟨(mem_torus3 M).2 ⟨d, hdM, hd, rfl⟩, a ^ 3, ?_⟩
    rw [diagHom_pow, scalar_eq_diagHom]
    congr 1
    funext i
    exact hd3 i
  rw [← h.toral_eq_cubeScalar hP hexp htor] at hmem
  obtain ⟨x, hx, hxd⟩ := hmem
  exact ⟨x, hx, hxd⟩

theorem mem_torus3_of_centralizes {g : H} (hg : ∀ y ∈ P, proj H g * y = y * proj H g) :
    (g : GL (Fin 3) K) ∈ torus3 M := by
  obtain ⟨a, haM, ha9, ha3⟩ := h.exists_nine hP hexp htor
  have hb3 : (a⁻¹ * a⁻¹) ^ 3 = a ^ 3 := by
    rw [show (a⁻¹ * a⁻¹) ^ 3 = (a ^ 9)⁻¹ * a ^ 3 by group, ha9, inv_one, one_mul]
  have hbM : a⁻¹ * a⁻¹ ∈ M := M.mul_mem (M.inv_mem haM) (M.inv_mem haM)
  have hab : (a : K) ≠ ((a⁻¹ * a⁻¹ : Kˣ) : K) := by
    intro hab
    apply ha3
    have e := Units.ext hab
    calc a ^ 3 = a * a * a := pow_three' a
      _ = (a⁻¹ * a⁻¹) * a * a := by rw [← e]
      _ = 1 := by group
  have ha9K : (a : K) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, ha9, Units.val_one]
  have htr : (a : K) + a + ((a⁻¹ * a⁻¹ : Kˣ) : K) ≠ 0 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact two_mul_add_inv_ne_zero h.three ha9K
  obtain ⟨x₁, hx₁, hxd₁⟩ := h.exists_lift_diag hP hexp htor (a := a)
    (d := ![a, a, a⁻¹ * a⁻¹]) (fun i => by fin_cases i <;> simp [haM, hbM]) (by simp)
    (fun i => by fin_cases i <;> simp [hb3])
  obtain ⟨x₂, hx₂, hxd₂⟩ := h.exists_lift_diag hP hexp htor (a := a)
    (d := ![a, a⁻¹ * a⁻¹, a]) (fun i => by fin_cases i <;> simp [haM, hbM]) (by simp)
    (fun i => by fin_cases i <;> simp [hb3])
  have hc₁ := commute_diag_of_centralizes hg hx₁ hxd₁ (by simpa using htr)
  have hc₂ := commute_diag_of_centralizes hg hx₂ hxd₂ (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [add_right_comm]
    simpa using htr)
  refine h.mem_torus3_of_isDiag3 g.2 fun i j hij => ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact offDiag_eq_zero_of_commute_diagonal hc₂ (by simpa using hab)
  · exact offDiag_eq_zero_of_commute_diagonal hc₁ (by simpa using hab)
  · exact offDiag_eq_zero_of_commute_diagonal hc₂ (by simpa using hab.symm)
  · exact absurd rfl hij
  · exact offDiag_eq_zero_of_commute_diagonal hc₁ (by simpa using hab)
  · exact offDiag_eq_zero_of_commute_diagonal hc₁ (by simpa using hab.symm)
  · exact offDiag_eq_zero_of_commute_diagonal hc₁ (by simpa using hab.symm)
  · exact absurd rfl hij

end Toral

theorem three_dvd_card [Finite K] : 3 ∣ Nat.card M := by
  obtain ⟨ω, hω3, hω1⟩ := h.prim
  have hord : orderOf (⟨ω, h.mu3 ω hω3⟩ : M) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hω3)) (fun h1 => hω1 (congrArg Subtype.val h1))
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem exists_pow_eq [Finite K] {u : Kˣ} (hu3 : u ^ 3 = 1) :
    ∃ v ∈ M, v ^ (Nat.card M / 3) = u := by
  have : IsCyclic M := isCyclic_subgroup_units M
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := M)
  have hord : orderOf γ = Nat.card M := orderOf_eq_card_of_forall_mem_zpowers hγ
  have huM := h.mu3 u hu3
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨u, huM⟩)
  set m := Nat.card M / 3 with hmdef
  have hm : Nat.card M = 3 * m := (Nat.mul_div_cancel' h.three_dvd_card).symm
  have h3k : ((3 * m : ℕ) : ℤ) ∣ 3 * k := by
    rw [← hm, ← hord, orderOf_dvd_iff_zpow_eq_one, mul_comm, _root_.zpow_mul, hk]
    exact Subtype.ext (by simpa using hu3)
  obtain ⟨j, hj⟩ : (m : ℤ) ∣ k := by
    push_cast at h3k
    exact (Int.dvd_of_mul_dvd_mul_left (by norm_num) h3k)
  refine ⟨((γ ^ j : M) : Kˣ), (γ ^ j).2, ?_⟩
  have : (γ ^ j) ^ m = ⟨u, huM⟩ := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, ← hj, hk]
  rw [← Subgroup.coe_pow, this]

theorem pow_mem_torus3_three [Finite K] {t : GL (Fin 3) K} (ht : t ∈ torus3 M) :
    t ^ (Nat.card M / 3) ∈ torus3 (rootsOfUnity 3 K) := by
  obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M).1 ht
  have hm : Nat.card M = 3 * (Nat.card M / 3) := (Nat.mul_div_cancel' h.three_dvd_card).symm
  rw [diagHom_pow]
  refine (mem_torus3 _).2 ⟨d ^ (Nat.card M / 3), fun i => ?_, ?_, rfl⟩
  · rw [mem_rootsOfUnity, Pi.pow_apply, ← pow_mul, mul_comm, ← hm]
    have := pow_card_eq_one' (G := M) (x := ⟨d i, hdM i⟩)
    exact congrArg Subtype.val this
  · simp only [Pi.pow_apply]
    rw [← mul_pow, ← mul_pow, hd, one_pow]

@[expose] noncomputable def toralQ (H : Subgroup (GL (Fin 3) K)) : Subgroup (StatedProj H) :=
  ((torus3 (rootsOfUnity 3 K)).comap H.subtype).map (proj H)

theorem card_toralQ [Finite K] : Nat.card (toralQ H) = 3 := by
  have hT : torus3 (rootsOfUnity 3 K) ≤ H := h.torus3_three_le.trans (torus3_le M h.mono)
  set T' := (torus3 (rootsOfUnity 3 K)).comap H.subtype with hT'def
  have hT'card : Nat.card T' = 9 := by
    rw [← h.card_torus3_three]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
  have hker : scal H ≤ T' := by
    intro x hx
    obtain ⟨c, hc⟩ := mem_scal_iff.1 hx
    have hc3 := h.cube_eq_one_of_scalar hc
    show (x : GL (Fin 3) K) ∈ torus3 (rootsOfUnity 3 K)
    rw [hc, scalar_eq_diagHom]
    exact (mem_torus3 _).2 ⟨fun _ => c, fun _ => (mem_rootsOfUnity _ _).2 hc3,
      by rw [← pow_three', hc3], rfl⟩
  have hcomap : (toralQ H).comap (proj H) = T' := by
    rw [toralQ, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hker]
  have := h.card_comap (toralQ H)
  rw [hcomap, hT'card] at this
  omega

section Toral

variable [Finite K] {P : Subgroup (StatedProj H)} (hP : Nat.card P = 9)
  (hexp : ∀ x ∈ P, x ^ 3 = 1) (htor : ∀ x : H, proj H x ∈ P → (x : GL (Fin 3) K) ∈ torus3 M)
include hP hexp htor

theorem toralQ_le : toralQ H ≤ P := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (x : GL (Fin 3) K) ∈ cubeScalar M := h.torus3_three_le_cubeScalar hx
  rw [← h.toral_eq_cubeScalar hP hexp htor] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  rw [show x = y from Subtype.ext hyx.symm]
  exact hy

theorem mem_toralQ_iff {z : StatedProj H} :
    z ∈ toralQ H ↔ ∃ c : StatedProj H, (∀ y ∈ P, c * y = y * c) ∧ z = c ^ (Nat.card M / 3) := by
  have hcomm : ∀ g : H, (g : GL (Fin 3) K) ∈ torus3 M → ∀ y ∈ P, proj H g * y = y * proj H g := by
    intro g hg y hy
    obtain ⟨x, rfl⟩ := proj_surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (torus3_comm M hg (htor x hy))
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨d, hdM, hd, hdt⟩ := (mem_torus3 _).1 (show (t : GL (Fin 3) K) ∈ _ from ht)
    have hd3 : ∀ i, d i ^ 3 = 1 := fun i => (mem_rootsOfUnity _ _).1 (hdM i)
    obtain ⟨v₀, hv₀M, hv₀⟩ := h.exists_pow_eq (hd3 0)
    obtain ⟨v₁, hv₁M, hv₁⟩ := h.exists_pow_eq (hd3 1)
    set g := diagHom 3 ![v₀, v₁, (v₀ * v₁)⁻¹] with hgdef
    have hgT : g ∈ torus3 M :=
      (mem_torus3 M).2 ⟨_, fun i => by fin_cases i <;> simp [hv₀M, hv₁M, M.mul_mem, M.inv_mem],
        by simp, rfl⟩
    have hgH : g ∈ H := torus3_le M h.mono hgT
    refine ⟨proj H ⟨g, hgH⟩, hcomm _ hgT, ?_⟩
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow, hdt]
    show diagHom 3 d = g ^ (Nat.card M / 3)
    rw [hgdef, diagHom_pow]
    congr 1
    have hd2 : d 2 = (d 0 * d 1)⁻¹ := eq_inv_of_mul_eq_one_right hd
    funext i
    fin_cases i
    · simp [hv₀]
    · simp [hv₁]
    · simp [hd2, inv_pow, mul_pow, hv₀, hv₁]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective c
    have hgT := h.mem_torus3_of_centralizes hP hexp htor hc
    refine ⟨g ^ (Nat.card M / 3), ?_, by rw [map_pow]⟩
    show ((g ^ (Nat.card M / 3) : H) : GL (Fin 3) K) ∈ torus3 (rootsOfUnity 3 K)
    rw [Subgroup.coe_pow]
    exact h.pow_mem_torus3_three hgT

theorem toral : ∃ Q : Subgroup (StatedProj H), Q ≤ P ∧ Nat.card Q = 3 ∧
    ∀ α : StatedProj H ≃* StatedProj H, P.map α.toMonoidHom = P → Q.map α.toMonoidHom = Q := by
  refine ⟨toralQ H, h.toralQ_le hP hexp htor, h.card_toralQ, fun α hα => ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (h.mem_toralQ_iff hP hexp htor).1 hz
    refine (h.mem_toralQ_iff hP hexp htor).2 ⟨α c, fun y hy => ?_, by
      simp only [MulEquiv.coe_toMonoidHom, map_pow]⟩
    rw [← hα] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc y' hy']
  · rw [Subgroup.card_map_of_injective α.injective]

end Toral

end OddModel

end CFSG.Quasithin.F134.LieOdd
