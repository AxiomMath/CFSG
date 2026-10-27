module

public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompL3
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418SylowCenter

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace SylowCenterSLEps3

open Matrix F618Comp

variable {K : Type} [Field K]

theorem cube_root_ne {i c : K} (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (hc : c ^ 3 = 1) :
    c ≠ -1 ∧ c ≠ i ∧ c ≠ -i := by
  refine ⟨fun h => h2 ?_, fun h => h2 ?_, fun h => h2 ?_⟩
  · rw [h] at hc
    linear_combination -hc
  · rw [h] at hc
    linear_combination (i - 1) * hc + (1 - i * (i - 1)) * hi
  · rw [h] at hc
    linear_combination (-(i + 1)) * hc + (1 - i * (i + 1)) * hi

theorem eq_zero_of_mul_eq {x y c m : K} (h : x * m = c * (m * y)) (hne : x ≠ c * y) : m = 0 := by
  by_contra hm
  exact hne (mul_right_cancel₀ hm (by rw [h]; ring))

theorem eq_diagonal_of_mul_eq {i c : K} (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (hc : c ^ 3 = 1)
    {M : Matrix (Fin 3) (Fin 3) K}
    (h : diagonal ![i, -i, 1] * M = c • (M * diagonal ![i, -i, 1])) :
    M = diagonal ![M 0 0, M 1 1, M 2 2] := by
  obtain ⟨hc1, hci, hcni⟩ := cube_root_ne hi h2 hc
  have key : ∀ a b, ![i, -i, 1] a * M a b = c * (M a b * ![i, -i, 1] b) := fun a b => by
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using congrFun (congrFun h a) b
  have h01 : M 0 1 = 0 := eq_zero_of_mul_eq (x := i) (y := -i) (key 0 1)
    fun h => hc1 (by linear_combination (-i) * h + (c + 1) * hi)
  have h02 : M 0 2 = 0 := eq_zero_of_mul_eq (x := i) (y := 1) (key 0 2)
    fun h => hci (by linear_combination -h)
  have h10 : M 1 0 = 0 := eq_zero_of_mul_eq (x := -i) (y := i) (key 1 0)
    fun h => hc1 (by linear_combination i * h + (c + 1) * hi)
  have h12 : M 1 2 = 0 := eq_zero_of_mul_eq (x := -i) (y := 1) (key 1 2)
    fun h => hcni (by linear_combination -h)
  have h20 : M 2 0 = 0 := eq_zero_of_mul_eq (x := 1) (y := i) (key 2 0)
    fun h => hcni (by linear_combination i * h + c * hi)
  have h21 : M 2 1 = 0 := eq_zero_of_mul_eq (x := 1) (y := -i) (key 2 1)
    fun h => hci (by linear_combination (-i) * h + c * hi)
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h01, h02, h10, h12, h20, h21]

theorem eq_of_rotMat_mul_eq {a b d c : K} (hd : d ≠ 0)
    (h : rotMat K * diagonal ![a, b, d] = c • (diagonal ![a, b, d] * rotMat K)) : b = a := by
  have h01 : b = c * a := by
    simpa [rotMat, Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h 0) 1
  have h22 : d = c * d := by
    simpa [rotMat, Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h 2) 2
  have hc : c = 1 := by
    have : (c - 1) * d = 0 := by linear_combination -h22
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hd
  rw [h01, hc, one_mul]

theorem row_zero_of_mul_eq {i c : K} (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (hc : c ^ 3 = 1)
    {X : Matrix (Fin 3) (Fin 3) K}
    (h : diagonal ![i, i, -1] * X * diagonal ![i, i, -1] = c • X) : ∀ j, X 0 j = 0 := by
  obtain ⟨hc1, -, hcni⟩ := cube_root_ne hi h2 hc
  have key : ∀ j, i * X 0 j * ![i, i, -1] j = c * X 0 j := fun j => by
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using congrFun (congrFun h 0) j
  have hii : i * i ≠ c * 1 := fun h => hc1 (by linear_combination -h + hi)
  have k0 : i * X 0 0 * i = c * X 0 0 := key 0
  have k1 : i * X 0 1 * i = c * X 0 1 := key 1
  have k2 : i * X 0 2 * -1 = c * X 0 2 := key 2
  have e0 : X 0 0 = 0 := eq_zero_of_mul_eq (by linear_combination k0) hii
  have e1 : X 0 1 = 0 := eq_zero_of_mul_eq (by linear_combination k1) hii
  have e2 : X 0 2 = 0 := eq_zero_of_mul_eq (x := -i) (y := 1) (c := c)
    (by linear_combination k2) fun h => hcni (by linear_combination -h)
  intro j
  fin_cases j
  exacts [e0, e1, e2]

section Groups

variable {G : Type*} [Group G]

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : IsPGroup p M) (P : Sylow p G) : ∃ x : G, ∀ m ∈ M, x * m * x⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hM.exists_le_sylow
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨x, fun m hm => ?_⟩
  rw [Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul m (MulAut.conj x) (Q : Subgroup G) (hQ hm)

theorem isPGroup_zpowers {p k : ℕ} {g : G} (hg : g ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨_, n, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hg,
    _root_.one_zpow]

theorem conj_commute_of_mem_center {P : Subgroup G} (z : ↥(Subgroup.center ↥P)) {x a : G}
    (ha : x * a * x⁻¹ ∈ P) :
    x⁻¹ * ((z : ↥P) : G) * x * a = a * (x⁻¹ * ((z : ↥P) : G) * x) := by
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨x * a * x⁻¹, ha⟩)
  simp only [Subgroup.coe_mul] at h
  calc x⁻¹ * ((z : ↥P) : G) * x * a = x⁻¹ * (((z : ↥P) : G) * (x * a * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * a * x⁻¹) * ((z : ↥P) : G)) * x := by rw [h]
    _ = a * (x⁻¹ * ((z : ↥P) : G) * x) := by group

theorem eq_one_of_pow_three (hG : IsPGroup 2 G) {z : G} (hz : z ^ 3 = 1) : z = 1 :=
  orderOf_eq_one_iff.mp
    ((hG.orderOf_coprime (n := 3) (by norm_num) z).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hz))

end Groups

section Quotient

variable {H Z₀ : Subgroup (GL (Fin 3) K)}

theorem exists_smul_of_mk_eq
    (hZ : ∀ s ∈ Z₀, ∃ c : K, (s : Matrix (Fin 3) (Fin 3) K) = c • 1)
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) {A B : ↥H}
    (h : (A : ↥H ⧸ Z₀.subgroupOf H) = B) :
    ∃ c : K, c ^ 3 = 1 ∧ ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := hZ _ h
  refine ⟨c, ?_, ?_⟩
  · have hd := hdet _ (A⁻¹ * B).2
    rwa [hc, det_smul, det_one, Fintype.card_fin, mul_one] at hd
  · have hAB : (B : GL (Fin 3) K) = A * ((A⁻¹ * B : ↥H) : GL (Fin 3) K) := by
      simp
    rw [hAB, Units.val_mul, hc, Matrix.mul_smul, mul_one]

noncomputable def ratio (q : ↥H ⧸ Z₀.subgroupOf H) : K :=
  (((Quotient.out q : ↥H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 /
    (((Quotient.out q : ↥H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2

def IsDiagAAB (q : ↥H ⧸ Z₀.subgroupOf H) : Prop :=
  ∀ A : ↥H, (A : ↥H ⧸ Z₀.subgroupOf H) = q →
    ∃ a b : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, b]

variable (hZ : ∀ s ∈ Z₀, ∃ c : K, (s : Matrix (Fin 3) (Fin 3) K) = c • 1)
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1)
include hZ hdet

theorem ratio_eq {q : ↥H ⧸ Z₀.subgroupOf H} {A : ↥H} (hA : (A : ↥H ⧸ Z₀.subgroupOf H) = q) :
    ratio q = ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 /
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  obtain ⟨c, hc3, hc⟩ := exists_smul_of_mk_eq hZ hdet (hA.trans (QuotientGroup.out_eq' q).symm)
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc3
  rw [ratio, hc, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_div_mul_left _ _ hc0]

theorem ratio_one [(Z₀.subgroupOf H).Normal] : ratio (1 : ↥H ⧸ Z₀.subgroupOf H) = 1 := by
  rw [ratio_eq hZ hdet (A := 1) (QuotientGroup.mk_one _)]
  simp

theorem ratio_mul [(Z₀.subgroupOf H).Normal] {q₁ q₂ : ↥H ⧸ Z₀.subgroupOf H} (h₁ : IsDiagAAB q₁)
    (h₂ : IsDiagAAB q₂) : ratio (q₁ * q₂) = ratio q₁ * ratio q₂ := by
  obtain ⟨A₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨A₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨a₁, b₁, e₁⟩ := h₁ A₁ rfl
  obtain ⟨a₂, b₂, e₂⟩ := h₂ A₂ rfl
  rw [← QuotientGroup.mk_mul, ratio_eq hZ hdet rfl, ratio_eq hZ hdet rfl, ratio_eq hZ hdet rfl,
    Subgroup.coe_mul, Units.val_mul, e₁, e₂, diagonal_mul_diagonal]
  simp only [diagonal_apply_eq]
  simp [mul_div_mul_comm]

theorem pow_three_eq_one_of_ratio [(Z₀.subgroupOf H).Normal] {q : ↥H ⧸ Z₀.subgroupOf H}
    (hq : IsDiagAAB q) (hr : ratio q = 1) : q ^ 3 = 1 := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, b, e⟩ := hq A rfl
  rw [ratio_eq hZ hdet rfl, e] at hr
  have hd := hdet _ A.2
  rw [e, det_diagonal, Fin.prod_univ_three] at hd
  replace hr : a / b = 1 := by simpa using hr
  replace hd : a * a * b = 1 := by simpa using hd
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hd
  obtain rfl : a = b := (div_eq_one_iff_eq hb).mp hr
  have ha3 : a ^ 3 = 1 := by linear_combination hd
  have hA3 : A ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, e, diagonal_pow, OneMemClass.coe_one,
      Units.val_one, ← diagonal_one]
    congr 1
    ext j
    fin_cases j <;> simp [ha3]
  rw [← QuotientGroup.mk_pow, hA3, QuotientGroup.mk_one]

end Quotient

theorem isCyclic_center_sylow {D : Type*} [Group D] [Finite D] {i : K} (hi : i ^ 2 = -1)
    (h2 : (2 : K) ≠ 0) {H Z₀ : Subgroup (GL (Fin 3) K)} [(Z₀.subgroupOf H).Normal]
    (hZ : ∀ s ∈ Z₀, ∃ c : K, (s : Matrix (Fin 3) (Fin 3) K) = c • 1)
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hδ : ∃ δ ∈ H, (δ : Matrix (Fin 3) (Fin 3) K) = diagonal ![i, i, -1])
    (hu : ∃ u ∈ H, (u : Matrix (Fin 3) (Fin 3) K) = diagonal ![i, -i, 1])
    (hR : rotGL K ∈ H)
    (hext : F6.IsExtendedByMatrixMap H Z₀ (fun A => (A⁻¹)ᵀ) D) (P : Sylow 2 D) :
    IsCyclic ↥(Subgroup.center ↥(P : Subgroup D)) := by
  classical
  obtain ⟨δ₀, hδH, hδm⟩ := hδ
  obtain ⟨u₀, huH, hum⟩ := hu
  obtain ⟨N, e, t, g, hidx, ht, hact⟩ := hext
  have hN : N.Normal := Subgroup.normal_of_index_eq_two hidx
  let δ : ↥H := ⟨δ₀, hδH⟩
  let u : ↥H := ⟨u₀, huH⟩
  let R : ↥H := ⟨rotGL K, hR⟩
  have hδm' : ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![i, i, -1] := hδm
  have hum' : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![i, -i, 1] := hum
  have hRm' : ((R : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = rotMat K := coe_rotGL
  let ι : ↥H →* D := N.subtype.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
  have hii : i * i = -1 := by rw [← sq, hi]
  have hi4 : i ^ 4 = 1 := by linear_combination (i ^ 2 - 1) * hi
  have hni4 : (-i) ^ 4 = 1 := by linear_combination (i ^ 2 - 1) * hi
  have hm4 : (-1 : K) ^ 4 = 1 := by norm_num
  have hδ4 : δ ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one, hδm',
      diagonal_pow, ← diagonal_one]
    congr 1
    ext j
    fin_cases j <;> simp [hi4, hm4]
  have hu4 : u ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one, hum',
      diagonal_pow, ← diagonal_one]
    congr 1
    ext j
    fin_cases j <;> simp [hi4, hni4]
  have hR4 : R ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one, hRm',
      rotMat_pow_four]
  have hRu : R * u * R⁻¹ = u⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hRm', hum']
    ext a b
    fin_cases a <;> fin_cases b <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [rotMat, hii]
  have step1 : ∀ y : D, y ∉ N → y * ι δ ≠ ι δ * y := by
    intro y hy hcomm
    have hn : y * t⁻¹ ∈ N := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false hy (fun h => ht (by simpa using N.inv_mem h))
    let m : ↥N := e.symm (δ : ↥H ⧸ Z₀.subgroupOf H)
    let m' : ↥N := ⟨t * m * t⁻¹, hN.conj_mem _ m.2 t⟩
    let B : ↥H := g * δ⁻¹ * g⁻¹
    have hB : e m' = (B : ↥H ⧸ Z₀.subgroupOf H) := by
      refine hact m m' δ B rfl (e.apply_symm_apply _) ?_
      have hT : ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ = (δ : GL (Fin 3) K) := by
        rw [hδm', diagonal_transpose]
      simp only [B, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
      rw [Matrix.transpose_nonsing_inv, hT, Matrix.coe_units_inv]
    have hrel : (⟨y * t⁻¹, hn⟩ : ↥N) * m' * (⟨y * t⁻¹, hn⟩ : ↥N)⁻¹ = m := by
      apply Subtype.ext
      have hc : y * (m : D) = (m : D) * y := hcomm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, m']
      calc y * t⁻¹ * (t * (m : D) * t⁻¹) * (y * t⁻¹)⁻¹ = y * (m : D) * y⁻¹ := by group
        _ = m := by rw [hc]; group
    obtain ⟨C, hC⟩ := QuotientGroup.mk_surjective (e ⟨y * t⁻¹, hn⟩)
    have hq : ((C * B * C⁻¹ : ↥H) : ↥H ⧸ Z₀.subgroupOf H) = (δ : ↥H ⧸ Z₀.subgroupOf H) := by
      have h' := congrArg e hrel
      rw [map_mul, map_mul, map_inv, hB, ← hC, e.apply_symm_apply] at h'
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact h'
    obtain ⟨c, hc3, hc⟩ := exists_smul_of_mk_eq hZ hdet hq
    let h : GL (Fin 3) K := (C : GL (Fin 3) K) * (g : GL (Fin 3) K)
    have hCB : ((C * B * C⁻¹ : ↥H) : GL (Fin 3) K) = h * (δ : GL (Fin 3) K)⁻¹ * h⁻¹ := by
      simp only [B, h, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hCB, Units.val_mul, Units.val_mul] at hc
    have hX : ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) *
        ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • (h : Matrix (Fin 3) (Fin 3) K) := by
      nth_rewrite 1 [hc]
      simp only [Matrix.smul_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [hδm'] at hX
    exact Matrix.GeneralLinearGroup.det_ne_zero h
      (Matrix.det_eq_zero_of_row_eq_zero 0 (row_zero_of_mul_eq hi h2 hc3 hX))
  have step2 : ∀ y : ↥N, (y : D) * ι u = ι u * y → (y : D) * ι R = ι R * y →
      ∀ A : ↥H, e y = (A : ↥H ⧸ Z₀.subgroupOf H) →
        ∃ a b : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, b] := by
    intro y hyu hyR A hA
    have hcomm : ∀ X : ↥H, (y : D) * ι X = ι X * y → ∃ c : K, c ^ 3 = 1 ∧
        ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          c • (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
      intro X hX
      have h1 : y * e.symm (X : ↥H ⧸ Z₀.subgroupOf H) = e.symm (X : ↥H ⧸ Z₀.subgroupOf H) * y :=
        Subtype.ext hX
      have hq := congrArg e h1
      rw [map_mul, map_mul, e.apply_symm_apply, hA, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul] at hq
      obtain ⟨c, hc3, hc⟩ := exists_smul_of_mk_eq hZ hdet hq
      refine ⟨c, hc3, ?_⟩
      simpa only [Subgroup.coe_mul, Units.val_mul] using hc
    obtain ⟨c, hc3, hc⟩ := hcomm u hyu
    rw [hum'] at hc
    have hdiag := eq_diagonal_of_mul_eq hi h2 hc3 hc
    obtain ⟨c', -, hc'⟩ := hcomm R hyR
    rw [hRm', hdiag] at hc'
    have hd : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
      intro h0
      have := hdet _ A.2
      rw [hdiag, det_diagonal, Fin.prod_univ_three] at this
      simp [h0] at this
    exact ⟨_, _, hdiag.trans (by rw [eq_of_rotMat_mul_eq hd hc'])⟩
  have hδ4' : ι δ ^ 2 ^ 2 = 1 := by rw [← map_pow, show 2 ^ 2 = 4 from rfl, hδ4, map_one]
  have hu4' : ι u ^ 2 ^ 2 = 1 := by rw [← map_pow, show 2 ^ 2 = 4 from rfl, hu4, map_one]
  have hR4' : ι R ^ 2 ^ 2 = 1 := by rw [← map_pow, show 2 ^ 2 = 4 from rfl, hR4, map_one]
  have hRu' : ι R * ι u * (ι R)⁻¹ = (ι u)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hRu, map_inv]
  obtain ⟨x₁, hx₁⟩ := exists_conj_mem_sylow (isPGroup_zpowers hδ4') P
  have hxδ : x₁ * ι δ * x₁⁻¹ ∈ (P : Subgroup D) := hx₁ _ (Subgroup.mem_zpowers _)
  have hnorm : Subgroup.zpowers (ι R) ≤
      Subgroup.normalizer (Subgroup.zpowers (ι u) : Set D) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow, hRu']
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow
    (IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers hR4') (isPGroup_zpowers hu4') hnorm) P
  have hxu : x * ι u * x⁻¹ ∈ (P : Subgroup D) :=
    hx _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hxR : x * ι R * x⁻¹ ∈ (P : Subgroup D) :=
    hx _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hcN : ∀ z : ↥(Subgroup.center ↥(P : Subgroup D)), ((z : ↥(P : Subgroup D)) : D) ∈ N := by
    intro z
    by_contra hz
    refine step1 (x₁⁻¹ * ((z : ↥(P : Subgroup D)) : D) * x₁) (fun hmem => hz ?_)
      (conj_commute_of_mem_center z hxδ)
    have := hN.conj_mem _ hmem x₁
    simpa [mul_assoc] using this
  have hconjN : ∀ z : ↥(Subgroup.center ↥(P : Subgroup D)),
      x⁻¹ * ((z : ↥(P : Subgroup D)) : D) * x ∈ N := by
    intro z
    have := hN.conj_mem _ (hcN z) x⁻¹
    simpa using this
  let c₁ : ↥(Subgroup.center ↥(P : Subgroup D)) →* D :=
    (MulAut.conj x⁻¹).toMonoidHom.comp ((P : Subgroup D).subtype.comp (Subgroup.center _).subtype)
  have hc₁ : ∀ z, c₁ z = x⁻¹ * ((z : ↥(P : Subgroup D)) : D) * x := fun z => by
    simp [c₁]
  let c₂ : ↥(Subgroup.center ↥(P : Subgroup D)) →* ↥N :=
    c₁.codRestrict N (fun z => (hc₁ z) ▸ hconjN z)
  let E : ↥(Subgroup.center ↥(P : Subgroup D)) →* ↥H ⧸ Z₀.subgroupOf H := e.toMonoidHom.comp c₂
  have hEinj : Function.Injective E := by
    intro a b hab
    have h1 : c₂ a = c₂ b := e.injective hab
    have h1' : c₁ a = c₁ b := congrArg Subtype.val h1
    rw [hc₁, hc₁] at h1'
    exact Subtype.ext (Subtype.ext (by simpa using h1'))
  have hE : ∀ z, IsDiagAAB (E z) := by
    intro z A hA
    refine step2 (c₂ z) ?_ ?_ A hA.symm
    · change c₁ z * ι u = ι u * c₁ z
      rw [hc₁]
      exact conj_commute_of_mem_center z hxu
    · change c₁ z * ι R = ι R * c₁ z
      rw [hc₁]
      exact conj_commute_of_mem_center z hxR
  let f : ↥(Subgroup.center ↥(P : Subgroup D)) →* K :=
    { toFun := fun z => ratio (E z)
      map_one' := by
        simp only [map_one]
        exact ratio_one hZ hdet
      map_mul' := fun a b => by
        simp only [map_mul]
        exact ratio_mul hZ hdet (hE a) (hE b) }
  refine isCyclic_of_injective_ringHom f ((injective_iff_map_eq_one f).mpr fun z hz => ?_)
  have h3 : E z ^ 3 = 1 := pow_three_eq_one_of_ratio hZ hdet (hE z) hz
  have hz3 : z ^ 3 = 1 := hEinj (by rw [map_pow, h3, map_one])
  exact eq_one_of_pow_three (P.isPGroup'.to_subgroup _) hz3

section Models

open CFSG.Assembly.LowTwoRank

theorem exists_diagonal_mem_statedSL {a b d : K} (h : a * b * d = 1) :
    ∃ A ∈ StatedSL 3 K, (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, b, d] := by
  have hd : (diagonal ![a, b, d]).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simpa using h
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by rw [hd]; exact one_ne_zero),
    mem_statedSL_of_det (by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hd]),
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩

theorem exists_diagonal_mem_statedSU [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ 2) {a b d : K} (h : a * b * d = 1) (ha : a ^ p * a = 1)
    (hb : b ^ p * b = 1) (hd : d ^ p * d = 1) :
    ∃ A ∈ StatedSU 3 p K, (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, b, d] := by
  have hdet : (diagonal ![a, b, d]).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simpa using h
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by rw [hdet]; exact one_ne_zero),
    (mem_statedSU_iff hK _).mpr ⟨by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hdet], ?_⟩,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, CFSG.LieType.Universal.Unitary.conjTr,
    Matrix.diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext j
  fin_cases j <;> simp [frobenius_def, ha, hb, hd]

theorem pow_mul_self_eq_one {p : ℕ} (hp : p % 4 = 3) {x : K} (hx : x ^ 4 = 1) :
    x ^ p * x = 1 := by
  obtain ⟨k, hk⟩ : 4 ∣ p + 1 := by omega
  rw [← pow_succ, hk, pow_mul, hx, one_pow]

theorem smul_one_of_mem_statedScalars :
    ∀ s ∈ StatedScalars (Fin 3) K, ∃ c : K, (s : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  rintro s ⟨r, rfl⟩
  exact ⟨r, by rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]⟩

theorem smul_one_of_mem_bot :
    ∀ s ∈ (⊥ : Subgroup (GL (Fin 3) K)), ∃ c : K, (s : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  intro s hs
  exact ⟨1, by rw [Subgroup.mem_bot.mp hs]; simp⟩

end Models

end SylowCenterSLEps3

open SylowCenterSLEps3 CFSG.Assembly.LowTwoRank F618Comp in
theorem sylowCenterCyclicSLEps3_holds : SylowCenterCyclicSLEps3 := by
  intro D _ _ p hp8 hD P
  obtain ⟨hp, K, _, _, h⟩ := hD
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases hp8 with h | h <;> omega
  have := Fintype.ofFinite K
  rcases h with ⟨hp4, hK, h⟩ | ⟨hp4, hK, h⟩
  · have : CharP K p := charP_of_card (f := 1) (by rw [pow_one]; exact hK)
    have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp hp2
    obtain ⟨i, hi⟩ : ∃ i : K, i ^ 2 = -1 := by
      obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).mpr
        (by rw [← Nat.card_eq_fintype_card, hK]; omega)
      exact ⟨r, by rw [sq, ← hr]⟩
    have hdet : ∀ A ∈ StatedSL 3 K, (A : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      fun _ hA => det_eq_one_of_mem_statedSL hA
    have hδ := exists_diagonal_mem_statedSL (a := i) (b := i) (d := -1)
      (by linear_combination -hi)
    have hu := exists_diagonal_mem_statedSL (a := i) (b := -i) (d := 1)
      (by linear_combination -hi)
    rcases h with h | h
    · exact isCyclic_center_sylow hi h2 smul_one_of_mem_bot hdet hδ hu rotGL_mem_statedSL h P
    · exact isCyclic_center_sylow hi h2 smul_one_of_mem_statedScalars hdet hδ hu
        rotGL_mem_statedSL h P
  · have : CharP K p := charP_of_card hK
    have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp hp2
    obtain ⟨i, hi⟩ : ∃ i : K, i ^ 2 = -1 := by
      obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).mpr
        (by rw [← Nat.card_eq_fintype_card, hK, Nat.pow_mod, hp4]; norm_num)
      exact ⟨r, by rw [sq, ← hr]⟩
    have hi4 : i ^ 4 = 1 := by linear_combination (i ^ 2 - 1) * hi
    have hni4 : (-i) ^ 4 = 1 := by linear_combination (i ^ 2 - 1) * hi
    have hdet : ∀ A ∈ StatedSU 3 p K, (A : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      fun A hA => ((mem_statedSU_iff hK A).mp hA).1
    have hδ := exists_diagonal_mem_statedSU hK (a := i) (b := i) (d := -1)
      (by linear_combination -hi) (pow_mul_self_eq_one hp4 hi4) (pow_mul_self_eq_one hp4 hi4)
      (pow_mul_self_eq_one hp4 (by norm_num))
    have hu := exists_diagonal_mem_statedSU hK (a := i) (b := -i) (d := 1)
      (by linear_combination -hi) (pow_mul_self_eq_one hp4 hi4) (pow_mul_self_eq_one hp4 hni4)
      (pow_mul_self_eq_one hp4 (by norm_num))
    rcases h with h | h
    · exact isCyclic_center_sylow hi h2 smul_one_of_mem_bot hdet hδ hu (rotGL_mem_statedSU hK) h P
    · exact isCyclic_center_sylow hi h2 smul_one_of_mem_statedScalars hdet hδ hu
        (rotGL_mem_statedSU hK) h P

end CFSG.Quasithin.EmptyFaithfulMultiple
