module

public import CFSG.Walter.ReeOrder.WardLocal.Outer
public import CFSG.Walter.ReeOrder.WardLocal.Five

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct

section CubeExt

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem inv_pow_eq_pow [Finite G] (y : G) (i : ℕ) : (y ^ i)⁻¹ = y ^ (i * (orderOf y - 1)) := by
  have hpos : 0 < orderOf y := orderOf_pos y
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, show i + i * (orderOf y - 1) = i * orderOf y by
    rw [Nat.mul_sub, mul_one]; have := Nat.le_mul_of_pos_right i hpos; omega, pow_mul',
    pow_orderOf_eq_one, one_pow]

@[expose] noncomputable def cubeExt (Z : Subgroup G) (y : G) (hZy : ∀ c ∈ Z, c * y = y * c) :
    Subgroup G where
  carrier := {u | ∃ i : ℕ, ∃ c ∈ Z, u = y ^ i * c}
  mul_mem' := by
    rintro a b ⟨i, c, hc, rfl⟩ ⟨j, d, hd, rfl⟩
    refine ⟨i + j, c * d, Z.mul_mem hc hd, ?_⟩
    have : c * y ^ j = y ^ j * c := (Commute.pow_right (hZy c hc) j).eq
    calc y ^ i * c * (y ^ j * d) = y ^ i * (c * y ^ j) * d := by group
      _ = y ^ i * (y ^ j * c) * d := by rw [this]
      _ = y ^ (i + j) * (c * d) := by rw [pow_add]; group
  one_mem' := ⟨0, 1, Z.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨i, c, hc, rfl⟩
    refine ⟨i * (orderOf y - 1), c⁻¹, Z.inv_mem hc, ?_⟩
    have hcy : c⁻¹ * y ^ (i * (orderOf y - 1)) = y ^ (i * (orderOf y - 1)) * c⁻¹ :=
      (Commute.pow_right (Commute.inv_left (hZy c hc)) _).eq
    rw [mul_inv_rev, inv_pow_eq_pow, hcy]

theorem eq_one_of_cubeExt {Z : Subgroup G} {y : G} (hZy : ∀ c ∈ Z, c * y = y * c)
    (hZab : ∀ c ∈ Z, ∀ d ∈ Z, c * d = d * c) (hy3 : y ^ 3 ∈ Z) (hy1 : y ∉ Z) (hy2 : y ^ 2 ∉ Z)
    {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (hZsum : ∑ c ∈ Finset.univ.filter (· ∈ Z), χ c = Nat.card Z)
    (hval1 : ∀ c ∈ Z, χ (y * c) = χ y) (hval2 : ∀ c ∈ Z, χ (y ^ 2 * c) = χ y) : χ y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := cubeExt Z y hZy with hA
  have hyA : y ∈ A := ⟨1, 1, Z.one_mem, by simp⟩
  have hZA : Z ≤ A := fun c hc => ⟨0, c, hc, by simp⟩
  have hpowA : ∀ (i : ℕ) (c : Z), y ^ i * (c : G) ∈ A := fun i c => ⟨i, c, c.2, rfl⟩
  let φ : Fin 3 × Z → A := fun p => ⟨y ^ (p.1 : ℕ) * p.2, hpowA _ _⟩
  have hkey' : ∀ i j : ℕ, i < 3 → j < 3 → y ^ i * (y ^ j)⁻¹ ∈ Z → i = j := by
    intro i j hi hj h
    have hy1' : y⁻¹ ∉ Z := fun h' => hy1 (by simpa using Z.inv_mem h')
    have hy2' : (y ^ 2)⁻¹ ∉ Z := fun h' => hy2 (by simpa using Z.inv_mem h')
    interval_cases i <;> interval_cases j
    · rfl
    · rw [show y ^ 0 * (y ^ 1)⁻¹ = y⁻¹ by group] at h; exact absurd h hy1'
    · rw [show y ^ 0 * (y ^ 2)⁻¹ = (y ^ 2)⁻¹ by group] at h; exact absurd h hy2'
    · rw [show y ^ 1 * (y ^ 0)⁻¹ = y by group] at h; exact absurd h hy1
    · rfl
    · rw [show y ^ 1 * (y ^ 2)⁻¹ = y⁻¹ by group] at h; exact absurd h hy1'
    · rw [show y ^ 2 * (y ^ 0)⁻¹ = y ^ 2 by group] at h; exact absurd h hy2
    · rw [show y ^ 2 * (y ^ 1)⁻¹ = y by group] at h; exact absurd h hy1
    · rfl
  have hkey : ∀ i j : Fin 3, y ^ (i : ℕ) * (y ^ (j : ℕ))⁻¹ ∈ Z → i = j := fun i j h =>
    Fin.ext (hkey' i j i.2 j.2 h)
  have hinj : Function.Injective φ := by
    rintro ⟨i, c⟩ ⟨j, d⟩ h
    have h' : y ^ (i : ℕ) * (c : G) = y ^ (j : ℕ) * d := congrArg Subtype.val h
    have hij : i = j := by
      apply hkey
      have : y ^ (i : ℕ) * (y ^ (j : ℕ))⁻¹ = (d : G) * (c : G)⁻¹ := by
        have e := congrArg (fun t => t * (c : G)⁻¹ * (y ^ (j : ℕ))⁻¹) h'
        simp only [mul_inv_cancel_right] at e
        rw [e]
        have hdy : (d : G) * y ^ (j : ℕ) = y ^ (j : ℕ) * d := (Commute.pow_right (hZy d d.2) _).eq
        have hcy : (c : G)⁻¹ * (y ^ (j : ℕ))⁻¹ = (y ^ (j : ℕ))⁻¹ * (c : G)⁻¹ :=
          (Commute.inv_inv (Commute.pow_right (hZy c c.2) _)).eq
        calc y ^ (j : ℕ) * d * (c : G)⁻¹ * (y ^ (j : ℕ))⁻¹
            = y ^ (j : ℕ) * d * ((c : G)⁻¹ * (y ^ (j : ℕ))⁻¹) := by group
          _ = y ^ (j : ℕ) * d * ((y ^ (j : ℕ))⁻¹ * (c : G)⁻¹) := by rw [hcy]
          _ = y ^ (j : ℕ) * (d * (y ^ (j : ℕ))⁻¹) * (c : G)⁻¹ := by group
          _ = (d : G) * (c : G)⁻¹ := by
              rw [show (d : G) * (y ^ (j : ℕ))⁻¹ = (y ^ (j : ℕ))⁻¹ * d from
                (Commute.inv_right (Commute.pow_right (hZy d d.2) _)).eq]
              group
      rw [this]; exact Z.mul_mem d.2 (Z.inv_mem c.2)
    subst hij
    have hcd : (c : G) = d := mul_left_cancel h'
    rw [Subtype.ext hcd]
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, i, c, hc, rfl⟩
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨(y ^ 3) ^ (i / 3) * c,
      Z.mul_mem (Z.pow_mem hy3 _) hc⟩), Subtype.ext ?_⟩
    show y ^ (i % 3) * ((y ^ 3) ^ (i / 3) * c) = y ^ i * c
    rw [← mul_assoc, ← pow_mul, ← pow_add, show i % 3 + 3 * (i / 3) = i from Nat.mod_add_div i 3]
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  have hcardA : Nat.card A = 3 * Nat.card Z := by
    rw [← Nat.card_congr (Equiv.ofBijective φ hbij), Nat.card_prod, Nat.card_fin]
  have hsumA : ∀ F : A → ℂ, ∑ u : A, F u =
      ∑ c : Z, F (φ (0, c)) + ∑ c : Z, F (φ (1, c)) + ∑ c : Z, F (φ (2, c)) := by
    intro F
    rw [← Function.Bijective.sum_comp hbij F, Fintype.sum_prod_type, Fin.sum_univ_three]
  set Z' := Z.subgroupOf A with hZ'
  have hZ'n : Z'.Normal := ⟨fun z hz a => by
    show ((a * z * a⁻¹ : A) : G) ∈ Z
    obtain ⟨i, c, hc, hac⟩ := a.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hz' : (z : G) ∈ Z := hz
    have hcom : (a : G) * z = z * a := by
      rw [hac]
      have h1 : (z : G) * y ^ i = y ^ i * z := (Commute.pow_right (hZy z hz') i).eq
      calc y ^ i * c * (z : G) = y ^ i * (c * z) := by group
        _ = y ^ i * (z * c) := by rw [hZab c hc z hz']
        _ = (y ^ i * z) * c := by group
        _ = (z * y ^ i) * c := by rw [h1]
        _ = (z : G) * (y ^ i * c) := by group
    rw [hcom]; simpa using hz'⟩
  have hcardQ : Nat.card (A ⧸ Z') = 3 := by
    have h := Z'.card_eq_card_quotient_mul_card_subgroup
    rw [hcardA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv] at h
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have : 3 * Nat.card Z = Nat.card (A ⧸ Z') * Nat.card Z := h
    exact (Nat.eq_of_mul_eq_mul_right hpos this).symm
  set ybar : A ⧸ Z' := QuotientGroup.mk ⟨y, hyA⟩ with hybar
  have hybar1 : ybar ≠ 1 := by
    intro h
    have := (QuotientGroup.eq_one_iff (N := Z') (⟨y, hyA⟩ : A)).mp h
    exact hy1 this
  have hgen : ∀ x : A ⧸ Z', x ∈ Subgroup.zpowers ybar := by
    intro x; rw [zpowers_eq_top_of_prime_card hcardQ hybar1]; exact Subgroup.mem_top x
  have hordy : orderOf ybar = 3 := by
    apply orderOf_eq_prime _ hybar1
    rw [← hcardQ]; exact pow_card_eq_one'
  have hω := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) with hωdef
  set ωu : ℂˣ := (hω.isUnit (by norm_num)).unit with hωu
  have hωu' : (ωu : ℂ) = ω := IsUnit.unit_spec _
  have hωdvd : orderOf ωu ∣ orderOf ybar := by
    rw [hordy]
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hωu', hω.pow_eq_one, Units.val_one]
  let νbar : A ⧸ Z' →* ℂˣ := monoidHomOfForallMemZpowers hgen hωdvd
  let ν : A →* ℂ := (Units.coeHom ℂ).comp (νbar.comp (QuotientGroup.mk' Z'))
  have hνZ : ∀ c : Z, ν ⟨c, hZA c.2⟩ = 1 := by
    intro c
    simp only [ν, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff (N := Z') (⟨c, hZA c.2⟩ : A)).mpr c.2, map_one, map_one]
  have hνy : ν ⟨y, hyA⟩ = ω := by
    simp only [ν, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [← hybar, monoidHomOfForallMemZpowers_apply_gen, Units.coeHom_apply, hωu']
  have hφ : ∀ (i : Fin 3) (c : Z), φ (i, c) = ⟨y, hyA⟩ ^ (i : ℕ) * ⟨c, hZA c.2⟩ := by
    intro i c; apply Subtype.ext; simp [φ]
  have hνφ : ∀ (i : Fin 3) (c : Z), ν (φ (i, c)) = ω ^ (i : ℕ) := by
    intro i c; rw [hφ, map_mul, map_pow, hνy, hνZ, mul_one]
  have hsum0 : ∑ c : Z, χ (φ (0, c)) = Nat.card Z := by
    rw [← hZsum]
    have : ∀ c : Z, χ ((φ (0, c) : A) : G) = χ c := fun c => by simp [φ]
    rw [Finset.sum_congr rfl fun c _ => this c]
    exact (Finset.sum_subtype (Finset.univ.filter (· ∈ Z)) (by simp) χ).symm
  have hsum1 : ∑ c : Z, χ (φ (1, c)) = Nat.card Z * χ y := by
    rw [Finset.sum_congr rfl fun c _ => show χ (φ (1, c)) = χ y by simpa [φ] using hval1 c c.2,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hsum2 : ∑ c : Z, χ (φ (2, c)) = Nat.card Z * χ y := by
    rw [Finset.sum_congr rfl fun c _ => show χ (φ (2, c)) = χ y by simpa [φ] using hval2 c c.2,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hZ0 : (Nat.card Z : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨n₀, hn₀⟩ := exists_natCast_restrict A.subtype hχ (one_mem_blocksIrr A)
  have h0 : (n₀ : ℂ) = (1 + 2 * χ y) / 3 := by
    rw [← hn₀, BlocksInnerProduct, hcardA]
    simp only [Function.comp_apply, Pi.one_apply, map_one, mul_one]
    rw [hsumA (fun u => χ (A.subtype u))]
    simp only [Subgroup.coe_subtype]
    have e0 : ∑ c : Z, χ ((φ (0, c) : A) : G) = Nat.card Z := hsum0
    have e1 : ∑ c : Z, χ ((φ (1, c) : A) : G) = Nat.card Z * χ y := hsum1
    have e2 : ∑ c : Z, χ ((φ (2, c) : A) : G) = Nat.card Z * χ y := hsum2
    rw [e0, e1, e2]
    push_cast
    field_simp
    ring
  obtain ⟨n₁, hn₁⟩ := exists_natCast_restrict A.subtype hχ
    (CFSG.Wreathed.CentralSL2.monoidHom_mem_blocksIrr ν)
  have hωsum : 1 + ω + ω ^ 2 = 0 := by
    have := hω.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ] using this
  have h1 : (n₁ : ℂ) = (1 - χ y) / 3 := by
    rw [← hn₁, BlocksInnerProduct, hcardA]
    simp only [Function.comp_apply]
    rw [hsumA (fun u => χ (A.subtype u) * starRingEnd ℂ (ν u))]
    simp only [Subgroup.coe_subtype, hνφ]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    have e0 : ∑ c : Z, χ ((φ (0, c) : A) : G) = Nat.card Z := hsum0
    have e1 : ∑ c : Z, χ ((φ (1, c) : A) : G) = Nat.card Z * χ y := hsum1
    have e2 : ∑ c : Z, χ ((φ (2, c) : A) : G) = Nat.card Z * χ y := hsum2
    rw [e0, e1, e2]
    have hc : starRingEnd ℂ ω + starRingEnd ℂ ω ^ 2 = -1 := by
      have := congrArg (starRingEnd ℂ) hωsum
      simp only [map_add, map_one, map_pow, map_zero] at this
      linear_combination this
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, map_one, mul_one, pow_one,
      map_pow]
    push_cast
    field_simp
    linear_combination χ y * hc
  have hsum : (n₀ : ℂ) + 2 * n₁ = 1 := by rw [h0, h1]; ring
  have hsum' : n₀ + 2 * n₁ = 1 := by exact_mod_cast hsum
  have hn₁0 : n₁ = 0 := by omega
  rw [hn₁0, Nat.cast_zero] at h1
  linear_combination 3 * h1

end CubeExt

end CFSG.Walter.WardLocal

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

theorem irr_class {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (g x : G) : χ (g * x * g⁻¹) = χ x :=
  blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ) x g

namespace Block

include B hq hK hG hP1P hPc hPn in
theorem mem_AA_of_zcen {x : G} (hx : x ∈ zcen P) (hx1 : x ≠ 1) : x ∈ AA S := by
  have hZ := zcen_eq_CC hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG) hP1P hPc hPn
  rw [hZ] at hx
  exact mem_AA_of_mem_CC hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG) hx hx1

include B hq hK hG hP1P hPc hPn in
theorem zcen_val {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {X X' : G} (hX : X ∈ zcen P) (hX1 : X ≠ 1)
    (hX' : X' ∈ zcen P) (hX'1 : X' ≠ 1) : χ X' = χ X := by
  obtain ⟨w, -, hw⟩ := AA_transitive hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
    (B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hX hX1)
    (B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hX' hX'1)
  rw [← hw, irr_class hχ]

include B hq hK hG hP1P hPc hPn in
theorem sum_zcen {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {X : G} (hX : X ∈ zcen P) (hX1 : X ≠ 1) :
    ∑ c ∈ Finset.univ.filter (· ∈ zcen P), χ c = χ 1 + ((q : ℂ) - 1) * χ X := by
  have h1 : (1 : G) ∈ Finset.univ.filter (· ∈ zcen P) := by simp [(zcen P).one_mem]
  rw [← Finset.add_sum_erase _ _ h1]
  have hconst : ∀ c ∈ (Finset.univ.filter (· ∈ zcen P)).erase 1, χ c = χ X := by
    intro c hc
    rw [Finset.mem_erase, Finset.mem_filter] at hc
    exact B.zcen_val hq hK hG hP1P hPc hPn hχ hX hX1 hc.2.2 hc.1
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_erase_of_mem h1,
    card_filter_eq, B.card_zcen hq hK hG hP1P hPc hPn, nsmul_eq_mul]
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  push_cast [Nat.cast_sub hq1]
  ring

include B hq hK hG hP1P hPc hPn hN1c in
theorem xi2_outer {y : G} (hy : y ∈ P) (hyP1 : y ∉ PP1 S) : B.ξ₂ y = 1 ∧ B.ξ₄ y = 0 := by
  have hcT := B.hcT hq hK hG
  have hZP1 := B.zcen_le_PP1 hq hK hG hP1P hPc hPn
  have hy3 := B.cube_mem_zcen hq hK hG hP1P hPc hPn hN1c hy hyP1
  have hy1 : y ∉ zcen P := fun h => hyP1 (hZP1 h)
  have hy2 : y ^ 2 ∉ zcen P := by
    intro h
    apply hyP1
    have : y = y ^ 3 * (y ^ 2)⁻¹ := by group
    rw [this]; exact (PP1 S).mul_mem (hZP1 hy3) ((PP1 S).inv_mem (hZP1 h))
  have hZy : ∀ c ∈ zcen P, c * y = y * c := fun c hc => (mem_zcen.mp hc).2 y hy
  have hZab : ∀ c ∈ zcen P, ∀ d ∈ zcen P, c * d = d * c := fun c hc d hd =>
    (mem_zcen.mp hc).2 d (mem_zcen.mp hd).1
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  obtain ⟨X, hX, hX1⟩ : ∃ X ∈ zcen P, X ≠ 1 := by
    have h := B.card_zcen hq hK hG hP1P hPc hPn
    by_contra hall
    push Not at hall
    have : zcen P = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [this, Subgroup.card_bot] at h
    omega
  have hXA := B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hX hX1
  have hξX : B.ξ₂ X = 1 - q := by
    rw [B.xi2_PP1 hq hK hG (hZP1 hX) hX1]; simp [hXA]
  have hZsum : ∑ c ∈ Finset.univ.filter (· ∈ zcen P), B.ξ₂ c = Nat.card (zcen P) := by
    rw [B.sum_zcen hq hK hG hP1P hPc hPn B.irr_2 hX hX1, hξX, B.xi_one.1,
      B.card_zcen hq hK hG hP1P hPc hPn]
    ring
  have hval1 : ∀ c ∈ zcen P, B.ξ₂ (y * c) = B.ξ₂ y := fun c hc => by
    obtain ⟨a, -, ha⟩ := B.exists_conj_outer hq hK hG hP1P hPc hPn hy hyP1 hc
    rw [← ha, irr_class B.irr_2]
  have hyinv : y⁻¹ ∉ PP1 S := fun h => hyP1 (by simpa using (PP1 S).inv_mem h)
  have hval2 : ∀ c ∈ zcen P, B.ξ₂ (y ^ 2 * c) = B.ξ₂ y := fun c hc => by
    obtain ⟨a, -, ha⟩ := B.exists_conj_outer hq hK hG hP1P hPc hPn (P.inv_mem hy) hyinv
      ((zcen P).mul_mem hy3 hc)
    have e : y ^ 2 * c = y⁻¹ * (y ^ 3 * c) := by group
    rw [e, ← ha, irr_class B.irr_2, inv_eq_conj B.irr_2]
    exact congrFun B.real_2 y
  have h2 := eq_one_of_cubeExt hZy hZab hy3 hy1 hy2 B.irr_2 hZsum hval1 hval2
  refine ⟨h2, ?_⟩
  have hy1' : y ≠ 1 := fun h => hy1 (h ▸ (zcen P).one_mem)
  have h3 : 3 ∣ orderOf y := three_dvd_of_mem (isPGroup_P hq hPc) hy hy1'
  have hodd : Odd (orderOf y) := by
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  have h24 := (B.eta_eq_one hq hG hodd h3 S.i₀).2.2
  linear_combination h24 - h2

end Block

end CFSG.Walter.WardLocal
