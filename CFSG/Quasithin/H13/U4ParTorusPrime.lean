module

public import CFSG.Quasithin.H13.U4ParTorus
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.Quasithin (perfectCore)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem exists_bar_mul_eq_one_orderOf_eq {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1) :
    ∃ a : K, h.bar a * a = 1 ∧ orderOf a = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  have hfac : 2 ^ (2 * m) - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
    have h := Nat.sq_sub_sq (2 ^ m) 1
    rw [one_pow] at h
    rw [show 2 ^ (2 * m) = (2 ^ m) ^ 2 by rw [pow_mul'], h, mul_comm]
  have hcardu : Nat.card Kˣ = 2 ^ (2 * m) - 1 := by
    rw [Nat.card_units, h.card]
  have hpcard : p ∣ Nat.card Kˣ := by
    rw [hcardu, hfac]
    exact dvd_mul_of_dvd_right hpq _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpcard
  refine ⟨(u : K), ?_, ?_⟩
  · have huord : orderOf (u : K) = p := by rw [orderOf_units, hu]
    have hupow : (u : K) ^ (2 ^ m + 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, huord]
      exact hpq
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    exact hupow
  · rw [orderOf_units]
    exact hu

private theorem coe_torElt_pow {a : K} (ha : h.bar a * a = 1) (n : ℕ) :
    (((torElt h ha ^ n : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = torMat (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torMat_one]; rfl
  | succ n ih =>
      rw [pow_succ, coe_mul_hypSU, ih, coe_torElt, torMat_mul, ← pow_succ]

theorem orderOf_torElt {a : K} (ha : h.bar a * a = 1) : orderOf (torElt h ha) = orderOf a := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro hn
    have hm := congrArg (fun g : hypSU h 2 0 =>
      (((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1)) hn
    rw [coe_torElt_pow h ha n] at hm
    simpa [torMat, torDiag, ie1] using hm
  · intro hn
    apply hypSU_ext h
    rw [coe_torElt_pow h ha n, hn, torMat_one]
    rfl

theorem torElt_mem_hypBorel {a : K} (ha : h.bar a * a = 1) : torElt h ha ∈ hypBorel h 2 0 := by
  refine mem_hypBorel_of_blockTriangular h ?_
  rw [coe_torElt]
  exact Matrix.blockTriangular_diagonal (torDiag a)

private theorem prime_ne_two_of_dvd_pow_two_add_one (h : UnitaryFieldData 2 m K) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1) : p ≠ 2 := by
  rintro rfl
  have hm1 : 0 < m := h.one_le
  have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 (Nat.ne_of_gt hm1)
  have h2 : 2 ∣ 2 ^ m + 1 := hpq
  exact Nat.Prime.not_dvd_one Nat.prime_two ((Nat.dvd_add_iff_right h2m).mpr h2)

private theorem mem_zpowers_of_pow_eq_one (h : UnitaryFieldData 2 m K) {p : ℕ} (hp : p.Prime)
    {a x : Kˣ} (ha : orderOf a = p) (hx : x ^ p = 1) : x ∈ Subgroup.zpowers a := by
  classical
  haveI : Finite K := h.finite
  haveI : IsCyclic Kˣ := inferInstance
  rcases eq_or_ne x 1 with rfl | hx1
  · exact Subgroup.one_mem _
  · have hxord : orderOf x = p := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_iff_pow_eq_one.mpr hx) with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact hp'
    have heq : Subgroup.zpowers x = Subgroup.zpowers a :=
      (IsCyclic.subgroup_eq_iff_card_eq).mpr
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hxord, ha])
    rw [← heq]
    exact Subgroup.mem_zpowers x

private theorem bar_eq_inv_of_pow_eq_one {p : ℕ} (hpq : p ∣ 2 ^ m + 1) {x : Kˣ}
    (hx : x ^ p = 1) : h.bar (x : K) = (x : K)⁻¹ := by
  have hxK : (x : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  obtain ⟨k, hk⟩ := hpq
  have hq1 : (x : K) ^ (2 ^ m + 1) = 1 := by
    rw [hk, pow_mul, hxK, one_pow]
  have hsplit : (x : K) ^ (2 ^ m) * (x : K) = 1 := by
    rw [← pow_succ]
    exact hq1
  rw [UnitaryFieldData.bar_apply]
  exact eq_inv_of_mul_eq_one_left hsplit

private theorem coe_hypDiagHom_torElt_pow {a : K} (ha : h.bar a * a = 1) (k : ℕ) (i : Fin 2) :
    ((hypDiagHom h 2 0 (by norm_num)
      ⟨torElt h ha ^ k, (hypBorel h 2 0).pow_mem (torElt_mem_hypBorel h ha) k⟩) i : K) =
      if i = 0 then a ^ k else (a ^ k)⁻¹ := by
  rw [coe_hypDiagHom, coe_torElt_pow]
  rw [torMat, Matrix.diagonal_apply_eq, torDiag]
  fin_cases i <;> simp [ie1, ie2, if1]

private theorem hypDiagHom_prod_eq_one {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1)
    {b : hypSU h 2 0} (hb : b ∈ hypBorel h 2 0) (hbpow : b ^ p = 1) :
    (hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩) 0 *
      (hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩) 1 = 1 := by
  classical
  haveI : Finite K := h.finite
  haveI : IsCyclic Kˣ := inferInstance
  let c : Fin 2 → Kˣ := hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩
  have hbp : (⟨b, hb⟩ : hypBorel h 2 0) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hbpow]
  have hcpow : ∀ i : Fin 2, c i ^ p = 1 := by
    intro i
    have h : (hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩) ^ p = 1 := by
      rw [← map_pow, hbp, map_one]
    have := congrFun h i
    simpa [c, Pi.pow_apply] using this
  have hceven : c ∈ evenDiagGroup h 2 := by
    rw [← range_hypDiagHom_even]
    exact ⟨⟨b, hb⟩, rfl⟩
  have hrat : (c 0 : K) / h.bar (c 0) * ((c 1 : K) / h.bar (c 1)) = 1 := by
    have h := (mem_evenDiagGroup (h := h) (r := 2)).mp hceven
    rwa [Fin.prod_univ_two] at h
  have hbar0 := bar_eq_inv_of_pow_eq_one h hpq (hcpow 0)
  have hbar1 := bar_eq_inv_of_pow_eq_one h hpq (hcpow 1)
  have hsq : ((c 0 : K) * (c 1 : K)) ^ 2 = 1 := by
    rw [hbar0, hbar1, div_inv_eq_mul, div_inv_eq_mul] at hrat
    calc ((c 0 : K) * (c 1 : K)) ^ 2
        = (c 0 : K) * (c 0 : K) * ((c 1 : K) * (c 1 : K)) := by ring
      _ = 1 := hrat
  have hprod_pow : (c 0 * c 1) ^ p = 1 := by
    rw [mul_pow, hcpow 0, hcpow 1, one_mul]
  have hprod_sq : (c 0 * c 1) ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mul]
    exact hsq
  have h2 : orderOf (c 0 * c 1) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hprod_sq
  have hp' : orderOf (c 0 * c 1) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hprod_pow
  have hcop : Nat.Coprime 2 p :=
    Nat.coprime_two_left.mpr
      (Nat.Prime.odd_of_ne_two hp (prime_ne_two_of_dvd_pow_two_add_one h hp hpq))
  have hgcd : Nat.gcd 2 p = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
  have hdvd : orderOf (c 0 * c 1) ∣ Nat.gcd 2 p := Nat.dvd_gcd h2 hp'
  rw [hgcd] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

private theorem exists_hypDiagHom_eq_torElt_pow {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ m + 1) {a : K} (ha : h.bar a * a = 1) (hap : orderOf a = p)
    {b : hypSU h 2 0} (hb : b ∈ hypBorel h 2 0) (hbpow : b ^ p = 1) :
    ∃ k : ℕ, hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩ =
      hypDiagHom h 2 0 (by norm_num)
        ⟨torElt h ha ^ k, (hypBorel h 2 0).pow_mem (torElt_mem_hypBorel h ha) k⟩ := by
  classical
  haveI : Finite K := h.finite
  haveI : IsCyclic Kˣ := inferInstance
  let c : Fin 2 → Kˣ := hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩
  have hbp : (⟨b, hb⟩ : hypBorel h 2 0) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hbpow]
  have hcpow : ∀ i : Fin 2, c i ^ p = 1 := by
    intro i
    have h : (hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩) ^ p = 1 := by
      rw [← map_pow, hbp, map_one]
    have := congrFun h i
    simpa [c, Pi.pow_apply] using this
  have hprod_one := hypDiagHom_prod_eq_one h hp hpq hb hbpow
  have hc1 : c 1 = (c 0)⁻¹ := eq_inv_of_mul_eq_one_right hprod_one
  let au : Kˣ := Units.mk0 a (ne_zero_of_bar_mul h ha)
  have hau : (au : K) = a := Units.val_mk0 _
  have hauord : orderOf au = p := by
    rw [← orderOf_units, hau, hap]
  have hc0mem : c 0 ∈ Subgroup.zpowers au :=
    mem_zpowers_of_pow_eq_one h hp hauord (hcpow 0)
  rw [mem_zpowers_iff_mem_range_orderOf] at hc0mem
  obtain ⟨k, -, hck⟩ := Finset.mem_image.mp hc0mem
  have hc0k : (c 0 : K) = a ^ k := by
    rw [← hck, Units.val_pow_eq_pow_val, hau]
  refine ⟨k, ?_⟩
  apply funext
  rw [Fin.forall_fin_two]
  constructor
  · apply Units.ext
    rw [show ((hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩) 0 : K) = (c 0 : K) from rfl,
      coe_hypDiagHom_torElt_pow h ha k 0, if_pos rfl]
    exact hc0k
  · apply Units.ext
    rw [show ((hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩) 1 : K) = (c 1 : K) from rfl,
      coe_hypDiagHom_torElt_pow h ha k 1, if_neg (by decide)]
    rw [hc1, Units.val_inv_eq_inv_val, hc0k]

private theorem mul_inv_mem_hypUnitriangular_of_hypDiagHom_eq {b u : hypSU h 2 0}
    (hb : b ∈ hypBorel h 2 0) (hu : u ∈ hypBorel h 2 0)
    (hdiag : hypDiagHom h 2 0 (by norm_num) ⟨b, hb⟩ =
      hypDiagHom h 2 0 (by norm_num) ⟨u, hu⟩) :
    b * u⁻¹ ∈ hypUnitriangular h 2 0 := by
  let g : hypSU h 2 0 := b * u⁻¹
  have hgB : g ∈ hypBorel h 2 0 :=
    (hypBorel h 2 0).mul_mem hb ((hypBorel h 2 0).inv_mem hu)
  have hg_eq : (⟨g, hgB⟩ : hypBorel h 2 0) = ⟨b, hb⟩ * ⟨u, hu⟩⁻¹ := by
    apply Subtype.ext
    rfl
  have hgdiag : hypDiagHom h 2 0 (by norm_num) ⟨g, hgB⟩ = 1 := by
    rw [hg_eq, map_mul, map_inv, hdiag, mul_inv_cancel]
  have hker : (⟨g, hgB⟩ : hypBorel h 2 0) ∈ (hypDiagHom h 2 0 (by norm_num)).ker := by
    rw [MonoidHom.mem_ker]
    exact hgdiag
  rw [ker_hypDiagHom (by norm_num), Subgroup.mem_subgroupOf] at hker
  exact hker

private theorem mem_sup_zpowers_of_mem_hypBorel_of_pow {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ m + 1) {a : K} (ha : h.bar a * a = 1) (hap : orderOf a = p)
    {b : hypSU h 2 0} (hb : b ∈ hypBorel h 2 0) (hbpow : b ^ p = 1) :
    b ∈ hypUnitriangular h 2 0 ⊔ Subgroup.zpowers (torElt h ha) := by
  obtain ⟨k, hk⟩ := exists_hypDiagHom_eq_torElt_pow h hp hpq ha hap hb hbpow
  let t := torElt h ha
  have htB : t ∈ hypBorel h 2 0 := torElt_mem_hypBorel h ha
  have huB : t ^ k ∈ hypBorel h 2 0 := (hypBorel h 2 0).pow_mem htB k
  have hmemU : b * (t ^ k)⁻¹ ∈ hypUnitriangular h 2 0 :=
    mul_inv_mem_hypUnitriangular_of_hypDiagHom_eq h hb huB hk
  have hb_eq : b = (b * (t ^ k)⁻¹) * t ^ k := by group
  rw [hb_eq]
  exact Subgroup.mul_mem_sup hmemU
    (Subgroup.pow_mem (Subgroup.zpowers t) (Subgroup.mem_zpowers t) k)

theorem map_sup_zpowers_torElt {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1) {a : K}
    (ha : h.bar a * a = 1) (hap : orderOf a = p) {θ : MulAut (hypSU h 2 0)}
    (hθ : (hypUnitriangular h 2 0).map θ.toMonoidHom = hypUnitriangular h 2 0) :
    (hypUnitriangular h 2 0 ⊔ Subgroup.zpowers (torElt h ha)).map θ.toMonoidHom =
      hypUnitriangular h 2 0 ⊔ Subgroup.zpowers (torElt h ha) := by
  haveI : Finite (hypSU h 2 0) := finite_hypSU h
  have hN : Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) =
      hypBorel h 2 0 :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular h
      (by norm_num) (by norm_num)
  have hBmap : (hypBorel h 2 0).map θ.toMonoidHom = hypBorel h 2 0 := by
    rw [← hN, Subgroup.map_equiv_normalizer_eq (hypUnitriangular h 2 0) θ, hθ, hN]
  have hbpow : (θ (torElt h ha)) ^ p = 1 := by
    have hbord : orderOf (θ (torElt h ha)) = p := by
      rw [MulEquiv.orderOf_eq, orderOf_torElt h ha, hap]
    rw [← orderOf_dvd_iff_pow_eq_one, hbord]
  have hbB : θ (torElt h ha) ∈ hypBorel h 2 0 := by
    rw [← hBmap]
    exact Subgroup.mem_map_of_mem θ.toMonoidHom (torElt_mem_hypBorel h ha)
  have hmem : θ (torElt h ha) ∈
      hypUnitriangular h 2 0 ⊔ Subgroup.zpowers (torElt h ha) :=
    mem_sup_zpowers_of_mem_hypBorel_of_pow h hp hpq ha hap hbB hbpow
  have hle : (hypUnitriangular h 2 0 ⊔ Subgroup.zpowers (torElt h ha)).map
      θ.toMonoidHom ≤ hypUnitriangular h 2 0 ⊔ Subgroup.zpowers (torElt h ha) := by
    rw [Subgroup.map_sup, hθ, MonoidHom.map_zpowers]
    exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hmem)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective θ.injective]

private theorem levHom_injective (h : UnitaryFieldData 2 m K) :
    Function.Injective (levHom h) := by
  intro A B hAB
  have hm : slMat h A = slMat h B := by
    have h' := congrArg (fun g : hypSU h 2 0 => (((g : GL Ix K) : Matrix Ix Ix K))) hAB
    simp only [coe_levHom] at h'
    ext i j
    fin_cases i <;> fin_cases j
    · have := congrFun (congrFun h' ie2) ie2
      simpa [levMat_apply, slMat, ie1, ie2, if1, if2] using this
    · have := congrFun (congrFun h' ie2) if2
      simpa [levMat_apply, slMat, ie1, ie2, if1, if2] using this
    · have := congrFun (congrFun h' if2) ie2
      simpa [levMat_apply, slMat, ie1, ie2, if1, if2] using this
    · have := congrFun (congrFun h' if2) if2
      simpa [levMat_apply, slMat, ie1, ie2, if1, if2] using this
  exact Subtype.ext (Matrix.map_injective h.fixedField.subtype_injective hm)

private theorem levHom_pow_apply_ie1 (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) (n : ℕ) :
    (((((levHom h A) ^ n : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)) ie1 ie1 = 1 := by
  rw [← map_pow, coe_levHom]
  simp [levMat_apply, ie1, ie2, if1, if2]

private theorem torElt_comm_levHom {a : K} (ha : h.bar a * a = 1)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    Commute (torElt h ha) (levHom h A) := by
  rw [Commute]
  apply hypSU_ext h
  rw [coe_mul_hypSU, coe_mul_hypSU, coe_torElt, coe_levHom]
  ext i j
  rw [torMat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [torDiag, levMat_apply, ie1, ie2, if1, if2] <;> ring

private theorem torElt_not_mem_zpowers_levHom {p : ℕ} (hp : p.Prime) {a : K}
    (ha : h.bar a * a = 1) (hap : orderOf a = p)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    torElt h ha ∉ Subgroup.zpowers (levHom h A) := by
  classical
  haveI : Finite (hypSU h 2 0) := finite_hypSU h
  intro hmem
  rw [mem_zpowers_iff_mem_range_orderOf] at hmem
  obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hmem
  have h1 : a = 1 := by
    have := levHom_pow_apply_ie1 h A n
    rw [hn] at this
    rw [coe_torElt, torMat, Matrix.diagonal_apply_eq, torDiag] at this
    simpa [ie1] using this
  rw [h1, orderOf_one] at hap
  exact hp.ne_one hap.symm

theorem exists_isElemAbelian_le_perfectCore_parP_sup (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ m + 1) {a : K} (ha : h.bar a * a = 1) (hap : orderOf a = p) :
    ∃ E : Subgroup (hypSU h 2 0),
      E ≤ perfectCore (parP h) ⊔ Subgroup.zpowers (torElt h ha) ∧
        IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) =
      Nat.card h.fixedField * (Nat.card h.fixedField ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := h.fixedField)
      (n := 2) (by norm_num)]
    simp
  have hqfac : Nat.card h.fixedField ^ 2 - 1 =
      (Nat.card h.fixedField - 1) * (Nat.card h.fixedField + 1) := by
    have h := Nat.sq_sub_sq (Nat.card h.fixedField) 1
    rw [one_pow] at h
    rw [h, mul_comm]
  have hpq' : p ∣ Nat.card h.fixedField + 1 := by
    rw [h.card_fixedField]
    exact hpq
  have hp_dvd : p ∣ Nat.card h.fixedField ^ 2 - 1 := by
    rw [hqfac]
    exact dvd_mul_of_dvd_right hpq' _
  have hp_card : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    rw [hcard]
    exact dvd_mul_of_dvd_right hp_dvd _
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
    (G := Matrix.SpecialLinearGroup (Fin 2) h.fixedField) p hp_card
  let s' : hypSU h 2 0 := levHom h s
  have hs'ord : orderOf s' = p := by
    dsimp [s']
    rw [orderOf_injective (levHom h) (levHom_injective h) s, hs]
  have hs'P : s' ∈ perfectCore (parP h) := by
    dsimp [s']
    exact levHom_range_le_perfectCore h hm ⟨s, rfl⟩
  have hXcard : Nat.card (Subgroup.zpowers s') = p := by
    rw [Nat.card_zpowers, hs'ord]
  have htord : orderOf (torElt h ha) = p := by
    rw [orderOf_torElt h ha, hap]
  have htnot : torElt h ha ∉ Subgroup.zpowers s' := by
    dsimp [s']
    exact torElt_not_mem_zpowers_levHom h hp ha hap s
  have hcomm : ∀ x ∈ Subgroup.zpowers s', x * torElt h ha = torElt h ha * x := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn]
    exact ((torElt_comm_levHom h ha s).symm.zpow_left n).eq
  obtain ⟨hEea, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hXcard htord htnot hcomm
  exact ⟨Subgroup.zpowers s' ⊔ Subgroup.zpowers (torElt h ha),
    sup_le ((show Subgroup.zpowers s' ≤ perfectCore (parP h) from
      Subgroup.zpowers_le.mpr hs'P).trans le_sup_left) le_sup_right, hEea, hEcard⟩

end CFSG.Quasithin.H13.U4Par
