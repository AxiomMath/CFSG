module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CD
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique SecA

section Matrix

variable {F : Type} [Field F]

theorem upperTri_pow {M : Matrix (Fin 2) (Fin 2) F} (h : M 1 0 = 0) (m : ℕ) :
    (M ^ m) 1 0 = 0 ∧ (M ^ m) 0 0 = M 0 0 ^ m ∧ (M ^ m) 1 1 = M 1 1 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h]
    refine ⟨by ring, by ring, by ring⟩

theorem pow_card_sub_one_eq_one [Fintype F] [CharP F 2] {g δ : Matrix.SpecialLinearGroup (Fin 2) F}
    (hc : ∃ c : F, (g * δ * g⁻¹) * unipSL 1 * (g * δ * g⁻¹)⁻¹ = unipSL c)
    (hodd : Odd (orderOf δ)) : δ ^ (Fintype.card F - 1) = 1 := by
  set δ' := g * δ * g⁻¹ with hδ'
  obtain ⟨c, hc⟩ := hc
  have hc' : δ' * unipSL 1 = unipSL c * δ' := by
    rw [← hc]
    group
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [unipSL_zero, one_mul] at hc'
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) (mul_left_cancel (a := δ') (hc'.trans (mul_one _).symm))
    simp [coe_unipSL] at h1
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) hc'
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    coe_unipSL] at h00
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.empty_val'] at h00
  have h10 : (δ' : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have : c * (δ' : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -h00
    exact (mul_eq_zero.mp this).resolve_left hc0
  have hdet := δ'.2
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  have ha : (δ' : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hd : (δ' : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  obtain ⟨p1, p2, p3⟩ := upperTri_pow h10 (Fintype.card F - 1)
  rw [FiniteField.pow_card_sub_one_eq_one _ ha] at p2
  rw [FiniteField.pow_card_sub_one_eq_one _ hd] at p3
  set x := ((δ' : Matrix (Fin 2) (Fin 2) F) ^ (Fintype.card F - 1)) 0 1 with hx
  have hu : δ' ^ (Fintype.card F - 1) = unipSL x := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow]
    fin_cases i <;> fin_cases j <;> simp [coe_unipSL, p1, p2, p3, hx]
  have hsq : (δ' ^ (Fintype.card F - 1)) ^ 2 = 1 := by
    rw [hu, pow_two]
    exact unipSL_mul_self x
  have hodd' : Odd (orderOf (δ' ^ (Fintype.card F - 1))) := by
    refine Odd.of_dvd_nat ?_ (orderOf_pow_dvd _)
    have : orderOf δ' = orderOf δ := by
      rw [hδ', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rwa [this]
  have h1 := eq_one_of_sq_of_odd hsq hodd'
  have h2 : δ ^ (Fintype.card F - 1) = g⁻¹ * δ' ^ (Fintype.card F - 1) * g := by
    rw [hδ', conj_pow]
    group
  rw [h2, h1, mul_one, inv_mul_cancel]

end Matrix

section Natural

variable {W : Type*} [CommGroup W]

theorem exists_fun_of_fix_sylow {K₀ : Subgroup (MulAut W)} {C : Subgroup W} {m : ℕ}
    (hnat : E2.IsL2Natural K₀ C m) {P : Subgroup (MulAut W)} (hP : IsSylowTwoOf P K₀) :
    ∃ (F : Type) (_ : Fintype F), Fintype.card F = 2 ^ m ∧ ∃ ψ : W → F,
      ∀ y ∈ commV K₀, ∀ y' ∈ commV K₀, (∀ p ∈ P, p y = y) → (∀ p ∈ P, p y' = y') →
        ψ y = ψ y' → y * y'⁻¹ ∈ C := by
  classical
  obtain ⟨-, F, _, _, hcard, e, β, -, hker, hβe⟩ := hnat
  have hF : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hcard]
  set P' := (P.subgroupOf K₀).map e.toMonoidHom with hP'
  have hP2 : IsPGroup 2 P' :=
    (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).map e.toMonoidHom
  have hPi : ¬ 2 ∣ P'.index := by
    rw [hP', Subgroup.index_map_eq _ e.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact bot_le)]
    exact hP.2.2
  obtain ⟨g, -, hg2⟩ := exists_conj_unip hF hP2 hPi
  refine ⟨F, inferInstance, hcard, fun y => if h : y ∈ commV K₀ then
    ((g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β ⟨y, h⟩))) 0 else 0, ?_⟩
  have key : ∀ y (h : y ∈ commV K₀), (∀ p ∈ P, p y = y) →
      ((g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β ⟨y, h⟩))) 1 = 0 := by
    intro y h hy
    obtain ⟨x, hxP, hxe⟩ := hg2 1
    have hxy : (x : MulAut W) y = y := hy _ hxP
    have hu : (x : MulAut W) y ∈ commV K₀ := by rw [hxy]; exact h
    have h1 := hβe x ⟨y, h⟩ hu
    have e1 : (⟨(x : MulAut W) y, hu⟩ : ↥(commV K₀)) = ⟨y, h⟩ := Subtype.ext hxy
    rw [e1] at h1
    set z := Multiplicative.toAdd (β ⟨y, h⟩) with hz
    have h2 := congrArg (fun w => (g : Matrix (Fin 2) (Fin 2) F).mulVec w) h1
    have hxe' : e x = g⁻¹ * unipSL 1 * g := hxe
    rw [mulVec_conj, hxe', show g * (g⁻¹ * unipSL 1 * g) * g⁻¹ = unipSL (1 : F) by group,
      coe_unipSL, unipSL_mulVec] at h2
    have h3 := congrFun h2 0
    simp only [Matrix.cons_val_zero, one_mul] at h3
    linear_combination -h3
  intro y hy y' hy' hfy hfy' hψ
  simp only [hy, hy', ↓reduceDIte] at hψ
  set z := Multiplicative.toAdd (β ⟨y, hy⟩) with hz
  set z' := Multiplicative.toAdd (β ⟨y', hy'⟩) with hz'
  have hgz : (g : Matrix (Fin 2) (Fin 2) F).mulVec z =
      (g : Matrix (Fin 2) (Fin 2) F).mulVec z' := by
    ext i
    fin_cases i
    · exact hψ
    · simp only [Fin.mk_one, Fin.isValue]
      rw [key y hy hfy, key y' hy' hfy']
  have hzz : z = z' := by
    have h1 := congrArg (fun w => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).mulVec w) hgz
    simpa only [Matrix.mulVec_mulVec, sl_inv_mul, Matrix.one_mulVec] using h1
  have hβ : β (⟨y, hy⟩ * (⟨y', hy'⟩ : ↥(commV K₀))⁻¹) = 1 := by
    rw [map_mul, map_inv, show β ⟨y, hy⟩ = β ⟨y', hy'⟩ from
      Multiplicative.toAdd.injective hzz, mul_inv_cancel]
  have hmem : (⟨y, hy⟩ * (⟨y', hy'⟩ : ↥(commV K₀))⁻¹) ∈ β.ker := hβ
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  exact hmem.2

end Natural

variable {G : Type*} [Group G]

theorem mul_mem_of_odd {L O : Subgroup G} (hO : IsPGroup 2 O)
    (hON : O ≤ Subgroup.normalizer (L : Set G)) {l o : G} (hl : l ∈ L) (ho : o ∈ O)
    (hodd : Odd (orderOf (l * o))) : l * o ∈ L := by
  have key : ∀ j : ℕ, ∃ l' ∈ L, (l * o) ^ j = l' * o ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨l', hl', he⟩ := ih
      have hc : o ^ j * l * (o ^ j)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hON (O.pow_mem ho j)) l).mp hl
      refine ⟨l' * (o ^ j * l * (o ^ j)⁻¹), L.mul_mem hl' hc, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨l', hl', he⟩ := key (orderOf (l * o))
  rw [pow_orderOf_eq_one] at he
  have hom : o ^ orderOf (l * o) ∈ L := by
    have : o ^ orderOf (l * o) = l'⁻¹ := eq_inv_of_mul_eq_one_right he.symm
    rw [this]
    exact L.inv_mem hl'
  obtain ⟨a, ha⟩ := hO ⟨o, ho⟩
  have ha' : o ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hcop : Nat.Coprime (orderOf (l * o)) (orderOf o) :=
    ((Nat.coprime_two_right.mpr hodd).pow_right a).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one ha')
  have hoL : o ∈ L := (Subgroup.zpowers_le.mpr hom) (A4.mem_zpowers_pow_of_coprime hcop)
  exact L.mul_mem hl hoL

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
