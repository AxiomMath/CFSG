module

public import CFSG.Sporadic.HN.Commutant
public import CFSG.Sporadic.Ly.CoprimeSimple

public section

namespace CFSG.Sporadic.Ly

open Matrix

noncomputable abbrev sA : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  Blueprint.NativeSporadic.decode 5 111 1 Blueprint.NativeSporadic.LySeed1

noncomputable abbrev sB : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  Blueprint.NativeSporadic.decode 5 111 1 Blueprint.NativeSporadic.LySeed2

noncomputable abbrev JS : Subgroup (GL (Fin 111) (ZMod 5)) :=
  Subgroup.closure {g | (g : Matrix (Fin 111) (Fin 111) (ZMod 5)) = sA ∨
    (g : Matrix (Fin 111) (Fin 111) (ZMod 5)) = sB}

noncomputable abbrev matS (g : JS) : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  ((g : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5))

theorem matS_injective : Function.Injective matS := fun _ _ e => Subtype.ext (Units.ext e)

theorem matS_mul (g h : JS) : matS (g * h) = matS g * matS h := rfl

theorem matS_one : matS 1 = 1 := rfl

theorem matS_pow (g : JS) (n : ℕ) : matS (g ^ n) = matS g ^ n := by
  simp [matS]

@[expose] noncomputable def aS (h : sA.det ≠ 0) : JS :=
  ⟨GeneralLinearGroup.mkOfDetNeZero sA h, Subgroup.subset_closure (Or.inl rfl)⟩

@[expose] noncomputable def bS (h : sB.det ≠ 0) : JS :=
  ⟨GeneralLinearGroup.mkOfDetNeZero sB h, Subgroup.subset_closure (Or.inr rfl)⟩

theorem matS_aS (h : sA.det ≠ 0) : matS (aS h) = sA := rfl

theorem matS_bS (h : sB.det ≠ 0) : matS (bS h) = sB := rfl

theorem closure_aS_bS (hA : sA.det ≠ 0) (hB : sB.det ≠ 0) :
    Subgroup.closure ({aS hA, bS hB} : Set JS) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    {g : GL (Fin 111) (ZMod 5) | (g : Matrix (Fin 111) (Fin 111) (ZMod 5)) = sA ∨
      (g : Matrix (Fin 111) (Fin 111) (ZMod 5)) = sB}
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype,
    Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (matS_injective h)
    · exact Or.inr (matS_injective h)

noncomputable abbrev detS : JS →* (ZMod 5)ˣ := (GeneralLinearGroup.det).comp JS.subtype

theorem detS_eq_one {hA : sA.det ≠ 0} {hB : sB.det ≠ 0} (hB5 : sB ^ 5 = 1) {g : JS} {n : ℕ}
    (hn : Nat.Coprime n 4) (hx : (aS hA * (g⁻¹ * bS hB * g)) ^ n = 1) (z : JS) : detS z = 1 := by
  have hb : detS (bS hB) = 1 := by
    refine CFSG.Sporadic.F5.units_five_eq_one (n := 5) (by norm_num) ?_
    rw [← map_pow]
    have : bS hB ^ 5 = 1 := by
      apply matS_injective
      rw [matS_pow, matS_bS, hB5, matS_one]
    rw [this, map_one]
  have hxd : detS (aS hA * (g⁻¹ * bS hB * g)) = 1 :=
    CFSG.Sporadic.F5.units_five_eq_one hn (by rw [← map_pow, hx, map_one])
  have ha : detS (aS hA) = 1 := by
    rw [map_mul, map_mul, map_mul, hb, map_inv, mul_one, inv_mul_cancel, mul_one] at hxd
    exact hxd
  have hker : (⊤ : Subgroup JS) ≤ detS.ker := by
    rw [← closure_aS_bS hA hB, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ha
    · exact hb
  exact hker (Subgroup.mem_top z)

theorem center_JS_eq_bot {hA : sA.det ≠ 0} {hB : sB.det ≠ 0} (hB5 : sB ^ 5 = 1) {g : JS}
    (hx : (aS hA * (g⁻¹ * bS hB * g)) ^ 67 = 1)
    (hcomm : ∀ M : Matrix (Fin 111) (Fin 111) (ZMod 5), M * sA = sA * M → M * sB = sB * M →
      ∃ c : ZMod 5, M = c • 1) :
    Subgroup.center JS = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hcA : matS z * sA = sA * matS z := by
    have h := congrArg matS (hz (aS hA))
    rw [matS_mul, matS_mul, matS_aS] at h
    exact h.symm
  have hcB : matS z * sB = sB * matS z := by
    have h := congrArg matS (hz (bS hB))
    rw [matS_mul, matS_mul, matS_bS] at h
    exact h.symm
  obtain ⟨c, hc⟩ := hcomm _ hcA hcB
  have hdet : (matS z).det = 1 := by
    have h := congrArg Units.val (detS_eq_one hB5 (by norm_num) hx z)
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GeneralLinearGroup.val_det_apply,
      Units.val_one] at h
    exact h
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hdet
    exact zero_ne_one hdet
  have hc4 : c ^ 4 = 1 := ZMod.pow_card_sub_one_eq_one hc0
  have hc3 : c ^ 3 = 1 := by
    have e : (111 : ℕ) = 4 * 27 + 3 := by norm_num
    rw [e, pow_add, pow_mul, hc4, one_pow, one_mul] at hdet
    exact hdet
  have hc1 : c = 1 := by
    have e : c ^ 4 = c ^ 3 * c := pow_succ c 3
    rw [hc4, hc3, one_mul] at e
    exact e.symm
  rw [hc1, one_smul] at hc
  exact matS_injective hc

theorem isSimpleGroup_JS {hA : sA.det ≠ 0} {hB : sB.det ≠ 0} (hA2 : sA ^ 2 = 1) (hB5 : sB ^ 5 = 1)
    {g : JS} (hx : orderOf (aS hA * (g⁻¹ * bS hB * g)) = 67)
    (hcomm : ∀ M : Matrix (Fin 111) (Fin 111) (ZMod 5), M * sA = sA * M → M * sB = sB * M →
      ∃ c : ZMod 5, M = c • 1)
    (hc : Nat.card JS = 51765179004000000) : IsSimpleGroup JS := by
  have : Finite JS := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have ha : aS hA ^ 2 = 1 := by
    apply matS_injective
    rw [matS_pow, matS_aS, hA2, matS_one]
  have hb : bS hB ^ 5 = 1 := by
    apply matS_injective
    rw [matS_pow, matS_bS, hB5, matS_one]
  have hx67 : (aS hA * (g⁻¹ * bS hB * g)) ^ 67 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  refine isSimpleGroup_of_conjProd_coprime (m := 2) (n := 5) (by norm_num) (by norm_num)
    (closure_aS_bS hA hB) ha hb hx ?_ (center_JS_eq_bot hB5 hx67 hcomm) ?_
  · rw [hc]
    norm_num
  · rw [hc]
    exact ly_GL_condition

end CFSG.Sporadic.Ly
