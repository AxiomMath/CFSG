module

public import CFSG.Quasithin.Background.H12OneHatM22PfModel
public import CFSG.Quasithin.Background.H12OneHatM22PfReal
public import CFSG.Quasithin.Background.SmithB45M22HatHat
public import CFSG.Quasithin.H13.L32NM22Model

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.HatM22

@[expose] def pC : List ℕ := [2565, 1518, 240, 2734, 1254, 3715, 3983, 3766, 4002, 466, 3131, 413]

@[expose] def pIC : List ℕ := [2133, 2929, 114, 2975, 2687, 760, 713, 2634, 2957, 3442, 360, 1364]

@[expose] def wP : List (List ℕ) :=
  [[1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0],
    [1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1,
      1, 1, 0, 1, 0, 0, 1, 0]]

@[expose] def zPC : List ℕ := [723, 3514, 1467, 1867, 883, 3911, 3663, 2261, 1571, 2130, 3935, 2772]

theorem link_facts : validB 12 pC = true ∧ validB 12 pIC = true ∧ validB 12 zPC = true ∧
    mulN pC pIC = oneN 12 ∧ mulN pIC pC = oneN 12 ∧
    (∀ i < 2, mulN pC (H12Cert.gG.getD i H12Cert.one12) =
      mulN (M22Cert.tW (wP.getD i [])) pC) ∧
    mulN pC H12Cert.z12 = mulN zPC pC ∧
    mulN (M22Cert.gG.getD 0 M22Cert.one12) (mulN zPC (M22Cert.gG.getD 0 M22Cert.one12)) =
      mulN zPC zPC ∧
    zPC ≠ oneN 12 := by
  decide +kernel

theorem validN_pC : ValidN 12 pC := validB_iff.mp link_facts.1

theorem validN_pIC : ValidN 12 pIC := validB_iff.mp link_facts.2.1

theorem validN_zPC : ValidN 12 zPC := validB_iff.mp link_facts.2.2.1

theorem mulN_pC_gG {i : ℕ} (hi : i < 2) : mulN pC (H12Cert.gG.getD i H12Cert.one12) =
    mulN (M22Cert.tW (wP.getD i [])) pC := link_facts.2.2.2.2.2.1 i hi

theorem mulN_pC_z12 : mulN pC H12Cert.z12 = mulN zPC pC := link_facts.2.2.2.2.2.2.1

theorem mulN_a_zPC :
    mulN (M22Cert.gG.getD 0 M22Cert.one12) (mulN zPC (M22Cert.gG.getD 0 M22Cert.one12)) =
      mulN zPC zPC := link_facts.2.2.2.2.2.2.2.1

theorem zPC_ne : zPC ≠ oneN 12 := link_facts.2.2.2.2.2.2.2.2

theorem decN_pC_mul : decN 12 pC * decN 12 pIC = 1 := by
  rw [← decN_mulN validN_pC.1 validN_pIC.1, link_facts.2.2.2.1, decN_oneN]

theorem decN_pIC_mul : decN 12 pIC * decN 12 pC = 1 := by
  rw [← decN_mulN validN_pIC.1 validN_pC.1, link_facts.2.2.2.2.1, decN_oneN]

@[expose] def conjP : GL (Fin 12) (ZMod 2) := ⟨decN 12 pC, decN 12 pIC, decN_pC_mul, decN_pIC_mul⟩

theorem conjP_val :
    ((conjP : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 pC := rfl

theorem conjP_inv_val :
    ((conjP⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 pIC := rfl

theorem conjP_mul_gU {i : ℕ} (hi : i < 2) :
    conjP * H12Cert.gU i = M22Cert.tU (wP.getD i []) * conjP := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [conjP_val, H12Cert.gU_val, M22Cert.tU_val,
    ← decN_mulN validN_pC.1 (H12Cert.length_gG i),
    ← decN_mulN (length_evalW _ _) validN_pC.1, mulN_pC_gG hi]

theorem conj_gU_eq {i : ℕ} (hi : i < 2) :
    conjP * H12Cert.gU i * conjP⁻¹ = M22Cert.tU (wP.getD i []) := by
  rw [conjP_mul_gU hi, mul_inv_cancel_right]

@[expose] def m22Zero : Subgroup (GL (Fin 12) (ZMod 2)) :=
  H12Cert.G.map (MulAut.conj conjP).toMonoidHom

theorem mem_m22Zero_iff {x : GL (Fin 12) (ZMod 2)} :
    x ∈ m22Zero ↔ conjP⁻¹ * x * conjP ∈ H12Cert.G := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_mem_m22Zero {y : GL (Fin 12) (ZMod 2)} (hy : y ∈ H12Cert.G) :
    conjP * y * conjP⁻¹ ∈ m22Zero :=
  ⟨y, hy, by simp [MulAut.conj_apply]⟩

theorem m22Zero_le_m22 : m22Zero ≤ L1442M.m22 := by
  rw [m22Zero, Subgroup.map_le_iff_le_comap]
  intro x hx
  refine H12Cert.G_induction
    (p := fun x => x ∈ L1442M.m22.comap (MulAut.conj conjP).toMonoidHom) (one_mem _) ?_ hx
  intro i hi y hy
  rw [Subgroup.mem_comap] at hy ⊢
  rw [map_mul]
  refine mul_mem ?_ hy
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_gU_eq hi]
  exact M22Cert.tU_mem _

theorem card_m22Zero : Nat.card m22Zero = 1330560 := by
  rw [m22Zero, Subgroup.card_map_of_injective (MulAut.conj conjP).injective, H12Cert.card_G]

@[expose] noncomputable def hatEquivG' : ↥hatM22Γ₀ ≃* ↥H12Cert.G :=
  (hatM22Γ₀.equivMapOfInjective H12Pf.realGL H12Pf.realGL_injective).trans
    (MulEquiv.subgroupCongr H12Pf.map_realGL_hatM22Γ₀)

@[expose] noncomputable def equivZero : ↥H12Cert.G ≃* ↥m22Zero :=
  H12Cert.G.equivMapOfInjective (MulAut.conj conjP).toMonoidHom (MulAut.conj conjP).injective

theorem isHat_of_mulEquiv' {A B S : Type} [Group A] [Group B] [Group S] (e : A ≃* B)
    (h : IsHat A S) : IsHat B S := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_,
    ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  rw [← hcen, Subgroup.card_map_of_injective e.injective, hc]

theorem isHat_m22Zero :
    IsHat ↥m22Zero ↥CFSG.Blueprint.NativeSporadic.M22 := by
  have hq : CFSG.Open.quasithinM22 = CFSG.Blueprint.NativeSporadic.M22 := rfl
  have h := isHat_hatM22Γ₀
  rw [hq] at h
  exact isHat_of_mulEquiv' (hatEquivG'.trans equivZero) h

theorem index_m22Zero :
    (m22Zero.subgroupOf L1442M.m22).index = 2 := by
  have h1 := Subgroup.card_mul_index (m22Zero.subgroupOf L1442M.m22)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m22Zero_le_m22).toEquiv, card_m22Zero,
    M22Cert.card_m22] at h1
  omega

theorem normal_m22Zero :
    (m22Zero.subgroupOf L1442M.m22).Normal :=
  Subgroup.normal_of_index_eq_two index_m22Zero

@[expose] def zP : GL (Fin 12) (ZMod 2) := conjP * H12Cert.zU * conjP⁻¹

theorem zP_val :
    ((zP : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 zPC := by
  have h : decN 12 pC * decN 12 H12Cert.z12 = decN 12 zPC * decN 12 pC := by
    rw [← decN_mulN validN_pC.1 H12Cert.z12_facts.1,
      ← decN_mulN validN_zPC.1 validN_pC.1, mulN_pC_z12]
  rw [zP, Units.val_mul, Units.val_mul, conjP_val, conjP_inv_val, H12Cert.zU_val, h,
    Matrix.mul_assoc, decN_pC_mul, Matrix.mul_one]

theorem zP_pow_three : zP ^ 3 = 1 := by
  rw [zP, ← MulAut.conj_apply, ← map_pow, H12Cert.zU_pow_three, map_one]

theorem zP_ne_one : zP ≠ 1 := by
  intro h
  apply zPC_ne
  have h1 := congrArg (fun u : GL (Fin 12) (ZMod 2) =>
    colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) h
  simp only [zP_val, Units.val_one, colsN_one] at h1
  rwa [colsN_decN validN_zPC] at h1

theorem m22a_mul_self : L1442M.m22a * L1442M.m22a = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  exact L1442M.m22a.val_inv

theorem m22a_mul_zP : L1442M.m22a * zP * L1442M.m22a = zP * zP := by
  apply Units.ext
  have ha : ((L1442M.m22a : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      decN 12 (M22Cert.gG.getD 0 M22Cert.one12) := M22Cert.gU_val 0
  have hla : (M22Cert.gG.getD 0 M22Cert.one12).length = 12 :=
    (validN_getD M22Cert.validN_gG 0).1
  have hz := validN_zPC.1
  simp only [Units.val_mul]
  rw [ha, zP_val, Matrix.mul_assoc, ← decN_mulN hz hla,
    ← decN_mulN hla ((length_mulN _ _).trans hla), ← decN_mulN hz hz, mulN_a_zPC]

theorem m22a_not_comm_zP : L1442M.m22a * zP ≠ zP * L1442M.m22a := by
  intro h
  have h1 : zP * zP = zP := by
    rw [← m22a_mul_zP, h, mul_assoc, m22a_mul_self, mul_one]
  exact zP_ne_one (mul_eq_left.mp h1)

end CFSG.Quasithin.H.Mathieu.M22Link
