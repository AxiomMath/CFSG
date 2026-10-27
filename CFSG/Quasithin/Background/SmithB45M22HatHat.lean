module

public import CFSG.Quasithin.Background.SmithB45M22HatModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.HatM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Open CFSG.Blueprint
open scoped Matrix commutatorElement

theorem hatM22Z_mem_center : hatM22Z ∈ Subgroup.center ↥hatM22Γ₀ := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hatM22Z_val, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

theorem center_hatM22Γ₀ :
    Subgroup.center ↥hatM22Γ₀ = hatM22Act.ker := by
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker]
    have hc : (⟨hatM22Act g, hatM22Act_mem g⟩ : ↥quasithinM22) ∈ Subgroup.center ↥quasithinM22 := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨x, hx⟩
      apply Subtype.ext
      rw [← range_hatM22Act] at hx
      obtain ⟨h, rfl⟩ := hx
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg h]
    have hbot : Subgroup.center ↥quasithinM22 = ⊥ := m22_center_eq_bot'
    rw [hbot, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  · intro hg
    rcases (mem_ker_hatM22Act_iff g).1 hg with rfl | rfl | rfl
    · exact one_mem _
    · exact hatM22Z_mem_center
    · exact Subgroup.pow_mem _ hatM22Z_mem_center 2

theorem hatM22Z_ne_one : hatM22Z ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : ↥hatM22Γ₀ =>
    ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) h
  simp only [hatM22Z_val] at h1
  exact absurd h1 (by decide)

theorem hatM22Z_sq_ne_one : hatM22Z ^ 2 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : ↥hatM22Γ₀ =>
    ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) h
  simp only [hatM22Z_sq_val] at h1
  exact absurd h1 (by decide)

theorem hatM22Z_ne_sq : hatM22Z ≠ hatM22Z ^ 2 := by
  intro h
  have h1 := congrArg (fun g : ↥hatM22Γ₀ =>
    ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) h
  simp only [hatM22Z_val, hatM22Z_sq_val] at h1
  exact absurd h1 (by decide)

theorem card_center_hatM22Γ₀ :
    Nat.card (Subgroup.center ↥hatM22Γ₀) = 3 := by
  rw [center_hatM22Γ₀]
  have hset : ((hatM22Act.ker : Subgroup ↥hatM22Γ₀) : Set ↥hatM22Γ₀) =
      {1, hatM22Z, hatM22Z ^ 2} := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_hatM22Act_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  show Nat.card ↑((hatM22Act.ker : Subgroup ↥hatM22Γ₀) : Set ↥hatM22Γ₀) = 3
  rw [hset, Nat.card_coe_set_eq, Set.ncard_eq_three]
  exact ⟨1, hatM22Z, hatM22Z ^ 2, hatM22Z_ne_one.symm, hatM22Z_sq_ne_one.symm, hatM22Z_ne_sq,
    rfl⟩

@[expose] noncomputable def hatM22QuotEquiv :
    ↥hatM22Γ₀ ⧸ Subgroup.center ↥hatM22Γ₀ ≃* ↥quasithinM22 :=
  (QuotientGroup.quotientMulEquivOfEq center_hatM22Γ₀).trans
    ((QuotientGroup.quotientKerEquivRange hatM22Act).trans
      (MulEquiv.subgroupCongr range_hatM22Act))

theorem isSimpleGroup_quasithinM22 :
    IsSimpleGroup ↥quasithinM22 :=
  fam_m22_simplicity.2.2

theorem quasithinM22_not_comm :
    ∃ a b : ↥quasithinM22, a * b ≠ b * a :=
  ⟨m22a, m22b, m22_gens_not_comm⟩

theorem commutator_quasithinM22 :
    commutator ↥quasithinM22 = ⊤ := by
  have hs : IsSimpleGroup ↥quasithinM22 := isSimpleGroup_quasithinM22
  rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥quasithinM22) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := quasithinM22_not_comm
    apply hab
    have h1 : ⁅a, b⁆ ∈ commutator ↥quasithinM22 :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exact h

theorem hatM22N1_pow_four : hatM22N1 ^ 4 = 1 := by decide +kernel

theorem hatM22N2_pow_four : hatM22N2 ^ 4 = 1 := by decide +kernel

theorem abelianization_pow_four (q : Abelianization ↥hatM22Γ₀) : q ^ 4 = 1 := by
  let S : Subgroup (Abelianization ↥hatM22Γ₀) :=
    { carrier := {q | q ^ 4 = 1}
      mul_mem' := fun {a b} (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) =>
        show (a * b) ^ 4 = 1 by rw [mul_pow, ha, hb, one_mul]
      one_mem' := show (1 : Abelianization ↥hatM22Γ₀) ^ 4 = 1 by rw [one_pow]
      inv_mem' := fun {a} (ha : a ^ 4 = 1) => show a⁻¹ ^ 4 = 1 by rw [inv_pow, ha, inv_one] }
  have hgen : (⊤ : Subgroup ↥hatM22Γ₀) = Subgroup.closure
      ((Subtype.val : ↥hatM22Γ₀ → Matrix.GeneralLinearGroup (Fin 6) FieldFour) ⁻¹'
        {hatM22G1, hatM22G2}) :=
    Subgroup.closure_closure_coe_preimage.symm
  have hle : (⊤ : Subgroup ↥hatM22Γ₀) ≤ S.comap Abelianization.of := by
    rw [hgen, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    show (Abelianization.of g) ^ 4 = 1
    rw [← map_pow]
    have hg4 : g ^ 4 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      rcases hg with hg | hg
      · rw [hg]
        exact hatM22N1_pow_four
      · rw [hg]
        exact hatM22N2_pow_four
    rw [hg4, map_one]
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : g ∈ S.comap Abelianization.of := hle (Subgroup.mem_top g)
  exact hmem

theorem hatM22Z_mem_commutator : hatM22Z ∈ commutator ↥hatM22Γ₀ := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  have h4 := abelianization_pow_four (Abelianization.of hatM22Z)
  have h3 : (Abelianization.of hatM22Z) ^ 3 = 1 := by rw [← map_pow, hatM22Z_pow_three, map_one]
  calc Abelianization.of hatM22Z = (Abelianization.of hatM22Z) ^ 4 *
        ((Abelianization.of hatM22Z) ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, h3, inv_one, one_mul]

theorem isPerfect_hatM22Γ₀ :
    Group.IsPerfect ↥hatM22Γ₀ := by
  rw [Group.isPerfect_def]
  have hmap : (commutator ↥hatM22Γ₀).map hatM22Act = quasithinM22 := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_hatM22Act,
      ← Subgroup.map_subtype_commutator, commutator_quasithinM22, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hker : hatM22Act.ker ≤ commutator ↥hatM22Γ₀ := by
    intro g hg
    rcases (mem_ker_hatM22Act_iff g).1 hg with rfl | rfl | rfl
    · exact one_mem _
    · exact hatM22Z_mem_commutator
    · exact Subgroup.pow_mem _ hatM22Z_mem_commutator 2
  rw [eq_top_iff]
  intro g _
  have hg : hatM22Act g ∈ (commutator ↥hatM22Γ₀).map hatM22Act := by
    rw [hmap]
    exact hatM22Act_mem g
  obtain ⟨c, hc, hcg⟩ := hg
  have hk : c⁻¹ * g ∈ hatM22Act.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
  have : g = c * (c⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem _ hc (hker hk)

theorem isHat_hatM22Γ₀ :
    IsHat ↥hatM22Γ₀ ↥quasithinM22 := by
  have hsimple : IsSimpleGroup ↥quasithinM22 := isSimpleGroup_quasithinM22
  refine ⟨⟨isPerfect_hatM22Γ₀, MulEquiv.isSimpleGroup hatM22QuotEquiv, ?_⟩,
    card_center_hatM22Γ₀, ⟨hatM22QuotEquiv⟩⟩
  obtain ⟨a, b, hab⟩ := quasithinM22_not_comm
  refine ⟨hatM22QuotEquiv.symm a, hatM22QuotEquiv.symm b, fun h => hab ?_⟩
  have := congrArg hatM22QuotEquiv h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

@[expose] def hatM22Form : Matrix (Fin 6) (Fin 6) FieldFour := untab hatM22FormTab

@[expose] def hatM22FormInv : Matrix (Fin 6) (Fin 6) FieldFour :=
  untab #v[#v[0, ω₂, 1, ω₂, 1, 1],
    #v[ω, 0, 1, ω, 0, ω₂],
    #v[1, 1, 1, ω₂, 0, 0],
    #v[ω, ω₂, ω, 0, 0, 1],
    #v[1, 0, 0, 0, 1, ω₂],
    #v[1, ω, 0, 1, ω, 0]]

theorem hatM22Form_mul_inv : hatM22Form * hatM22FormInv = 1 := by decide +kernel

theorem hatM22Form_det_ne_zero : hatM22Form.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det hatM22Form_mul_inv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem frobPow_one_eq (X : Matrix (Fin 6) (Fin 6) FieldFour) : frobPow 1 X = X.map frob := by
  unfold frobPow
  congr 1
  funext x
  rw [frob_apply, pow_one]

theorem frobPow_one_mul (X Y : Matrix (Fin 6) (Fin 6) FieldFour) :
    frobPow 1 (X * Y) = frobPow 1 X * frobPow 1 Y := by
  rw [frobPow_one_eq, frobPow_one_eq, frobPow_one_eq, Matrix.map_mul]

theorem frobPow_one_one : frobPow 1 (1 : Matrix (Fin 6) (Fin 6) FieldFour) = 1 := by
  rw [frobPow_one_eq]
  exact Matrix.map_one _ (map_zero frob) (map_one frob)

theorem hatM22Form_hermitian : (frobPow 1 hatM22Form)ᵀ = hatM22Form := by
  rw [frobPow_one_eq]
  decide +kernel

theorem hatM22Form_N1 : (frobPow 1 hatM22N1)ᵀ * hatM22Form * hatM22N1 = hatM22Form := by
  rw [frobPow_one_eq]
  decide +kernel

theorem hatM22Form_N2 : (frobPow 1 hatM22N2)ᵀ * hatM22Form * hatM22N2 = hatM22Form := by
  rw [frobPow_one_eq]
  decide +kernel

theorem hatM22Form_invariant : ∀ g ∈ hatM22Γ₀,
    (frobPow 1 ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour))ᵀ * hatM22Form *
      ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) =
      hatM22Form := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hatM22Form_N1
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hatM22Form_N2
  | one =>
    rw [Units.val_one, frobPow_one_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, frobPow_one_mul, Matrix.transpose_mul]
    calc (frobPow 1 (y : Matrix (Fin 6) (Fin 6) FieldFour))ᵀ *
          (frobPow 1 (x : Matrix (Fin 6) (Fin 6) FieldFour))ᵀ * hatM22Form *
          ((x : Matrix (Fin 6) (Fin 6) FieldFour) * (y : Matrix (Fin 6) (Fin 6) FieldFour))
        = (frobPow 1 (y : Matrix (Fin 6) (Fin 6) FieldFour))ᵀ *
          ((frobPow 1 (x : Matrix (Fin 6) (Fin 6) FieldFour))ᵀ * hatM22Form *
            (x : Matrix (Fin 6) (Fin 6) FieldFour)) * (y : Matrix (Fin 6) (Fin 6) FieldFour) := by
          simp only [Matrix.mul_assoc]
      _ = hatM22Form := by rw [hx, hy]
  | inv x _ hx =>
    have hxi : ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour) * (x : Matrix (Fin 6) (Fin 6) FieldFour) = 1 :=
      Units.inv_mul x
    have hix : (x : Matrix (Fin 6) (Fin 6) FieldFour) *
        ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour) = 1 :=
      Units.mul_inv x
    have hf : (frobPow 1 ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour))ᵀ *
        (frobPow 1 (x : Matrix (Fin 6) (Fin 6) FieldFour))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← frobPow_one_mul, hix, frobPow_one_one, Matrix.transpose_one]
    calc (frobPow 1 ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour))ᵀ * hatM22Form *
          ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)
        = (frobPow 1 ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
            Matrix (Fin 6) (Fin 6) FieldFour))ᵀ *
          ((frobPow 1 (x : Matrix (Fin 6) (Fin 6) FieldFour))ᵀ * hatM22Form *
            (x : Matrix (Fin 6) (Fin 6) FieldFour)) *
          ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
            Matrix (Fin 6) (Fin 6) FieldFour) := by rw [hx]
      _ = ((frobPow 1 ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
            Matrix (Fin 6) (Fin 6) FieldFour))ᵀ *
            (frobPow 1 (x : Matrix (Fin 6) (Fin 6) FieldFour))ᵀ) * hatM22Form *
          ((x : Matrix (Fin 6) (Fin 6) FieldFour) *
            ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
              Matrix (Fin 6) (Fin 6) FieldFour)) := by simp only [Matrix.mul_assoc]
      _ = hatM22Form := by rw [hf, hix, Matrix.one_mul, Matrix.mul_one]

end CFSG.Quasithin.HatM22
