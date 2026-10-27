module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix

namespace LinModel

variable {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem diagGL_injective : Function.Injective (InnerDiagA.diagGL (m := m) (F := F)) := by
  intro d e h
  funext i
  have := congrArg (fun A : GL (Fin (m + 1)) F =>
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) h
  simp only [diagGL_apply] at this
  exact Units.ext (by simpa using this)

theorem det_diagGL (d : Fin (m + 1) → Fˣ) :
    GeneralLinearGroup.det (InnerDiagA.diagGL d) = ∏ i, d i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, InnerDiagA.coe_diagGL, det_diagonal, Units.coe_prod]

theorem det_scalar_eq (u : Fˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (m + 1)) u) = u ^ (m + 1) := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]

theorem prod_pow_val_eq_one {p : ℕ} [NeZero p] {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (a : Fin (m + 1) → ZMod p) (ha : ∑ i, a i = 0) : ∏ i, ω ^ (a i).val = 1 := by
  rw [Finset.prod_pow_eq_pow_sum, hω.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sum]
  simpa only [ZMod.natCast_zmod_val] using ha

theorem card_le_card_rootTorus_three [CharP F 2] [Finite G] {p : ℕ} [NeZero p] (hm : 4 ≤ m)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {ω : Fˣ} (hω : IsPrimitiveRoot ω p) : p ^ 3 ≤ Nat.card (rootTorus p ψ) := by
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (m + 1) := ⟨2, by omega⟩ with hi₂
  set i₃ : Fin (m + 1) := ⟨3, by omega⟩ with hi₃
  set i₄ : Fin (m + 1) := ⟨4, by omega⟩ with hi₄
  have h01 : (0 : Fin (m + 1)) ≠ i₁ := Fin.ne_of_val_ne (by simp [hi₁])
  have h02 : (0 : Fin (m + 1)) ≠ i₂ := Fin.ne_of_val_ne (by simp [hi₂])
  have h03 : (0 : Fin (m + 1)) ≠ i₃ := Fin.ne_of_val_ne (by simp [hi₃])
  have h04 : (0 : Fin (m + 1)) ≠ i₄ := Fin.ne_of_val_ne (by simp [hi₄])
  have h12 : i₁ ≠ i₂ := Fin.ne_of_val_ne (by simp [hi₁, hi₂])
  have h13 : i₁ ≠ i₃ := Fin.ne_of_val_ne (by simp [hi₁, hi₃])
  have h14 : i₁ ≠ i₄ := Fin.ne_of_val_ne (by simp [hi₁, hi₄])
  have h23 : i₂ ≠ i₃ := Fin.ne_of_val_ne (by simp [hi₂, hi₃])
  have h24 : i₂ ≠ i₄ := Fin.ne_of_val_ne (by simp [hi₂, hi₄])
  have h34 : i₃ ≠ i₄ := Fin.ne_of_val_ne (by simp [hi₃, hi₄])
  set a : (Fin 3 → ZMod p) → Fin (m + 1) → ZMod p := fun x =>
    Pi.single i₁ (x 0) + Pi.single i₂ (x 1) + Pi.single i₃ (x 2) -
      Pi.single i₄ (x 0 + x 1 + x 2) with ha
  have ha0 : ∀ x, a x 0 = 0 := fun x => by
    simp only [ha, Pi.sub_apply, Pi.add_apply, Pi.single_eq_of_ne h01, Pi.single_eq_of_ne h02,
      Pi.single_eq_of_ne h03, Pi.single_eq_of_ne h04, add_zero, sub_zero]
  have hai : ∀ x, a x i₁ = x 0 ∧ a x i₂ = x 1 ∧ a x i₃ = x 2 := fun x => by
    simp only [ha, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h12,
      Pi.single_eq_of_ne h13, Pi.single_eq_of_ne h14, Pi.single_eq_of_ne h12.symm,
      Pi.single_eq_of_ne h23, Pi.single_eq_of_ne h24, Pi.single_eq_of_ne h13.symm,
      Pi.single_eq_of_ne h23.symm, Pi.single_eq_of_ne h34]
    simp
  have hainj : Function.Injective a := fun x y hxy => by
    have h1 := hai x
    have h2 := hai y
    rw [hxy] at h1
    funext k
    fin_cases k
    · exact h1.1.symm.trans h2.1
    · exact h1.2.1.symm.trans h2.2.1
    · exact h1.2.2.symm.trans h2.2.2
  have hsum : ∀ x, ∑ i, a x i = 0 := fun x => by
    simp only [ha, Pi.sub_apply, Pi.add_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_pi_single', Finset.mem_univ, ite_true]
    ring
  have h := card_le_card_rootTorus hker hω a ha0 hainj fun x =>
    ⟨_, exists_mem_of_prod_eq_one ψ _ (prod_pow_val_eq_one hω (a x) (hsum x))⟩
  simpa [Nat.card_fun] using h

theorem card_le_card_rootTorus_cons [CharP F 2] [Finite G] {p : ℕ} [NeZero p]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (hreal : ∀ a : Fin (m + 1) → ZMod p, ∃ g : G,
      (g, InnerDiagA.diagGL (fun i => ω ^ (a i).val)) ∈ LinFusion.ggInducedPairs ψ) :
    p ^ m ≤ Nat.card (rootTorus p ψ) := by
  have h := card_le_card_rootTorus hker hω
    (fun x : Fin m → ZMod p => (Fin.cons 0 x : Fin (m + 1) → ZMod p))
    (fun x => Fin.cons_zero _ _)
    (fun x y hxy => Fin.cons_right_injective (α := fun _ : Fin (m + 1) => ZMod p) 0 hxy)
    fun x => hreal _
  simpa [Nat.card_fun] using h

theorem exists_conj_mem_rootTorus [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmp : m + 1 = p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {y : G}
    (hyp : y ^ p = 1) {Y : GL (Fin (m + 1)) F} (hY : (y, Y) ∈ LinFusion.ggInducedPairs ψ)
    (hdet : ∃ c : Fˣ, c ^ p = GeneralLinearGroup.det Y) :
    ∃ s : Matrix.SpecialLinearGroup (Fin (m + 1)) F, ψ s * y * (ψ s)⁻¹ ∈ rootTorus p ψ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpm : ∀ u : Fˣ, u ^ (m + 1) = u ^ p := fun u => by rw [hmp]
  obtain ⟨c, hc⟩ := hdet
  set Y₂ := GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * Y with hY₂def
  have hY₂ : (y, Y₂) ∈ LinFusion.ggInducedPairs ψ := scalar_mul_mem_ggInducedPairs hY c⁻¹
  have hdetY₂ : GeneralLinearGroup.det Y₂ = 1 := by
    rw [hY₂def, map_mul, det_scalar_eq, hpm, ← hc, inv_pow, inv_mul_cancel]
  have hpow := (LinFusion.ggInducedPairs ψ).pow_mem hY₂ p
  rw [Prod.pow_mk, hyp] at hpow
  obtain ⟨l, hl⟩ := LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker hpow
  obtain ⟨μ, hμ⟩ : ∃ μ : Fˣ, μ ^ p = l := by
    by_contra hne
    have hnot : ∀ b : F, b ^ p ≠ (l : F) := by
      intro b hb
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hb
        exact l.ne_zero hb.symm
      exact hne ⟨Units.mk0 b hb0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hb])⟩
    have hdetl := det_eq_of_pow_eq_scalar hp hp2 (by rw [Fintype.card_fin, hmp])
      (M := ((Y₂ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (c := (l : F))
      (by rw [← Units.val_pow_eq_pow_val, hl, GeneralLinearGroup.coe_scalar]) hnot
    have h1 := GeneralLinearGroup.val_det_apply Y₂
    rw [hdetY₂, Units.val_one, hdetl] at h1
    exact hne ⟨1, by rw [one_pow]; exact Units.ext h1⟩
  set Y₃ := GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹ * Y₂ with hY₃def
  have hY₃ : (y, Y₃) ∈ LinFusion.ggInducedPairs ψ := scalar_mul_mem_ggInducedPairs hY₂ μ⁻¹
  have hY₃p : Y₃ ^ p = 1 := by
    rw [hY₃def, (TypeA.PGLTor.commute_scalar μ⁻¹ Y₂).mul_pow, hl, ← map_pow, ← map_mul, inv_pow,
      hμ, inv_mul_cancel, map_one]
  obtain ⟨A, hA⟩ := TypeA.PGLTor.exists_conj_diagonal hζ
    ({Y₃} : Set (GL (Fin (m + 1)) F)) (by rintro x rfl y rfl; rfl) (by rintro x rfl; exact hY₃p)
  obtain ⟨d, hd⟩ := LinTorus.exists_eq_diagGL (M := A * Y₃ * A⁻¹) fun i j hij => by
    rw [Units.val_mul, Units.val_mul]
    exact hA Y₃ rfl i j hij
  have hdp : ∀ i, d i ^ p = 1 := by
    have h1 : InnerDiagA.diagGL (d ^ p) = InnerDiagA.diagGL 1 := by
      rw [diagGL_pow, ← hd, conj_pow, hY₃p, mul_one, mul_inv_cancel, LinFusion.diagGL_one]
    intro i
    have := congrFun (diagGL_injective h1) i
    simpa using this
  set e : Fin (m + 1) → Fˣ := Pi.mulSingle 0 (GeneralLinearGroup.det A)⁻¹ with he
  set A' := InnerDiagA.diagGL e * A with hA'
  have hA'det : GeneralLinearGroup.det A' = 1 := by
    rw [hA', map_mul, det_diagGL, he]
    simp
  have hA'conj : A' * Y₃ * A'⁻¹ = InnerDiagA.diagGL d := by
    rw [show A' * Y₃ * A'⁻¹ = InnerDiagA.diagGL e * (A * Y₃ * A⁻¹) * (InnerDiagA.diagGL e)⁻¹ by
      rw [hA']; group, hd, LinFusion.diagGL_mul_comm e d, mul_inv_cancel_right]
  set s : Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
    ⟨(A' : Matrix (Fin (m + 1)) (Fin (m + 1)) F), by
      rw [← GeneralLinearGroup.val_det_apply, hA'det, Units.val_one]⟩ with hs
  have hsA' : Matrix.SpecialLinearGroup.toGL s = A' := Units.ext rfl
  refine ⟨s, d, hdp, ?_⟩
  have h1 := (LinFusion.ggInducedPairs ψ).mul_mem
    ((LinFusion.ggInducedPairs ψ).mul_mem (map_toGL_mem_ggInducedPairs ψ s) hY₃)
    ((LinFusion.ggInducedPairs ψ).inv_mem (map_toGL_mem_ggInducedPairs ψ s))
  rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, hsA', hA'conj] at h1
  exact h1

theorem card_bstar_le_of_sl [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m)
    (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b) :
    Nat.card Bs ≤ p ^ m := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpf
  have hBsA : ∀ b ∈ Bs, ∃ A, (b, A) ∈ LinFusion.ggInducedPairs ψ := fun b hb =>
    LinFusion.exists_mem_ggInducedPairs hm ψ hker (hBsI b⁻¹ (Bs.inv_mem hb))
  have hEC : Bs ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hC, inf_bot_eq]
  have h1 := TypeA.PGLTor.card_le_of_isProjElem hp hp2 hpF
    (LinTorus.isProjElem_inducedMatrices (p := p) hker hBsE)
  rw [LinTorus.card_inducedMatrices hker hBsA hEC, Fintype.card_fin, ← mul_assoc] at h1
  have hF1 : 0 < Nat.card (GaloisField 2 f) - 1 := by
    have := Finite.one_lt_card (α := GaloisField 2 f)
    omega
  have h2 := Nat.le_of_mul_le_mul_right h1 hF1
  rw [pow_succ'] at h2
  exact Nat.le_of_mul_le_mul_left h2 hp.pos

theorem exists_frame_of_sl [Finite G] {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmp : m + 1 = p)
    (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs) :
    ∃ P : GL (Fin (m + 1)) (GaloisField 2 f),
      (∀ b ∈ Bs, ∃ d, (b, InnerDiagA.diagGL d) ∈
        LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹))) ∧
      rootTorus p (ψ.comp (InnerDiagA.conjSL P⁻¹)) ≤ Bs := by
  have hp2 : p ≠ 2 := by omega
  have : NeZero p := ⟨hp.ne_zero⟩
  have hm : 2 ≤ m := by omega
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpf
  obtain ⟨ζ, hζ⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpF
  set ω : (GaloisField 2 f)ˣ := (hζ.isUnit hp.ne_zero).unit with hωdef
  have hω : IsPrimitiveRoot ω p := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hωdef, IsUnit.unit_spec]; exact hζ)
  have hBsA : ∀ b ∈ Bs, ∃ A, (b, A) ∈ LinFusion.ggInducedPairs ψ := fun b hb =>
    LinFusion.exists_mem_ggInducedPairs hm ψ hker (hBsI b⁻¹ (Bs.inv_mem hb))
  have hEC : Bs ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hC, inf_bot_eq]
  have hlow3 : p ^ 3 ≤ Nat.card Bs :=
    (card_le_card_rootTorus_three (by omega) hker hω).trans
      (card_le_of_bstarUniqueIn hp hBsE hBsM hU (isElemAbelian_rootTorus hC)
        (rootTorus_le_normalizer p ψ))
  have hbig : p ^ ((m + 1) / p + 1) < Nat.card Bs := by
    rw [hmp, Nat.div_self hp.pos]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp.one_lt (by norm_num)) hlow3
  obtain ⟨P, hP⟩ := LinTorus.exists_le_ggFrameTorus hp hp2 hpF hker hBsE hbig hBsA hEC
  have hC' : Subgroup.centralizer ((ψ.comp (InnerDiagA.conjSL P⁻¹)).range : Set G) = ⊥ := by
    rw [LinTorus.range_comp_conjSL ψ P⁻¹]
    exact hC
  have hBsD : ∀ b ∈ Bs, ∃ d, (b, InnerDiagA.diagGL d) ∈
      LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹)) := fun b hb => by
    obtain ⟨d, hd⟩ := hP hb
    exact ⟨d, LinTorus.mem_ggInducedPairs_frame hd⟩
  exact ⟨P, hBsD, rootTorus_le hC' hBsD hom⟩

theorem card_bstar_eq_of_sl [Finite G] {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmp : m + 1 = p)
    (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs) {y : G}
    (hyM : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyo : orderOf y = p)
    (hy : ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), g⁻¹ * y * g ∉ Bs) :
    Nat.card Bs = p ^ (p - 1) := by
  have hp2 : p ≠ 2 := by omega
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hm : 2 ≤ m := by omega
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpf
  obtain ⟨ζ, hζ⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpF
  set ω : (GaloisField 2 f)ˣ := (hζ.isUnit hp.ne_zero).unit with hωdef
  have hω : IsPrimitiveRoot ω p := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hωdef, IsUnit.unit_spec]; exact hζ)
  have hupper := card_bstar_le_of_sl hp hp2 hm hf hpf hker hC hBsE hBsI
  obtain ⟨P, -, hW⟩ := exists_frame_of_sl hp hp5 hmp hf hpf hker hC hBsM hBsE hBsI hom hU
  set ψ' := ψ.comp (InnerDiagA.conjSL P⁻¹) with hψ'
  have hker' := LinTorus.ker_comp_conjSL_le hker P⁻¹
  have hrange' : ψ'.range = ψ.range := LinTorus.range_comp_conjSL ψ P⁻¹
  have hpm : ∀ u : (GaloisField 2 f)ˣ, u ^ (m + 1) = u ^ p := fun u => by rw [hmp]
  have hfin : p ^ m ≤ Nat.card (rootTorus p ψ') → Nat.card Bs = p ^ (p - 1) := fun h => by
    rw [show p - 1 = m by omega]
    exact le_antisymm hupper (h.trans (Subgroup.card_le_of_le hW))
  by_cases hA : ∃ (g₀ : G) (A₀ : GL (Fin (m + 1)) (GaloisField 2 f)),
      (g₀, A₀) ∈ LinFusion.ggInducedPairs ψ' ∧ ¬ ∃ c, c ^ p = GeneralLinearGroup.det A₀
  · obtain ⟨g₀, A₀, h₀, hdet⟩ := hA
    exact hfin (card_le_card_rootTorus_cons hker' hω fun a => exists_mem_of_det hmp h₀ hdet _)
  by_cases hB : ∃ ζ' : (GaloisField 2 f)ˣ, ζ' ^ p = ω
  · obtain ⟨ζ', hζ'⟩ := hB
    refine hfin (card_le_card_rootTorus_cons hker' hω fun a => ?_)
    obtain ⟨g, -, hg⟩ := exists_mem_of_scalar ψ' (fun i => ω ^ (a i).val)
      (ζ' ^ (∑ i, (a i).val))⁻¹ (by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hpm,
          Finset.prod_pow_eq_pow_sum, inv_pow, pow_right_comm, hζ', inv_mul_cancel])
    exact ⟨g, hg⟩
  exfalso
  have hpf' : ¬ p ∣ f := fun h => hB (exists_pow_eq_of_sq_dvd hp
    (by rw [Nat.card_units, hF]; exact sq_dvd_two_pow_sub_one hp hp2 h hf hpf) hω.pow_eq_one)
  have hσ : ∀ σ : GaloisField 2 f ≃+* GaloisField 2 f, σ ^ p = 1 → σ = 1 := fun σ h =>
    eq_one_of_pow_eq_one_of_not_dvd (by omega) hp hpf' h
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  obtain ⟨Y, hY⟩ := exists_mem_ggInducedPairs_of_pow_eq_one hm hp hp2 hσ hker hC hyM hyp
  have hY' := mem_ggInducedPairs_comp_conjSL_inv hY P
  obtain ⟨c, hc⟩ : ∃ c, c ^ p = GeneralLinearGroup.det (P * Y * P⁻¹) := by
    by_contra hne
    exact hA ⟨y, _, hY', hne⟩
  obtain ⟨s, hs⟩ := exists_conj_mem_rootTorus hp hp2 hmp hζ hker' hyp hY' ⟨c, hc⟩
  have hsM : (ψ' s)⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) := by
    refine Subgroup.le_normalizer (Subgroup.inv_mem _ ?_)
    rw [← hrange']
    exact ⟨s, rfl⟩
  exact hy _ hsM (by rw [inv_inv]; exact hW hs)

end LinModel

section Inputs

theorem ggSixLinearRankOn_PSL : GGSixLinearRankOn .PSL := by
  intro G _ _ p Bs G₀ n f ψ hS hlin y hyM hyo hy
  obtain ⟨hp5, hnp, hcase⟩ := hlin
  have hpf : p ∣ 2 ^ f - 1 := by
    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hS.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hrange
  exact LinModel.card_bstar_eq_of_sl hS.prime hp5 hnp hadm.2.1 hpf hker hS.2.2.1
    hS.bstar_le hS.elem hS.2.2.2.1.2.2 hS.omega hS.unique hyM hyo hy

theorem ggSixLinearRankInput_of_psu (hU : GGSixLinearRankOn .PSU) : GGSixLinearRankInput :=
  ggSixLinearRankInput_of_tags ggSixLinearRankOn_PSL hU

end Inputs

end CFSG.StandardType
