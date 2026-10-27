module

public import CFSG.Quasithin.Vol2.Ch9L34Gam
public import CFSG.Quasithin.Background.HL3NineNorm
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.Quasithin.H13.Ch9.L34N

open CFSG.Fischer Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M CFSG.ComponentClassification

variable {M : Type*} [Group M]

@[expose] def slRep (ρ : GL (Fin 3) F4 →* MulAut M) :
    SpecialLinearGroup (Fin 3) F4 →* MulAut M :=
  ρ.comp SpecialLinearGroup.toGL

@[expose] def img (ρ : GL (Fin 3) F4 →* MulAut M) : Subgroup (MulAut M) := (slRep ρ).range

theorem slRep_mem_img (ρ : GL (Fin 3) F4 →* MulAut M) (g : SpecialLinearGroup (Fin 3) F4) :
    slRep ρ g ∈ img ρ :=
  ⟨g, rfl⟩

theorem le_scalars_of_normal {N : Subgroup (SpecialLinearGroup (Fin 3) F4)} (hN : N.Normal)
    (hne : N.map (LinearFlag.proj 3 F4) ≠ ⊤) : N ≤ LinearFlag.scalars 3 F4 := by
  have hs := CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL
    (n := 3) (K := F4) le_rfl
  have hNm : (N.map (LinearFlag.proj 3 F4)).Normal := hN.map _ (LinearFlag.proj_surjective 3 F4)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (LinearFlag.proj 3 F4)) with h | h
  · intro g hg
    rw [← LinearFlag.proj_eq_one_iff]
    have : LinearFlag.proj 3 F4 g ∈ N.map (LinearFlag.proj 3 F4) := ⟨g, hg, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  · exact absurd h hne

theorem exists_mul_of_map_eq_top {N : Subgroup (SpecialLinearGroup (Fin 3) F4)}
    (h : N.map (LinearFlag.proj 3 F4) = ⊤) (g : SpecialLinearGroup (Fin 3) F4) :
    ∃ n ∈ N, ∃ z ∈ LinearFlag.scalars 3 F4, g = n * z := by
  have hg : LinearFlag.proj 3 F4 g ∈ N.map (LinearFlag.proj 3 F4) := h ▸ Subgroup.mem_top _
  obtain ⟨n, hn, hng⟩ := hg
  refine ⟨n, hn, n⁻¹ * g, LinearFlag.proj_eq_proj_iff.mp hng, by group⟩

theorem commute_of_scalars {z : SpecialLinearGroup (Fin 3) F4}
    (hz : z ∈ LinearFlag.scalars 3 F4) (k : SpecialLinearGroup (Fin 3) F4) : z * k = k * z :=
  (Subgroup.mem_center_iff.mp (LinearFlag.scalars_le_center 3 F4 hz) k).symm

theorem mem_scalars_of_slRep_eq_one (ρ : GL (Fin 3) F4 →* MulAut M)
    (hnc : ∃ a b, slRep ρ a * slRep ρ b ≠ slRep ρ b * slRep ρ a)
    {g : SpecialLinearGroup (Fin 3) F4} (hg : slRep ρ g = 1) : g ∈ LinearFlag.scalars 3 F4 := by
  refine le_scalars_of_normal (slRep ρ).normal_ker (fun h => ?_) (MonoidHom.mem_ker.mpr hg)
  obtain ⟨a, b, hab⟩ := hnc
  obtain ⟨n, hn, z, hz, rfl⟩ := exists_mul_of_map_eq_top h a
  obtain ⟨n', hn', z', hz', rfl⟩ := exists_mul_of_map_eq_top h b
  apply hab
  rw [map_mul, map_mul, MonoidHom.mem_ker.mp hn, MonoidHom.mem_ker.mp hn', one_mul, one_mul,
    ← map_mul, ← map_mul, commute_of_scalars hz z']

@[expose] def centPre (ρ : GL (Fin 3) F4 →* MulAut M) : Subgroup (SpecialLinearGroup (Fin 3) F4) :=
  (Subgroup.centralizer (img ρ : Set (MulAut M))).comap (slRep ρ)

theorem centPre_normal (ρ : GL (Fin 3) F4 →* MulAut M) : (centPre ρ).Normal := by
  refine ⟨fun g hg h => ?_⟩
  change slRep ρ (h * g * h⁻¹) ∈ Subgroup.centralizer (img ρ : Set (MulAut M))
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp hg
  have e1 := hc (slRep ρ (h⁻¹ * k * h)) (slRep_mem_img ρ _)
  simp only [map_mul, map_inv] at e1 ⊢
  calc slRep ρ k * (slRep ρ h * slRep ρ g * (slRep ρ h)⁻¹) =
      slRep ρ h * ((slRep ρ h)⁻¹ * slRep ρ k * slRep ρ h * slRep ρ g) * (slRep ρ h)⁻¹ := by
        group
    _ = slRep ρ h * (slRep ρ g * ((slRep ρ h)⁻¹ * slRep ρ k * slRep ρ h)) * (slRep ρ h)⁻¹ := by
        rw [e1]
    _ = slRep ρ h * slRep ρ g * (slRep ρ h)⁻¹ * slRep ρ k := by group

theorem mem_scalars_of_comm (ρ : GL (Fin 3) F4 →* MulAut M)
    (hnc : ∃ a b, slRep ρ a * slRep ρ b ≠ slRep ρ b * slRep ρ a)
    {g : SpecialLinearGroup (Fin 3) F4} (hg : ∀ k, slRep ρ g * slRep ρ k = slRep ρ k * slRep ρ g) :
    g ∈ LinearFlag.scalars 3 F4 := by
  have hmem : g ∈ centPre ρ := by
    change slRep ρ g ∈ Subgroup.centralizer (img ρ : Set (MulAut M))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (hg k).symm
  refine le_scalars_of_normal (centPre_normal ρ) (fun h => ?_) hmem
  obtain ⟨a, b, hab⟩ := hnc
  obtain ⟨n, hn, z, hz, rfl⟩ := exists_mul_of_map_eq_top h a
  obtain ⟨n', hn', z', hz', rfl⟩ := exists_mul_of_map_eq_top h b
  apply hab
  have hzc : ∀ y z₀, z₀ ∈ LinearFlag.scalars 3 F4 →
      slRep ρ z₀ * slRep ρ y = slRep ρ y * slRep ρ z₀ := fun y z₀ hz₀ => by
    rw [← map_mul, ← map_mul, commute_of_scalars hz₀ y]
  have hnc' : ∀ (y : SpecialLinearGroup (Fin 3) F4) (m : SpecialLinearGroup (Fin 3) F4),
      m ∈ centPre ρ → slRep ρ m * slRep ρ y = slRep ρ y * slRep ρ m := fun y m hm =>
    (Subgroup.mem_centralizer_iff.mp hm (slRep ρ y) (slRep_mem_img ρ y)).symm
  simp only [map_mul]
  exact (Commute.mul_left (Commute.mul_right (hnc' n' n hn) (hnc' z' n hn))
    (Commute.mul_right (hzc n' z hz) (hzc z' z hz))).eq

@[expose] def w0GL : GL (Fin 3) F4 := ⟨w0, w0, w0_mul_w0, w0_mul_w0⟩

theorem coe_w0GL : ((w0GL : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = w0 := rfl

theorem coe_w0GL_inv : ((w0GL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = w0 := rfl

theorem toGL_dual (g : SpecialLinearGroup (Fin 3) F4) :
    SpecialLinearGroup.toGL (g⁻¹).transpose =
      w0GL * grGL (SpecialLinearGroup.toGL g) * w0GL⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_w0GL, coe_w0GL_inv, grGL_apply, coe_grU, grM, ← map_inv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_transpose]
  simp only [Matrix.mul_assoc]
  rw [w0_mul_w0_mul, w0_mul_w0, Matrix.mul_one]

theorem toGL_map_cj (g : SpecialLinearGroup (Fin 3) F4) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map cjRing.toRingHom g) =
      frobGL (SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rw [coe_frobGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem ringEquiv_eq_refl_or_cj (σ : F4 ≃+* F4) : σ = RingEquiv.refl F4 ∨ σ = cjRing := by
  have hw : (⟨2⟩ : F4) * ⟨2⟩ + ⟨2⟩ + 1 = 0 := by
    simp only [mk_mul_mk, mk_add_mk, one_eq, zero_eq, F4.mk.injEq]
    decide
  have hσ : σ ⟨2⟩ * σ ⟨2⟩ + σ ⟨2⟩ + 1 = 0 := by
    rw [← map_mul, ← map_add, ← map_one σ, ← map_add, hw, map_zero]
  have hroot : ∀ x : F4, x * x + x + 1 = 0 → x = ⟨2⟩ ∨ x = ⟨3⟩ := by
    rintro ⟨a⟩ h
    simp only [mk_mul_mk, mk_add_mk, one_eq, zero_eq, F4.mk.injEq] at h ⊢
    revert a
    decide
  have hall : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = ⟨2⟩ ∨ x = ⟨2⟩ * ⟨2⟩ := by
    rintro ⟨a⟩
    simp only [mk_mul_mk, one_eq, zero_eq, F4.mk.injEq]
    revert a
    decide
  rcases hroot _ hσ with h | h
  · left
    refine RingEquiv.ext fun x => ?_
    rw [RingEquiv.refl_apply]
    rcases hall x with rfl | rfl | rfl | rfl
    · exact map_zero σ
    · exact map_one σ
    · exact h
    · rw [map_mul, h]
  · right
    refine RingEquiv.ext fun x => ?_
    rw [cjRing_apply]
    rcases hall x with rfl | rfl | rfl | rfl
    · rw [map_zero, cj_zero]
    · rw [map_one, cj_one]
    · rw [h, cj]
      simp only [mk_mul_mk, F4.mk.injEq]
      decide
    · rw [map_mul, h, cj]
      simp only [mk_mul_mk, F4.mk.injEq]
      decide

section Normalizer

variable (ρ : GL (Fin 3) F4 →* MulAut M)

theorem pow_three_of_scalars {z : SpecialLinearGroup (Fin 3) F4}
    (hz : z ∈ LinearFlag.scalars 3 F4) : z ^ 3 = 1 := by
  obtain ⟨c', hc', hzc⟩ := LinearFlag.mem_scalars.mp hz
  have h : ((z ^ 3 : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      ((1 : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hzc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
      ← Units.val_pow_eq_pow_val, hc', Units.val_one, map_one]
  exact Subtype.ext h

theorem mem_centralizer_of_proj {x P : MulAut M}
    {τ gp : SpecialLinearGroup (Fin 3) F4 → SpecialLinearGroup (Fin 3) F4}
    (hgp : ∀ g, slRep ρ (gp g) = x * slRep ρ g * x⁻¹)
    (hP : ∀ g, P * slRep ρ g * P⁻¹ = slRep ρ (τ g))
    (hrel : ∀ g, LinearFlag.proj 3 F4 (gp g) = LinearFlag.proj 3 F4 (τ g)) :
    P⁻¹ * x ∈ Subgroup.centralizer (img ρ : Set (MulAut M)) := by
  set ρ' := slRep ρ with hρ'
  have hw : ∀ g, ∃ z ∈ LinearFlag.scalars 3 F4,
      P⁻¹ * x * ρ' g * (P⁻¹ * x)⁻¹ = ρ' g * (P⁻¹ * ρ' z * P) := by
    intro g
    refine ⟨(τ g)⁻¹ * gp g, LinearFlag.proj_eq_proj_iff.mp (hrel g).symm, ?_⟩
    have h1 : ρ' (τ g) = P * ρ' g * P⁻¹ := (hP g).symm
    have h2 : x * ρ' g * x⁻¹ = ρ' (τ g) * ρ' ((τ g)⁻¹ * gp g) := by
      rw [← map_mul, mul_inv_cancel_left, hgp]
    calc P⁻¹ * x * ρ' g * (P⁻¹ * x)⁻¹ = P⁻¹ * (x * ρ' g * x⁻¹) * P := by group
      _ = P⁻¹ * (ρ' (τ g) * ρ' ((τ g)⁻¹ * gp g)) * P := by rw [h2]
      _ = P⁻¹ * (P * ρ' g * P⁻¹ * ρ' ((τ g)⁻¹ * gp g)) * P := by rw [h1]
      _ = ρ' g * (P⁻¹ * ρ' ((τ g)⁻¹ * gp g) * P) := by group
  have htr : ∀ t ∈ Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin 3) F4 → SpecialLinearGroup (Fin 3) F4),
      P⁻¹ * x * ρ' t * (P⁻¹ * x)⁻¹ = ρ' t := by
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [TransvectionStruct.toSpecialLinearGroup_mk]
    set t := SpecialLinearGroup.transvection hij c with ht
    obtain ⟨z, hz, he⟩ := hw t
    set w := P⁻¹ * ρ' z * P with hwdef
    have hw3 : w ^ 3 = 1 := by
      have e : w = P⁻¹ * ρ' z * P⁻¹⁻¹ := by rw [hwdef, inv_inv]
      rw [e, conj_pow, ← map_pow, pow_three_of_scalars hz, map_one, mul_one, mul_inv_cancel]
    have hwc : w * ρ' t = ρ' t * w := by
      have hm : ρ' t = P⁻¹ * ρ' (τ t) * P := by
        rw [← hP t]
        group
      have hzc : ρ' z * ρ' (τ t) = ρ' (τ t) * ρ' z := by
        rw [← map_mul, ← map_mul, commute_of_scalars hz (τ t)]
      calc w * ρ' t = P⁻¹ * (ρ' z * ρ' (τ t)) * P := by
            rw [hwdef, hm]
            group
        _ = P⁻¹ * (ρ' (τ t) * ρ' z) * P := by rw [hzc]
        _ = ρ' t * w := by
            rw [hwdef, hm]
            group
    have ht2 : t * t = 1 := CFSG.Quasithin.H.L3Nine.transvection_mul_self hij c
    have h1 : (P⁻¹ * x * ρ' t * (P⁻¹ * x)⁻¹) * (P⁻¹ * x * ρ' t * (P⁻¹ * x)⁻¹) = 1 := by
      calc (P⁻¹ * x * ρ' t * (P⁻¹ * x)⁻¹) * (P⁻¹ * x * ρ' t * (P⁻¹ * x)⁻¹) =
          P⁻¹ * x * ρ' (t * t) * (P⁻¹ * x)⁻¹ := by
            rw [map_mul]
            group
        _ = 1 := by
            rw [ht2, map_one]
            group
    rw [he] at h1
    have h4 : (ρ' t * w) * (ρ' t * w) = w * w := by
      calc (ρ' t * w) * (ρ' t * w) = ρ' t * (w * ρ' t) * w := by group
        _ = ρ' t * (ρ' t * w) * w := by rw [hwc]
        _ = ρ' (t * t) * (w * w) := by
            rw [map_mul]
            group
        _ = w * w := by rw [ht2, map_one, one_mul]
    have h3 : w * w = 1 := h4 ▸ h1
    have hw1 : w = 1 := by
      have e : w = w ^ 3 * (w * w)⁻¹ := by group
      rw [e, hw3, h3, inv_one, one_mul]
    rw [he, hw1, mul_one]
  have hfun : (MulAut.conj (P⁻¹ * x)).toMonoidHom.comp ρ' = ρ' :=
    MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 3)
        (K := F4)) fun t ht => htr t ht
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  have h := congrArg (fun F => F g) hfun
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  calc ρ' g * (P⁻¹ * x) = (P⁻¹ * x * ρ' g * (P⁻¹ * x)⁻¹) * (P⁻¹ * x) := by rw [h]
    _ = P⁻¹ * x * ρ' g := by group

theorem conj_slRep_rho (A : GL (Fin 3) F4) (g : SpecialLinearGroup (Fin 3) F4) :
    ρ A * slRep ρ g * (ρ A)⁻¹ =
      slRep ρ (CatalogueBHigherLinearAction.slConjugation 3 F4 A g) := by
  change _ = ρ (SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation 3 F4 A g))
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]
  rfl

theorem exists_eq_mul_of_mem_normalizer {f γ : MulAut M}
    (hf : ∀ g, ρ (frobGL g) = f * ρ g * f⁻¹) (hγ : ∀ g, ρ (grGL g) = γ * ρ g * γ⁻¹)
    (hnc : ∃ a b, slRep ρ a * slRep ρ b ≠ slRep ρ b * slRep ρ a)
    {R : Subgroup (MulAut M)} (hR : ∀ g, ρ g ∈ R) (hfR : f ∈ R) (hγR : γ ∈ R)
    {x : MulAut M} (hx : x ∈ Subgroup.normalizer (img ρ : Set (MulAut M))) :
    ∃ r ∈ R, ∃ c ∈ Subgroup.centralizer (img ρ : Set (MulAut M)), x = r * c := by
  classical
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (img ρ : Set (MulAut M)) := inv_mem hx
  have hmem : ∀ g, ∃ g', slRep ρ g' = x * slRep ρ g * x⁻¹ := fun g =>
    (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨g, rfl⟩
  choose gp hgp using hmem
  have hmem' : ∀ h, ∃ g, slRep ρ g = x⁻¹ * slRep ρ h * x := fun h => by
    have := (Subgroup.mem_normalizer_iff.mp hxinv (slRep ρ h)).mp ⟨h, rfl⟩
    rwa [inv_inv] at this
  let α' : SpecialLinearGroup (Fin 3) F4 →* LinearFlag.projectiveSL 3 F4 :=
    { toFun := fun g => LinearFlag.proj 3 F4 (gp g)
      map_one' := by
        rw [LinearFlag.proj_eq_one_iff]
        apply mem_scalars_of_slRep_eq_one ρ hnc
        rw [hgp, map_one, mul_one, mul_inv_cancel]
      map_mul' := fun g h => by
        rw [← map_mul, LinearFlag.proj_eq_proj_iff]
        apply mem_scalars_of_slRep_eq_one ρ hnc
        rw [map_mul, map_inv, map_mul, hgp, hgp, hgp, map_mul]
        group }
  have hker : LinearFlag.scalars 3 F4 ≤ α'.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    change LinearFlag.proj 3 F4 (gp g) = 1
    rw [LinearFlag.proj_eq_one_iff]
    apply mem_scalars_of_comm ρ hnc
    intro k
    obtain ⟨k', hk'⟩ := hmem' k
    have hgc : slRep ρ g * slRep ρ k' = slRep ρ k' * slRep ρ g := by
      rw [← map_mul, ← map_mul, commute_of_scalars hg k']
    have e : slRep ρ k = x * slRep ρ k' * x⁻¹ := by
      rw [hk']
      group
    rw [hgp, e]
    calc x * slRep ρ g * x⁻¹ * (x * slRep ρ k' * x⁻¹) =
        x * (slRep ρ g * slRep ρ k') * x⁻¹ := by group
      _ = x * (slRep ρ k' * slRep ρ g) * x⁻¹ := by rw [hgc]
      _ = x * slRep ρ k' * x⁻¹ * (x * slRep ρ g * x⁻¹) := by group
  let α := QuotientGroup.lift (LinearFlag.scalars 3 F4) α' hker
  have hαproj : ∀ g, α (LinearFlag.proj 3 F4 g) = LinearFlag.proj 3 F4 (gp g) := fun g => rfl
  have hαsurj : Function.Surjective α := by
    intro p
    obtain ⟨h, rfl⟩ := LinearFlag.proj_surjective 3 F4 p
    obtain ⟨g, hg⟩ := hmem' h
    refine ⟨LinearFlag.proj 3 F4 g, ?_⟩
    rw [hαproj, LinearFlag.proj_eq_proj_iff]
    apply mem_scalars_of_slRep_eq_one ρ hnc
    rw [map_mul, map_inv, hgp, hg]
    group
  have hαinj : Function.Injective α := Finite.injective_iff_surjective.mpr hαsurj
  obtain ⟨A, σ, ε, hε, hαe⟩ := (LinearFlag.automorphism_generation (K := F4) (n := 3) le_rfl).2
    (MulEquiv.ofBijective α ⟨hαinj, hαsurj⟩)
  have hrel0 : ∀ g, LinearFlag.proj 3 F4 (gp g) = (LinearFlag.conjAut 3 F4 A *
      LinearFlag.fieldAut 3 F4 σ * LinearFlag.dualAut 3 F4 ^ ε) (LinearFlag.proj 3 F4 g) :=
    fun g => by
      rw [← hαe]
      rfl
  set d := ρ w0GL * γ with hd
  have hdρ : ∀ g, d * slRep ρ g * d⁻¹ = slRep ρ (g⁻¹).transpose := fun g => by
    change d * ρ (SpecialLinearGroup.toGL g) * d⁻¹ = ρ (SpecialLinearGroup.toGL (g⁻¹).transpose)
    rw [toGL_dual, map_mul, map_mul, hγ, map_inv, hd]
    group
  have hfρ : ∀ g, f * slRep ρ g * f⁻¹ =
      slRep ρ (SpecialLinearGroup.map cjRing.toRingHom g) := fun g => by
    change f * ρ (SpecialLinearGroup.toGL g) * f⁻¹ =
      ρ (SpecialLinearGroup.toGL (SpecialLinearGroup.map cjRing.toRingHom g))
    rw [toGL_map_cj, hf]
  have hdR : d ∈ R := mul_mem (hR _) hγR
  have key : ∀ (P : MulAut M) (τ : SpecialLinearGroup (Fin 3) F4 → SpecialLinearGroup (Fin 3) F4),
      P ∈ R → (∀ g, P * slRep ρ g * P⁻¹ = slRep ρ (τ g)) →
      (∀ g, LinearFlag.proj 3 F4 (gp g) = LinearFlag.proj 3 F4 (τ g)) →
      ∃ r ∈ R, ∃ c ∈ Subgroup.centralizer (img ρ : Set (MulAut M)), x = r * c :=
    fun P τ hPR hP hrel => ⟨P, hPR, P⁻¹ * x, mem_centralizer_of_proj ρ hgp hP hrel, by group⟩
  have hconjA := conj_slRep_rho ρ A
  have hfld1 : LinearFlag.fieldAut 3 F4 (RingEquiv.refl F4) = 1 :=
    map_one (LinearFlag.fieldAut 3 F4)
  rcases ringEquiv_eq_refl_or_cj σ with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    refine key (ρ A) (fun g => CatalogueBHigherLinearAction.slConjugation 3 F4 A g) (hR A)
      hconjA fun g => ?_
    rw [hrel0, pow_zero, mul_one, MulAut.mul_apply, hfld1, MulAut.one_apply,
      LinearFlag.conjAut_proj]
  ·
    refine key (ρ A * d)
      (fun g => CatalogueBHigherLinearAction.slConjugation 3 F4 A (g⁻¹).transpose)
      (mul_mem (hR A) hdR) (fun g => ?_) fun g => ?_
    · rw [← hconjA, ← hdρ]
      group
    · rw [hrel0, pow_one, MulAut.mul_apply, MulAut.mul_apply, hfld1, MulAut.one_apply,
        LinearFlag.dualAut_proj, LinearFlag.conjAut_proj]
  ·
    refine key (ρ A * f)
      (fun g => CatalogueBHigherLinearAction.slConjugation 3 F4 A
        (SpecialLinearGroup.map cjRing.toRingHom g))
      (mul_mem (hR A) hfR) (fun g => ?_) fun g => ?_
    · rw [← hconjA, ← hfρ]
      group
    · rw [hrel0, pow_zero, mul_one, MulAut.mul_apply, LinearFlag.fieldAut_proj,
        LinearFlag.conjAut_proj]
  ·
    refine key (ρ A * f * d)
      (fun g => CatalogueBHigherLinearAction.slConjugation 3 F4 A
        (SpecialLinearGroup.map cjRing.toRingHom (g⁻¹).transpose))
      (mul_mem (mul_mem (hR A) hfR) hdR) (fun g => ?_) fun g => ?_
    · rw [← hconjA, ← hfρ, ← hdρ]
      group
    · rw [hrel0, pow_one, MulAut.mul_apply, MulAut.mul_apply, LinearFlag.dualAut_proj,
        LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj]

end Normalizer


section Model

variable (ρ : GL (Fin 3) F4 →* MulAut M)

theorem det_um (a b c : F4) : (um a b c).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [um]

theorem det_w0 : (w0 : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [w0]
  rfl

@[expose] def uSL (a b c : F4) : SpecialLinearGroup (Fin 3) F4 := ⟨um a b c, det_um a b c⟩

@[expose] def w0SL : SpecialLinearGroup (Fin 3) F4 := ⟨w0, det_w0⟩

theorem toGL_uSL (a b c : F4) : SpecialLinearGroup.toGL (uSL a b c) = uGL a b c := Units.ext rfl

theorem toGL_w0SL : SpecialLinearGroup.toGL w0SL = w0GL := Units.ext rfl

theorem slRep_uSL (a b c : F4) : slRep ρ (uSL a b c) = ρ (uGL a b c) := by
  rw [slRep, MonoidHom.comp_apply, toGL_uSL]

theorem slRep_w0SL : slRep ρ w0SL = ρ w0GL := by
  rw [slRep, MonoidHom.comp_apply, toGL_w0SL]

theorem mem_normalizer_of_conj {x : MulAut M}
    (h1 : ∀ k, ∃ k', x * slRep ρ k * x⁻¹ = slRep ρ k')
    (h2 : ∀ k, ∃ k', x⁻¹ * slRep ρ k * x = slRep ρ k') :
    x ∈ Subgroup.normalizer (img ρ : Set (MulAut M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := h1 k
    exact ⟨k', hk'.symm⟩
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk'⟩ := h2 k
    refine ⟨k', ?_⟩
    rw [← hk', hk]
    group

theorem rho_mem_normalizer (g : GL (Fin 3) F4) :
    ρ g ∈ Subgroup.normalizer (img ρ : Set (MulAut M)) := by
  refine mem_normalizer_of_conj ρ (fun k => ⟨_, conj_slRep_rho ρ g k⟩) fun k =>
    ⟨CatalogueBHigherLinearAction.slConjugation 3 F4 g⁻¹ k, ?_⟩
  rw [← conj_slRep_rho ρ g⁻¹ k, map_inv, inv_inv]

theorem frob_mem_normalizer {f : MulAut M} (hf : ∀ g, ρ (frobGL g) = f * ρ g * f⁻¹) :
    f ∈ Subgroup.normalizer (img ρ : Set (MulAut M)) := by
  have h1 : ∀ k, f * slRep ρ k * f⁻¹ = slRep ρ (SpecialLinearGroup.map cjRing.toRingHom k) :=
    fun k => by
      change f * ρ (SpecialLinearGroup.toGL k) * f⁻¹ =
        ρ (SpecialLinearGroup.toGL (SpecialLinearGroup.map cjRing.toRingHom k))
      rw [toGL_map_cj, hf]
  refine mem_normalizer_of_conj ρ (fun k => ⟨_, h1 k⟩) fun k => ⟨SpecialLinearGroup.map
    cjRing.toRingHom k, ?_⟩
  have h2 := h1 (SpecialLinearGroup.map cjRing.toRingHom k)
  have hk : SpecialLinearGroup.map cjRing.toRingHom (SpecialLinearGroup.map cjRing.toRingHom k) =
      k := by
    ext i j
    exact cj_cj _
  rw [hk] at h2
  rw [← h2]
  group

theorem gr_mem_normalizer {γ : MulAut M} (hγ : ∀ g, ρ (grGL g) = γ * ρ g * γ⁻¹) :
    γ ∈ Subgroup.normalizer (img ρ : Set (MulAut M)) := by
  have hgr : ∀ k : SpecialLinearGroup (Fin 3) F4, ρ (grGL (SpecialLinearGroup.toGL k)) =
      slRep ρ (CatalogueBHigherLinearAction.slConjugation 3 F4 w0GL⁻¹ (k⁻¹).transpose) := by
    intro k
    rw [← conj_slRep_rho]
    change ρ (grGL (SpecialLinearGroup.toGL k)) =
      ρ w0GL⁻¹ * ρ (SpecialLinearGroup.toGL (k⁻¹).transpose) * (ρ w0GL⁻¹)⁻¹
    rw [toGL_dual]
    simp only [map_mul, map_inv]
    group
  have h1 : ∀ k, γ * slRep ρ k * γ⁻¹ = slRep ρ
      (CatalogueBHigherLinearAction.slConjugation 3 F4 w0GL⁻¹ (k⁻¹).transpose) := fun k => by
    rw [← hgr, hγ]
    rfl
  refine mem_normalizer_of_conj ρ (fun k => ⟨_, h1 k⟩) fun k =>
    ⟨CatalogueBHigherLinearAction.slConjugation 3 F4 w0GL⁻¹ (k⁻¹).transpose, ?_⟩
  have hgg : ∀ g : GL (Fin 3) F4, γ⁻¹ * ρ g * γ = ρ (grGL g) := fun g => by
    have := hγ (grGL g)
    rw [show grGL (grGL g) = g from grU_grU g] at this
    rw [this]
    group
  change γ⁻¹ * ρ (SpecialLinearGroup.toGL k) * γ = _
  rw [hgg, hgr]

theorem mul_c22Hom_mem_normalizer {f γ : MulAut M} (hf : ∀ g, ρ (frobGL g) = f * ρ g * f⁻¹)
    (hγ : ∀ g, ρ (grGL g) = γ * ρ g * γ⁻¹) (hf2 : f * f = 1) (hγ2 : γ * γ = 1)
    (hfγ : f * γ = γ * f) (g : GL (Fin 3) F4) (a : C22) :
    ρ g * c22Hom f γ hf2 hγ2 hfγ a ∈ Subgroup.normalizer (img ρ : Set (MulAut M)) := by
  refine mul_mem (rho_mem_normalizer ρ g) ?_
  rw [c22Hom_apply]
  split_ifs
  · exact mul_mem (one_mem _) (one_mem _)
  · exact mul_mem (one_mem _) (gr_mem_normalizer ρ hγ)
  · exact mul_mem (frob_mem_normalizer ρ hf) (one_mem _)
  · exact mul_mem (frob_mem_normalizer ρ hf) (gr_mem_normalizer ρ hγ)

end Model

section Sylow

theorem eq_one_of_mem_centralizer [Finite M] {Γ P : Subgroup (MulAut M)} (hPΓ : P ≤ Γ)
    (hodd : Odd (Nat.card {w : M // w ≠ 1 ∧ (∀ p ∈ P, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ Γ, γ w = v} = ⊤}))
    {z : MulAut M} (hz : z ∈ Subgroup.centralizer (Γ : Set (MulAut M))) (hz2 : z * z = 1) :
    z = 1 := by
  classical
  have hzc : ∀ γ ∈ Γ, ∀ v, z (γ v) = γ (z v) := fun γ hγ v => by
    have h1 := congrArg (fun F : MulAut M => F v) (Subgroup.mem_centralizer_iff.mp hz γ hγ)
    simp only [MulAut.mul_apply] at h1
    exact h1.symm
  have hzz : ∀ v, z (z v) = v := fun v => by
    have h1 := congrArg (fun F : MulAut M => F v) hz2
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h1
  have hcl : ∀ w : M, Subgroup.closure {v | ∃ γ ∈ Γ, γ w = v} = ⊤ →
      Subgroup.closure {v | ∃ γ ∈ Γ, γ (z w) = v} = ⊤ := fun w hw => by
    have himg : {v | ∃ γ ∈ Γ, γ (z w) = v} = z '' {v | ∃ γ ∈ Γ, γ w = v} := by
      ext v
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ w, ⟨γ, hγ, rfl⟩, hzc γ hγ w⟩
      · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
        exact ⟨γ, hγ, (hzc γ hγ w).symm⟩
    have h := MonoidHom.map_closure z.toMonoidHom {v | ∃ γ ∈ Γ, γ w = v}
    rw [hw, MulEquiv.coe_toMonoidHom] at h
    rw [himg, ← h, Subgroup.map_top_of_surjective _ z.surjective]
  set S := {w : M // w ≠ 1 ∧ (∀ p ∈ P, p w = w) ∧
    Subgroup.closure {v | ∃ γ ∈ Γ, γ w = v} = ⊤} with hS
  have hmem : ∀ w : S, z w.1 ≠ 1 ∧ (∀ p ∈ P, p (z w.1) = z w.1) ∧
      Subgroup.closure {v | ∃ γ ∈ Γ, γ (z w.1) = v} = ⊤ := fun w => by
    obtain ⟨w, hw1, hwP, hwcl⟩ := w
    refine ⟨fun h => hw1 ?_, fun p hp => ?_, hcl w hwcl⟩
    · rw [← hzz w, h, map_one]
    · rw [← hzc p (hPΓ hp), hwP p hp]
  let f : S → S := fun w => ⟨z w.1, hmem w⟩
  have hf : Function.Involutive f := fun w => Subtype.ext (hzz w.1)
  have : Fintype S := Fintype.ofFinite S
  obtain ⟨w, hw⟩ : ∃ w : S, f w = w := by
    by_contra hno
    push Not at hno
    have hsq : (hf.toPerm f) ^ 2 = 1 := Equiv.ext fun w => by
      rw [sq, Equiv.Perm.mul_apply]
      exact hf w
    have hsupp : (hf.toPerm f).support = Finset.univ :=
      Finset.eq_univ_of_forall fun w => Equiv.Perm.mem_support.mpr (hno w)
    have h2 := Equiv.Perm.two_dvd_card_support hsq
    rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hfix : ∀ v ∈ {v | ∃ γ ∈ Γ, γ w.1 = v}, z v = v := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hzc γ hγ, show z w.1 = w.1 from congrArg Subtype.val hw]
  have hle : Subgroup.closure {v | ∃ γ ∈ Γ, γ w.1 = v} ≤
      {v | z v = v} := by
    refine (Subgroup.closure_le (K := ⟨⟨⟨{v | z v = v}, fun {a b} ha hb => ?_⟩, ?_⟩, ?_⟩)).2 hfix
    · change z (a * b) = a * b
      rw [map_mul, ha, hb]
    · change z 1 = 1
      exact map_one z
    · intro a ha
      change z a⁻¹ = a⁻¹
      rw [map_inv, ha]
  rw [w.2.2.2] at hle
  exact MulEquiv.ext fun v => hle (Subgroup.mem_top v)

theorem conj_mem_centralizer {G : Type*} [Group G] {S : Subgroup G} {n c : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : n⁻¹ * g * n ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) g).mp hg
    rwa [inv_inv] at this
  have h := Subgroup.mem_centralizer_iff.mp hc _ hg'
  calc g * (n * c * n⁻¹) = n * ((n⁻¹ * g * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * g * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * g := by group

theorem exists_sylow_le {G : Type*} [Group G] [Finite G] {N R C : Subgroup G} (hRN : R ≤ N)
    (hCN : C ≤ N) (hCnorm : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C)
    (hmul : ∀ x ∈ N, ∃ r ∈ R, ∃ c ∈ C, x = r * c) (hodd : Odd (Nat.card C)) :
    ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R' := R.subgroupOf N with hR'
  set C' := C.subgroupOf N with hC'
  have hCn : C'.Normal := ⟨fun c hc n => hCnorm n n.2 c hc⟩
  have hsup : R' ⊔ C' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨r, hr, c, hc, rfl⟩ := hmul x hx
    have hrN := hRN hr
    have hcN := hCN hc
    have e : (⟨r * c, hx⟩ : N) = ⟨r, hrN⟩ * ⟨c, hcN⟩ := rfl
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (show (⟨r, hrN⟩ : N) ∈ R' from hr))
      (Subgroup.mem_sup_right (show (⟨c, hcN⟩ : N) ∈ C' from hc))
  have h1 : C'.index = C'.relIndex R' := by
    rw [← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_right]
  have h2 := Subgroup.relIndex_mul_card (H := C') (K := R')
  have h3 := Subgroup.card_mul_index C'
  have h4 := Subgroup.card_mul_index R'
  have hCcard : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  have hidx : R'.index * Nat.card ↥(C' ⊓ R') = Nat.card C' := by
    have hpos : 0 < Nat.card R' := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card R' * (R'.index * Nat.card ↥(C' ⊓ R')) =
        (Nat.card R' * R'.index) * Nat.card ↥(C' ⊓ R') := by ring
      _ = (Nat.card C' * C'.index) * Nat.card ↥(C' ⊓ R') := by rw [h4, h3]
      _ = Nat.card C' * (C'.relIndex R' * Nat.card ↥(C' ⊓ R')) := by rw [h1]; ring
      _ = Nat.card R' * Nat.card C' := by rw [h2]; ring
  have hRodd : Odd R'.index := by
    rw [hCcard] at hidx
    exact Odd.of_dvd_nat hodd ⟨_, hidx.symm⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 R'))
  set T' := (T : Subgroup R').map R'.subtype with hT'
  have hTcard : Nat.card T' = Nat.card T :=
    Nat.card_congr ((T : Subgroup R').equivMapOfInjective _ R'.subtype_injective).symm.toEquiv
  have hfac : (Nat.card N).factorization 2 = (Nat.card R').factorization 2 := by
    rw [← Subgroup.card_mul_index R', Nat.factorization_mul Nat.card_pos.ne'
      (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hRodd ∘ even_iff_two_dvd.mpr),
      add_zero]
  have hTs : Nat.card T' = 2 ^ (Nat.card N).factorization 2 := by
    rw [hTcard, hfac]
    exact T.card_eq_multiplicity
  refine ⟨Sylow.ofCard T' hTs, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨t, -, rfl⟩ := hy
  exact t.2

theorem exists_conj_le_of_normalizer [Finite M] (ρ : GL (Fin 3) F4 →* MulAut M) {f γ : MulAut M}
    (hf : ∀ g, ρ (frobGL g) = f * ρ g * f⁻¹) (hγ : ∀ g, ρ (grGL g) = γ * ρ g * γ⁻¹)
    (hnc : ∃ a b, slRep ρ a * slRep ρ b ≠ slRep ρ b * slRep ρ a)
    {R : Subgroup (MulAut M)} (hR : ∀ g, ρ g ∈ R) (hfR : f ∈ R) (hγR : γ ∈ R)
    (hRN : R ≤ Subgroup.normalizer (img ρ : Set (MulAut M)))
    {P : Subgroup (MulAut M)} (hP : P ≤ img ρ)
    (hodd : Odd (Nat.card {w : M // w ≠ 1 ∧ (∀ p ∈ P, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ img ρ, γ w = v} = ⊤}))
    {A : Subgroup (MulAut M)} (hA : A ≤ Subgroup.normalizer (img ρ : Set (MulAut M)))
    (h2 : IsPGroup 2 A) :
    ∃ n ∈ Subgroup.normalizer (img ρ : Set (MulAut M)),
      A.map (MulAut.conj n).toMonoidHom ≤ R := by
  have : Finite (MulAut M) := MulEquiv.finite_left
  have hCN : Subgroup.centralizer (img ρ : Set (MulAut M)) ≤
      Subgroup.normalizer (img ρ : Set (MulAut M)) := Subgroup.centralizer_le_normalizer _
  have hCodd : Odd (Nat.card (Subgroup.centralizer (img ρ : Set (MulAut M)))) := by
    by_contra h
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
    have : Fintype (Subgroup.centralizer (img ρ : Set (MulAut M))) := Fintype.ofFinite _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 h
    have hz2 : (z : MulAut M) * z = 1 := by
      have h1 := pow_orderOf_eq_one z
      rw [hz, sq] at h1
      exact congrArg Subtype.val h1
    have hz1 : z = 1 := Subtype.ext (eq_one_of_mem_centralizer hP hodd z.2 hz2)
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨P₀, hP₀⟩ := exists_sylow_le hRN hCN (fun n hn c hc => conj_mem_centralizer hn hc)
    (fun x hx => exists_eq_mul_of_mem_normalizer ρ hf hγ hnc hR hfR hγR hx) hCodd
  obtain ⟨g, hg⟩ := L34M.exists_conj_le
    (Subgroup.normalizer (img ρ : Set (MulAut M))).subtype P₀ (B := A)
    (by rwa [Subgroup.range_subtype]) h2
  exact ⟨(g : MulAut M)⁻¹, inv_mem g.2, hg.trans hP₀⟩

end Sylow

end CFSG.Quasithin.H13.Ch9.L34N
