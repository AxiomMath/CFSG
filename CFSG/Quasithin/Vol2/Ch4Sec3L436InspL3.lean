module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Par

public section

namespace CFSG.Quasithin.H13.Ch4.L3M

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat
  CFSG.Quasithin.H13.NQCat.SL3
open CFSG.Quasithin (perfectCore perfectCore_le)

variable {F : Type} [Field F]

theorem trace_transvection {a b : Fin 3} (hab : a ≠ b) (t : F) :
    Matrix.trace (transvection a b t) = 3 := by
  rw [transvection, Matrix.trace_add, Matrix.trace_one, Matrix.trace_single_eq_of_ne _ _ _ hab]
  simp

theorem eq_of_proj_eq {g h : SpecialLinearGroup (Fin 3) F} (hp : proj 3 F h = proj 3 F g)
    (htr : Matrix.trace (h : Matrix (Fin 3) (Fin 3) F) =
      Matrix.trace (g : Matrix (Fin 3) (Fin 3) F))
    (h0 : Matrix.trace (g : Matrix (Fin 3) (Fin 3) F) ≠ 0) :
    (h : Matrix (Fin 3) (Fin 3) F) = g := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hp)
  have hg : (g : Matrix (Fin 3) (Fin 3) F) =
      (h : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (c : F) := by
    have e : (g : Matrix (Fin 3) (Fin 3) F) =
        ((h * (h⁻¹ * g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [mul_inv_cancel_left]
    rw [e]
    show (h : Matrix (Fin 3) (Fin 3) F) *
      ((h⁻¹ * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [hc]
  have htr' : Matrix.trace (g : Matrix (Fin 3) (Fin 3) F) =
      (c : F) * Matrix.trace (g : Matrix (Fin 3) (Fin 3) F) := by
    conv_lhs => rw [hg]
    rw [← htr]
    simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, scalar_apply, diagonal_apply]
    ring
  have hc1 : (c : F) = 1 := mul_right_cancel₀ h0 (htr'.symm.trans (one_mul _).symm)
  rw [hg, hc1, map_one, Matrix.mul_one]

theorem transvection_map {a b : Fin 3} (σ : F ≃+* F) (t : F) :
    (transvection a b t).map σ = transvection a b (σ t) := by
  ext i k
  simp only [map_apply, transvection, Matrix.add_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp_all

theorem coe_tv_inv_transpose {a b : Fin 3} (hab : a ≠ b) (t : F) :
    (((tv hab t)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
      transvection b a (-t) := by
  have hinv : (tv hab t)⁻¹ = tv hab (-t) := by
    rw [inv_eq_iff_mul_eq_one, tv_mul, add_neg_cancel]
    apply Subtype.ext
    rw [coe_tv]
    simp [transvection]
  rw [hinv, coe_tv]
  ext i k
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases k <;>
    simp_all [transvection]

theorem aut_proj_zero (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) :
    (LinearFlag.conjAut 3 F A * LinearFlag.fieldAut 3 F σ * LinearFlag.dualAut 3 F ^ 0)
        (proj 3 F g) =
      proj 3 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        3 F A (SpecialLinearGroup.map σ.toRingHom g)) := by
  rw [pow_zero, mul_one, MulAut.mul_apply, LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj]

theorem aut_proj_one (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) :
    (LinearFlag.conjAut 3 F A * LinearFlag.fieldAut 3 F σ * LinearFlag.dualAut 3 F ^ 1)
        (proj 3 F g) =
      proj 3 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        3 F A (SpecialLinearGroup.map σ.toRingHom (g⁻¹).transpose)) := by
  rw [pow_one, MulAut.mul_apply, MulAut.mul_apply, LinearFlag.dualAut_proj,
    LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj]

theorem three_ne_zero [CharP F 2] : (3 : F) ≠ 0 := by
  have h : (3 : F) = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  rw [h]
  exact one_ne_zero

theorem conj_eq_of_proj [CharP F 2] (A : GL (Fin 3) F) {a b c d : Fin 3} (hab : a ≠ b)
    (hcd : c ≠ d) (s t : F) {x : SpecialLinearGroup (Fin 3) F}
    (hx : (x : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * transvection c d s * ((A⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F))
    (hp : proj 3 F x = proj 3 F (tv hab t)) :
    (A : Matrix (Fin 3) (Fin 3) F) * transvection c d s =
      transvection a b t * (A : Matrix (Fin 3) (Fin 3) F) := by
  have htr : Matrix.trace (x : Matrix (Fin 3) (Fin 3) F) =
      Matrix.trace ((tv hab t : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hx, coe_tv, trace_transvection hab, Matrix.trace_mul_cycle, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, trace_transvection hcd]
  have h0 : Matrix.trace ((tv hab t : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    rw [coe_tv, trace_transvection hab]
    exact three_ne_zero
  have he := eq_of_proj_eq hp htr h0
  rw [hx, coe_tv] at he
  rw [← he, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one]

theorem embSL_lo2_zero :
    embSL 0 (lo2 (1 : F)) = tv (show (2 : Fin 3) ≠ 1 by decide) 1 := by
  apply Subtype.ext
  change embMat 0 ((lo2 (1 : F) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    transvection 2 1 1
  ext i k
  fin_cases i <;> fin_cases k <;> simp [embMat, lo2, transvection]

theorem embSL_lo2_one :
    embSL 1 (lo2 (1 : F)) = tv (show (1 : Fin 3) ≠ 0 by decide) 1 := by
  apply Subtype.ext
  change embMat 1 ((lo2 (1 : F) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    transvection 1 0 1
  ext i k
  fin_cases i <;> fin_cases k <;> simp [embMat, lo2, transvection]

theorem aut_eq_one_of_fixes [Finite F] [CharP F 2] (hK4 : ∃ s : Finset F, s.card = 4) (j : Fin 2)
    (φ : MulAut (projectiveSL 3 F))
    (hφ : ∀ g ∈ perfectCore (Q3 F j), φ (proj 3 F g) = proj 3 F g) : φ = 1 := by
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    (LinearFlag.automorphism_generation (n := 3) (K := F) (by norm_num)).2 φ
  have hU : ∀ {a b : Fin 3} (hab : a < b) (t : F), tv hab.ne t ∈ perfectCore (Q3 F j) :=
    fun hab t => unitriangular_le_perfectCore hK4 j (tv_mem_unitriangular hab t)
  have hdet : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det A).isUnit
    exact this.ne_zero
  interval_cases ε
  ·
    have key : ∀ {a b : Fin 3} (hab : a ≠ b) (t : F), tv hab t ∈ perfectCore (Q3 F j) →
        (A : Matrix (Fin 3) (Fin 3) F) * transvection a b (σ t) =
          transvection a b t * (A : Matrix (Fin 3) (Fin 3) F) := by
      intro a b hab t ht
      have h := hφ _ ht
      rw [aut_proj_zero] at h
      refine conj_eq_of_proj A hab hab (σ t) t ?_ h
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        coe_tv]
      rw [show (transvection a b t).map σ.toRingHom = transvection a b (σ t) from
        transvection_map σ t]
    have h01 := key (show (0 : Fin 3) ≠ 1 by decide) 1 (hU (show (0 : Fin 3) < 1 by decide) 1)
    have h12 := key (show (1 : Fin 3) ≠ 2 by decide) 1 (hU (show (1 : Fin 3) < 2 by decide) 1)
    rw [map_one] at h01 h12
    set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hM
    have m10 : M 1 0 = 0 := by
      have := congrFun₂ h01 1 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply] using this
    have m20 : M 2 0 = 0 := by
      have := congrFun₂ h01 2 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply] using this
    have m00 : M 0 0 = M 1 1 := by
      have := congrFun₂ h01 0 1
      simp [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply] at this
      linear_combination this
    have m12 : M 1 2 = 0 := by
      have := congrFun₂ h01 0 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply] using this.symm
    have m01 : M 0 1 = 0 := by
      have := congrFun₂ h12 0 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply] using this
    have m21 : M 2 1 = 0 := by
      have := congrFun₂ h12 2 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply] using this
    have m11 : M 1 1 = M 2 2 := by
      have := congrFun₂ h12 1 2
      simp [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply] at this
      linear_combination this
    have hdet' := hdet
    rw [Matrix.det_fin_three] at hdet'
    simp only [m10, m20, m12, m01, m21, mul_zero, zero_mul, sub_zero, add_zero] at hdet'
    have hm00 : M 0 0 ≠ 0 := fun h => hdet' (by rw [h, zero_mul, zero_mul])
    have hσ : ∀ t : F, σ t = t := by
      intro t
      have h := congrFun₂ (key (show (0 : Fin 3) ≠ 1 by decide) t
        (hU (show (0 : Fin 3) < 1 by decide) t)) 0 1
      simp [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, m01] at h
      rw [← m00] at h
      exact mul_left_cancel₀ hm00 (h.trans (mul_comm t _))
    have m02 : M 0 2 = 0 := by
      fin_cases j
      · have hL : tv (show (2 : Fin 3) ≠ 1 by decide) (1 : F) ∈ perfectCore (Q3 F 0) := by
          rw [← embSL_lo2_zero]
          exact embSL_mem_perfectCore hK4 0 _
        have h := congrFun₂ (key (show (2 : Fin 3) ≠ 1 by decide) 1 hL) 0 1
        rw [map_one] at h
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using h
      · have hL : tv (show (1 : Fin 3) ≠ 0 by decide) (1 : F) ∈ perfectCore (Q3 F 1) := by
          rw [← embSL_lo2_one]
          exact embSL_mem_perfectCore hK4 1 _
        have h := congrFun₂ (key (show (1 : Fin 3) ≠ 0 by decide) 1 hL) 1 2
        rw [map_one] at h
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using h
    have hMs : M = scalar (Fin 3) (M 0 0) := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [m10, m20, m12, m01, m21, m02, m00, m11]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [aut_proj_zero, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    have hgσ : (g : Matrix (Fin 3) (Fin 3) F).map σ.toRingHom = g := by
      ext i k
      simp [hσ]
    rw [hgσ, ← hM, hMs,
      (scalar_commute (M 0 0) (fun _ => Commute.all _ _) (g : Matrix (Fin 3) (Fin 3) F)).eq,
      ← hMs, hM, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  ·
    exfalso
    have key : ∀ {a b : Fin 3} (hab : a ≠ b), tv hab 1 ∈ perfectCore (Q3 F j) →
        (A : Matrix (Fin 3) (Fin 3) F) * transvection b a 1 =
          transvection a b 1 * (A : Matrix (Fin 3) (Fin 3) F) := by
      intro a b hab ht
      have h := hφ _ ht
      rw [aut_proj_one] at h
      have h1 : σ (-1) = 1 := by rw [map_neg, map_one, CharTwo.neg_eq]
      have := conj_eq_of_proj A hab hab.symm (σ (-1)) 1 (x := _) ?_ h
      · rwa [h1] at this
      · rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Matrix.SpecialLinearGroup.coe_transpose, coe_tv_inv_transpose hab]
        rw [show (transvection b a (-1 : F)).map σ.toRingHom = transvection b a (σ (-1)) from
          transvection_map σ (-1)]
    set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hM
    fin_cases j
    · have h1 := key (show (0 : Fin 3) ≠ 1 by decide) (hU (show (0 : Fin 3) < 1 by decide) 1)
      have h2 := key (show (0 : Fin 3) ≠ 2 by decide) (hU (show (0 : Fin 3) < 2 by decide) 1)
      have m11 : M 1 1 = 0 := by
        have := congrFun₂ h1 1 0
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using this
      have m21 : M 2 1 = 0 := by
        have := congrFun₂ h1 2 0
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using this
      have m12 : M 1 2 = 0 := by
        have := congrFun₂ h2 1 0
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using this
      have m22 : M 2 2 = 0 := by
        have := congrFun₂ h2 2 0
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using this
      apply hdet
      rw [Matrix.det_fin_three, m11, m21, m12, m22]
      ring
    · have h1 := key (show (0 : Fin 3) ≠ 2 by decide) (hU (show (0 : Fin 3) < 2 by decide) 1)
      have h2 := key (show (1 : Fin 3) ≠ 2 by decide) (hU (show (1 : Fin 3) < 2 by decide) 1)
      have m12 : M 1 2 = 0 := by
        have := congrFun₂ h1 1 0
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using this
      have m22 : M 2 2 = 0 := by
        have := congrFun₂ h1 2 0
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using this
      have m02 : M 0 2 = 0 := by
        have := congrFun₂ h2 0 1
        simpa [Matrix.mul_apply, Fin.sum_univ_three, transvection, single_apply, ← hM] using this
      apply hdet
      rw [Matrix.det_fin_three, m12, m22, m02]
      ring

section Transport

variable {G : Type} [Group G]

@[expose] noncomputable def conjOn (K : Subgroup G) {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) : MulAut ↥K :=
  ((MulAut.conj r).subgroupMap K).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hr))

theorem coe_conjOn (K : Subgroup G) {r : G} (hr : r ∈ Subgroup.normalizer (K : Set G))
    (x : ↥K) : ((conjOn K hr x : ↥K) : G) = r * x * r⁻¹ :=
  rfl

@[expose] noncomputable def autCenter {X : Type*} [Group X] (α : MulAut X) :
    MulAut (X ⧸ Subgroup.center X) :=
  QuotientGroup.congr _ _ α (Subgroup.characteristic_iff_map_eq.mp inferInstance α)

theorem autCenter_mk {X : Type*} [Group X] (α : MulAut X) (x : X) :
    autCenter α (x : X ⧸ Subgroup.center X) = (α x : X ⧸ Subgroup.center X) :=
  rfl

theorem eq_of_autCenter_eq_one {X : Type*} [Group X] (hX : commutator X = ⊤) (α : MulAut X)
    (h : autCenter α = 1) (x : X) : α x = x := by
  have hc : ∀ y : X, y⁻¹ * α y ∈ Subgroup.center X := fun y => by
    have := congrArg (fun β : MulAut (X ⧸ Subgroup.center X) =>
      β (y : X ⧸ Subgroup.center X)) h
    simp only [autCenter_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.mp this.symm
  let f : X →* ↥(Subgroup.center X) :=
    { toFun := fun y => ⟨y⁻¹ * α y, hc y⟩
      map_one' := by
        apply Subtype.ext
        change (1 : X)⁻¹ * α 1 = 1
        rw [map_one, inv_one, one_mul]
      map_mul' := fun a b => by
        apply Subtype.ext
        change (a * b)⁻¹ * α (a * b) = a⁻¹ * α a * (b⁻¹ * α b)
        have hb := Subgroup.mem_center_iff.mp (hc a) b⁻¹
        calc (a * b)⁻¹ * α (a * b) = b⁻¹ * (a⁻¹ * α a) * α b := by
              rw [map_mul]; group
          _ = a⁻¹ * α a * b⁻¹ * α b := by rw [hb]
          _ = a⁻¹ * α a * (b⁻¹ * α b) := by group }
  have hker : commutator X ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hX] at hker
  have h1 : f x = 1 := hker (Subgroup.mem_top x)
  have h2 : x⁻¹ * α x = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.mp h2).symm

theorem isSylowTwoOf_map_top {X Y : Type*} [Group X] [Group Y] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {f : X →* Y} (hf : Function.Surjective f) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T.map f) ⊤ := by
  refine ⟨le_top, hT.2.1.map f, fun hd => hT.2.2 ?_⟩
  have h1 : ((T.map f).subgroupOf ⊤).index = (T.map f).index := Subgroup.relIndex_top_right _
  have h2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
  rw [h1] at hd
  rw [h2]
  exact hd.trans (Subgroup.index_map_dvd T hf)

theorem exists_card_four {F : Type} [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ∃ s : Finset F, s.card = 4 := by
  have : Fintype F := Fintype.ofFinite F
  have h4 : 4 ≤ (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  exact ⟨s, hs⟩

end Transport

end CFSG.Quasithin.H13.Ch4.L3M

namespace CFSG.Quasithin.H13.Ch4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.H13.NQCat.SL3 L3M
open CFSG.Quasithin (perfectCore map_perfectCore)

theorem insp436L3_holds :
    ∀ (G : Type) [Group G] [Finite G] (K P R₀ : Subgroup G) (n : ℕ), 2 ≤ n →
      CFSG.Open.IsQuasisimple ↥K → IsPSL 3 2 n (↥K ⧸ Subgroup.center ↥K) → IsMaxParabolic2 K P →
      R₀ ≤ Subgroup.normalizer (K : Set G) → R₀ ≤ Subgroup.centralizer (perfectCore P : Set G) →
      R₀ ≤ Subgroup.centralizer (K : Set G) := by
  intro G _ _ K P R₀ n hn hKq hL3 hP hR₀N hR₀P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Subgroup ↥K := P.comap K.subtype with hP₀
  have hPK : P ≤ K := hP.1.1
  have hP₀K : P₀.map K.subtype = P := by
    rw [hP₀, Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])]
  have hP₀max : IsMaxParabolic2 (⊤ : Subgroup ↥K) P₀ :=
    L436.isMaxParabolic2_comap K.subtype K.subtype_injective K.range_subtype.symm hP
  obtain ⟨S₁, hS₁, hNS₁, hPcov⟩ :=
    CFSG.Quasithin.Lie2Parabolic.exists_sylow_of_isMaxParabolic2 hP₀max
  set q : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hSb : CFSG.QuasithinUnique.IsSylowTwoOf (S₁.map q) ⊤ := isSylowTwoOf_map_top hS₁ hqs
  obtain ⟨F, _, _, _, φ, hcard, -, hres, -⟩ := even_rank_two_residual_linear hL3 hSb
  have hker : q.ker ≤ P₀ := by
    rw [hq, QuotientGroup.ker_mk']
    exact (Subgroup.center_le_normalizer _).trans hNS₁
  have hcov : P₀.map q ⋖ ⊤ := by
    rw [← Subgroup.map_top_of_surjective q hqs]
    exact covBy_map_of_ker_le hqs hker hPcov
  have hSP : S₁.map q ≤ P₀.map q := Subgroup.map_mono (Subgroup.le_normalizer.trans hNS₁)
  obtain ⟨j, hj⟩ := (hres.2.2.1 _ hSP).mp hcov
  have hK4 := exists_card_four hn hcard
  intro r hr
  set ψ : MulAut ↥K := conjOn K (hR₀N hr) with hψ
  have hfix : ∀ x ∈ perfectCore P₀, ψ x = x := by
    intro x hx
    have hxP : (x : G) ∈ perfectCore P := by
      rw [← hP₀K, ← map_perfectCore]
      exact Subgroup.mem_map_of_mem _ hx
    apply Subtype.ext
    rw [hψ, coe_conjOn, ← Subgroup.mem_centralizer_iff.mp (hR₀P hr) _ hxP, mul_inv_cancel_right]
  set φ' : MulAut (projectiveSL 3 F) := (φ.symm.trans (autCenter ψ)).trans φ with hφ'
  have hφ'fix : ∀ g ∈ perfectCore (Q3 F j), φ' (proj 3 F g) = proj 3 F g := by
    intro g hg
    have hg1 : φ.symm (proj 3 F g) ∈ (perfectCore P₀).map q := by
      rw [map_perfectCore, hj, ← map_perfectCore]
      refine Subgroup.mem_map_of_mem _ ?_
      change proj 3 F g ∈ perfectCore ((Q3 F j).map (proj 3 F))
      rw [← map_perfectCore]
      exact Subgroup.mem_map_of_mem _ hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg1
    have h1 : autCenter ψ (φ.symm (proj 3 F g)) = φ.symm (proj 3 F g) := by
      rw [← hxg, hq, QuotientGroup.mk'_apply, autCenter_mk, hfix x hx]
    rw [hφ', MulEquiv.trans_apply, MulEquiv.trans_apply, h1, MulEquiv.apply_symm_apply]
  have hφ'1 := aut_eq_one_of_fixes hK4 j φ' hφ'fix
  have hψ1 : autCenter ψ = 1 := by
    ext y
    have h := congrArg (fun β : MulAut (projectiveSL 3 F) => β (φ y)) hφ'1
    simp only [hφ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h
    rw [MulAut.one_apply]
    exact φ.injective h
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h := congrArg Subtype.val (eq_of_autCenter_eq_one hKq.1 ψ hψ1 ⟨k, hk⟩)
  rw [hψ, coe_conjOn] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

end CFSG.Quasithin.H13.Ch4
