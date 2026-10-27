module

public import CFSG.RankThree.PartOne.KFOUT3.Root
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open scoped commutatorElement

section Abstract

variable {F : Type} [Field F] {n : ℕ}

section Fin

variable [Finite F]

theorem exists_third (hn : 3 ≤ n) (a b : Fin n) : ∃ k : Fin n, k ≠ a ∧ k ≠ b := by
  by_cases h0 : a.val ≠ 0 ∧ b.val ≠ 0
  · exact ⟨⟨0, by omega⟩, fun e => h0.1 (by rw [← e]), fun e => h0.2 (by rw [← e])⟩
  · by_cases h1 : a.val ≠ 1 ∧ b.val ≠ 1
    · exact ⟨⟨1, by omega⟩, fun e => h1.1 (by rw [← e]), fun e => h1.2 (by rw [← e])⟩
    · refine ⟨⟨2, by omega⟩, fun e => ?_, fun e => ?_⟩
      · have := congrArg Fin.val e
        simp only at this
        omega
      · have := congrArg Fin.val e
        simp only at this
        omega

theorem exists_phi_d (hn : 3 ≤ n) (f : ∀ i j : Fin n, i ≠ j → F → F)
    (hadd : ∀ i j (h : i ≠ j) s s', f i j h (s + s') = f i j h s + f i j h s')
    (hinj : ∀ i j (h : i ≠ j), Function.Injective (f i j h))
    (hmul : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s t,
      f i k hik (s * t) = f i j hij s * f j k hjk t) :
    ∃ (φ : F ≃+* F) (d : Fin n → Fˣ), ∀ i j (h : i ≠ j) s,
      f i j h s = (d i : F) * φ s * (((d j)⁻¹ : Fˣ) : F) := by
  have f_zero : ∀ i j (h : i ≠ j), f i j h 0 = 0 := fun i j h => by
    have := hadd i j h 0 0
    simpa using this
  have c_ne : ∀ i j (h : i ≠ j), f i j h 1 ≠ 0 := fun i j h e =>
    one_ne_zero (hinj i j h (e.trans (f_zero i j h).symm))
  have hA : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s,
      f i k hik s = f i j hij s * f j k hjk 1 := fun i j k hij hjk hik s => by
    simpa using hmul i j k hij hjk hik s 1
  have hB : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) t,
      f i k hik t = f i j hij 1 * f j k hjk t := fun i j k hij hjk hik t => by
    simpa using hmul i j k hij hjk hik 1 t
  have hC : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      f i k hik 1 = f i j hij 1 * f j k hjk 1 := fun i j k hij hjk hik => by
    simpa using hmul i j k hij hjk hik 1 1
  let ψ : ∀ i j : Fin n, i ≠ j → F → F := fun i j h s => f i j h s / f i j h 1
  have Ψ1 : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s,
      ψ i j hij s = ψ i k hik s := by
    intro i j k hij hjk hik s
    simp only [ψ]
    rw [hA i j k hij hjk hik s, hC i j k hij hjk hik]
    have h1 := c_ne i j hij
    have h2 := c_ne j k hjk
    field_simp
  have Ψ2 : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) t,
      ψ i k hik t = ψ j k hjk t := by
    intro i j k hij hjk hik t
    simp only [ψ]
    rw [hB i j k hij hjk hik t, hC i j k hij hjk hik]
    have h1 := c_ne i j hij
    have h2 := c_ne j k hjk
    field_simp
  have move2 : ∀ i j k (hij : i ≠ j) (hik : i ≠ k) s, ψ i j hij s = ψ i k hik s := by
    intro i j k hij hik s
    by_cases hjk : j = k
    · subst hjk
      rfl
    · exact Ψ1 i j k hij hjk hik s
  have move1 : ∀ i l k (hik : i ≠ k) (hlk : l ≠ k) s, ψ i k hik s = ψ l k hlk s := by
    intro i l k hik hlk s
    by_cases hil : i = l
    · subst hil
      rfl
    · exact Ψ2 i l k hil hlk hik s
  have sym : ∀ a b (hab : a ≠ b) s, ψ a b hab s = ψ b a hab.symm s := by
    intro a b hab s
    obtain ⟨k, hka, hkb⟩ := exists_third hn a b
    calc ψ a b hab s = ψ a k hka.symm s := Ψ1 a b k hab hkb.symm hka.symm s
      _ = ψ b k hkb.symm s := Ψ2 a b k hab hkb.symm hka.symm s
      _ = ψ b a hab.symm s := Ψ1 b k a hkb.symm hka hab.symm s
  have hall : ∀ a b (hab : a ≠ b) c d (hcd : c ≠ d) s, ψ a b hab s = ψ c d hcd s := by
    intro a b hab c d hcd s
    by_cases had : a = d
    · subst had
      calc ψ a b hab s = ψ a c hcd.symm s := move2 a b c hab hcd.symm s
        _ = ψ c a hcd s := sym a c hcd.symm s
    · calc ψ a b hab s = ψ a d had s := move2 a b d hab had s
        _ = ψ c d hcd s := move1 a c d had hcd s
  let r1 : Fin n := ⟨0, by omega⟩
  let r2 : Fin n := ⟨1, by omega⟩
  let r3 : Fin n := ⟨2, by omega⟩
  have h12 : r1 ≠ r2 := fun e => by have := congrArg Fin.val e; simp [r1, r2] at this
  have h23 : r2 ≠ r3 := fun e => by have := congrArg Fin.val e; simp [r2, r3] at this
  have h13 : r1 ≠ r3 := fun e => by have := congrArg Fin.val e; simp [r1, r3] at this
  let φf : F → F := ψ r1 r2 h12
  have φf_eq : ∀ i j (h : i ≠ j) s, ψ i j h s = φf s := fun i j h s => hall i j h r1 r2 h12 s
  have φf_one : φf 1 = 1 := div_self (c_ne r1 r2 h12)
  have φf_add : ∀ s s', φf (s + s') = φf s + φf s' := by
    intro s s'
    simp only [φf, ψ]
    rw [hadd, add_div]
  have φf_zero : φf 0 = 0 := by
    have := φf_add 0 0
    simpa using this
  have φf_mul : ∀ s t, φf (s * t) = φf s * φf t := by
    intro s t
    have e1 : ψ r1 r3 h13 (s * t) = ψ r1 r2 h12 s * ψ r2 r3 h23 t := by
      simp only [ψ]
      rw [hmul r1 r2 r3 h12 h23 h13 s t, hC r1 r2 r3 h12 h23 h13]
      have := c_ne r1 r2 h12
      have := c_ne r2 r3 h23
      field_simp
    rw [φf_eq r1 r3 h13, φf_eq r2 r3 h23] at e1
    exact e1
  have φf_inj : Function.Injective φf := by
    intro s s' h
    exact hinj r1 r2 h12 ((div_left_inj' (c_ne r1 r2 h12)).mp h)
  let φr : F →+* F :=
    { toFun := φf, map_one' := φf_one, map_mul' := φf_mul, map_zero' := φf_zero,
      map_add' := φf_add }
  let φ : F ≃+* F := RingEquiv.ofBijective φr ⟨φf_inj, Finite.injective_iff_surjective.mp φf_inj⟩
  have hφ : ∀ s, φ s = φf s := fun s => rfl
  let cc : Fin n → Fin n → F := fun i j => if h : i = j then 1 else f i j h 1
  have cc_ne : ∀ i j, cc i j ≠ 0 := by
    intro i j
    by_cases h : i = j
    · simp [cc, h]
    · simp only [cc, h, dite_false]
      exact c_ne i j h
  have cc_of_ne : ∀ i j (h : i ≠ j), cc i j = f i j h 1 := by
    intro i j h
    simp [cc, h]
  have cc_self : ∀ i, cc i i = 1 := by
    intro i
    simp [cc]
  have hkey : ∀ i j, cc i j = cc r1 j / cc r1 i := by
    intro i j
    by_cases hij : i = j
    · rw [hij, cc_self, div_self (cc_ne r1 j)]
    by_cases hir : i = r1
    · rw [hir, cc_self, div_one]
    by_cases hjr : j = r1
    · rw [hjr, cc_self]
      obtain ⟨k, hki, hkr⟩ := exists_third hn i r1
      have e1 := hC i r1 k hir hkr.symm hki.symm
      have e2 := hC r1 i k (Ne.symm hir) hki.symm hkr.symm
      rw [cc_of_ne i r1 hir, cc_of_ne r1 i (Ne.symm hir)]
      rw [e2] at e1
      have hP := c_ne i k hki.symm
      have hab : f i r1 hir 1 * f r1 i (Ne.symm hir) 1 = 1 := by
        apply mul_right_cancel₀ hP
        linear_combination (-1 : F) * e1
      exact eq_one_div_of_mul_eq_one_left hab
    · rw [cc_of_ne i j hij, cc_of_ne r1 j (Ne.symm hjr), cc_of_ne r1 i (Ne.symm hir)]
      have e := hC r1 i j (Ne.symm hir) hij (Ne.symm hjr)
      have h2 := c_ne r1 i (Ne.symm hir)
      field_simp
      rw [e]
      ring
  refine ⟨φ, fun i => Units.mk0 (cc r1 i)⁻¹ (inv_ne_zero (cc_ne r1 i)), ?_⟩
  intro i j h s
  have hf : f i j h s = f i j h 1 * ψ i j h s := by
    simp only [ψ]
    field_simp [c_ne i j h]
  rw [hf, φf_eq i j h s, ← hφ, ← cc_of_ne i j h, hkey i j]
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val, inv_inv]
  field_simp


end Fin

end Abstract

section Std

variable {K : Type} [Field K]

@[expose] def slConj (G : GL (Fin 3) K) : SL3 K →* SL3 K where
  toFun b := ⟨(G : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K) *
      ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), by
    rw [Matrix.det_mul, Matrix.det_mul]
    have h1 : (G : Matrix (Fin 3) (Fin 3) K).det *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [b.det_coe, mul_one, h1]⟩
  map_one' := by
    apply Subtype.ext
    show (G : Matrix (Fin 3) (Fin 3) K) * (1 : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' a b := by
    apply Subtype.ext
    show (G : Matrix (Fin 3) (Fin 3) K) * ((a : Matrix (Fin 3) (Fin 3) K) *
          (b : Matrix (Fin 3) (Fin 3) K)) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((G : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) *
          ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((G : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K) *
          ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    have hGG : ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (G : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (G : Matrix (Fin 3) (Fin 3) K) * ((a : Matrix (Fin 3) (Fin 3) K) *
            (b : Matrix (Fin 3) (Fin 3) K)) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = (G : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) * 1 *
            (b : Matrix (Fin 3) (Fin 3) K) *
          ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          simp [Matrix.mul_assoc]
      _ = _ := by rw [← hGG]; simp only [Matrix.mul_assoc]

theorem coe_slConj (G : GL (Fin 3) K) (x : SL3 K) :
    ((slConj G x : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

@[expose] noncomputable def stdHom (G : GL (Fin 3) K) (σ : K ≃+* K) : SL3 K →* SL3 K :=
  (slConj G).comp (Matrix.SpecialLinearGroup.map σ.toRingHom)

theorem coe_stdHom (G : GL (Fin 3) K) (σ : K ≃+* K) (x : SL3 K) :
    ((stdHom G σ x : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K).map σ *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  simp only [stdHom, MonoidHom.comp_apply, coe_slConj, Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

theorem diagU_inv' (d : Fin 3 → Kˣ) : (KFU.diagU d : GL (Fin 3) K)⁻¹ = KFU.diagU d⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [KFU.diagU_mul, mul_inv_cancel, KFU.diagU_one])

theorem stdHom_diagU_rt (d : Fin 3 → Kˣ) (σ : K ≃+* K) {i j : Fin 3} (h : i ≠ j) (c : K) :
    stdHom (KFU.diagU d) σ (rt h c) = rt h ((d i : K) * σ c * (((d j)⁻¹ : Kˣ) : K)) := by
  refine ent_ext fun a b => ?_
  have h1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) K => m a b)
    (coe_stdHom (KFU.diagU d) σ (rt h c))
  simp only [diagU_inv', KFU.diagU_val, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
  change _ = _ at h1
  rw [show ent (stdHom (KFU.diagU d) σ (rt h c)) a b = _ from h1, ent_rt]
  rw [Matrix.map_apply, show ((rt h c : SL3 K) : Matrix (Fin 3) (Fin 3) K) a b = _ from
    ent_rt h c a b, Pi.inv_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hc : i = a ∧ j = a
    · exact absurd (hc.1.trans hc.2.symm) h
    · simp [hc]
  · by_cases hc : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hc
      simp [hab]
    · simp [hab, hc]

theorem mk_rt_injective {i j : Fin 3} (h : i ≠ j) {s s' : K}
    (hss' : (QuotientGroup.mk (rt h s) : PSL3 K) = QuotientGroup.mk (rt h s')) : s = s' := by
  by_cases hs : s = 0
  · subst hs
    rw [rt_zero, QuotientGroup.mk_one] at hss'
    exact ((Matrix.SpecialLinearGroup.transvection_mem_center_iff h s').1
      ((QuotientGroup.eq_one_iff _).1 hss'.symm)).symm
  · exact (rt_eq_of_mk_eq h h hs hss').2.2

theorem std_of_root_stable [Finite K] (Ψ : PSL3 K ≃* PSL3 K)
    (hroot : ∀ (i j : Fin 3) (h : i ≠ j) (s : K),
      ∃ t, Ψ (QuotientGroup.mk (rt h s)) = QuotientGroup.mk (rt h t)) :
    ∃ (d : Fin 3 → Kˣ) (σ : K ≃+* K), ∀ x : SL3 K,
      Ψ (QuotientGroup.mk x) = QuotientGroup.mk (stdHom (KFU.diagU d) σ x) := by
  choose f hf using hroot
  have hadd : ∀ i j (h : i ≠ j) s s', f i j h (s + s') = f i j h s + f i j h s' := by
    intro i j h s s'
    apply mk_rt_injective h
    rw [← hf, rt_add, QuotientGroup.mk_mul, map_mul, hf, hf, ← QuotientGroup.mk_mul, ← rt_add]
  have hinj : ∀ i j (h : i ≠ j), Function.Injective (f i j h) := by
    intro i j h s s' e
    apply mk_rt_injective h
    apply Ψ.injective
    rw [hf, hf, e]
  have hmul : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) s t,
      f i k hik (s * t) = f i j hij s * f j k hjk t := by
    intro i j k hij hjk hik s t
    apply mk_rt_injective hik
    have h1 : (⁅(QuotientGroup.mk (rt hij s) : PSL3 K), (QuotientGroup.mk (rt hjk t) : PSL3 K)⁆) =
        (QuotientGroup.mk (rt hik (s * t)) : PSL3 K) := by
      have := map_commutatorElement (QuotientGroup.mk' (Subgroup.center (SL3 K)))
        (rt hij s) (rt hjk t)
      rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik] at this
      exact this.symm
    have h2 := congrArg Ψ h1
    rw [map_commutatorElement Ψ, hf, hf, hf] at h2
    have h3 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center (SL3 K)))
      (rt hij (f i j hij s)) (rt hjk (f j k hjk t))
    rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik] at h3
    rw [← h2]
    exact h3.symm
  obtain ⟨φ, d, hd⟩ := exists_phi_d (n := 3) le_rfl f hadd hinj hmul
  refine ⟨d, φ, fun x => ?_⟩
  let α : SL3 K →* PSL3 K := Ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (SL3 K)))
  let β : SL3 K →* PSL3 K :=
    (QuotientGroup.mk' (Subgroup.center (SL3 K))).comp (stdHom (KFU.diagU d) φ)
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) K → SL3 K)) ≤ MonoidHom.eqLocus α β := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    show α t.toSpecialLinearGroup = β t.toSpecialLinearGroup
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def]
    show Ψ (QuotientGroup.mk (rt t.hij t.c)) =
      QuotientGroup.mk (stdHom (KFU.diagU d) φ (rt t.hij t.c))
    rw [hf, stdHom_diagU_rt, hd]
  have hx : x ∈ MonoidHom.eqLocus α β := by
    apply hle
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top x
  exact hx

end Std

end CFSG.RankThree.PartOne.KFOUT3
