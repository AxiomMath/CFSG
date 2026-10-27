module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelConj

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))

private theorem exists_trace_mul_sig_ne (hF : Fintype.card F = 2 ^ (2 * l))
    (t : F) (ht : t ≠ 0) :
    ∃ b : F, t ^ 2 ^ l * b + t * b ^ 2 ^ l ≠ 0 := by
  by_cases htσ : t ^ 2 ^ l + t = 0
  · obtain ⟨b, hb⟩ := exists_add_sig_eq (F := F) hF (a := (1 : F)) (by simp)
    refine ⟨b, ?_⟩
    have htfix : t ^ 2 ^ l = t := by
      have h := (add_eq_zero_iff_eq_neg.mp htσ)
      rwa [CharTwo.neg_eq] at h
    rw [htfix, ← mul_add, add_comm b (b ^ 2 ^ l), hb, mul_one]
    exact ht
  · refine ⟨1, ?_⟩
    simpa using htσ

theorem cenOn_commSub_upperSylow_eq_bot :
    cenOn (hermRep l hF) upperSylow (commSub (hermRep l hF) upperSylow) = ⊥ := by
  ext s
  constructor
  · intro hs
    rw [Subgroup.mem_bot]
    obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hs.1
    by_contra ht
    have ht0 : t ≠ 0 := by
      intro h0
      apply ht
      rw [h0, uMat_zero]
    obtain ⟨b, hb⟩ := exists_trace_mul_sig_ne (hF := hF) t ht0
    have hX : hermOff l hF b ∈ commSub (hermRep l hF) upperSylow := by
      rw [commSub_upperSylow]
      change ((hermOff l hF b : Matrix (Fin 2) (Fin 2) F)) 1 1 = 0
      rw [hermOff_coe]
      rfl
    have h := congrArg (fun Y : ↥(hermA l F) =>
      ((Y : Matrix (Fin 2) (Fin 2) F)) 0 0) (hs.2 _ hX)
    rw [hermRep_apply, hermAct_uMat_00, hermOff_coe] at h
    have h' : t ^ 2 ^ l * b + t * b ^ 2 ^ l = 0 := by
      simpa [sig_apply] using h
    exact hb h'
  · intro hs
    rw [Subgroup.mem_bot] at hs
    subst hs
    exact ⟨upperSylow.one_mem, fun _ _ => by simp⟩

private theorem cenOn_commSub_eq_bot_of_sylow (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l)) :
    cenOn (hermRep l hF) A (commSub (hermRep l hF) A) = ⊥ := by
  have hAeq : Nat.card A = Nat.card F := by
    rw [hA, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hAeq
  have hEq : A = upperSylow.map (MulAut.conj x).toMonoidHom :=
    eq_map_conj_upperSylow_of_forall_mem_iff hx
  rw [hEq]
  ext a
  constructor
  · intro ha
    rw [Subgroup.mem_bot]
    have hxinv : x⁻¹ * a * x ∈
        cenOn (hermRep l hF) upperSylow (commSub (hermRep l hF) upperSylow) := by
      refine ⟨?_, ?_⟩
      · obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.mp ha.1
        have hcoe : x⁻¹ * a * x = s := by
          rw [← hsa]
          simp [MulAut.conj_apply]
          group
        rwa [hcoe]
      · intro v hv
        have hmem : hermRep l hF x v ∈
            commSub (hermRep l hF) (upperSylow.map (MulAut.conj x).toMonoidHom) := by
          rw [commSub_map_conj (hermRep l hF) x upperSylow]
          exact Submodule.mem_map_of_mem hv
        have h := ha.2 _ hmem
        calc hermRep l hF (x⁻¹ * a * x) v =
            hermRep l hF x⁻¹ (hermRep l hF a (hermRep l hF x v)) := by
              rw [map_mul, map_mul]
              rfl
          _ = hermRep l hF x⁻¹ (hermRep l hF x v) := by rw [h]
          _ = v := by
            calc hermRep l hF x⁻¹ (hermRep l hF x v)
                = (hermRep l hF x⁻¹ * hermRep l hF x) v := rfl
              _ = hermRep l hF (x⁻¹ * x) v := by rw [map_mul]
              _ = v := by rw [inv_mul_cancel, map_one]; rfl
    rw [cenOn_commSub_upperSylow_eq_bot] at hxinv
    have ha1 : x⁻¹ * a * x = 1 := Subgroup.mem_bot.mp hxinv
    calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      _ = 1 := by rw [ha1]; group
  · intro ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact ⟨upperSylow.map (MulAut.conj x).toMonoidHom |>.one_mem,
      fun _ _ => by simp⟩

theorem IsOrthModule.eq_one_of_forall_commSub_fixed
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) SL(2, F) W} (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) {a : SL(2, F)} (ha : a ∈ A)
    (hfix : ∀ w ∈ commSub ρ A, ρ a w = w) : a = 1 := by
  have horth0 := horth
  obtain ⟨j, β, hβ⟩ := horth0
  let B : Subgroup SL(2, F) := A.map (fieldAut F j)
  let b : SL(2, F) := fieldAut F j a
  have hbB : b ∈ B := Subgroup.mem_map_of_mem _ ha
  have hfixB : ∀ y ∈ commSub (hermRep l hF) B,
      hermRep l hF b y = y := by
    intro y hy
    have hy' : β.symm y ∈ commSub ρ A :=
      (commSub_fieldAut_mem (hF := hF) hβ A (β.symm y)).mpr (by
        simpa using hy)
    have h := hfix _ hy'
    have hβa' : β (ρ a (β.symm y)) =
        hermAct l (sig_sig hF) (fieldAut F j a) y := by
      simpa using hβ a (β.symm y)
    change hermAct l (sig_sig hF) (fieldAut F j a) y = y
    rw [← hβa', h, β.apply_symm_apply]
  have hb1 : b = 1 := by
    have hbCen : b ∈ cenOn (hermRep l hF) B (commSub (hermRep l hF) B) :=
      ⟨hbB, hfixB⟩
    have hsyl := fieldAut_image_sylow A hA2 hA j
    have hbot := cenOn_commSub_eq_bot_of_sylow (hF := hF) B hsyl.1 hsyl.2
    rw [hbot] at hbCen
    exact Subgroup.mem_bot.mp hbCen
  exact (fieldAutEquiv j).injective (by
    rw [fieldAutEquiv_apply, fieldAutEquiv_apply]
    simpa using hb1)

@[expose] def hermPlane (l : ℕ) (b0 : F) : Submodule (ZMod 2) ↥(hermA l F) where
  carrier := {X | (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
    ∃ k : F, k ^ 2 ^ l = k ∧ (X : Matrix (Fin 2) (Fin 2) F) 0 1 = k * b0}
  zero_mem' := by
    refine ⟨rfl, 0, by simp, by simp⟩
  add_mem' := by
    rintro X Y ⟨hX11, k, hk, hX01⟩ ⟨hY11, m, hm, hY01⟩
    refine ⟨?_, k + m, ?_, ?_⟩
    · rw [AddSubgroup.coe_add, Matrix.add_apply, hX11, hY11, add_zero]
    · rw [add_pow_char_pow, hk, hm]
    · rw [AddSubgroup.coe_add, Matrix.add_apply, hX01, hY01, add_mul]
  smul_mem' := by
    intro c X ⟨h11, k, hk, h01⟩
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · rw [zero_smul]
      exact ⟨rfl, 0, by simp, by simp⟩
    · simpa using ⟨h11, k, hk, h01⟩

theorem mem_hermPlane_iff {b0 : F} {X : ↥(hermA l F)} :
    X ∈ hermPlane l b0 ↔
      (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
        ∃ k : F, k ^ 2 ^ l = k ∧ (X : Matrix (Fin 2) (Fin 2) F) 0 1 = k * b0 :=
  Iff.rfl

theorem hermPlane_le_commSub (b0 : F) :
    hermPlane l b0 ≤ commSub (hermRep l hF) upperSylow := by
  intro X hX
  rw [commSub_upperSylow]
  exact hX.1

theorem fixedSub_upperSylow_le_hermPlane (b0 : F) :
    fixedSub (hermRep l hF) upperSylow ≤ hermPlane l b0 := by
  intro X hX
  have hX' : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
      (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 :=
    (mem_fixedSub_upperSylow l hF).mp hX
  exact ⟨hX'.1, 0, by simp, by rw [hX'.2, zero_mul]⟩

private theorem hermPlane_mem_hermMk (b0 a k : F) (ha : a ^ 2 ^ l = a)
    (hk : k ^ 2 ^ l = k) :
    hermMk hF a ha (k * b0) 0 (by simp) ∈ hermPlane l b0 := by
  refine ⟨?_, k, hk, ?_⟩
  · rw [hermMk_coe]; rfl
  · rw [hermMk_coe]; rfl

theorem card_hermPlane (hF : Fintype.card F = 2 ^ (2 * l)) {b0 : F} (hb0 : b0 ≠ 0) :
    Nat.card ↥(hermPlane l b0) = 2 ^ (2 * l) := by
  let e : ↥(hermPlane l b0) ≃ ↥(frobFixField l F) × ↥(frobFixField l F) :=
    { toFun := fun X =>
        let k := Classical.choose X.2.2
        (⟨((X : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) 0 0, by
            rw [mem_frobFixField]
            have h := hermA_00 (a := l) (X : ↥(hermA l F))
            simpa [sig_apply] using h⟩,
          ⟨k, by
            rw [mem_frobFixField]
            exact (Classical.choose_spec X.2.2).1⟩)
      invFun := fun p =>
        ⟨hermMk hF (p.1 : F) (show (p.1 : F) ^ 2 ^ l = (p.1 : F) from p.1.2)
            ((p.2 : F) * b0) 0 (by simp),
          hermPlane_mem_hermMk (l := l) (hF := hF) b0 (p.1 : F) (p.2 : F)
            (show (p.1 : F) ^ 2 ^ l = (p.1 : F) from p.1.2) p.2.2⟩
      left_inv := fun X => by
        apply Subtype.ext
        have hk := Classical.choose_spec X.2.2
        apply hermA_ext
        · rw [hermMk_coe]
          rfl
        · simpa [hermMk_coe] using hk.2.symm
        · simpa [hermMk_coe] using X.2.1.symm
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          simp [hermMk_coe]
        · apply Subtype.ext
          let k' := Classical.choose
            (hermPlane_mem_hermMk (l := l) (hF := hF) b0 (p.1 : F) (p.2 : F)
              (show (p.1 : F) ^ 2 ^ l = (p.1 : F) from p.1.2) p.2.2).2
          have hk' : ((hermMk hF (p.1 : F) (show (p.1 : F) ^ 2 ^ l = (p.1 : F) from p.1.2)
              ((p.2 : F) * b0) 0 (by simp) : ↥(hermA l F)) :
                Matrix (Fin 2) (Fin 2) F) 0 1 = k' * b0 :=
            (Classical.choose_spec
              (hermPlane_mem_hermMk (l := l) (hF := hF) b0 (p.1 : F) (p.2 : F)
                (show (p.1 : F) ^ 2 ^ l = (p.1 : F) from p.1.2) p.2.2).2).2
          have hbase : ((hermMk hF (p.1 : F) (show (p.1 : F) ^ 2 ^ l = (p.1 : F) from p.1.2)
              ((p.2 : F) * b0) 0 (by simp) : ↥(hermA l F)) :
                Matrix (Fin 2) (Fin 2) F) 0 1 = (p.2 : F) * b0 := by
            rw [hermMk_coe]
            rfl
          have hk'' : k' * b0 = (p.2 : F) * b0 := by
            rw [← hk', hbase]
          exact mul_right_cancel₀ hb0 hk'' }
  rw [Nat.card_congr e, Nat.card_prod, card_frobFixField (hF := hF)]
  rw [← pow_add]
  congr 1
  ring

@[expose] def hermPlaneTrace (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (b0 : F) :
    AddSubgroup F where
  carrier := {t | (t * b0 ^ 2 ^ l) ^ 2 ^ l = t * b0 ^ 2 ^ l}
  zero_mem' := by simp
  add_mem' := by
    intro t s ht hs
    have hpowb : (b0 ^ 2 ^ l) ^ 2 ^ l = b0 := by
      simpa [sig_apply] using sig_sig hF b0
    have ht' : t ^ 2 ^ l * b0 = t * b0 ^ 2 ^ l := by
      have h := ht
      change (t * b0 ^ 2 ^ l) ^ 2 ^ l = t * b0 ^ 2 ^ l at h
      rw [mul_pow, hpowb] at h
      exact h
    have hs' : s ^ 2 ^ l * b0 = s * b0 ^ 2 ^ l := by
      have h := hs
      change (s * b0 ^ 2 ^ l) ^ 2 ^ l = s * b0 ^ 2 ^ l at h
      rw [mul_pow, hpowb] at h
      exact h
    calc ((t + s) * b0 ^ 2 ^ l) ^ 2 ^ l
        = (t ^ 2 ^ l + s ^ 2 ^ l) * b0 := by
          simp [add_mul, add_pow_char_pow, mul_pow, hpowb]
      _ = t * b0 ^ 2 ^ l + s * b0 ^ 2 ^ l := by rw [add_mul, ht', hs']
      _ = (t + s) * b0 ^ 2 ^ l := by rw [add_mul]
  neg_mem' := by
    intro t ht
    simpa [CharTwo.neg_eq] using ht

@[expose] def hermPlaneFix (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (b0 : F) :
    Subgroup (SL(2, F)) :=
  rootSub (hermPlaneTrace l hF b0)

theorem hermPlaneFix_le_upperSylow (b0 : F) : hermPlaneFix l hF b0 ≤ upperSylow := by
  rintro g ⟨t, -, rfl⟩
  exact mem_upperSylow_iff.mpr ⟨t, rfl⟩

theorem card_hermPlaneFix {b0 : F} (hb0 : b0 ≠ 0) :
    Nat.card ↥(hermPlaneFix l hF b0) = 2 ^ l := by
  let e2 : ↥(hermPlaneTrace l hF b0) ≃ ↥(frobFixField l F) :=
    { toFun := fun t => ⟨(t : F) * b0 ^ 2 ^ l, t.2⟩
      invFun := fun c =>
        ⟨(c : F) / b0 ^ 2 ^ l, by
          change ((((c : F) / b0 ^ 2 ^ l) * b0 ^ 2 ^ l) ^ 2 ^ l =
            ((c : F) / b0 ^ 2 ^ l) * b0 ^ 2 ^ l)
          rw [div_mul_cancel₀ _ (pow_ne_zero _ hb0)]
          exact c.2⟩
      left_inv := fun t => by
        apply Subtype.ext
        change ((t : F) * b0 ^ 2 ^ l) / b0 ^ 2 ^ l = (t : F)
        rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hb0)]
      right_inv := fun c => by
        apply Subtype.ext
        change ((c : F) / b0 ^ 2 ^ l) * b0 ^ 2 ^ l = (c : F)
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hb0)] }
  rw [hermPlaneFix, card_rootSub, Nat.card_congr e2, card_frobFixField (hF := hF)]

theorem fixator_hermPlane_eq {b0 : F} {X : ↥(hermA l F)}
    (hX : X ∈ hermPlane l b0)
    (hXnot : X ∉ fixedSub (hermRep l hF) upperSylow) :
    {s : SL(2, F) | s ∈ upperSylow ∧ hermRep l hF s X = X} =
      (hermPlaneFix l hF b0 : Set (SL(2, F))) := by
  have hpowb : (b0 ^ 2 ^ l) ^ 2 ^ l = b0 := by
    simpa [sig_apply] using sig_sig hF b0
  ext s
  constructor
  · rintro ⟨hsS, hsX⟩
    obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hsS
    obtain ⟨k, hk, hk01⟩ := hX.2
    have hX01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
      intro h01
      exact hXnot (by rw [mem_fixedSub_upperSylow]; exact ⟨hX.1, h01⟩)
    have hk0 : k ≠ 0 := by
      intro hk0
      exact hX01 (by rw [hk01, hk0, zero_mul])
    have h := congrArg (fun Y : ↥(hermA l F) =>
      ((Y : Matrix (Fin 2) (Fin 2) F)) 0 0) hsX
    rw [hermRep_apply, hermAct_uMat_00, hX.1, mul_zero, add_zero] at h
    have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 =
        ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l := hermA_10 (a := l) X
    have htr : t ^ 2 ^ l * b0 + t * b0 ^ 2 ^ l = 0 := by
      have h' : t ^ 2 ^ l * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
          t * ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l = 0 := by
        rw [h10, sig_apply] at h
        linear_combination h
      rw [hk01, mul_pow, hk] at h'
      have hk' : k * (t ^ 2 ^ l * b0 + t * b0 ^ 2 ^ l) = 0 := by
        rw [mul_add, ← mul_assoc, ← mul_assoc]
        linear_combination h'
      exact (mul_eq_zero.mp hk').resolve_left hk0
    refine ⟨t, ?_, rfl⟩
    change (t * b0 ^ 2 ^ l) ^ 2 ^ l = t * b0 ^ 2 ^ l
    rw [mul_pow, hpowb]
    have hneg := (add_eq_zero_iff_eq_neg.mp htr)
    rwa [CharTwo.neg_eq] at hneg
  · rintro ⟨t, ht, rfl⟩
    refine ⟨mem_upperSylow_iff.mpr ⟨t, rfl⟩, ?_⟩
    obtain ⟨k, hk, hk01⟩ := hX.2
    have ht' : t ^ 2 ^ l * b0 = t * b0 ^ 2 ^ l := by
      have h := ht
      change (t * b0 ^ 2 ^ l) ^ 2 ^ l = t * b0 ^ 2 ^ l at h
      rw [mul_pow, hpowb] at h
      exact h
    have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 =
        ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l := hermA_10 (a := l) X
    rw [hermRep_apply]
    refine hermA_ext ?_ ?_ ?_
    · rw [hermAct_uMat_00, hX.1, hk01, h10, hk01, mul_pow, hk]
      rw [sig_apply]
      linear_combination k * ht' +
        (k * b0 ^ 2 ^ l * t) * (CharP.cast_eq_zero F 2)
    · rw [hermAct_uMat_01, hX.1]
      ring
    · rw [hermAct_uMat_11]

private theorem mem_hermPlaneFix_map_conj_iff (x : SL(2, F)) {p : ↥(hermA l F)}
    (hp : p ∈ hermPlane l 1)
    (hpnot : p ∉ fixedSub (hermRep l hF) upperSylow) {s : SL(2, F)} :
    s ∈ (hermPlaneFix l hF 1).map (MulAut.conj x).toMonoidHom ↔
      s ∈ upperSylow.map (MulAut.conj x).toMonoidHom ∧
        hermRep l hF s (hermRep l hF x p) = hermRep l hF x p := by
  have hset := fixator_hermPlane_eq (hF := hF) (b0 := 1) hp hpnot
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hts : t ∈ upperSylow := hermPlaneFix_le_upperSylow (hF := hF) 1 ht
    have htp : hermRep l hF t p = p :=
      ((Set.ext_iff.mp hset t).mpr ht).2
    refine ⟨Subgroup.mem_map_of_mem _ hts, ?_⟩
    have hconj : MulAut.conj x t = x * t * x⁻¹ := rfl
    change hermRep l hF ((MulAut.conj x) t) (hermRep l hF x p) = hermRep l hF x p
    rw [hconj, map_mul, map_mul]
    change hermRep l hF x (hermRep l hF t (hermRep l hF x⁻¹ (hermRep l hF x p))) =
      hermRep l hF x p
    rw [Representation.inv_self_apply, htp]
  · rintro ⟨hsS, hfix⟩
    obtain ⟨t, htS, rfl⟩ := Subgroup.mem_map.mp hsS
    have htp : hermRep l hF t p = p := by
      have hconj : MulAut.conj x t = x * t * x⁻¹ := rfl
      change hermRep l hF ((MulAut.conj x) t) (hermRep l hF x p) = hermRep l hF x p at hfix
      rw [hconj, map_mul, map_mul] at hfix
      change hermRep l hF x (hermRep l hF t (hermRep l hF x⁻¹ (hermRep l hF x p))) =
        hermRep l hF x p at hfix
      rw [Representation.inv_self_apply] at hfix
      have hinj : Function.Injective (hermRep l hF x) :=
        Function.LeftInverse.injective (g := hermRep l hF x⁻¹) fun u =>
          Representation.inv_self_apply (hermRep l hF) x u
      exact hinj hfix
    refine Subgroup.mem_map_of_mem _ ?_
    exact (Set.ext_iff.mp hset t).mp ⟨htS, htp⟩

private theorem fixedSub_conj_le_hermPlane_map (x : SL(2, F)) :
    fixedSub (hermRep l hF) (upperSylow.map (MulAut.conj x).toMonoidHom) ≤
      (hermPlane l 1).map (hermRep l hF x) := by
  rw [fixedSub_map_conj]
  exact Submodule.map_mono (fixedSub_upperSylow_le_hermPlane (hF := hF) 1)

private theorem hermPlane_map_le_commSub_conj (x : SL(2, F)) :
    (hermPlane l 1).map (hermRep l hF x) ≤
      commSub (hermRep l hF) (upperSylow.map (MulAut.conj x).toMonoidHom) := by
  rw [commSub_map_conj]
  exact Submodule.map_mono (hermPlane_le_commSub (hF := hF) 1)

private theorem card_hermPlane_map_conj (x : SL(2, F)) :
    Nat.card ↥((hermPlane l 1).map (hermRep l hF x)) = 2 ^ (2 * l) := by
  have hinj : Function.Injective (hermRep l hF x) :=
    Function.LeftInverse.injective (g := hermRep l hF x⁻¹) fun u =>
      Representation.inv_self_apply (hermRep l hF) x u
  rw [← Nat.card_congr (Submodule.equivMapOfInjective (hermRep l hF x) hinj
      (hermPlane l 1)).toEquiv, card_hermPlane (hF := hF) one_ne_zero]

private theorem card_hermPlaneFix_map_conj (x : SL(2, F)) :
    Nat.card ↥((hermPlaneFix l hF 1).map (MulAut.conj x).toMonoidHom) = 2 ^ l := by
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
    card_hermPlaneFix (hF := hF) one_ne_zero]

private theorem fixedSub_lt_comap_hermPlane
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) SL(2, F) W} (horth : IsOrthModule hF ρ)
    {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) {x : SL(2, F)}
    (hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom)
    (hcardL : Nat.card ↥(((hermPlane l 1).map (hermRep l hF x)).comap
      (β.toAddMonoidHom.toZModLinearMap 2)) = 2 ^ (2 * l)) :
    fixedSub ρ A < ((hermPlane l 1).map (hermRep l hF x)).comap
        (β.toAddMonoidHom.toZModLinearMap 2) ∧
      ((hermPlane l 1).map (hermRep l hF x)).comap
          (β.toAddMonoidHom.toZModLinearMap 2) ≤ commSub ρ A := by
  let βlin : W →ₗ[ZMod 2] ↥(hermA l F) := β.toAddMonoidHom.toZModLinearMap 2
  let L : Submodule (ZMod 2) W :=
    ((hermPlane l 1).map (hermRep l hF x)).comap βlin
  have hfixedLe : fixedSub ρ A ≤ L := by
    intro w hw
    change β w ∈ (hermPlane l 1).map (hermRep l hF x)
    have hβw : β w ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) :=
      (fixedSub_fieldAut_mem (hF := hF) hβ A w).mp hw
    rw [hEq] at hβw
    exact fixedSub_conj_le_hermPlane_map (hF := hF) x hβw
  have hcommLe : L ≤ commSub ρ A := by
    intro w hw
    apply (commSub_fieldAut_mem (hF := hF) hβ A w).mpr
    have h := (hermPlane_map_le_commSub_conj (hF := hF) x) hw
    rw [← hEq] at h
    exact h
  refine ⟨lt_of_le_of_ne hfixedLe ?_, hcommLe⟩
  intro hEqL
  have hcard : Nat.card ↥(fixedSub ρ A) = Nat.card ↥L := by rw [hEqL]
  rw [IsOrthModule.card_fixedSub hF horth A hA2 hA, hcardL] at hcard
  have hl : 1 ≤ l := one_le_of_card hF
  have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (show l < 2 * l by omega)
  omega

private theorem fixator_hermPlane_map_eq
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) SL(2, F) W}
    {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (A : Subgroup SL(2, F)) {x : SL(2, F)}
    (hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom) :
    ∀ w ∈ ((hermPlane l 1).map (hermRep l hF x)).comap
          (β.toAddMonoidHom.toZModLinearMap 2),
      w ∉ fixedSub ρ A → ∀ a ∈ A, ρ a w = w ↔ a ∈ ((hermPlaneFix l hF 1).map
          (MulAut.conj x).toMonoidHom).map ((fieldAutEquiv j).symm).toMonoidHom := by
  let L0 : Submodule (ZMod 2) ↥(hermA l F) := (hermPlane l 1).map (hermRep l hF x)
  let C0 : Subgroup SL(2, F) := (hermPlaneFix l hF 1).map (MulAut.conj x).toMonoidHom
  let βlin : W →ₗ[ZMod 2] ↥(hermA l F) := β.toAddMonoidHom.toZModLinearMap 2
  let L : Submodule (ZMod 2) W := L0.comap βlin
  let C : Subgroup SL(2, F) := C0.map ((fieldAutEquiv j).symm).toMonoidHom
  change ∀ w ∈ L, w ∉ fixedSub ρ A → ∀ a ∈ A, ρ a w = w ↔ a ∈ C
  intro w hwL hwNot a haA
  have hwL0 : β w ∈ L0 := hwL
  have hwNot0 : β w ∉ fixedSub (hermRep l hF) (A.map (fieldAut F j)) := by
    intro hfix
    exact hwNot ((fixedSub_fieldAut_mem (hF := hF) hβ A w).mpr hfix)
  obtain ⟨p, hpP0, hpEq⟩ := Submodule.mem_map.mp hwL0
  have hpNot : p ∉ fixedSub (hermRep l hF) upperSylow := by
    intro hpfix
    apply hwNot0
    rw [← hpEq, hEq, fixedSub_map_conj]
    exact Submodule.mem_map_of_mem hpfix
  have hfix0 : hermRep l hF (fieldAut F j a) (hermRep l hF x p) =
      hermRep l hF x p ↔ fieldAut F j a ∈ C0 := by
    have h := mem_hermPlaneFix_map_conj_iff (hF := hF) x hpP0 hpNot
      (s := fieldAut F j a)
    have hB : fieldAut F j a ∈ upperSylow.map (MulAut.conj x).toMonoidHom := by
      rw [← hEq]
      exact Subgroup.mem_map_of_mem _ haA
    exact ⟨fun hfix => h.mpr ⟨hB, hfix⟩, fun hC => (h.mp hC).2⟩
  have hCa : a ∈ C ↔ fieldAut F j a ∈ C0 := by
    constructor
    · rintro ⟨t, ht, hta⟩
      rwa [← show t = fieldAut F j a by
        simpa [fieldAutEquiv_apply] using congrArg (fieldAutEquiv j) hta]
    · intro h
      refine ⟨fieldAut F j a, h, ?_⟩
      rw [← fieldAutEquiv_apply]
      exact (fieldAutEquiv j).symm_apply_apply a
  have hbeta : β (ρ a w) = hermRep l hF (fieldAut F j a) (hermRep l hF x p) := by
    rw [hβ, hpEq]
    rfl
  constructor
  · intro hfix
    apply hCa.mpr
    apply hfix0.mp
    rw [← hbeta, hfix, ← hpEq]
  · intro haC
    apply β.injective
    rw [hbeta]
    exact (hfix0.mpr (hCa.mp haC)).trans hpEq

theorem IsOrthModule.exists_fixed_plane
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) SL(2, F) W} (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) :
    ∃ L : Submodule (ZMod 2) W, ∃ C : Subgroup SL(2, F),
      fixedSub ρ A < L ∧ L ≤ commSub ρ A ∧ Nat.card ↥L = 2 ^ (2 * l) ∧
        C ≤ A ∧ Nat.card ↥C = 2 ^ l ∧
          ∀ w ∈ L, w ∉ fixedSub ρ A → ∀ a ∈ A, ρ a w = w ↔ a ∈ C := by
  have horth0 := horth
  obtain ⟨j, β, hβ⟩ := horth0
  let B : Subgroup SL(2, F) := A.map (fieldAut F j)
  have hsB := fieldAut_image_sylow A hA2 hA j
  have hAeq : Nat.card B = Nat.card F := by
    rw [hsB.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup B hsB.1 hAeq
  have hEq : B = upperSylow.map (MulAut.conj x).toMonoidHom :=
    eq_map_conj_upperSylow_of_forall_mem_iff hx
  let L0 : Submodule (ZMod 2) ↥(hermA l F) := (hermPlane l 1).map (hermRep l hF x)
  let C0 : Subgroup SL(2, F) := (hermPlaneFix l hF 1).map (MulAut.conj x).toMonoidHom
  let βlin : W →ₗ[ZMod 2] ↥(hermA l F) := β.toAddMonoidHom.toZModLinearMap 2
  let L : Submodule (ZMod 2) W := L0.comap βlin
  let C : Subgroup SL(2, F) := C0.map ((fieldAutEquiv j).symm).toMonoidHom
  have hcardL0 : Nat.card ↥L0 = 2 ^ (2 * l) := card_hermPlane_map_conj (hF := hF) x
  have hcardC0 : Nat.card ↥C0 = 2 ^ l := card_hermPlaneFix_map_conj (hF := hF) x
  have hL_eq : L = L0.map (β.symm.toAddMonoidHom.toZModLinearMap 2) := by
    ext w
    simp only [L, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · intro hw
      exact ⟨β w, hw, β.symm_apply_apply w⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [βlin] using hy
  have hcardL : Nat.card ↥L = 2 ^ (2 * l) := by
    rw [hL_eq, ← Nat.card_congr (Submodule.equivMapOfInjective
      (β.symm.toAddMonoidHom.toZModLinearMap 2)
      (fun a b h => β.symm.injective h) L0).toEquiv, hcardL0]
  have hcardC : Nat.card ↥C = 2 ^ l := by
    rw [Subgroup.card_map_of_injective (fieldAutEquiv j).symm.injective, hcardC0]
  have hC0_le_B : C0 ≤ B := by
    rw [hEq]
    exact Subgroup.map_mono (hermPlaneFix_le_upperSylow (hF := hF) 1)
  have hC_le_A : C ≤ A := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hc
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp (hC0_le_B ht)
    rw [← hae]
    change (fieldAutEquiv j).symm ((fieldAutEquiv j) a) ∈ A
    rwa [MulEquiv.symm_apply_apply]
  obtain ⟨hlt, hcommLe⟩ := fixedSub_lt_comap_hermPlane (hF := hF) horth hβ A hA2 hA hEq hcardL
  refine ⟨L, C, hlt, hcommLe, hcardL, hC_le_A, hcardC, ?_⟩
  exact fixator_hermPlane_map_eq (hF := hF) hβ A hEq

end CFSG.RankThree.GF2n.Tim81.Sec2
