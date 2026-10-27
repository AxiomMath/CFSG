module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_hom_lift (hW : ∀ w : W, w ^ 2 = 1) (A T B' : Subgroup W) (h : A ≤ B' ⊔ T) :
    ∃ β : ↥A →* W, (∀ a : ↥A, β a ∈ T) ∧ ∀ a : ↥A, (a : W) * (β a)⁻¹ ∈ B' := by
  classical
  letI : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact hW x.toMul
  letI : Module (ZMod 2) (Additive ↥A) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact Subtype.ext (hW (x.toMul : W))
  let b := Module.Basis.ofVectorSpace (ZMod 2) (Additive ↥A)
  have hgen : ∀ i, ∃ bi, bi ∈ B' ∧ ∃ ti, ti ∈ T ∧ bi * ti = ((b i).toMul : W) := by
    intro i
    have hmem : ((b i).toMul : W) ∈ B' ⊔ T := h (b i).toMul.2
    rw [Subgroup.mem_sup] at hmem
    obtain ⟨bi, hbi, ti, hti, hbiti⟩ := hmem
    exact ⟨bi, hbi, ti, hti, hbiti⟩
  choose bi hbi ti hti hbiti using hgen
  let f : Additive ↥A →ₗ[ZMod 2] Additive W :=
    b.constr (ZMod 2) fun i => Additive.ofMul (ti i)
  let β : ↥A →* W :=
    { toFun := fun a => (f (Additive.ofMul a)).toMul
      map_one' := by
        change (f (Additive.ofMul (1 : ↥A))).toMul = 1
        rw [ofMul_one, map_zero, toMul_zero]
      map_mul' := by
        intro a a'
        change (f (Additive.ofMul (a * a'))).toMul =
          (f (Additive.ofMul a)).toMul * (f (Additive.ofMul a')).toMul
        rw [ofMul_mul, map_add, toMul_add] }
  have hβbasis : ∀ i, β ((b i).toMul) = ti i := by
    intro i
    change ((b.constr (ZMod 2) (fun j => Additive.ofMul (ti j))) (b i)).toMul = ti i
    rw [Module.Basis.constr_basis]
    exact toMul_ofMul (ti i)
  let P : Subgroup ↥A :=
    { carrier := {a | (a : W) * (β a)⁻¹ ∈ B' ∧ β a ∈ T}
      one_mem' := by
        constructor
        · simpa using B'.one_mem
        · simpa using T.one_mem
      mul_mem' := by
        intro a a' ha ha'
        constructor
        · have h1 : (a : W) * (β a)⁻¹ ∈ B' := ha.1
          have h2 : (a' : W) * (β a')⁻¹ ∈ B' := ha'.1
          have heq : ((a * a' : ↥A) : W) * (β (a * a'))⁻¹ =
              ((a : W) * (β a)⁻¹) * ((a' : W) * (β a')⁻¹) := by
            rw [MonoidHom.map_mul, Subgroup.coe_mul]
            apply Additive.ofMul.injective
            simp only [ofMul_mul, ofMul_inv]
            abel
          rw [heq]
          exact B'.mul_mem h1 h2
        · rw [MonoidHom.map_mul]
          exact T.mul_mem ha.2 ha'.2
      inv_mem' := by
        intro a ha
        have hinv : a⁻¹ = a := by
          apply Subtype.ext
          exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW (a : W))
        rwa [hinv] }
  have hPmem : ∀ a : ↥A, a ∈ P := by
    have hspan : Submodule.span (ZMod 2) (Set.range b) ≤
        AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup P) := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      change b i ∈ Subgroup.toAddSubgroup P
      rw [Additive.mem_toAddSubgroup]
      change ((b i).toMul : W) * (β ((b i).toMul))⁻¹ ∈ B' ∧ β ((b i).toMul) ∈ T
      constructor
      · rw [hβbasis i]
        have hbiti' : ((b i).toMul : W) = bi i * ti i := (hbiti i).symm
        rw [hbiti']
        simpa only [mul_assoc, mul_inv_cancel, mul_one] using hbi i
      · rw [hβbasis i]
        exact hti i
    have htop : (⊤ : Submodule (ZMod 2) (Additive ↥A)) ≤
        AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup P) := by
      rw [← b.span_eq]
      exact hspan
    intro a
    have ha : Additive.ofMul a ∈ Subgroup.toAddSubgroup P := by
      have h : Additive.ofMul a ∈
          AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup P) := htop trivial
      change Additive.ofMul a ∈ Subgroup.toAddSubgroup P at h
      exact h
    rw [Additive.mem_toAddSubgroup, toMul_ofMul] at ha
    exact ha
  exact ⟨β, fun a => (hPmem a).2, fun a => (hPmem a).1⟩

private theorem gf2_Sec_sup_stable {ι : Type*} [DecidableEq ι] {H : Subgroup (MulAut W)}
    {B : ι → Subgroup W} (hB : ∀ i, StableUnder H (B i)) (s : Finset ι) :
    StableUnder H (s.sup B) := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
      intro x hx u hu
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
  | insert j s hj ih =>
      rw [Finset.sup_insert]
      exact stableUnder_sup (hB j) ih

private theorem gf2_Sec_inf_eq {H : Subgroup (MulAut W)} {C A B' T : Subgroup W}
    (hA : IsIrrOn H A C) (hT : IsIrrOn H T C) (hB' : StableUnder H B') (hCB' : C ≤ B')
    (hAle : A ≤ B' ⊔ T) (hAB' : ¬ A ≤ B') : A ⊓ B' = C ∧ T ⊓ B' = C := by
  constructor
  · have hstab : StableUnder H (A ⊓ B') := stableUnder_inf hA.2.1 hB'
    have hC : C ≤ A ⊓ B' := le_inf hA.1.le hCB'
    rcases hA.2.2.2 (A ⊓ B') hstab hC inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hAB'
  · have hstab : StableUnder H (T ⊓ B') := stableUnder_inf hT.2.1 hB'
    have hC : C ≤ T ⊓ B' := le_inf hT.1.le hCB'
    rcases hT.2.2.2 (T ⊓ B') hstab hC inf_le_left with h | h
    · exact h
    · exfalso
      have hTB' : T ≤ B' := h ▸ inf_le_right
      exact hAB' (hAle.trans (le_of_eq (sup_eq_left.mpr hTB')))

private theorem gf2_Sec_one_way (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {C A B' T : Subgroup W} (hA : IsIrrOn H A C) (hT : IsIrrOn H T C)
    (hB' : StableUnder H B') (hCB' : C ≤ B') (hAle : A ≤ B' ⊔ T) (hAB' : ¬ A ≤ B') :
    SecIsoOn H A C T C ∧ T ≤ B' ⊔ A := by
  have hinf := gf2_Sec_inf_eq hA hT hB' hCB' hAle hAB'
  have hAB'inf : A ⊓ B' = C := hinf.1
  have hTB'inf : T ⊓ B' = C := hinf.2
  obtain ⟨β, hβT, hβB'⟩ := exists_hom_lift hW A T B' hAle
  have hβC : ∀ a : ↥A, β a ∈ C ↔ (a : W) ∈ C := by
    intro a
    constructor
    · intro hβaC
      have haB' : (a : W) ∈ B' := by
        have h1 : (a : W) * (β a)⁻¹ ∈ B' := hβB' a
        have h2 : β a ∈ B' := hCB' hβaC
        have h : (a : W) = ((a : W) * (β a)⁻¹) * β a := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [h]
        exact B'.mul_mem h1 h2
      have hmem : (a : W) ∈ A ⊓ B' := ⟨a.2, haB'⟩
      rwa [hAB'inf] at hmem
    · intro haC
      have haB' : (a : W) ∈ B' := hCB' haC
      have hβaB' : β a ∈ B' := by
        have h1 : (a : W) * (β a)⁻¹ ∈ B' := hβB' a
        have h : β a = ((a : W) * (β a)⁻¹)⁻¹ * (a : W) := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [h]
        exact B'.mul_mem (B'.inv_mem h1) haB'
      have hmem : β a ∈ T ⊓ B' := ⟨hβT a, hβaB'⟩
      rwa [hTB'inf] at hmem
  have heq : ∀ x ∈ H, ∀ a a' : ↥A, (a' : W) = x a → β a' * (x (β a))⁻¹ ∈ C := by
    intro x hx a a' ha'
    have hxT : x (β a) ∈ T := hT.2.1 x hx (β a) (hβT a)
    have hp : (a' : W) * (β a')⁻¹ ∈ B' := hβB' a'
    have hq : (a' : W) * (x (β a))⁻¹ ∈ B' := by
      have h := hB' x hx ((a : W) * (β a)⁻¹) (hβB' a)
      rwa [map_mul, map_inv, ← ha'] at h
    have huB' : β a' * (x (β a))⁻¹ ∈ B' := by
      have h : ((a' : W) * (x (β a))⁻¹) * ((a' : W) * (β a')⁻¹)⁻¹ =
          β a' * (x (β a))⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [← h]
      exact B'.mul_mem hq (B'.inv_mem hp)
    have huT : β a' * (x (β a))⁻¹ ∈ T := T.mul_mem (hβT a') (T.inv_mem hxT)
    have hmem : β a' * (x (β a))⁻¹ ∈ T ⊓ B' := ⟨huT, huB'⟩
    rwa [hTB'inf] at hmem
  have hSstab : StableUnder H (β.range ⊔ C) := by
    intro x hx s hs
    rw [Subgroup.mem_sup] at hs
    obtain ⟨r, hr, c, hc, rfl⟩ := hs
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
    rw [map_mul]
    have hxβ : x (β a) ∈ β.range ⊔ C := by
      let a'' : ↥A := ⟨x a, hA.2.1 x hx (a : W) a.2⟩
      have ha'' : (a'' : W) = x a := rfl
      have he : β a'' * (x (β a))⁻¹ ∈ C := heq x hx a a'' ha''
      have hxβeq : x (β a) = β a'' * (β a'' * (x (β a))⁻¹)⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [hxβeq]
      exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨a'', rfl⟩) (C.inv_mem he)
    have hxc : x c ∈ β.range ⊔ C := Subgroup.mem_sup_right (hA.2.2.1 x hx c hc)
    exact (β.range ⊔ C).mul_mem hxβ hxc
  have hSleT : β.range ⊔ C ≤ T := by
    apply sup_le
    · intro r hr
      rw [MonoidHom.mem_range] at hr
      obtain ⟨a, rfl⟩ := hr
      exact hβT a
    · exact hT.1.le
  have hCS : C ≤ β.range ⊔ C := le_sup_right
  have hsurj : ∀ b ∈ T, ∃ a : ↥A, β a * b⁻¹ ∈ C := by
    rcases hT.2.2.2 (β.range ⊔ C) hSstab hCS hSleT with hSC | hST
    · exfalso
      have hAC : A ≤ C := by
        intro a ha
        have hmem : β ⟨a, ha⟩ ∈ β.range ⊔ C :=
          Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
        have hCmem : β ⟨a, ha⟩ ∈ C := by rwa [hSC] at hmem
        exact (hβC ⟨a, ha⟩).mp hCmem
      exact (not_le_of_gt hA.1) hAC
    · intro b hb
      have hbS : b ∈ β.range ⊔ C := by rwa [← hST] at hb
      rw [Subgroup.mem_sup] at hbS
      obtain ⟨r, hr, c, hc, hbc⟩ := hbS
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
      refine ⟨a, ?_⟩
      have h : β a * b⁻¹ = c⁻¹ := by
        rw [← hbc]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [h]
      exact C.inv_mem hc
  refine ⟨?_, ?_⟩
  · exact ⟨hA.1.le, hT.1.le, hA.2.1, hA.2.2.1, hT.2.1, hT.2.2.1,
      β, hβT, hβC, hsurj, heq⟩
  · intro b hb
    obtain ⟨a, ha⟩ := hsurj b hb
    have hcB' : (β a * b⁻¹)⁻¹ ∈ B' := hCB' (C.inv_mem ha)
    have hdB' : ((a : W) * (β a)⁻¹)⁻¹ ∈ B' := B'.inv_mem (hβB' a)
    have hb_eq : b = (a : W) * (((a : W) * (β a)⁻¹)⁻¹ * (β a * b⁻¹)⁻¹) := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [hb_eq]
    exact (sup_comm A B') ▸ Subgroup.mul_mem_sup a.2 (B'.mul_mem hdB' hcB')

theorem secIsoOn_of_le_sup (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {C A B' T : Subgroup W} (hA : IsIrrOn H A C) (hT : IsIrrOn H T C)
    (hB' : StableUnder H B') (hCB' : C ≤ B') (hAle : A ≤ B' ⊔ T) (hAB' : ¬ A ≤ B') :
    SecIsoOn H A C T C ∧ SecIsoOn H T C A C := by
  have hnot : ¬ T ≤ B' := by
    intro hTB'
    have h2 : T ⊓ B' = C := (gf2_Sec_inf_eq hA hT hB' hCB' hAle hAB').2
    have hTC : T ≤ C := h2 ▸ le_inf le_rfl hTB'
    exact (not_le_of_gt hT.1) hTC
  have hTA : T ≤ B' ⊔ A := (gf2_Sec_one_way hW hA hT hB' hCB' hAle hAB').2
  exact ⟨(gf2_Sec_one_way hW hA hT hB' hCB' hAle hAB').1,
    (gf2_Sec_one_way hW hT hA hB' hCB' hTA hnot).1⟩

theorem exists_secIsoOn_of_le_iSup (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {C A : Subgroup W} {ι : Type*} [Finite ι] {B : ι → Subgroup W} (hA : IsIrrOn H A C)
    (hB : ∀ i, IsIrrOn H (B i) C) (hle : A ≤ C ⊔ ⨆ i, B i) :
    ∃ i, SecIsoOn H A C (B i) C ∧ SecIsoOn H (B i) C A C := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, A ≤ C ⊔ s.sup B →
      ∃ i ∈ s, SecIsoOn H A C (B i) C ∧ SecIsoOn H (B i) C A C := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro h
        rw [Finset.sup_empty, sup_bot_eq] at h
        exact absurd h (not_le_of_gt hA.1)
    | insert j s hj ih =>
        intro h
        have hstab : StableUnder H (C ⊔ s.sup B) :=
          stableUnder_sup hA.2.2.1 (gf2_Sec_sup_stable (fun i => (hB i).2.1) s)
        have hAle' : A ≤ (C ⊔ s.sup B) ⊔ B j := by
          have heq : C ⊔ (insert j s).sup B = (C ⊔ s.sup B) ⊔ B j := by
            rw [Finset.sup_insert]
            ac_rfl
          rwa [heq] at h
        by_cases hAB'' : A ≤ C ⊔ s.sup B
        · obtain ⟨i, hi, hiso⟩ := ih hAB''
          exact ⟨i, Finset.mem_insert_of_mem hi, hiso⟩
        · obtain ⟨hiso1, hiso2⟩ :=
            secIsoOn_of_le_sup hW hA (hB j) hstab le_sup_left hAle' hAB''
          exact ⟨j, Finset.mem_insert_self j s, hiso1, hiso2⟩
  have hle' : A ≤ C ⊔ Finset.univ.sup B := by
    rwa [Finset.sup_univ_eq_iSup]
  obtain ⟨i, -, hiso⟩ := key Finset.univ hle'
  exact ⟨i, hiso⟩

end CFSG.LocalAnalysis.WeakClosure81
