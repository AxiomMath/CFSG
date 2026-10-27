module

public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverRigid
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX

public section

namespace CFSG.RankThree.PartTwo.Sec13.KS135Cover

open CFSG CFSG.ComponentClassification.CentralCover
open scoped commutatorElement

section Cocycle

variable {Q : Type*} [Group Q] {f : NormCocycle Q}

theorem mk_zero_mul_self (s : Q) :
    (⟨0, s⟩ * ⟨0, s⟩ : CocycleExtension f) = ⟨f s s, s * s⟩ := by
  rw [CocycleExtension.mk_mul_mk, zero_add, zero_add]

theorem mk_eq_one_iff {e : ZMod 2} {s : Q} :
    (⟨e, s⟩ : CocycleExtension f) = 1 ↔ e = 0 ∧ s = 1 := by
  constructor
  · intro h
    exact ⟨congrArg CocycleExtension.fst h, congrArg CocycleExtension.snd h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem three_le_pRank_of_cocycle {J : Type*} [Group J] [Finite J]
    (ψ : CocycleExtension f →* J) (hψ : Function.Injective ψ) {s₁ s₂ : Q}
    (h11 : s₁ * s₁ = 1) (h22 : s₂ * s₂ = 1) (h12 : s₁ * s₂ = s₂ * s₁) (h1 : s₁ ≠ 1)
    (h2 : s₂ ≠ 1) (h3 : s₁ * s₂ ≠ 1) (hf1 : f s₁ s₁ = 0) (hf2 : f s₂ s₂ = 0)
    (hf3 : f (s₁ * s₂) (s₁ * s₂) = 0) : 3 ≤ CFSG.pRank 2 J := by
  set X : CocycleExtension f := ⟨0, s₁⟩ with hX
  set Y : CocycleExtension f := ⟨0, s₂⟩ with hY
  set C : CocycleExtension f := ⟨1, 1⟩ with hC
  have hXX : X * X = 1 := by rw [hX, mk_zero_mul_self, hf1, h11]; rfl
  have hYY : Y * Y = 1 := by rw [hY, mk_zero_mul_self, hf2, h22]; rfl
  have hCC : C * C = 1 := by
    rw [hC, CocycleExtension.mk_one_mul]
    exact (mk_eq_one_iff).mpr ⟨zmod_two_add_self 1, rfl⟩
  have hCc : ∀ w : CocycleExtension f, C * w = w * C := fun w =>
    (Subgroup.mem_center_iff.mp (CocycleExtension.mk_one_mem_center 1) w).symm
  have hXY2 : (X * Y) * (X * Y) = 1 := by
    have e : X * Y = ⟨f s₁ s₂, s₁ * s₂⟩ := by
      rw [hX, hY, CocycleExtension.mk_mul_mk, zero_add, zero_add]
    rw [e, CocycleExtension.mk_mul_mk, hf3, add_zero, zmod_two_add_self,
      show s₁ * s₂ * (s₁ * s₂) = 1 by
        calc s₁ * s₂ * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by group
          _ = s₁ * (s₁ * s₂) * s₂ := by rw [h12]
          _ = (s₁ * s₁) * (s₂ * s₂) := by group
          _ = 1 := by rw [h11, h22, one_mul]]
    rfl
  have hXinv : X⁻¹ = X := inv_eq_of_mul_eq_one_right hXX
  have hYinv : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hYY
  have hXYc : X * Y = Y * X := by
    have h := inv_eq_of_mul_eq_one_right hXY2
    rw [mul_inv_rev, hXinv, hYinv] at h
    exact h.symm
  have hval : ∀ a : ZMod 2, a = 0 ∨ a = 1 := fun a => by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hind : ∀ a b d : ZMod 2, X ^ a.val * Y ^ b.val * C ^ d.val = 1 →
      a = 0 ∧ b = 0 ∧ d = 0 := by
    intro a b d h
    have hsnd := congrArg CocycleExtension.snd h
    simp only [CocycleExtension.mul_snd, CocycleExtension.one_snd] at hsnd
    have hXs : ∀ n : ℕ, (X ^ n).snd = s₁ ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero, pow_zero]; rfl
      | succ n ih => rw [pow_succ, CocycleExtension.mul_snd, ih, pow_succ]
    have hYs : ∀ n : ℕ, (Y ^ n).snd = s₂ ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero, pow_zero]; rfl
      | succ n ih => rw [pow_succ, CocycleExtension.mul_snd, ih, pow_succ]
    have hCs : ∀ n : ℕ, (C ^ n).snd = 1 := fun n => by
      induction n with
      | zero => rw [pow_zero]; rfl
      | succ n ih => rw [pow_succ, CocycleExtension.mul_snd, ih, one_mul]
    rw [hXs, hYs, hCs, mul_one] at hsnd
    rcases hval a with rfl | rfl <;> rcases hval b with rfl | rfl
    · refine ⟨rfl, rfl, ?_⟩
      rw [ZMod.val_zero, pow_zero, pow_zero, one_mul, one_mul] at h
      rcases hval d with rfl | rfl
      · rfl
      · exfalso
        rw [ZMod.val_one, pow_one, hC] at h
        exact CocycleExtension.mk_one_one_ne_one h
    · exfalso
      rw [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul] at hsnd
      exact h2 hsnd
    · exfalso
      rw [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, mul_one] at hsnd
      exact h1 hsnd
    · exfalso
      rw [ZMod.val_one, pow_one, pow_one] at hsnd
      exact h3 hsnd
  refine Sec4.Census.three_le_pRank_of_involutions (x := ψ X) (y := ψ Y) (c := ψ C)
    (by rw [← map_mul, hXX, map_one]) (by rw [← map_mul, hYY, map_one])
    (by rw [← map_mul, hCC, map_one]) (by rw [← map_mul, hXYc, map_mul])
    (by rw [← map_mul, ← hCc X, map_mul]) (by rw [← map_mul, ← hCc Y, map_mul]) ?_
  intro a b d h
  refine hind a b d (hψ ?_)
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, h, map_one]

end Cocycle

section Center

variable {J : Type} [Group J] [Finite J]

theorem exists_eq_zpowers_of_card_le_two {Z : Subgroup J} (hZ1 : Z ≠ ⊥)
    (hZ2 : Nat.card Z ≤ 2) : ∃ t : J, orderOf t = 2 ∧ Z = Subgroup.zpowers t := by
  obtain ⟨t, htZ, ht1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left hZ1
  have hcard : Nat.card Z = 2 := by
    have h1 : 1 < Nat.card Z := by
      have : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZ1
      exact Finite.one_lt_card
    omega
  have hord : orderOf t = 2 := by
    have hd : orderOf t ∣ 2 := by
      rw [← hcard, ← Subgroup.orderOf_mk t htZ]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  refine ⟨t, hord, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htZ) ?_).symm
  rw [hcard, Nat.card_zpowers, hord]

omit [Finite J] in
theorem ker_comp_mk' {X : Type*} [Group X] (e : J ⧸ Subgroup.center J ≃* X) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))).ker = Subgroup.center J := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk x) = 1 ↔ _
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

end Center

section M12

open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow

variable {J : Type} [Group J] [Finite J]

theorem three_le_pRank_of_m12_cover
    (hq : IsQuasisimple J) (hZ2 : IsPGroup 2 (Subgroup.center J))
    (hZ1 : Subgroup.center J ≠ ⊥)
    (e : J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.M12) :
    3 ≤ CFSG.pRank 2 J := by
  have hEq : CFSG.Assembly.IsQuasisimple J := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
  have hle := CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound J
    hEq hZ2 (Or.inl ⟨e⟩)
  obtain ⟨t, ht, hZ⟩ := exists_eq_zpowers_of_card_le_two hZ1 hle
  set ρ : J →* CFSG.Blueprint.NativeSporadic.M12 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J)) with hρdef
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.zpowers t := by rw [hρdef, ker_comp_mk', hZ]
  have : Group.IsPerfect J := hq.1
  have hπ : IsCentralDoubleExt ρ t := ⟨hρ, hZ ▸ Subgroup.mem_zpowers t, ht, hker⟩
  obtain ⟨-, h4, h0⟩ := m12_double_cover_involution_lift_orders hEq ht hZ ρ hρ hker
  obtain ⟨ι, -, -, -⟩ := exists_local_coordinates hπ h4 (fun v hv hv0 => (h0 v hv hv0).1)
  have hm11 : mTab 1 1 = 0 := by decide +kernel
  have hm22 : mTab 2 2 = 0 := by decide +kernel
  have hm12 : mTab 1 2 = 3 := by decide +kernel
  have hm21 : mTab 2 1 = 3 := by decide +kernel
  have hf11 : fIdx ((1 : Fin 64) : ℕ) ((1 : Fin 64) : ℕ) = 0 := by decide +kernel
  have hf22 : fIdx ((2 : Fin 64) : ℕ) ((2 : Fin 64) : ℕ) = 0 := by decide +kernel
  have hf33 : fIdx ((3 : Fin 64) : ℕ) ((3 : Fin 64) : ℕ) = 0 := by decide +kernel
  have hd : ∀ i j : Fin 64, d i * d j = d (mTab i j) := fun i j => (d_mul i j).symm
  have hne : ∀ i : Fin 64, i ≠ 0 → d i ≠ 1 := fun i hi h =>
    hi (d_injective (h.trans d_zero.symm))
  refine three_le_pRank_of_cocycle
    ((Subgroup.comap ρ InternalSylow.S).subtype.comp ι.symm.toMonoidHom)
    (Subtype.val_injective.comp ι.symm.injective) (s₁ := d 1) (s₂ := d 2)
    (by rw [hd, hm11, d_zero]) (by rw [hd, hm22, d_zero]) (by rw [hd, hd, hm12, hm21])
    (hne 1 (by decide)) (hne 2 (by decide)) (by rw [hd, hm12]; exact hne 3 (by decide))
    ?_ ?_ ?_
  · rw [fN_apply, f_d, hf11]; rfl
  · rw [fN_apply, f_d, hf22]; rfl
  · rw [hd, hm12, fN_apply, f_d, hf33]; rfl

end M12

section J2

open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Models

variable {J : Type} [Group J] [Finite J]

theorem fCoc_elt_self_of_conjOf
    {a : ℕ} (ha : a < 128) (ha0 : a ≠ 0) (haa : mulIdx a a = 0) (hc : (conjOf a).1 = 4) :
    fCoc (elt a) (elt a) = 0 := by
  have hmt : (mulTab[a]!)[a]! = 0 := by rw [mulTab_get ha ha, haa]
  obtain ⟨hcase, -⟩ := involCheck_parts.2.2 a ha ha0 hmt
  rw [fCoc, tbl_elt _ ha ha]
  rcases hcase with ⟨-, -, hb⟩ | ⟨hc2, -, -⟩
  · rw [hb]
    rfl
  · rw [hc] at hc2
    exact absurd hc2 (by norm_num)

theorem three_le_pRank_of_j2_cover
    (hq : IsQuasisimple J) (hZ2 : IsPGroup 2 (Subgroup.center J))
    (hZ1 : Subgroup.center J ≠ ⊥)
    (e : J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.J2) :
    3 ≤ CFSG.pRank 2 J := by
  have hEq : CFSG.Assembly.IsQuasisimple J := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
  have hle := CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound J
    hEq hZ2 (Or.inr ⟨e⟩)
  obtain ⟨t, ht, hZ⟩ := exists_eq_zpowers_of_card_le_two hZ1 hle
  let eP : CFSG.Blueprint.NativeSporadic.J2 ≃* Models.P := nativeEquivP.trans Lift.toModels
  set ρ : J →* Models.P :=
    (e.trans eP).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J)) with hρdef
  have hρ : Function.Surjective ρ := (e.trans eP).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.zpowers t := by rw [hρdef, ker_comp_mk', hZ]
  have : Group.IsPerfect J := hq.1
  have hπ : IsCentralDoubleExt ρ t := ⟨hρ, hZ ▸ Subgroup.mem_zpowers t, ht, hker⟩
  obtain ⟨ι, -, -, -⟩ := exists_local_coordinates_of_finite hπ
  have h44 : mulIdx 4 4 = 0 := by decide +kernel
  have h4646 : mulIdx 46 46 = 0 := by decide +kernel
  have h446 : mulIdx 4 46 = 108 := by decide +kernel
  have h464 : mulIdx 46 4 = 108 := by decide +kernel
  have h108 : mulIdx 108 108 = 0 := by decide +kernel
  have hc46 : (conjOf 46).1 = 4 := by decide +kernel
  have hc108 : (conjOf 108).1 = 4 := by decide +kernel
  have hmul : ∀ {a b : ℕ}, b < 128 → elt a * elt b = elt (mulIdx a b) := fun hb =>
    (mulIdx_spec hb).2.symm
  have hne : ∀ {a : ℕ}, a < 128 → a ≠ 0 → eS.symm (elt a) ≠ 1 := by
    intro a ha ha0 h
    have h' : elt a = elt 0 := by
      rw [elt_zero]
      exact (MulEquiv.map_eq_one_iff eS.symm).mp h
    exact ha0 (elt_injective ha (by norm_num) h')
  have hmulS : ∀ {a b : ℕ}, b < 128 →
      eS.symm (elt a) * eS.symm (elt b) = eS.symm (elt (mulIdx a b)) := by
    intro a b hb
    rw [← map_mul, hmul hb]
  have hfN : ∀ {a : ℕ}, a < 128 → a ≠ 0 → mulIdx a a = 0 → (conjOf a).1 = 4 →
      fN (eS.symm (elt a)) (eS.symm (elt a)) = 0 := by
    intro a ha ha0 haa hc
    rw [fN_apply, MulEquiv.apply_symm_apply]
    exact fCoc_elt_self_of_conjOf ha ha0 haa hc
  refine three_le_pRank_of_cocycle ((Subgroup.comap ρ Sp).subtype.comp ι.symm.toMonoidHom)
    (Subtype.val_injective.comp ι.symm.injective) (s₁ := eS.symm (elt 4))
    (s₂ := eS.symm (elt 46)) ?_ ?_ ?_ (hne (by norm_num) (by norm_num))
    (hne (by norm_num) (by norm_num)) ?_ Lift.fN_elt_four
    (hfN (by norm_num) (by norm_num) h4646 hc46) ?_
  · rw [hmulS (by norm_num), h44, elt_zero, map_one]
  · rw [hmulS (by norm_num), h4646, elt_zero, map_one]
  · rw [hmulS (by norm_num), hmulS (by norm_num), h446, h464]
  · rw [hmulS (by norm_num), h446]
    exact hne (by norm_num) (by norm_num)
  · rw [hmulS (by norm_num), h446]
    exact hfN (by norm_num) (by norm_num) h108 hc108

end J2

end CFSG.RankThree.PartTwo.Sec13.KS135Cover
