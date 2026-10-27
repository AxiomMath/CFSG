module

public import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusFix
public import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusRoot
public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusNorm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs

public section

namespace CFSG.StandardType.KGPosOm

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted QuadraticMap
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CurtisTits CFSG.SeitzReduction.SymplecticPilot
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Open
open scoped Matrix

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1)

@[expose] noncomputable def omTorus :
    (Fin 3 → Multiplicative (ZMod p)) →* spinGroup (quadMinus 4 F b c) :=
  (peRhoMEquiv (by decide : 4 ≤ 4) hirr).symm.toMonoidHom.comp (omMinusTorus b c hζ (m := 3))

theorem spinAction_omTorus (u : Fin 3 → Multiplicative (ZMod p)) (v : Vm 4 F) :
    spinAction (quadMinus 4 F b c) (omTorus hirr hζ u) v =
      fun a => kOmMWeight F 3 (omMinusTorusParam 3 hζ u) a * v a := by
  have hmat : spinMatrix (quadMinus 4 F b c) (omTorus hirr hζ u) = omMinusTorusGL hζ u :=
    congrArg (fun A : StatedOmega (StatedQuadMinus 4 F b c) =>
      (A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F))
      ((peRhoMEquiv (by decide : 4 ≤ 4) hirr).apply_symm_apply (omMinusTorus b c hζ u))
  rw [← spinMatrix_mulVec, hmat, omMinusTorusGL_apply, kOmMDiag_coe]
  funext a
  exact Matrix.mulVec_diagonal _ _ _

omit [Finite F] [CharP F 2] in
theorem apply_eq_zero_of_commute {g t : spinGroup (quadMinus 4 F b c)} (hc : g * t = t * g)
    {d : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F}
    (ht : ∀ v, spinAction (quadMinus 4 F b c) t v = fun a => d a * v a) {v : Vm 4 F} {l : F}
    (hv : ∀ a, d a * v a = l * v a) {a : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2} (ha : d a ≠ l) :
    spinAction (quadMinus 4 F b c) g v a = 0 := by
  have h := congrArg (fun x => spinAction (quadMinus 4 F b c) x v) hc
  simp only [map_mul, LinearEquiv.mul_apply] at h
  have htv : spinAction (quadMinus 4 F b c) t v = l • v := by
    rw [ht]
    funext a'
    rw [hv]
    rfl
  rw [htv, map_smul, ht] at h
  have h' := congrFun h a
  simp only [Pi.smul_apply, smul_eq_mul] at h'
  have h0 : (d a - l) * spinAction (quadMinus 4 F b c) g v a = 0 := by
    rw [sub_mul, ← h', sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr ha)

variable (p) in
@[expose] def omVec (S : Finset (Fin 3)) : Fin 3 → Multiplicative (ZMod p) :=
  fun j => Multiplicative.ofAdd (((if j ∈ S then 1 else 0 : ℕ)) : ZMod p)

@[expose] def omExp (S : Finset (Fin 3)) : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ℤ :=
  Sum.elim (fun j => if j ∈ S then 1 else 0)
    (Sum.elim (fun j => if j ∈ S then -1 else 0) fun _ => 0)

theorem omExp_bound (S : Finset (Fin 3)) (a : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) :
    -1 ≤ omExp S a ∧ omExp S a ≤ 1 := by
  rcases a with j | j | t <;> simp only [omExp, Sum.elim_inl, Sum.elim_inr] <;>
    (try split_ifs) <;> decide

omit [Finite F] [CharP F 2] in
theorem kOmMWeight_omVec (S : Finset (Fin 3)) (a : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) :
    kOmMWeight F 3 (omMinusTorusParam 3 hζ (omVec p S)) a = (ζ : F) ^ omExp S a := by
  rcases a with j | j | t
  · simp only [kOmMWeight_inl, omMinusTorusParam_apply, omVec, TableBSymp.zmodPowHom_natCast,
      omExp, Sum.elim_inl]
    split_ifs <;> simp
  · simp only [kOmMWeight_inr_inl, omMinusTorusParam_apply, omVec, TableBSymp.zmodPowHom_natCast,
      omExp, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp
  · simp only [omExp, Sum.elim_inr, zpow_zero]
    rfl

theorem omExp_eq_of_commute (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    {g : spinGroup (quadMinus 4 F b c)} {S : Finset (Fin 3)}
    (hc : g * omTorus hirr hζ (omVec p S) = omTorus hirr hζ (omVec p S) * g)
    {a a' : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2}
    (h : spinAction (quadMinus 4 F b c) g (Pi.single a' 1) a ≠ 0) : omExp S a = omExp S a' := by
  by_contra hne
  apply h
  have hζF : (ζ : F) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  have hζ1 : (ζ : F) ≠ 1 := fun h1 => by
    have : ζ = 1 := Units.ext h1
    rw [this, orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  refine apply_eq_zero_of_commute hc (spinAction_omTorus hirr hζ _)
    (l := (ζ : F) ^ omExp S a') (fun x => ?_) ?_
  · by_cases hx : x = a'
    · rw [hx, kOmMWeight_omVec]
    · rw [Pi.single_eq_of_ne hx, mul_zero, mul_zero]
  · rw [kOmMWeight_omVec]
    intro heq
    have h0 : (ζ : F) ≠ 0 := Units.ne_zero ζ
    have h1 : (ζ : F) ^ (omExp S a - omExp S a') = 1 := by
      rw [zpow_sub₀ h0, heq, div_self (zpow_ne_zero _ h0)]
    have hb := omExp_bound S a
    have hb' := omExp_bound S a'
    exact KGPosSU.zpow_ne_one_of_pow_eq_one hp hp2 hζF hζ1 (sub_ne_zero.mpr hne) (by omega)
      (by omega) h1

end Torus

section Centralize

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1)

include hirr in
theorem commute_of_eichler {t x : spinGroup (quadMinus 4 F b c)} {v₁ v₂ : Vm 4 F}
    (hx : spinAction (quadMinus 4 F b c) x = eichler (quadMinus 4 F b c) v₁ v₂) {μ : Fˣ}
    (h₁ : spinAction (quadMinus 4 F b c) t v₁ = (μ : F) • v₁)
    (h₂ : spinAction (quadMinus 4 F b c) t v₂ = ((μ⁻¹ : Fˣ) : F) • v₂) : t * x = x * t := by
  have hO : spinAction (quadMinus 4 F b c) t ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ t)
  have h : t * x * t⁻¹ = x := by
    apply RootCentOmega.spinAction_quadMinus_injective hirr
    rw [map_mul, map_mul, map_inv, hx, eichler_conj hO, h₁, h₂, eichler_smul_left, smul_smul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  calc t * x = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [h]

include hirr in
theorem rankOne_le_centralizer_long {k : Fin (4 - 1)} (hk : k.val + 1 < 4 - 1)
    {u : Fin 3 → Multiplicative (ZMod p)} (hu : u k = u ⟨k.val + 1, hk⟩) :
    rankOne (minusRootGroup 4 hirr) k ≤ Subgroup.centralizer {omTorus hirr hζ u} := by
  have hkj := succ_ne_of_lt 4 hk
  set w := omMinusTorusParam 3 hζ u with hw
  have hwk : w k = w ⟨k.val + 1, hk⟩ := by rw [hw, omMinusTorusParam_apply,
    omMinusTorusParam_apply, hu]
  have he : ∀ i : Fin (4 - 1), spinAction (quadMinus 4 F b c) (omTorus hirr hζ u)
      (minusVec 4 i true) = ((w i : Fˣ) : F) • minusVec 4 i true := fun i => by
    rw [spinAction_omTorus]
    funext a
    rcases a with i' | i' | t
    · by_cases h : i' = i
      · subst h
        simp only [minusVec, eVec, Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul]
        rfl
      · simp [minusVec, eVec, h]
    · simp [minusVec, eVec]
    · simp [minusVec, eVec]
  have hf : ∀ i : Fin (4 - 1), spinAction (quadMinus 4 F b c) (omTorus hirr hζ u)
      (minusVec 4 i false) = (((w i)⁻¹ : Fˣ) : F) • minusVec 4 i false := fun i => by
    rw [spinAction_omTorus]
    funext a
    rcases a with i' | i' | t
    · simp [minusVec, fVec]
    · by_cases h : i' = i
      · subst h
        simp only [minusVec, fVec, Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul]
        rfl
      · simp [minusVec, fVec, h]
    · simp [minusVec, fVec]
  have key : ∀ (i j : Fin (4 - 1)) (hij : i ≠ j), w i = w j → ∀ a : F,
      omTorus hirr hζ u * (minusFrame 4 b c).longRoot hij true false (.ofAdd a) =
        (minusFrame 4 b c).longRoot hij true false (.ofAdd a) * omTorus hirr hζ u := by
    intro i j hij hij' a
    refine commute_of_eichler hirr
      ((minusFrame 4 b c).toHypFrame.spinAction_longRoot_eq_eichler hij true false a)
      (μ := (w j)⁻¹) (hf j) ?_
    rw [map_smul, show (minusFrame 4 b c).vec i true = minusVec 4 i true from rfl, he i,
      smul_comm, inv_inv, hij']
  rw [rankOne, minusRootGroup_single_of_lt 4 hirr hk, minusRootGroup_neg_single_of_lt 4 hirr hk]
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (key _ _ hkj hwk (Multiplicative.toAdd a)).symm
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (key _ _ hkj.symm hwk.symm (Multiplicative.toAdd a)).symm

include hirr in
theorem rankOne_le_centralizer_short {u : Fin 3 → Multiplicative (ZMod p)} (hu : u 2 = 1) :
    rankOne (minusRootGroup 4 hirr) ⟨2, by decide⟩ ≤ Subgroup.centralizer {omTorus hirr hζ u} := by
  have hw : omMinusTorusParam 3 hζ u 2 = 1 := by rw [omMinusTorusParam_apply, hu, map_one]
  have hfix : ∀ v : Vm 4 F, (∀ a, v a ≠ 0 →
      a = .inl ⟨2, by decide⟩ ∨ a = .inr (.inl ⟨2, by decide⟩) ∨ ∃ t, a = .inr (.inr t)) →
      spinAction (quadMinus 4 F b c) (omTorus hirr hζ u) v = v := by
    intro v hv
    rw [spinAction_omTorus]
    funext a
    by_cases h0 : v a = 0
    · rw [h0, mul_zero]
    rcases hv a h0 with rfl | rfl | ⟨t, rfl⟩
    · rw [kOmMWeight_inl]
      change ((omMinusTorusParam 3 hζ u 2 : Fˣ) : F) * _ = _
      rw [hw, Units.val_one, one_mul]
    · rw [kOmMWeight_inr_inl]
      change (((omMinusTorusParam 3 hζ u 2)⁻¹ : Fˣ) : F) * _ = _
      rw [hw, inv_one, Units.val_one, one_mul]
    · rw [kOmMWeight_inr_inr, one_mul]
  have key : ∀ (s : Bool) (q : Fin 2 → F), omTorus hirr hζ u * twShortRoot 4 hirr ⟨2, by decide⟩ s
      (.ofAdd q) = twShortRoot 4 hirr ⟨2, by decide⟩ s (.ofAdd q) * omTorus hirr hζ u := by
    intro s q
    refine commute_of_eichler hirr (spinAction_twShortRoot_eq_eichler 4 hirr _ s q) (μ := 1)
      ?_ ?_
    · rw [Units.val_one, one_smul]
      refine hfix _ fun a ha => ?_
      cases s
      · right; left
        by_contra h
        exact ha (Pi.single_eq_of_ne h 1)
      · left
        by_contra h
        exact ha (Pi.single_eq_of_ne h 1)
    · rw [inv_one, Units.val_one, one_smul]
      refine hfix _ fun a ha => ?_
      right; right
      rcases a with i | i | t
      · exact absurd rfl ha
      · exact absurd rfl ha
      · exact ⟨t, rfl⟩
  rw [rankOne_minusRootGroup_of_not_lt 4 hirr (by decide)]
  refine sup_le ?_ ?_
  · rintro _ ⟨q, rfl⟩
    rw [← twShortRoot_true]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (key true (Multiplicative.toAdd q)).symm
  · rintro _ ⟨q, rfl⟩
    rw [← twShortRoot_false]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (key false (Multiplicative.toAdd q)).symm

end Centralize

section Block

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1)

omit [Finite F] [CharP F 2] in
theorem eq_of_support_pair {x : Vm 4 F} {a₁ a₂ : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2}
    (h12 : a₁ ≠ a₂) (hx : ∀ a, x a ≠ 0 → a = a₁ ∨ a = a₂) :
    x = x a₁ • Pi.single a₁ 1 + x a₂ • Pi.single a₂ 1 := by
  funext a
  by_cases h1 : a = a₁
  · subst h1
    simp [h12]
  by_cases h2 : a = a₂
  · subst h2
    simp [h1]
  have h0 : x a = 0 := by
    by_contra h
    rcases hx a h with h' | h'
    · exact h1 h'
    · exact h2 h'
  simp [h1, h2, h0]

omit [Finite F] [CharP F 2] in
theorem eq_of_support_single {x : Vm 4 F} {a₁ : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2}
    (hx : ∀ a, x a ≠ 0 → a = a₁) : x = x a₁ • Pi.single a₁ 1 := by
  funext a
  by_cases h1 : a = a₁
  · subst h1
    simp
  have h0 : x a = 0 := by
    by_contra h
    exact h1 (hx a h)
  simp [h1, h0]

omit [Finite F] [CharP F 2] in
theorem eq_planeVec_of_support {x : Vm 4 F} (hx : ∀ a, x a ≠ 0 → ∃ t, a = .inr (.inr t)) :
    x = planeVec 4 fun t => x (.inr (.inr t)) := by
  funext a
  rcases a with i | i | t
  · by_contra h
    obtain ⟨t, ht⟩ := hx _ fun h0 => h (by rw [h0]; rfl)
    exact Sum.inl_ne_inr ht
  · by_contra h
    obtain ⟨t, ht⟩ := hx _ fun h0 => h (by rw [h0]; rfl)
    exact Sum.inl_ne_inr (Sum.inr_injective ht)
  · rfl

omit [Finite F] [CharP F 2] in
theorem planeVec_eq_add (q : Fin 2 → F) :
    planeVec 4 q = q 0 • Pi.single (.inr (.inr 0)) 1 + q 1 • Pi.single (.inr (.inr 1)) 1 := by
  funext a
  rcases a with i | i | t
  · simp [planeVec]
  · simp [planeVec]
  · fin_cases t <;> simp [planeVec]

omit [Finite F] in
theorem eq_one_of_smul {g : spinGroup (quadMinus 4 F b c)} {v : Vm 4 F} (hv0 : v ≠ 0) {a : F}
    (hgv : spinAction (quadMinus 4 F b c) g v = a • v) {N : ℕ} (hN : g ^ (2 ^ N) = 1) : a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ∀ n, spinAction (quadMinus 4 F b c) (g ^ n) v = a ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, LinearEquiv.mul_apply, hgv, map_smul, ih, smul_smul,
        pow_succ, mul_comm]
  have h := hn (2 ^ N)
  rw [hN, map_one] at h
  change v = _ at h
  have h1 : a ^ (2 ^ N) = 1 := by
    by_contra hne
    apply hv0
    have h' : (a ^ (2 ^ N) - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have h2 := sub_pow_char_pow a 1 (p := 2) (n := N)
  rw [h1, one_pow, sub_self] at h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h2)

include hirr hζ in
theorem mem_rankOne_of_commute_long (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    {k : Fin (4 - 1)} (hk : k.val + 1 < 4 - 1) (m : Fin (4 - 1)) {S₁ S₂ : Finset (Fin 3)}
    (hm3 : ∀ m' : Fin (4 - 1), m' ≠ k → m' ≠ ⟨k.val + 1, hk⟩ → m' = m)
    (he₁ : ∀ a, omExp S₁ a = omExp S₁ (.inl k) → a = .inl k ∨ a = .inl ⟨k.val + 1, hk⟩)
    (he₂ : ∀ a, omExp S₁ a = omExp S₁ (.inl ⟨k.val + 1, hk⟩) →
      a = .inl k ∨ a = .inl ⟨k.val + 1, hk⟩)
    (hf₁ : ∀ a, omExp S₁ a = omExp S₁ (.inr (.inl k)) →
      a = .inr (.inl k) ∨ a = .inr (.inl ⟨k.val + 1, hk⟩))
    (hf₂ : ∀ a, omExp S₁ a = omExp S₁ (.inr (.inl ⟨k.val + 1, hk⟩)) →
      a = .inr (.inl k) ∨ a = .inr (.inl ⟨k.val + 1, hk⟩))
    (hme : ∀ a, omExp S₂ a = omExp S₂ (.inl m) → a = .inl m)
    (hmf : ∀ a, omExp S₂ a = omExp S₂ (.inr (.inl m)) → a = .inr (.inl m))
    (hpl : ∀ (t : Fin 2) a, omExp S₁ a = omExp S₁ (.inr (.inr t)) →
      omExp S₂ a = omExp S₂ (.inr (.inr t)) → ∃ t', a = .inr (.inr t'))
    {g : spinGroup (quadMinus 4 F b c)}
    (h₁ : g * omTorus hirr hζ (omVec p S₁) = omTorus hirr hζ (omVec p S₁) * g)
    (h₂ : g * omTorus hirr hζ (omVec p S₂) = omTorus hirr hζ (omVec p S₂) * g)
    {N : ℕ} (hN : g ^ (2 ^ N) = 1) : g ∈ rankOne (minusRootGroup 4 hirr) k := by
  set j : Fin (4 - 1) := ⟨k.val + 1, hk⟩ with hj
  have hkj : k ≠ j := succ_ne_of_lt 4 hk
  have hsep := fun {S} (hc : g * omTorus hirr hζ (omVec p S) = omTorus hirr hζ (omVec p S) * g)
    {a a'} (h : spinAction (quadMinus 4 F b c) g (Pi.single a' 1) a ≠ 0) =>
    omExp_eq_of_commute hirr hζ hp hp2 hζo hc h
  have hge : ∀ i, i = k ∨ i = j → spinAction (quadMinus 4 F b c) g (minusVec 4 i true) =
      spinAction (quadMinus 4 F b c) g (minusVec 4 i true) (.inl k) • minusVec 4 k true +
      spinAction (quadMinus 4 F b c) g (minusVec 4 i true) (.inl j) • minusVec 4 j true := by
    intro i hi
    refine eq_of_support_pair (fun h => hkj (Sum.inl_injective h)) fun a ha => ?_
    rcases hi with rfl | rfl
    · exact he₁ a (hsep h₁ ha)
    · exact he₂ a (hsep h₁ ha)
  have hgf : ∀ i, i = k ∨ i = j → spinAction (quadMinus 4 F b c) g (minusVec 4 i false) =
      spinAction (quadMinus 4 F b c) g (minusVec 4 i false) (.inr (.inl k)) • minusVec 4 k false +
      spinAction (quadMinus 4 F b c) g (minusVec 4 i false) (.inr (.inl j)) •
        minusVec 4 j false := by
    intro i hi
    refine eq_of_support_pair (fun h => hkj (Sum.inl_injective (Sum.inr_injective h)))
      fun a ha => ?_
    rcases hi with rfl | rfl
    · exact hf₁ a (hsep h₁ ha)
    · exact hf₂ a (hsep h₁ ha)
  have hgm : ∀ u, spinAction (quadMinus 4 F b c) g (minusVec 4 m u) = minusVec 4 m u := by
    intro u
    have hx : spinAction (quadMinus 4 F b c) g (minusVec 4 m u) =
        spinAction (quadMinus 4 F b c) g (minusVec 4 m u) (cond u (.inl m) (.inr (.inl m))) •
          minusVec 4 m u := by
      cases u
      · exact eq_of_support_single fun a ha => hmf a (hsep h₂ ha)
      · exact eq_of_support_single fun a ha => hme a (hsep h₂ ha)
    have h0 : minusVec 4 m u ≠ (0 : Vm 4 F) := fun h => by
      have := congrFun h (cond u (.inl m) (.inr (.inl m)))
      cases u <;> simp [minusVec, eVec, fVec] at this
    rw [hx, eq_one_of_smul h0 hx hN, one_smul]
  let A : Matrix (Fin 2) (Fin 2) F :=
    !![spinAction (quadMinus 4 F b c) g (minusVec 4 k true) (.inl k),
      spinAction (quadMinus 4 F b c) g (minusVec 4 j true) (.inl k);
      spinAction (quadMinus 4 F b c) g (minusVec 4 k true) (.inl j),
      spinAction (quadMinus 4 F b c) g (minusVec 4 j true) (.inl j)]
  refine mem_rankOne_long_of_block hirr hk A (fun v => ?_) (fun v => ?_) (fun m' hmk hmj u => ?_)
    (fun q => ?_) hN
  · rw [pairVec, map_add, map_smul, map_smul, hge k (Or.inl rfl), hge j (Or.inr rfl)]
    simp only [pairVec, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    module
  · obtain ⟨α, γ, hα⟩ : ∃ α γ : F, spinAction (quadMinus 4 F b c) g (minusVec 4 k false) =
        α • minusVec 4 k false + γ • minusVec 4 j false := ⟨_, _, hgf k (Or.inl rfl)⟩
    obtain ⟨β, δ, hβ⟩ : ∃ β δ : F, spinAction (quadMinus 4 F b c) g (minusVec 4 j false) =
        β • minusVec 4 k false + δ • minusVec 4 j false := ⟨_, _, hgf j (Or.inr rfl)⟩
    refine ⟨![v 0 * α + v 1 * β, v 0 * γ + v 1 * δ], ?_⟩
    rw [pairVec, map_add, map_smul, map_smul, hα, hβ]
    simp only [pairVec, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · rw [hm3 m' hmk hmj]
    exact hgm u
  · have hP : ∀ t : Fin 2, ∃ w : Fin 2 → F,
        spinAction (quadMinus 4 F b c) g (Pi.single (.inr (.inr t)) 1) = planeVec 4 w := fun t =>
      ⟨_, eq_planeVec_of_support fun a ha => hpl t a (hsep h₁ ha) (hsep h₂ ha)⟩
    obtain ⟨w₀, hw₀⟩ := hP 0
    obtain ⟨w₁, hw₁⟩ := hP 1
    refine ⟨q 0 • w₀ + q 1 • w₁, ?_⟩
    rw [planeVec_eq_add, map_add, map_smul, map_smul, hw₀, hw₁, planeVec_add, planeVec_smul,
      planeVec_smul]

include hirr hζ in
theorem mem_rankOne_of_commute_short (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    {g : spinGroup (quadMinus 4 F b c)}
    (h₁ : g * omTorus hirr hζ (omVec p {0}) = omTorus hirr hζ (omVec p {0}) * g)
    (h₂ : g * omTorus hirr hζ (omVec p {1}) = omTorus hirr hζ (omVec p {1}) * g)
    {N : ℕ} (hN : g ^ (2 ^ N) = 1) : g ∈ rankOne (minusRootGroup 4 hirr) ⟨2, by decide⟩ := by
  have hsep := fun {S} (hc : g * omTorus hirr hζ (omVec p S) = omTorus hirr hζ (omVec p S) * g)
    {a a'} (h : spinAction (quadMinus 4 F b c) g (Pi.single a' 1) a ≠ 0) =>
    omExp_eq_of_commute hirr hζ hp hp2 hζo hc h
  refine mem_rankOne_short_of_fix hirr fun i hi u => ?_
  have hi01 : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    obtain ⟨i, hi'⟩ := i
    simp only at hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hfix1 : ∀ (S : Finset (Fin 3)) (a' : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2),
      g * omTorus hirr hζ (omVec p S) = omTorus hirr hζ (omVec p S) * g →
      (∀ a, omExp S a = omExp S a' → a = a') →
      spinAction (quadMinus 4 F b c) g (Pi.single a' 1) = Pi.single a' 1 := by
    intro S a' hc hcl
    have hx : spinAction (quadMinus 4 F b c) g (Pi.single a' 1) =
        spinAction (quadMinus 4 F b c) g (Pi.single a' 1) a' • Pi.single a' 1 :=
      eq_of_support_single fun a ha => hcl a (hsep hc ha)
    have h0 : (Pi.single a' 1 : Vm 4 F) ≠ 0 := fun h => by simpa using congrFun h a'
    rw [hx, eq_one_of_smul h0 hx hN, one_smul]
  rcases hi01 with rfl | rfl <;> cases u
  · exact hfix1 {0} (.inr (.inl ⟨0, by decide⟩)) h₁ (by decide)
  · exact hfix1 {0} (.inl ⟨0, by decide⟩) h₁ (by decide)
  · exact hfix1 {1} (.inr (.inl ⟨1, by decide⟩)) h₂ (by decide)
  · exact hfix1 {1} (.inl ⟨1, by decide⟩) h₂ (by decide)

end Block

section Fix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1)
  {ν : GGWeyl (minusDatum 4 hirr) →* spinGroup (quadMinus 4 F b c)}

variable (p) in
@[expose] def omChar (i : Fin (4 - 1)) :
    (Fin 3 → Multiplicative (ZMod p)) →* Multiplicative (ZMod p) where
  toFun u := if h : i.val + 1 < 4 - 1 then u i / u ⟨i.val + 1, h⟩ else u 2
  map_one' := by split_ifs <;> simp
  map_mul' u u' := by split_ifs <;> simp [mul_div_mul_comm]

include hirr hζ in
theorem rankOne_le_centralizer_of_omChar (i : Fin (4 - 1))
    {u : Fin 3 → Multiplicative (ZMod p)} (hu : omChar p i u = 1) :
    rankOne (minusRootGroup 4 hirr) i ≤ Subgroup.centralizer {omTorus hirr hζ u} := by
  change (if h : i.val + 1 < 4 - 1 then u i / u ⟨i.val + 1, h⟩ else u 2) = 1 at hu
  split_ifs at hu with hk
  · exact rankOne_le_centralizer_long hirr hζ hk (div_eq_one.mp hu)
  · have hi : i = ⟨2, by decide⟩ := by
      obtain ⟨i, hi⟩ := i
      simp only [Fin.mk.injEq]
      simp only at hk
      omega
    subst hi
    exact rankOne_le_centralizer_short hirr hζ hu

omit [CharP F 2] in
include hirr in
theorem not_mem_ggTorus (hν : GGWeylLift (minusDatum 4 hirr) ν) (i : Fin (4 - 1)) :
    ν ((coxeterMatrix (minusDatum 4 hirr).isFiniteType).toCoxeterSystem.simple i) ∉
      ggTorus (minusDatum 4 hirr) := by
  intro hT
  have hext := minusDatum_steinbergExtras 4 hirr
  have hα : Pi.single i 1 ∈ (minusDatum 4 hirr).roots :=
    (isCTRootSystem (minusDatum 4 hirr).isFiniteType (minusDatum 4 hirr).divisible).single_mem i
  have hN := mem_normalizer_iff_map_conj.mp
    (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hT (Pi.single i 1)) hα)
  have hact := ggStdPos_actsAs_weylLift hν
    ((coxeterMatrix (minusDatum 4 hirr).isFiniteType).toCoxeterSystem.simple i) _ hα
  have heq := hN.symm.trans (hact.trans (congrArg (minusDatum 4 hirr).rootGroup
    (weylAction_simple_single (minusDatum 4 hirr).isFiniteType i)))
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hext.ne_bot _ hα)
  refine hx1 (Subtype.ext (hext.eq_one_of_mem_normalizer i x x.2 ?_))
  rw [← heq]
  exact Subgroup.le_normalizer x.2

include hirr hζ in
theorem omChar_eq_one_of_commute (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    (hν : GGWeylLift (minusDatum 4 hirr) ν) (i : Fin (4 - 1))
    {u : Fin 3 → Multiplicative (ZMod p)}
    (hu : omTorus hirr hζ u * ν ((coxeterMatrix (minusDatum 4 hirr).isFiniteType).simple i) =
      ν ((coxeterMatrix (minusDatum 4 hirr).isFiniteType).simple i) * omTorus hirr hζ u) :
    omChar p i u = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set n := ν ((coxeterMatrix (minusDatum 4 hirr).isFiniteType).simple i) with hn
  have hnL : n ∈ rankOne (minusRootGroup 4 hirr) i := by
    have h := hν.simple_mem i
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at h
  by_contra h0
  apply not_mem_ggTorus hirr hν i
  rw [CoxeterMatrix.toCoxeterSystem_simple, ← hn]
  have hC : Subgroup.centralizer ((omTorus hirr hζ).range : Set (spinGroup (quadMinus 4 F b c))) =
      ggTorus (minusDatum 4 hirr) := centralizer_spinMinus_splitPrimeTorus hirr hp hp2 hζ hζo
  rw [← hC, Subgroup.mem_centralizer_iff]
  rintro _ ⟨u', rfl⟩
  have h0' : Multiplicative.toAdd (omChar p i u) ≠ 0 := fun h => h0 (Multiplicative.toAdd.injective h)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ZMod p) =
      Multiplicative.toAdd (omChar p i u') / Multiplicative.toAdd (omChar p i u) :=
    ⟨_, ZMod.natCast_zmod_val _⟩
  have hker : omChar p i (u' * (u ^ m)⁻¹) = 1 := by
    have h1 : omChar p i (u' * (u ^ m)⁻¹) * omChar p i (u ^ m) = omChar p i u' := by
      rw [← map_mul]
      exact congrArg _ (inv_mul_cancel_right u' (u ^ m))
    have h2 : omChar p i (u ^ m) = omChar p i u' := Multiplicative.toAdd.injective (by
      rw [map_pow, toAdd_pow, nsmul_eq_mul, hm, div_mul_cancel₀ _ h0'])
    rw [h2] at h1
    exact mul_eq_right.mp h1
  have hc1 := Subgroup.mem_centralizer_singleton_iff.mp
    (rankOne_le_centralizer_of_omChar hirr hζ i hker hnL)
  have hc2 : n * omTorus hirr hζ u = omTorus hirr hζ u * n := hu.symm
  have hc3 : n * omTorus hirr hζ (u ^ m) = omTorus hirr hζ (u ^ m) * n := by
    rw [map_pow]
    exact (Commute.pow_right hc2 m)
  have e : u' = u' * (u ^ m)⁻¹ * u ^ m := (inv_mul_cancel_right u' (u ^ m)).symm
  rw [e, map_mul]
  calc omTorus hirr hζ (u' * (u ^ m)⁻¹) * omTorus hirr hζ (u ^ m) * n
      = omTorus hirr hζ (u' * (u ^ m)⁻¹) * (n * omTorus hirr hζ (u ^ m)) := by rw [mul_assoc, hc3]
    _ = n * omTorus hirr hζ (u' * (u ^ m)⁻¹) * omTorus hirr hζ (u ^ m) := by
        rw [← mul_assoc, hc1]
    _ = n * (omTorus hirr hζ (u' * (u ^ m)⁻¹) * omTorus hirr hζ (u ^ m)) := by rw [mul_assoc]

omit [Finite F] in
theorem mul_self_eq_one_of_mem_rankOne_gen (i : Fin (4 - 1)) {x : spinGroup (quadMinus 4 F b c)}
    (hx : x ∈ minusRootGroup 4 hirr (Pi.single i 1) ∨
      x ∈ minusRootGroup 4 hirr (-Pi.single i 1)) : x * x = 1 := by
  have h2 : ∀ {A : Type} [AddCommGroup A] [Module F A] {G : Type} [Group G]
      (φ : Multiplicative A →* G) (z : Multiplicative A), φ z * φ z = 1 := by
    intro A _ _ G _ φ z
    rw [← map_mul, show z * z = 1 from Multiplicative.toAdd.injective (by
      rw [toAdd_mul, toAdd_one, ← two_smul F (Multiplicative.toAdd z), CharTwo.two_eq_zero,
        zero_smul]), map_one]
  by_cases hk : i.val + 1 < 4 - 1
  · rcases hx with hx | hx
    · rw [minusRootGroup_single_of_lt 4 hirr hk] at hx
      obtain ⟨z, rfl⟩ := hx
      exact h2 _ z
    · rw [minusRootGroup_neg_single_of_lt 4 hirr hk] at hx
      obtain ⟨z, rfl⟩ := hx
      exact h2 _ z
  · rcases hx with hx | hx
    · rw [minusRootGroup_single_of_not_lt 4 hirr hk] at hx
      obtain ⟨z, rfl⟩ := hx
      exact h2 _ z
    · rw [minusRootGroup_neg_single_of_not_lt 4 hirr hk] at hx
      obtain ⟨z, rfl⟩ := hx
      exact h2 _ z

include hζ in
theorem ggOTwoPrime_centralizer_omFix (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    (hν : GGWeylLift (minusDatum 4 hirr) ν) (i : Fin (4 - 1)) :
    ggOTwoPrime (Subgroup.centralizer (((omTorus hirr hζ).range ⊓ Subgroup.centralizer
      {ν ((coxeterMatrix (minusDatum 4 hirr).isFiniteType).simple i)} :
        Subgroup (spinGroup (quadMinus 4 F b c))) : Set (spinGroup (quadMinus 4 F b c)))) =
      rankOne (minusRootGroup 4 hirr) i := by
  set n := ν ((coxeterMatrix (minusDatum 4 hirr).isFiniteType).simple i) with hn
  have hnL : n ∈ rankOne (minusRootGroup 4 hirr) i := by
    have h := hν.simple_mem i
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at h
  have hE : ∀ u, omChar p i u = 1 → omTorus hirr hζ u ∈ (omTorus hirr hζ).range ⊓
      Subgroup.centralizer {n} := fun u hu =>
    ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp
        (rankOne_le_centralizer_of_omChar hirr hζ i hu hnL)).symm⟩
  have hLC : rankOne (minusRootGroup 4 hirr) i ≤ Subgroup.centralizer
      (((omTorus hirr hζ).range ⊓ Subgroup.centralizer {n} :
        Subgroup (spinGroup (quadMinus 4 F b c))) : Set (spinGroup (quadMinus 4 F b c))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨u, rfl⟩, hu⟩
    have hu' := omChar_eq_one_of_commute hirr hζ hp hp2 hζo hν i
      (Subgroup.mem_centralizer_singleton_iff.mp hu)
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (rankOne_le_centralizer_of_omChar hirr hζ i hu' hx)).symm
  apply le_antisymm
  · rw [ggOTwoPrime, Subgroup.closure_le]
    rintro y ⟨hy, N, hN⟩
    have hc : ∀ S : Finset (Fin 3), omChar p i (omVec p S) = 1 →
        y * omTorus hirr hζ (omVec p S) = omTorus hirr hζ (omVec p S) * y := fun S hS =>
      ((Subgroup.mem_centralizer_iff.mp hy) _ (hE _ hS)).symm
    have hi3 : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ := by
      obtain ⟨i, hi⟩ := i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases hi3 with rfl | rfl | rfl
    · exact mem_rankOne_of_commute_long hirr hζ hp hp2 hζo (k := ⟨0, by decide⟩) (by decide)
        ⟨2, by decide⟩ (S₁ := {0, 1}) (S₂ := {2}) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (hc _ (by simp [omChar, omVec])) (hc _ (by simp [omChar, omVec])) hN
    · exact mem_rankOne_of_commute_long hirr hζ hp hp2 hζo (k := ⟨1, by decide⟩) (by decide)
        ⟨0, by decide⟩ (S₁ := {1, 2}) (S₂ := {0}) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (hc _ (by simp [omChar, omVec])) (hc _ (by simp [omChar, omVec])) hN
    · exact mem_rankOne_of_commute_short hirr hζ hp hp2 hζo (hc _ (by simp [omChar, omVec]))
        (hc _ (by simp [omChar, omVec])) hN
  · have hgen : ∀ x, (x ∈ minusRootGroup 4 hirr (Pi.single i 1) ∨
        x ∈ minusRootGroup 4 hirr (-Pi.single i 1)) →
        x ∈ ggOTwoPrime (Subgroup.centralizer (((omTorus hirr hζ).range ⊓
          Subgroup.centralizer {n} : Subgroup (spinGroup (quadMinus 4 F b c))) :
            Set (spinGroup (quadMinus 4 F b c)))) := fun x hx =>
      Subgroup.subset_closure ⟨hLC (hx.elim (fun h => Subgroup.mem_sup_left h)
        (fun h => Subgroup.mem_sup_right h)), 1, by
          rw [pow_one, _root_.sq, mul_self_eq_one_of_mem_rankOne_gen hirr i hx]⟩
    exact sup_le (fun x hx => hgen x (Or.inl hx)) (fun x hx => hgen x (Or.inr hx))

end Fix

end CFSG.StandardType.KGPosOm

end
