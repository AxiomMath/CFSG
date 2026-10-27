module

public import CFSG.Timmesfeld.ARS.Sec8Natural
public import CFSG.Timmesfeld.ARS.SimplyLacedConfigA

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

section SL4

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def pm (σ : Equiv.Perm (Fin 4)) : SpecialLinearGroup (Fin 4) F :=
  ⟨SpecialLinear.signedPerm σ 1, by
    have : SpecialLinear.signedPerm σ (1 : Fin 4 → F) = (σ⁻¹).permMatrix F := by
      ext r s
      simp only [SpecialLinear.signedPerm_apply, Pi.one_apply, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
        Equiv.Perm.inv_def]
      by_cases h : r = σ s
      · subst h
        simp
      · rw [ite_eq_right_iff.2 (fun e => absurd e h), eq_comm, ite_eq_right_iff]
        intro e
        exact absurd (by rw [← e, Equiv.apply_symm_apply]) h
    rw [this, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
    · simp [h]
    · simp [h, CharTwo.neg_eq]⟩

omit [CharP F 2] in
theorem coe_pm' (σ : Equiv.Perm (Fin 4)) (h) :
    ((⟨SpecialLinear.signedPerm σ 1, h⟩ : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = SpecialLinear.signedPerm σ 1 := rfl

theorem coe_pm (σ : Equiv.Perm (Fin 4)) :
    ((pm σ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      SpecialLinear.signedPerm σ 1 := rfl

theorem pm_mul_transvection_mul_inv (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (hij : i ≠ j)
    (c : F) :
    pm σ * SpecialLinearGroup.transvection hij c * (pm σ)⁻¹ =
      SpecialLinearGroup.transvection (σ.injective.ne hij) c := by
  rw [SpecialLinear.conj_transvection_of_coe_eq_signedPerm (coe_pm σ) (fun _ => by simp) hij c]
  simp

theorem pm_mul (σ τ : Equiv.Perm (Fin 4)) : (pm σ * pm τ : SpecialLinearGroup (Fin 4) F) =
    pm (σ * τ) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_pm, SpecialLinear.signedPerm_mul_signedPerm]
  simp
  rfl

@[expose] noncomputable def X (a b : Fin 4) : Subgroup (SpecialLinearGroup (Fin 4) F) :=
  if h : a = b then ⊥ else SpecialLinear.rootSubgroup 3 F h

omit [CharP F 2] in
theorem X_of_ne {a b : Fin 4} (h : a ≠ b) :
    (X a b : Subgroup (SpecialLinearGroup (Fin 4) F)) = SpecialLinear.rootSubgroup 3 F h := by
  simp [X, h]

omit [CharP F 2] in
theorem mem_X {a b : Fin 4} (h : a ≠ b) {g : SpecialLinearGroup (Fin 4) F} :
    g ∈ X a b ↔ ∃ c : F, SpecialLinearGroup.transvection h c = g := by
  rw [X_of_ne h]
  exact SpecialLinear.mem_rootSubgroup h g

omit [CharP F 2] in
theorem transvection_mem_X {a b : Fin 4} (h : a ≠ b) (c : F) :
    SpecialLinearGroup.transvection h c ∈ (X a b : Subgroup (SpecialLinearGroup (Fin 4) F)) :=
  (mem_X h).2 ⟨c, rfl⟩

theorem conjSub_X_pm (σ : Equiv.Perm (Fin 4)) {a b : Fin 4} (h : a ≠ b) :
    conjSub (X a b) (pm σ : SpecialLinearGroup (Fin 4) F) = X (σ a) (σ b) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_X h).1 hx
    show pm σ * _ * (pm σ)⁻¹ ∈ _
    rw [pm_mul_transvection_mul_inv]
    exact transvection_mem_X _ c
  · intro hg
    obtain ⟨c, rfl⟩ := (mem_X (σ.injective.ne h)).1 hg
    exact ⟨_, transvection_mem_X h c, pm_mul_transvection_mul_inv σ h c⟩

omit [CharP F 2] in
theorem commuting_X {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hbc : b ≠ c) (hda : d ≠ a) :
    Commuting (X a b : Subgroup (SpecialLinearGroup (Fin 4) F)) (X c d) := by
  intro x hx y hy
  obtain ⟨s, rfl⟩ := (mem_X hab).1 hx
  obtain ⟨t, rfl⟩ := (mem_X hcd).1 hy
  exact SpecialLinearGroup.commute_transvection hab hcd hbc hda s t

omit [CharP F 2] in
theorem commutator_X {a b c : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ⁅(X a b : Subgroup (SpecialLinearGroup (Fin 4) F)),
      (X b c : Subgroup (SpecialLinearGroup (Fin 4) F))⁆ = X a c := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨s, rfl⟩ := (mem_X hab).1 hx
    obtain ⟨t, rfl⟩ := (mem_X hbc).1 hy
    rw [SpecialLinearGroup.commutatorElement_transvection hab hbc hac]
    exact transvection_mem_X hac _
  · intro g hg
    obtain ⟨s, rfl⟩ := (mem_X hac).1 hg
    have e := SpecialLinearGroup.commutatorElement_transvection hab hbc hac s (1 : F)
    rw [mul_one] at e
    rw [← e]
    exact Subgroup.commutator_mem_commutator (transvection_mem_X hab s) (transvection_mem_X hbc 1)

theorem pm_swap_eq {a b : Fin 4} (h : a ≠ b) :
    (pm (Equiv.swap a b) : SpecialLinearGroup (Fin 4) F) =
      SpecialLinearGroup.transvection h 1 * SpecialLinearGroup.transvection h.symm 1 *
        SpecialLinearGroup.transvection h 1 := by
  have e : SpecialLinearGroup.transvection h.symm (1 : F) =
      SpecialLinearGroup.transvection h.symm (-1) := by rw [CharTwo.neg_eq]
  rw [e]
  apply Subtype.ext
  rw [SpecialLinear.coe_transvection_mul_transvection_mul_transvection h, coe_pm]
  unfold SpecialLinear.weylMatrix
  congr 1
  funext s
  have hs := SpecialLinear.weylSign_mul_self (R := F) a s
  have h0 : (SpecialLinear.weylSign (R := F) a s + 1) ^ 2 = 0 := by
    rw [add_sq, sq, hs, CharTwo.two_eq_zero]
    simp [CharTwo.add_self_eq_zero]
  have h1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  rw [Pi.one_apply, eq_comm, ← sub_eq_zero, CharTwo.sub_eq_add]
  exact h1

theorem pm_swap_mem {a b : Fin 4} (h : a ≠ b) :
    (pm (Equiv.swap a b) : SpecialLinearGroup (Fin 4) F) ∈ X a b ⊔ X b a := by
  rw [pm_swap_eq h]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (transvection_mem_X h 1))
    (Subgroup.mem_sup_right (transvection_mem_X h.symm 1)))
    (Subgroup.mem_sup_left (transvection_mem_X h 1))

omit [CharP F 2] in
theorem X_injective {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (h : (X a b : Subgroup (SpecialLinearGroup (Fin 4) F)) = X c d) : a = c ∧ b = d := by
  have hm := transvection_mem_X (F := F) hab 1
  rw [h] at hm
  obtain ⟨t, ht⟩ := (mem_X hcd).1 hm
  have e := congrArg (fun g : SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) a b)
    ht
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, ite_eq_right_iff.2 (fun h' => absurd h' hab)] at e
  by_contra hne
  rw [ite_eq_right_iff.2 (fun h' => absurd ⟨h'.1.symm, h'.2.symm⟩ hne)] at e
  simp at e

omit [CharP F 2] in
theorem transvection_conj_row {a b c : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (s μ : F) :
    (SpecialLinearGroup.transvection hbc μ)⁻¹ * SpecialLinearGroup.transvection hab s *
        ((SpecialLinearGroup.transvection hbc μ)⁻¹)⁻¹ =
      SpecialLinearGroup.transvection hab s * SpecialLinearGroup.transvection hac (s * μ) := by
  rw [inv_inv, mul_assoc, SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul hab hbc hac,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]

omit [CharP F 2] in
theorem transvection_conj_col {a b c : Fin 4} (hba : b ≠ a) (hcb : c ≠ b) (hca : c ≠ a)
    (s μ : F) :
    SpecialLinearGroup.transvection hcb μ * SpecialLinearGroup.transvection hba s *
        (SpecialLinearGroup.transvection hcb μ)⁻¹ =
      SpecialLinearGroup.transvection hba s * SpecialLinearGroup.transvection hca (μ * s) := by
  rw [SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul hcb hba hca,
    mul_assoc (SpecialLinearGroup.transvection hba s),
    (SpecialLinearGroup.commute_transvection hcb hca hcb.symm hca.symm μ (μ * s)).eq,
    mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

end SL4

section Skeleton

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

noncomputable abbrev xg (Ψ : SpecialLinearGroup (Fin 4) F →* G) (a b : Fin 4) : Subgroup G :=
  (X a b).map Ψ

theorem conjSub_map (H : Subgroup (SpecialLinearGroup (Fin 4) F))
    (g : SpecialLinearGroup (Fin 4) F) : conjSub (H.map Ψ) (Ψ g) = (conjSub H g).map Ψ := by
  show (H.map Ψ).map (MulAut.conj (Ψ g)).toMonoidHom = (H.map (MulAut.conj g).toMonoidHom).map Ψ
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

structure Skel (R : Set (Subgroup G)) (Ψ : SpecialLinearGroup (Fin 4) F →* G) : Prop where
  inj : Function.Injective Ψ
  mem : ∀ a b : Fin 4, a ≠ b → xg Ψ a b ∈ R
  opp : ∀ a b : Fin 4, a ≠ b → Opposite (xg Ψ a b) (xg Ψ b a)

theorem conjSub_xg [CharP F 2] (σ : Equiv.Perm (Fin 4)) {a b : Fin 4} (h : a ≠ b) :
    conjSub (xg Ψ a b) (Ψ (pm σ)) = xg Ψ (σ a) (σ b) := by
  rw [conjSub_map, conjSub_X_pm σ h]

theorem commuting_xg {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hbc : b ≠ c) (hda : d ≠ a) :
    Commuting (xg Ψ a b) (xg Ψ c d) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (commuting_X hab hcd hbc hda x hx y hy).map Ψ

theorem commutator_xg {a b c : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ⁅xg Ψ a b, xg Ψ b c⁆ = xg Ψ a c := by
  rw [← Subgroup.map_commutator, commutator_X hab hbc hac]

theorem pm_swap_mem_sup [CharP F 2] {a b : Fin 4} (h : a ≠ b) :
    Ψ (pm (Equiv.swap a b)) ∈ xg Ψ a b ⊔ xg Ψ b a := by
  rw [← Subgroup.map_sup]
  exact ⟨_, pm_swap_mem h, rfl⟩

namespace Skel

theorem special (hS : Skel R Ψ) {a b c : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Special R (xg Ψ a b) (xg Ψ b c) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [commutator_xg hab hbc hac]
    exact hS.mem a c hac
  · rw [commutator_xg hab hbc hac]
    exact commuting_xg hac hab hac.symm hab.symm
  · rw [commutator_xg hab hbc hac]
    exact commuting_xg hac hbc hbc.symm hac.symm

theorem xg_ne (hS : Skel R Ψ) {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : ¬ (a = c ∧ b = d)) : xg Ψ a b ≠ xg Ψ c d := fun e =>
  hne (X_injective hab hcd (Subgroup.map_injective hS.inj e))

theorem coveredBy_row (hS : Skel R Ψ) (hR : IsRootClass R) {a b c : Fin 4} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : CoveredBy R (xg Ψ a b ⊔ xg Ψ a c) := by
  intro x hx hx1
  have hcomm : Commuting (xg Ψ a b) (xg Ψ a c) := commuting_xg hab hac hab.symm hac.symm
  have hle : xg Ψ a b ≤ Subgroup.normalizer ((xg Ψ a c : Subgroup G) : Set G) :=
    le_normalizer_of_conjSub_le fun g hg =>
      (conjSub_of_forall_commute fun k hk => hcomm g hg k hk).le
  have hx' : x ∈ ((xg Ψ a b : Subgroup G) : Set G) * ((xg Ψ a c : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hx
  obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩ := hx'
  obtain ⟨s, rfl⟩ := (mem_X hab).1 hy
  obtain ⟨t, rfl⟩ := (mem_X hac).1 hz
  beta_reduce
  by_cases hs : s = 0
  · subst hs
    refine ⟨xg Ψ a c, hS.mem a c hac, le_sup_right, ?_⟩
    rw [SpecialLinearGroup.transvection_coeff_zero, map_one, one_mul]
    exact ⟨_, transvection_mem_X hac t, rfl⟩
  set g := (SpecialLinearGroup.transvection hbc (s⁻¹ * t))⁻¹
  refine ⟨conjSub (xg Ψ a b) (Ψ g), hR.conjSub_mem (hS.mem a b hab) _, ?_, ?_⟩
  · rw [conjSub_map]
    rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
    obtain ⟨s', rfl⟩ := (mem_X hab).1 hy'
    show Ψ (g * _ * g⁻¹) ∈ _
    rw [transvection_conj_row hab hbc hac, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, transvection_mem_X hab s', rfl⟩)
      (Subgroup.mem_sup_right ⟨_, transvection_mem_X hac _, rfl⟩)
  · rw [conjSub_map]
    refine ⟨g * SpecialLinearGroup.transvection hab s * g⁻¹,
      ⟨_, transvection_mem_X hab s, rfl⟩, ?_⟩
    rw [transvection_conj_row hab hbc hac, map_mul, mul_inv_cancel_left₀ hs]

theorem coveredBy_col (hS : Skel R Ψ) (hR : IsRootClass R) {a b c : Fin 4} (hba : b ≠ a)
    (hcb : c ≠ b) (hca : c ≠ a) : CoveredBy R (xg Ψ b a ⊔ xg Ψ c a) := by
  intro x hx hx1
  have hcomm : Commuting (xg Ψ b a) (xg Ψ c a) := commuting_xg hba hca hca.symm hba.symm
  have hle : xg Ψ b a ≤ Subgroup.normalizer ((xg Ψ c a : Subgroup G) : Set G) :=
    le_normalizer_of_conjSub_le fun g hg =>
      (conjSub_of_forall_commute fun k hk => hcomm g hg k hk).le
  have hx' : x ∈ ((xg Ψ b a : Subgroup G) : Set G) * ((xg Ψ c a : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hx
  obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩ := hx'
  obtain ⟨s, rfl⟩ := (mem_X hba).1 hy
  obtain ⟨t, rfl⟩ := (mem_X hca).1 hz
  beta_reduce
  by_cases hs : s = 0
  · subst hs
    refine ⟨xg Ψ c a, hS.mem c a hca, le_sup_right, ?_⟩
    rw [SpecialLinearGroup.transvection_coeff_zero, map_one, one_mul]
    exact ⟨_, transvection_mem_X hca t, rfl⟩
  set g := SpecialLinearGroup.transvection hcb (t * s⁻¹)
  refine ⟨conjSub (xg Ψ b a) (Ψ g), hR.conjSub_mem (hS.mem b a hba) _, ?_, ?_⟩
  · rw [conjSub_map]
    rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
    obtain ⟨s', rfl⟩ := (mem_X hba).1 hy'
    show Ψ (g * _ * g⁻¹) ∈ _
    rw [transvection_conj_col hba hcb hca, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, transvection_mem_X hba s', rfl⟩)
      (Subgroup.mem_sup_right ⟨_, transvection_mem_X hca _, rfl⟩)
  · rw [conjSub_map]
    refine ⟨g * SpecialLinearGroup.transvection hba s * g⁻¹,
      ⟨_, transvection_mem_X hba s, rfl⟩, ?_⟩
    rw [transvection_conj_col hba hcb hca, map_mul, inv_mul_cancel_right₀ hs]

theorem mem_lambdaSet_row (hS : Skel R Ψ) (hR : IsRootClass R) {a b c : Fin 4} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : xg Ψ a b ∈ lambdaSet R (xg Ψ a c) := by
  refine ⟨⟨hS.mem a b hab, hS.xg_ne hab hac fun h => hbc h.2, ?_⟩, ?_⟩
  · exact commuting_xg hac hab hac.symm hab.symm
  · rw [sup_comm]
    exact hS.coveredBy_row hR hab hbc hac

theorem mem_lambdaSet_col (hS : Skel R Ψ) (hR : IsRootClass R) {a b c : Fin 4} (hba : b ≠ a)
    (hcb : c ≠ b) (hca : c ≠ a) : xg Ψ b a ∈ lambdaSet R (xg Ψ c a) := by
  refine ⟨⟨hS.mem b a hba, hS.xg_ne hba hca fun h => hcb h.1.symm, ?_⟩, ?_⟩
  · exact commuting_xg hca hba hba.symm hca.symm
  · rw [sup_comm]
    exact hS.coveredBy_col hR hba hcb hca

theorem of_isConfig [CharP F 2] (hR : IsRootClass R) {A B : Fin 3 → Subgroup G}
    (hX : IsConfig R (edgeA 3) A B) (hinj : Function.Injective Ψ)
    (hA : ∀ k, ((SpecialLinear.rootDatum 3 F).rootGroup (CFSG.Timmesfeld.sroot k)).map Ψ = A k)
    (hB : ∀ k, ((SpecialLinear.rootDatum 3 F).rootGroup (-CFSG.Timmesfeld.sroot k)).map Ψ =
      B k) : Skel R Ψ := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hA0 : xg Ψ 0 1 = A 0 := by
    rw [← hA (0 : Fin 3)]
    show (X 0 1).map Ψ = _
    rw [X_of_ne h01]
    congr 1
    exact (SpecialLinear.rootGroup_eq 3 F h01 (SpecialLinear.toStd_single 3 0)).symm
  have hB0 : xg Ψ 1 0 = B 0 := by
    rw [← hB (0 : Fin 3)]
    show (X 1 0).map Ψ = _
    rw [X_of_ne h01.symm]
    congr 1
    have ht : SpecialLinear.toStd 3 (-(Pi.single (0 : Fin 3) 1 : Fin 3 → ℤ)) =
        Pi.single 1 1 - Pi.single 0 1 := by
      rw [SpecialLinear.toStd_neg, SpecialLinear.toStd_single]
      simp
    exact (SpecialLinear.rootGroup_eq 3 F h01.symm ht).symm
  have hperm : ∀ a b : Fin 4, a ≠ b → ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b := by decide
  have key : ∀ a b : Fin 4, a ≠ b → xg Ψ a b ∈ R ∧ xg Ψ b a ∈ R ∧
      Opposite (xg Ψ a b) (xg Ψ b a) := by
    intro a b hab
    obtain ⟨σ, rfl, rfl⟩ := hperm a b hab
    rw [← conjSub_xg σ h01, ← conjSub_xg σ h01.symm, hA0, hB0]
    exact ⟨hR.conjSub_mem (hX.memA 0) _, hR.conjSub_mem (hX.memB 0) _, (hX.opp 0).conj _⟩
  exact ⟨hinj, fun a b hab => (key a b hab).1, fun a b hab => (key a b hab).2.2⟩

end Skel

end Skeleton

section LineStab

variable {F : Type} [Field F]

@[expose] noncomputable def lineStab : Subgroup (SpecialLinearGroup (Fin 4) F) where
  carrier := {g | ∃ c : F, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 0 1 = c • Pi.single 0 1}
  mul_mem' := by
    rintro g g' ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul, hc,
      smul_smul, mul_comm]
  one_mem' := ⟨1, by rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, one_smul]⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    have h1 : ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
        ((g : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 0 1) = Pi.single 0 1 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [hc, Matrix.mulVec_smul] at h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h1
      have := congrFun h1 0
      simp at this
    refine ⟨c⁻¹, ?_⟩
    calc ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 0 1 =
        c⁻¹ • (c • (((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
          Pi.single 0 1)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • Pi.single 0 1 := by rw [h1]

theorem mem_lineStab_of {g : SpecialLinearGroup (Fin 4) F}
    (hg : ∀ i : Fin 4, i ≠ 0 → (g : Matrix (Fin 4) (Fin 4) F) i 0 = 0) : g ∈ lineStab := by
  refine ⟨(g : Matrix (Fin 4) (Fin 4) F) 0 0, ?_⟩
  ext i
  rw [Matrix.mulVec_single]
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hg i hi, hi]

theorem mem_lineStab_of_conj_mem {g : SpecialLinearGroup (Fin 4) F}
    (hg : g * SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 3 by decide) 1 * g⁻¹ ∈
      (X 0 3 : Subgroup (SpecialLinearGroup (Fin 4) F))) : g ∈ lineStab := by
  obtain ⟨c, hc⟩ := (mem_X (show (0 : Fin 4) ≠ 3 by decide)).1 hg
  have e : SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 3 by decide) c * g =
      g * SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 3 by decide) (1 : F) := by
    rw [hc, inv_mul_cancel_right]
  have e' := congrArg (fun x : SpecialLinearGroup (Fin 4) F =>
    (x : Matrix (Fin 4) (Fin 4) F)) e
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, add_right_inj] at e'
  refine mem_lineStab_of fun i hi => ?_
  have := congrFun (congrFun e' i) 3
  simp only [Matrix.mul_apply, Matrix.single_apply] at this
  simp [Ne.symm hi] at this
  exact this.symm

theorem transvection_31_mem_lineStab (t : F) :
    SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 1 by decide) t ∈ lineStab := by
  refine mem_lineStab_of fun i hi => ?_
  simp [SpecialLinearGroup.transvection_coe, hi]

theorem transvection_10_notMem_lineStab :
    SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) (1 : F) ∉ lineStab := by
  rintro ⟨c, hc⟩
  have := congrFun hc 1
  rw [Matrix.mulVec_single] at this
  simp [SpecialLinearGroup.transvection_coe] at this

end LineStab

namespace Skel

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

theorem not_isCoatom_of_surjective [Finite G] (hS : Skel R Ψ) (hR : IsRootClass R)
    (hsurj : Function.Surjective Ψ) :
    ¬ IsCoatom (Subgroup.normalizer ((xg Ψ 0 3 : Subgroup G) : Set G)) := by
  intro hmax
  set H := (lineStab (F := F)).map Ψ with hH
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hNH : Subgroup.normalizer ((xg Ψ 0 3 : Subgroup G) : Set G) ≤ H := by
    intro y hy
    obtain ⟨g, rfl⟩ := hsurj y
    refine ⟨g, mem_lineStab_of_conj_mem ?_, rfl⟩
    have hx : Ψ (SpecialLinearGroup.transvection h03 1) ∈ xg Ψ 0 3 :=
      ⟨_, transvection_mem_X h03 1, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hy _).1 hx
    obtain ⟨z, hz, hz'⟩ := this
    rw [← map_inv, ← map_mul, ← map_mul] at hz'
    rwa [← hS.inj hz']
  have hXH : xg Ψ 3 1 ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_X h31).1 hx
    exact ⟨_, transvection_31_mem_lineStab t, rfl⟩
  have hXN : ¬ xg Ψ 3 1 ≤ Subgroup.normalizer ((xg Ψ 0 3 : Subgroup G) : Set G) := by
    intro hle
    have hc := commutator_le_of_le_normalizer le_rfl hle
    rw [commutator_xg h03 h31 h01] at hc
    have heq : xg Ψ 0 1 = xg Ψ 0 3 :=
      Subgroup.eq_of_le_of_card_ge hc (hR.card_eq (hS.mem 0 3 h03) (hS.mem 0 1 h01)).le
    exact hS.xg_ne h01 h03 (by decide) heq
  have hlt : Subgroup.normalizer ((xg Ψ 0 3 : Subgroup G) : Set G) < H :=
    lt_of_le_of_ne hNH fun e => hXN (e ▸ hXH)
  have htop := hmax.2 H hlt
  have hmem : Ψ (SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) 1) ∈ H := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨g, hg, hg'⟩ := hmem
  rw [hS.inj hg'] at hg
  exact transvection_10_notMem_lineStab hg

end Skel

end CaseB

end CFSG.Timmesfeld.ARS
