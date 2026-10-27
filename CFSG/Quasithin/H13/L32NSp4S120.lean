module

public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Quasithin.H13.L32NSp4Cases
public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix
open scoped commutatorElement

section Facts

variable [Sp4Data]

theorem s120_nat : ∀ d ∈ specK.s120.1, ∀ v ∈ List.range 16,
    psi4 (mulVecC d v) = RuType.sigmaAct (phiC d) (psi4 v) := by
  have := specialOk_get (c := decide (∀ d ∈ specK.s120.1, ∀ v ∈ List.range 16,
      psi4 (mulVecC d v) = RuType.sigmaAct (phiC d) (psi4 v))) (by simp [specialChecks])
  simpa using this

theorem psi4_xor : ∀ x ∈ List.range 16, ∀ y ∈ List.range 16, psi4 (x ^^^ y) = psi4 x + psi4 y := by
  have := specialOk_get (c := decide (∀ x ∈ List.range 16, ∀ y ∈ List.range 16,
      psi4 (x ^^^ y) = psi4 x + psi4 y)) (by simp [specialChecks])
  simpa using this

theorem psi4_inj : ∀ x ∈ List.range 16, ∀ y ∈ List.range 16, psi4 x = psi4 y → x = y := by
  have := specialOk_get (c := decide (∀ x ∈ List.range 16, ∀ y ∈ List.range 16,
      psi4 x = psi4 y → x = y)) (by simp [specialChecks])
  simpa using this

omit [Sp4Data] in
theorem permOk_spec {l : List (List ℕ)} (h : permOk l = true) :
    (∀ d ∈ l, ∀ e ∈ l, permC (mulC d e) = compP (permC d) (permC e)) ∧
      (∀ d ∈ l, permC d = [0, 1, 2, 3, 4] → d = oneC4) ∧
      ∀ d ∈ l, (∀ c ∈ permC d, c < 5) ∧ (permC d).Nodup := by
  simp only [permOk, Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun d hd hp => ?_, h3⟩
  rcases h2 d hd with h | h
  · exact absurd hp h
  · exact h

theorem s120_perm :
    (∀ d ∈ specK.s120.1, ∀ e ∈ specK.s120.1, permC (mulC d e) = compP (permC d) (permC e)) ∧
      (∀ d ∈ specK.s120.1, permC d = [0, 1, 2, 3, 4] → d = oneC4) ∧
      ∀ d ∈ specK.s120.1, (∀ c ∈ permC d, c < 5) ∧ (permC d).Nodup :=
  permOk_spec (specialOk_get (c := permOk specK.s120.1) (by simp [specialChecks]))

theorem s120_permCond : ∀ d ∈ specK.s120.1, PermCond (permC d) := by
  simpa using specialOk_get (c := decide (∀ d ∈ specK.s120.1, PermCond (permC d)))
    (by simp [specialChecks])

theorem s120_closed : ∀ x ∈ specK.s120.1, ∀ y ∈ specK.s120.1, mulC x y ∈ specK.s120.1 := by
  have := specialOk_get (c := specK.s120.1.all (fun x => specK.s120.1.all fun y =>
    memM specK.s120.2 (mulC x y))) (by simp [specialChecks])
  intro x hx y hy
  have h := List.all_eq_true.mp (List.all_eq_true.mp this x hx) y hy
  rw [specK_s120_mask] at h
  exact mem_of_memM_maskOf specK_s120_valid
    (validC4_mulC (specK_s120_valid x hx) (specK_s120_valid y hy)) h

theorem s120_permInj : ∀ d ∈ specK.s120.1, permF d = 1 → d = oneC4 := by
  simpa using specialOk_get (c := decide (∀ d ∈ specK.s120.1, permF d = 1 → d = oneC4))
    (by simp [specialChecks])

theorem s120_sign : ∀ d ∈ specK.s120.1, (phiC d).right = 1 → Equiv.Perm.sign (permF d) = 1 := by
  simpa using specialOk_get (c := decide (∀ d ∈ specK.s120.1, (phiC d).right = 1 →
    Equiv.Perm.sign (permF d) = 1)) (by simp [specialChecks])

theorem s120_m60 : ∀ d ∈ specK.s120.1, memM specK.m60 d = decide ((phiC d).right = 1) := by
  simpa using specialOk_get (c := decide (∀ d ∈ specK.s120.1,
    memM specK.m60 d = decide ((phiC d).right = 1))) (by simp [specialChecks])

end Facts

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {b : Module.Basis (Fin 4) (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {s : Node}

@[expose] noncomputable def psiFun (b : Module.Basis (Fin 4) (ZMod 2) V) (v : V) :
    Fin 2 → RuType.F4 :=
  psi4 (vc b v)

theorem psiFun_add [Sp4Data] (v w : V) :
    psiFun b (v + w) = psiFun b v + psiFun b w := by
  simp only [psiFun, vc_add]
  exact psi4_xor _ (List.mem_range.mpr (vc_lt b v)) _ (List.mem_range.mpr (vc_lt b w))

theorem psiFun_injective [Sp4Data] : Function.Injective (psiFun b) := by
  intro v w h
  apply vc_injective b
  exact psi4_inj _ (List.mem_range.mpr (vc_lt b v)) _ (List.mem_range.mpr (vc_lt b w)) h

theorem card_V_of_basis (b : Module.Basis (Fin 4) (ZMod 2) V) : Nat.card V = 16 := by
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem card_F4sq : Nat.card (Fin 2 → RuType.F4) = 16 := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card]
  rfl

@[expose] noncomputable def psiV [Sp4Data]
    (b : Module.Basis (Fin 4) (ZMod 2) V) : V ≃+ (Fin 2 → RuType.F4) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (psiFun b) psiFun_add)
    (psiFun_injective.bijective_of_nat_card_le (by rw [card_F4sq, card_V_of_basis b]))

theorem psiV_apply [Sp4Data] (v : V) : psiV b v = psiFun b v := rfl

theorem sigma_ext {x y : RuType.SigmaL2F4}
    (hxy : ∀ w, RuType.sigmaAct x w = RuType.sigmaAct y w) : x = y := by
  have : y⁻¹ * x = 1 := RuType.Sigma.eq_one_of_sigmaAct_eq fun w => by
    rw [RuType.Sigma.sigmaAct_mul, hxy, ← RuType.Sigma.sigmaAct_mul, inv_mul_cancel,
      RuType.Sigma.sigmaAct_one]
  exact (inv_mul_eq_one.mp this).symm

theorem permOfList_apply {p : List ℕ} (hp : PermCond p) (i : Fin 5) :
    permOfList p i = permFunL p i := by
  simp only [permOfList, hp, dite_true]
  rfl

theorem length_permC (d : List ℕ) : (permC d).length = 5 := by
  simp [permC, pts]

theorem permOfList_compP {p q : List ℕ} (hp : PermCond p) (hq : PermCond q)
    (hpq : PermCond (compP p q)) (hq5 : ∀ c ∈ q, c < 5) (hql : q.length = 5) :
    permOfList (compP p q) = permOfList p * permOfList q := by
  ext i
  rw [Equiv.Perm.mul_apply, permOfList_apply hpq, permOfList_apply hp, permOfList_apply hq]
  have hi : (i : ℕ) < q.length := by rw [hql]; exact i.isLt
  have hqi : q.getD i 0 < 5 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hq5 _ (List.getElem_mem hi)
  simp only [permFunL, compP]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hi, Nat.mod_eq_of_lt hqi]

section Gamma

variable [Finite V] [Sp4Data]
variable (h : IsNodeOf b Γ s) (h120 : ∀ x, x ∈ s.els ↔ x ∈ specK.s120.1)
include h h120

omit [Finite V] in
theorem S120.equivariant {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) (v : V) :
    psiV b (γ v) = RuType.sigmaAct (phiC (cf b γ)) (psiV b v) := by
  rw [psiV_apply, psiV_apply, psiFun, psiFun, ← mulVecC_cf]
  exact s120_nat _ ((h120 _).mp (h.mem_els hγ)) _ (List.mem_range.mpr (vc_lt b v))

omit [Finite V] in
theorem S120.sigmaAct_eq {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) (w : Fin 2 → RuType.F4) :
    RuType.sigmaAct (phiC (cf b γ)) w = psiV b (γ ((psiV b).symm w)) := by
  rw [S120.equivariant h h120 hγ, AddEquiv.apply_symm_apply]

@[expose] noncomputable def S120.phiHom : ↥Γ →* RuType.SigmaL2F4 :=
  MonoidHom.mk' (fun γ => phiC (cf b γ)) fun γ δ => sigma_ext fun w => by
    show RuType.sigmaAct (phiC (cf b ((γ : V ≃ₗ[ZMod 2] V) * δ))) w =
      RuType.sigmaAct (phiC (cf b γ) * phiC (cf b δ)) w
    rw [RuType.Sigma.sigmaAct_mul, S120.sigmaAct_eq h h120 (Γ.mul_mem γ.2 δ.2),
      S120.sigmaAct_eq h h120 γ.2, S120.sigmaAct_eq h h120 δ.2, AddEquiv.symm_apply_apply]
    rfl

omit [Finite V] in
theorem S120.phiHom_apply (γ : ↥Γ) : S120.phiHom h h120 γ = phiC (cf b γ) := rfl

omit [Finite V] in
theorem S120.card_eq : Nat.card Γ = 120 := by
  rw [h.card_eq]
  have hl : specK.s120.1.length = 120 := by
    simpa using specialOk_get (c := specK.s120.1.length == 120) (by simp [specialChecks])
  have hnd : specK.s120.1.Nodup := by
    simpa using specialOk_get (c := decide specK.s120.1.Nodup) (by simp [specialChecks])
  rw [← hl, ← List.toFinset_card_of_nodup h.nodup, ← List.toFinset_card_of_nodup hnd]
  exact congrArg Finset.card (Finset.ext fun x => by
    simp only [List.mem_toFinset]
    exact h120 x)

omit [Finite V] in
theorem S120.phiHom_bijective : Function.Bijective (S120.phiHom h h120) := by
  have hinj : Function.Injective (S120.phiHom h h120) := by
    intro γ δ hγδ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply (psiV b).injective
    rw [S120.equivariant h h120 γ.2, S120.equivariant h h120 δ.2]
    rw [S120.phiHom_apply, S120.phiHom_apply] at hγδ
    rw [hγδ]
  refine hinj.bijective_of_nat_card_le ?_
  rw [RuType.Sigma.card_Sigma', S120.card_eq h h120]

omit [Finite V] in
theorem S120.natural : ∃ (φ : ↥Γ ≃* RuType.SigmaL2F4) (ψ : V ≃+ (Fin 2 → RuType.F4)),
    ∀ (γ : ↥Γ) (v : V), ψ ((γ : V ≃ₗ[ZMod 2] V) v) = RuType.sigmaAct (φ γ) (ψ v) :=
  ⟨MulEquiv.ofBijective _ (S120.phiHom_bijective h h120), psiV b, fun γ v =>
    S120.equivariant h h120 γ.2 v⟩

omit [Finite V] in
theorem S120.mem_s120 {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) : cf b γ ∈ specK.s120.1 :=
  (h120 _).mp (h.mem_els hγ)

@[expose] noncomputable def S120.permHom : ↥Γ →* Equiv.Perm (Fin 5) :=
  MonoidHom.mk' (fun γ => permF (cf b γ)) fun γ δ => by
    show permF (cf b ((γ : V ≃ₗ[ZMod 2] V) * δ)) = permF (cf b γ) * permF (cf b δ)
    have hγ := S120.mem_s120 h h120 γ.2
    have hδ := S120.mem_s120 h h120 δ.2
    rw [cf_mul, permF, s120_perm.1 _ hγ _ hδ, permF, permF]
    refine permOfList_compP (s120_permCond _ hγ) (s120_permCond _ hδ) ?_
      (s120_perm.2.2 _ hδ).1 (length_permC _)
    rw [← s120_perm.1 _ hγ _ hδ]
    exact s120_permCond _ (s120_closed _ hγ _ hδ)

omit [Finite V] in
theorem S120.permHom_apply (γ : ↥Γ) : S120.permHom h h120 γ = permF (cf b γ) := rfl

omit [Finite V] in
theorem S120.permHom_injective : Function.Injective (S120.permHom h h120) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  rw [S120.permHom_apply] at hγ
  apply Subtype.ext
  rw [Subgroup.coe_one, ← cf_eq_oneC4_iff b]
  exact s120_permInj _ (S120.mem_s120 h h120 γ.2) hγ

omit [Finite V] in
theorem S120.permEquiv : Nonempty (↥Γ ≃* Equiv.Perm (Fin 5)) := by
  refine ⟨MulEquiv.ofBijective _ ((S120.permHom_injective h h120).bijective_of_nat_card_le ?_)⟩
  rw [S120.card_eq h h120, Nat.card_perm, Nat.card_fin]
  decide

@[expose] noncomputable def S120.n60 : Subgroup ↥Γ :=
  ((SemidirectProduct.rightHom).comp (S120.phiHom h h120)).ker

omit [Finite V] in
theorem S120.mem_n60 (γ : ↥Γ) : γ ∈ S120.n60 h h120 ↔ (phiC (cf b γ)).right = 1 := by
  rw [S120.n60, MonoidHom.mem_ker, MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right,
    S120.phiHom_apply]

omit [Finite V] in
theorem S120.card_n60 : Nat.card (S120.n60 h h120) = 60 := by
  set f := (SemidirectProduct.rightHom).comp (S120.phiHom h h120) with hf
  have hsurj : Function.Surjective f :=
    SemidirectProduct.rightHom_surjective.comp (S120.phiHom_bijective h h120).2
  have hrange : Nat.card f.range = 2 := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    rw [Nat.card_congr Multiplicative.toAdd]
    exact Nat.card_zmod 2
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, S120.card_eq h h120] at h1
  show Nat.card f.ker = 60
  omega

@[expose] noncomputable def S120.toAlt : S120.n60 h h120 →* alternatingGroup (Fin 5) :=
  ((S120.permHom h h120).comp (S120.n60 h h120).subtype).codRestrict _ fun γ => by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, S120.permHom_apply,
      Equiv.Perm.mem_alternatingGroup]
    exact s120_sign _ (S120.mem_s120 h h120 γ.1.2) ((S120.mem_n60 h h120 γ.1).mp γ.2)

omit [Finite V] in
theorem S120.toAlt_bijective : Function.Bijective (S120.toAlt h h120) := by
  have hinj : Function.Injective (S120.toAlt h h120) := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (S120.permHom_injective h h120 this)
  refine hinj.bijective_of_nat_card_le ?_
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_perm, Nat.card_fin] at h2
  rw [S120.card_n60 h h120]
  have : Nat.factorial 5 = 120 := by decide
  omega

omit [Finite V] in
theorem S120.isSimple_n60 : IsSimpleGroup (S120.n60 h h120) :=
  (MulEquiv.ofBijective _ (S120.toAlt_bijective h h120)).isSimpleGroup

omit [Finite V] in
theorem S120.nonab_n60 : ∃ x y : S120.n60 h h120, x * y ≠ y * x := by
  let e := MulEquiv.ofBijective _ (S120.toAlt_bijective h h120)
  have : ∃ x y : alternatingGroup (Fin 5), x * y ≠ y * x := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, ?_⟩
    intro hc
    have := congrArg Subtype.val hc
    exact absurd this (by decide)
  obtain ⟨x, y, hxy⟩ := this
  exact ⟨e.symm x, e.symm y, fun h' => hxy (by
    have := congrArg e h'
    simpa using this)⟩

omit [Finite V] in
theorem S120.isQuasisimple_n60 : CFSG.Open.IsQuasisimple (S120.n60 h h120) := by
  have hs := S120.isSimple_n60 h h120
  obtain ⟨x, y, hxy⟩ := S120.nonab_n60 h h120
  refine ⟨?_, ?_⟩
  · rcases (inferInstance : (commutator (S120.n60 h h120)).Normal).eq_bot_or_eq_top with
      h0 | h1
    · exfalso
      apply hxy
      have : ⁅x, y⁆ ∈ commutator (S120.n60 h h120) := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h1
  · have hc : Subgroup.center (S120.n60 h h120) = ⊥ := by
      rcases (inferInstance : (Subgroup.center (S120.n60 h h120)).Normal).eq_bot_or_eq_top with
        h0 | h1
      · exact h0
      · exfalso
        apply hxy
        have : x ∈ Subgroup.center (S120.n60 h h120) := by rw [h1]; exact Subgroup.mem_top x
        exact (Subgroup.mem_center_iff.mp this y).symm
    exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

omit [Finite V] in
theorem S120.n60_le_layer : S120.n60 h h120 ≤ CFSG.Open.genFittingLayer ↥Γ := by
  refine le_sSup ⟨le_top, ?_, S120.isQuasisimple_n60 h h120⟩
  refine CFSG.Open.IsSubnormal.step le_top ?_ (CFSG.Open.IsSubnormal.refl ⊤)
  have : (S120.n60 h h120).Normal := MonoidHom.normal_ker _
  exact Subgroup.normal_subgroupOf

omit [Finite V] in
theorem S120.mem_layer {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ)
    (hm : memM specK.m60 (cf b γ) = true) :
    γ ∈ (CFSG.Open.genFittingLayer ↥Γ).map Γ.subtype := by
  refine ⟨⟨γ, hγ⟩, S120.n60_le_layer h h120 ?_, rfl⟩
  rw [S120.mem_n60]
  have := s120_m60 _ (S120.mem_s120 h h120 hγ)
  rw [hm] at this
  exact of_decide_eq_true this.symm

end Gamma

end CFSG.Quasithin.H13.Sp4Cert
