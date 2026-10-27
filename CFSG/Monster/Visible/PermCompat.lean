module

public import CFSG.Monster.Visible.PermSpin
public import CFSG.Monster.Visible.Pair

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix Subgroup

theorem comp_mem_codeLattice {q : Equiv.Perm (Fin 24)} (hq : q ∈ AutPerm) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : u ∘ ⇑q ∈ codeLattice C := by
  obtain ⟨m, hm, d, hd, hmod, hsum⟩ := hu
  refine ⟨m, hm, d ∘ ⇑q, comp_mem_of_mem_AutPerm hq hd, fun i => hmod (q i), ?_⟩
  have e : ∑ i, (u ∘ ⇑q) i = ∑ i, u i := Equiv.sum_comp q u
  rw [e]
  exact hsum

theorem image_Pmat_latticeQ (p : AutPerm) :
    (fun x => x ᵥ* Pmat p) '' latticeQ = latticeQ := by
  have hp : ∀ {q : Equiv.Perm (Fin 24)}, q ∈ AutPerm → ∀ x ∈ latticeQ, x ∘ ⇑q ∈ latticeQ := by
    rintro q hq _ ⟨u, hu, rfl⟩
    exact ⟨u ∘ ⇑q, comp_mem_codeLattice hq hu, rfl⟩
  ext x
  simp only [Set.mem_image, vecMul_Pmat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hp (inv_mem p.2) y hy
  · intro hx
    refine ⟨x ∘ ⇑(p : Equiv.Perm (Fin 24)), hp p.2 x hx, ?_⟩
    funext i
    simp

theorem PU_mem_latticeO (p : AutPerm) : PU p ∈ latticeO :=
  ⟨(mem_orthogonalGroup_iff _ _).2 (Pmat_mul_transpose_self p), image_Pmat_latticeQ p⟩

@[expose] def PO (p : AutPerm) : latticeO := ⟨PU p, PU_mem_latticeO p⟩

theorem mat_PO (p : AutPerm) : mat (PO p) = Pmat p := rfl

theorem latVec_Pmat (p : Equiv.Perm (Fin 24)) (u : Fin 24 → ℤ) :
    latVec (Pmat p) u = u ∘ ⇑p⁻¹ := by
  funext i
  show ((ratVec u ᵥ* Pmat p) i).num = u (p⁻¹ i)
  rw [vecMul_Pmat]
  exact Rat.num_intCast _

theorem modTwoEnd_cls (g : latticeO) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    modTwoEnd g (cls u hu) = cls (latVec (mat g) u) (latVec_spec g hu).1 := rfl

theorem modTwoEnd_PO_cls (p : AutPerm) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    modTwoEnd (PO p) (cls u hu) =
      cls (u ∘ ⇑(p : Equiv.Perm (Fin 24))⁻¹) (comp_mem_codeLattice (inv_mem p.2) hu) :=
  (modTwoEnd_cls (PO p) hu).trans (cls_congr _ (latVec_Pmat p u))

theorem lamCode_permWord (p : Equiv.Perm (Fin 24)) (a : Fin 24 → ZMod 2) :
    lamCode (permWord p a) = lamCode a ∘ ⇑p⁻¹ := by
  funext k
  show 2 * bitLift (a (p⁻¹ k)) + 2 * Pint (permWord p a) -
      4 * Pint (permWord p a) * bitLift (a (p⁻¹ k)) =
    2 * bitLift (a (p⁻¹ k)) + 2 * Pint a - 4 * Pint a * bitLift (a (p⁻¹ k))
  rw [Pint, Pint, P_permWord]

theorem lamSum_permWord (p : Equiv.Perm (Fin 24)) (v : Fin 24 → ZMod 2) :
    lamSum (permWord p v) = lamSum v ∘ ⇑p⁻¹ := by
  funext k
  show (hammingNorm (permWord p v) : ℤ) - 4 * bitLift (v (p⁻¹ k)) =
    (hammingNorm v : ℤ) - 4 * bitLift (v (p⁻¹ k))
  rw [hammingNorm_permWord]

theorem modTwoEnd_PO_lamX (p : AutPerm) (a : C) :
    modTwoEnd (PO p) (lamX a) = lamX (permC p a) :=
  (modTwoEnd_PO_cls p (lamCode_mem a.2)).trans (cls_congr _ (lamCode_permWord p a).symm)

theorem modTwoEnd_PO_lamCocode (p : AutPerm) (δ : Cocode) :
    modTwoEnd (PO p) (lamCocode δ) = lamCocode (permD p δ) := by
  induction δ using Submodule.Quotient.induction_on with
  | H x =>
    rw [permD_mk, lamCocode_mk, lamCocode_mk]
    exact (modTwoEnd_PO_cls p (lamSum_mem x)).trans (cls_congr _ (lamSum_permWord p x).symm)

@[expose] def conjSp (p : AutPerm) : Q ≃* Q := conjQOf (sU p) (sU_conj_mem_Q_iff p)

theorem coe_conjSp (p : AutPerm) (r : Q) : (conjSp p r : GL SpinIdx ℚ) = (sU p)⁻¹ * r * sU p :=
  rfl

theorem conjSp_XQ (p : AutPerm) (e : Parker) :
    conjSp p (XQ e) = zQ ^ (kappaP p e.code).val * XQ ⟨permC p e.code, e.sign⟩ :=
  Subtype.ext ((sU_conj_XU p e).trans (by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, coe_zQ]
    rfl))

theorem conjSp_DQ (p : AutPerm) (δ : Cocode) : conjSp p (DQ δ) = DQ (permD p δ) :=
  Subtype.ext (sU_conj_DU p δ)

theorem mk_mul_of_mem {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {z : G} (hz : z ∈ N)
    (x : G) : (QuotientGroup.mk (z * x) : G ⧸ N) = QuotientGroup.mk x := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, one_mul]

theorem zQ_mem_center : zQ ∈ center Q := by
  rw [center_Q]
  exact mem_zpowers zQ

theorem mk_zQ_pow_mul (n : ℕ) (x : Q) :
    (QuotientGroup.mk (zQ ^ n * x) : Q ⧸ center Q) = QuotientGroup.mk x :=
  mk_mul_of_mem (pow_mem zQ_mem_center n) x

private def phiConj (p : AutPerm) : Q →* Multiplicative L2 :=
  (phi.toMonoidHom.comp (QuotientGroup.mk' (center Q))).comp (conjSp p).toMonoidHom

private def phiPerm (p : AutPerm) : Q →* Multiplicative L2 :=
  (AddMonoidHom.toMultiplicative (modTwoEnd (PO p)).toAddMonoidHom).comp
    (phi.toMonoidHom.comp (QuotientGroup.mk' (center Q)))

private theorem phiConj_apply (p : AutPerm) (x : Q) :
    phiConj p x = phi (QuotientGroup.mk (conjSp p x)) := rfl

private theorem phiPerm_apply (p : AutPerm) (x : Q) :
    phiPerm p x =
      Multiplicative.ofAdd (modTwoEnd (PO p) (Multiplicative.toAdd (phi (QuotientGroup.mk x)))) :=
  rfl

private theorem phiConj_eq_phiPerm (p : AutPerm) : phiConj p = phiPerm p := by
  refine MonoidHom.eq_of_eqOn_dense (closure_preimage_eq_top (Set.range XU ∪ Set.range DU)) ?_
  rintro g (⟨e, he⟩ | ⟨δ, hδ⟩)
  · have hg : g = XQ e := Subtype.ext he.symm
    rw [hg]
    have hX₁ : phiConj p (XQ e) = Multiplicative.ofAdd (lamX (permC p e.code)) :=
      (phiConj_apply p _).trans ((congrArg (fun x : Q => phi (QuotientGroup.mk x))
        (conjSp_XQ p e)).trans ((congrArg phi (mk_zQ_pow_mul _ _)).trans (phi_XQ _)))
    have hX₂ : phiPerm p (XQ e) = Multiplicative.ofAdd (lamX (permC p e.code)) :=
      (phiPerm_apply p _).trans ((congrArg (fun x => Multiplicative.ofAdd (modTwoEnd (PO p)
        (Multiplicative.toAdd x))) (phi_XQ e)).trans
          (congrArg Multiplicative.ofAdd (modTwoEnd_PO_lamX p e.code)))
    exact hX₁.trans hX₂.symm
  · have hg : g = DQ δ := Subtype.ext hδ.symm
    rw [hg]
    have hD₁ : phiConj p (DQ δ) = Multiplicative.ofAdd (lamCocode (permD p δ)) :=
      (phiConj_apply p _).trans ((congrArg (fun x : Q => phi (QuotientGroup.mk x))
        (conjSp_DQ p δ)).trans (phi_DQ _))
    have hD₂ : phiPerm p (DQ δ) = Multiplicative.ofAdd (lamCocode (permD p δ)) :=
      (phiPerm_apply p _).trans ((congrArg (fun x => Multiplicative.ofAdd (modTwoEnd (PO p)
        (Multiplicative.toAdd x))) (phi_DQ δ)).trans
          (congrArg Multiplicative.ofAdd (modTwoEnd_PO_lamCocode p δ)))
    exact hD₁.trans hD₂.symm

theorem phi_conjSp (p : AutPerm) (r : Q) :
    Multiplicative.toAdd (phi (QuotientGroup.mk (conjSp p r))) =
      modTwoEnd (PO p) (Multiplicative.toAdd (phi (QuotientGroup.mk r))) :=
  congrArg Multiplicative.toAdd ((phiConj_apply p r).symm.trans
    ((DFunLike.congr_fun (phiConj_eq_phiPerm p) r).trans (phiPerm_apply p r)))

theorem isDyadicSpinNormalizer_sU (p : AutPerm) : IsDyadicSpinNormalizer (sU p) := by
  refine ⟨(mem_orthogonalGroup_iff _ _).2 (smat_mul_transpose_self p), fun i j => ?_,
    image_sU_conj_Q p⟩
  show smat p i j ∈ dyadic
  rw [smat_eq_spm]
  rcases spm_apply_mem (R := ℚ) (sPerm p) (sSign p) i j with h | h | h <;> rw [h]
  · exact dyadic.zero_mem
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem isCompatible_sU_PO (p : AutPerm) : IsCompatible (sU p) (PO p) := by
  intro r r' h
  have hr : r' = conjSp p r := Subtype.ext (h.trans (coe_conjSp p r).symm)
  exact (congrArg (fun x : Q => Multiplicative.toAdd (phi (QuotientGroup.mk x))) hr).trans
    (phi_conjSp p r)

theorem sU_PO_mem_Pvis (p : AutPerm) : (sU p, PO p) ∈ Pvis :=
  ⟨isDyadicSpinNormalizer_sU p, isCompatible_sU_PO p⟩

theorem code_permutation_compatible_spin_lift (p : AutPerm) :
    (∀ a a' b : C, betaP p (a + a') b = betaP p a b + betaP p a' b) ∧
    (∀ a b b' : C, betaP p a (b + b') = betaP p a b + betaP p a b') ∧
    (∀ a : C, betaP p a a = 0) ∧
    (∀ a b : C, betaBilin p a b = betaP p a b) ∧ (betaBilin p).IsAlt ∧
    (∀ a b : C, kappaP p (a + b) + kappaP p a + kappaP p b = betaP p a b) ∧
    smat p = spm ℚ (sPerm p) (sSign p) ∧ Function.Bijective (sPerm p) ∧
    (∀ i : SpinIdx, sPerm p i = (i.1 + kappaP p ΩC, π₀ (permC p i.2)) ∧
      sSign p i = kappaP p i.2 + (i.1 + kappaP p ΩC) * μ₀ (permC p i.2)) ∧
    (∀ x : Fin 24 → ZMod 2,
      permD p (Submodule.Quotient.mk x) = Submodule.Quotient.mk (permWord p x)) ∧
    (∀ δ : Cocode, (sU p)⁻¹ * DU δ * sU p = DU (permD p δ)) ∧
    (∀ (a : C) (s : ZMod 2),
      (sU p)⁻¹ * XU ⟨a, s⟩ * sU p = zU ^ (kappaP p a).val * XU ⟨permC p a, s⟩) ∧
    (((sU p)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = (smat p)ᵀ ∧
    (∀ δ : Cocode, (smat p)ᵀ * Dmat δ * smat p = Dmat (permD p δ)) ∧
    (∀ (a : C) (s : ZMod 2),
      (smat p)ᵀ * Xmat ⟨a, s⟩ * smat p = sgn (kappaP p a) • Xmat ⟨permC p a, s⟩) ∧
    PU p ∈ latticeO ∧ mat (PO p) = Pmat p ∧ (sU p, PO p) ∈ Pvis ∧
    (∀ (η : ZMod 2) (c : C₀), E η c ᵥ* smat p =
        sgn (kappaP p c + (η + kappaP p ΩC) * μ₀ (permC p c)) •
          E (η + kappaP p ΩC) (π₀ (permC p c)) ∧
      (π₀ (permC p c) : C) = permC p c + μ₀ (permC p c) • ΩC) :=
  ⟨betaP_add_left p, betaP_add_right p, betaP_self p, betaBilin_apply p, betaBilin_isAlt p,
    kappaP_add p, smat_eq_spm p, sPerm_bijective p, fun _ => ⟨rfl, rfl⟩, permD_mk p,
    sU_conj_DU p, fun a s => sU_conj_XU p ⟨a, s⟩, coe_sU_inv p,
    smat_transpose_mul_Dmat_mul_smat p, fun a s => smat_transpose_mul_Xmat_mul_smat p ⟨a, s⟩,
    PU_mem_latticeO p, mat_PO p, sU_PO_mem_Pvis p,
    fun η c => ⟨E_vecMul_smat p η c, coe_π₀ _⟩⟩

end CFSG.Monster.Visible
