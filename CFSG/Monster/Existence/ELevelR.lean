module

public import CFSG.Monster.Existence.ELevelDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open scoped commutatorElement

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.TwoA.Census

private theorem rhoGriess_pow (q : Q) (n : ℕ) : rhoGriess (q ^ n) = rhoGriess q ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rhoGriess_one]
  | succ n ih => rw [pow_succ q n, rhoGriess_mul, ih, pow_succ' (rhoGriess q) n]

private theorem rhoGriess_comm {q q' : Q} (h : q * q' = q' * q) :
    rhoGriess q * rhoGriess q' = rhoGriess q' * rhoGriess q := by
  rw [← rhoGriess_mul, ← rhoGriess_mul, h]

private theorem rhoGriess_rOneTwo : rhoGriess rOneTwo = tGriess * uGriess := by
  rw [← rTwo_mul_rStar, rhoGriess_mul, rhoGriess_rStar, rhoGriess_rTwo]

private theorem xGriess_inv_mul_rhoGriess (q : Q) :
    xGriess⁻¹ * rhoGriess q = rhoGriess (q * zQ) := by
  rw [inv_eq_of_mul_eq_one_right xGriess_mul_self, rhoGriess_mul, rhoGriess_zQ]

private theorem rhoGriess_mem_FE_iff {q : Q} :
    rhoGriess q ∈ FE ↔ q = 1 ∨ q = rStar ∨ q = rTwo ∨ q = rOneTwo := by
  constructor
  · rintro (h | h | h | h)
    · exact .inl (rhoGriess_injective (h.trans rhoGriess_one.symm))
    · exact .inr (.inl (rhoGriess_injective (h.trans rhoGriess_rStar.symm)))
    · exact .inr (.inr (.inl (rhoGriess_injective (h.trans rhoGriess_rTwo.symm))))
    · exact .inr (.inr (.inr (rhoGriess_injective (h.trans rhoGriess_rOneTwo.symm))))
  · rintro (rfl | rfl | rfl | rfl)
    · exact .inl rhoGriess_one
    · exact .inr (.inl rhoGriess_rStar)
    · exact .inr (.inr (.inl rhoGriess_rTwo))
    · exact .inr (.inr (.inr rhoGriess_rOneTwo))

private theorem coordOf_rTwo : coordOf rTwo = (0, deltaPair 0 2) := coordOf_DQ _

private theorem coordOf_rOneTwo : coordOf rOneTwo = (0, deltaPair 1 2) := coordOf_DQ _

private theorem coordOf_mul_zQ (r : Q) : coordOf (r * zQ) = coordOf r := by
  rw [Subgroup.mem_center_iff.1 Short.zQ_mem_center r, coordOf_zQ_mul]

private theorem mk_ne_of_weight {x y : Fin 24 → ZMod 2} (h0 : x - y ≠ 0)
    (hw : hammingNorm (x - y) < 8) :
    (Submodule.Quotient.mk x : Cocode) ≠ Submodule.Quotient.mk y := fun h =>
  absurd (eight_le_wt (Submodule.Quotient.eq _ |>.1 h) h0) (by omega)

private theorem deltaPair_ne_zero :
    deltaPair 0 1 ≠ 0 ∧ deltaPair 0 2 ≠ 0 ∧ deltaPair 1 2 ≠ 0 := by
  refine ⟨fun h => mk_ne_of_weight (x := Pi.single 0 1 + Pi.single 1 1) (y := 0) (by decide)
    (by decide) (h.trans (Submodule.Quotient.mk_zero _).symm),
    fun h => mk_ne_of_weight (x := Pi.single 0 1 + Pi.single 2 1) (y := 0) (by decide)
    (by decide) (h.trans (Submodule.Quotient.mk_zero _).symm),
    fun h => mk_ne_of_weight (x := Pi.single 1 1 + Pi.single 2 1) (y := 0) (by decide)
    (by decide) (h.trans (Submodule.Quotient.mk_zero _).symm)⟩

private theorem deltaPair_three_four_ne :
    deltaPair 3 4 ≠ 0 ∧ deltaPair 3 4 ≠ deltaPair 0 1 ∧ deltaPair 3 4 ≠ deltaPair 0 2 ∧
      deltaPair 3 4 ≠ deltaPair 1 2 := by
  refine ⟨fun h => mk_ne_of_weight (x := Pi.single 3 1 + Pi.single 4 1) (y := 0) (by decide)
    (by decide) (h.trans (Submodule.Quotient.mk_zero _).symm),
    mk_ne_of_weight (by decide) (by decide), mk_ne_of_weight (by decide) (by decide),
    mk_ne_of_weight (by decide) (by decide)⟩

private theorem rhoGriess_zQ_not_mem_FE : rhoGriess zQ ∉ FE := by
  intro h
  have hz : coordOf zQ = 0 :=
    (congrArg coordOf (mul_one zQ).symm).trans
      ((coordOf_zQ_mul 1).trans CFSG.Monster.B.coordOf_one')
  obtain ⟨h1, h2, h3⟩ := deltaPair_ne_zero
  rcases rhoGriess_mem_FE_iff.1 h with h' | h' | h' | h'
  · have := orderOf_zQ
    rw [h', orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [h', coordOf_rStar] at hz
    exact h1 (congrArg Prod.snd hz)
  · rw [h', coordOf_rTwo] at hz
    exact h2 (congrArg Prod.snd hz)
  · rw [h', coordOf_rOneTwo] at hz
    exact h3 (congrArg Prod.snd hz)

theorem RE_le_centralizer_x : RE ≤ Subgroup.centralizer ({xGriess} : Set MGriess) := by
  intro g hg
  obtain ⟨q, -, rfl⟩ := mem_RE_iff.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff, ← rhoGriess_zQ]
  exact rhoGriess_comm (Subgroup.mem_center_iff.1 Short.zQ_mem_center q)

theorem RE_le_centralizer_FE : RE ≤ Subgroup.centralizer (FE : Set MGriess) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := mem_RE_iff.1 hg
  obtain ⟨h1, h2⟩ := mem_RQ_iff.1 hq
  have ht : Commute (rhoGriess q) tGriess := by
    rw [← rhoGriess_rStar]
    exact rhoGriess_comm h1
  have hu : Commute (rhoGriess q) uGriess := by
    rw [← rhoGriess_rTwo]
    exact rhoGriess_comm h2
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  rcases mem_FE.1 hf with rfl | rfl | rfl | rfl
  · exact (Commute.one_left _).eq
  · exact ht.symm.eq
  · exact hu.symm.eq
  · exact (ht.symm.mul_left hu.symm).eq

theorem isPGroup_RE : IsPGroup 2 RE := by
  rintro ⟨g, hg⟩
  obtain ⟨q, -, rfl⟩ := mem_RE_iff.1 hg
  obtain ⟨k, hk⟩ := isExtraspecialPGroup_Q.1 q
  refine ⟨k, Subtype.ext ?_⟩
  change rhoGriess q ^ 2 ^ k = 1
  rw [← rhoGriess_pow, hk, rhoGriess_one]

private theorem comm_map_of_fix {G : Type*} [Group G] (f : G ≃* G) {r q : G} (hr : f r = r)
    (hq : q * r = r * q) : f q * r = r * f q :=
  Subgroup.mem_centralizer_singleton_iff.1
    (mem_centralizer_of_map f hr (Subgroup.mem_centralizer_singleton_iff.2 hq))

private theorem conjQ_mem_RQ (p : Pvis) (h1 : conjQ p rStar = rStar) (h2 : conjQ p rTwo = rTwo)
    {q : Q} (hq : q ∈ RQ) : conjQ p q ∈ RQ :=
  mem_RQ_iff.2 ⟨comm_map_of_fix (conjQ p) h1 (mem_RQ_iff.1 hq).1,
    comm_map_of_fix (conjQ p) h2 (mem_RQ_iff.1 hq).2⟩

private theorem exists_conjQ_of_mem_centralizer_x {h : MGriess}
    (hx : h ∈ Subgroup.centralizer ({xGriess} : Set MGriess)) :
    ∃ p : Pvis, ∀ q : Q, h * rhoGriess q * h⁻¹ = rhoGriess (conjQ p q) := by
  obtain ⟨p, hp⟩ := mem_Gvis.1 (mem_Gvis_of_mem_cent_xGriess hx)
  refine ⟨p, fun q => Subtype.ext ?_⟩
  have := CFSG.Monster.B.Short.thetaEquiv_conj_rhoEquiv p q
  rw [hp] at this
  exact this

theorem RE_normalized :
    ∀ h ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
        Subgroup.centralizer ({xGriess} : Set MGriess), ∀ r ∈ RE, h * r * h⁻¹ ∈ RE := by
  intro h hh r hr
  obtain ⟨q, hq, rfl⟩ := mem_RE_iff.1 hr
  obtain ⟨hF, hx⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨p, hconj⟩ := exists_conjQ_of_mem_centralizer_x hx
  have hcF : ∀ f ∈ FE, h * f * h⁻¹ = f := fun f hf => by
    rw [← Subgroup.mem_centralizer_iff.1 hF f hf, mul_inv_cancel_right]
  have h1 : conjQ p rStar = rStar := rhoGriess_injective (by
    rw [← hconj, rhoGriess_rStar]
    exact hcF _ (mem_FE.2 (.inr (.inl rfl))))
  have h2 : conjQ p rTwo = rTwo := rhoGriess_injective (by
    rw [← hconj, rhoGriess_rTwo]
    exact hcF _ (mem_FE.2 (.inr (.inr (.inl rfl)))))
  rw [hconj]
  exact rhoGriess_mem_RE (conjQ_mem_RQ p h1 h2 hq)

private theorem zmod2_cases' : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

private theorem phi0_coordOf_rOneTwo :
    phi0 (coordOf rOneTwo) = phi0 (coordOf rStar) + phi0 (coordOf rTwo) := by
  rw [← rStar_mul_rTwo, phi0_coordOf_mul]

private theorem eq_or_eq_mul_zQ {q c : Q} (h : phi0 (coordOf q) = phi0 (coordOf c)) :
    q = c ∨ q = c * zQ := by
  have h1 : phi0 (coordOf (c⁻¹ * q)) = 0 := by
    rw [phi0_coordOf_mul, phi0_coordOf_inv, h]
    exact ZModModule.add_self _
  rcases (phi0_coordOf_eq_zero_iff _).1 h1 with h2 | h2
  · exact .inl (inv_mul_eq_one.1 h2).symm
  · exact .inr (by rw [← h2, mul_inv_cancel_left])

private theorem phi0_mem_span_of_forall_commute {q : Q} (hc : ∀ q' ∈ RQ, q * q' = q' * q) :
    phi0 (coordOf q) ∈
      Submodule.span (ZMod 2) {phi0 (coordOf rStar), phi0 (coordOf rTwo)} := by
  set W : Submodule (ZMod 2) L2 :=
    Submodule.span (ZMod 2) {phi0 (coordOf rStar), phi0 (coordOf rTwo)}
  have hrefl : (bL : LinearMap.BilinForm (ZMod 2) L2).IsRefl := fun x y h => by
    rw [bL_comm]
    exact h
  have hWW : bL.orthogonal (bL.orthogonal W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal bL_nondegenerate hrefl W
  rw [← hWW, LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy
  have hy1 := hy _ (Submodule.subset_span (Set.mem_insert _ _))
  have hy2 := hy _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨q', hq'⟩ := phiQ_surjective (Multiplicative.ofAdd y)
  have hq'y : phi0 (coordOf q') = y := by rw [← toAdd_phiQ, hq', toAdd_ofAdd]
  rw [← hq'y] at hy1 hy2 ⊢
  have hmem : q' ∈ RQ := mem_RQ_iff.2
    ⟨(commute_iff_bL _ _).2 (by rw [bL_comm]; exact hy1),
      (commute_iff_bL _ _).2 (by rw [bL_comm]; exact hy2)⟩
  rw [bL_comm]
  exact (commute_iff_bL q q').1 (hc q' hmem)

private theorem comm_of_commutator_mem_FE {q q' : Q}
    (h : rhoGriess q * rhoGriess q' * (rhoGriess q)⁻¹ * (rhoGriess q')⁻¹ ∈ FE) :
    q * q' = q' * q := by
  have h2 : rhoGriess ⁅q'⁻¹, q⁻¹⁆ =
      rhoGriess q * rhoGriess q' * (rhoGriess q)⁻¹ * (rhoGriess q')⁻¹ := by
    rw [commutatorElement_def, inv_inv, inv_inv, rhoGriess_mul, rhoGriess_mul, rhoGriess_mul,
      rhoGriess_inv, rhoGriess_inv]
    simp only [mul_assoc]
  have h3 : ⁅q'⁻¹, q⁻¹⁆ ∈ commutator Q :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [commutator_Q] at h3
  have h4 : ⁅q'⁻¹, q⁻¹⁆ = 1 := by
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_zQ).1 h3 with h' | h'
    · exact h'
    · exfalso
      apply rhoGriess_zQ_not_mem_FE
      rw [← h', h2]
      exact h
  exact (Commute.inv_inv_iff.1 (commutatorElement_eq_one_iff_mul_comm.1 h4)).eq.symm

private theorem mem_span_pair_zmod_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {x y z : M} (h : z ∈ Submodule.span (ZMod 2) {x, y}) :
    z = 0 ∨ z = x ∨ z = y ∨ z = x + y := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
  rcases zmod2_cases' a with rfl | rfl <;> rcases zmod2_cases' b with rfl | rfl
  · exact .inl (by simp)
  · exact .inr (.inr (.inl (by simp)))
  · exact .inr (.inl (by simp))
  · exact .inr (.inr (.inr (by simp)))

private theorem exists_rho_mem_FE_of_mem_span {q : Q}
    (h : phi0 (coordOf q) ∈
      Submodule.span (ZMod 2) {phi0 (coordOf rStar), phi0 (coordOf rTwo)}) :
    ∃ c : Q, rhoGriess c ∈ FE ∧ phi0 (coordOf q) = phi0 (coordOf c) := by
  rcases mem_span_pair_zmod_two h with h | h | h | h
  · exact ⟨1, rhoGriess_mem_FE_iff.2 (.inl rfl),
      h.trans (by rw [CFSG.Monster.B.coordOf_one', map_zero])⟩
  · exact ⟨rStar, rhoGriess_mem_FE_iff.2 (.inr (.inl rfl)), h⟩
  · exact ⟨rTwo, rhoGriess_mem_FE_iff.2 (.inr (.inr (.inl rfl))), h⟩
  · exact ⟨rOneTwo, rhoGriess_mem_FE_iff.2 (.inr (.inr (.inr rfl))),
      h.trans phi0_coordOf_rOneTwo.symm⟩

theorem RE_hZR : ∀ r ∈ RE, (∀ r' ∈ RE, r * r' * r⁻¹ * r'⁻¹ ∈ FE) →
    r ∈ FE ∨ xGriess⁻¹ * r ∈ FE := by
  intro r hr hcomm
  obtain ⟨q, -, rfl⟩ := mem_RE_iff.1 hr
  have hc : ∀ q' ∈ RQ, q * q' = q' * q := fun q' hq' =>
    comm_of_commutator_mem_FE (hcomm (rhoGriess q') (rhoGriess_mem_RE hq'))
  obtain ⟨c, hcFE, hqc⟩ := exists_rho_mem_FE_of_mem_span (phi0_mem_span_of_forall_commute hc)
  rcases eq_or_eq_mul_zQ hqc with rfl | rfl
  · exact .inl hcFE
  · right
    rw [xGriess_inv_mul_rhoGriess, mul_assoc, Short.zQ_mul_zQ, mul_one]
    exact hcFE

theorem RE_hinv : ∃ r ∈ RE, r * r ∈ FE ∧ r ∉ FE ∧ xGriess⁻¹ * r ∉ FE := by
  obtain ⟨h0, h1, h2, h3⟩ := deltaPair_three_four_ne
  have hdR : DQ (deltaPair 3 4) ∈ RQ := mem_RQ_iff.2 ⟨TwoA.DQ_comm _ _, TwoA.DQ_comm _ _⟩
  have key : ∀ q : Q, coordOf q = coordOf (DQ (deltaPair 3 4)) →
      ¬ (q = 1 ∨ q = rStar ∨ q = rTwo ∨ q = rOneTwo) := by
    intro q hq hF
    have hq' : coordOf q = (0, deltaPair 3 4) := hq.trans (coordOf_DQ _)
    rcases hF with rfl | rfl | rfl | rfl
    · exact h0 (congrArg Prod.snd ((CFSG.Monster.B.coordOf_one').symm.trans hq')).symm
    · rw [coordOf_rStar] at hq'
      exact h1 (congrArg Prod.snd hq').symm
    · rw [coordOf_rTwo] at hq'
      exact h2 (congrArg Prod.snd hq').symm
    · rw [coordOf_rOneTwo] at hq'
      exact h3 (congrArg Prod.snd hq').symm
  refine ⟨rhoGriess (DQ (deltaPair 3 4)), rhoGriess_mem_RE hdR, ?_, ?_, ?_⟩
  · rw [← rhoGriess_mul, OddCocode.DQ_mul_self, rhoGriess_one]
    exact FE.one_mem
  · intro h
    exact key _ rfl (rhoGriess_mem_FE_iff.1 h)
  · intro h
    rw [xGriess_inv_mul_rhoGriess] at h
    exact key _ (coordOf_mul_zQ _) (rhoGriess_mem_FE_iff.1 h)

theorem FE_le_RE : FE ≤ RE := by
  have ht : tGriess ∈ RE := by
    rw [← rhoGriess_rStar]
    exact rhoGriess_mem_RE (mem_RQ_iff.2 ⟨rfl, rStar_mul_rTwo.trans rTwo_mul_rStar.symm⟩)
  have hu : uGriess ∈ RE := by
    rw [← rhoGriess_rTwo]
    exact rhoGriess_mem_RE (mem_RQ_iff.2 ⟨rTwo_mul_rStar.trans rStar_mul_rTwo.symm, rfl⟩)
  intro g hg
  rcases mem_FE.1 hg with rfl | rfl | rfl | rfl
  · exact RE.one_mem
  · exact ht
  · exact hu
  · exact RE.mul_mem ht hu

end CFSG.Monster.Existence
