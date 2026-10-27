module

public import CFSG.Monster.B.GSide.EdgeAutAbstract
public import CFSG.Monster.B.TwoA.Unitary.Twenty
public import CFSG.Monster.B.TwoA.Sp8.Par1Base

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8

abbrev N1P : Subgroup P1 := N1.subgroupOf P1

instance N1P_normal :
    N1P.Normal := by
  rw [N1P, ← ker_p1Proj]
  infer_instance

theorem orth_sigLine_eq_sigmaPerp :
    bV.orthogonal Sp8.sigLine = Unitary.sigmaPerp := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact h _ sigmaW_mem_sigLine
  · intro h y hy
    rcases mem_sigLine.1 hy with rfl | rfl
    · exact LinearMap.map_zero₂ _ _
    · exact h

theorem psiW_mem_sigmaPerp
    {n : Dfull} (hn : n ∈ N1) :
    psiW ⟨n, N1_le_Ehat hn⟩ ∈ Unitary.sigmaPerp := by
  rw [← orth_sigLine_eq_sigmaPerp]
  rw [N1_eq_EU] at hn
  obtain ⟨_, hU⟩ := mem_EU.1 hn
  exact hU

theorem mem_unitary_sigLine_iff
    (x : Unitary.sigmaPerp) :
    x ∈ Unitary.sigLine ↔ (x : Wv v0) ∈ Sp8.sigLine := by
  rw [Unitary.sigLine, Sp8.sigLine, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem mem_N1_of_mem_N1P (n : N1P) : ((n : P1) : Dfull) ∈ N1 := Subgroup.mem_subgroupOf.1 n.2

@[expose] def psiN
    (n : N1P) : Unitary.sigmaPerp :=
  ⟨psiW ⟨((n : P1) : Dfull), N1_le_Ehat (mem_N1_of_mem_N1P n)⟩,
    psiW_mem_sigmaPerp (mem_N1_of_mem_N1P n)⟩

theorem coe_psiN
    (n : N1P) :
    (psiN n : Wv v0) = psiW ⟨((n : P1) : Dfull), N1_le_Ehat (mem_N1_of_mem_N1P n)⟩ := rfl

theorem psiN_one :
    psiN 1 = 0 := Subtype.ext psiW_one

theorem psiN_mul
    (n m : N1P) : psiN (n * m) = psiN n + psiN m :=
  Subtype.ext (psiW_mul ⟨((n : P1) : Dfull), N1_le_Ehat (mem_N1_of_mem_N1P n)⟩
    ⟨((m : P1) : Dfull), N1_le_Ehat (mem_N1_of_mem_N1P m)⟩)

theorem psiN_inv
    (n : N1P) : psiN n⁻¹ = -psiN n := by
  have h := psiN_mul n⁻¹ n
  rw [inv_mul_cancel, psiN_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

@[expose] def thetaV :
    N1P →* Multiplicative Unitary.W20 where
  toFun n := Multiplicative.ofAdd (Submodule.Quotient.mk (psiN n) : Unitary.W20)
  map_one' := by rw [psiN_one, Submodule.Quotient.mk_zero, ofAdd_zero]
  map_mul' n m := by rw [psiN_mul, Submodule.Quotient.mk_add, ofAdd_add]

theorem thetaV_apply
    (n : N1P) :
    Multiplicative.toAdd (thetaV n) = (Submodule.Quotient.mk (psiN n) : Unitary.W20) := rfl

theorem mem_center_N1P_iff
    (n : N1P) :
    n ∈ Subgroup.center N1P ↔ ((n : P1) : Dfull) ∈ EU Sp8.sigLine := by
  rw [← mem_center_N1 (mem_N1_of_mem_N1P n), Subgroup.mem_center_iff]
  constructor
  · intro h k hk
    have h1 := h ⟨⟨k, N1_le_P1 hk⟩, hk⟩
    exact (congrArg (fun x : N1P => ((x : P1) : Dfull)) h1).symm
  · intro h k
    exact Subtype.ext (Subtype.ext (h _ k.2).symm)

theorem ker_thetaV :
    thetaV.ker = Subgroup.center N1P := by
  ext n
  rw [MonoidHom.mem_ker, mem_center_N1P_iff]
  change Multiplicative.ofAdd (Submodule.Quotient.mk (psiN n) : Unitary.W20) =
    Multiplicative.ofAdd 0 ↔ _
  rw [EmbeddingLike.apply_eq_iff_eq, Submodule.Quotient.mk_eq_zero, mem_unitary_sigLine_iff,
    coe_psiN]
  constructor
  · intro h
    exact mem_EU.2 ⟨_, h⟩
  · intro h
    obtain ⟨_, hU⟩ := mem_EU.1 h
    exact hU

theorem mem_center_of_mk_psiN_eq_zero
    {m : N1P}
    (h : (Submodule.Quotient.mk (psiN m) : Unitary.W20) = 0) : m ∈ Subgroup.center N1P := by
  rw [Submodule.Quotient.mk_eq_zero, mem_unitary_sigLine_iff, coe_psiN] at h
  exact (mem_center_N1P_iff m).2 (mem_EU.2 ⟨_, h⟩)

theorem thetaV_surjective :
    Function.Surjective thetaV := by
  intro w
  obtain ⟨⟨x, hx⟩, hxw⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd w)
  obtain ⟨e, rfl⟩ := psiW_surjective x
  have heN : (e : Dfull) ∈ N1 := by
    rw [N1_eq_EU, orth_sigLine_eq_sigmaPerp]
    exact mem_EU_of hx
  refine ⟨⟨⟨e, N1_le_P1 heN⟩, heN⟩, ?_⟩
  have hpsi : psiN ⟨⟨e, N1_le_P1 heN⟩, heN⟩ = ⟨psiW e, hx⟩ :=
    Subtype.ext (congrArg psiW (Subtype.ext rfl))
  rw [← ofAdd_toAdd w, ← hxw, ← hpsi]
  rfl

@[expose] def vEquiv :
    N1P ⧸ Subgroup.center N1P ≃* Multiplicative Unitary.W20 :=
  (QuotientGroup.quotientMulEquivOfEq ker_thetaV.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective thetaV thetaV_surjective)

theorem vEquiv_mk
    (n : N1P) : vEquiv (n : N1P ⧸ Subgroup.center N1P) = thetaV n := rfl

theorem psiN_conj
    (a : P1) (n : N1P) :
    psiN (MulAut.conjNormal a n) = Unitary.perpEnd (p1Proj a⁻¹) (psiN n) := by
  apply Subtype.ext
  have hconj := psiW_conj (P1_le_Jhat (a⁻¹).2) (N1_le_Ehat (mem_N1_of_mem_N1P n))
  have e : (⟨((a⁻¹ : P1) : Dfull)⁻¹ * ((n : P1) : Dfull) * ((a⁻¹ : P1) : Dfull),
      conj_mem_Ehat (P1_le_Jhat (a⁻¹).2) (N1_le_Ehat (mem_N1_of_mem_N1P n))⟩ : Ehat) =
      ⟨(((MulAut.conjNormal a n : N1P) : P1) : Dfull),
        N1_le_Ehat (mem_N1_of_mem_N1P (MulAut.conjNormal a n))⟩ :=
    Subtype.ext (by
      show ((a⁻¹ : P1) : Dfull)⁻¹ * ((n : P1) : Dfull) * ((a⁻¹ : P1) : Dfull) =
        (((MulAut.conjNormal a n : N1P) : P1) : Dfull)
      rw [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        inv_inv])
  rw [e] at hconj
  calc (psiN (MulAut.conjNormal a n) : Wv v0)
      = psiW ⟨(((MulAut.conjNormal a n : N1P) : P1) : Dfull),
          N1_le_Ehat (mem_N1_of_mem_N1P (MulAut.conjNormal a n))⟩ := coe_psiN _
    _ = wAct v0 (jhatToKv0 ⟨((a⁻¹ : P1) : Dfull), P1_le_Jhat (a⁻¹).2⟩)
          (psiW ⟨((n : P1) : Dfull), N1_le_Ehat (mem_N1_of_mem_N1P n)⟩) := hconj
    _ = wAct v0 (p1Proj a⁻¹) (psiN n) := by rw [coe_p1Proj, coe_psiN]
    _ = _ := (Unitary.perpEnd_apply _ _).symm

theorem thetaV_conj
    (a : P1) (n : N1P) :
    thetaV (MulAut.conjNormal a n) =
      Multiplicative.ofAdd (Unitary.w20End (p1Proj a⁻¹) (Multiplicative.toAdd (thetaV n))) := by
  calc thetaV (MulAut.conjNormal a n)
      = Multiplicative.ofAdd (Submodule.Quotient.mk (psiN (MulAut.conjNormal a n)) :
          Unitary.W20) := rfl
    _ = Multiplicative.ofAdd (Submodule.Quotient.mk (Unitary.perpEnd (p1Proj a⁻¹) (psiN n)) :
          Unitary.W20) :=
        congrArg (fun x => Multiplicative.ofAdd (Submodule.Quotient.mk x : Unitary.W20))
          (psiN_conj a n)
    _ = _ := rfl

theorem vEquiv_conjQuot
    (a : P1) (v : N1P ⧸ Subgroup.center N1P) :
    vEquiv (conjQuot N1P a v) =
      Multiplicative.ofAdd (Unitary.w20End (p1Proj a⁻¹) (Multiplicative.toAdd (vEquiv v))) := by
  induction v using QuotientGroup.induction_on with
  | H n =>
  calc vEquiv (conjQuot N1P a (n : N1P ⧸ Subgroup.center N1P))
      = vEquiv ((MulAut.conjNormal a n : N1P) : N1P ⧸ Subgroup.center N1P) :=
        congrArg vEquiv (conjQuot_mk N1P a n)
    _ = thetaV (MulAut.conjNormal a n) := vEquiv_mk _
    _ = _ := (thetaV_conj a n).trans (congrArg (fun x => Multiplicative.ofAdd
        (Unitary.w20End (p1Proj a⁻¹) (Multiplicative.toAdd x))) (vEquiv_mk n).symm)

theorem w20_commutant
    (φ : Module.End (ZMod 2) Unitary.W20)
    (hφ : ∀ u, φ * Unitary.w20End u = Unitary.w20End u * φ) : φ = 0 ∨ φ = 1 := by
  have hle : Algebra.adjoin (ZMod 2) (Set.range Unitary.w20End) ≤
      Subalgebra.centralizer (ZMod 2) {φ} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨u, rfl⟩
    exact (Subalgebra.mem_centralizer_iff (ZMod 2)).2 fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hφ u
  have hall : ∀ T : Module.End (ZMod 2) Unitary.W20, T * φ = φ * T := by
    intro T
    have hmem : T ∈ Algebra.adjoin (ZMod 2) (Set.range Unitary.w20End) := by
      have h := Unitary.adjoin_w20End
      simp only [h]
      exact Algebra.mem_top
    exact ((Subalgebra.mem_centralizer_iff (ZMod 2)).1 (hle hmem) φ rfl).symm
  have hcen : φ ∈ Subalgebra.center (ZMod 2) (Module.End (ZMod 2) Unitary.W20) :=
    Subalgebra.mem_center_iff.2 hall
  obtain ⟨α, hαc, hα⟩ := Module.End.mem_subalgebraCenter_iff.1 hcen
  have hz2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz2 α with rfl | rfl
  · left
    subst hα
    exact LinearMap.ext fun x => zero_smul _ x
  · right
    subst hα
    exact LinearMap.ext fun x => one_smul _ x

@[expose] def transW
    (ψ : N1P ⧸ Subgroup.center N1P →* N1P ⧸ Subgroup.center N1P) :
    Module.End (ZMod 2) Unitary.W20 :=
  (AddMonoidHom.toMultiplicative.symm
    (vEquiv.toMonoidHom.comp (ψ.comp vEquiv.symm.toMonoidHom))).toZModLinearMap 2

theorem transW_apply
    (ψ : N1P ⧸ Subgroup.center N1P →* N1P ⧸ Subgroup.center N1P)
    (w : Unitary.W20) :
    transW ψ w = Multiplicative.toAdd (vEquiv (ψ (vEquiv.symm (Multiplicative.ofAdd w)))) :=
  rfl

theorem transW_comm
    (ψ : N1P ⧸ Subgroup.center N1P →* N1P ⧸ Subgroup.center N1P)
    (hψ : ∀ a : P1, ψ.comp (conjQuot N1P a) = (conjQuot N1P a).comp ψ) (u : Unitary.Usig) :
    transW ψ * Unitary.w20End u = Unitary.w20End u * transW ψ := by
  obtain ⟨a, ha⟩ := p1Proj_surjective u⁻¹
  have hu : p1Proj a⁻¹ = u := by rw [map_inv, ha, inv_inv]
  subst hu
  refine LinearMap.ext fun w => ?_
  have h1 : Multiplicative.ofAdd (Unitary.w20End (p1Proj a⁻¹) w) =
      vEquiv (conjQuot N1P a (vEquiv.symm (Multiplicative.ofAdd w))) :=
    ((vEquiv_conjQuot a (vEquiv.symm (Multiplicative.ofAdd w))).trans
      (congrArg (fun y => Multiplicative.ofAdd (Unitary.w20End (p1Proj a⁻¹)
        (Multiplicative.toAdd y))) (vEquiv.apply_symm_apply _))).symm
  have h2 : ψ (conjQuot N1P a (vEquiv.symm (Multiplicative.ofAdd w))) =
      conjQuot N1P a (ψ (vEquiv.symm (Multiplicative.ofAdd w))) :=
    congrArg (fun f => f (vEquiv.symm (Multiplicative.ofAdd w))) (hψ a)
  calc (transW ψ * Unitary.w20End (p1Proj a⁻¹)) w
      = Multiplicative.toAdd (vEquiv (ψ (vEquiv.symm
          (Multiplicative.ofAdd (Unitary.w20End (p1Proj a⁻¹) w))))) := rfl
    _ = Multiplicative.toAdd (vEquiv (ψ (vEquiv.symm (vEquiv (conjQuot N1P a
          (vEquiv.symm (Multiplicative.ofAdd w))))))) :=
        congrArg (fun y => Multiplicative.toAdd (vEquiv (ψ (vEquiv.symm y)))) h1
    _ = Multiplicative.toAdd (vEquiv (ψ (conjQuot N1P a
          (vEquiv.symm (Multiplicative.ofAdd w))))) :=
        congrArg (fun y => Multiplicative.toAdd (vEquiv (ψ y))) (vEquiv.symm_apply_apply _)
    _ = Multiplicative.toAdd (vEquiv (conjQuot N1P a
          (ψ (vEquiv.symm (Multiplicative.ofAdd w))))) :=
        congrArg (fun y => Multiplicative.toAdd (vEquiv y)) h2
    _ = Unitary.w20End (p1Proj a⁻¹)
          (Multiplicative.toAdd (vEquiv (ψ (vEquiv.symm (Multiplicative.ofAdd w))))) :=
        congrArg Multiplicative.toAdd (vEquiv_conjQuot a _)
    _ = (Unitary.w20End (p1Proj a⁻¹) * transW ψ) w := rfl

theorem vEquiv_symm_thetaV
    (n : N1P) :
    vEquiv.symm (Multiplicative.ofAdd (Multiplicative.toAdd (thetaV n))) =
      (n : N1P ⧸ Subgroup.center N1P) :=
  vEquiv.symm_apply_eq.2 (vEquiv_mk n).symm

theorem transW_thetaV
    (ψ : N1P ⧸ Subgroup.center N1P →* N1P ⧸ Subgroup.center N1P)
    (n m : N1P) (hm : (m : N1P ⧸ Subgroup.center N1P) = ψ n) :
    transW ψ (Multiplicative.toAdd (thetaV n)) =
      (Submodule.Quotient.mk (psiN m) : Unitary.W20) :=
  calc transW ψ (Multiplicative.toAdd (thetaV n))
      = Multiplicative.toAdd (vEquiv (ψ (vEquiv.symm
          (Multiplicative.ofAdd (Multiplicative.toAdd (thetaV n)))))) := transW_apply ψ _
    _ = Multiplicative.toAdd (vEquiv (ψ (n : N1P ⧸ Subgroup.center N1P))) :=
        congrArg (fun y => Multiplicative.toAdd (vEquiv (ψ y))) (vEquiv_symm_thetaV n)
    _ = Multiplicative.toAdd (vEquiv (m : N1P ⧸ Subgroup.center N1P)) :=
        congrArg (fun y => Multiplicative.toAdd (vEquiv y)) hm.symm
    _ = Multiplicative.toAdd (thetaV m) := congrArg Multiplicative.toAdd (vEquiv_mk m)
    _ = _ := thetaV_apply m

theorem mk_eq_of_mk_psiN_eq
    {n m : N1P}
    (h : (Submodule.Quotient.mk (psiN m) : Unitary.W20) = Submodule.Quotient.mk (psiN n)) :
    (n : N1P ⧸ Subgroup.center N1P) = m := by
  have h2 : psiN (n⁻¹ * m) = psiN m - psiN n :=
    calc psiN (n⁻¹ * m) = psiN n⁻¹ + psiN m := psiN_mul n⁻¹ m
      _ = -psiN n + psiN m := congrArg (· + psiN m) (psiN_inv n)
      _ = psiN m - psiN n := neg_add_eq_sub _ _
  have h3 : (Submodule.Quotient.mk (psiN (n⁻¹ * m)) : Unitary.W20) = 0 :=
    calc (Submodule.Quotient.mk (psiN (n⁻¹ * m)) : Unitary.W20)
        = Submodule.Quotient.mk (psiN m - psiN n) := congrArg Submodule.Quotient.mk h2
      _ = Submodule.Quotient.mk (psiN m) - Submodule.Quotient.mk (psiN n) :=
          Submodule.Quotient.mk_sub _
      _ = 0 := sub_eq_zero.2 h
  exact QuotientGroup.eq.2 (mem_center_of_mk_psiN_eq_zero h3)

theorem end_N1P
    (ψ : N1P ⧸ Subgroup.center N1P →* N1P ⧸ Subgroup.center N1P)
    (hψ : ∀ a : P1, ψ.comp (conjQuot N1P a) = (conjQuot N1P a).comp ψ) :
    ψ = 1 ∨ ψ = MonoidHom.id _ := by
  refine (w20_commutant (transW ψ) (transW_comm ψ hψ)).imp (fun h0 => ?_) (fun h1 => ?_)
  · refine MonoidHom.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H n =>
    have hs := QuotientGroup.mk_surjective (ψ (n : N1P ⧸ Subgroup.center N1P))
    obtain ⟨m, hm⟩ := hs
    have h : (Submodule.Quotient.mk (psiN m) : Unitary.W20) = 0 :=
      (transW_thetaV ψ n m hm).symm.trans
        ((LinearMap.congr_fun h0 _).trans (LinearMap.zero_apply _))
    calc ψ (n : N1P ⧸ Subgroup.center N1P) = (m : N1P ⧸ Subgroup.center N1P) := hm.symm
      _ = 1 := (QuotientGroup.eq_one_iff m).2 (mem_center_of_mk_psiN_eq_zero h)
      _ = (1 : N1P ⧸ Subgroup.center N1P →* N1P ⧸ Subgroup.center N1P)
            (n : N1P ⧸ Subgroup.center N1P) := (MonoidHom.one_apply _).symm
  · refine MonoidHom.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H n =>
    have hs := QuotientGroup.mk_surjective (ψ (n : N1P ⧸ Subgroup.center N1P))
    obtain ⟨m, hm⟩ := hs
    have h : (Submodule.Quotient.mk (psiN m) : Unitary.W20) = Submodule.Quotient.mk (psiN n) :=
      (transW_thetaV ψ n m hm).symm.trans (((LinearMap.congr_fun h1 _).trans
        (Module.End.one_apply _)).trans (thetaV_apply n))
    calc ψ (n : N1P ⧸ Subgroup.center N1P) = (m : N1P ⧸ Subgroup.center N1P) := hm.symm
      _ = n := (mk_eq_of_mk_psiN_eq h).symm
      _ = MonoidHom.id _ (n : N1P ⧸ Subgroup.center N1P) := (MonoidHom.id_apply _ _).symm

end CFSG.Monster.B.GSide
