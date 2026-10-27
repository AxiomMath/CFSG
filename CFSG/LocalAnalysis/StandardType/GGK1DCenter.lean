module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.StandardType.GGK1DTorus
public import CFSG.LocalAnalysis.StandardType.GGK1DBlocks
public import CFSG.LocalAnalysis.StandardType.GGK1DFamily
public import CFSG.LocalAnalysis.StandardType.GGK1DFixed
public import CFSG.LocalAnalysis.StandardType.GGK1DMult
public import CFSG.LocalAnalysis.StandardType.GGK1DCentreless
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial supportedBlock
  isometryCentralizer fixedSpace fixedBlockEquiv restrictFixed mem_supportedBlock
  toLinearMap_pow aeval_reciprocalPolynomial_of_unit monic_reciprocalPolynomial
  irreducible_reciprocalPolynomial coeff_zero_reciprocalPolynomial IsOrbitRepresentatives
  supportedBlock_le_isometryCentralizer reciprocalPolynomial_X_sub_one
      fixedSpace_eq_primaryComponent)
open CFSG.RankThree.PartOne.KCUnitary (root_ne_zero)
open CFSG.RankThree.Classical (IsReciprocalTransversal)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup dicksonHom mem_omegaGroup commSpace)
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open scoped Pointwise
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv)
open CFSG.StandardType.TableBSymp

private theorem ggK1Dn_charP_two {K : Type} [Field K] [Finite K] {nf : ℕ}
    (hK : Nat.card K = 2 ^ nf) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)

private theorem ggK1Dn_prime_cast_ne_zero {p nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) : (p : K) ≠ 0 := by
  haveI : CharP K 2 := ggK1Dn_charP_two hK
  intro h
  rw [CharP.cast_eq_zero_iff K 2] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

private theorem ggK1Dn_fixSub_conj {R : Type} [Group R] (a : R) :
    ggFixSub (MulAut.conj a) = Subgroup.centralizer ({a} : Set R) := by
  ext g
  rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc g * a = (a * g * a⁻¹) * a := by rw [h]
      _ = a * g := by group
  · intro h
    calc a * g * a⁻¹ = (g * a) * a⁻¹ := by rw [h.symm]
      _ = g := by group

private theorem ggK1Dn_conj_eq_one_iff {G : Type} [Group G] (u : G) :
    MulAut.conj u = 1 ↔ u ∈ Subgroup.center G := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun f : MulAut G => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    calc g * u = (u * g * u⁻¹) * u := by rw [hg]
      _ = u * g := by group
  · intro h
    ext g
    rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.mp h g, mul_assoc, mul_inv_cancel, mul_one]
    rfl

private theorem ggK1Dn_dvd_cyclotomic {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {c : K[X]}
    (hc : Irreducible c) (hcm : c.Monic) (hcd : c ∣ X ^ p - 1) (hc1 : c ≠ X - 1) :
    c ∣ cyclotomic p K := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← cyclotomic_prime_mul_X_sub_one K p] at hcd
  rcases hc.prime.dvd_or_dvd hcd with h1 | h1
  · exact h1
  · exfalso
    have heq : c = X - 1 :=
      (eq_of_monic_of_associated hcm (monic_X_sub_C 1)
        (hc.associated_of_dvd (irreducible_X_sub_C 1) h1)).trans (by rw [C_1])
    exact hc1 heq

private theorem ggK1Dn_ordQ_eq_one {K : Type} [Field K] [Finite K] {p nf : ℕ} (hp : p.Prime)
    (h1 : p ∣ 2 ^ nf - 1) (hK : Nat.card K = 2 ^ nf) : OrdPNS.ordQ K p = 1 := by
  have hle : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  have hcast : ((Nat.card K : ℕ) : ZMod p) = 1 := by
    rw [hK]
    have hz : ((2 ^ nf - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h1
    rw [Nat.cast_sub hle, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  rw [OrdPNS.ordQ_def, hcast, orderOf_one]

private theorem ggK1Dn_natDegree_eq_one {K : Type} [Field K] [Finite K] {p nf : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) (h1 : p ∣ 2 ^ nf - 1) (hK : Nat.card K = 2 ^ nf) {h : K[X]}
    (hirr : Irreducible h) (hgd : h ∣ cyclotomic p K) : h.natDegree = 1 := by
  rw [OrdPNS.natDegree_eq_ordQ hp hpK hirr hgd, ggK1Dn_ordQ_eq_one hp h1 hK]

private noncomputable def ggK1Dn_scalarUnit (E M : Type) [Field E] [AddCommGroup M]
    [Module E M] (c : Eˣ) : (Module.End E M)ˣ where
  val := algebraMap E (Module.End E M) (c : E)
  inv := algebraMap E (Module.End E M) ((c⁻¹ : Eˣ) : E)
  val_inv := by
    rw [← (algebraMap E (Module.End E M)).map_mul, Units.mul_inv,
      (algebraMap E (Module.End E M)).map_one]
  inv_val := by
    rw [← (algebraMap E (Module.End E M)).map_mul, Units.inv_mul,
      (algebraMap E (Module.End E M)).map_one]

private theorem ggK1Dn_orderOf_scalarUnit {E M : Type} [Field E] [AddCommGroup M]
    [Module E M] [Nontrivial M] (c : Eˣ) :
    orderOf (ggK1Dn_scalarUnit E M c) = orderOf c := by
  have hinj : Function.Injective (algebraMap E (Module.End E M)) := by
    intro x y h
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    have h1 : x • m = y • m := by
      have := congrArg (fun f : Module.End E M => f m) h
      simpa [Algebra.algebraMap_eq_smul_one'] using this
    have h2 : (x - y) • m = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact h1
    have hxy : x - y = 0 := (smul_eq_zero.mp h2).resolve_right hm
    exact sub_eq_zero.mp hxy
  let f : Eˣ →* (Module.End E M)ˣ := Units.map (algebraMap E (Module.End E M)).toMonoidHom
  have hf : Function.Injective f := by
    intro a b hab
    exact Units.ext (hinj (congrArg Units.val hab))
  have hfc : ggK1Dn_scalarUnit E M c = f c := by
    ext; rfl
  rw [hfc]
  exact orderOf_injective f hf c

private theorem ggK1Dn_scalarUnit_central {E M : Type} [Field E] [AddCommGroup M]
    [Module E M] (c : Eˣ) :
    ggK1Dn_scalarUnit E M c ∈
      Subgroup.center (LinearMap.GeneralLinearGroup E M) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  ext v
  simp only [Units.val_mul, ggK1Dn_scalarUnit, Algebra.algebraMap_eq_smul_one',
    LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply, map_smul]

private theorem ggK1Dn_scalarUnit_mem_unitary {E M : Type} [Field E] [AddCommGroup M]
    [Module E M] {σ : E →+* E} {B : M →ₛₗ[σ] M →ₗ[E] E}
    (c : Eˣ) (hc : σ (c : E) * (c : E) = 1) :
    (ggK1Dn_scalarUnit E M c : LinearMap.GeneralLinearGroup E M) ∈
      CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B := by
  rw [CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
  intro v w
  simp only [ggK1Dn_scalarUnit, Algebra.algebraMap_eq_smul_one', LinearMap.smul_apply,
    Module.End.one_apply]
  rw [map_smulₛₗ, map_smulₛₗ]
  simp only [RingHom.id_apply, smul_eq_mul]
  rw [show σ (c:E) = (c:E)⁻¹ from eq_inv_of_mul_eq_one_left hc]
  have hc0 : (c:E) ≠ 0 := Units.ne_zero c
  field_simp
  simp

private theorem ggK1Dn_fixed_torus_plus {p d nf : ℕ} {K V : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf)
    (hd : d = ggMultOrd p nf) (hd1 : d = 1)
    (hW : Module.finrank K (fixedSpace x) = 2)
    (hplus : IsPlusType (Q.comp (fixedSpace x).subtype)) :
    ∃ e ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q, orderOf e = p ∧
      ∀ g ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q, Commute e g := by
  classical
  have hWnd : (Q.comp (fixedSpace x).subtype).polarBilin.Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have h1 : p ∣ 2 ^ nf - 1 := by
    have hgm : ggMultOrd p nf = 1 := by rw [← hd]; exact hd1
    by_contra hc
    unfold ggMultOrd at hgm
    rw [if_neg hc] at hgm
    split_ifs at hgm <;> omega
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact h1
  obtain ⟨e0, he0mem, he0ord⟩ := ggK1D_torus_exists hWnd hW hp (Or.inl ⟨hplus, hpq⟩)
  have he0O : (e0 : fixedSpace x ≃ₗ[K] fixedSpace x) ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
    (mem_omegaGroup.mp he0mem).1
  let g : ↥(supportedBlock Q x (X - 1)) := (fixedBlockEquiv hx).symm ⟨e0, he0O⟩
  have hg_restrict : restrictFixed Q x g = e0 :=
    congrArg Subtype.val ((fixedBlockEquiv hx).apply_symm_apply ⟨e0, he0O⟩)
  have hX1mem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra h
    have hbot : primaryComponent x.toLinearMap (X - 1) = ⊥ :=
      CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
        (CFSG.RankThree.PartOne.KCOrthogonal.irreducible_X_sub_one)
        (CFSG.RankThree.PartOne.KCOrthogonal.monic_X_sub_one) h
    rw [CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace_eq_primaryComponent, hbot,
      finrank_bot] at hW
    omega
  have hΩ : orthDerived Q = omegaGroup Q hQ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
  have hgO : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp
      (CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock_le_isometryCentralizer (X - 1) g.2)).1
  have he_orth : (g : V ≃ₗ[K] V) ∈ orthDerived Q := by
    rw [hΩ, mem_omegaGroup]
    refine ⟨hgO, ?_⟩
    have h1 : Module.finrank K (commSpace (g : V ≃ₗ[K] V)) =
        Module.finrank K (commSpace e0) := by
      rw [hx.finrank_commSpace_eq_restrictFixed g.2, hg_restrict]
    rw [h1]
    exact (mem_omegaGroup.mp he0mem).2
  have hg_mem : (g : V ≃ₗ[K] V) ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q :=
    Subgroup.mem_inf.mpr ⟨g.2, he_orth⟩
  have hord_g : orderOf (g : V ≃ₗ[K] V) = p := by
    have hcoe : orderOf (g : V ≃ₗ[K] V) = orderOf g := Subgroup.orderOf_coe g
    have h1 : orderOf (fixedBlockEquiv hx g) = orderOf g :=
      orderOf_injective (fixedBlockEquiv hx).toMonoidHom (fixedBlockEquiv hx).injective g
    have h2 : orderOf (fixedBlockEquiv hx g) = orderOf e0 := by
      rw [(fixedBlockEquiv hx).apply_symm_apply ⟨e0, he0O⟩]
      exact (orderOf_injective (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)))
        (Subgroup.subtype_injective _) ⟨e0, he0O⟩).symm
    rw [hcoe]
    exact h1.symm.trans (h2.trans he0ord)
  have hcomm : ∀ h ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q,
      Commute (g : V ≃ₗ[K] V) h :=
    ggK1D_fixed_abelian hx hQ hT (m := 1) (by norm_num)
      (by rw [← CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace_eq_primaryComponent]; omega)
      g hg_mem
  exact ⟨(g : V ≃ₗ[K] V), hg_mem, hord_g, hcomm⟩

private theorem ggK1Dn_fixed_torus_minus {p d nf : ℕ} {K V : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf)
    (hd : d = ggMultOrd p nf) (hd2 : d = 2)
    (hW : Module.finrank K (fixedSpace x) = 2)
    (hminus : ¬ IsPlusType (Q.comp (fixedSpace x).subtype)) :
    ∃ e ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q, orderOf e = p ∧
      ∀ g ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q, Commute e g := by
  classical
  have hWnd : (Q.comp (fixedSpace x).subtype).polarBilin.Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have h1 : p ∣ 2 ^ nf + 1 := by
    by_contra hc
    have hgm : ggMultOrd p nf = 2 := by rw [← hd]; exact hd2
    unfold ggMultOrd at hgm
    by_cases hsub : p ∣ 2 ^ nf - 1
    · rw [if_pos hsub] at hgm; omega
    · rw [if_neg hsub, if_neg hc] at hgm; omega
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact h1
  obtain ⟨e0, he0mem, he0ord⟩ := ggK1D_torus_exists hWnd hW hp (Or.inr ⟨hminus, hpq⟩)
  have he0O : (e0 : fixedSpace x ≃ₗ[K] fixedSpace x) ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
    (mem_omegaGroup.mp he0mem).1
  let g : ↥(supportedBlock Q x (X - 1)) := (fixedBlockEquiv hx).symm ⟨e0, he0O⟩
  have hg_restrict : restrictFixed Q x g = e0 :=
    congrArg Subtype.val ((fixedBlockEquiv hx).apply_symm_apply ⟨e0, he0O⟩)
  have hΩ : orthDerived Q = omegaGroup Q hQ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
  have hgO : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp
      (CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock_le_isometryCentralizer (X - 1) g.2)).1
  have he_orth : (g : V ≃ₗ[K] V) ∈ orthDerived Q := by
    rw [hΩ, mem_omegaGroup]
    refine ⟨hgO, ?_⟩
    have h1 : Module.finrank K (commSpace (g : V ≃ₗ[K] V)) =
        Module.finrank K (commSpace e0) := by
      rw [hx.finrank_commSpace_eq_restrictFixed g.2, hg_restrict]
    rw [h1]
    exact (mem_omegaGroup.mp he0mem).2
  have hg_mem : (g : V ≃ₗ[K] V) ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q :=
    Subgroup.mem_inf.mpr ⟨g.2, he_orth⟩
  have hord_g : orderOf (g : V ≃ₗ[K] V) = p := by
    have hcoe : orderOf (g : V ≃ₗ[K] V) = orderOf g := Subgroup.orderOf_coe g
    have h1 : orderOf (fixedBlockEquiv hx g) = orderOf g :=
      orderOf_injective (fixedBlockEquiv hx).toMonoidHom (fixedBlockEquiv hx).injective g
    have h2 : orderOf (fixedBlockEquiv hx g) = orderOf e0 := by
      rw [(fixedBlockEquiv hx).apply_symm_apply ⟨e0, he0O⟩]
      exact (orderOf_injective (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)))
        (Subgroup.subtype_injective _) ⟨e0, he0O⟩).symm
    rw [hcoe]
    exact h1.symm.trans (h2.trans he0ord)
  have hcomm : ∀ h ∈ supportedBlock Q x (X - 1) ⊓ orthDerived Q,
      Commute (g : V ≃ₗ[K] V) h :=
    ggK1D_fixed_abelian hx hQ hT (m := 1) (by norm_num)
      (by rw [← CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace_eq_primaryComponent]; omega)
      g hg_mem
  exact ⟨(g : V ≃ₗ[K] V), hg_mem, hord_g, hcomm⟩

private theorem ggK1Dn_block_elemAbelian {p : ℕ} {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hp : p.Prime) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Subgroup (V ≃ₗ[K] V))
    (hind : iSupIndep A)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (B : Subgroup (V ≃ₗ[K] V)) (hAB : ∀ i, A i ≤ B)
    (e : ι → V ≃ₗ[K] V) (hmem : ∀ i, e i ∈ A i)
    (hp_pow : ∀ i, e i ^ p = 1)
    (hord : ∀ i, orderOf (e i) = p)
    (hcent : ∀ i, ∀ g ∈ B, Commute (e i) g) :
    ∃ E0 : Subgroup (V ≃ₗ[K] V), IsElemAbelian p E0 ∧
      Nat.card E0 = p ^ Fintype.card ι ∧
      E0 ≤ Subgroup.centralizer (B : Set (V ≃ₗ[K] V)) ∧
      E0 ≤ ⨆ i, A i := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let φ : (i : ι) → Multiplicative (ZMod p) →* (V ≃ₗ[K] V) := fun i => zmodPowHom (hp_pow i)
  have hφmem : ∀ (i : ι) (a : Multiplicative (ZMod p)), φ i a ∈ A i := by
    intro i a
    have h : φ i a ∈ Subgroup.zpowers (e i) := by
      refine Subgroup.mem_zpowers_iff.mpr ?_
      exact ⟨(a : Multiplicative (ZMod p)).toAdd.val, by rw [zmodPowHom_apply]; rfl⟩
    exact Subgroup.zpowers_le.mpr (hmem i) h
  have hcommφ : Pairwise fun i j => ∀ a b, Commute (φ i a) (φ j b) := by
    intro i j hij a b
    exact hcomm i j hij _ (hφmem i a) _ (hφmem j b)
  let F : ((i : ι) → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V) :=
    MonoidHom.noncommPiCoprod φ hcommφ
  have hφinj : ∀ i, Function.Injective (φ i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro a ha
    exact (zmodPowHom_eq_one_iff (hp_pow i) (hord i)).mp ha
  have hind' : iSupIndep fun i => (φ i).range :=
    hind.mono (fun i => by
      rintro _ ⟨a, rfl⟩
      exact hφmem i a)
  have hinjF : Function.Injective F :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep φ hind' hφinj
  let E0 : Subgroup (V ≃ₗ[K] V) := F.range
  have hab : IsElemAbelian p E0 := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
      exact (map_mul F x y).symm.trans
        ((congrArg F (mul_comm x y)).trans (map_mul F y x))
    · intro z hz
      obtain ⟨a, ha⟩ := hz
      rw [← ha, ← map_pow]
      have hap : a ^ p = 1 := by
        ext i
        simpa [Fintype.card_multiplicative, ZMod.card] using pow_card_eq_one (x := a i)
      rw [hap, map_one]
  have hcard : Nat.card E0 = p ^ Fintype.card ι := by
    calc Nat.card E0
        = Nat.card ((i : ι) → Multiplicative (ZMod p)) :=
          Nat.card_congr (MonoidHom.ofInjective hinjF).toEquiv.symm
      _ = ∏ i : ι, Nat.card (Multiplicative (ZMod p)) := Nat.card_pi
      _ = ∏ _i : ι, p := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp [Nat.card_eq_fintype_card, ZMod.card]
      _ = p ^ Fintype.card ι := by simp
  have hcenter : E0 ≤ Subgroup.centralizer (B : Set (V ≃ₗ[K] V)) := by
    intro z hz
    have hzF : z ∈ F.range := hz
    rw [MonoidHom.noncommPiCoprod_range] at hzF
    have hle : (⨆ i, (φ i).range) ≤ Subgroup.centralizer (B : Set (V ≃ₗ[K] V)) := by
      refine iSup_le fun i => ?_
      rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [zmodPowHom_apply]
      exact ((hcent i g hg).pow_left _).eq.symm
    exact hle hzF
  have hleF : E0 ≤ ⨆ i, A i := by
    have : F.range ≤ ⨆ i, A i := by
      rw [MonoidHom.noncommPiCoprod_range]
      refine iSup_le (fun i => ?_)
      rintro _ ⟨a, rfl⟩
      exact Subgroup.mem_iSup_of_mem i (hφmem i a)
    exact this
  exact ⟨E0, hab, hcard, hcenter, hleF⟩

private theorem ggK1Dn_range_succ_cons (n : ℕ) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => simp
  | succ n ih =>
      conv_lhs => rw [List.range_succ, ih]
      rw [List.cons_append]
      simp [List.range_succ, List.map_append]

private theorem ggK1Dn_filter_range_getD_length (l : List ℕ) :
    ((List.range l.length).filter (fun k => decide (0 < l.getD k 0))).length =
      (l.filter (fun a => decide (a ≠ 0))).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.length_cons, ggK1Dn_range_succ_cons t.length, List.filter_cons]
      have hmap : ((List.range t.length).map Nat.succ).filter
            (fun k => decide (0 < (a :: t).getD k 0))
          = ((List.range t.length).filter (fun j => decide (0 < t.getD j 0))).map Nat.succ := by
        rw [List.filter_map]
        apply congrArg (List.map Nat.succ)
        apply List.filter_congr
        intro j _
        simp [Function.comp_apply, List.getD_cons_succ]
      by_cases hp : 0 < a
      · have ha' : a ≠ 0 := Nat.pos_iff_ne_zero.mp hp
        rw [if_pos (by simpa using hp), List.length_cons, hmap, List.length_map, ih,
          List.filter_cons, if_pos (by simp [ha']), List.length_cons]
      · have ha : a = 0 := by omega
        rw [if_neg (by simpa using hp), hmap, List.length_map, ih,
          List.filter_cons, if_neg (by simp [ha])]

private theorem ggK1Dn_rZ_filter (p : ℕ) (m : List ℕ)
    (hlen : m.length = (p - 1) / 2 + 1) :
    ((List.range ((p - 1) / 2 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length =
      (m.tail.filter (fun j => decide (j ≠ 0))).length := by
  rw [← hlen]
  cases m with
  | nil => simp
  | cons a t =>
      rw [List.length_cons, List.tail_cons]
      have h1 : (List.range (t.length + 1)).filter
            (fun j => decide (1 ≤ j ∧ 0 < (a :: t).getD j 0))
          = ((List.range t.length).filter (fun k => decide (0 < t.getD k 0))).map Nat.succ := by
        rw [ggK1Dn_range_succ_cons t.length]
        rw [List.filter_cons]
        rw [if_neg (by simp)]
        rw [List.filter_map]
        congr 1
      rw [h1, List.length_map, ggK1Dn_filter_range_getD_length t]

private theorem ggK1Dn_rZ_eq_tail (p nf d : ℕ) (tw : Bool) (m : List ℕ)
    (hlen : m.length = (p - 1) / 2 + 1) :
    (ggMultDatumD p nf d tw m).rZ =
      (m.tail.filter (fun j => decide (j ≠ 0))).length +
        (if m.headD 0 = 1 ∧ ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
          (ggMultEps0 p d tw m = false ∧ d = 2)) then 1 else 0) := by
  have hF := ggK1Dn_rZ_filter p m hlen
  unfold ggMultDatumD
  dsimp only
  rw [hF]
  by_cases hc : m.headD 0 = 1 ∧ ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
      (ggMultEps0 p d tw m = false ∧ d = 2))
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]; omega

private theorem ggK1Dn_card_tail_eq (p nf d : ℕ) (tw : Bool) (m : List ℕ) (tail : ℕ)
    (hlen : m.length = (p - 1) / 2 + 1)
    (htail : tail = (m.tail.filter (fun j => decide (j ≠ 0))).length) :
    Fintype.card (Fin tail ⊕ {_u : Unit // m.headD 0 = 1 ∧
        ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
          (ggMultEps0 p d tw m = false ∧ d = 2))}) =
      (ggMultDatumD p nf d tw m).rZ := by
  rw [ggK1Dn_rZ_eq_tail p nf d tw m hlen, htail, Fintype.card_sum, Fintype.card_fin]
  by_cases hc : m.headD 0 = 1 ∧ ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
      (ggMultEps0 p d tw m = false ∧ d = 2))
  · rw [if_pos hc]
    have h1 : Fintype.card {_u : Unit // m.headD 0 = 1 ∧
        ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
          (ggMultEps0 p d tw m = false ∧ d = 2))} = 1 := by
      have e : {_u : Unit // m.headD 0 = 1 ∧
          ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
            (ggMultEps0 p d tw m = false ∧ d = 2))} ≃ Unit :=
        ⟨fun _ => ⟨⟩, fun _ => ⟨⟨⟩, hc⟩,
          fun y => Subtype.ext (Subsingleton.elim _ _), fun _ => rfl⟩
      rw [Fintype.card_congr e, Fintype.card_unit]
    omega
  · rw [if_neg hc]
    have h1 : Fintype.card {_u : Unit // m.headD 0 = 1 ∧
        ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
          (ggMultEps0 p d tw m = false ∧ d = 2))} = 0 := by
      have e : {_u : Unit // m.headD 0 = 1 ∧
          ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
            (ggMultEps0 p d tw m = false ∧ d = 2))} ≃ Empty :=
        ⟨fun y => (hc y.2).elim, fun y => y.elim,
          fun y => (hc y.2).elim, fun y => y.elim⟩
      rw [Fintype.card_congr e, Fintype.card_empty]
    omega

private theorem ggK1Dn_finish {p nf d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {Q : (ι → K) → K} (tw : Bool)
    {x : ↥(LargeEvenOmega Q)} {m : List ℕ} {n : ℕ}
    (hcenterR : Subgroup.center (LargeEvenProj (LargeEvenOmega Q)) = ⊥)
    (E : Subgroup (LargeEvenProj (LargeEvenOmega Q)))
    (hEab : IsElemAbelian p E) (hEcard : Nat.card E = p ^ n)
    (hEC : E ≤ Subgroup.centralizer
      ({LargeEvenProjMk (LargeEvenOmega Q) x} : Set (LargeEvenProj (LargeEvenOmega Q))))
    (hEcent : ∀ z ∈ E, ∀ g ∈ Subgroup.centralizer
      ({LargeEvenProjMk (LargeEvenOmega Q) x} : Set (LargeEvenProj (LargeEvenOmega Q))),
      g * z = z * g)
    (hrZ : (ggMultDatumD p nf d tw m).rZ = n) :
    GGK1Center p (ggMultDatumD p nf d tw m)
      (LargeEvenProj (LargeEvenOmega Q))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega Q)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega Q) x)) := by
  intro h2
  refine ⟨E, hEab, ?_, ?_, ?_, ?_⟩
  · rw [hrZ]; exact hEcard
  · intro z hz
    rw [ggK1Dn_fixSub_conj]
    exact hEC hz
  · intro z hz g hg
    rw [ggK1Dn_fixSub_conj] at hg
    exact hEcent z hz g hg
  · intro ψ hψ _ hcomm z hz
    rcases hψ with ⟨s, rfl⟩
    have hconj_mul : ∀ u v : LargeEvenProj (LargeEvenOmega Q),
        MulAut.conj (u * v) = MulAut.conj u * MulAut.conj v := by
      intro u v; ext g; simp [MulAut.conj_apply, mul_assoc]
    have hconj_inv : ∀ u : LargeEvenProj (LargeEvenOmega Q),
        MulAut.conj u⁻¹ = (MulAut.conj u)⁻¹ := by
      intro u; ext g; simp [MulAut.conj_apply]
    have hsC : s ∈ Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenOmega Q) x} : Set (LargeEvenProj (LargeEvenOmega Q))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : MulAut.conj (s * LargeEvenProjMk (LargeEvenOmega Q) x) =
          MulAut.conj (LargeEvenProjMk (LargeEvenOmega Q) x * s) := by
        rw [hconj_mul, hconj_mul]
        exact hcomm.eq
      have h2 : MulAut.conj ((s * LargeEvenProjMk (LargeEvenOmega Q) x) *
          (LargeEvenProjMk (LargeEvenOmega Q) x * s)⁻¹) = 1 := by
        rw [hconj_mul, hconj_inv, h1, mul_inv_cancel]
      have h3 : (s * LargeEvenProjMk (LargeEvenOmega Q) x) *
          (LargeEvenProjMk (LargeEvenOmega Q) x * s)⁻¹ ∈
          Subgroup.center (LargeEvenProj (LargeEvenOmega Q)) :=
        (ggK1Dn_conj_eq_one_iff _).mp h2
      rw [hcenterR, Subgroup.mem_bot] at h3
      exact mul_inv_eq_one.mp h3
    have hsz : s * z = z * s := hEcent z hz s hsC
    change s * z * s⁻¹ = z
    rw [hsz, mul_assoc, mul_inv_cancel, mul_one]

private theorem ggK1Dn_eq_zero_of_sum_eq_zero {l : List ℕ} (h : l.sum = 0) :
    ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons b t ih =>
      intro a ha
      simp only [List.sum_cons] at h
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · exact ih (by omega) a ha

private theorem ggK1Dn_card_sq_eq_one {p nf : ℕ} (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) :
    (((2 ^ nf : ℕ) : ZMod p)) ^ 2 = 1 := by
  have hpos : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  rcases hdvd with h1 | h1
  · have h0 : (((2 ^ nf - 1 : ℕ) : ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    rw [Nat.cast_sub hpos, sub_eq_zero] at h0
    rw [h0]; simp
  · have h0 : (((2 ^ nf + 1 : ℕ) : ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    rw [Nat.cast_add, Nat.cast_one] at h0
    have h2 : ((2 ^ nf : ℕ) : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h0
    rw [h2]; simp

private theorem ggK1Dn_natDegree_le_two {K : Type} [Field K] [Fintype K] {p nf : ℕ}
    (hp : p.Prime) (hpchar : p ≠ ringChar K) (hK : Fintype.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) {h : K[X]} (hirr : Irreducible h)
    (hmon : h.Monic) (hdvdX : h ∣ X ^ p - 1) (hne : h ≠ X - 1) : h.natDegree ≤ 2 := by
  rw [ggK1CBl_ff_degree hp hpchar hirr hmon hdvdX hne]
  have hsq : ((Fintype.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [hK]; exact ggK1Dn_card_sq_eq_one hdvd
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hsq)

private lemma ggK1Dn_selfDual_card {p nf : ℕ} {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf (AdjoinRoot h),
      h.natDegree = 2 ∧ Nat.card (AdjoinRoot h) = (2 ^ nf) ^ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := (mem_primaryFactors.mp hh).2.1
  have hdvdX : h ∣ X ^ p - 1 := hx.dvd_X_pow_sub_one hh
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hrc : ringChar K = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hK]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : nf ≠ 0))
  have hpchar : p ≠ ringChar K := by rw [hrc]; exact hp2
  have hcardK : Fintype.card K = 2 ^ nf := by rw [Fintype.card_eq_nat_card, hK]
  have hle2 : h.natDegree ≤ 2 :=
    ggK1Dn_natDegree_le_two hp hpchar hcardK hdvd hirr hmon hdvdX hne1
  obtain ⟨d, _, hndeg, -⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry.exists_selfDual_hermitian
      hx hpodd hh hne1 hself
  have hpos : 0 < h.natDegree := hirr.natDegree_pos
  have hd1 : d = 1 := by omega
  have hndeg2 : h.natDegree = 2 := by omega
  have hcard : Nat.card (AdjoinRoot h) = (2 ^ nf) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K),
      CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot, hndeg2, hK]
  exact ⟨⟨Nat.prime_two, hnf, by rw [hcard, ← pow_mul, mul_comm]⟩, hndeg2, hcard⟩

private theorem ggK1Dn_selfDual_unitary {p nf : ℕ} {K V : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf (AdjoinRoot h))
      (Hf : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
      Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) =
        primaryMultiplicity x.toLinearMap h ∧
      Nonempty (↥(supportedBlock Q x h) ≃*
        CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hU, hndeg2, hcard⟩ := ggK1Dn_selfDual_card hx hp hp2 hnf hK hdvd hh hne1 hself
  obtain ⟨d, H, hndeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry.exists_selfDual_hermitian
      hx (hp.odd_of_ne_two hp2) hh hne1 hself
  have hd1 : d = 1 := by omega
  have hbar' : ∀ z, CFSG.RankThree.PartOne.KCOrthogonal.frobPow K (AdjoinRoot h) d z =
      hU.bar z := by
    intro z
    rw [hd1, CFSG.RankThree.PartOne.KCOrthogonal.frobPow_apply, hU.bar_apply, hK, pow_one]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (CFSG.RankThree.PartOne.KCOrthogonal.blockGL Q x h).range =
      CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH,
      CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
    exact Iff.rfl
  exact ⟨hU, B, hBsymm, hBl, rfl,
    ⟨(MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)⟩⟩

private theorem ggK1Dn_paired_scalar' {p nf : ℕ} {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hpq : p ∣ Nat.card K - 1) :
    ∃ e ∈ supportedBlock Q x h, e ^ p = 1 ∧ orderOf e = p ∧
      ∀ g ∈ supportedBlock Q x h, Commute e g := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hpK : (p : K) ≠ 0 := ggK1Dn_prime_cast_ne_zero hp hp2 hK
  have h1 : p ∣ 2 ^ nf - 1 := by rw [hK] at hpq; exact hpq
  have hgd : h ∣ cyclotomic p K := ggK1Dn_dvd_cyclotomic hp hirr
    (monic_of_mem_primaryFactors hh) (hx.dvd_X_pow_sub_one hh) hne1
  have hdeg : h.natDegree = 1 := ggK1Dn_natDegree_eq_one hp hpK h1 hK hirr hgd
  haveI : Nontrivial (primaryComponent x.toLinearMap h) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hx.squarefree_minpoly hh)
  have hcardE : Nat.card (AdjoinRoot h) = Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K),
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg, pow_one]
  have hdvdE : p ∣ Nat.card (AdjoinRoot h)ˣ := by
    rw [Nat.card_units, hcardE, hK]; exact h1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (AdjoinRoot h)ˣ) p hdvdE
  let s : LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    ggK1Dn_scalarUnit (AdjoinRoot h) (primaryComponent x.toLinearMap h) ζ
  have hsord : orderOf s = p := by rw [ggK1Dn_orderOf_scalarUnit ζ, hζ]
  have hscen : s ∈ Subgroup.center
      (LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :=
    ggK1Dn_scalarUnit_central ζ
  let φ : ↥(supportedBlock Q x h) ≃* LinearMap.GeneralLinearGroup (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) :=
    CFSG.RankThree.PartOne.KCOrthogonal.pairedBlockEquiv hx hh hne
  let e : ↥(supportedBlock Q x h) := φ.symm s
  have hmem : (e : V ≃ₗ[K] V) ∈ supportedBlock Q x h := e.2
  have hord : orderOf (e : V ≃ₗ[K] V) = p := by
    have h1 : orderOf (e : V ≃ₗ[K] V) = orderOf e := Subgroup.orderOf_coe e
    have h2 : orderOf e = orderOf s :=
      orderOf_injective φ.symm.toMonoidHom φ.symm.injective s
    rw [h1, h2, hsord]
  refine ⟨(e : V ≃ₗ[K] V), hmem, ?_, hord, ?_⟩
  · rw [← hord]; exact pow_orderOf_eq_one _
  · intro g hg
    change (e : V ≃ₗ[K] V) * g = g * (e : V ≃ₗ[K] V)
    have hsub : e * ⟨g, hg⟩ = ⟨g, hg⟩ * e := by
      apply φ.injective
      rw [map_mul, map_mul]
      rw [show φ e = s from φ.apply_symm_apply s]
      exact (Subgroup.mem_center_iff.mp hscen (φ ⟨g, hg⟩)).symm
    simpa [Subgroup.coe_mul] using congrArg Subtype.val hsub

private theorem ggK1Dn_selfDual_scalar' {p nf : ℕ} {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hpq : p ∣ 2 ^ nf + 1) :
    ∃ e ∈ supportedBlock Q x h, e ^ p = 1 ∧ orderOf e = p ∧
      ∀ g ∈ supportedBlock Q x h, Commute e g := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Nontrivial (primaryComponent x.toLinearMap h) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hx.squarefree_minpoly hh)
  obtain ⟨hU, Hf, hHsymm, hHsep, hWdim, ⟨φ⟩⟩ :=
    ggK1Dn_selfDual_unitary hx hp hp2 hnf hK hdvd hh hne1 hself
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζord, hζnorm⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hU hp hpq
  have hζval : (ζ : AdjoinRoot h) ^ (2 ^ nf + 1) = 1 := by
    simpa using congrArg (fun u : (AdjoinRoot h)ˣ => (u : AdjoinRoot h)) hζnorm
  have hnormζ : hU.bar (ζ : AdjoinRoot h) * (ζ : AdjoinRoot h) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← pow_succ]
    exact hζval
  let s : LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    ggK1Dn_scalarUnit (AdjoinRoot h) (primaryComponent x.toLinearMap h) ζ
  have hsunit : s ∈ CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf :=
    ggK1Dn_scalarUnit_mem_unitary ζ hnormζ
  let e : ↥(supportedBlock Q x h) := φ.symm ⟨s, hsunit⟩
  have hmem : (e : V ≃ₗ[K] V) ∈ supportedBlock Q x h := e.2
  have hord : orderOf (e : V ≃ₗ[K] V) = p := by
    have h0 : orderOf (e : V ≃ₗ[K] V) = orderOf e := Subgroup.orderOf_coe e
    have h1 : orderOf e =
        orderOf (⟨s, hsunit⟩ : CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) :=
      orderOf_injective φ.symm.toMonoidHom φ.symm.injective ⟨s, hsunit⟩
    have h2 : orderOf (⟨s, hsunit⟩ :
        CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) = orderOf s :=
      (Subgroup.orderOf_coe ⟨s, hsunit⟩).symm
    have h3 : orderOf s = orderOf ζ := ggK1Dn_orderOf_scalarUnit ζ
    rw [h0, h1, h2, h3, hζord]
  refine ⟨(e : V ≃ₗ[K] V), hmem, ?_, hord, ?_⟩
  · rw [← hord]; exact pow_orderOf_eq_one _
  · intro g hg
    change (e : V ≃ₗ[K] V) * g = g * (e : V ≃ₗ[K] V)
    have hsub : e * ⟨g, hg⟩ = ⟨g, hg⟩ * e := by
      apply φ.injective
      rw [map_mul, map_mul]
      rw [show φ e = (⟨s, hsunit⟩ :
        CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) from
          φ.apply_symm_apply ⟨s, hsunit⟩]
      apply Subtype.ext
      have hc : s ∈ Subgroup.center
          (LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :=
        ggK1Dn_scalarUnit_central ζ
      exact (Subgroup.mem_center_iff.mp hc (φ ⟨g, hg⟩ :
        LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h))).symm
    simpa [Subgroup.coe_mul] using congrArg Subtype.val hsub

private lemma ggK1Dn_supportedBlock_le_orthDerived {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1) :
    supportedBlock Q x r ≤ orthDerived Q := by
  intro g hg
  exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
      ⟨(Subgroup.mem_inf.mp
        (CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock_le_isometryCentralizer r hg)).1,
        hx.even_finrank_commSpace_of_mem_supportedBlock hp2 hr hne1 hg⟩)

private lemma ggK1Dn_polarBilin_nondegenerate {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) : Q.polarBilin.Nondegenerate :=
  ⟨fun v hv => hx.regular v fun w => hv w,
    fun w hw => hx.regular w fun v => by
      rw [← QuadraticMap.polar_comm]
      exact hw v⟩

private lemma ggK1Dn_exists_totallySingular_three {K V : Type*} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 8 ≤ Module.finrank K V) :
    ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨n, hn⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hn4 : 4 ≤ n := by rw [hn] at hdim; omega
  obtain ⟨-, -, -, -, -, h3pairs⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms Q hQ
  have hn' : Module.finrank K V = 2 * n := by omega
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := h3pairs n hn' hn4
  exact CFSG.ClassicalGroups.Orthogonal.exists_totallySingular_of_hypPairs h12 h13 h23

private theorem ggK1Dn_finish_plus {p nf d r n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hr : 1 ≤ r) {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hcenterR : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) = ⊥)
    (E0 : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)))
    (hE0ab : IsElemAbelian p E0) (hE0card : Nat.card E0 = p ^ n)
    (hE0le : E0 ≤ orthDerived (TableBOrth.qPlusForm K r))
    (hE0cent : ∀ z ∈ E0, ∀ g ∈ (isometryCentralizer (TableBOrth.qPlusForm K r)
        (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) ⊓ orthDerived (TableBOrth.qPlusForm K r)),
        g * z = z * g)
    (hrz : (ggMultDatumD p nf d false m).rZ = n) :
    GGK1Center p (ggMultDatumD p nf d false m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)) := by
  classical
  let Qf : QuadraticForm K (Fin r ⊕ Fin r → K) := TableBOrth.qPlusForm K r
  let O : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
    TauCeti.QuadraticMap.orthogonalGroup Qf
  let L : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) := ⁅O, O⁆
  have hL : L = orthDerived Qf := rfl
  have hscal : (LargeEvenScalars (Fin r ⊕ Fin r) K).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K r)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) hr
  have hcomap : LargeEvenOmega (LargeEvenQPlus K r) =
      Subgroup.comap (toLinEquiv (Fin r ⊕ Fin r) K).toMonoidHom L :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (Q := Qf) (Q₀ := LargeEvenQPlus K r) (by rw [TableBOrth.coe_qPlusForm])
  have hmap : (LargeEvenOmega (LargeEvenQPlus K r)).map
      (toLinEquiv (Fin r ⊕ Fin r) K).toMonoidHom = L := by
    rw [hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ _).surjective L
  let eΩ : LargeEvenOmega (LargeEvenQPlus K r) ≃* L :=
    (MulEquiv.subgroupMap (toLinEquiv (Fin r ⊕ Fin r) K)
      (LargeEvenOmega (LargeEvenQPlus K r))).trans (MulEquiv.subgroupCongr hmap)
  let Ψ : L ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)) :=
    eΩ.symm.trans (TableBOrth.projMkEquiv hscal)
  have hΨt : Ψ (eΩ x) = LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x := by
    change TableBOrth.projMkEquiv hscal (eΩ.symm (eΩ x)) = _
    rw [MulEquiv.symm_apply_apply]
    exact TableBOrth.projMkEquiv_apply hscal x
  have heΩ : (eΩ x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      ggK1DLin (x : GL (Fin r ⊕ Fin r) K) := rfl
  have hE0leL : E0 ≤ L := hE0le
  let E1 : Subgroup ↥L := E0.subgroupOf L
  let E : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) :=
    E1.map Ψ.toMonoidHom
  have hcardE1 : Nat.card E1 = Nat.card E0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0leL).toEquiv
  have hcardE : Nat.card E = Nat.card E0 := by
    rw [Subgroup.card_map_of_injective Ψ.injective, hcardE1]
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a1, ha1, ha⟩ := a.2
      obtain ⟨b1, hb1, hb⟩ := b.2
      change a.1 * b.1 = b.1 * a.1
      rw [← ha, ← hb]
      change Ψ a1 * Ψ b1 = Ψ b1 * Ψ a1
      rw [← Ψ.map_mul, ← Ψ.map_mul]
      exact congrArg Ψ (Subtype.coe_injective (congrArg
        (fun x : ↥E0 => (x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)))
        (hE0ab.1.is_comm.comm ⟨(a1 : _), Subgroup.mem_subgroupOf.mp ha1⟩
          ⟨(b1 : _), Subgroup.mem_subgroupOf.mp hb1⟩)))
    · intro z hz
      obtain ⟨z1, hz1, hz⟩ := hz
      rw [← hz, ← map_pow]
      have hzp : z1 ^ p = 1 := by
        apply Subtype.coe_injective
        exact hE0ab.2 (z1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
          (Subgroup.mem_subgroupOf.mp hz1)
      rw [hzp, map_one]
  have hxO_mem : ggK1DLin (x : GL (Fin r ⊕ Fin r) K) ∈
      TauCeti.QuadraticMap.orthogonalGroup Qf := by
    rw [← heΩ]
    exact Subgroup.commutator_le_self O (eΩ x).2
  have hxLmem : ggK1DLin (x : GL (Fin r ⊕ Fin r) K) ∈
      isometryCentralizer Qf (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) ⊓ orthDerived Qf :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxO_mem,
      Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _)⟩, heΩ ▸ (eΩ x).2⟩
  have hEC : E ≤ Subgroup.centralizer
      ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x} :
        Set (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))) := by
    intro z hz
    obtain ⟨z1, hz1, rfl⟩ := hz
    have hz0 : (z1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈ E0 :=
      Subgroup.mem_subgroupOf.mp hz1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm0 : (z1 : _) * ggK1DLin (x : GL (Fin r ⊕ Fin r) K) =
        ggK1DLin (x : GL (Fin r ⊕ Fin r) K) * (z1 : _) :=
      (hE0cent _ hz0 _ hxLmem).symm
    rw [← hΨt]
    change Ψ z1 * Ψ (eΩ x) = Ψ (eΩ x) * Ψ z1
    rw [← Ψ.map_mul, ← Ψ.map_mul]
    refine congrArg Ψ ?_
    apply Subtype.coe_injective
    show (z1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) * (eΩ x : _) =
      (eΩ x : _) * (z1 : _)
    rw [heΩ]
    exact hcomm0
  have hEcent : ∀ z ∈ E, ∀ g ∈ Subgroup.centralizer
      ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x} :
        Set (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))), g * z = z * g := by
    intro z hz g hg
    obtain ⟨z1, hz1, rfl⟩ := hz
    have hz0 : (z1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈ E0 :=
      Subgroup.mem_subgroupOf.mp hz1
    obtain ⟨g1, hg1eq⟩ := MulEquiv.surjective Ψ g
    have hcommπ : Ψ g1 * LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x =
        LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x * Ψ g1 :=
      hg1eq.symm ▸ Subgroup.mem_centralizer_singleton_iff.mp hg
    have hcomm1 : g1 * eΩ x = eΩ x * g1 := by
      refine Ψ.injective ?_
      rw [Ψ.map_mul, Ψ.map_mul, hΨt]
      exact hcommπ
    have hcommV : (g1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) *
        ggK1DLin (x : GL (Fin r ⊕ Fin r) K) =
        ggK1DLin (x : GL (Fin r ⊕ Fin r) K) * (g1 : _) := by
      have h := congrArg Subtype.val hcomm1
      change (g1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) * (eΩ x : _) =
        (eΩ x : _) * (g1 : _) at h
      rw [heΩ] at h
      exact h
    have hgO : (g1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
        TauCeti.QuadraticMap.orthogonalGroup Qf := Subgroup.commutator_le_self O g1.2
    have hgmem : (g1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
        isometryCentralizer Qf (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) ⊓ orthDerived Qf :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgO,
        Subgroup.mem_centralizer_singleton_iff.mpr hcommV⟩, hL ▸ g1.2⟩
    have hcomm0 : g1 * (z1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
        (z1 : _) * g1 := hE0cent _ hz0 _ hgmem
    rw [← hg1eq]
    change Ψ g1 * Ψ z1 = Ψ z1 * Ψ g1
    rw [← Ψ.map_mul, ← Ψ.map_mul]
    refine congrArg Ψ ?_
    apply Subtype.coe_injective
    show (g1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) * (z1 : _) =
      (z1 : _) * (g1 : _)
    exact hcomm0
  exact ggK1Dn_finish false hcenterR E hEab (by rw [hcardE, hE0card]) hEC hEcent (by rw [hrz])

private theorem ggK1Dn_finish_minus {p nf d r n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b
    c : K}
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hcenterR : Subgroup.center
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) = ⊥)
    (E0 : Subgroup ((LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K] (LargeEvenMinusIdx (r - 1) → K)))
    (hE0ab : IsElemAbelian p E0) (hE0card : Nat.card E0 = p ^ n)
    (hE0le : E0 ≤ orthDerived (TableBOrth.qMinusForm K (r - 1) b c))
    (hE0cent : ∀ z ∈ E0, ∀ g ∈ (isometryCentralizer (TableBOrth.qMinusForm K (r - 1) b c)
        (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) ⊓
          orthDerived (TableBOrth.qMinusForm K (r - 1) b c)), g * z = z * g)
    (hrz : (ggMultDatumD p nf d true m).rZ = n) :
    GGK1Center p (ggMultDatumD p nf d true m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)) := by
  classical
  let Qf : QuadraticForm K (LargeEvenMinusIdx (r - 1) → K) :=
    TableBOrth.qMinusForm K (r - 1) b c
  let O : Subgroup ((LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
      (LargeEvenMinusIdx (r - 1) → K)) := TauCeti.QuadraticMap.orthogonalGroup Qf
  let L : Subgroup ((LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
      (LargeEvenMinusIdx (r - 1) → K)) := ⁅O, O⁆
  have hL : L = orthDerived Qf := rfl
  have hscal : (LargeEvenScalars (LargeEvenMinusIdx (r - 1)) K).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := r - 1) b c
  have hcomap : LargeEvenOmega (LargeEvenQMinus (r - 1) b c) =
      Subgroup.comap (toLinEquiv (LargeEvenMinusIdx (r - 1)) K).toMonoidHom L :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (Q := Qf) (Q₀ := LargeEvenQMinus (r - 1) b c) (by rw [TableBOrth.coe_qMinusForm])
  have hmap : (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)).map
      (toLinEquiv (LargeEvenMinusIdx (r - 1)) K).toMonoidHom = L := by
    rw [hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ _).surjective L
  let eΩ : LargeEvenOmega (LargeEvenQMinus (r - 1) b c) ≃* L :=
    (MulEquiv.subgroupMap (toLinEquiv (LargeEvenMinusIdx (r - 1)) K)
      (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))).trans (MulEquiv.subgroupCongr hmap)
  let Ψ : L ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) :=
    eΩ.symm.trans (TableBOrth.projMkEquiv hscal)
  have hΨt : Ψ (eΩ x) = LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x := by
    change TableBOrth.projMkEquiv hscal (eΩ.symm (eΩ x)) = _
    rw [MulEquiv.symm_apply_apply]
    exact TableBOrth.projMkEquiv_apply hscal x
  have heΩ : (eΩ x : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
      (LargeEvenMinusIdx (r - 1) → K)) = ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) := rfl
  have hE0leL : E0 ≤ L := hE0le
  let E1 : Subgroup ↥L := E0.subgroupOf L
  let E : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) :=
    E1.map Ψ.toMonoidHom
  have hcardE1 : Nat.card E1 = Nat.card E0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0leL).toEquiv
  have hcardE : Nat.card E = Nat.card E0 := by
    rw [Subgroup.card_map_of_injective Ψ.injective, hcardE1]
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a1, ha1, ha⟩ := a.2
      obtain ⟨b1, hb1, hb⟩ := b.2
      change a.1 * b.1 = b.1 * a.1
      rw [← ha, ← hb]
      change Ψ a1 * Ψ b1 = Ψ b1 * Ψ a1
      rw [← Ψ.map_mul, ← Ψ.map_mul]
      exact congrArg Ψ (Subtype.coe_injective (congrArg
        (fun x : ↥E0 => (x : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
          (LargeEvenMinusIdx (r - 1) → K)))
        (hE0ab.1.is_comm.comm ⟨(a1 : _), Subgroup.mem_subgroupOf.mp ha1⟩
          ⟨(b1 : _), Subgroup.mem_subgroupOf.mp hb1⟩)))
    · intro z hz
      obtain ⟨z1, hz1, hz⟩ := hz
      rw [← hz, ← map_pow]
      have hzp : z1 ^ p = 1 := by
        apply Subtype.coe_injective
        exact hE0ab.2 (z1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
          (LargeEvenMinusIdx (r - 1) → K)) (Subgroup.mem_subgroupOf.mp hz1)
      rw [hzp, map_one]
  have hxO_mem : ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) ∈
      TauCeti.QuadraticMap.orthogonalGroup Qf := by
    rw [← heΩ]
    exact Subgroup.commutator_le_self O (eΩ x).2
  have hxLmem : ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) ∈
      isometryCentralizer Qf (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) ⊓
        orthDerived Qf :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxO_mem,
      Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _)⟩, heΩ ▸ (eΩ x).2⟩
  have hEC : E ≤ Subgroup.centralizer
      ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x} :
        Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) := by
    intro z hz
    obtain ⟨z1, hz1, rfl⟩ := hz
    have hz0 : (z1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) ∈ E0 := Subgroup.mem_subgroupOf.mp hz1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm0 : (z1 : _) * ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) =
        ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) * (z1 : _) :=
      (hE0cent _ hz0 _ hxLmem).symm
    rw [← hΨt]
    change Ψ z1 * Ψ (eΩ x) = Ψ (eΩ x) * Ψ z1
    rw [← Ψ.map_mul, ← Ψ.map_mul]
    refine congrArg Ψ ?_
    apply Subtype.coe_injective
    show (z1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) * (eΩ x : _) = (eΩ x : _) * (z1 : _)
    rw [heΩ]
    exact hcomm0
  have hEcent : ∀ z ∈ E, ∀ g ∈ Subgroup.centralizer
      ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x} :
        Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))), g * z = z * g := by
    intro z hz g hg
    obtain ⟨z1, hz1, rfl⟩ := hz
    have hz0 : (z1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) ∈ E0 := Subgroup.mem_subgroupOf.mp hz1
    obtain ⟨g1, hg1eq⟩ := MulEquiv.surjective Ψ g
    have hcommπ : Ψ g1 * LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x =
        LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x * Ψ g1 :=
      hg1eq.symm ▸ Subgroup.mem_centralizer_singleton_iff.mp hg
    have hcomm1 : g1 * eΩ x = eΩ x * g1 := by
      refine Ψ.injective ?_
      rw [Ψ.map_mul, Ψ.map_mul, hΨt]
      exact hcommπ
    have hcommV : (g1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) * ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) =
        ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K) * (g1 : _) := by
      have h := congrArg Subtype.val hcomm1
      change (g1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) * (eΩ x : _) = (eΩ x : _) * (g1 : _) at h
      rw [heΩ] at h
      exact h
    have hgO : (g1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
      Subgroup.commutator_le_self O g1.2
    have hgmem : (g1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) ∈ isometryCentralizer Qf
        (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) ⊓ orthDerived Qf :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgO,
        Subgroup.mem_centralizer_singleton_iff.mpr hcommV⟩, hL ▸ g1.2⟩
    have hcomm0 : g1 * (z1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) = (z1 : _) * g1 := hE0cent _ hz0 _ hgmem
    rw [← hg1eq]
    change Ψ g1 * Ψ z1 = Ψ z1 * Ψ g1
    rw [← Ψ.map_mul, ← Ψ.map_mul]
    refine congrArg Ψ ?_
    apply Subtype.coe_injective
    show (g1 : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K]
        (LargeEvenMinusIdx (r - 1) → K)) * (z1 : _) = (z1 : _) * (g1 : _)
    exact hcomm0
  exact ggK1Dn_finish true hcenterR E hEab (by rw [hcardE, hE0card]) hEC hEcent (by rw [hrz])

private noncomputable def ggK1Dn_nontrivialFactors {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (x : V ≃ₗ[K] V) : Finset K[X] := by
  classical
  exact (primaryFactors x.toLinearMap).filter (fun h => h ≠ X - 1)

private theorem ggK1Dn_reciprocal_eq_self {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p nf : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hpq : p ∣ 2 ^ nf + 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    reciprocalPolynomial h = h := by
  classical
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have h0 : h.coeff 0 ≠ 0 := hx.coeff_zero_ne hh
  let E := AdjoinRoot h
  let lam : E := AdjoinRoot.root h
  have hroot : aeval lam h = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hqroot : aeval (lam ^ Nat.card K) h = 0 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, ← Polynomial.expand_aeval, FiniteField.Polynomial.expand_card,
      map_pow, hroot, zero_pow Fintype.card_ne_zero]
  have hpqK : p ∣ Nat.card K + 1 := by rwa [hK]
  have hord : orderOf lam = p :=
    CFSG.RankThree.Classical.orderOf_root_of_mem hp
      (y := x.toLinearMap) (by rw [← toLinearMap_pow, hx.pow_eq_one]; rfl) hh hne
  have hpow : lam ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact hpqK
  have hmul : lam ^ Nat.card K * lam = 1 := by
    rw [← pow_succ, hpow]
  have hinv : lam ^ Nat.card K = lam⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hrootinv : aeval (lam⁻¹) h = 0 := by
    rw [← hinv]
    exact hqroot
  let u : Eˣ := Units.mk0 lam (root_ne_zero h0)
  have hrec : aeval lam (reciprocalPolynomial h) = 0 := by
    have hu := aeval_reciprocalPolynomial_of_unit u h
    rw [show (u : E) = lam from rfl,
      show ((u⁻¹ : Eˣ) : E) = lam⁻¹ by rw [Units.val_inv_eq_inv_val]; rfl,
      hrootinv, mul_zero, smul_zero] at hu
    exact hu
  have hrec_monic : (reciprocalPolynomial h).Monic := monic_reciprocalPolynomial h0
  have hrec_irr : Irreducible (reciprocalPolynomial h) := irreducible_reciprocalPolynomial hirr h0
  have hmin : minpoly K lam = h := by
    rw [AdjoinRoot.minpoly_root hmon.ne_zero, hmon.leadingCoeff, inv_one, Polynomial.C_1,
      mul_one]
  have hdvd : h ∣ reciprocalPolynomial h := by
    nth_rewrite 1 [← hmin]
    rw [minpoly.dvd_iff]
    exact hrec
  exact eq_of_monic_of_associated hrec_monic hmon (hirr.associated_of_dvd hrec_irr hdvd).symm

private theorem ggK1Dn_commute_iSup_blocks {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    {r : K[X]} (hr : r ∈ Rep) {z : V ≃ₗ[K] V} (hz : z ∈ supportedBlock Q x r)
    (hzc : ∀ g ∈ supportedBlock Q x r, Commute z g) :
    ∀ g ∈ isometryCentralizer Q x, Commute z g := by
  intro g hg
  rw [← hx.blocks_iSup_eq hRep] at hg
  refine Subgroup.iSup_induction (fun s : ↥Rep => supportedBlock Q x ↑s)
    (C := fun y => Commute z y) hg ?_ (Commute.one_right z) ?_
  · intro s y hy
    by_cases hsr : (s : K[X]) = r
    · subst hsr
      exact hzc y hy
    · refine hx.blocks_commute hRep (i := ⟨r, hr⟩) (j := s) ?_ z y hz hy
      intro h
      exact hsr (congrArg Subtype.val h).symm
  · intro a b ha hb
    exact ha.mul_right hb

private theorem ggK1Dn_head_central {p : ℕ} {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {xL : V ≃ₗ[K] V}
    (hp2 : Odd p) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hxO : OddOrderIsometry Q p xL)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives xL Rep) (hX1 : (X - 1 : K[X]) ∈ Rep)
    {z : V ≃ₗ[K] V} (hz : z ∈ supportedBlock Q xL (X - 1) ⊓ orthDerived Q)
    (hzc : ∀ g ∈ supportedBlock Q xL (X - 1) ⊓ orthDerived Q, Commute z g) :
    ∀ g ∈ isometryCentralizer Q xL ⊓ orthDerived Q, Commute z g := by
  classical
  let i0 : ↥Rep := ⟨X - 1, hX1⟩
  let H0 : Subgroup (V ≃ₗ[K] V) := supportedBlock Q xL (X - 1)
  let N : Subgroup (V ≃ₗ[K] V) := ⨆ (r : ↥Rep) (_ : r ≠ i0), supportedBlock Q xL ↑r
  have hNle : N ≤ orthDerived Q := by
    refine iSup_le fun r => iSup_le fun hr => ?_
    exact ggK1Dn_supportedBlock_le_orthDerived hxO hp2 hQ hT (hRep.1 r.2)
      (fun h => hr (Subtype.ext h))
  have hC : isometryCentralizer Q xL = H0 ⊔ N := by
    rw [← hxO.blocks_iSup_eq hRep,
      iSup_split_single (fun r : ↥Rep => supportedBlock Q xL ↑r) i0]
  have hcommN : ∀ b ∈ H0, ∀ n ∈ N, b * n = n * b := by
    intro b hb n hn
    refine Subgroup.iSup_induction (fun r : ↥Rep => ⨆ (_ : r ≠ i0), supportedBlock Q xL ↑r)
      (C := fun y => b * y = y * b) hn ?_ (by simp) ?_
    · intro r y hy
      refine Subgroup.iSup_induction (fun _ : r ≠ i0 => supportedBlock Q xL ↑r)
        (C := fun y => b * y = y * b) hy ?_ (by simp) ?_
      · intro hr y hy
        exact (hxO.blocks_commute hRep (fun h : i0 = r => hr h.symm) b y hb hy).eq
      · intro y y' hy hy'
        calc b * (y * y') = b * y * y' := by rw [mul_assoc]
          _ = y * b * y' := by rw [hy]
          _ = y * (b * y') := by rw [mul_assoc]
          _ = y * (y' * b) := by rw [hy']
          _ = y * y' * b := by rw [← mul_assoc]
    · intro y y' hy hy'
      calc b * (y * y') = b * y * y' := by rw [mul_assoc]
        _ = y * b * y' := by rw [hy]
        _ = y * (b * y') := by rw [mul_assoc]
        _ = y * (y' * b) := by rw [hy']
        _ = y * y' * b := by rw [← mul_assoc]
  have hBnorm : H0 ≤ Subgroup.normalizer N := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hcommN b hb n hn]
      simpa using hn
    · intro hn
      have h4 : b⁻¹ * (b * n * b⁻¹) * b = b * n * b⁻¹ := by
        calc b⁻¹ * (b * n * b⁻¹) * b
            = b⁻¹ * ((b * n * b⁻¹) * b) := by rw [mul_assoc]
          _ = b⁻¹ * (b * (b * n * b⁻¹)) := by rw [← hcommN b hb (b * n * b⁻¹) hn]
          _ = b * n * b⁻¹ := by group
      have h5 : n = b⁻¹ * (b * n * b⁻¹) * b := by group
      rw [h5, h4]; exact hn
  have hsup : ∀ g ∈ H0 ⊔ N, ∃ b ∈ H0, ∃ n ∈ N, b * n = g := by
    intro g hg
    have h1 : g ∈ (H0 : Set (V ≃ₗ[K] V)) * (N : Set (V ≃ₗ[K] V)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBnorm]
      exact hg
    exact h1
  have hzN : ∀ n ∈ N, Commute z n := by
    intro n hn
    refine Subgroup.iSup_induction (fun r : ↥Rep => ⨆ (_ : r ≠ i0), supportedBlock Q xL ↑r)
      (C := fun y => Commute z y) hn ?_ (Commute.one_right z) ?_
    · intro r y hy
      refine Subgroup.iSup_induction (fun _ : r ≠ i0 => supportedBlock Q xL ↑r)
        (C := fun y => Commute z y) hy ?_ (Commute.one_right z) ?_
      · intro hr y hy
        exact hxO.blocks_commute hRep (fun h : i0 = r => hr h.symm) z y
          (Subgroup.mem_inf.mp hz).1 hy
      · intro a b ha hb
        exact ha.mul_right hb
    · intro a b ha hb
      exact ha.mul_right hb
  intro g hg
  have hgC : g ∈ H0 ⊔ N := hC ▸ (Subgroup.mem_inf.mp hg).1
  have hgΩ : g ∈ orthDerived Q := (Subgroup.mem_inf.mp hg).2
  obtain ⟨h, hh, n, hn, hhn⟩ := hsup g hgC
  have hnΩ : n ∈ orthDerived Q := hNle hn
  have hhΩ : h ∈ orthDerived Q := by
    have h1 : h * n * n⁻¹ ∈ orthDerived Q :=
      (orthDerived Q).mul_mem (hhn ▸ hgΩ) ((orthDerived Q).inv_mem hnΩ)
    simpa using h1
  have hzh : Commute z h := hzc h (Subgroup.mem_inf.mpr ⟨hh, hhΩ⟩)
  have hzn : Commute z n := hzN n hn
  rw [← hhn]
  exact hzh.mul_right hzn

private theorem ggK1Dn_build_E0 {p nf d : ℕ} {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {xL : V ≃ₗ[K] V} {tw : Bool} {m : List ℕ}
    (hp : p.Prime)
    (hxO : OddOrderIsometry Q p xL)
    (Rep : Finset K[X]) (hRep : IsOrbitRepresentatives xL Rep)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (rep : ι → K[X]) (hrep_mem : ∀ i, rep i ∈ Rep) (hrep_inj : Function.Injective rep)
    (e : ι → V ≃ₗ[K] V)
    (hmem : ∀ i, e i ∈ supportedBlock Q xL (rep i) ⊓ orthDerived Q)
    (hp_pow : ∀ i, e i ^ p = 1) (hord : ∀ i, orderOf (e i) = p)
    (hcent : ∀ i, ∀ g ∈ isometryCentralizer Q xL ⊓ orthDerived Q, Commute (e i) g)
    (hcard : Fintype.card ι = (ggMultDatumD p nf d tw m).rZ) :
    ∃ E0 : Subgroup (V ≃ₗ[K] V), IsElemAbelian p E0 ∧
      Nat.card E0 = p ^ (ggMultDatumD p nf d tw m).rZ ∧ E0 ≤ orthDerived Q ∧
      ∀ z ∈ E0, ∀ g ∈ (isometryCentralizer Q xL ⊓ orthDerived Q), g * z = z * g := by
  classical
  let A : ι → Subgroup (V ≃ₗ[K] V) := fun i => supportedBlock Q xL (rep i) ⊓ orthDerived Q
  let repRep : ι → ↥Rep := fun i => ⟨rep i, hrep_mem i⟩
  have hrepRep_inj : Function.Injective repRep := by
    intro i j hij
    exact hrep_inj (congrArg Subtype.val hij)
  have hind : iSupIndep A :=
    ((hxO.blocks_iSupIndep hRep).comp hrepRep_inj).mono (fun i => inf_le_left)
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b := by
    intro i j hij a ha b hb
    have hne : repRep i ≠ repRep j := fun h => hij (hrepRep_inj h)
    exact hxO.blocks_commute hRep (i := repRep i) (j := repRep j) hne a b
      (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hb).1
  let B : Subgroup (V ≃ₗ[K] V) := isometryCentralizer Q xL ⊓ orthDerived Q
  have hAB : ∀ i, A i ≤ B := by
    intro i
    exact le_inf (le_trans inf_le_left (supportedBlock_le_isometryCentralizer (rep i)))
      inf_le_right
  obtain ⟨E0, hab, hcardE0, hcentE0, hleE0⟩ :=
    ggK1Dn_block_elemAbelian hp A hind hcomm B hAB e hmem hp_pow hord hcent
  refine ⟨E0, hab, ?_, ?_, ?_⟩
  · rw [hcardE0, hcard]
  · exact hleE0.trans (iSup_le fun i => inf_le_right)
  · intro z hz g hg
    exact (Subgroup.mem_centralizer_iff.mp (hcentE0 hz)) g hg

private theorem ggK1Dn_exists_E0 {p nf d : ℕ} {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {xL : V ≃ₗ[K] V} {tw : Bool} {m : List ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    (hxO : OddOrderIsometry Q p xL)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hlen : m.length = (p - 1) / 2 + 1)
    (hhead : m.headD 0 = Module.finrank K (primaryComponent xL.toLinearMap (X - 1)) / 2)
    (hblocks : (d = 1 ∧ ∃ P : Finset K[X], IsReciprocalTransversal xL.toLinearMap P ∧
        Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
          P.val.map (primaryMultiplicity xL.toLinearMap)) ∨
      (d = 2 ∧ Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
        (ggK1Dn_nontrivialFactors xL).val.map (primaryMultiplicity xL.toLinearMap)))
    (hWitt : IsPlusType (Q.restrict (primaryComponent xL.toLinearMap (X - 1))) ↔
      ggMultEps0 p d tw m = true) :
    ∃ E0 : Subgroup (V ≃ₗ[K] V),
      IsElemAbelian p E0 ∧ Nat.card E0 = p ^ (ggMultDatumD p nf d tw m).rZ ∧
      E0 ≤ orthDerived Q ∧
      ∀ z ∈ E0, ∀ g ∈ (isometryCentralizer Q xL ⊓ orthDerived Q), g * z = z * g := by
  classical
  have hpq1 : d = 1 → p ∣ 2 ^ nf - 1 := by
    intro h1
    have hgm : ggMultOrd p nf = 1 := by rw [← hd]; exact h1
    unfold ggMultOrd at hgm
    by_cases hc : p ∣ 2 ^ nf - 1
    · exact hc
    · rw [if_neg hc] at hgm; split_ifs at hgm <;> omega
  have hpq2 : d = 2 → p ∣ 2 ^ nf + 1 := by
    intro h2
    have hgm : ggMultOrd p nf = 2 := by rw [← hd]; exact h2
    unfold ggMultOrd at hgm
    by_cases hc : p ∣ 2 ^ nf - 1
    · rw [if_pos hc] at hgm; omega
    · rw [if_neg hc] at hgm
      by_cases hc2 : p ∣ 2 ^ nf + 1
      · exact hc2
      · rw [if_neg hc2] at hgm; omega
  let tail := (m.tail.filter (fun j => decide (j ≠ 0))).length
  let headCond : Prop := m.headD 0 = 1 ∧ ((ggMultEps0 p d tw m = true ∧ d = 1) ∨
    (ggMultEps0 p d tw m = false ∧ d = 2))
  obtain ⟨Rep0, hRep0⟩ := hxO.exists_orbitRepresentatives
  have hdata : ∃ tailSet : Finset K[X],
      (∀ t ∈ tailSet, t ∈ primaryFactors xL.toLinearMap) ∧
      (∀ t ∈ tailSet, t ≠ X - 1) ∧
      tailSet.card = tail ∧
      (d = 1 → ∀ t ∈ tailSet, t ≠ reciprocalPolynomial t) ∧
      (d = 2 → ∀ t ∈ tailSet, t = reciprocalPolynomial t) ∧
      (∀ t ∈ tailSet, ∀ t' ∈ tailSet, (t' = t ∨ t' = reciprocalPolynomial t) → t' = t) := by
    rcases hblocks with ⟨hd1, P, hP, hmult⟩ | ⟨hd2, hmult⟩
    · have hne1 : ∀ t ∈ P, t ≠ X - 1 := by
        intro t ht h
        exact (hP.1 t ht).2 (by rw [h]; exact reciprocalPolynomial_X_sub_one.symm)
      have hcard : P.card = tail := by
        have h := congrArg Multiset.card hmult
        rw [Multiset.coe_card, Multiset.card_map] at h
        exact h.symm
      have hns : d = 1 → ∀ t ∈ P, t ≠ reciprocalPolynomial t :=
        fun _ t ht => (hP.1 t ht).2
      have hsd : d = 2 → ∀ t ∈ P, t = reciprocalPolynomial t :=
        fun h2 => absurd (hd1.symm.trans h2) (by omega)
      have hdist : ∀ t ∈ P, ∀ t' ∈ P, (t' = t ∨ t' = reciprocalPolynomial t) → t' = t := by
        intro t ht t' ht' h
        rcases h with h | h
        · exact h
        · exact absurd (h ▸ ht') (hP.2.2 t ht)
      exact ⟨P, fun t ht => (hP.1 t ht).1, hne1, hcard, hns, hsd, hdist⟩
    · have hne1 : ∀ t ∈ ggK1Dn_nontrivialFactors xL, t ≠ X - 1 :=
        fun t ht => (Finset.mem_filter.mp ht).2
      have hcard : (ggK1Dn_nontrivialFactors xL).card = tail := by
        have h := congrArg Multiset.card hmult
        rw [Multiset.coe_card, Multiset.card_map] at h
        exact h.symm
      have hns : d = 1 → ∀ t ∈ ggK1Dn_nontrivialFactors xL, t ≠ reciprocalPolynomial t :=
        fun h1 => absurd (hd2.symm.trans h1) (by omega)
      have hsd : d = 2 → ∀ t ∈ ggK1Dn_nontrivialFactors xL, t = reciprocalPolynomial t :=
        fun _ t ht => (ggK1Dn_reciprocal_eq_self hxO hp hK (hpq2 hd2)
          (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2).symm
      have hdist : ∀ t ∈ ggK1Dn_nontrivialFactors xL,
          ∀ t' ∈ ggK1Dn_nontrivialFactors xL,
            (t' = t ∨ t' = reciprocalPolynomial t) → t' = t := by
        intro t ht t' ht' h
        rcases h with h | h
        · exact h
        · rw [h]; exact (hsd hd2 t ht).symm
      exact ⟨ggK1Dn_nontrivialFactors xL, fun t ht => (Finset.mem_filter.mp ht).1,
        hne1, hcard, hns, hsd, hdist⟩
  obtain ⟨tailSet, htail_prim, htail_ne1, htail_card, htail_ns, htail_sd, htail_distinct⟩ := hdata
  let repTail : ↥tailSet → ↥Rep0 := fun t =>
    ⟨Classical.choose (hRep0.2 t.1 (htail_prim t.1 t.2)),
     (Classical.choose_spec (hRep0.2 t.1 (htail_prim t.1 t.2))).1.1⟩
  have hrepTail_spec : ∀ t : ↥tailSet,
      t.1 = (repTail t : K[X]) ∨ t.1 = reciprocalPolynomial (repTail t : K[X]) :=
    fun t => (Classical.choose_spec (hRep0.2 t.1 (htail_prim t.1 t.2))).1.2
  have hrepTail_inj : Function.Injective repTail := by
    intro t t' h
    have ht := hrepTail_spec t
    have ht' := hrepTail_spec t'
    have hval : (repTail t : K[X]) = (repTail t' : K[X]) := congrArg Subtype.val h
    have hcase : t'.1 = t.1 ∨ t'.1 = reciprocalPolynomial t.1 := by
      rcases ht' with h' | h'
      · rw [h', hval.symm]
        rcases ht with h'' | h''
        · exact Or.inl h''.symm
        · have h3 : reciprocalPolynomial t.1 = (repTail t : K[X]) := by
            rw [h'', hxO.reciprocal_reciprocal_eq (hRep0.1 (repTail t).2)]
          exact Or.inr h3.symm
      · rw [h', hval.symm]
        rcases ht with h'' | h''
        · exact Or.inr (by rw [← h''])
        · exact Or.inl h''.symm
    exact Subtype.ext (htail_distinct t.1 t.2 t'.1 t'.2 hcase).symm
  have hrepTail_ne1 : ∀ t : ↥tailSet, (repTail t : K[X]) ≠ X - 1 := by
    intro t h
    rcases hrepTail_spec t with h' | h'
    · exact htail_ne1 t t.2 (h'.trans h)
    · exact htail_ne1 t t.2 (h'.trans (by rw [h, reciprocalPolynomial_X_sub_one]))
  have head_mem : headCond → (X - 1 : K[X]) ∈ Rep0 := by
    intro hc
    obtain ⟨s, hs⟩ := hxO.even_finrank_fixed
    have hfin : Module.finrank K (primaryComponent xL.toLinearMap (X - 1)) = 2 := by
      have h1 : m.headD 0 = s := by
        rw [hhead, ← fixedSpace_eq_primaryComponent, hs]; omega
      rw [← fixedSpace_eq_primaryComponent, hs]; omega
    have hX1pf : (X - 1 : K[X]) ∈ primaryFactors xL.toLinearMap := by
      by_contra h
      have hbot : primaryComponent xL.toLinearMap (X - 1) = ⊥ :=
        CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
          CFSG.RankThree.PartOne.KCOrthogonal.irreducible_X_sub_one
          CFSG.RankThree.PartOne.KCOrthogonal.monic_X_sub_one h
      rw [hbot, finrank_bot] at hfin
      omega
    obtain ⟨r, ⟨hr, hdisj⟩, -⟩ := hRep0.2 (X - 1) hX1pf
    have hrX : r = X - 1 := by
      rcases hdisj with h' | h'
      · exact h'.symm
      · calc r = reciprocalPolynomial (reciprocalPolynomial r) :=
              (hxO.reciprocal_reciprocal_eq (hRep0.1 hr)).symm
          _ = reciprocalPolynomial (X - 1) := by rw [h']
          _ = X - 1 := reciprocalPolynomial_X_sub_one
    rwa [← hrX]
  let repRep : (Fin tail ⊕ {_u : Unit // headCond}) → ↥Rep0 := fun i => match i with
    | Sum.inl j => repTail ((Finset.equivFin tailSet).symm (Fin.cast htail_card.symm j))
    | Sum.inr u => ⟨X - 1, head_mem u.2⟩
  have hrepRep_inj : Function.Injective repRep := by
    intro i j h
    match i, j with
    | Sum.inl a, Sum.inl b =>
      have h1 : (Finset.equivFin tailSet).symm (Fin.cast htail_card.symm a) =
          (Finset.equivFin tailSet).symm (Fin.cast htail_card.symm b) := hrepTail_inj h
      have h2 : Fin.cast htail_card.symm a = Fin.cast htail_card.symm b :=
        (Finset.equivFin tailSet).symm.injective h1
      exact congrArg Sum.inl (Fin.cast_injective htail_card.symm h2)
    | Sum.inl a, Sum.inr u =>
      exact absurd (congrArg Subtype.val h)
        (hrepTail_ne1 ((Finset.equivFin tailSet).symm (Fin.cast htail_card.symm a)))
    | Sum.inr u, Sum.inl a =>
      exact absurd (congrArg Subtype.val h).symm
        (hrepTail_ne1 ((Finset.equivFin tailSet).symm (Fin.cast htail_card.symm a)))
    | Sum.inr u, Sum.inr v => exact congrArg Sum.inr (Subtype.ext (Subsingleton.elim _ _))
  have hrep_mem : ∀ i, (repRep i : K[X]) ∈ Rep0 := fun i => (repRep i).2
  have hrep_inj : Function.Injective (fun i => (repRep i : K[X])) :=
    fun i j h => hrepRep_inj (Subtype.ext h)
  have selfdual_iff : ∀ {a b : K[X]}, a ∈ primaryFactors xL.toLinearMap →
      b ∈ primaryFactors xL.toLinearMap → (a = b ∨ a = reciprocalPolynomial b) →
      (a = reciprocalPolynomial a ↔ b = reciprocalPolynomial b) := by
    intro a b ha hb hab
    rcases hab with h | h
    · rw [h]
    · constructor
      · intro haa
        calc b = reciprocalPolynomial a :=
              ((congrArg reciprocalPolynomial h).trans (hxO.reciprocal_reciprocal_eq hb)).symm
          _ = a := haa.symm
          _ = reciprocalPolynomial b := h
      · intro hbb
        calc a = reciprocalPolynomial b := h
          _ = b := hbb.symm
          _ = reciprocalPolynomial a :=
              ((congrArg reciprocalPolynomial h).trans (hxO.reciprocal_reciprocal_eq hb)).symm
  have htail_elem : ∀ t : ↥tailSet,
      ∃ e ∈ supportedBlock Q xL (repTail t : K[X]) ⊓ orthDerived Q, e ^ p = 1 ∧ orderOf e = p ∧
        ∀ g ∈ supportedBlock Q xL (repTail t : K[X]), Commute e g := by
    intro t
    have hr_prim : (repTail t : K[X]) ∈ primaryFactors xL.toLinearMap := hRep0.1 (repTail t).2
    have hsd_iff := selfdual_iff (htail_prim t t.2) hr_prim (hrepTail_spec t)
    have hr_ne1 : (repTail t : K[X]) ≠ X - 1 := by
      intro h
      rcases hrepTail_spec t with h' | h'
      · exact htail_ne1 t t.2 (h'.trans h)
      · exact htail_ne1 t t.2 (h'.trans (by rw [h, reciprocalPolynomial_X_sub_one]))
    rcases hblocks with ⟨hd1, P, hP, hmult⟩ | ⟨hd2, hmult⟩
    · have hr_ns : (repTail t : K[X]) ≠ reciprocalPolynomial (repTail t : K[X]) :=
        fun h => htail_ns hd1 t t.2 (hsd_iff.mpr h)
      have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq1 hd1
      obtain ⟨e, he, hep, heord, hecent⟩ :=
        ggK1Dn_paired_scalar' hxO hp hp2 hK hr_prim hr_ne1 hr_ns hpq
      exact ⟨e, Subgroup.mem_inf.mpr ⟨he,
          ggK1Dn_supportedBlock_le_orthDerived hxO (hp.odd_of_ne_two hp2) hQ hT hr_prim hr_ne1 he⟩,
        hep, heord, hecent⟩
    · have hr_sd : (repTail t : K[X]) = reciprocalPolynomial (repTail t : K[X]) :=
        hsd_iff.mp (htail_sd hd2 t t.2)
      obtain ⟨e, he, hep, heord, hecent⟩ :=
        ggK1Dn_selfDual_scalar' hxO hp hp2 hnf hK hdvd hr_prim hr_ne1 hr_sd (hpq2 hd2)
      exact ⟨e, Subgroup.mem_inf.mpr ⟨he,
          ggK1Dn_supportedBlock_le_orthDerived hxO (hp.odd_of_ne_two hp2) hQ hT hr_prim hr_ne1 he⟩,
        hep, heord, hecent⟩
  have hhead_elem : ∀ u : {_u : Unit // headCond},
      ∃ e ∈ supportedBlock Q xL (X - 1) ⊓ orthDerived Q, e ^ p = 1 ∧ orderOf e = p ∧
        ∀ g ∈ supportedBlock Q xL (X - 1) ⊓ orthDerived Q, Commute e g := by
    intro u
    have hW : Module.finrank K (fixedSpace xL) = 2 := by
      obtain ⟨s, hs⟩ := hxO.even_finrank_fixed
      have h1 : m.headD 0 = s := by rw [hhead, ← fixedSpace_eq_primaryComponent, hs]; omega
      rw [hs]; omega
    rcases u.2.2 with ⟨heps, hd1⟩ | ⟨heps, hd2⟩
    · have hplus : IsPlusType (Q.comp (fixedSpace xL).subtype) := by
        rw [fixedSpace_eq_primaryComponent]
        exact hWitt.mpr heps
      obtain ⟨e, he, heord, hecent⟩ :=
        ggK1Dn_fixed_torus_plus hxO hQ hT hp hp2 hK hd hd1 hW hplus
      exact ⟨e, he, by rw [← heord]; exact pow_orderOf_eq_one e, heord, hecent⟩
    · have hminus : ¬ IsPlusType (Q.comp (fixedSpace xL).subtype) := by
        intro hcontra
        rw [fixedSpace_eq_primaryComponent] at hcontra
        exact Bool.false_ne_true (heps ▸ hWitt.mp hcontra)
      obtain ⟨e, he, heord, hecent⟩ :=
        ggK1Dn_fixed_torus_minus hxO hQ hT hp hp2 hK hd hd2 hW hminus
      exact ⟨e, he, by rw [← heord]; exact pow_orderOf_eq_one e, heord, hecent⟩
  let sel : Fin tail → ↥tailSet := fun j =>
    (Finset.equivFin tailSet).symm (Fin.cast htail_card.symm j)
  let e : (Fin tail ⊕ {_u : Unit // headCond}) → V ≃ₗ[K] V := fun i => match i with
    | Sum.inl j => Classical.choose (htail_elem (sel j))
    | Sum.inr u => Classical.choose (hhead_elem u)
  have hmem : ∀ i, e i ∈ supportedBlock Q xL (repRep i : K[X]) ⊓ orthDerived Q := by
    intro i
    match i with
    | Sum.inl j => exact (Classical.choose_spec (htail_elem (sel j))).1
    | Sum.inr u => exact (Classical.choose_spec (hhead_elem u)).1
  have hp_pow : ∀ i, e i ^ p = 1 := by
    intro i
    match i with
    | Sum.inl j => exact (Classical.choose_spec (htail_elem (sel j))).2.1
    | Sum.inr u => exact (Classical.choose_spec (hhead_elem u)).2.1
  have hord : ∀ i, orderOf (e i) = p := by
    intro i
    match i with
    | Sum.inl j => exact (Classical.choose_spec (htail_elem (sel j))).2.2.1
    | Sum.inr u => exact (Classical.choose_spec (hhead_elem u)).2.2.1
  have hcent : ∀ i, ∀ g ∈ isometryCentralizer Q xL ⊓ orthDerived Q, Commute (e i) g := by
    intro i
    match i with
    | Sum.inl j =>
      have hb := (Classical.choose_spec (htail_elem (sel j))).2.2.2
      exact fun g hg => ggK1Dn_commute_iSup_blocks hxO hRep0 (repTail (sel j)).2
        (Subgroup.mem_inf.mp (hmem (Sum.inl j))).1 hb g (Subgroup.mem_inf.mp hg).1
    | Sum.inr u =>
      exact fun g hg => ggK1Dn_head_central (hp.odd_of_ne_two hp2) hQ hT hxO hRep0
        (head_mem u.2) (hmem (Sum.inr u)) (Classical.choose_spec (hhead_elem u)).2.2.2 g hg
  have hcard : Fintype.card (Fin tail ⊕ {_u : Unit // headCond}) =
      (ggMultDatumD p nf d tw m).rZ :=
    ggK1Dn_card_tail_eq p nf d tw m tail hlen rfl
  exact ggK1Dn_build_E0 hp hxO Rep0 hRep0 (fun i => (repRep i : K[X])) hrep_mem hrep_inj e
    hmem hp_pow hord hcent hcard

private theorem ggK1Dn_exists_E0_plus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (Fin r ⊕ Fin r) K) m) (hx : x ^ p = 1)
    (hx1 : x ≠ 1) :
    ∃ E0 : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
      IsElemAbelian p E0 ∧ Nat.card E0 = p ^ (ggMultDatumD p nf d false m).rZ ∧
      E0 ≤ orthDerived (TableBOrth.qPlusForm K r) ∧
      ∀ z ∈ E0, ∀ g ∈ (isometryCentralizer (TableBOrth.qPlusForm K r)
          (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) ⊓ orthDerived (TableBOrth.qPlusForm K r)),
        g * z = z * g := by
  classical
  let Qf : QuadraticForm K (Fin r ⊕ Fin r → K) := TableBOrth.qPlusForm K r
  let xL : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
    ggK1DLin (x : GL (Fin r ⊕ Fin r) K)
  have hxO : OddOrderIsometry Qf p xL := ggK1D_omegaLift_plus hp hp2 hnf hK hx
  have hQ : Qf.polarBilin.Nondegenerate := ggK1Dn_polarBilin_nondegenerate hxO
  have hdim : 8 ≤ Module.finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hT := ggK1Dn_exists_totallySingular_three hQ hdim
  have hhead : m.headD 0 =
      Module.finrank K (primaryComponent xL.toLinearMap (X - 1)) / 2 := hm.head_eq
  have hblocks : (d = 1 ∧ ∃ P : Finset K[X], IsReciprocalTransversal xL.toLinearMap P ∧
        Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
          P.val.map (primaryMultiplicity xL.toLinearMap)) ∨
      (d = 2 ∧ Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
        (ggK1Dn_nontrivialFactors xL).val.map (primaryMultiplicity xL.toLinearMap)) := by
    rcases hm.blocks_eq with ⟨hd1, P, hP, hmult⟩ | ⟨hd2, hmult⟩
    · exact Or.inl ⟨hd1, P, hP, hmult⟩
    · exact Or.inr ⟨hd2, by simpa [ggK1Dn_nontrivialFactors, ggK1DSelfDualFactors, xL,
        ggK1DOrthEnd] using hmult⟩
  have hWitt : IsPlusType (Qf.restrict (primaryComponent xL.toLinearMap (X - 1))) ↔
      ggMultEps0 p d false m = true := by
    have hm' : GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (Fin r ⊕ Fin r) K) m := hd ▸ hm
    have hw := ggK1D_v0_witt_plus hp hp2 hdvd hnf hK hm' hx (TableBOrth.qPlusForm K r)
      (TableBOrth.coe_qPlusForm (K := K) r).symm
    rwa [← hd] at hw
  exact ggK1Dn_exists_E0 hp hp2 hdvd hnf hK hd hxO hQ hT hm.length_eq hhead hblocks hWitt

private theorem ggK1Dn_exists_E0_minus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1)
    (hx1 : x ≠ 1) :
    ∃ E0 : Subgroup ((LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K] (LargeEvenMinusIdx (r - 1) → K)),
      IsElemAbelian p E0 ∧ Nat.card E0 = p ^ (ggMultDatumD p nf d true m).rZ ∧
      E0 ≤ orthDerived (TableBOrth.qMinusForm K (r - 1) b c) ∧
      ∀ z ∈ E0, ∀ g ∈ (isometryCentralizer (TableBOrth.qMinusForm K (r - 1) b c)
          (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) ⊓
            orthDerived (TableBOrth.qMinusForm K (r - 1) b c)),
        g * z = z * g := by
  classical
  let Qf : QuadraticForm K (LargeEvenMinusIdx (r - 1) → K) :=
    TableBOrth.qMinusForm K (r - 1) b c
  let xL : (LargeEvenMinusIdx (r - 1) → K) ≃ₗ[K] (LargeEvenMinusIdx (r - 1) → K) :=
    ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)
  have hxO : OddOrderIsometry Qf p xL := ggK1D_omegaLift_minus hp hp2 hnf hK hirr hx
  have hQ : Qf.polarBilin.Nondegenerate := ggK1Dn_polarBilin_nondegenerate hxO
  have hdim : 8 ≤ Module.finrank K (LargeEvenMinusIdx (r - 1) → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    omega
  have hT := ggK1Dn_exists_totallySingular_three hQ hdim
  have hhead : m.headD 0 =
      Module.finrank K (primaryComponent xL.toLinearMap (X - 1)) / 2 := hm.head_eq
  have hblocks : (d = 1 ∧ ∃ P : Finset K[X], IsReciprocalTransversal xL.toLinearMap P ∧
        Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
          P.val.map (primaryMultiplicity xL.toLinearMap)) ∨
      (d = 2 ∧ Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
        (ggK1Dn_nontrivialFactors xL).val.map (primaryMultiplicity xL.toLinearMap)) := by
    rcases hm.blocks_eq with ⟨hd1, P, hP, hmult⟩ | ⟨hd2, hmult⟩
    · exact Or.inl ⟨hd1, P, hP, hmult⟩
    · exact Or.inr ⟨hd2, by simpa [ggK1Dn_nontrivialFactors, ggK1DSelfDualFactors, xL,
        ggK1DOrthEnd] using hmult⟩
  have hWitt : IsPlusType (Qf.restrict (primaryComponent xL.toLinearMap (X - 1))) ↔
      ggMultEps0 p d true m = true := by
    have hm' : GGK1DMultOf p nf (ggMultOrd p nf) r K
        (x : GL (LargeEvenMinusIdx (r - 1)) K) m := hd ▸ hm
    have hw := ggK1D_v0_witt_minus hp hp2 hdvd hnf hK hirr hm' hx
      (TableBOrth.qMinusForm K (r - 1) b c)
      (TableBOrth.coe_qMinusForm (K := K) (r - 1) b c).symm
    rwa [← hd] at hw
  exact ggK1Dn_exists_E0 hp hp2 hdvd hnf hK hd hxO hQ hT hm.length_eq hhead hblocks hWitt

theorem ggK1D_core_center_plus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (Fin r ⊕ Fin r) K) m) (hx : x ^ p = 1) :
    GGK1Center p (ggMultDatumD p nf d false m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)) := by
  classical
  intro h2
  haveI : CharP K 2 := ggK1Dn_charP_two hK
  by_cases hx1 : x = 1
  · subst hx1
    have hhead : m.headD 0 = r := by
      rw [hm.head_eq]
      have hcoe : ((1 : ↥(LargeEvenOmega (LargeEvenQPlus K r))) : GL (Fin r ⊕ Fin r) K) = 1 := by
        simp
      rw [hcoe, CFSG.RankThree.Classical.primaryComponent_X_sub_one]
      have h1 : ggK1DOrthEnd (1 : GL (Fin r ⊕ Fin r) K) = 1 := by
        ext v; simp [ggK1DOrthEnd, ggK1DLin]
      rw [h1, sub_self, LinearMap.ker_zero, finrank_top,
        Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    cases m with
    | nil =>
        have hlen := hm.length_eq
        simp at hlen
    | cons a t =>
        have ha : a = r := by simpa using hhead
        have hsum : a + t.sum = r := by simpa using hm.sum_eq
        have htsum : t.sum = 0 := by omega
        have htailnil : t.filter (fun j => decide (j ≠ 0)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          have hb0 := ggK1Dn_eq_zero_of_sum_eq_zero htsum b hb
          simp [hb0]
        have hzero : (t.filter (fun j => decide (j ≠ 0))).length = 0 := by
          rw [htailnil]; simp
        have hrz := ggK1Dn_rZ_eq_tail p nf d false (a :: t) hm.length_eq
        rw [List.tail_cons, hzero, zero_add] at hrz
        rw [hrz] at h2
        have hcond : ¬ ((a :: t).headD 0 = 1 ∧
            ((ggMultEps0 p d false (a :: t) = true ∧ d = 1) ∨
              (ggMultEps0 p d false (a :: t) = false ∧ d = 2))) := by
          intro hc
          have h1 := hc.1
          simp only [List.headD_cons] at h1
          omega
        rw [if_neg hcond] at h2
        omega
  · have hcenterR := ggK1D_centreless_plus (r := r) hp hp2 hdvd hnf hK (by omega)
    obtain ⟨E0, hab, hcard, hle, hcent⟩ :=
      ggK1Dn_exists_E0_plus hp hp2 hdvd h4 hnf hK hd hm hx hx1
    exact ggK1Dn_finish_plus (by omega) hcenterR E0 hab hcard hle hcent rfl h2

theorem ggK1D_core_center_minus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1) :
    GGK1Center p (ggMultDatumD p nf d true m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))
      (MulAut.conj (LargeEvenProjMk
        (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)) := by
  classical
  intro h2
  haveI : CharP K 2 := ggK1Dn_charP_two hK
  by_cases hx1 : x = 1
  · subst hx1
    have hhead : m.headD 0 = r := by
      rw [hm.head_eq]
      have hcoe : ((1 : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) : GL (LargeEvenMinusIdx (r
          - 1)) K) = 1 := by
        simp
      rw [hcoe, CFSG.RankThree.Classical.primaryComponent_X_sub_one]
      have h1 : ggK1DOrthEnd (1 : GL (LargeEvenMinusIdx (r - 1)) K) = 1 := by
        ext v; simp [ggK1DOrthEnd, ggK1DLin]
      rw [h1, sub_self, LinearMap.ker_zero, finrank_top,
        Module.finrank_fintype_fun_eq_card]
      simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
      omega
    cases m with
    | nil =>
        have hlen := hm.length_eq
        simp at hlen
    | cons a t =>
        have ha : a = r := by simpa using hhead
        have hsum : a + t.sum = r := by simpa using hm.sum_eq
        have htsum : t.sum = 0 := by omega
        have htailnil : t.filter (fun j => decide (j ≠ 0)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          have hb0 := ggK1Dn_eq_zero_of_sum_eq_zero htsum b hb
          simp [hb0]
        have hzero : (t.filter (fun j => decide (j ≠ 0))).length = 0 := by
          rw [htailnil]; simp
        have hrz := ggK1Dn_rZ_eq_tail p nf d true (a :: t) hm.length_eq
        rw [List.tail_cons, hzero, zero_add] at hrz
        rw [hrz] at h2
        have hcond : ¬ ((a :: t).headD 0 = 1 ∧
            ((ggMultEps0 p d true (a :: t) = true ∧ d = 1) ∨
              (ggMultEps0 p d true (a :: t) = false ∧ d = 2))) := by
          intro hc
          have h1 := hc.1
          simp only [List.headD_cons] at h1
          omega
        rw [if_neg hcond] at h2
        omega
  · have hcenterR := ggK1D_centreless_minus (r := r) hp hp2 hdvd hnf hK (by omega) hirr
    obtain ⟨E0, hab, hcard, hle, hcent⟩ :=
      ggK1Dn_exists_E0_minus hp hp2 hdvd h4 hnf hK hd hirr hm hx hx1
    exact ggK1Dn_finish_minus hcenterR E0 hab hcard hle hcent rfl h2

end CFSG.StandardType

end
