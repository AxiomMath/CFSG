module

public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlanePrimary
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Characters

theorem exists_functional_of_card_lt {k : Type*} [Field k] [Finite k]
    (S : Submodule k (Fin 2 → k)) (hS : Nat.card S < Nat.card k ^ 2) :
    ∃ m n : k, (m ≠ 0 ∨ n ≠ 0) ∧ ∀ v ∈ S, m * v 0 + n * v 1 = 0 := by
  have hlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hc : Nat.card (Fin 2 → k) ≤ Nat.card S := by
      refine Nat.card_le_card_of_surjective (fun x : S => (x : Fin 2 → k)) ?_
      intro v
      exact ⟨⟨v, htop ▸ Submodule.mem_top⟩, rfl⟩
    have : Nat.card (Fin 2 → k) = Nat.card k ^ 2 := by
      rw [Nat.card_fun]
      simp
    omega
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_le_ker_of_lt_top S hlt
  have hfv : ∀ v : Fin 2 → k, f v = f (Pi.single 0 1) * v 0 + f (Pi.single 1 1) * v 1 := by
    intro v
    have : v = v 0 • (Pi.single 0 1 : Fin 2 → k) + v 1 • Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [this]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  refine ⟨f (Pi.single 0 1), f (Pi.single 1 1), ?_, fun v hv => ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hf0
    refine LinearMap.ext fun v => ?_
    rw [hfv, hcon.1, hcon.2]
    simp
  · have := LinearMap.mem_ker.mp (hfS hv)
    rwa [hfv] at this

theorem eq_one_of_chars_ker {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p ^ 2) (χ₁ χ₂ : G →* Multiplicative (ZMod p))
    (hχ : ∀ m n : ZMod p, (∀ y : G, m * (χ₁ y).toAdd + n * (χ₂ y).toAdd = 0) → m = 0 ∧ n = 0)
    {y : G} (h1 : χ₁ y = 1) (h2 : χ₂ y = 1) : y = 1 := by
  by_contra hy
  let c₁ : Additive G →+ ZMod p :=
    { toFun := fun g => (χ₁ (Additive.toMul g)).toAdd
      map_zero' := by simp
      map_add' := fun a b => by simp }
  let c₂ : Additive G →+ ZMod p :=
    { toFun := fun g => (χ₂ (Additive.toMul g)).toAdd
      map_zero' := by simp
      map_add' := fun a b => by simp }
  let F : Additive G →+ (Fin 2 → ZMod p) := AddMonoidHom.pi fun i => if i = 0 then c₁ else c₂
  have hF : ∀ g : G, F (Additive.ofMul g) = ![(χ₁ g).toAdd, (χ₂ g).toAdd] := by
    intro g
    ext i
    fin_cases i <;> simp [F, c₁, c₂]
  have hfin : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ hp.out.ne_zero)
  have hcardG : Nat.card (Additive G) = p ^ 2 := by rw [← hG]; rfl
  have hker1 : Additive.ofMul y ∈ F.ker := by
    rw [AddMonoidHom.mem_ker, hF, h1, h2]
    ext i
    fin_cases i <;> rfl
  have hprod := F.ker.card_mul_index
  rw [AddSubgroup.index_ker, hcardG] at hprod
  have hdvd : Nat.card F.ker ∣ p ^ 2 := by
    rw [← hcardG]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hne : 1 < Nat.card F.ker := by
    have : Nontrivial F.ker := ⟨⟨⟨Additive.ofMul y, hker1⟩, 0, fun h => hy (by
      have := congrArg Subtype.val h
      exact this)⟩⟩
    exact Finite.one_lt_card
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    omega
  have hpk : p ≤ Nat.card F.ker := by
    rw [hcard]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.out.pos (Nat.one_le_iff_ne_zero.mpr hi0)
  have hrange : Nat.card F.range ≤ p := by
    by_contra hlt
    push Not at hlt
    have : p * p < Nat.card F.ker * Nat.card F.range :=
      calc p * p < p * Nat.card F.range := Nat.mul_lt_mul_of_pos_left hlt hp.out.pos
        _ ≤ Nat.card F.ker * Nat.card F.range := Nat.mul_le_mul_right _ hpk
    rw [hprod] at this
    nlinarith
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let W : Submodule (ZMod p) (Fin 2 → ZMod p) :=
    { carrier := F.range
      add_mem' := fun ha hb => F.range.add_mem ha hb
      zero_mem' := F.range.zero_mem
      smul_mem' := fun c v hv => by
        have hc : c • v = c.val • v := by
          calc c • v = ((c.val : ℕ) : ZMod p) • v := by rw [ZMod.natCast_zmod_val]
            _ = c.val • v := Nat.cast_smul_eq_nsmul _ _ _
        show c • v ∈ F.range
        rw [hc]
        exact F.range.nsmul_mem hv _ }
  have hWcard : Nat.card W < Nat.card (ZMod p) ^ 2 := by
    have h1 : Nat.card W = Nat.card F.range := rfl
    rw [h1, Nat.card_zmod]
    have hp2 := hp.out.two_le
    nlinarith
  obtain ⟨m, n, hmn, hW⟩ := exists_functional_of_card_lt W hWcard
  obtain ⟨hm, hn⟩ := hχ m n (fun g => by
    have hg : F (Additive.ofMul g) ∈ W := ⟨Additive.ofMul g, rfl⟩
    have := hW _ hg
    rw [hF] at this
    simpa using this)
  rcases hmn with h | h
  · exact h hm
  · exact h hn

end Characters

section Field

variable {K : Type*} [Field K] [Finite K] {E : Type*} [Field E] [Algebra K E]

theorem exists_quadData_norm (hE : finrank K E = 2) :
    ∃ (D : QuadData K E) (c : E), (∀ z, D.bar z = z ^ Nat.card K) ∧ c ≠ 0 ∧ D.Nm c = -1 := by
  obtain ⟨D, hbar⟩ := exists_quadData hE
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite K E := Module.finite_of_finrank_pos (by omega)
  have : Finite E := Module.finite_of_finite K
  have : Fintype E := Fintype.ofFinite E
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  have hcardE : Nat.card E = ringChar K ^ (2 * (n : ℕ)) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := E), hE, hn, ← pow_mul,
      mul_comm]
  have hU : UnitaryFieldData (ringChar K) (n : ℕ) E := ⟨hℓ, n.pos, hcardE⟩
  have hmem : (-1 : E) ∈ hU.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_neg, map_one]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨-1, hmem⟩
  have hnorm : hU.norm c = -1 := congrArg Subtype.val hc
  have hqn : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hcq : c * D.bar c = -1 := by
    rw [hbar, hqn, ← hnorm, UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
  have hNm : D.Nm c = -1 := by
    refine (algebraMap K E).injective ?_
    rw [D.algebraMap_Nm, hcq, map_neg, map_one]
  refine ⟨D, c, hbar, ?_, hNm⟩
  rintro rfl
  have hx0 : D.X 0 = 0 := by simpa using D.X_algebraMap 0
  have hy0 : D.Y 0 = 0 := by simpa using D.Y_algebraMap 0
  have h0 : D.Nm 0 = 0 := by simp [QuadData.Nm, hx0, hy0]
  have h1 : (-1 : K) = 0 := by rw [← hNm, h0]
  exact one_ne_zero (neg_eq_zero.mp h1)

end Field

section Component

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_special_component (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpl : p ≠ ringChar K) (Dg : Subgroup (MulAut (ProjOrthDerived Q)))
    (hDg : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ Dg)
    (x : orthDerived Q) (hxp : orderOf x = p) {E : Type*} [Field E] [Algebra K E]
    (D : QuadData K E) {μ₁ μ₂ : E} (hμ₁0 : μ₁ ≠ 0) (hμ₁1 : μ₁ ≠ 1) (hbar : D.bar μ₁ = μ₁⁻¹)
    (hroot₂ : aeval μ₂ (minpoly K μ₁) = 0) {U₁ U₂ : Submodule K V} {φ₁ : E →ₗ[K] U₁}
    {φ₂ : E →ₗ[K] U₂} (hN : NormPlanes D Q U₁ U₂ φ₁ φ₂)
    (hx₁ : ∀ z, (x : V ≃ₗ[K] V) (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, (x : V ≃ₗ[K] V) (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) {G : Type*} [Group G]
    (hG : Group.IsPerfect G) (ι : G →* (V ≃ₗ[K] V))
    (hιO : ∀ g, ι g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hιx : ∀ g, ι g * (x : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) * ι g)
    (hιfix : ∀ g, ∀ w ∈ orthPerp Q (U₁ ⊔ U₂), ι g w = w) :
    ∃ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧ h = reciprocalPolynomial h ∧
      2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ∧
      ι.range ≤ specialBlock Q (x : V ≃ₗ[K] V) h ∧
      specialBlock Q (x : V ≃ₗ[K] V) h ≤
        orthDerived Q ⊓ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) ∧
      specialBlock Q (x : V ≃ₗ[K] V) h ≠ ⊥ ∧
      IsComponent (((componentImage Q (x : V ≃ₗ[K] V) h).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
        (Dg ⊓ Subgroup.centralizer
          ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
            Set (MulAut (ProjOrthDerived Q))))) ∧
      (componentImage Q (x : V ≃ₗ[K] V) h).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
        inSubgroup CFSG.layer (Dg ⊓ Subgroup.centralizer
          ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
            Set (MulAut (ProjOrthDerived Q)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Module.Finite K E := Module.Finite.of_basis D.basis
  have hxO : OddOrderIsometry Q p (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hint : IsIntegral K μ₁ := Algebra.IsIntegral.isIntegral μ₁
  have hirr : Irreducible (minpoly K μ₁) := minpoly.irreducible hint
  have hmon : (minpoly K μ₁).Monic := minpoly.monic hint
  have hroot₁ : aeval μ₁ (minpoly K μ₁) = 0 := minpoly.aeval K μ₁
  have hR : U₁ ⊔ U₂ ≤ primaryComponent (x : V ≃ₗ[K] V).toLinearMap (minpoly K μ₁) :=
    sup_le_primaryComponent hN.φ₁_surjective hN.φ₂_surjective hx₁ hx₂ hroot₁ hroot₂
  have hR4 : finrank K ↥(U₁ ⊔ U₂) = 4 := hN.finrank_sup
  have hne : primaryComponent (x : V ≃ₗ[K] V).toLinearMap (minpoly K μ₁) ≠ ⊥ := by
    intro h0
    rw [h0, le_bot_iff] at hR
    rw [hR, finrank_bot] at hR4
    omega
  have hmem : minpoly K μ₁ ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap :=
    mem_primaryFactors_of_primaryComponent_ne_bot hirr hmon hne
  have hself : reciprocalPolynomial (minpoly K μ₁) = minpoly K μ₁ :=
    reciprocalPolynomial_minpoly_eq D.bar hμ₁0 hbar
  have hdeg : (minpoly K μ₁).natDegree ≤ 2 := by
    have : (minpoly K μ₁).natDegree ≤ finrank K E := minpoly.natDegree_le μ₁
    rwa [D.finrank_eq_two] at this
  have : Fact (Irreducible (minpoly K μ₁)) := ⟨hirr⟩
  have hmult : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (minpoly K μ₁) :=
    two_le_primaryMultiplicity hdeg hR hR4
  have hne1 : minpoly K μ₁ ≠ X - 1 := by
    intro h1
    have := hroot₁
    rw [h1, map_sub, aeval_X, map_one, sub_eq_zero] at this
    exact hμ₁1 this
  have hι : ι.range ≤ specialBlock Q (x : V ≃ₗ[K] V) (minpoly K μ₁) :=
    range_le_specialBlock hxO hmem hR hG ι hιO hιx hιfix
  obtain ⟨-, -, hZcard, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have ha : orderOf (QuotientGroup.mk x : ProjOrthDerived Q) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      have hxZ : x ∈ (scalars K V).subgroupOf (orthDerived Q) := (QuotientGroup.eq_one_iff x).mp h1
      have h2 := orderOf_dvd_natCard (⟨x, hxZ⟩ : ↥((scalars K V).subgroupOf (orthDerived Q)))
      have h3 : orderOf (⟨x, hxZ⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) = p := by
        rw [← hxp]
        exact Subgroup.orderOf_mk x hxZ
      rw [h3] at h2
      have := Nat.le_of_dvd (by
        have : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
        exact this) h2
      omega
  obtain ⟨⟨Rep, hRep⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl Dg hDg
      (QuotientGroup.mk x) ha x rfl hxp
  obtain ⟨-, -, -, -, -, hspecial, -, -⟩ := hmain Rep hRep
  have hhRep : minpoly K μ₁ ∈ Rep := mem_of_isOrbitRepresentatives_of_selfdual hxO hRep hmem hself
  obtain ⟨hsb, -, hcne, -, hcent, -, hcomp⟩ := hspecial _ hhRep hne1 hmult
  refine ⟨minpoly K μ₁, hmem, hne1, hself.symm, hmult, hι, ?_, ?_, hcomp, ?_⟩
  · intro g hg
    refine Subgroup.mem_inf.mpr ⟨hsb hg, ?_⟩
    exact (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _
      (specialBlock_le_supportedBlock _ hg))).2
  · intro hbot
    apply hcne
    rw [componentImage, hbot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  ·
    set C : Subgroup (MulAut (ProjOrthDerived Q)) := Dg ⊓ Subgroup.centralizer
      ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (MulAut (ProjOrthDerived Q))) with hC
    have hXC : (componentImage Q (x : V ≃ₗ[K] V) (minpoly K μ₁)).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤ C := by
      rintro _ ⟨t, ht, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hDg ⟨t, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hcent ht)
      rw [← map_mul, ← map_mul, this]
    have hlayer : (((componentImage Q (x : V ≃ₗ[K] V) (minpoly K μ₁)).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf C) ≤
        CFSG.layer ↥C := le_sSup hcomp
    have hmap := Subgroup.map_mono (f := C.subtype) hlayer
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXC] at hmap
    exact hmap

end Component

section Commute

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] {D : QuadData K E}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
  {U₁ U₂ : Submodule K V} {φ₁ : E →ₗ[K] U₁} {φ₂ : E →ₗ[K] U₂}

namespace NormPlanes

variable (h : NormPlanes D Q U₁ U₂ φ₁ φ₂) {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1)

include h hc hNc

omit [FiniteDimensional K V] in
theorem isoDet_symm_apply (g : ↥(DeterminantIsometries K)) (r : ↥(U₁ ⊔ U₂)) :
    (((h.isoDet hc hNc).symm g :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U₁ ⊔ U₂).subtype))) :
      ↥(U₁ ⊔ U₂) ≃ₗ[K] ↥(U₁ ⊔ U₂)) r =
      (h.normPlaneIsometry hc hNc).symm
        ((g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
          (h.normPlaneIsometry hc hNc r)) :=
  TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply _ g r

theorem iota₂_commute_left {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {lam : E} (hlam : lam ≠ 0)
    (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (lam * z) : V)) (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (lam * z) : V))
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    h.iota₂ hc hNc B * x = x * h.iota₂ hc hNc B := by
  have hxR : ∀ r ∈ U₁ ⊔ U₂, x r ∈ U₁ ⊔ U₂ := fun r hr => h.act_mem_sup hx₁ hx₂ hr
  have hxP : ∀ w ∈ orthPerp Q (U₁ ⊔ U₂), x w ∈ orthPerp Q (U₁ ⊔ U₂) := fun w hw =>
    mem_orthPerp.mpr (h.act_perp hxO hlam hlam hx₁ hx₂ (mem_orthPerp.mp hw))
  have key : h.iota₂ hc hNc B = extendHom (h.isCompl hc hNc)
      ((h.isoDet hc hNc).symm (specialRho (1, B))) := rfl
  rw [key]
  refine extendHom_commute (h.isCompl hc hNc) hxR hxP _ ?_
  have happ : ∀ r' : ↥(U₁ ⊔ U₂),
      (((h.isoDet hc hNc).symm (specialRho (1, B)) :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U₁ ⊔ U₂).subtype))) :
        ↥(U₁ ⊔ U₂) ≃ₗ[K] ↥(U₁ ⊔ U₂)) r' =
      (h.normPlaneIsometry hc hNc).symm
        (h.normPlaneIsometry hc hNc r' * (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val) := by
    intro r'
    rw [h.isoDet_symm_apply hc hNc, specialRho_apply]
    simp
  intro r
  set ψ := h.normPlaneIsometry hc hNc with hψ
  obtain ⟨hr, h1⟩ := h.psi_left hc hNc hx₁ hx₂ r
  obtain ⟨hr2, h2⟩ := h.psi_left hc hNc hx₁ hx₂
    (ψ.symm (ψ r * (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val))
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply] at h2
  rw [happ, happ]
  have e : (⟨x ((ψ.symm (ψ r * (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val) :
      ↥(U₁ ⊔ U₂)) : V), hr2⟩ : ↥(U₁ ⊔ U₂)) =
      ψ.symm (D.lmat lam * (ψ r * (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val)) := by
    rw [← h2, QuadraticMap.IsometryEquiv.symm_apply_apply]
  have e' : ((ψ.symm (ψ ⟨x r, hr⟩ * (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val) :
      ↥(U₁ ⊔ U₂)) : V) =
      ((ψ.symm (D.lmat lam * (ψ r * (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val)) :
        ↥(U₁ ⊔ U₂)) : V) := by
    rw [h1, Matrix.mul_assoc]
  rw [e']
  exact congrArg Subtype.val e.symm

theorem iota₁_commute_right {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {eta : E} (heta : eta ≠ 0)
    (hbar : D.bar eta ≠ 0) (hx₁ : ∀ z, x (φ₁ z : V) = (φ₁ (eta * z) : V))
    (hx₂ : ∀ z, x (φ₂ z : V) = (φ₂ (D.bar eta * z) : V))
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    h.iota₁ hc hNc A * x = x * h.iota₁ hc hNc A := by
  have hxR : ∀ r ∈ U₁ ⊔ U₂, x r ∈ U₁ ⊔ U₂ := fun r hr => h.act_mem_sup hx₁ hx₂ hr
  have hxP : ∀ w ∈ orthPerp Q (U₁ ⊔ U₂), x w ∈ orthPerp Q (U₁ ⊔ U₂) := fun w hw =>
    mem_orthPerp.mpr (h.act_perp hxO heta hbar hx₁ hx₂ (mem_orthPerp.mp hw))
  have key : h.iota₁ hc hNc A = extendHom (h.isCompl hc hNc)
      ((h.isoDet hc hNc).symm (specialRho (A, 1))) := rfl
  rw [key]
  refine extendHom_commute (h.isCompl hc hNc) hxR hxP _ ?_
  have happ : ∀ r' : ↥(U₁ ⊔ U₂),
      (((h.isoDet hc hNc).symm (specialRho (A, 1)) :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U₁ ⊔ U₂).subtype))) :
        ↥(U₁ ⊔ U₂) ≃ₗ[K] ↥(U₁ ⊔ U₂)) r' =
      (h.normPlaneIsometry hc hNc).symm (A.val * h.normPlaneIsometry hc hNc r') := by
    intro r'
    rw [h.isoDet_symm_apply hc hNc, specialRho_apply]
    simp
  intro r
  set ψ := h.normPlaneIsometry hc hNc with hψ
  obtain ⟨hr, h1⟩ := h.psi_right hc hNc hx₁ hx₂ r
  obtain ⟨hr2, h2⟩ := h.psi_right hc hNc hx₁ hx₂ (ψ.symm (A.val * ψ r))
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply] at h2
  rw [happ, happ]
  have e : (⟨x ((ψ.symm (A.val * ψ r) : ↥(U₁ ⊔ U₂)) : V), hr2⟩ : ↥(U₁ ⊔ U₂)) =
      ψ.symm ((A.val * ψ r) * D.lmat eta) := by
    rw [← h2, QuadraticMap.IsometryEquiv.symm_apply_apply]
  have e' : ((ψ.symm (A.val * ψ ⟨x r, hr⟩) : ↥(U₁ ⊔ U₂)) : V) =
      ((ψ.symm ((A.val * ψ r) * D.lmat eta) : ↥(U₁ ⊔ U₂)) : V) := by
    rw [h1, Matrix.mul_assoc]
  rw [e']
  exact congrArg Subtype.val e.symm

end NormPlanes

end Commute

section Dimension

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem six_le_finrank (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) : 6 ≤ finrank K V := by
  obtain ⟨T, hT3, hTQ⟩ := hT
  have hTT : T ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) T := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    rw [polarBilin_apply_apply, polar, hTQ _ (T.add_mem hb ha), hTQ b hb, hTQ a ha, sub_zero,
      sub_zero]
  have h1 := Submodule.finrank_mono hTT
  rw [LinearMap.BilinForm.finrank_orthogonal hQ T, hT3] at h1
  omega

omit [FiniteDimensional K V] in
theorem exists_ne_zero_orthPerp {R : Submodule K V} (hR : IsCompl R (orthPerp Q R))
    (hR4 : finrank K R = 4) (hV : 6 ≤ finrank K V) : ∃ w ∈ orthPerp Q R, w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hbot : orthPerp Q R = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
  have htop : R = ⊤ := by
    have := hR.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  rw [htop, finrank_top] at hR4
  omega

end Dimension

end CFSG.RankThree.PartOne.KCOrthogonal
