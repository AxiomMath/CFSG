module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltXhat
public import CFSG.LargeExtraspecial.A2ModPLCohomology
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

import CFSG.RankThree.GF2n.Stroth78.Sec3SevenFix
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LargeExtraspecial.A2Mod (IsPointMaps)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

private theorem exists_mem_commutator_of_mem_zpowers (S : Setting z E F) {x : G}
    (hx : x ∈ Subgroup.zpowers z) :
    ∃ c ∈ _root_.commutator ↥(Q z), ((c : ↥(Q z)) : G) = x := by
  have h := Subgroup.map_subtype_commutator (Q z)
  rw [Q_deriv_eq S] at h
  have hx' : x ∈ (_root_.commutator ↥(Q z)).map (Q z).subtype := by rw [h]; exact hx
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx'
  exact ⟨c, hc, rfl⟩

theorem exists_hom_zmodTwo_apply_ne_one (S : Setting z E F) {b : G} (hb : b ∈ Q z)
    (hbz : b ∉ Subgroup.zpowers z) :
    ∃ lam : ↥(Q z) →* Multiplicative (ZMod 2), lam ⟨b, hb⟩ ≠ 1 := by
  have hsq : ∀ q : ↥(Q z), q ^ 2 ∈ _root_.commutator ↥(Q z) := by
    intro q
    obtain ⟨c, hc, hcq⟩ := exists_mem_commutator_of_mem_zpowers S
      (sq_mem_zpowers_of_mem_Q S q.2)
    have : c = q ^ 2 := Subtype.ext hcq
    rwa [this] at hc
  have hof : ∀ q : ↥(Q z), (Abelianization.of q) ^ 2 = 1 := fun q => by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker _ (hsq q))
  have hsurj : Function.Surjective (Abelianization.of : ↥(Q z) →* Abelianization ↥(Q z)) := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, by rw [← hg]; rfl⟩
  letI : Module (ZMod 2) (Additive (Abelianization ↥(Q z))) :=
    AddCommGroup.zmodModule (fun x => by
      obtain ⟨q, hq⟩ := hsurj (Additive.toMul x)
      apply Additive.toMul.injective
      rw [toMul_nsmul, ← hq, toMul_zero]
      exact hof q)
  have hb1 : (Additive.ofMul (Abelianization.of (⟨b, hb⟩ : ↥(Q z))) :
      Additive (Abelianization ↥(Q z))) ≠ 0 := by
    intro h
    have h1 : Abelianization.of (⟨b, hb⟩ : ↥(Q z)) = 1 := h
    have h2 : (⟨b, hb⟩ : ↥(Q z)) ∈ _root_.commutator ↥(Q z) := by
      have := MonoidHom.mem_ker.mpr h1
      rwa [Abelianization.ker_of] at this
    have h3 : b ∈ (_root_.commutator ↥(Q z)).map (Q z).subtype := ⟨⟨b, hb⟩, h2, rfl⟩
    rw [Subgroup.map_subtype_commutator, Q_deriv_eq S] at h3
    exact hbz h3
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Additive (Abelianization ↥(Q z))),
      φ (Additive.ofMul (Abelianization.of (⟨b, hb⟩ : ↥(Q z)))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb1 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hcon)
  refine ⟨{ toFun := fun q => Multiplicative.ofAdd (φ (Additive.ofMul (Abelianization.of q)))
            map_one' := by simp
            map_mul' := fun q q' => by simp [map_add] }, ?_⟩
  intro h
  apply hφ
  exact Multiplicative.ofAdd.injective h

private noncomputable def liftQbar (S : Setting z E F) (f : ↥(Q z) →* Multiplicative (ZMod 2))
    (hf : ∀ q : ↥(Q z), (q : G) ∈ ZQ z → f q = 1) : QbarOf S →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift ((ZQ z).subgroupOf (Q z)) f
    (fun q hq => hf q (Subgroup.mem_subgroupOf.mp hq))

private theorem liftQbar_mkQbar (S : Setting z E F) (f : ↥(Q z) →* Multiplicative (ZMod 2))
    (hf : ∀ q : ↥(Q z), (q : G) ∈ ZQ z → f q = 1) (q : ↥(Q z)) :
    liftQbar S f hf (mkQbar S q) = f q :=
  QuotientGroup.lift_mk _ _ q

private noncomputable def liftV (S : Setting z E F) (f : ↥(Q z) →* Multiplicative (ZMod 2))
    (hf : ∀ q : ↥(Q z), (q : G) ∈ ZQ z → f q = 1) :
    Additive (QbarOf S) →ₗ[ZMod 2] ZMod 2 :=
  AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditiveLeft (liftQbar S f hf))

private theorem liftV_apply (S : Setting z E F) (f : ↥(Q z) →* Multiplicative (ZMod 2))
    (hf : ∀ q : ↥(Q z), (q : G) ∈ ZQ z → f q = 1) (q : ↥(Q z)) :
    liftV S f hf (Additive.ofMul (mkQbar S q)) = Multiplicative.toAdd (f q) := by
  simp only [liftV, AddMonoidHom.coe_toZModLinearMap, MonoidHom.coe_toAdditiveLeft,
    Function.comp_apply, toMul_ofMul, liftQbar_mkQbar]

private theorem conjAutQ_inv_apply (S : Setting z E F) (h : ↥(H z)) (q : ↥(Q z)) :
    ((conjAutQ S h⁻¹ q : ↥(Q z)) : G) = (h : G)⁻¹ * (q : G) * (h : G) := by
  rw [conjAutQ_apply]
  simp

private theorem rhoLin_inv_mk_apply (S : Setting z E F) (h : ↥(H z)) (q : ↥(Q z)) :
    rhoLin S (QuotientGroup.mk h⁻¹) (Additive.ofMul (mkQbar S q)) =
      Additive.ofMul (mkQbar S (conjAutQ S h⁻¹ q)) := by
  rw [rhoLin_mk_eq_conjQbar]
  exact conjQbar_apply_mk S h⁻¹ q

private noncomputable def dlf (S : Setting z E F) (a : G)
    (lam0 : ↥(Q z) →* Multiplicative (ZMod 2)) (g : ↥(XsubPre S a)) :
    ↥(Q z) →* Multiplicative (ZMod 2) :=
  (lam0.comp (conjAutQ S (g : ↥(H z))⁻¹).toMonoidHom) * lam0⁻¹

private theorem dlf_apply (S : Setting z E F) (a : G) (lam0 : ↥(Q z) →* Multiplicative (ZMod 2))
    (g : ↥(XsubPre S a)) (q : ↥(Q z)) :
    dlf S a lam0 g q = lam0 (conjAutQ S (g : ↥(H z))⁻¹ q) * (lam0 q)⁻¹ := rfl

private theorem dlf_eq_one_of_mem_ZQ (S : Setting z E F) (a : G)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (lam0 : ↥(Q z) →* Multiplicative (ZMod 2)) (g : ↥(XsubPre S a)) (q : ↥(Q z))
    (hq : (q : G) ∈ ZQ z) : dlf S a lam0 g q = 1 := by
  have h1 := rhoZ_mk S (g : ↥(H z)) ⟨(q : G), hq⟩
  have h2 : rhoZ S (QuotientGroup.mk (g : ↥(H z))) ⟨(q : G), hq⟩ = ⟨(q : G), hq⟩ :=
    hX1 _ g.2 _
  rw [h2] at h1
  have h3 : ((g : ↥(H z)) : G) * (q : G) * ((g : ↥(H z)) : G)⁻¹ = (q : G) := h1.symm
  have h4 : conjAutQ S (g : ↥(H z))⁻¹ q = q := by
    apply Subtype.ext
    rw [conjAutQ_inv_apply]
    generalize ((g : ↥(H z)) : G) = gg at h3 ⊢
    calc gg⁻¹ * (q : G) * gg = gg⁻¹ * (gg * (q : G) * gg⁻¹) * gg := by rw [h3]
      _ = (q : G) := by group
  rw [dlf_apply, h4, mul_inv_cancel]

private noncomputable def psiV (S : Setting z E F) (a : G)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (lam0 : ↥(Q z) →* Multiplicative (ZMod 2)) (g : ↥(XsubPre S a)) :
    Additive (QbarOf S) →ₗ[ZMod 2] ZMod 2 :=
  liftV S (dlf S a lam0 g) (fun q hq => dlf_eq_one_of_mem_ZQ S a hX1 lam0 g q hq)

private theorem psiV_apply (S : Setting z E F) (a : G)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (lam0 : ↥(Q z) →* Multiplicative (ZMod 2)) (g : ↥(XsubPre S a)) (q : ↥(Q z)) :
    psiV S a hX1 lam0 g (Additive.ofMul (mkQbar S q)) =
      Multiplicative.toAdd (lam0 (conjAutQ S (g : ↥(H z))⁻¹ q)) -
        Multiplicative.toAdd (lam0 q) := by
  rw [psiV, liftV_apply, dlf_apply, toAdd_mul, toAdd_inv, sub_eq_add_neg]

private theorem psiV_mul (S : Setting z E F) (a : G)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (lam0 : ↥(Q z) →* Multiplicative (ZMod 2)) (g h : ↥(XsubPre S a))
    (v : Additive (QbarOf S)) :
    psiV S a hX1 lam0 (g * h) v = psiV S a hX1 lam0 g v +
      psiV S a hX1 lam0 h (rhoLin S (QuotientGroup.mk (g : ↥(H z))⁻¹) v) := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) (Additive.toMul v)
  have hv : v = Additive.ofMul (mkQbar S q) := by
    have h0 := congrArg Additive.ofMul hq.symm
    simpa [mkQbar] using h0
  subst hv
  rw [rhoLin_inv_mk_apply, psiV_apply, psiV_apply, psiV_apply]
  have e : conjAutQ S ((g * h : ↥(XsubPre S a)) : ↥(H z))⁻¹ q =
      conjAutQ S (h : ↥(H z))⁻¹ (conjAutQ S (g : ↥(H z))⁻¹ q) := by
    rw [Subgroup.coe_mul, mul_inv_rev, conjAutQ_mul, MulAut.mul_apply]
  rw [e]
  ring

private theorem polarBilin_rhoLin (S : Setting z E F) (x : Hbar z)
    (u v : Additive (QbarOf S)) :
    (qS S).polarBilin (rhoLin S x u) v = (qS S).polarBilin u (rhoLin S x⁻¹ v) := by
  have hO : rhoLin S x ∈ TauCeti.QuadraticMap.orthogonalGroup (qS S) := (rhoBar S x).2
  have hv : rhoLin S x (rhoLin S x⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← rhoLin_mul, mul_inv_cancel]
    simp [rhoLin]
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  conv_lhs => rw [← hv]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO u (rhoLin S x⁻¹ v)

theorem exists_invariant_hom_of_pointMaps (S : Setting z E F) (a : G)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (ρX : ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
    (hρX : ∀ x : ↥(Xsub S a), ρX x = rhoLin S (x : Hbar z))
    (Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a))
    (hΨs : Function.Surjective Ψ) (hΨi : Function.Injective Ψ)
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)}
    (hP : IsPointMaps (ρX.comp Ψ) (qS S) P Pd)
    (htop : LinearMap.range P ⊔ LinearMap.range Pd = ⊤)
    (lam0 : ↥(Q z) →* Multiplicative (ZMod 2)) :
    ∃ lam : ↥(Q z) →* Multiplicative (ZMod 2),
      (∀ q : ↥(Q z), (q : G) ∈ ZQ z → lam q = lam0 q) ∧
      ∀ (g : ↥(XsubPre S a)) (q : ↥(Q z)), lam (conjAutQ S (g : ↥(H z)) q) = lam q := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hB : (qS S).polarBilin.Nondegenerate := q_nondegenerate S

  let Ψe : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃* ↥(Xsub S a) :=
    MulEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩
  let π : ↥(XsubPre S a) →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    Ψe.symm.toMonoidHom.comp (toXsub S a)
  have hπ : Function.Surjective π := fun s => by
    obtain ⟨g, hg⟩ := toXsub_surjective S a (Ψe s)
    refine ⟨g, ?_⟩
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hg, MulEquiv.symm_apply_apply]
  have hρπ : ∀ g : ↥(XsubPre S a), (ρX.comp Ψ) (π g) =
      rhoLin S (QuotientGroup.mk (g : ↥(H z))) := by
    intro g
    have h1 : Ψ (π g) = toXsub S a g := by
      simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact Ψe.apply_symm_apply _
    rw [MonoidHom.comp_apply, h1, hρX]
    rfl
  let δ : ↥(XsubPre S a) → Additive (QbarOf S) :=
    fun g => (LinearMap.BilinForm.toDual (qS S).polarBilin hB).symm (psiV S a hX1 lam0 g)
  have hδB : ∀ g v, (qS S).polarBilin (δ g) v = psiV S a hX1 lam0 g v := by
    intro g v
    have h1 := LinearMap.BilinForm.toDual_def (B := (qS S).polarBilin) hB (m := δ g) (n := v)
    rw [← h1]
    simp [δ]
  have hext : ∀ x y : Additive (QbarOf S),
      (∀ v, (qS S).polarBilin x v = (qS S).polarBilin y v) → x = y := by
    intro x y hxy
    apply (LinearMap.BilinForm.toDual (qS S).polarBilin hB).injective
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def]
    exact hxy v
  have hδcoc : ∀ g h, δ (g * h) = δ g + (ρX.comp Ψ) (π g) (δ h) := by
    intro g h
    apply hext
    intro v
    rw [hδB, map_add, LinearMap.add_apply, hδB, hρπ, polarBilin_rhoLin, hδB, psiV_mul,
      ← QuotientGroup.mk_inv]
  have hδker : ∀ g, π g = 1 → δ g = 0 := by
    intro g hg
    have hx : toXsub S a g = 1 := by
      have h1 : Ψe.symm (toXsub S a g) = 1 := hg
      exact (MulEquiv.map_eq_one_iff Ψe.symm).mp h1
    have hgQ : ((g : ↥(H z)) : G) ∈ Q z := (toXsub_eq_one_iff S a g).mp hx
    apply hext
    intro v
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) (Additive.toMul v)
    have hv : v = Additive.ofMul (mkQbar S q) := by
      have h0 := congrArg Additive.ofMul hq.symm
      simpa [mkQbar] using h0
    subst hv
    rw [hδB, map_zero, LinearMap.zero_apply, psiV_apply]
    have hc : conjAutQ S (g : ↥(H z))⁻¹ q =
        (⟨(g : ↥(H z)), hgQ⟩ : ↥(Q z))⁻¹ * q * ⟨(g : ↥(H z)), hgQ⟩ :=
      Subtype.ext (by rw [conjAutQ_inv_apply]; rfl)
    have h2 : lam0 (conjAutQ S (g : ↥(H z))⁻¹ q) = lam0 q := by
      rw [hc, map_mul, map_mul, map_inv]
      simp [mul_comm, mul_left_comm]
    rw [h2, sub_self]
  obtain ⟨w, hw⟩ := hP.exists_coboundary htop π hπ δ hδcoc hδker
  let tw : ↥(Q z) →* Multiplicative (ZMod 2) :=
    { toFun := fun q => Multiplicative.ofAdd
        ((qS S).polarBilin w (Additive.ofMul (mkQbar S q)))
      map_one' := by simp
      map_mul' := fun q q' => by
        simp only [map_mul, ofMul_mul, map_add, ofAdd_add] }
  have htw : ∀ q : ↥(Q z), tw q = Multiplicative.ofAdd
      ((qS S).polarBilin w (Additive.ofMul (mkQbar S q))) := fun q => rfl
  refine ⟨lam0 * tw, ?_, ?_⟩
  · intro q hq
    have h1 : mkQbar S q = 1 :=
      (QuotientGroup.eq_one_iff q).mpr (Subgroup.mem_subgroupOf.mpr hq)
    rw [MonoidHom.mul_apply, htw, h1]
    simp
  · have key : ∀ (g : ↥(XsubPre S a)) (q : ↥(Q z)),
        (lam0 * tw) (conjAutQ S (g : ↥(H z))⁻¹ q) = (lam0 * tw) q := by
      intro g q
      have h1 := hδB g (Additive.ofMul (mkQbar S q))
      rw [hw g, map_add, LinearMap.add_apply, hρπ, polarBilin_rhoLin, psiV_apply] at h1
      apply Multiplicative.toAdd.injective
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, htw, htw, toAdd_mul, toAdd_mul,
        toAdd_ofAdd, toAdd_ofAdd, ← rhoLin_inv_mk_apply]
      rw [← QuotientGroup.mk_inv] at h1
      revert h1
      generalize Multiplicative.toAdd (lam0 (conjAutQ S (g : ↥(H z))⁻¹ q)) = A
      generalize Multiplicative.toAdd (lam0 q) = Bq
      generalize (qS S).polarBilin w (rhoLin S (QuotientGroup.mk (g : ↥(H z))⁻¹)
        (Additive.ofMul (mkQbar S q))) = X
      generalize (qS S).polarBilin w (Additive.ofMul (mkQbar S q)) = Y
      revert A Bq X Y
      decide
    intro g q
    have := key g⁻¹ q
    simpa using this

theorem FsubH_le_ker_of_invariant (S : Setting z E F) (a : G)
    (lam : ↥(Q z) →* Multiplicative (ZMod 2))
    (hlam : ∀ (g : ↥(XsubPre S a)) (q : ↥(Q z)), lam (conjAutQ S (g : ↥(H z)) q) = lam q) :
    ∀ f ∈ FsubH S a, ∃ hf : f ∈ Q z, lam ⟨f, hf⟩ = 1 := by
  have hle : FsubH S a ≤ lam.ker.map (Q z).subtype := by
    rw [FsubH, Subgroup.commutator_le]
    intro q hq x hx
    obtain ⟨hxH, hxX⟩ := (mem_XsubHat_iff S a).mp hx
    let g : ↥(XsubPre S a) := ⟨⟨x, hxH⟩, hxX⟩
    let qq : ↥(Q z) := ⟨q, hq⟩
    have hc : (((conjAutQ S (g : ↥(H z)) qq⁻¹ : ↥(Q z))) : G) = x * q⁻¹ * x⁻¹ := by
      rw [conjAutQ_apply]
      rfl
    refine Subgroup.mem_map.mpr ⟨qq * conjAutQ S (g : ↥(H z)) qq⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hlam g qq⁻¹, map_inv, mul_inv_cancel]
    · change q * ((conjAutQ S (g : ↥(H z)) qq⁻¹ : ↥(Q z)) : G) = ⁅q, x⁆
      rw [hc, commutatorElement_def]
      group
  intro f hf
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hle hf)
  exact ⟨y.2, MonoidHom.mem_ker.mp hy⟩

theorem exists_mem_ZQ_not_mem_zpowers (S : Setting z E F) (hZ : Nat.card ↥(ZQ z) = 4) :
    ∃ b ∈ ZQ z, b ∉ Subgroup.zpowers z := by
  by_contra h
  push Not at h
  have hle : ZQ z ≤ Subgroup.zpowers z := h
  have h1 := Subgroup.card_le_of_le hle
  rw [hZ, Nat.card_zpowers, S.hyp.orderOf_z] at h1
  omega

theorem ZQ_inf_ker_eq_zpowers (S : Setting z E F) (hZ : Nat.card ↥(ZQ z) = 4)
    (lam0 : ↥(Q z) →* Multiplicative (ZMod 2)) {b : G} (hbZ : b ∈ ZQ z) (hbQ : b ∈ Q z)
    (hb : lam0 ⟨b, hbQ⟩ ≠ 1) :
    ZQ z ⊓ lam0.ker.map (Q z).subtype = Subgroup.zpowers z := by
  set M : Subgroup G := ZQ z ⊓ lam0.ker.map (Q z).subtype with hM
  have hzM : Subgroup.zpowers z ≤ M := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨z_mem_ZQ S, ?_⟩)
    obtain ⟨c, hc, hcz⟩ := exists_mem_commutator_of_mem_zpowers S (Subgroup.mem_zpowers z)
    have hc1 : lam0 c = 1 :=
      MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker lam0 hc)
    refine Subgroup.mem_map.mpr ⟨c, MonoidHom.mem_ker.mpr hc1, hcz⟩
  have hbM : b ∉ M := by
    intro hbM
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hbM).2
    have : y = ⟨b, hbQ⟩ := Subtype.ext hyb
    rw [this] at hy
    exact hb (MonoidHom.mem_ker.mp hy)
  have hMlt : Nat.card M < 4 := by
    by_contra hge
    push Not at hge
    have : M = ZQ z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZ]; exact hge)
    exact hbM (this ▸ hbZ)
  have hMd : Nat.card M ∣ 4 := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hzd : Nat.card (Subgroup.zpowers z) ∣ Nat.card M := Subgroup.card_dvd_of_le hzM
  rw [Nat.card_zpowers, S.hyp.orderOf_z] at hzd
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hM2 : Nat.card M = 2 := by
    obtain ⟨k, hk⟩ := hzd
    have hle : Nat.card M ≤ 4 := Nat.le_of_dvd (by norm_num) hMd
    omega
  refine (Subgroup.eq_of_le_of_card_ge hzM ?_).symm
  rw [hM2, Nat.card_zpowers, S.hyp.orderOf_z]

theorem Q_le_FsubH_sup_ZQ (S : Setting z E F) (a : G)
    (ρX : ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
    (hρX : ∀ x : ↥(Xsub S a), ρX x = rhoLin S (x : Hbar z))
    (Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a))
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)}
    (hP : IsPointMaps (ρX.comp Ψ) (qS S) P Pd)
    (htop : LinearMap.range P ⊔ LinearMap.range Pd = ⊤) :
    Q z ≤ FsubH S a ⊔ ZQ z := by
  have hW : CFSG.LargeExtraspecial.A2Mod.commSpaceOf (ρX.comp Ψ) ⊤ ≤
      QaInterImage S (FsubH S a ⊔ ZQ z) := by
    rw [CFSG.LargeExtraspecial.A2Mod.commSpaceOf_le_iff]
    intro g _ v hv
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective ((Ψ g : ↥(Xsub S a)) : Hbar z)
    have hsX : (s : ↥(H z)) ∈ XsubPre S a := by
      rw [mem_XsubPre_iff, hs]
      exact (Ψ g).2
    have hρ : (ρX.comp Ψ) g = conjQbar S s := by
      rw [MonoidHom.comp_apply, hρX, ← hs, rhoLin_mk_eq_conjQbar]
    rw [hρ] at hv
    obtain ⟨q, hq⟩ := (mem_commSpace_conjQbar_iff S s.2).mp hv
    refine (mem_QaInterImage_iff S).mpr ⟨⟨⁅(q : G), (s : G)⁆, commutator_mem_Q_of_mem_H s.2 q.2⟩,
      ?_, ?_⟩
    · refine Subgroup.mem_sup_left ?_
      exact Subgroup.commutator_mem_commutator q.2
        ((mem_XsubHat_iff S a).mpr ⟨s.2, hsX⟩)
    · rw [hq]
      simp
  have htop' : QaInterImage S (FsubH S a ⊔ ZQ z) = ⊤ := by
    rw [eq_top_iff]
    refine le_trans ?_ hW
    rw [hP.commSpaceOf_top, htop]
  intro q hq
  have hv : Additive.ofMul (mkQbar S ⟨q, hq⟩) ∈ QaInterImage S (FsubH S a ⊔ ZQ z) := by
    rw [htop']
    trivial
  obtain ⟨y, hyF, hyq⟩ := (mem_QaInterImage_iff S).mp hv
  have hyq' : mkQbar S y = mkQbar S ⟨q, hq⟩ := by simpa using hyq
  have h1 : y⁻¹ * ⟨q, hq⟩ ∈ (ZQ z).subgroupOf (Q z) := by
    rw [← QuotientGroup.eq]
    exact hyq'
  have h2 : (y : G)⁻¹ * q ∈ ZQ z := Subgroup.mem_subgroupOf.mp h1
  have h3 : q = (y : G) * ((y : G)⁻¹ * q) := by group
  rw [h3]
  exact Subgroup.mul_mem _ hyF (Subgroup.mem_sup_right h2)

theorem FsubH_inf_ZQ_eq_and_sup_eq (S : Setting z E F) (a : G)
    (hZ : Nat.card ↥(ZQ z) = 4)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (ρX : ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
    (hρX : ∀ x : ↥(Xsub S a), ρX x = rhoLin S (x : Hbar z))
    (Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a))
    (hΨs : Function.Surjective Ψ) (hΨi : Function.Injective Ψ)
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)}
    (hP : IsPointMaps (ρX.comp Ψ) (qS S) P Pd)
    (htop : LinearMap.range P ⊔ LinearMap.range Pd = ⊤) :
    FsubH S a ⊓ ZQ z = Subgroup.zpowers z ∧ FsubH S a ⊔ ZQ z = Q z := by
  obtain ⟨b, hbZ, hbz⟩ := exists_mem_ZQ_not_mem_zpowers S hZ
  have hbQ : b ∈ Q z := (inf_le_left : ZQ z ≤ Q z) hbZ
  obtain ⟨lam0, hlam0⟩ := exists_hom_zmodTwo_apply_ne_one S hbQ hbz
  obtain ⟨lam, hlamZ, hlam⟩ :=
    exists_invariant_hom_of_pointMaps S a hX1 ρX hρX Ψ hΨs hΨi hP htop lam0
  refine ⟨?_, ?_⟩
  · refine le_antisymm ?_ (le_inf (Subgroup.zpowers_le.mpr (z_mem_FsubH S a))
      (Subgroup.zpowers_le.mpr (z_mem_ZQ S)))
    intro u hu
    obtain ⟨huF, huZ⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨huQ, hlu⟩ := FsubH_le_ker_of_invariant S a lam hlam u huF
    have h1 : lam0 ⟨u, huQ⟩ = 1 := by
      rw [← hlamZ _ huZ]
      exact hlu
    have hM := ZQ_inf_ker_eq_zpowers S hZ lam0 hbZ hbQ hlam0
    rw [← hM]
    exact Subgroup.mem_inf.mpr ⟨huZ, Subgroup.mem_map.mpr
      ⟨⟨u, huQ⟩, MonoidHom.mem_ker.mpr h1, rfl⟩⟩
  · exact le_antisymm (sup_le (FsubH_le_Q S a) inf_le_left)
      (Q_le_FsubH_sup_ZQ S a ρX hρX Ψ hP htop)

end CFSG.RankThree.GF2n.Stroth78
