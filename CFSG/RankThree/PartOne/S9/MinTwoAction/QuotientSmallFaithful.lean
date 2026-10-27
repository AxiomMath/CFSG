module

public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRealize
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientIrreducible
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientShape
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientExtraspecial
public import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.Quotient36
open scoped IsMulCommutative commutatorElement

namespace Quotient36

section Aux

variable {G : Type*} [Group G]

theorem eq_frattini_or_eq_of_irreducible {P H : Subgroup G}
    (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hirr : letI : MulDistribMulAction ↥H ↥P :=
        MulDistribMulAction.compHom ↥P (Subgroup.inclusion hHP)
      letI := frattiniQuotientAction ↥H ↥P
      ∀ T : Subgroup (↥P ⧸ frattini ↥P), (∀ h : ↥H, ∀ v ∈ T, h • v ∈ T) → T = ⊥ ∨ T = ⊤)
    (Y : Subgroup G) (hΦY : inSubgroup frattini P ≤ Y) (hYP : Y ≤ P)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) :
    Y = inSubgroup frattini P ∨ Y = P := by
  let _ : MulDistribMulAction ↥H ↥P := MulDistribMulAction.compHom ↥P (Subgroup.inclusion hHP)
  let _ := frattiniQuotientAction ↥H ↥P
  let Y₀ : Subgroup ↥P := Y.subgroupOf P
  have hY₀ : ∀ y : ↥P, y ∈ Y₀ ↔ (y : G) ∈ Y := fun y => Iff.rfl
  have hmemΦ : ∀ y : ↥P, (y : G) ∈ inSubgroup frattini P ↔ y ∈ frattini ↥P := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      subst this
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  let T : Subgroup (↥P ⧸ frattini ↥P) := Y₀.map (QuotientGroup.mk' (frattini ↥P))
  have hTinv : ∀ h : ↥H, ∀ v ∈ T, h • v ∈ T := by
    rintro h _ ⟨y, hy, rfl⟩
    refine ⟨h • y, ?_, rfl⟩
    show ((h • y : ↥P) : G) ∈ Y
    exact (Subgroup.mem_normalizer_iff.mp (hHY h.2) y).mp ((hY₀ y).mp hy)
  rcases hirr T hTinv with h0 | h1
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h0
    refine le_antisymm (fun g hg => ?_) hΦY
    exact (hmemΦ ⟨g, hYP hg⟩).mpr (h0 hg)
  · right
    refine le_antisymm hYP (fun g hg => ?_)
    have hv : (QuotientGroup.mk' (frattini ↥P)) ⟨g, hg⟩ ∈ T := by rw [h1]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyg⟩ := hv
    have h2 : y⁻¹ * ⟨g, hg⟩ ∈ frattini ↥P := QuotientGroup.eq.mp hyg
    have h3 : (((y⁻¹ * ⟨g, hg⟩ : ↥P)) : G) ∈ Y := hΦY ((hmemΦ _).mpr h2)
    have h4 : g = (y : G) * (((y⁻¹ * ⟨g, hg⟩ : ↥P)) : G) := by simp
    rw [h4]
    exact Y.mul_mem ((hY₀ y).mp hy) h3

theorem fixed_map_eq_quot {R A X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (r : ↥R) :
    letI C := Compat.ofSubgroups hAR hRX hAX
    letI : MulDistribMulAction C.Q ↥X := MulDistribMulAction.compHom ↥X C.fS
    (fixedPointSubgroup (Subgroup.zpowers (r : C.Q)) ↥X).map X.subtype =
      X ⊓ Subgroup.centralizer ({(r : G)} : Set G) := by
  let C := Compat.ofSubgroups hAR hRX hAX
  let _ : MulDistribMulAction C.Q ↥X := MulDistribMulAction.compHom ↥X C.fS
  have hfix : ∀ x : ↥X, x ∈ fixedPointSubgroup (Subgroup.zpowers (r : C.Q)) ↥X ↔
      (r : G) * x = x * (r : G) := by
    intro x
    rw [mem_fixedPointSubgroup_zpowers_iff]
    constructor
    · intro h
      have h1 := congrArg (fun y : ↥X => (y : G)) h
      change (r : G) * x * (r : G)⁻¹ = x at h1
      calc (r : G) * x = ((r : G) * x * (r : G)⁻¹) * r := by group
        _ = x * r := by rw [h1]
    · intro h
      apply Subtype.ext
      change (r : G) * x * (r : G)⁻¹ = x
      calc (r : G) * x * (r : G)⁻¹ = (x * r) * (r : G)⁻¹ := by rw [h]
        _ = x := by group
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ({(r : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hfix x).mp hx).symm
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hgX⟩, (hfix ⟨g, hgX⟩).mpr ?_, rfl⟩
    have hgC' : g ∈ Subgroup.centralizer ({(r : G)} : Set G) := hgC
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC'
    exact hgC'.symm

end Aux

end Quotient36

theorem minimalTwoActionSmallFaithfulQuotient_of (h32 : ExtraspecialThirtyTwoFiveRecognition) :
    MinimalTwoActionSmallFaithfulQuotient := by
  intro G _ _ p q A D R hset hrk
  classical
  obtain ⟨hp, hq, hp3, hq2, hpq, hAel, hAcard, hLD, hDq, hDexp, hDcl, hR2, hAR, hRA, hRne, hact,
    hRmin⟩ := hset
  have hAord : ¬ q ∣ Nat.card A := by
    rw [hAcard]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm
  obtain ⟨X, hXD, hLX, hcommX, hirrX, hXfrat, hnoC⟩ :=
    exists_realization hq hq2 hR2 hAord hAR hLD hDq hact
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_left hLX
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_right hLX
  let C := Compat.ofSubgroups hAR hRX hAX
  have hq1 : 1 < q := hq.one_lt
  have hXq : IsPGroup q ↥X := hDq.of_injective (Subgroup.inclusion hXD)
    (Subgroup.inclusion_injective hXD)
  have hXexp : ∀ x : ↥X, x ^ q = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hDexp x (hXD x.2))
  have hXcl : commutator ↥X ≤ Subgroup.center ↥X := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ = 1 := by
      have : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ ∈ ⁅⁅D, D⁆, D⁆ :=
        Subgroup.commutator_mem_commutator
          (Subgroup.commutator_mem_commutator (hXD a.2) (hXD b.2)) (hXD z.2)
      rw [hDcl, Subgroup.mem_bot] at this
      exact this
    apply Subtype.ext
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    have e : ((⁅a, b⁆ : ↥X) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, e]
    exact h2.symm
  let _ : MulDistribMulAction ↥R ↥X := MulDistribMulAction.compHom ↥X C.fR
  let _ : MulDistribMulAction ↥A ↥X := MulDistribMulAction.compHom ↥X C.fA
  let _ : MulDistribMulAction ↥A ↥R := MulDistribMulAction.compHom ↥R (Subgroup.inclusion hAR)
  have hψ : ∀ (a : ↥A) (r : ↥R), a • r = C.ψ a r := fun _ _ => rfl
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q ↥X) := ⟨hXq⟩
  let ρR : Representation (ZMod q) ↥R (Additive (↥X ⧸ frattini ↥X)) :=
    frattiniRep (E := ↥R) (X := ↥X) q
  let ρA : Representation (ZMod q) ↥A (Additive (↥X ⧸ frattini ↥X)) :=
    frattiniRep (E := ↥A) (X := ↥X) q
  have hρR : ∀ (r : ↥R) (x : ↥X), ρR r (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) =
      Additive.ofMul ((C.fR r x : ↥X) : ↥X ⧸ frattini ↥X) := fun r x =>
    frattiniRep_apply_mk (E := ↥R) (X := ↥X) q r x
  have hρA : ∀ (a : ↥A) (x : ↥X), ρA a (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) =
      Additive.ofMul ((C.fA a x : ↥X) : ↥X ⧸ frattini ↥X) := fun a x =>
    frattiniRep_apply_mk (E := ↥A) (X := ↥X) q a x
  have hcompat : ∀ (a : ↥A) (r : ↥R), ρA a * ρR r = ρR (a • r) * ρA a := by
    intro a r
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [Module.End.mul_apply]
    rw [hρR, hρA, hρA, hρR]
    have h := congrArg (fun f : MulAut ↥X => f (C.fA a x)) (C.compat a r)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h
    exact congrArg (fun y : ↥X => Additive.ofMul (y : ↥X ⧸ frattini ↥X)) h
  have hker : ∀ r : ↥R, r ∈ C.fR.ker ↔ (r : G) ∈ Subgroup.centralizer (X : Set G) :=
    fun r => mem_ker_conjHom hRX r
  have hRord : ∀ r : ↥R, ¬ q ∣ orderOf r := by
    intro r hdvd
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
    have h1 : q ∣ 2 ^ a := ha ▸ hdvd.trans (orderOf_dvd_natCard r)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1))
  have hK : ∀ r : ↥R, r ∈ C.fR.ker ↔ ρR r = 1 := by
    intro r
    constructor
    · intro h
      refine LinearMap.ext fun w => ?_
      obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      rw [hρR, Module.End.one_apply]
      have : C.fR r x = x := congrArg (fun f : MulAut ↥X => f x) (MonoidHom.mem_ker.mp h)
      rw [this]
    · intro h
      have htriv : ∀ x : ↥X, (((r • x : ↥X)) : ↥X ⧸ frattini ↥X) = (x : ↥X ⧸ frattini ↥X) := by
        intro x
        have h1 := congrArg (fun f : Module.End (ZMod q) (Additive (↥X ⧸ frattini ↥X)) =>
          f (Additive.ofMul (x : ↥X ⧸ frattini ↥X))) h
        simp only [hρR, Module.End.one_apply] at h1
        exact Additive.ofMul.injective h1
      exact MonoidHom.mem_ker.mpr (MulEquiv.ext (smul_eq_of_smul_mk_eq hXq r (hRord r) htriv))
  have hinv : CFSG.IsInvariant ↥A ↥R C.fR.ker := by
    refine ⟨fun a g => ⟨fun hg => C.ker_invariant a g hg, fun hg => ?_⟩⟩
    have h1 := C.ker_invariant a⁻¹ _ hg
    have e : C.ψ a⁻¹ (a • g) = g := by
      change C.ψ a⁻¹ (C.ψ a g) = g
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rwa [e] at h1
  have hKtop : C.fR.ker ≠ ⊤ := by
    intro h
    apply hnoC
    intro g hg
    have : (⟨g, hg⟩ : ↥R) ∈ C.fR.ker := h ▸ Subgroup.mem_top _
    exact (hker _).mp this
  have hRA' : actionCommutator ↥A (⊤ : Subgroup ↥R) = ⊤ := by
    have h1 := SteinbergBM.map_actionCommutator_conj hAR (⊤ : Subgroup ↥R)
    rw [Subgroup.map_top, Subgroup.range_subtype, hRA] at h1
    have h2 : (actionCommutator ↥A (⊤ : Subgroup ↥R)).map R.subtype =
        (⊤ : Subgroup ↥R).map R.subtype := by
      rw [h1, Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective R.subtype_injective h2
  have hmin' : ∀ U : Subgroup ↥R, U < ⊤ → (∀ a : ↥A, ∀ x ∈ U, a • x ∈ U) →
      actionCommutator ↥A U = U → U ≤ C.fR.ker := by
    intro U hUlt hUinv hUcomm
    let Y : Subgroup G := U.map R.subtype
    have hYR : Y ≤ R := Subgroup.map_subtype_le U
    have hYlt : Y < R := by
      refine lt_of_le_of_ne hYR (fun h => ?_)
      apply hUlt.ne
      have : U.map R.subtype = (⊤ : Subgroup ↥R).map R.subtype := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
        exact h
      exact Subgroup.map_injective R.subtype_injective this
    have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
      refine le_normalizer_of_conj_mem fun a ha g hg => ?_
      obtain ⟨u, hu, rfl⟩ := hg
      exact ⟨(⟨a, ha⟩ : ↥A) • u, hUinv ⟨a, ha⟩ u hu, rfl⟩
    have hcommY : ⁅Y, A⁆ = Y := by
      have h1 := SteinbergBM.map_actionCommutator_conj hAR U
      rw [hUcomm] at h1
      exact h1.symm
    have hYC := hRmin Y hYlt hAY hcommY
    intro u hu
    rw [hker]
    have h1 : (u : G) ∈ Subgroup.centralizer (D : Set G) := hYC ⟨u, hu, rfl⟩
    exact Subgroup.centralizer_le (fun x hx => hXD hx) h1
  have hntW : Nontrivial (Additive (↥X ⧸ frattini ↥X)) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hsub : Subsingleton (↥X ⧸ frattini ↥X) :=
      ⟨fun a b => Additive.ofMul.injective (Subsingleton.elim _ _)⟩
    have hbt : (⊥ : Subgroup (↥X ⧸ frattini ↥X)) = ⊤ := Subsingleton.elim _ _
    have h1 := (liftSub_eq_frattini_iff (X := X) ⊥).mpr rfl
    have h2 := (liftSub_eq_top_iff (X := X) ⊤).mpr rfl
    rw [hbt] at h1
    exact hirrX.2.1.ne (h1.symm.trans h2)
  have hirr : ∀ U : Submodule (ZMod q) (Additive (↥X ⧸ frattini ↥X)),
      (∀ r : ↥R, ∀ w ∈ U, ρR r w ∈ U) → (∀ a : ↥A, ∀ w ∈ U, ρA a w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hUR hUA
    let T := toSubgroup q U
    have hTR : ∀ r : ↥R, ∀ x : ↥X, (x : ↥X ⧸ frattini ↥X) ∈ T →
        ((conjHom hRX r x : ↥X) : ↥X ⧸ frattini ↥X) ∈ T := by
      intro r x hx
      have h1 := hUR r (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) hx
      rw [hρR] at h1
      exact h1
    have hTA : ∀ a : ↥A, ∀ x : ↥X, (x : ↥X ⧸ frattini ↥X) ∈ T →
        ((conjHom hAX a x : ↥X) : ↥X ⧸ frattini ↥X) ∈ T := by
      intro a x hx
      have h1 := hUA a (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) hx
      rw [hρA] at h1
      exact h1
    have hnorm : R ⊔ A ≤ Subgroup.normalizer (liftSub X T : Set G) :=
      sup_le (le_normalizer_liftSub hRX T hTR) (le_normalizer_liftSub hAX T hTA)
    rcases hirrX.2.2 _ (frattini_le_liftSub T) (liftSub_le T) hnorm with h0 | h1
    · exact Or.inl ((toSubgroup_eq_bot_iff q U).mp ((liftSub_eq_frattini_iff T).mp h0))
    · exact Or.inr ((toSubgroup_eq_top_iff q U).mp ((liftSub_eq_top_iff T).mp h1))
  have hA2 : ¬ 2 ∣ Nat.card ↥A := by
    rw [hAcard]
    intro h
    have h1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)
    omega
  have hk : (2 : ZMod q) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1)
  have := hntW
  obtain ⟨hKΦ, hnt0, ⟨hnt1, hcent, hshape, hFfix, hkerS, hkerSΦ⟩, hlast⟩ :=
    irreducibleRelativeMinimalTwoActionQuotient (R := ↥R) (A := ↥A) (k := ZMod q)
      (W := Additive (↥X ⧸ frattini ↥X)) hR2 hA2 hk ρR ρA hcompat hirr C.fR.ker hK hinv hKtop
      hRA' hmin'
  have hS2 : IsPGroup 2 C.Q := hR2.to_quotient _
  let _ : MulDistribMulAction ↥A C.Q := quotientMulDistribMulAction C.fR.ker hinv
  let _ : MulDistribMulAction C.Q ↥X := MulDistribMulAction.compHom ↥X C.fS
  have : FaithfulSMul C.Q ↥X := ⟨fun {a b} h => C.fS_injective (MulEquiv.ext h)⟩
  have hne1 : ∀ r : ↥R, (r : C.Q) ≠ 1 → (r : G) ≠ 1 := by
    intro r hr h1
    apply hr
    have : r = 1 := Subtype.ext h1
    rw [this]
    rfl
  have hrankS : ∀ s : C.Q, s ≠ 1 →
      CFSG.pRank q ↥(fixedPointSubgroup (Subgroup.zpowers s) ↥X) ≤ 3 := by
    intro s hs
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    rw [← pRank_map_subtype hq1, fixed_map_eq_quot hAR hRX hAX r]
    exact (pRank_mono_subgroup hq1 (inf_le_inf_right _ hXD)).trans (hrk r r.2 (hne1 r hs))
  have : IsElementaryAbelian p ↥A := hAel
  have hshp := small_faithful_quotient_shape (smallExtraspecialOddActionRecognition_of h32) hp hq
    hp3 hq2 hXq hXexp hXcl hS2 hrankS hAcard hshape hnt1
  obtain ⟨hshape3, hrange, hkercard, hkerS'⟩ := hshp
  have hKsub : (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R = C.fR.ker := by
    ext r
    rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨r.2, h⟩⟩
  have hmk : ∀ (a : ↥A) (r : ↥R) (N : Subgroup ↥R) [N.Normal],
      ((a • r : ↥R) : ↥R ⧸ N) = (r : ↥R ⧸ N) ↔ (a • r) * r⁻¹ ∈ N := fun a r N _ => by
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  have hcoe : ∀ (a : ↥A) (r : ↥R), ((((a • r) * r⁻¹ : ↥R)) : G) = ⁅(a : G), (r : G)⁆ := by
    intro a r
    rw [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rfl
  have hsmulR : ∀ (a : ↥A) (r : ↥R), ((a • r : ↥R) : G) = (a : G) * r * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hmemΦR : ∀ y : ↥R, (y : G) ∈ inSubgroup frattini R ↔ y ∈ frattini ↥R := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      subst this
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hcentC : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (R : Set G) ↔ ∀ r : ↥R, a • r = r := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h r
      apply Subtype.ext
      rw [hsmulR]
      have h1 := h (r : G) r.2
      calc (a : G) * r * (a : G)⁻¹ = (r * a) * (a : G)⁻¹ := by rw [← h1]
        _ = r := by group
    · intro h g hg
      have h1 := congrArg (fun y : ↥R => (y : G)) (h ⟨g, hg⟩)
      change (a : G) * g * (a : G)⁻¹ = g at h1
      calc g * (a : G) = ((a : G) * g * (a : G)⁻¹) * a := by rw [h1]
        _ = a * g := by group
  refine ⟨X, hXD, hcommX, hirrX, hXfrat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    have h1 : (⟨g, hg.1⟩ : ↥R) ∈ C.fR.ker := (hker _).mpr hg.2
    exact (hmemΦR _).mpr (hKΦ h1)
  ·
    obtain ⟨a, v, hav⟩ := hnt0.1
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨a, a.2, r, r.2, fun h => hav ?_⟩
    have h1 : (a • r) * r⁻¹ ∈ frattini ↥R := by
      have := (hmemΦR ((a • r) * r⁻¹)).mp (by rw [hcoe]; exact h)
      exact this
    exact (hmk a r (frattini ↥R)).mpr h1
  ·
    intro Y hΦY hYR hAY
    exact eq_frattini_or_eq_of_irreducible hAR hnt0.2 Y hΦY hYR hAY
  ·
    intro a ha g hg
    obtain ⟨ρ, hρ, rfl⟩ := hg
    have h1 : (QuotientGroup.mk' C.fR.ker) ρ ∈ frattini C.Q :=
      frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective _) hρ
    have h2 := hFfix ⟨a, ha⟩ _ h1
    have h3 : ((⟨a, ha⟩ : ↥A) • ρ) * ρ⁻¹ ∈ C.fR.ker :=
      (hmk ⟨a, ha⟩ ρ C.fR.ker).mp h2
    have h4 := (hker _).mp h3
    have e := hcoe ⟨a, ha⟩ ρ
    have hgoal : ⁅(a : G), ((ρ : ↥R) : G)⁆ ∈ R ⊓ Subgroup.centralizer (X : Set G) := by
      rw [show (a : G) = ((⟨a, ha⟩ : ↥A) : G) from rfl, ← e]
      exact ⟨(((⟨a, ha⟩ : ↥A) • ρ) * ρ⁻¹).2, h4⟩
    exact hgoal
  ·
    rcases hshape3 with ⟨hel, hord⟩ | ⟨hext, hp5, ⟨e⟩⟩
    · have hcomm' : ⁅R, R⁆ ≤ R ⊓ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hmem : ⁅(⟨g₁, hg₁⟩ : ↥R), (⟨g₂, hg₂⟩ : ↥R)⁆ ∈ C.fR.ker := by
          rw [← QuotientGroup.eq_one_iff]
          have h1 := map_commutatorElement (QuotientGroup.mk' C.fR.ker) (⟨g₁, hg₁⟩ : ↥R)
            (⟨g₂, hg₂⟩ : ↥R)
          refine h1.trans ?_
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hel.toIsMulCommutative.is_comm.comm _ _)
        have h2 := (hker _).mp hmem
        have e1 : ((⁅(⟨g₁, hg₁⟩ : ↥R), (⟨g₂, hg₂⟩ : ↥R)⁆ : ↥R) : G) = ⁅g₁, g₂⁆ := by
          simp [commutatorElement_def]
        rw [e1] at h2
        exact ⟨R.mul_mem (R.mul_mem (R.mul_mem hg₁ hg₂) (R.inv_mem hg₁)) (R.inv_mem hg₂), h2⟩
      have hsq : ∀ r ∈ R, r ^ 2 ∈ R ⊓ Subgroup.centralizer (X : Set G) := by
        intro r hr
        refine ⟨R.pow_mem hr 2, ?_⟩
        have h1 : ((⟨r, hr⟩ : ↥R) : C.Q) ^ 2 = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p _
        have h2 : (⟨r, hr⟩ : ↥R) ^ 2 ∈ C.fR.ker := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
          exact h1
        have h3 := (hker _).mp h2
        rwa [Subgroup.coe_pow] at h3
      have hrel : (R ⊓ Subgroup.centralizer (X : Set G)).relIndex R = Nat.card C.Q := by
        rw [Subgroup.relIndex, hKsub]
        rfl
      rcases hord with ⟨h7, h8⟩ | ⟨h5, h16⟩
      · exact Or.inl ⟨h7, hcomm', hsq, hrel.trans h8⟩
      · exact Or.inr (Or.inl ⟨h5, hcomm', hsq, hrel.trans h16⟩)
    · refine Or.inr (Or.inr ⟨hp5, (e : C.Q ≃* CFSG.RankThree.GroupTheory.QD32).toMonoidHom.comp
        (QuotientGroup.mk' C.fR.ker), ?_, ?_⟩)
      · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      · rw [hKsub]
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        constructor
        · intro h
          have : (QuotientGroup.mk' C.fR.ker) x = 1 := e.injective (by rw [map_one]; exact h)
          exact (QuotientGroup.eq_one_iff x).mp this
        · intro h
          have : (QuotientGroup.mk' C.fR.ker) x = 1 := (QuotientGroup.eq_one_iff x).mpr h
          rw [this, map_one]
  ·
    have hkereq : (MulDistribMulAction.toMulAut ↥A C.Q).ker =
        (A ⊓ Subgroup.centralizer (R : Set G)).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        refine ⟨a.2, (hcentC a).mpr ((hkerS a).mpr fun s => ?_)⟩
        exact congrArg (fun f : MulAut C.Q => f s) h
      · rintro ⟨-, h⟩
        refine MulEquiv.ext fun s => ?_
        exact ((hkerS a).mp ((hcentC a).mp h)) s
    rw [hkereq] at hkercard
    rw [← hkercard]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : A ⊓ Subgroup.centralizer (R : Set G) ≤ A)).toEquiv).symm
  · intro a ha h
    refine (hcentC ⟨a, ha⟩).mpr ((hkerS ⟨a, ha⟩).mpr fun s => ?_)
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    have h1 := (h r r.2).2
    have h2 : ((⟨a, ha⟩ : ↥A) • r) * r⁻¹ ∈ C.fR.ker := by
      rw [hker, hcoe]
      exact h1
    exact (hmk _ r C.fR.ker).mpr h2
  · intro a ha h
    refine (hcentC ⟨a, ha⟩).mpr (hlast ⟨a, ha⟩ fun v => ?_)
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective v
    have h2 : ((⟨a, ha⟩ : ↥A) • r) * r⁻¹ ∈ frattini ↥R := by
      rw [← hmemΦR, hcoe]
      exact h r r.2
    exact (hmk _ r (frattini ↥R)).mpr h2
  · intro r hr hrK
    have hr1 : r ≠ 1 := fun h => hrK (h ▸ (R ⊓ Subgroup.centralizer (X : Set G)).one_mem)
    exact (pRank_mono_subgroup hq1 (inf_le_inf_right _ hXD)).trans (hrk r hr hr1)

end CFSG.RankThree.PartOne
