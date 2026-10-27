module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup)
open scoped commutatorElement

@[expose] def K423TypeCAlpha : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], PiField π p f K → ModThree π (p ^ f) →
  ∀ (e : X ≃* projImage (slPi π 3 (p ^ f) K)) (D : Subgroup (GL (Fin 3) K)),
    IsTypeC π (p ^ f) K D →
  ∀ B Y : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ Y → B ≤ Y →
    (∀ τ ∈ B, ∃ y ∈ D, ∀ z : X, ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) →
    (∀ y ∈ D, ∃ τ ∈ B, ∀ z : X, ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) →
    thetaAlpha 3 (B.subgroupOf Y) = ⊥

@[expose] def K423TypeCAlphaSL : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], PiField π p f K → ModThree π (p ^ f) →
  ∀ (e : X ≃* slPi π 3 (p ^ f) K) (D : Subgroup (GL (Fin 3) K)), IsTypeC π (p ^ f) K D →
  ∀ B Y : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ Y → B ≤ Y →
    (∀ τ ∈ B, ∃ y ∈ D, ∀ z : X, ((e (τ z) : GL (Fin 3) K)) = y * (e z : GL (Fin 3) K) * y⁻¹) →
    (∀ y ∈ D, ∃ τ ∈ B, ∀ z : X, ((e (τ z) : GL (Fin 3) K)) = y * (e z : GL (Fin 3) K) * y⁻¹) →
    thetaAlpha 3 (B.subgroupOf Y) = ⊥

@[expose] def K423L3HeisFrame : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal] (π : Bool) (p f : ℕ)
    (K : Type) [Field K], IsQuasisimple L → PiField π p f K → ModThree π (p ^ f) → 2 < p ^ f →
  ∀ (e : L ≃* projImage (slPi π 3 (p ^ f) K)) (A : Subgroup H) (c : H),
    Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
    (∀ a ∈ A, ∃ y, IsPGLAtP e a y) →
    A ⊔ L = Subgroup.zpowers c ⊔ L →
    (∀ x ∈ A ⊓ L, x ≠ 1 → InducesTypeOn L x 1) →
    (∀ x ∈ A ⊓ L, x ≠ 1 → ∀ y ∈ A ⊓ L, y ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup H) : Set H), n * x * n⁻¹ = y) →
      Nonempty (autIn L A ≃* QuaternionGroup 2) ∨
        Nonempty (autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

@[expose] def K423L3TypeThreeFrame : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal] (π : Bool) (p f : ℕ)
    (K : Type) [Field K], IsQuasisimple L → PiField π p f K → ModThree π (p ^ f) →
  ∀ (e : L ≃* projImage (slPi π 3 (p ^ f) K)) (A : Subgroup H) (c : H),
    Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
    (∀ a ∈ A, ∃ y, IsPGLAtP e a y) →
    (∃ x₁ ∈ A, ∃ x₂ ∈ A, ∃ (y₁ y₂ : GL (Fin 3) K) (ζ : Kˣ), IsPGLAtP e x₁ y₁ ∧
      IsPGLAtP e x₂ y₂ ∧ ζ ≠ 1 ∧
        y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂) →
    (∃ b : H, A ⊓ L = Subgroup.zpowers b ∧ orderOf b = 3) →
      Sec8.IsZ3PGLThreePi ↥(A ⊔ L) ∧ Nonempty (autIn L A ≃* Multiplicative (ZMod 3))

@[expose] def K423SL3TypeThreeFrame : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) [L.Normal] (π : Bool) (p f : ℕ)
    (K : Type) [Field K], IsQuasisimple L → PiField π p f K → ModThree π (p ^ f) → 2 < p ^ f →
  ∀ (e : L ≃* slPi π 3 (p ^ f) K) (A : Subgroup H) (c : H),
    Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c →
    (∀ a ∈ A, ∃ y, IsPGLAt e a y) →
    IsSLThreePiTwo ↥(A ⊔ L) →
    (∃ a ∈ A, InducesTypeOnSL L a 3 ∧
      ∃ u v : H, u ∈ Subgroup.centralizer (L : Set H) ∧ u ∉ L ∧ v ∈ L ∧
        v ∉ Subgroup.centralizer (L : Set H) ∧ orderOf u = 3 ∧ orderOf v = 3 ∧
        A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) = Subgroup.closure {c, u * v} ∧
        A ⊔ L = L ⊔ Subgroup.closure {u, a} ∧ u * a * u⁻¹ * a⁻¹ = c) →
      Nonempty (autIn L A ≃* Multiplicative (ZMod 3))

namespace Res423Four

open Sec21.Item211Proof

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G}

theorem nonempty_quotX_equiv_thetaImage (hLsn : L.IsSubnormal) (hA : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    Nonempty (QuotX L A ≃* ↥(thetaImage (L ⊔ A))) := by
  set N := aschbacherSolvableCore 3 G with hN
  set f : ↥(L ⊔ A) →* G ⧸ N := (QuotientGroup.mk' N).comp (L ⊔ A).subtype with hf
  have hrange : f.range = thetaImage (L ⊔ A) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hθ := inSubgroup_theta_sup hA hAL
  have hθL := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hLsn
  have hker : f.ker = aschbacherSolvableCore 3 ↥(L ⊔ A) := by
    ext x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have h1 : (x : G) ∈ (L ⊔ A) ⊓ inSubgroup (aschbacherSolvableCore 3) (⊤ : Subgroup G) := by
        rw [inSubgroup_aschbacherSolvableCore_top Nat.prime_three]
        exact ⟨x.2, hx⟩
      obtain ⟨y, hy, hyx⟩ := Sec13.inf_inSubgroup_theta_le le_top h1
      rwa [show y = x from Subtype.ext hyx] at hy
    · intro hx
      have h1 : (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) := ⟨x, hx, rfl⟩
      rw [hθ, hθL] at h1
      exact h1.2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))⟩

omit [Finite G] in
theorem aOne_sup_lOne : aOne L A ⊔ lOne L A = ⊤ := by
  have h1 : A.subgroupOf (L ⊔ A) ⊔ L.subgroupOf (L ⊔ A) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_right le_sup_left, Subgroup.subgroupOf_eq_top]
    exact (sup_comm L A).le
  rw [aOne, lOne, ← Subgroup.map_sup, h1]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem nonempty_sup_equiv_thetaImage (hLsn : L.IsSubnormal) (hA : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    Nonempty (↥(aOne L A ⊔ lOne L A) ≃* ↥(thetaImage (L ⊔ A))) := by
  obtain ⟨φ⟩ := nonempty_quotX_equiv_thetaImage hLsn hA hAL
  exact ⟨((MulEquiv.subgroupCongr aOne_sup_lOne).trans Subgroup.topEquiv).trans φ⟩

theorem nonempty_autIn_lOne_equiv' (hA : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    Nonempty (autIn (lOne L A) (aOne L A) ≃* autIn L A) := by
  obtain ⟨φ⟩ := nonempty_autIn_lOne_equiv hA hAL
  exact ⟨φ.trans (MulEquiv.subgroupCongr (autIn_eq_starOf A L).symm)⟩

theorem inducesTypeOn_of_lOne (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {Φ₀ : Sec21.lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : Sec21.lBar L) : QuotX L A) =
      piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) {k : ℕ}
    (h : InducesTypeOn (lOne L A) (piX L A ⟨a, Subgroup.mem_sup_right haA⟩) k) :
    InducesTypeOn L a k := by
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, hy, hyk, hconj⟩ := h
  refine ⟨hAL haA, π, p, f, K, inferInstance, hK, hq, (lEquivTheta Φ₀).trans e, y, hy, hyk,
    fun z => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, lEquivTheta_conj hΦ₀ haA (hAL haA) hx z]
  exact hconj _

end Res423Four

namespace Res423Four

theorem ne_one_of_inducesTypeOn_three {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLp : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L)) {x : G}
    (h : InducesTypeOn L x 3) : x ≠ 1 := by
  rintro rfl
  obtain ⟨hx, π, p, f, K, _, hK, hqK, e, y, hy, hy3, hconj⟩ := h
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hqK
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hqK
  have h1 : ∀ z, thetaQuotMulAut L (L.normalizerMonoidHom ⟨1, hx⟩) z = z := by
    intro z
    rw [show (⟨1, hx⟩ : Subgroup.normalizer (L : Set G)) = 1 from rfl, map_one, map_one]
    rfl
  have hys : y ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_comm_mod hK hqK fun s hs => ?_
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h2 := hconj (e.symm (projOf _ ⟨s, hs⟩))
    rw [h1, MulEquiv.apply_symm_apply, coe_projOf] at h2
    simp only [map_mul, map_inv]
    rw [← h2]
    group
  exact hy3.1 ((zPi_eq hπ hq' hτ hτ1) ▸ Subgroup.mem_inf.mpr ⟨hy, hys⟩)

theorem nonempty_zpowers_sup_equiv_prod {X : Type} [Group X] [Finite X] {L₁ : Subgroup X}
    [hLn : L₁.Normal] (hZ : Subgroup.center L₁ = ⊥) {c : X}
    (hc : c ∈ Subgroup.centralizer (L₁ : Set X)) (hc3 : orderOf c = 3) :
    Nonempty (↥(Subgroup.zpowers c ⊔ L₁) ≃* Multiplicative (ZMod 3) × L₁) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.zpowers c with hZdef
  have hZC : Z ≤ Subgroup.centralizer (L₁ : Set X) := Subgroup.zpowers_le.mpr hc
  have hcomm : ∀ (z : Z) (l : L₁), Commute (Z.subtype z) (L₁.subtype l) := fun z l =>
    (Subgroup.mem_centralizer_iff.mp (hZC z.2) l l.2).symm
  let F : Z × L₁ →* X := MonoidHom.noncommCoprod Z.subtype L₁.subtype hcomm
  have hF : ∀ y : Z × L₁, F y = (y.1 : X) * y.2 := fun y => rfl
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨z, l⟩ hzl
    rw [hF] at hzl
    have hlz : (l : X) = (z : X)⁻¹ := eq_inv_of_mul_eq_one_right hzl
    have hlC : (l : X) ∈ Subgroup.centralizer (L₁ : Set X) := by
      rw [hlz]
      exact inv_mem (hZC z.2)
    have hlZ : l ∈ Subgroup.center L₁ := by
      rw [Subgroup.mem_center_iff]
      intro m
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hlC m m.2)
    rw [hZ, Subgroup.mem_bot] at hlZ
    subst hlZ
    have hz : (z : X) = 1 := by simpa using hzl
    exact Prod.ext (Subtype.ext hz) rfl
  have hFr : F.range = Z ⊔ L₁ := by
    apply le_antisymm
    · rintro _ ⟨⟨z, l⟩, rfl⟩
      rw [hF]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left z.2) (Subgroup.mem_sup_right l.2)
    · intro x hx
      obtain ⟨z, hz, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      exact ⟨(⟨z, hz⟩, ⟨l, hl⟩), rfl⟩
  have hZ3 : Nat.card Z = 3 := by rw [hZdef, Nat.card_zpowers, hc3]
  have hC3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let eZ : Z ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hZ3 hC3
  exact ⟨(MulEquiv.subgroupCongr hFr.symm).trans ((MonoidHom.ofInjective hFinj).symm.trans
    (MulEquiv.prodCongr eZ (MulEquiv.refl _)))⟩

theorem autIn_of_isHeisCentral {X : Type} [Group X] [Finite X] {L₁ A₁ : Subgroup X}
    [hLn : L₁.Normal] (hLperf : Group.IsPerfect L₁) (hH : IsHeisCentral X L₁)
    (hmax : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) A₁)
    (hA27 : Nat.card A₁ = 27)
    (hAC : Nat.card (A₁ ⊓ Subgroup.centralizer (L₁ : Set X) : Subgroup X) = 3) :
    CFSG.Assembly.IsElemAbelian 3 (autIn L₁ A₁) ∧ Nat.card (autIn L₁ A₁) = 9 := by
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := hH
  have hZU : (Subgroup.center U).map U.subtype = U ⊓ V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rintro w ⟨hwU, hwV⟩
      refine ⟨⟨w, hwU⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
      exact hcomm u u.2 w hwV
    · rw [hcard, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  let ψ : U × V →* X := MonoidHom.noncommCoprod U.subtype V.subtype
    (fun u v => hcomm u u.2 v v.2)
  have hψapp : ∀ y : U × V, ψ y = (y.1 : X) * y.2 := fun y => rfl
  have hψ : ∀ x : X, ∃ y : U × V, ψ y = x := by
    have hrange : ψ.range = ⊤ := by
      rw [eq_top_iff, ← hUV, sup_le_iff]
      constructor
      · intro u hu
        exact ⟨(⟨u, hu⟩, 1), by rw [hψapp]; simp⟩
      · intro v hv
        exact ⟨(1, ⟨v, hv⟩), by rw [hψapp]; simp⟩
    intro x
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top x)
  have hcommV : commutator X ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨⟨u, v⟩, rfl⟩ := hψ x
    obtain ⟨⟨u', v'⟩, rfl⟩ := hψ y
    rw [← map_commutatorElement, hψapp]
    have h1 : ((⁅(u, v), (u', v')⁆ : U × V).1 : X) ∈ V := by
      have h2 : (⁅u, u'⁆ : U) ∈ commutator U :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hU.1.2.1] at h2
      have h3 : ((⁅u, u'⁆ : U) : X) ∈ (Subgroup.center U).map U.subtype := ⟨_, h2, rfl⟩
      rw [hZU] at h3
      exact h3.2
    exact V.mul_mem h1 (⁅(u, v), (u', v')⁆ : U × V).2.2
  have hLV : L₁ ≤ V := by
    have h1 : (⊤ : Subgroup L₁).map L₁.subtype = L₁ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc L₁ = (commutator L₁).map L₁.subtype := by
          rw [hLperf.commutator_eq_top, h1]
      _ = ⁅L₁, L₁⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator X := Subgroup.commutator_mono le_top le_top
      _ ≤ V := hcommV
  have hLVeq : L₁ = V :=
    Subgroup.eq_of_le_of_card_ge hLV (le_of_eq (Nat.card_congr eV.toEquiv))
  subst hLVeq
  exact Sec21.Item211Proof.autIn_heis hUV hcomm hU hcard hLn hmax.prop
    (fun B hB hAB => hmax.2 hB hAB) hA27 hAC

end Res423Four

open Res423Four Sec21.Item211Proof

section Main


theorem k423SLThree_of (h45 : Item4_5) (hC : K423TypeCAlpha) (hCSL : K423TypeCAlphaSL)
    (hH : K423L3HeisFrame) (h3 : K423L3TypeThreeFrame) (h3SL : K423SL3TypeThreeFrame) :
    K423SLThree := by
  intro G _ _ A L a h h9 hα hany h8
  have hAL := h.le_normalizer h45
  have hA : IsPGroup 3 A := h.isPGroup
  have hCA := h.inf_thetaQuotCentralizer hAL
  have hLsn : L.IsSubnormal := h.mem_thetaComponents.2.1
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hL₁n : (lOne L A).Normal := normal_lOne hAL
  have hLq : IsQuasisimple (lOne L A) :=
    LocalCores.isQuasisimple_of_mulEquiv Φ₀ h.isQuasisimple_L
  have : Group.IsPerfect (lOne L A) := hLq.1
  have hmax : Maximal (fun B : Subgroup (QuotX L A) => CFSG.Assembly.IsElemAbelian 3 B)
      (aOne L A) :=
    maximal_aOne h.isElemAbelian (fun B hB hAB => h.maximal.eq_of_ge hB hAB)
  have hA27 : Nat.card (aOne L A) = 27 := by
    rw [← Nat.card_congr (aEquiv (L := L) hA).toEquiv, h.card_eq]
  set c₁ : QuotX L A := piX L A ⟨a, Subgroup.mem_sup_right h.a_mem⟩ with hc₁def
  have hc₁ : orderOf c₁ = 3 := by
    have h1 : c₁ = ((aEquiv (L := L) hA ⟨a, h.a_mem⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact h.orderOf_a
  have hAc₁ : aOne L A ⊓ Subgroup.centralizer (lOne L A : Set (QuotX L A)) =
      Subgroup.zpowers c₁ := aOne_inf_centralizer hA hAL h.a_mem hCA
  have hnofield : ∀ x ∈ aOne L A, ¬ InducesStdKind (lOne L A) x .field := by
    intro x hx hk
    obtain ⟨a', ha', rfl⟩ := exists_eq_piX_of_mem_aOne hx
    have hk' := inducesStdKind_of_lOne hAL hΦ₀ ha' hk
    by_cases ha'1 : a' = 1
    · subst ha'1
      exact not_inducesStdKind_one_field L hk'
    · exact h8 a' ha' ha'1 (Or.inl hk')
  obtain ⟨eT⟩ := nonempty_sup_equiv_thetaImage hLsn hA hAL
  obtain ⟨eAut⟩ := nonempty_autIn_lOne_equiv' hA hAL
  have hle : autThetaQuot A L ≤ autThetaQuot ⊤ L := fun τ hτ => by
    obtain ⟨g, hg, -, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    exact mem_autThetaQuot_iff.mpr ⟨g, hg, Subgroup.mem_top g, rfl⟩
  have hInn := Config423.range_conj_le_autThetaQuot_top L
  have hcube : ∀ x ∈ aOne L A,
      (⟨x, mem_normalizer_of_normal x⟩ : Subgroup.normalizer (lOne L A : Set (QuotX L A))) ^ 3
        = 1 := fun x hx => Subtype.ext (by rw [Subgroup.coe_pow]; exact hmax.prop.2 x hx)
  rcases hany with hSL | ⟨p, e, hp, he, hiso⟩
  ·
    obtain ⟨π, p, f, K, _, hK, hq, hq2, ⟨e₁⟩⟩ :=
      exists_slPi_model (Sec13.isSLThreePi_of_mulEquiv Φ₀ hSL) hLq
    have hθ₁ := aschbacherSolvableCore_eq_bot_of_slPi hK hq hLq e₁
    have hpgl : ∀ x ∈ aOne L A, ∃ y, IsPGLAt e₁ x y := by
      intro x hx
      rcases slAct_pgl_or_field hK hq2 hθ₁ e₁ _ (hcube x hx) with ⟨y, hy, hys⟩ | ⟨hk, -⟩
      · exact ⟨y, hy, hys⟩
      · exact (hnofield x hx hk).elim
    rcases alt411_of_pgl hK hq e₁ hmax (by rw [hA27]) hc₁ hAc₁ hpgl with
      ⟨-, -, hTC⟩ | ⟨-, hHeis⟩ | ⟨-, hTwo, hrest⟩ | ⟨-, σ, hσ, hσk, -⟩ |
        ⟨-, σ, hσ, hσk, -⟩ | ⟨-, σ, hσ, hσk, -⟩
    ·
      exfalso
      obtain ⟨π', p', f', K', _, hK', hq', e', D, hD, hD1, hD2⟩ :=
        isTypeCOnBarSL_of_lOne hAL hΦ₀ hTC
      exact hα (hCSL _ h.isQuasisimple_L π' p' f' K' hK' hq' e' D hD _ _ hInn hle hD1 hD2)
    ·
      have hHX : IsHeisCentral (QuotX L A) (lOne L A) :=
        Sec13.isHeisCentral_of_mulEquiv
          ((MulEquiv.subgroupCongr Res423Four.aOne_sup_lOne).trans Subgroup.topEquiv)
          (MulEquiv.refl _) hHeis
      have hAC₁ : Nat.card (aOne L A ⊓ Subgroup.centralizer (lOne L A : Set (QuotX L A)) :
          Subgroup (QuotX L A)) = 3 := by rw [hAc₁, Nat.card_zpowers, hc₁]
      obtain ⟨hab, hcard9⟩ := autIn_of_isHeisCentral hLq.1 hHX hmax hA27 hAC₁
      refine Or.inr (Or.inr (Or.inl ⟨?_, Or.inr (Or.inr hSL),
        Sec21.Item211Proof.isElemAbelian_of_mulEquiv eAut hab,
        by rw [← Nat.card_congr eAut.toEquiv, hcard9]⟩))
      exact Sec13.isHeisCentral_of_mulEquiv eT Φ₀.symm hHeis
    ·
      obtain ⟨φ⟩ := h3SL _ _ π p f K hLq hK hq hq2 e₁ _ _ hmax hA27 hc₁ hAc₁ hpgl hTwo hrest
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Sec13.isSLThreePiTwo_of_mulEquiv eT hTwo,
        ⟨eAut.symm.trans φ⟩⟩)))
    · exact (hnofield σ hσ hσk).elim
    · exact (hnofield σ hσ hσk).elim
    · exact (hnofield σ hσ hσk).elim
  ·
    obtain ⟨π, K, _, hK, hq, hq2, ⟨e₁⟩⟩ :=
      exists_pslPi_model he (Sec21.Item211Proof.isoLThreePi_of_mulEquiv Φ₀ hiso) hLq
    have hθ₁ := aschbacherSolvableCore_eq_bot_proj hK hq hLq e₁
    have := isPerfect_projImage_of_equiv e₁
    have hpgl : ∀ x ∈ aOne L A, ∃ y, IsPGLAtP e₁ x y := by
      intro x hx
      rcases pslAct_pgl_or_field hK hq2 hθ₁ e₁ _ (hcube x hx) with ⟨y, hy, hys⟩ | ⟨hk, -⟩
      · exact ⟨y, hy, hys⟩
      · exact (hnofield x hx hk).elim
    rcases alt412_of_pgl hK hq hθ₁ e₁ hmax (by rw [hA27]) hc₁ hAc₁ hpgl with
      ⟨-, hsup, htype, htrans⟩ | ⟨-, hTC⟩ | ⟨-, hthree, hb⟩ | ⟨-, σ, hσ, hσk, -⟩
    ·
      have hZ₁ : Subgroup.center (lOne L A) = ⊥ := center_eq_bot_proj hK hq e₁
      have hc₁C : c₁ ∈ Subgroup.centralizer (lOne L A : Set (QuotX L A)) := by
        have : c₁ ∈ Subgroup.zpowers c₁ := Subgroup.mem_zpowers c₁
        rw [← hAc₁] at this
        exact this.2
      obtain ⟨eP⟩ := nonempty_zpowers_sup_equiv_prod hZ₁ hc₁C hc₁
      have hP : Sec8.IsZ3LThreePi ↥(thetaImage (L ⊔ A)) := by
        rcases hiso with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
        · exact ⟨p, e, hp, he, Or.inl ⟨hq3, ⟨eT.symm.trans ((MulEquiv.subgroupCongr hsup).trans
            (eP.trans (MulEquiv.prodCongr (MulEquiv.refl _) (Φ₀.symm.trans φ))))⟩⟩⟩
        · exact ⟨p, e, hp, he, Or.inr ⟨hq3, ⟨eT.symm.trans ((MulEquiv.subgroupCongr hsup).trans
            (eP.trans (MulEquiv.prodCongr (MulEquiv.refl _) (Φ₀.symm.trans φ))))⟩⟩⟩
      rcases hH _ _ π p e K hLq hK hq hq2 e₁ _ _ hmax hA27 hc₁ hAc₁ hpgl hsup htype htrans with
        ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact Or.inl ⟨hP, Or.inl ⟨eAut.symm.trans φ⟩⟩
      · exact Or.inl ⟨hP, Or.inr ⟨eAut.symm.trans φ⟩⟩
    ·
      exfalso
      obtain ⟨π', p', f', K', _, hK', hq', e', D, hD, hD1, hD2⟩ := isTypeCOn_of_lOne hAL hΦ₀ hTC
      exact hα (hC _ h.isQuasisimple_L π' p' f' K' hK' hq' e' D hD _ _ hInn hle hD1 hD2)
    ·
      have hA3₁ : ∀ x ∈ aOne L A, x ^ 3 = 1 := hmax.prop.2
      have hAcomm₁ : ∀ x ∈ aOne L A, ∀ y ∈ aOne L A, x * y = y * x := fun x hx y hy =>
        congrArg Subtype.val (hmax.prop.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      have hcardA := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hpgl)
      rw [hAc₁, Nat.card_zpowers, hc₁, hA27] at hcardA
      have hR9 : Nat.card (pglHomP hK hq (aOne L A) hpgl).range = 9 := by omega
      have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm₁
      have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpgl) hA3₁
      obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
      rcases frame_or_heis (hK.three_ne_zero hq) hτ hτ1 _ hRcomm hRexp (by rw [hR9]; norm_num) with
        ⟨bb, hbb, hd, -⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
      · exfalso
        have hTC := isTypeCOn_of_frameP hK hq hθ₁ hpgl hA3₁ hR9 hbb hd
        obtain ⟨π', p', f', K', _, hK', hq', e', D, hD, hD1, hD2⟩ :=
          isTypeCOn_of_lOne hAL hΦ₀ hTC
        exact hα (hC _ h.isQuasisimple_L π' p' f' K' hK' hq' e' D hD _ _ hInn hle hD1 hD2)
      obtain ⟨⟨x₁, hx₁⟩, hx₁y⟩ := hy₁
      obtain ⟨⟨x₂, hx₂⟩, hx₂y⟩ := hy₂
      obtain ⟨z₁, hz₁⟩ := hpgl x₁ hx₁
      obtain ⟨z₂, hz₂⟩ := hpgl x₂ hx₂
      have hm₁ : y₁⁻¹ * z₁ ∈ StatedScalars (Fin 3) K :=
        QuotientGroup.eq.mp (hx₁y.symm.trans (pglHomP_apply ⟨x₁, hx₁⟩ hz₁))
      have hm₂ : y₂⁻¹ * z₂ ∈ StatedScalars (Fin 3) K :=
        QuotientGroup.eq.mp (hx₂y.symm.trans (pglHomP_apply ⟨x₂, hx₂⟩ hz₂))
      have hheis := heis_of_mul_scalar hm₁ hm₂ hζ
      obtain ⟨b₁, hb₁A, hb₁3, -⟩ := hb
      obtain ⟨hP, ⟨φ⟩⟩ := h3 _ _ π p e K hLq hK hq e₁ _ _ hmax hA27 hc₁ hAc₁ hpgl
        ⟨x₁, hx₁, x₂, hx₂, z₁, z₂, ζ, hz₁, hz₂, hζ1, hheis⟩ ⟨b₁, hb₁A, hb₁3⟩
      obtain ⟨x, hx, hxT⟩ := hthree
      obtain ⟨a', ha', rfl⟩ := exists_eq_piX_of_mem_aOne hx
      have hT := inducesTypeOn_of_lOne hAL hΦ₀ ha' hxT
      exact Or.inr (Or.inl ⟨Sec13.isZ3PGLThreePi_of_mulEquiv eT hP, ⟨eAut.symm.trans φ⟩, a', ha',
        ne_one_of_inducesTypeOn_three h.isQuasisimple_L.1 hT, hT⟩)
    · exact (hnofield σ hσ hσk).elim

end Main

end CFSG.RankThree.PartTwo.Sec4
