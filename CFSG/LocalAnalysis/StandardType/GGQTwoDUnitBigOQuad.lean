module

public import CFSG.LocalAnalysis.StandardType.GGResOrthogonalExactTwo
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusHolds

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal (formOfRingEquiv formOfRingEquiv_apply
  nondegenerate_formOfRingEquiv)
open CFSG.GroupTheory.WeirSylow (IsPlusType)

private theorem plh_finrank_eq_of_carrier_eq {F V : Type} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [Finite V]
    (hFc : Nat.card F = Nat.card (ZMod 2)) {W : Submodule F V}
    {W₂ : Submodule (ZMod 2) V} (h : (W : Set V) = (W₂ : Set V)) :
    Module.finrank F W = Module.finrank (ZMod 2) W₂ := by
  haveI : Module.Finite F ↥W := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) ↥W₂ := Module.Finite.of_finite
  have h1 : Nat.card ↥W = Nat.card F ^ Module.finrank F W := Module.natCard_eq_pow_finrank
  have h2 : Nat.card ↥W₂ = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) W₂ :=
    Module.natCard_eq_pow_finrank
  have hc : Nat.card ↥W = Nat.card ↥W₂ :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Set.ext_iff.mp h x)
  rw [hc, hFc] at h1
  exact Nat.pow_right_injective (by rw [Nat.card_zmod]) (h1.symm.trans h2)

private theorem plh_isPlusType_formOfRingEquiv {F V : Type} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [Finite V]
    (e : ZMod 2 ≃+* F) (hsmul : ∀ (c : ZMod 2) (v : V), c • v = e c • v)
    (hFc : Nat.card F = Nat.card (ZMod 2))
    (hVdim : Module.finrank (ZMod 2) V = Module.finrank F V) (Q : QuadraticForm F V) :
    IsPlusType (formOfRingEquiv e hsmul Q) ↔ IsPlusType Q := by
  constructor
  · rintro ⟨W, hWdim, hW0⟩
    let W' : Submodule F V :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          have h := W.smul_mem (e.symm c) hv
          rwa [hsmul, RingEquiv.apply_symm_apply] at h }
    have hdimW : Module.finrank F W' = Module.finrank (ZMod 2) W :=
      plh_finrank_eq_of_carrier_eq hFc rfl
    refine ⟨W', ?_, fun x hx => ?_⟩
    · rw [hdimW, hWdim, hVdim]
    · have hx0 : formOfRingEquiv e hsmul Q x = 0 := hW0 x hx
      rw [formOfRingEquiv_apply] at hx0
      exact (map_eq_zero_iff e.symm e.symm.injective).1 hx0
  · rintro ⟨W, hWdim, hW0⟩
    let W₂ : Submodule (ZMod 2) V :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          have h := W.smul_mem (e c) hv
          rwa [← hsmul] at h }
    have hdimW : Module.finrank F W = Module.finrank (ZMod 2) W₂ :=
      plh_finrank_eq_of_carrier_eq hFc rfl
    refine ⟨W₂, ?_, fun x hx => ?_⟩
    · rw [← hdimW, hWdim, ← hVdim]
    · rw [formOfRingEquiv_apply, hW0 x hx, map_zero]


theorem qtwoDB43_quad (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {Bs N : Subgroup G} {m : ℕ} (hm : 6 ≤ m) (hmark : GGInnerDiagOn Bs N)
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (htag : lab = ⟨.D, m, 1⟩ ∨ lab = ⟨.twD, m, 1⟩) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : FiniteDimensional (ZMod 2) V)
      (Q : QuadraticForm (ZMod 2) V) (σ : ↥N ≃* ↥(orthDerived Q))
      (β : ↥Bs →* ↥(orthDerived Q)),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank (ZMod 2) V = 2 * m ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ lab = ⟨.D, m, 1⟩) ∧
      Subgroup.center ↥(orthDerived Q) = ⊥ ∧
      ∀ (s : ↥Bs) (n : ↥N), σ (ggGamma N hBsN s n) = β s * σ n * (β s)⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htag' : lab.tag = .D ∨ lab.tag = .twD := by
    rcases htag with h | h
    · left; rw [h]
    · right; rw [h]
  have hrank_eq : lab.rank = m := by
    rcases htag with h | h <;> rw [h]
  have hn : lab.n = 1 := by
    rcases htag with h | h <;> rw [h]
  have hrank : 4 ≤ lab.rank := by
    rw [hrank_eq]
    omega
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontriv, Q, hQ, eQ, ρ,
      hFcard, hchar, hU, hdim, hplus, hEQ, hconj⟩ :=
    CFSG.StandardType.OrthKExactTwo.exists_quadratic_image_of_orthogonal_marking
      hRig (by norm_num : (3 : ℕ) ≠ 2) hmark hBs hSC hΛ hlab htag' hrank
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  letI : Nontrivial V := hNontriv
  haveI : Group.IsPerfect ↥N := Group.isPerfect_def.mpr hmark.1
  have hrow : (lab.tag = .D ∧ 5 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank) := by
    rcases htag with h | h
    · rw [h]
      exact Or.inl ⟨rfl, by show 5 ≤ m; omega⟩
    · rw [h]
      exact Or.inr ⟨rfl, by show 4 ≤ m; omega⟩
  have hcenter : Subgroup.center ↥N = ⊥ :=
    CFSG.StandardType.OrthTorus.center_eq_bot_of_hasLabel_orth_two hrow hn hlab
  let ι : ↥N ≃* (↥N ⧸ Subgroup.center ↥N) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥N))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hcenter]),
        QuotientGroup.mk'_surjective (Subgroup.center ↥N)⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  have hF : Nat.card F = 2 := by
    rw [hFcard, hn]
    norm_num
  let e : ZMod 2 ≃+* F :=
    ZMod.ringEquivOfPrime F Nat.prime_two (by rwa [← Nat.card_eq_fintype_card])
  let modInst : Module (ZMod 2) V := Module.compHom V (e : ZMod 2 →+* F)
  letI : Module (ZMod 2) V := modInst
  have hsmul : ∀ (c : ZMod 2) (v : V), c • v = e c • v := fun _ _ => rfl
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hFc2 : Nat.card F = Nat.card (ZMod 2) := by rw [hF, Nat.card_zmod]
  have hdim2 : Module.finrank (ZMod 2) V = 2 * m := by
    have h1 : Nat.card V = Nat.card F ^ Module.finrank F V := Module.natCard_eq_pow_finrank
    have h2 : Nat.card V = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) V :=
      Module.natCard_eq_pow_finrank
    rw [hdim, hrank_eq, hFc2] at h1
    exact Nat.pow_right_injective (by rw [Nat.card_zmod]) (h2.symm.trans h1)
  have hVdim : Module.finrank (ZMod 2) V = Module.finrank F V := by
    rw [hdim2, hdim, hrank_eq]
  let Q' : QuadraticForm (ZMod 2) V := formOfRingEquiv e hsmul Q
  have hQ' : (QuadraticMap.polarBilin Q').Nondegenerate :=
    nondegenerate_formOfRingEquiv hQ
  have hplusQ' : IsPlusType Q' ↔ lab = ⟨.D, m, 1⟩ := by
    change IsPlusType (formOfRingEquiv e hsmul Q) ↔ lab = ⟨.D, m, 1⟩
    rw [plh_isPlusType_formOfRingEquiv e hsmul hFc2 hVdim Q]
    have hlabD : (lab = ⟨.D, m, 1⟩) ↔ lab.tag = .D := by
      rcases htag with h | h
      · rw [h]; simp
      · rw [h]; simp
    exact hplus.trans hlabD.symm
  let j := (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
  let σQ : (↥N ⧸ Subgroup.center ↥N) ≃* ↥(orthDerived Q) := eQ.trans j
  let iso : ↥(orthDerived Q') ≃* ↥(orthDerived Q) :=
    (CFSG.LocalAnalysis.GLTheoremA.T171S.nonempty_orthDerived_equiv_of_ringEquiv
      e hsmul Q).some
  let σ : ↥N ≃* ↥(orthDerived Q') := ι.trans (σQ.trans iso.symm)
  let β : ↥Bs →* ↥(orthDerived Q') := iso.symm.toMonoidHom.comp (σQ.toMonoidHom.comp ρ)
  have hcompat : ∀ (s : ↥Bs) (n : ↥N),
      σ (ggGamma N hBsN s n) = β s * σ n * (β s)⁻¹ := by
    intro s n
    have h1 : eQ (QuotientGroup.mk (ggGamma N (GGInnerDiagOn.le_normalizer hmark) s n)) =
        MulAut.conj (eQ (ρ s)) (eQ (QuotientGroup.mk n)) := hconj s n
    have hgg : ggGamma N (GGInnerDiagOn.le_normalizer hmark) s n =
        ggGamma N hBsN s n := Subtype.ext rfl
    rw [hgg] at h1
    have hι : ∀ x : ↥N, ι x = QuotientGroup.mk x :=
      fun x => QuotientGroup.mk'_apply (Subgroup.center ↥N) x
    have hconjQ : σQ (ι (ggGamma N hBsN s n)) =
        σQ (ρ s) * σQ (ι n) * (σQ (ρ s))⁻¹ := by
      have h1' : eQ (ι (ggGamma N hBsN s n)) =
          eQ (ρ s) * eQ (ι n) * (eQ (ρ s))⁻¹ := by
        rw [hι, hι, h1, MulAut.conj_apply]
      change j (eQ (ι (ggGamma N hBsN s n))) =
        j (eQ (ρ s)) * j (eQ (ι n)) * (j (eQ (ρ s)))⁻¹
      rw [show j (eQ (ρ s)) * j (eQ (ι n)) * (j (eQ (ρ s)))⁻¹ =
          j (eQ (ρ s) * eQ (ι n) * (eQ (ρ s))⁻¹) by
        simp only [map_mul, map_inv]]
      rw [h1']
    show iso.symm (σQ (ι (ggGamma N hBsN s n))) =
      iso.symm (σQ (ρ s)) * iso.symm (σQ (ι n)) * (iso.symm (σQ (ρ s)))⁻¹
    rw [show iso.symm (σQ (ρ s)) * iso.symm (σQ (ι n)) * (iso.symm (σQ (ρ s)))⁻¹ =
        iso.symm (σQ (ρ s) * σQ (ι n) * (σQ (ρ s))⁻¹) by
      simp only [map_mul, map_inv]]
    rw [hconjQ]
  have hcenterQ' : Subgroup.center ↥(orthDerived Q') = ⊥ := by
    apply le_antisymm
    · intro ω hω
      rw [Subgroup.mem_bot]
      have hmem : σ.symm ω ∈ Subgroup.center ↥N := by
        rw [Subgroup.mem_center_iff] at hω ⊢
        intro n
        apply σ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hω (σ n)
      have h2 : σ.symm ω ∈ (⊥ : Subgroup ↥N) := by rwa [hcenter] at hmem
      have h1 : σ.symm ω = 1 := by simpa using h2
      calc ω = σ (σ.symm ω) := (MulEquiv.apply_symm_apply σ ω).symm
        _ = σ 1 := by rw [h1]
        _ = 1 := map_one σ
    · exact bot_le
  exact ⟨V, hAdd, modInst, inferInstance, Q', σ, β, hQ', hdim2, hplusQ', hcenterQ',
    hcompat⟩

end CFSG.StandardType.QTwo

end
