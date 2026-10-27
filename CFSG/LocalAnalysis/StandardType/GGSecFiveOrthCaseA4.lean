module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthAInf
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyDim
public import CFSG.LocalAnalysis.StandardType.GGP3LineNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.Monster.B.TwoA.Base.SymFiveAut

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ct_a4_eigen {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {u : V} (hu : Q u ≠ 0) {r C : V →ₗ[ZMod 3] V}
    (hr : ∀ w, r w = w - (QuadraticMap.polar Q u w / Q u) • u) (hC : ∀ w, C (r w) = r (C w)) :
    C u = (2 * (QuadraticMap.polar Q u (C u) / Q u)) • u := by
  have hru : r u = -u := by
    have h0 : QuadraticMap.polar Q u u / Q u = 2 := by
      rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat, mul_div_assoc, div_self hu,
        mul_one]
    rw [hr, h0, two_smul]
    abel
  have h1 : C u - (QuadraticMap.polar Q u (C u) / Q u) • u = -C u := by
    rw [← hr, ← hC, hru, map_neg]
  have h2 : (QuadraticMap.polar Q u (C u) / Q u) • u = C u + C u := by
    have h3 : C u - (QuadraticMap.polar Q u (C u) / Q u) • u + C u = 0 :=
      eq_neg_iff_add_eq_zero.mp h1
    have h4 : (QuadraticMap.polar Q u (C u) / Q u) • u - (C u + C u) =
        -(C u - (QuadraticMap.polar Q u (C u) / Q u) • u + C u) := by abel
    exact sub_eq_zero.mp (by rw [h4, h3, neg_zero])
  have h5 : (2 + 2 : ZMod 3) = 1 := by decide
  rw [mul_smul, h2, smul_add, ← add_smul, h5, one_smul]

private lemma ct_a4_edge {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {u u' : V} (hu : Q u ≠ 0)
    (huu' : QuadraticMap.polar Q u u' ≠ 0) {r C : V →ₗ[ZMod 3] V}
    (hr : ∀ w, r w = w - (QuadraticMap.polar Q u w / Q u) • u) (hC : ∀ w, C (r w) = r (C w))
    {a b : ZMod 3} (ha : C u = a • u) (hb : C u' = b • u') : a = b := by
  have hu0 : u ≠ 0 := fun h => hu (by rw [h, map_zero])
  have h1 := hC u'
  rw [hr u', map_sub, map_smul, hb, ha, hr (b • u'), QuadraticMap.polar_smul_right,
    smul_eq_mul] at h1
  have h2 := sub_right_inj.mp h1
  rw [smul_smul] at h2
  have h3 := smul_left_injective (ZMod 3) hu0 h2
  rw [mul_div_assoc, mul_comm b] at h3
  exact mul_left_cancel₀ (div_ne_zero huu' hu) h3

private lemma ct_a4_scalar {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : Fin 4 → V} (hvQ : ∀ i, Q (v i) ≠ 0)
    (h01 : QuadraticMap.polar Q (v 0) (v 1) ≠ 0) (h12 : QuadraticMap.polar Q (v 1) (v 2) ≠ 0)
    (h23 : QuadraticMap.polar Q (v 2) (v 3) ≠ 0) {r : Fin 4 → V →ₗ[ZMod 3] V}
    (hr : ∀ i w, r i w = w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i)
    {C : V →ₗ[ZMod 3] V} (hC : ∀ i w, C (r i w) = r i (C w)) :
    ∀ i, C (v i) = (2 * (QuadraticMap.polar Q (v 0) (C (v 0)) / Q (v 0))) • v i := by
  have he : ∀ i, C (v i) = (2 * (QuadraticMap.polar Q (v i) (C (v i)) / Q (v i))) • v i :=
    fun i => ct_a4_eigen (hvQ i) (hr i) (hC i)
  have e01 := ct_a4_edge (hvQ 0) h01 (hr 0) (hC 0) (he 0) (he 1)
  have e12 := ct_a4_edge (hvQ 1) h12 (hr 1) (hC 1) (he 1) (he 2)
  have e23 := ct_a4_edge (hvQ 2) h23 (hr 2) (hC 2) (he 2) (he 3)
  intro i
  fin_cases i
  · exact he 0
  · rw [e01]; exact he 1
  · rw [e01, e12]; exact he 2
  · rw [e01, e12, e23]; exact he 3

theorem ggOrth_caseA4
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hFix : GGSecFiveFixInput) (hd : Module.finrank (ZMod 3) V = 5)
    (hA4 : GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs)) (hx : x ∈ Bs) (hQx : Q (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0) :
    False := by
  classical
  have : Finite V := Finite.of_equiv ↥Bs (Additive.ofMul.trans ι.toEquiv)
  have : FiniteDimensional (ZMod 3) V :=
    (Module.finite_iff_finite (R := ZMod 3) (M := V)).mpr inferInstance
  have : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  obtain ⟨E, -⟩ := exists_permEquiv_of_ggWeylOfType_A hA4
  have : Finite (MulAut ↥(ggAutomizer L Bs)) :=
    Finite.of_injective (fun φ : MulAut ↥(ggAutomizer L Bs) =>
      (φ : ↥(ggAutomizer L Bs) → ↥(ggAutomizer L Bs))) DFunLike.coe_injective
  have hAut : Nat.card (MulAut ↥(ggAutomizer L Bs)) ≤ 120 := by
    rw [← Nat.card_congr (MulAut.congr E).toEquiv]
    calc Nat.card (MulAut (Equiv.Perm (Fin 5))) ≤ Nat.card (Equiv.Perm (Fin 5)) :=
          Nat.card_le_card_of_surjective _ CFSG.Monster.B.TwoA.sym5_conj_surjective
      _ = 120 := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  obtain ⟨ε, hε⟩ := hA4
  obtain ⟨v, hvQ, hvr, -, hv3, hvfin, hx', -, hxperp⟩ :=
    ggOrthTy_roots S hFix (CoxeterMatrix.A 4) ε hε
  set w0 : V := ι (Additive.ofMul ⟨x, hx⟩) with hw0
  have hw0perp : ∀ i, QuadraticMap.polar Q (v i) w0 = 0 := hxperp
  have hspan : Submodule.span (ZMod 3) (Set.range v ∪ {w0}) = ⊤ := by
    set U := Submodule.span (ZMod 3) (Set.range v) with hU
    have hU4 : Module.finrank (ZMod 3) U = 4 := by omega
    have hw0U : w0 ∉ U := by
      intro hw
      have hperp : ∀ u ∈ U, QuadraticMap.polar Q u w0 = 0 := by
        intro u hu
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
        · rintro _ ⟨i, rfl⟩
          exact hw0perp i
        · exact QuadraticMap.polar_zero_left Q w0
        · intro a b _ _ ha hb
          rw [QuadraticMap.polar_add_left, ha, hb, add_zero]
        · intro c a _ ha
          rw [QuadraticMap.polar_smul_left, ha, smul_zero]
      have h := hperp w0 hw
      rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at h
      exact hQx ((mul_eq_zero.mp h).resolve_left (by decide))
    have hdisj : U ⊓ Submodule.span (ZMod 3) {w0} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      obtain ⟨hyU, hyw⟩ := Submodule.mem_inf.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyw
      by_contra hne
      have hc : c ≠ 0 := by
        rintro rfl
        exact hne (zero_smul _ _)
      apply hw0U
      have h := U.smul_mem c⁻¹ hyU
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
    have hw0ne : w0 ≠ 0 := fun h => hQx (by rw [h, map_zero])
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span (ZMod 3) {w0})
    rw [hdisj, finrank_bot, add_zero, hU4, finrank_span_singleton hw0ne] at hsum
    rw [Submodule.span_union, ← hU]
    exact Submodule.eq_top_of_finrank_eq (by omega)
  let St : Subgroup (MulAut ↥Bs) :=
    ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)
  have hStmem : ∀ φ : MulAut ↥Bs, φ ∈ St ↔ φ ∈ ggAutomizer ⊤ Bs ∧ φ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    fun φ => Iff.rfl
  have hcard_St : Nat.card {φ : ↥(ggAutomizer ⊤ Bs) // (φ : MulAut ↥Bs) ⟨x, hx⟩ = ⟨x, hx⟩} =
      Nat.card St :=
    Nat.card_congr
      { toFun := fun φ => ⟨φ.1.1, (hStmem _).mpr ⟨φ.1.2, φ.2⟩⟩
        invFun := fun φ => ⟨⟨φ.1, ((hStmem _).mp φ.2).1⟩, ((hStmem _).mp φ.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hStN : St ≤ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) := fun φ hφ =>
    ggAutomizer_fixes_mem_normalizer ggLNoncyclicInput_holds S.cfg.1.1 hx ((hStmem φ).mp hφ).1
      ((hStmem φ).mp hφ).2
  let f : ↥St →* MulAut ↥(ggAutomizer L Bs) :=
    (ggAutomizer L Bs).normalizerMonoidHom.comp (Subgroup.inclusion hStN)
  have hkerC : ∀ φ : ↥St, φ ∈ f.ker →
      ∀ a ∈ ggAutomizer L Bs, a * (φ : MulAut ↥Bs) = (φ : MulAut ↥Bs) * a := by
    intro φ hφ a ha
    have h1 : Subgroup.inclusion hStN φ ∈ (ggAutomizer L Bs).normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hφ)
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    exact Subgroup.mem_centralizer_iff.mp h1 a ha
  let r : Fin 4 → V →ₗ[ZMod 3] V := fun i =>
    (ggLin (p := 3) ι ((ε ((CoxeterMatrix.A 4).simple i) : ↥(ggAutomizer L Bs)) :
      MulAut ↥Bs)).toLinearMap
  have h01 : QuadraticMap.polar Q (v 0) (v 1) ≠ 0 := (hv3 0 1 (by decide) (by decide)).2
  have h12 : QuadraticMap.polar Q (v 1) (v 2) ≠ 0 := (hv3 1 2 (by decide) (by decide)).2
  have h23 : QuadraticMap.polar Q (v 2) (v 3) ≠ 0 := (hv3 2 3 (by decide) (by decide)).2
  let lam : MulAut ↥Bs → ZMod 3 := fun φ =>
    2 * (QuadraticMap.polar Q (v 0) (ggLin (p := 3) ι φ (v 0)) / Q (v 0))
  have hscalar : ∀ φ : ↥St, φ ∈ f.ker →
      ∀ i, ggLin (p := 3) ι (φ : MulAut ↥Bs) (v i) = lam φ • v i := by
    intro φ hφ
    refine ct_a4_scalar hvQ h01 h12 h23 (r := r) (fun i w => hvr i w)
      (C := (ggLin (p := 3) ι (φ : MulAut ↥Bs)).toLinearMap) ?_
    intro i w
    have hc := hkerC φ hφ _ (ε ((CoxeterMatrix.A 4).simple i)).property
    have h := congrArg (fun φ' => ggLin (p := 3) ι φ' w) hc
    simp only [map_mul, LinearEquiv.mul_apply] at h
    exact h.symm
  have hfix0 : ∀ φ : ↥St, ggLin (p := 3) ι (φ : MulAut ↥Bs) w0 = w0 := fun φ =>
    (ggLin_fix_iff (p := 3) ι (φ : MulAut ↥Bs) ⟨x, hx⟩).mp ((hStmem _).mp φ.2).2
  have hker_le : Nat.card f.ker ≤ 3 := by
    have hinj : Function.Injective (fun φ : ↥f.ker => lam ((φ : ↥St) : MulAut ↥Bs)) := by
      intro φ ψ h
      have hlin : (ggLin (p := 3) ι ((φ : ↥St) : MulAut ↥Bs)).toLinearMap =
          (ggLin (p := 3) ι ((ψ : ↥St) : MulAut ↥Bs)).toLinearMap := by
        refine LinearMap.ext_on hspan ?_
        rintro y (⟨i, rfl⟩ | hy)
        · simp only [LinearEquiv.coe_coe]
          rw [hscalar _ φ.2 i, hscalar _ ψ.2 i]
          exact congrArg (· • v i) h
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          simp only [LinearEquiv.coe_coe]
          rw [hfix0, hfix0]
      exact Subtype.ext (Subtype.ext
        (ggLin_injective (p := 3) ι (LinearEquiv.toLinearMap_injective hlin)))
    calc Nat.card ↥f.ker ≤ Nat.card (ZMod 3) := Nat.card_le_card_of_injective _ hinj
      _ = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hrange : Nat.card f.range ≤ 120 := (Subgroup.card_le_card_group f.range).trans hAut
  have h360 : Nat.card ↥St ≤ 360 := by
    rw [← Subgroup.card_ker_mul_card_range f]
    exact (Nat.mul_le_mul hker_le hrange).trans (by norm_num)
  have hge := GGOrthSetup.stab_ge S hd hx hQx
  rw [hcard_St] at hge
  omega

end CFSG.StandardType.OrthF3

end
