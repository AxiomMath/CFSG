module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResFFDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.RankThree.GF2n.Stroth80.Sec7SingularVectors
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Orth

open TauCeti

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

theorem ggOrthF3_exists_mem_map_eq (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : Module.finrank (ZMod 3) V = 4)
    (W : Submodule (ZMod 3) V) (hW : Module.finrank (ZMod 3) W = 3) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ w ∈ W, Q w = c := by
  have hperp : Module.finrank (ZMod 3)
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hd, hW]
  have hsmall : ∀ U : Submodule (ZMod 3) V,
      (∀ u ∈ U, ∀ w ∈ W, QuadraticMap.polar Q w u = 0) → Module.finrank (ZMod 3) U ≤ 1 := by
    intro U hU
    rw [← hperp]
    refine Submodule.finrank_mono fun u hu => ?_
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun w hw => ?_
    change QuadraticMap.polarBilin Q w u = 0
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hU u hu w hw
  have hpolar0 : ∀ U : Submodule (ZMod 3) V, (∀ u ∈ U, Q u = 0) →
      ∀ u ∈ U, ∀ u' ∈ U, QuadraticMap.polar Q u u' = 0 := by
    intro U hU u hu u' hu'
    rw [QuadraticMap.polar, hU _ (U.add_mem hu hu'), hU u hu, hU u' hu']
    simp
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  obtain ⟨w₁, hw₁W, hw₁⟩ : ∃ w ∈ W, Q w ≠ 0 := by
    by_contra hno
    push Not at hno
    have h := hsmall W fun u hu w hw => hpolar0 W hno w hw u hu
    omega
  set φ : V →ₗ[ZMod 3] ZMod 3 := QuadraticMap.polarBilin Q w₁ with hφ
  set U : Submodule (ZMod 3) V := W ⊓ LinearMap.ker φ with hU
  have hker : 3 ≤ Module.finrank (ZMod 3) (LinearMap.ker φ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2' : Module.finrank (ZMod 3) (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [Module.finrank_self] at this
    omega
  have hUdim : 2 ≤ Module.finrank (ZMod 3) U := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker φ)
    rw [← hU] at h1
    have h2' := Submodule.finrank_le (W ⊔ LinearMap.ker φ)
    rw [hd] at h2'
    omega
  have hUpol : ∀ u ∈ U, QuadraticMap.polar Q w₁ u = 0 := by
    intro u hu
    have h := (LinearMap.mem_ker.mp hu.2)
    rwa [hφ, QuadraticMap.polarBilin_apply_apply] at h
  obtain ⟨w₂, hw₂U, hw₂⟩ : ∃ u ∈ U, Q u ≠ 0 := by
    by_contra hno
    push Not at hno
    have hpU := hpolar0 U hno
    have hq1 : QuadraticMap.polar Q w₁ w₁ ≠ 0 := by
      rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat]
      exact mul_ne_zero h2 hw₁
    have h := hsmall U fun u hu w hw => by
      set t : ZMod 3 := QuadraticMap.polar Q w₁ w * (QuadraticMap.polar Q w₁ w₁)⁻¹
      have hwt : w - t • w₁ ∈ U := by
        refine ⟨W.sub_mem hw (W.smul_mem t hw₁W), LinearMap.mem_ker.mpr ?_⟩
        rw [hφ, map_sub, map_smul, QuadraticMap.polarBilin_apply_apply,
          QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
        simp only [t]
        rw [mul_assoc, inv_mul_cancel₀ hq1, mul_one, sub_self]
      have hsplit : w = (w - t • w₁) + t • w₁ := by abel
      rw [hsplit, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
        hpU _ hwt u hu, hUpol u hu, smul_zero, add_zero]
    omega
  have hpol12 : QuadraticMap.polar Q w₁ w₂ = 0 := hUpol w₂ hw₂U
  have key : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → a = c ∨ b = c ∨ a + b = c := by
    revert c
    decide
  rcases key (Q w₁) (Q w₂) hw₁ hw₂ with h | h | h
  · exact ⟨w₁, hw₁W, h⟩
  · exact ⟨w₂, hw₂U.1, h⟩
  · refine ⟨w₁ + w₂, W.add_mem hw₁W hw₂U.1, ?_⟩
    rw [QuadraticMap.map_add Q w₁ w₂, hpol12, add_zero]
    exact h

end Orth

theorem ggGOFour_exists_apply_mem {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (hA : GGIsGOFourMinusThree A) {E : Subgroup G} (hE : E ≤ Bs)
    (hEc : Nat.card E = 27) (b : ↥Bs) : ∃ a ∈ A, ((a b : ↥Bs) : G) ∈ E := by
  obtain ⟨hcard, hcardA, V, _, _, ι, Q, hQ, hinv⟩ := hA
  have : Finite ↥Bs := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfinV : Finite V := Finite.of_equiv ↥Bs (Additive.ofMul.trans ι.toEquiv)
  have : FiniteDimensional (ZMod 3) V := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 3) V = 4 := by
    have h1 : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 4 := by
      rw [FiniteField.pow_finrank_eq_natCard 3 V, ← card_eq_of_ggLin ι, hcard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 3] V => (g : V → V)) DFunLike.coe_injective
  let f : ↥A → ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun a =>
    ⟨ggLin (p := 3) ι a, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hinv a a.2)⟩
  have hf : Function.Injective f := fun a a' h =>
    Subtype.ext (ggLin_injective (p := 3) ι (congrArg Subtype.val h))
  have hOle : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) ≤ Nat.card ↥A := by
    rw [hcardA]
    by_cases hplus : ∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0
    · rw [OrthF3.card_orthogonalGroup_four_plus Q hQ hd hplus]
      norm_num
    · rw [OrthF3.card_orthogonalGroup_four_minus Q hQ hd hplus]
  have hsurj : Function.Surjective f := (hf.bijective_of_nat_card_le hOle).2
  set W : Submodule (ZMod 3) V := AddSubgroup.toZModSubmodule 3
    ((Subgroup.toAddSubgroup (E.subgroupOf Bs)).comap ι.symm.toAddMonoidHom) with hWdef
  have hmemW : ∀ v : V, v ∈ W ↔ ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ E := fun v =>
    (AddSubgroup.mem_toZModSubmodule 3).trans Iff.rfl
  have hcardW : Nat.card W = 27 := by
    rw [← hEc]
    refine Nat.card_congr
      { toFun := fun v => ⟨((Additive.toMul (ι.symm v) : ↥Bs) : G), (hmemW v).mp v.2⟩
        invFun := fun e => ⟨ι (Additive.ofMul (⟨e, hE e.2⟩ : ↥Bs)), (hmemW _).mpr (by simp)⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun e => Subtype.ext (by simp) }
  have hW : Module.finrank (ZMod 3) W = 3 := by
    have h1 : 3 ^ Module.finrank (ZMod 3) W = 3 ^ 3 := by
      rw [FiniteField.pow_finrank_eq_natCard 3 W, hcardW]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  set v : V := ι (Additive.ofMul b) with hv
  obtain ⟨w, hwW, g, hg, hgv⟩ :
      ∃ w ∈ W, ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g v = w := by
    by_cases hQv : Q v = 0
    · by_cases hv0 : v = 0
      · exact ⟨0, W.zero_mem, 1, one_mem _, by rw [hv0]; rfl⟩
      obtain ⟨w, hwW, hw0, hQw⟩ :=
        CFSG.RankThree.GF2n.Stroth80.sec7_exists_singular_of_finrank_three Q W hW
      obtain ⟨g, hg, hgv⟩ :=
        CFSG.ClassicalInvolution.exists_mem_orthogonalGroup_apply_eq_of_nondegenerate hQ hQv hQw
          hv0 hw0
      exact ⟨w, hwW, g, hg, hgv⟩
    · obtain ⟨w, hwW, hQw⟩ := ggOrthF3_exists_mem_map_eq Q hQ hd W hW hQv
      have : NeZero (2 : ZMod 3) := ⟨by decide⟩
      obtain ⟨e, he⟩ :=
        QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq Q hQw.symm (hQw ▸ hQv)
      exact ⟨w, hwW, e.toLinearEquiv,
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun m => e.map_app m, he⟩
  obtain ⟨a, ha⟩ := hsurj ⟨g, hg⟩
  refine ⟨a, a.2, ?_⟩
  have hga : ggLin (p := 3) ι a = g := congrArg Subtype.val ha
  have hw : ι (Additive.ofMul (a.1 b)) = w := by
    rw [← ggLin_apply_ofMul (p := 3) ι, hga, ← hgv]
  have h1 := (hmemW w).mp hwW
  rwa [← hw, AddEquiv.symm_apply_apply, toMul_ofMul] at h1

theorem ggFF_inner (hRig : GGLabelRigidInput) {G : Type} [Group G] {Bs L : Subgroup G}
    (hInn : GGInnerDiagOn Bs L) {lab : LargeEvenLabel} (hlab : lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.A, 6, 1⟩)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) :
    Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ c ∈ L, ∀ l ∈ L, b * l * b⁻¹ = c * l * c⁻¹ := by
  have hΛ : LargeEvenInLambda2 lab := by
    rcases hlab with rfl | rfl <;> simp [LargeEvenInLambda2]
  have hall : ∀ lab', LargeEvenInLambda2 lab' → lab' = lab →
      LargeEvenLabelAll lab' (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
    rintro lab' - rfl Q hQ
    rcases hlab with rfl | rfl
    · exact recipeLinear_subsetInn (by decide) hQ
    · exact recipeLinear_subsetInn (by decide) hQ
  have hmark := largeEvenMarking_and_labelAll_simple (S := fun lab' => lab' = lab)
    (P' := fun R _ I _ => I ⊆ LargeEvenInnSet R) hall
    (by intro _ _ _ _ _ _ h; exact h.1) (ggInnerDiagOn_relabel hRig hInn hΛ hhas)
  obtain ⟨hperf, lab', -, hraw⟩ := hmark
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hN, h3⟩, hIinn⟩ := largeEvenRawDatum_exists hraw
  refine ⟨hN, fun b hb => ?_⟩
  obtain ⟨r, hr⟩ := hIinn (ggLAut_mem_of_induces L θ hN h3 hb)
  obtain ⟨q, hq⟩ := θ.surjective r
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hkN : (k : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer k.2
  have hcN : (k : G)⁻¹ * b ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hkN) (hN hb)
  have hc1 : ggLAut L θ ⟨(k : G)⁻¹ * b, hcN⟩ = 1 := by
    have e : (⟨(k : G)⁻¹ * b, hcN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨k, hkN⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨b, hN hb⟩ := Subtype.ext rfl
    rw [e, map_mul, map_inv, ← hr, ggLAut_mk_self, hq, inv_mul_cancel]
  have hcC := mem_centralizer_of_ggLAut_eq_one L θ hperf hc1
  refine ⟨k, k.2, fun l hl => ?_⟩
  have h := Subgroup.mem_centralizer_iff.mp hcC l hl
  calc b * l * b⁻¹ = (k : G) * ((k : G)⁻¹ * b * l) * b⁻¹ := by group
    _ = (k : G) * (l * ((k : G)⁻¹ * b)) * b⁻¹ := by rw [← h]
    _ = (k : G) * l * (k : G)⁻¹ := by group

theorem ggResFFGOFourInput_of_ff (hRig : GGLabelRigidInput) (hZ : GGO2aCentreKnown)
    (hFF : GGFFLinearProp2Input) : GGResFFGOFourInput := by
  intro G _ _ p B Bs x L D J y K hH hsh
  obtain ⟨hp3, hlabL, hGO⟩ := hsh
  subst hp3
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hBsG : GGBstar 3 B Bs := hcfg.2.1
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hperf : commutator ↥L = ⊤ := hInn.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxBs : x ∈ Bs := hBsG.1 hS.2.1
  obtain ⟨lab, hlab, hhas⟩ : ∃ lab : LargeEvenLabel, (lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.A, 6, 1⟩) ∧
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
    rcases hlabL with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hZL : Subgroup.center ↥L = ⊥ := ggO2a_center_eq_bot hZ hperf hlab hhas
  have hLlab : GGHasLabel ⟨.A, 5, 1⟩ ↥L ∨ GGHasLabel ⟨.A, 6, 1⟩ ↥L := by
    rcases hlab with rfl | rfl
    · exact Or.inl (ggO2a_hasLabel_of_centre hZ hperf (Or.inl rfl) hhas)
    · exact Or.inr (ggO2a_hasLabel_of_centre hZ hperf (Or.inr rfl) hhas)
  obtain ⟨hN, hinner⟩ := ggFF_inner hRig hInn hlab hhas
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hcfg.bstar_inf_centralizer_L
  have hcard27 : Nat.card ↥(Bs ⊓ L) = 27 := by
    have h := card_ggBstar_split hBsG hZL hN hinner
    rw [hcfg.card_bstar_inf_centralizer_L, hGO.1] at h
    omega
  have hjoin : Subgroup.closure {x} ⊔ Bs ⊓ L = Bs := by
    refine le_antisymm
      (sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hxBs)) inf_le_left)
      fun b hb => ?_
    obtain ⟨e, he, c, hc, rfl⟩ := ggBstar_split_of_inner hBsG hZL hN hinner b hb
    rw [hCx, Subgroup.zpowers_eq_closure] at hc
    exact mul_mem (le_sup_right (a := Subgroup.closure {x}) he)
      (le_sup_left (b := Bs ⊓ L) hc)
  have hEA : IsElemAbelian 3 (Bs ⊓ L) := CFSG.Open.IsElemAbelian.mono hBsG.2.1 inf_le_left
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
    refine ⟨Bs ⊓ L, inf_le_right, fun e => ⟨1, Subtype.ext (by simpa using hEA.2 e e.2)⟩,
      fun hcyc => ?_⟩
    have hexp : Monoid.exponent ↥(Bs ⊓ L) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun e => Subtype.ext (by simpa using hEA.2 e e.2)
    rw [IsCyclic.exponent_eq_card, hcard27] at hexp
    norm_num at hexp
  have hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mpr
      fun g hg => mem_normalizer_of_sstar hS hnc hg
  have hAtop : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  obtain ⟨a, haA, hax⟩ := ggGOFour_exists_apply_mem hGO (E := Bs ⊓ L) inf_le_left hcard27
    ⟨x, hxBs⟩
  obtain ⟨g, -, -, hga⟩ := mem_ggAutomizer_iff.mp (hAtop haA)
  have hfus : ∃ g : G, g * x * g⁻¹ ∈ L := ⟨g, hga ⟨x, hxBs⟩ ▸ hax.2⟩
  have hc := hFF G x L (Bs ⊓ L) hcfg.orderOf_x hLx hLn hLlab inf_le_right hEA
    (hcard27.trans (by norm_num)) hS.2.2.2.2 hfus hH.1.1.2.2.2.1
  rw [hjoin] at hc
  have hdvd : 1440 ∣ Nat.card ↥(ggAutomizer ⊤ Bs) := by
    rw [← hGO.2.1]
    exact Subgroup.card_dvd_of_le hAtop
  rcases hc with hc | hc <;> rw [hc] at hdvd <;> norm_num at hdvd

end CFSG.StandardType
