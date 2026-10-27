module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcE6Outer
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcC4Native
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
import CFSG.LieType.SeitzGeneration.OrdinaryOuterLocal
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.Burgoyne.E2 (e6GraphSign)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

private theorem fixed_of_conj_image_e6 {G : Type*} [Group G] (ψ β : MulAut G) {a : G}
    (h : (ψ * β * ψ⁻¹) a = a) : β (ψ.symm a) = ψ.symm a := by
  have h' : ψ (β (ψ.symm a)) = a := by
    simpa only [MulAut.mul_apply, MulAut.inv_apply] using h
  apply ψ.injective
  rw [h', ψ.apply_symm_apply]

private theorem fixed_of_generators_e6' {G : Type} [Group G] [Finite G] [Finite (MulAut G)]
    (E : Subgroup (MulAut G))
    {x : MulAut G} {h : G} (hxE : x ∈ E) (hhE : MulAut.conj h ∈ E)
    (hx2 : x * x = 1) (hconj2 : MulAut.conj h * MulAut.conj h = 1)
    (hcomm : x * MulAut.conj h = MulAut.conj h * x)
    (hxne : x ≠ 1) (hhne : MulAut.conj h ≠ 1) (hne : MulAut.conj h ≠ x)
    (h4 : Nat.card E = 4) {a : G} (hfixx : x a = a) (hfixh : MulAut.conj h a = a) :
    ∀ e ∈ E, e a = a := by
  obtain ⟨hmem, -, -, hcard⟩ :=
    CFSG.GH74.GLS.Stage1.Main.four_of_invols (u₁ := MulAut.conj h) (u₂ := x)
      hconj2 hx2 hcomm.symm hhne hxne hne
  have hEeq : zpowers (MulAut.conj h) ⊔ zpowers x = E :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (zpowers_le.2 hhE) (zpowers_le.2 hxE))
      (by rw [hcard, h4])
  intro e he
  rw [← hEeq] at he
  rcases hmem e he with rfl | rfl | rfl | rfl
  · rfl
  · exact hfixh
  · exact hfixx
  · rw [MulAut.mul_apply, hfixx, hfixh]


theorem exists_fixed_rElement_four_e6 {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    (E : Subgroup (MulAut ↥(adjointGroup .E6 K))) (hE : CFSG.Open.IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) :
    ∃ y : ↥(adjointGroup .E6 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      ∀ e ∈ E, e y = y := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL .E6 K) := finite_modGL
  have : Finite ↥(adjointGroup .E6 K) := Subtype.finite
  have : Finite (MulAut ↥(adjointGroup .E6 K)) :=
    Finite.of_injective (fun e : MulAut ↥(adjointGroup .E6 K) => (e : _ → _))
      DFunLike.coe_injective
  have hZ : ∀ c : ↥(adjointGroup .E6 K), MulAut.conj c = 1 → c = 1 := by
    intro c hc
    have hcZ : c ∈ Subgroup.center ↥(adjointGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : c * g * c⁻¹ = g := by
        have := congrArg (fun φ : MulAut ↥(adjointGroup .E6 K) => φ g) hc
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * c = c * g * c⁻¹ * c := by rw [h1]
        _ = c * g := by group
    rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hcZ
  rcases exists_fixed_rElement_four_e6_or_signedGraph hK E hE h4 with h |
    ⟨x, h, δ, δ', hxE, hhE, hhne, hh2, hxh, hδ, hδ'⟩
  · exact h
  · have hE2 : ∀ e ∈ E, e ^ 2 = 1 := hE.2
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hx2 : x * x = 1 := by rw [← sq]; exact hE2 x hxE
    have hch2 : MulAut.conj h * MulAut.conj h = 1 := by rw [← sq, ← map_pow, hh2, map_one]
    have hcomm : x * MulAut.conj h = MulAut.conj h * x := hEcomm x hxE _ hhE
    have hαne : (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
        diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup Tag.E6 K)) ≠ 1 := by
      intro hα1
      obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
        ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
      have h1m : ∀ x : ModGL TwistTag.E6.tag K,
          Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x := fun x =>
        Units.ext (entrywise_id _)
      set e1 : Fin (exactE Tag.E6) := ⟨1, by decide⟩ with he1
      have hQ : exactQ TwistTag.E6.tag K (e1 : ℕ) = diagramMap TwistTag.E6 K := by
        rw [show (e1 : ℕ) = 1 from by rw [he1]]
        exact pow_one _
      have hform : ∀ h : adjointGroup TwistTag.E6.tag K,
          ((rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
            diagramConjAut TwistTag.E6 K) h : ModGL TwistTag.E6.tag K) =
          ((1 : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) *
            rootDiagUnit TwistTag.E6.tag (e6GraphSign K) *
            exactQ TwistTag.E6.tag K (e1 : ℕ) *
            Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
              (h : ModGL TwistTag.E6.tag K) *
            (exactQ TwistTag.E6.tag K (e1 : ℕ))⁻¹ *
            (rootDiagUnit TwistTag.E6.tag (e6GraphSign K))⁻¹ *
            (((1 : adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro h
        rw [MulAut.mul_apply, coe_rootDiagAut, coe_diagramConjAut, hQ, h1m]
        rw [show ((1 : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) = 1
          from rfl]
        group
      have hΘα : Θ (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
            diagramConjAut TwistTag.E6 K) =
          (1, Multiplicative.ofAdd ((e1 : ℕ) : ZMod (exactE Tag.E6))) :=
        hΘ _ 1 (e6GraphSign K) 1 e1 hform
      have hkey : Multiplicative.ofAdd ((e1 : ℕ) : ZMod (exactE Tag.E6)) = 1 := by
        have h1 : Θ (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
            diagramConjAut TwistTag.E6 K) = Θ 1 := congrArg Θ hα1
        have h2 : Θ (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
            diagramConjAut TwistTag.E6 K) = 1 := h1.trans (map_one Θ)
        have h3 := congrArg (fun p : RingAut K × Multiplicative (ZMod (exactE Tag.E6)) =>
          p.2) h2
        have h4 := congrArg (fun p : RingAut K × Multiplicative (ZMod (exactE Tag.E6)) =>
          p.2) hΘα
        exact h4.symm.trans h3
      have h5 : ((e1 : ℕ) : ZMod (exactE Tag.E6)) = 0 :=
        Multiplicative.ofAdd.injective (by simpa using hkey)
      have h7 : ((1 : ℕ) : ZMod (exactE Tag.E6)) = 0 := by simpa [he1] using h5
      exact absurd h7 (by decide)
    have hδT : δ * x * δ⁻¹ = (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
        diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup Tag.E6 K)) := hδ
    have hδ'T : δ' * (x * MulAut.conj h) * δ'⁻¹ =
        (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
          diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup Tag.E6 K)) := hδ'
    have hx1 : x ≠ 1 := by
      intro hx
      have h : δ * x * δ⁻¹ = 1 := by rw [hx, mul_one, mul_inv_cancel]
      exact hαne (hδT.symm.trans h)
    have hch1 : MulAut.conj h ≠ 1 := fun hce => hhne (hZ h hce)
    have hxh1 : MulAut.conj h ≠ x := by
      intro hxe
      have h : δ' * (x * MulAut.conj h) * δ'⁻¹ = 1 := by
        rw [hxe, hx2, mul_one, mul_inv_cancel]
      exact hαne (hδ'T.symm.trans h)
    set h' : ↥(adjointGroup .E6 K) := δ h with hh'def
    have hh'2 : h' ^ 2 = 1 := by rw [hh'def, ← map_pow, hh2, map_one]
    have hαh'' : (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
        diagramConjAut TwistTag.E6 K) h' = h' := by
      rw [hh'def, ← hδ]
      change δ (x (δ⁻¹ (δ h))) = δ h
      rw [MulAut.inv_apply_self, hxh]
    obtain ⟨u, hu1, ⟨n, hun⟩, hucomm, huα⟩ :
        ∃ u : ↥(adjointGroup Tag.E6 K), u ≠ 1 ∧
          (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ Commute u h' ∧
          (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
            diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup Tag.E6 K)) u = u :=
      exists_rElement_fixed_signedGraph_inv hK h' hh'2 hαh''
    refine ⟨δ.symm u, ?_, ⟨n, ?_⟩, ?_⟩
    · intro hc
      have h := congrArg δ hc
      rw [map_one, δ.apply_symm_apply] at h
      exact hu1 h
    · apply δ.injective
      rw [map_pow, δ.apply_symm_apply, hun, map_one]
    · refine fixed_of_generators_e6' E hxE hhE hx2 hch2 hcomm hx1 hch1 hxh1 h4
        (fixed_of_conj_image_e6 δ x (by rw [hδT]; exact huα)) ?_
      have hcomm' : Commute (δ.symm u) h := by
        have hmul := congrArg δ.symm hucomm.eq
        rw [map_mul, map_mul, hh'def, δ.symm_apply_apply] at hmul
        exact hmul
      rw [MulAut.conj_apply, ← hcomm'.eq, mul_inv_cancel_right]

theorem exists_normalized_rSubgroup_four_e6 {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(adjointGroup .E6 K)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    ∃ R : Subgroup ↥(adjointGroup .E6 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      ∀ e ∈ E, R.map e.toMonoidHom = R := by
  obtain ⟨y, hy1, ⟨n, hyn⟩, hyE⟩ := exists_fixed_rElement_four_e6 hK E hE h4
  refine ⟨zpowers y, fun h => hy1 ?_, ?_, fun e he => ?_⟩
  · have hmem : y ∈ zpowers y := mem_zpowers y
    rwa [h, Subgroup.mem_bot] at hmem
  · rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyn, one_zpow]
  · rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hyE e he]

theorem seitzFour_e6 :
    SeitzFour fun X _ => ∃ p f : ℕ, p ≠ 2 ∧ CFSG.Models.LieModel X .E6 0 p f := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 _
  obtain ⟨p, f, hp2, hm⟩ := hP
  obtain ⟨K, _, _, hK2, ⟨φ⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 2 ∧
      Nonempty (↥L ≃* ↥(adjointGroup .E6 K)) := by
    obtain ⟨hadm, hU⟩ :=
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        hm).chevalleyExceptionalModel (by decide)
    obtain ⟨K, _, _, hK, he⟩ := nonempty_mulEquiv_adjointGroup .E6 hU
    have : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        hadm.1 hadm.2.1 hK
    exact ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp2, he⟩
  set A := E.map (MulAut.conjNormal : G →* MulAut ↥L)
  have hA : CFSG.Open.IsElemAbelian 2 A := hE.map _
  have hA4 : Nat.card A = 4 := by
    rw [Subgroup.card_map_of_injective (conjNormal_injective_of_centralizer_eq_bot hC), h4]
  set A' := A.map (MulAut.congr φ).toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian 2 A' := hA.map _
  have hA'4 : Nat.card A' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hA4]
  obtain ⟨R, hR, hRr, hER⟩ := exists_normalized_rSubgroup_four_e6 hK2 A' hA' hA'4
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have : IsSimpleGroup ↥(adjointGroup .E6 K) := φ.symm.isSimpleGroup
  have hPA : PlaneGen A := (planeGen_map_congr φ A).1
    (planeGen_of_normalized_rSubgroup_adjointGroup hK2 A' hA' hA'4 R hR hRr hER)
  exact iSup_centralizer_eq_of_seitzHyperGamma hC h4
    ((planeGen_iff_seitzHyperGamma Nat.prime_two (by rw [hA4]; norm_num)).1 hPA)

end CFSG.LocalAnalysis.WeakClosure81
