module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4TISets

public section

namespace CFSG.ASVolI

section TopSp

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF4m_eq_zero_or_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (c : K) : c = 0 ∨ c = 1 := by
  classical
  by_contra h
  push Not at h
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have h3 : ({0, 1, c} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, 1, c, zero_ne_one, Ne.symm h.1, Ne.symm h.2, rfl⟩
  have hle := Finset.card_le_univ ({0, 1, c} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem burnsideF4m_ringEquiv_eq_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (φ : K ≃+* K) : φ = 1 := by
  ext c
  rcases burnsideF4m_eq_zero_or_one_of_card_two hK c with rfl | rfl
  · rw [map_zero]
    rfl
  · rw [map_one]
    rfl

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_sp4_model_card (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (θ : StatedSp 2 K →* E),
      Nat.card K = 2 ^ f ∧ Function.Injective θ ∧ θ.range = Gp ∧
        Gp ⊓ M₁ = (Q2 K 0).map θ ∧ Gp ⊓ M₂ = (Q2 K 1).map θ := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have hinj : Function.Injective marking.transport := by
    refine (injective_iff_map_eq_one marking.transport).2 fun a ha => ?_
    have h3 := (burnsideF4f_transport_eq_one_iff marking a).1 ha
    exact Subtype.ext (burnsideF4gSpInv_scalar_eq_one h3 a.2)
  have hsurj := burnsideF4f_transport_surjective marking
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : ∀ b : Bool, nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    intro b
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSp_mem_rawStabilizer, burnsideF4gSp_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSp_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).2)
  let θ : StatedSp 2 marking.field →* E := Gp.subtype.comp marking.transport
  have hθinj : Function.Injective θ := Gp.subtype_injective.comp hinj
  have hrange : θ.range = Gp := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (marking.transport y).2
    · intro hx
      obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  have hpar : ∀ (b : Bool) (M : Subgroup E), M.subgroupOf Gp = marking.parabolic b →
      Gp ⊓ M = (Q2 marking.field (if b then 1 else 0)).map θ := by
    intro b M hM
    have e1 : marking.parabolic b =
        (Q2 marking.field (if b then 1 else 0)).map marking.transport :=
      congrArg (Subgroup.map marking.transport) (key b)
    calc Gp ⊓ M = (M.subgroupOf Gp).map Gp.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = ((Q2 marking.field (if b then 1 else 0)).map marking.transport).map Gp.subtype := by
          rw [hM, e1]
      _ = (Q2 marking.field (if b then 1 else 0)).map θ := Subgroup.map_map _ _ _
  exact ⟨marking.field, inferInstance, inferInstance, inferInstance, θ, hK, hθinj, hrange,
    by simpa using hpar false M₁ h1, by simpa using hpar true M₂ h2⟩

theorem burnsideF4m_transvectionT₀_eq {K : Type} [Field K] :
    CFSG.RankThree.PartOne.KCSpComm.transvectionT₀ K = burnsideF4gSpInv_xl (1 : K) := by
  apply Subtype.ext
  apply Units.ext
  rw [burnsideF4gSpInv_xl_val]
  exact coe_upperUnipotentSp _

theorem burnsideF4m_xl_mem_ctr_oPPrime {K : Type} [Field K] [Finite K] [CharP K 2] {t : K}
    (ht : t ≠ 0) : burnsideF4gSpInv_xl t ∈ ctr (oPPrime 2 (Q2 K 0)) := by
  rw [burnsideF4gSpInv_oPPrime_eq_S1]
  refine ⟨show burnsideF4gSpInv_xl t ∈ burnsideF4gSpInv_S1 K from ?_,
    Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  · rw [burnsideF4gSpInv_mem_S1, burnsideF4gSpInv_xl_mv]
    simp
  · rw [← burnsideF4gSpInv_centralizer_xl ht] at hs
    exact Subgroup.mem_centralizer_singleton_iff.1 hs

theorem burnsideF4m_top_Sp4two (hyp : HypF_4_4 .Sp4 2 1 Gp M₁ M₂) : Gp = ⊤ := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, _, _, _, θ, hK, hθinj, hrange, hM₁, -⟩ := burnsideF4m_sp4_model_card hyp
  rw [pow_one] at hK
  let Ψ : StatedSp 2 K ≃* ↥Gp :=
    (MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hrange)
  have hΨ : ∀ g, ((Ψ g : ↥Gp) : E) = θ g := fun g => rfl
  let π : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    MulEquiv.ofBijective (proj 2 K) CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  have hπ : ∀ g, π g = proj 2 K g := fun g => rfl
  let Φ : StatedProj (StatedSp 2 K) ≃* ↥Gp := π.symm.trans Ψ
  have hΦ : ∀ g, Φ (proj 2 K g) = Ψ g := fun g => by
    show Ψ (π.symm (proj 2 K g)) = Ψ g
    rw [← hπ, MulEquiv.symm_apply_apply]
  have hZ1 : ctr (oPPrime 2 (Gp ⊓ M₁)) = (ctr (oPPrime 2 (Q2 K 0))).map θ := by
    rw [hM₁, burnsideF4d_oPPrime_map θ hθinj, burnsideF4j_ctr_map θ hθinj]
  have hxl1 : burnsideF4gSpInv_xl (1 : K) ≠ 1 := burnsideF4gSpInv_xl_ne_one one_ne_zero
  rw [eq_top_iff]
  intro e _
  obtain ⟨n, hn, x, hx, rfl⟩ := hyp.split e
  suffices hxG : x ∈ Gp from Gp.mul_mem hn hxG
  have hfixE : x * θ (burnsideF4gSpInv_xl 1) * x⁻¹ = θ (burnsideF4gSpInv_xl 1) := by
    have hxN : x ∈ Subgroup.normalizer ((ctr (oPPrime 2 (Gp ⊓ M₁)) : Subgroup E) : Set E) :=
      burnsideF4j_mem_normalizer_ctr (burnsideF4d_Z1_normalizer_oPPrime
        (burnsideF4j_le_normalizer_inf hyp.normal M₁ hx.1))
    have hmem : θ (burnsideF4gSpInv_xl 1) ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) := by
      rw [hZ1]
      exact ⟨_, burnsideF4m_xl_mem_ctr_oPPrime one_ne_zero, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hxN _).mp hmem
    rw [hZ1] at hconj
    obtain ⟨z', hz', hz'e⟩ := hconj
    obtain ⟨t, rfl⟩ := burnsideF4gSpInv_ctr_oPPrime hz'
    rcases burnsideF4m_eq_zero_or_one_of_card_two hK t with rfl | rfl
    · exfalso
      rw [burnsideF4gSpInv_xl_zero, map_one] at hz'e
      have h1 : θ (burnsideF4gSpInv_xl 1) = 1 := by
        have := congrArg (fun y => x⁻¹ * y * x) hz'e
        simpa [mul_assoc] using this.symm
      exact hxl1 (hθinj (h1.trans (map_one θ).symm))
    · exact hz'e.symm
  let α : MulAut (StatedProj (StatedSp 2 K)) := (Φ.trans (burnsideF4d_rho Gp x)).trans Φ.symm
  have hα : ∀ g, Φ (α (proj 2 K g)) = burnsideF4d_rho Gp x (Ψ g) := fun g => by
    show Φ (Φ.symm (burnsideF4d_rho Gp x (Φ (proj 2 K g)))) = _
    rw [MulEquiv.apply_symm_apply, hΦ]
  have hfix : α (proj 2 K (CFSG.RankThree.PartOne.KCSpComm.transvectionT₀ K)) =
      proj 2 K (CFSG.RankThree.PartOne.KCSpComm.transvectionT₀ K) := by
    rw [burnsideF4m_transvectionT₀_eq]
    apply Φ.injective
    rw [hα, hΦ]
    apply Subtype.ext
    rw [burnsideF4d_rho_apply, hΨ, hfixE]
  have hαE : α ∈ spSemilinearAutGroup 2 K := by
    by_contra h
    exact CFSG.RankThree.PartOne.KCSpComm.not_fixes_transvectionT₀_of_not_mem h hfix
  obtain ⟨g, φ, hgφ⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exists_eq_spInner_mul_fieldAut hαE
  rw [burnsideF4m_ringEquiv_eq_one_of_card_two hK φ, map_one, mul_one,
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.spInner_eq_conj] at hgφ
  have hcomm : ∀ m ∈ Gp, x * m * x⁻¹ = θ g * m * (θ g)⁻¹ := by
    intro m hm
    obtain ⟨h, rfl⟩ := hrange ▸ hm
    have h1 := hα h
    rw [hgφ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hΦ] at h1
    have h2 := congrArg Subtype.val h1
    rw [burnsideF4d_rho_apply, hΨ, hΨ, map_mul, map_mul, map_inv] at h2
    exact h2.symm
  have hcx : (θ g)⁻¹ * x ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := hcomm m hm
    calc m * ((θ g)⁻¹ * x) = (θ g)⁻¹ * (θ g * m * (θ g)⁻¹) * x := by group
      _ = (θ g)⁻¹ * (x * m * x⁻¹) * x := by rw [h1]
      _ = (θ g)⁻¹ * x * m := by group
  rw [hyp.centralizer_trivial, Subgroup.mem_bot, inv_mul_eq_one] at hcx
  rw [← hcx, ← hrange]
  exact ⟨g, rfl⟩

end TopSp

end CFSG.ASVolI
