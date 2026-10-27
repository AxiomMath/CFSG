module

public import CFSG.Quasithin.Background.C1GNDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellHull
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization commutatorElement

section Output

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem natural_center_output_of_supplement (h : IsNatBase S ρ (Ecore G) ψ) {V' : Subgroup G}
    (hV'S : V' ≤ (S : Subgroup G)) (hV'n : (V'.subgroupOf (S : Subgroup G)).Normal)
    (hV'e : CFSG.IsElementaryAbelian 2 V')
    (hSV' : ⁅(S : Subgroup G), V'⁆ ≤ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (hsup : (S : Subgroup G) = CFSG.pCore 2 G ⊔ V') :
    ⁅CFSG.pCore 2 G, Kodd G⁆ = Vmod G ∧ Vmod G ≤ Ecore G ∧
      ∃ β : (⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G) →* Multiplicative (Fin 2 → k),
        Function.Surjective β ∧
        β.ker = ((⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G) ⊓ Subgroup.center G).subgroupOf
          (⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G) ∧
        (∀ (g : G) (u u' : (⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G)),
          (u' : G) = g * u * g⁻¹ → Multiplicative.toAdd (β u') =
            (ρ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (β u))) := by
  classical
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have hgen : ⨆ g : G, cj (S : Subgroup G) g = ⊤ := by
    rw [iSup_cj_eq_normalClosure]; exact h.normalClosure_sylow_eq_top
  have hα : (S : Subgroup G) = CFSG.pCore 2 G ⊔
      aimg (S : Subgroup G) (MulEquiv.refl (S : Subgroup G)) V' := by
    rw [aimg_refl_of_le hV'S]; exact hsup
  obtain ⟨hQK, -⟩ := sylow_module_translate_centralizes_core hQ2 S hgen hV'S hV'n hV'e hSV'
    (MulEquiv.refl _) hα
  have hQKE : ⁅CFSG.pCore 2 G, Kodd G⁆ ≤ Ecore G := hQK
  have hEq : ⁅CFSG.pCore 2 G, Kodd G⁆ = Vmod G := by
    have : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
    exact (prime_residual_commutator_through_normal_layer (p := 2) (E := Ecore G)
      (Q := CFSG.pCore 2 G) (K := Kodd G) Ecore_le_core hQ2 Kodd_closure hQK).1
  refine ⟨hEq, Vmod_le_Ecore, ψ.comp (Subgroup.inclusion hQKE), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨v, hv, hψ⟩ := h.ψ_Vmod_surj w
    exact ⟨⟨v, hEq.symm ▸ hv⟩, hψ⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : (ψ.comp (Subgroup.inclusion hQKE)) u = 1 ↔
        ((Subgroup.inclusion hQKE u : Ecore G) : G) ∈ Subgroup.center G := h.ψ_eq_one_iff
    rw [h1]
    exact ⟨fun hc => ⟨u.2, hc⟩, fun hc => hc.2⟩
  · intro g u u' hu
    exact h.ψ_equiv g (Subgroup.inclusion hQKE u) (Subgroup.inclusion hQKE u') hu

end Output

section Ambient

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem map_Kodd_subtype (H : Subgroup Ω) : (Kodd ↥H).map H.subtype = oddOrderSubgroup H := by
  unfold Kodd pPrimeGen oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    refine ⟨x.2, ?_⟩
    show Odd (orderOf (x : Ω))
    rw [Subgroup.orderOf_coe]
    exact Nat.coprime_two_right.mp hx
  · rintro ⟨hyH, hy⟩
    refine ⟨⟨y, hyH⟩, ⟨trivial, ?_⟩, rfl⟩
    rw [Subgroup.orderOf_mk]
    exact Nat.coprime_two_right.mpr hy

theorem twoResidual_eq_oddOrderSubgroup (H : Subgroup Ω) :
    twoResidual H = oddOrderSubgroup H := by
  apply le_antisymm
  · have hLH : oddOrderSubgroup H ≤ H := (Subgroup.closure_le H).mpr fun _ hy => hy.1
    refine iInf₂_le (oddOrderSubgroup H) ?_ |>.trans le_rfl
    exact ⟨hLH, (Subgroup.le_normalizer).trans (normalizer_le_normalizer_oddOrderSubgroup H),
      fun x hx => exists_pow_mem_oddOrderSubgroup hx⟩
  · refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H y hy.1
    exact mem_of_odd_orderOf_of_pow_mem hy.2 hk

theorem isL2OrA3Block_of_supplement {H : Subgroup Ω} (hchar : CharTwo H) {k : Type} [Field k]
    [Finite k] {S : Sylow 2 ↥H} {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k}
    {ψ : Ecore ↥H →* Multiplicative (Fin 2 → k)} (h : IsSeed S ρ (Ecore ↥H) ψ)
    {V' : Subgroup ↥H} (hV'S : V' ≤ (S : Subgroup ↥H))
    (hV'n : ∀ s ∈ (S : Subgroup ↥H), ∀ x ∈ V', s * x * s⁻¹ ∈ V')
    (hV'e : CFSG.Open.IsElemAbelian 2 V')
    (hSV' : ⁅(S : Subgroup ↥H), V'⁆ ≤ Subgroup.centralizer ((S : Subgroup ↥H) : Set ↥H))
    (hsup : (S : Subgroup ↥H) = CFSG.pCore 2 ↥H ⊔ V') :
    IsL2OrA3Block H (twoResidual H) := by
  classical
  obtain ⟨n, hn, hcard⟩ := h.card_k
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hV'n' : (V'.subgroupOf (S : Subgroup ↥H)).Normal :=
    ⟨fun x hx g => by
      have := hV'n (g : ↥H) g.2 (x : ↥H) hx
      exact this⟩
  have hV'e' : CFSG.IsElementaryAbelian 2 V' :=
    isElementaryAbelian_iff.mpr (isElemAbelian_iff.mp hV'e)
  obtain ⟨hQK, hVE, βo, hβs, hβk, hβe⟩ :=
    natural_center_output_of_supplement h.toIsNatBase hV'S hV'n' hV'e' hSV' hsup
  set L : Subgroup Ω := oddOrderSubgroup H with hLdef
  have hKodd' : (Kodd ↥H).map H.subtype = L := map_Kodd_subtype H
  have hLH : L ≤ H := (Subgroup.closure_le H).mpr fun _ hy => hy.1
  have hQmap : blockQ H = (CFSG.pCore 2 ↥H).map H.subtype := blockQ_eq_map H
  have hUmap : (⁅blockQ H, L⁆ : Subgroup Ω) = (⁅CFSG.pCore 2 ↥H, Kodd ↥H⁆).map H.subtype := by
    rw [hQmap, ← hKodd', Subgroup.map_commutator]
  have hcentral : (⁅blockQ H, L⁆ : Subgroup Ω) ≤
      Subgroup.centralizer ((blockQ H : Subgroup Ω) : Set Ω) := by
    rw [hUmap, hQK]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [hQmap] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hxE := hVE hx
    have := (mem_centerTorsion_iff.mp hxE).2.1 p hp
    exact congrArg Subtype.val this
  have hsetup : NaturalOvergroupSetup H L :=
    { charTwo := hchar
      le := hLH
      normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr
        ((Subgroup.le_normalizer).trans (normalizer_le_normalizer_oddOrderSubgroup H))
      noPQ := hasNoTwoQuotient_oddOrderSubgroup H
      two_quot := fun x hx => exists_pow_mem_oddOrderSubgroup hx
      central := hcentral }
  let W : Subgroup ↥H := ⁅CFSG.pCore 2 ↥H, Kodd ↥H⁆
  let eU : ↥(⁅blockQ H, L⁆ : Subgroup Ω) ≃* ↥W :=
    (MulEquiv.subgroupCongr hUmap).trans
      (W.equivMapOfInjective H.subtype H.subtype_injective).symm
  have heU : ∀ u : ↥(⁅blockQ H, L⁆ : Subgroup Ω), (((eU u : ↥W) : ↥H) : Ω) = (u : Ω) := by
    intro u
    have h3' := (W.equivMapOfInjective H.subtype H.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hUmap u)
    have h4' := congrArg (fun z : ↥(W.map H.subtype) => (z : Ω)) h3'
    rw [Subgroup.coe_equivMapOfInjective_apply] at h4'
    exact h4'
  let β' : ↥(⁅blockQ H, L⁆ : Subgroup Ω) →* Multiplicative (Fin 2 → k) :=
    βo.comp eU.toMonoidHom
  have hmod : NaturalOvergroupModule H L H ρ β' :=
    { KD := hLH
      DX := le_rfl
      ρ_surj := h.surj
      β_surj := hβs.comp eU.surjective
      β_ker := by
        ext u
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        show βo (eU u) = 1 ↔ _
        have hkerβ : βo (eU u) = 1 ↔ (eU u) ∈ (W ⊓ Subgroup.center ↥H).subgroupOf W := by
          rw [← hβk]; exact MonoidHom.mem_ker.symm
        rw [hkerβ, Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          have := Subgroup.mem_center_iff.mp hx.2 ⟨g, hg⟩
          have h5 := congrArg Subtype.val this
          rw [← heU u]
          exact h5
        · intro hx
          refine Subgroup.mem_inf.mpr ⟨(eU u).2, Subgroup.mem_center_iff.mpr fun g => ?_⟩
          apply Subtype.ext
          have := Subgroup.mem_centralizer_iff.mp hx.2 (g : Ω) g.2
          show (g : Ω) * ((eU u : ↥W) : ↥H) = ((eU u : ↥W) : ↥H) * (g : Ω)
          rw [heU u]
          exact this
      β_equiv := by
        intro d u u' hu'
        exact hβe d (eU u) (eU u') (Subtype.ext (by
          show (((eU u' : ↥W) : ↥H) : Ω) = (d : Ω) * (((eU u : ↥W) : ↥H) : Ω) * (d : Ω)⁻¹
          rw [heU u', heU u]; exact hu')) }
  obtain ⟨-, -, -, -, -, hchi, -, -, -, hLin, hAlt⟩ :=
    natural_overgroup_recognizes_actual_chi0_block hn hcard hsetup hmod
  rw [twoResidual_eq_oddOrderSubgroup]
  refine ⟨hchi.1, ?_⟩
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · exact Or.inl ⟨n, hn1, (hLin hn1).2⟩
  · exact Or.inr (hAlt (le_antisymm hn1 hn)).2.2

end Ambient

end CFSG.Quasithin
