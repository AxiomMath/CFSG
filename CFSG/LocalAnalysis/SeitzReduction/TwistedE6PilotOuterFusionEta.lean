module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotOuterFusionBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotClasses

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.SeitzReduction.E6Pilot (a2Roots a2Gen)

local instance twistedE6PilotOuterFusionEtaNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotOuterFusionEtaNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotOuterFusionEtaNeZeroReeF4 : NeZero ReeTag.F4.tag.rank :=
  ⟨by decide⟩

section ClassTU

variable {K : Type} [Field K]
  [CharP K 2]


@[expose] noncomputable def classTU {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    Set (graphFixedRootGroup TwistTag.E6 K σ) :=
  {x | IsConj x (repXC hσσ 0) ∨ IsConj x (repXC hσσ 1)}

end ClassTU

section F4

theorem dualRoot_single_one_F4 :
    ReeTag.F4.dualRoot (Pi.single 1 1 : Fin ReeTag.F4.tag.rank → ℤ) = Pi.single 2 1 := by
  decide

theorem dualRoot_single_two_F4 :
    ReeTag.F4.dualRoot (Pi.single 2 1 : Fin ReeTag.F4.tag.rank → ℤ) = Pi.single 1 1 := by
  decide

variable
  {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem finiteExceptionalAut_pinnedX_a23 {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : γ = Pi.single 1 1 ∨ γ = Pi.single 2 1) {d : k} (hd : d ≠ 0) :
    ∃ γ' : Fin ReeTag.F4.tag.rank → ℤ, (γ' = Pi.single 1 1 ∨ γ' = Pi.single 2 1) ∧
      ∃ d' : k, d' ≠ 0 ∧
        ReeTag.F4.finiteExceptionalAut k ⟨pinnedX ReeTag.F4.tag k γ d, pinnedX_mem_adjointGroup γ d⟩ =
          ⟨pinnedX ReeTag.F4.tag k γ' d', pinnedX_mem_adjointGroup γ' d'⟩ := by
  have hroot : IsRoot ReeTag.F4.tag γ := by
    rcases hγ with h | h <;> rw [h] <;> exact isRoot_single _ _
  have hdual : ReeTag.F4.dualRoot γ = Pi.single 1 1 ∨ ReeTag.F4.dualRoot γ = Pi.single 2 1 := by
    rcases hγ with h | h <;> rw [h]
    · exact Or.inr dualRoot_single_one_F4
    · exact Or.inl dualRoot_single_two_F4
  have hsl : γ ∈ ReeTag.F4.shortRoots ∪ ReeTag.F4.longRoots := by
    rw [ReeTag.shortRoots_union_longRoots]
    exact hroot
  rcases hsl with hs | hl
  · exact ⟨_, hdual, d ^ 2, pow_ne_zero 2 hd, finiteExceptionalAut_pinnedX_short hs d⟩
  · exact ⟨_, hdual, d, hd, finiteExceptionalAut_pinnedX_long hl d⟩

theorem finiteExceptionalAut_pow_pinnedX_a23 (n : ℕ) {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : γ = Pi.single 1 1 ∨ γ = Pi.single 2 1) {d : k} (hd : d ≠ 0) :
    ∃ γ' : Fin ReeTag.F4.tag.rank → ℤ, (γ' = Pi.single 1 1 ∨ γ' = Pi.single 2 1) ∧
      ∃ d' : k, d' ≠ 0 ∧
        (ReeTag.F4.finiteExceptionalAut k ^ n)
            ⟨pinnedX ReeTag.F4.tag k γ d, pinnedX_mem_adjointGroup γ d⟩ =
          ⟨pinnedX ReeTag.F4.tag k γ' d', pinnedX_mem_adjointGroup γ' d'⟩ := by
  induction n generalizing γ d with
  | zero => exact ⟨γ, hγ, d, hd, rfl⟩
  | succ n ih =>
    obtain ⟨γ₁, hγ₁, d₁, hd₁, h₁⟩ := finiteExceptionalAut_pinnedX_a23 hγ hd
    obtain ⟨γ₂, hγ₂, d₂, hd₂, h₂⟩ := ih hγ₁ hd₁
    refine ⟨γ₂, hγ₂, d₂, hd₂, ?_⟩
    rw [pow_succ, MulAut.mul_apply, h₁, h₂]

theorem exists_conj_pinnedX_a23_of_mulAut {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (β : MulAut (adjointGroup Tag.F4 k)) {d : k} (hd : d ≠ 0) :
    ∃ γ' : Fin Tag.F4.rank → ℤ, (γ' = Pi.single 1 1 ∨ γ' = Pi.single 2 1) ∧
      ∃ d' : k, d' ≠ 0 ∧ ∃ g : adjointGroup Tag.F4 k,
        β ⟨pinnedX Tag.F4 k (Pi.single 2 1) d, pinnedX_mem_adjointGroup _ d⟩ =
          g * ⟨pinnedX Tag.F4 k γ' d', pinnedX_mem_adjointGroup γ' d'⟩ * g⁻¹ := by
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf k hk
  obtain ⟨⟨g, n⟩, hgn, -⟩ := hNF β
  obtain ⟨γ', hγ', d', hd', h⟩ := finiteExceptionalAut_pow_pinnedX_a23 (n : ℕ)
    (Or.inr rfl) hd
  refine ⟨γ', hγ', d', hd', g, ?_⟩
  have h' := congrArg (fun z => (MulAut.conj g) z) h
  rw [hgn]
  exact h'

end F4

section Torus

theorem permLattice_single_three :
    permLattice TwistTag.E6.perm (Pi.single 3 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single 3 1 := by
  decide

theorem permLattice_single_two_add_four :
    permLattice TwistTag.E6.perm (Pi.single 2 1 + Pi.single 4 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      Pi.single 2 1 + Pi.single 4 1 := by
  decide

theorem iform_single_two_add_four :
    iform (Pi.single 2 1 + Pi.single 4 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single 2 1) = 2 ∧
      iform (Pi.single 2 1 + Pi.single 4 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single 4 1) = 2 := by
  decide

variable
  {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K →+* K}

theorem isConj_repXC_zero_of_pinnedX (hσσ : ∀ c, σ (σ c) = c) {a : K} (ha : a ≠ 0)
    (haσ : σ a = a)
    (hmem : pinnedX TwistTag.E6.tag K (Pi.single 3 1) a ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    IsConj (⟨_, hmem⟩ : graphFixedRootGroup TwistTag.E6 K σ) (repXC hσσ 0) := by
  obtain ⟨h, hh, -, hconj⟩ := exists_twistedE6_torus_conj_frame_prod σ
    (F := [Pi.single 3 1]) (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      exact ⟨isRoot_single _ _, permLattice_single_three⟩)
    (List.pairwise_singleton _ _) (fun _ => a) (fun γ _ => ⟨ha, haσ⟩)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hconj
  refine isConj_iff.2 ⟨⟨h, hh⟩, Subtype.ext ?_⟩
  change h * pinnedX TwistTag.E6.tag K (Pi.single 3 1) a * h⁻¹ = repX K 0
  rw [hconj]
  rfl

theorem isConj_repYC_one_of_pinnedX (hσσ : ∀ c, σ (σ c) = c) {a : K} (ha : a ≠ 0)
    (haσ : σ a = a)
    (hmem : pinnedX TwistTag.E6.tag K (Pi.single 2 1) a * pinnedX TwistTag.E6.tag K (Pi.single 4 1) a ∈
      graphFixedRootGroup TwistTag.E6 K σ) :
    IsConj (⟨_, hmem⟩ : graphFixedRootGroup TwistTag.E6 K σ) (repYC hσσ 1) := by
  obtain ⟨b, hb2, hbσ⟩ := exists_sq_eq_of_sigma_fixed σ (u := (Units.mk0 a ha)⁻¹)
    (Units.ext (by simp [haσ]))
  have hhC := frameTorusElt_mem_graphFixedRootGroup σ permLattice_single_two_add_four hbσ
  set h := frameTorusElt TwistTag.E6.tag K (Pi.single 2 1 + Pi.single 4 1) b with hdef
  have hcoef : (((b ^ (2 : ℤ) : Kˣ)) : K) * a = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hb2, Units.val_inv_eq_inv_val,
      Units.val_mk0, inv_mul_cancel₀ ha]
  have h3 : h * pinnedX TwistTag.E6.tag K (Pi.single 2 1) a * h⁻¹ =
      pinnedX TwistTag.E6.tag K (Pi.single 2 1) 1 := by
    rw [hdef, frameTorusElt_conj_pinnedX _ _ (isRoot_single _ _), iform_single_two_add_four.1,
      hcoef]
  have h5 : h * pinnedX TwistTag.E6.tag K (Pi.single 4 1) a * h⁻¹ =
      pinnedX TwistTag.E6.tag K (Pi.single 4 1) 1 := by
    rw [hdef, frameTorusElt_conj_pinnedX _ _ (isRoot_single _ _), iform_single_two_add_four.2,
      hcoef]
  refine isConj_iff.2 ⟨⟨h, hhC⟩, Subtype.ext ?_⟩
  change h * (pinnedX TwistTag.E6.tag K (Pi.single 2 1) a *
    pinnedX TwistTag.E6.tag K (Pi.single 4 1) a) * h⁻¹ = repY K 1
  rw [show h * (pinnedX TwistTag.E6.tag K (Pi.single 2 1) a *
      pinnedX TwistTag.E6.tag K (Pi.single 4 1) a) * h⁻¹ =
      (h * pinnedX TwistTag.E6.tag K (Pi.single 2 1) a * h⁻¹) *
        (h * pinnedX TwistTag.E6.tag K (Pi.single 4 1) a * h⁻¹) by group, h3, h5]
  rfl

end Torus

section Eta

theorem permLattice_single_two :
    permLattice TwistTag.E6.perm (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single 4 1 := by
  decide

theorem single_two_mem_a2Roots :
    (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) ∈ a2Roots := by
  decide

theorem orbitWord_f4FoldedIndex_one_two :
    TwistTag.E6.orbitWord (f4FoldedIndex 1) = [3] ∧ TwistTag.E6.orbitWord (f4FoldedIndex 2) = [2, 4] :=
  by decide

theorem baseChangeGL_f4OrbitXUnit_one_two
    {k K : Type} [Field k] [Field K] (ι : k →+* K) (d : k) :
    baseChangeGL ι (f4OrbitXUnit k 1 d) = pinnedX TwistTag.E6.tag K (Pi.single 3 1) (ι d) ∧
      baseChangeGL ι (f4OrbitXUnit k 2 d) = pinnedX TwistTag.E6.tag K (Pi.single 2 1) (ι d) *
        pinnedX TwistTag.E6.tag K (Pi.single 4 1) (ι d) := by
  obtain ⟨h1, h2⟩ := orbitWord_f4FoldedIndex_one_two
  constructor
  · rw [f4OrbitXUnit, h1, List.map_singleton, List.prod_singleton, ← pinnedX_single,
      baseChangeGL_pinnedX]
  · rw [f4OrbitXUnit, h2, List.map_cons, List.map_singleton, List.prod_cons, List.prod_singleton,
      map_mul, ← pinnedX_single, ← pinnedX_single, baseChangeGL_pinnedX, baseChangeGL_pinnedX]


theorem twistedFusionIn_etaAut {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k] [Field K] [CharP K 2]
    [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    TwistedFusionIn (etaAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)) := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : Finite K := finite_of_card hK
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  have : CharP k ReeTag.F4.prime := ‹CharP k 2›
  have h2k : (2 : k) = 0 := CharP.cast_eq_zero k 2
  set hσσ := apply_apply_eq hK hσ with hσσdef
  set ι := algebraMap k K with hιdef
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀def
  set J := (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι) with hJdef
  obtain ⟨-, ⟨hcan, e, he⟩⟩ := even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨η', hη', -, hJC, hfixJ, -⟩ := hcan
  have hηe : η' = etaAut σ hσσ := MulEquiv.ext fun g => Subtype.ext (by rw [hη', coe_etaAut])
  set F := (etaAut σ hσσ).toMonoidHom.eqLocus (MonoidHom.id C₀) with hFdef
  have hmemF : ∀ g : C₀, g ∈ F ↔ (g : ModGL TwistTag.E6.tag K) ∈ J := fun g => by
    rw [← hfixJ g, hηe]
    rfl
  have hFJ : F = J.subgroupOf C₀ := by
    ext g
    rw [hmemF, mem_subgroupOf]
  set Φ : F ≃* adjointGroup Tag.F4 k :=
    (MulEquiv.subgroupCongr hFJ).trans ((subgroupOfEquivOfLe hJC).trans e) with hΦdef
  have hΦ : ∀ (x : F) (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k)),
      ((x : C₀) : ModGL TwistTag.E6.tag K) = baseChangeGL ι g →
        (Φ x : ModGL Tag.F4 k) = e6FixedToF4 k g := fun x g h => he g _ h
  have hJorb : ∀ (j : Fin Tag.F4.rank) (d : k), baseChangeGL ι (f4OrbitXUnit k j d) ∈ J :=
    fun j d => ⟨_, f4OrbitXUnit_mem j d, rfl⟩
  let orbF : Fin Tag.F4.rank → k → F := fun j d =>
    ⟨⟨_, hJC (hJorb j d)⟩, (hmemF _).2 (hJorb j d)⟩
  have hΦorb : ∀ (j : Fin Tag.F4.rank) (d : k), Φ (orbF j d) =
      ⟨pinnedX Tag.F4 k (Pi.single j 1) d, pinnedX_mem_adjointGroup _ _⟩ := fun j d =>
    Subtype.ext ((hΦ _ ⟨_, f4OrbitXUnit_mem j d⟩ rfl).trans
      (by rw [e6FixedToF4_f4OrbitXUnit h2k j d]; exact (pinnedX_single Tag.F4 k j d).symm))
  obtain ⟨c, hc⟩ := exists_apply_ne hf hK hσ
  have hσfix : σ (c + σ c) = c + σ c := by rw [map_add, hσσ, add_comm]
  have hne : c + σ c ≠ 0 := fun h => hc (CharTwo.add_eq_zero.1 h).symm
  obtain ⟨d, hd⟩ : c + σ c ∈ Set.range ι := by
    refine mem_range_algebraMap_of_pow_card_eq ?_
    rw [hk, ← hσ, hσfix]
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact hne hd.symm
  have hβ3 := single_two_mem_a2Roots
  set m₀ : C₀ := ⟨a2Gen σ (Pi.single 2 1) c, coe_a2Gen_mem σ hσσ hβ3 c⟩ with hm₀
  have hy₀ : ((orbF 2 d : C₀) : ModGL TwistTag.E6.tag K) =
      a2Gen σ (Pi.single 2 1) (c + σ c) := by
    change baseChangeGL ι (f4OrbitXUnit k 2 d) = _
    rw [(baseChangeGL_f4OrbitXUnit_one_two ι d).2, E6Pilot.coe_a2Gen, permLattice_single_two, hd,
      hσfix]
  refine ⟨?_, m₀, orbF 2 d, ?_, ?_, fun β => ?_⟩
  ·
    have : Group.IsPerfect (adjointGroup Tag.F4 k) :=
      CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 k
    have : Group.IsPerfect F := Group.IsPerfect.ofSurjective (f := Φ.symm.toMonoidHom)
      Φ.symm.surjective
    exact Subgroup.isPerfect_iff.1 this
  ·
    intro h1
    have h2 : orbF 2 d = 1 := Subtype.ext h1
    have h3 : (⟨pinnedX Tag.F4 k (Pi.single 2 1) d, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup Tag.F4 k) = 1 := by
      rw [← hΦorb 2 d, h2, map_one]
    have h4 : pinnedX Tag.F4 k (Pi.single 2 1) d = pinnedX Tag.F4 k (Pi.single 2 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h3
    exact hd0 (pinnedX_injective (τ := Tag.F4) (R := k) _ h4)
  ·
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_etaAut, hm₀]
    change (diagramMap TwistTag.E6 K * (a2Gen σ (Pi.single 2 1) c : ModGL TwistTag.E6.tag K) *
      (diagramMap TwistTag.E6 K)⁻¹)⁻¹ * a2Gen σ (Pi.single 2 1) c = _
    rw [diagramMap_conj_a2Gen σ hσσ hβ3 c, hy₀]
    have key : (a2Gen σ (Pi.single 2 1) (σ c))⁻¹ * a2Gen σ (Pi.single 2 1) c =
        a2Gen σ (Pi.single 2 1) (c + σ c) := by
      rw [inv_mul_eq_iff_eq_mul, ← E6Pilot.a2Gen_add σ hβ3]
      congr 1
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    exact congrArg Subtype.val key
  ·
    set β' : MulAut (adjointGroup Tag.F4 k) := MulAut.congr Φ β with hβ'
    obtain ⟨γ', hγ', d', hd', g, hg⟩ := exists_conj_pinnedX_a23_of_mulAut hf hk β' hd0
    have hβy : β (orbF 2 d) = Φ.symm (β' (Φ (orbF 2 d))) := by
      rw [hβ', MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hg' : β' (Φ (orbF 2 d)) = g *
        ⟨pinnedX Tag.F4 k γ' d', pinnedX_mem_adjointGroup _ _⟩ * g⁻¹ := by
      rw [hΦorb 2 d]
      exact hg
    rw [hg', map_mul, map_mul, map_inv] at hβy
    have hι0 : ι d' ≠ 0 := fun h => hd' ((map_eq_zero_iff ι ι.injective).1 h)
    have hισ : σ (ι d') = ι d' := by
      have : Fintype k := Fintype.ofFinite k
      rw [hσ, ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hconj : ∀ j : Fin Tag.F4.rank, γ' = Pi.single j 1 →
        IsConj ((β (orbF 2 d) : F) : C₀) ((orbF j d' : F) : C₀) := by
      intro j hj
      subst hj
      have hsymm : Φ.symm ⟨pinnedX Tag.F4 k (Pi.single j 1) d', pinnedX_mem_adjointGroup _ _⟩ =
          orbF j d' := (Φ.symm_apply_eq).2 (hΦorb j d').symm
      rw [hβy, hsymm]
      refine isConj_iff.2 ⟨((Φ.symm g : F) : C₀)⁻¹, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rcases hγ' with h1 | h2
    ·
      have hmem : pinnedX TwistTag.E6.tag K (Pi.single 3 1) (ι d') ∈ C₀ := by
        rw [← (baseChangeGL_f4OrbitXUnit_one_two ι d').1]
        exact hJC (hJorb 1 d')
      have he : ((orbF 1 d' : F) : C₀) = ⟨_, hmem⟩ :=
        Subtype.ext (baseChangeGL_f4OrbitXUnit_one_two ι d').1
      left
      exact (hconj 1 h1).trans (he ▸ isConj_repXC_zero_of_pinnedX hσσ hι0 hισ hmem)
    ·
      have hmem : pinnedX TwistTag.E6.tag K (Pi.single 2 1) (ι d') *
          pinnedX TwistTag.E6.tag K (Pi.single 4 1) (ι d') ∈ C₀ := by
        rw [← (baseChangeGL_f4OrbitXUnit_one_two ι d').2]
        exact hJC (hJorb 2 d')
      have he : ((orbF 2 d' : F) : C₀) = ⟨_, hmem⟩ :=
        Subtype.ext (baseChangeGL_f4OrbitXUnit_one_two ι d').2
      right
      exact (hconj 2 h2).trans ((he ▸ isConj_repYC_one_of_pinnedX hσσ hι0 hισ hmem).trans
        (isConj_repXC_repYC hσσ 1).symm)

end Eta

end CFSG.SeitzReduction.TwistedE6Pilot
