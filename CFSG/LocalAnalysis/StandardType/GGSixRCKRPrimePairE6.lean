module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairLabE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairFix
public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverSplit
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFFinite
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.ClassicalInvolution.ModelFacts
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

theorem rckA4_compRank_le {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) : compRank Ψ ≤ τ.rank := by
  unfold compRank
  calc Module.finrank ℚ ↥(Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ))
      ≤ Module.finrank ℚ (Fin τ.rank → ℚ) := Submodule.finrank_le _
    _ = τ.rank := by simp

theorem rckA4_tag {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (h6 : compRank Ψ = 6) :
    τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
  have := rckA4_compRank_le Ψ
  rw [h6] at this
  cases τ <;> simp [Tag.rank] at this ⊢

theorem rckA4_twistInner {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ} {i : KernelComponent χ}
    (hkind : twistKind ρ χ i = .inner) (h6 : compRank (componentRoots χ i) = 6)
    (hn : (componentRoots χ i).ncard = 72) :
    twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) := by
  by_contra hno
  simp [twistKind, hno, h6, hn] at hkind

theorem rckA4_cast_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : GGL) ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff GGL 2 p).1 h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm

theorem rckA4_preimage_center {G C : Type*} [Group G] [Group C] (Ψ : G →* C)
    (hperf : commutator G = ⊤) (hker : Ψ.ker ≤ Subgroup.center G) :
    (Subgroup.center C).comap Ψ ≤ Subgroup.center G := by
  intro x hx
  have hxc : ∀ y : G, Ψ y * Ψ x = Ψ x * Ψ y := fun y =>
    Subgroup.mem_center_iff.1 (Subgroup.mem_comap.1 hx) (Ψ y)
  have hc : ∀ y : G, ⁅x, y⁆ ∈ Subgroup.center G := fun y => hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (hxc y).symm)
  let f : G →* Subgroup.center G :=
    MonoidHom.mk' (fun y => ⟨⁅x, y⁆, hc y⟩) fun y y' => by
      apply Subtype.ext
      have h1 : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
        simp only [commutatorElement_def]; group
      have h2 : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by
        have := Subgroup.mem_center_iff.1 (hc y') y
        calc y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ * y * y⁻¹ := by rw [this]
          _ = ⁅x, y'⁆ := by group
      show ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆
      rw [h1, h2]
  have hle : commutator G ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : f y = 1 := hle (by rw [hperf]; trivial)
  have h' : ⁅x, y⁆ = 1 := congrArg Subtype.val hy
  exact (commutatorElement_eq_one_iff_commute.1 h').symm

theorem rckA4_mem_rootsOfFam {τ : Tag} {n : ℕ} (β : Fin n → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (k : Fin n) :
    β k ∈ rootsOfFam β Set.univ ∧ -β k ∈ rootsOfFam β Set.univ := by
  classical
  have hsum : ∑ b, ((fun b => if b = k then 1 else 0 : Fin n → ℕ) b : ℤ) • β b = β k := by
    simp [ite_smul, Finset.sum_ite_eq']
  exact ⟨⟨hroot k, fun b => if b = k then 1 else 0, fun _ _ => Set.mem_univ _,
    Or.inl hsum.symm⟩, ⟨IsRoot.neg (hroot k), fun b => if b = k then 1 else 0,
    fun _ _ => Set.mem_univ _, Or.inr (by rw [hsum])⟩⟩

theorem rckPairE6_holds
    : RCKPairE6 := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hshape hquasi
  classical
  obtain ⟨hkind, h6, hn⟩ := hshape
  have hτ := rckA4_tag h6
  have hinner := rckA4_twistInner hkind h6 hn
  have hpL := rckA4_cast_ne_zero hp hp2
  obtain ⟨β, hβroot, hΨβ, hgram, hedge, hframe⟩ := rckE6_labelled hτ S hp hpL hTp i h6 hn
  obtain ⟨σ, -, hfin, hcard, f, hf1, hf2, hf3, hz⟩ := rckInnerCoverExplicit S hT i hinner
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hs
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · have := S.hqpow.1
      rw [hq, h0, pow_zero] at this
      exact absurd this not_isPrimePow_one
    · exact h0
  have hg : 0 < h * s := Nat.mul_pos hh hs0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(fixSubfield σ) := hfin
  have hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ (h * s) := by rw [hcard, hq, pow_mul]
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  obtain ⟨Ψ, hΨrange, hΨker, hpin⟩ := innerRecogPinned_E6 (K := ↥(fixSubfield σ)) (p := 2) (f := h * s) hτ' hg
    hKcard β hβroot id (fun i j hij h1 h2 => hgram i j hij h1 h2)
    (fun i j hij => hframe (F := ↥(fixSubfield σ)) i j hij)
  have hadm : StatedLieAdmissible .E6 0 2 (h * s) := ⟨Nat.prime_two, hg, rfl⟩
  have hrk : 2 ≤ (ggU .E6 0 (h * s)).D.rank := by
    show 2 ≤ (e6Datum (GaloisField 2 (h * s))).rank
    show 2 ≤ 6
    norm_num
  haveI hfinM : Finite (ggU .E6 0 (h * s)).K :=
    ggU_finite_exc (Or.inr (Or.inl rfl)) ⟨hadm, hrk⟩
  obtain ⟨hcommM, -⟩ := ggU_perfect_lieModel hadm hrk
  have hsplit := CFSG.StandardType.LieOddCover.oddCentralSplit_ggU_pos (t := .E6) (n := 0)
    (f := h * s) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) hadm
  have hC : componentRootSpan (fixSubfield σ) (rootCharHom a) i = Ψ.range := by
    rw [hΨrange, Set.range_id]
    show rootSpan τ ↥(fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hΨβ]
  have hmem : ∀ x, Ψ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i := fun x => by
    rw [hC]; exact ⟨x, rfl⟩
  let Ψ' : (ggU .E6 0 (h * s)).K →* ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    (show (ggU .E6 0 (h * s)).K →* ModGL τ ↥(fixSubfield σ) from Ψ).codRestrict _ hmem
  have hΨ'surj : Function.Surjective Ψ' := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ Ψ.range := hC ▸ hc
    obtain ⟨x, rfl⟩ := hc'
    exact ⟨x, rfl⟩
  let φ : (ggU .E6 0 (h * s)).K →* ModGL τ GGL := f.comp Ψ'
  have hperfC : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i, componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    apply Subgroup.isPerfect_iff.1
    refine Group.isPerfect_def.2 ?_
    have h1 := congrArg (Subgroup.map Ψ') hcommM
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective Ψ' hΨ'surj] at h1
    rw [commutator_def]
    exact h1
  have hrangeφ : φ.range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΨ'surj, Subgroup.map_top]
  have hR : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf3 hperfC) hf1
  have hkerφ : φ.ker ≤ Subgroup.center (ggU .E6 0 (h * s)).K := by
    intro x hx
    have h2 : Ψ' x ∈ Subgroup.center _ := hf2 (show Ψ' x ∈ f.ker from hx)
    exact rckA4_preimage_center Ψ' hcommM (fun y hy => hΨker
      (show Ψ y = 1 from congrArg Subtype.val hy)) h2
  unfold RCKFrameCoverPair
  refine ⟨ggU .E6 0 (h * s), φ, rfl, ?_, hrangeφ.trans hR, hkerφ, hfinM,
    Group.isPerfect_def.2 hcommM, hsplit, ?_⟩
  · exact Or.inl ⟨.E6, 0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hadm, rfl⟩
  · intro hs1 β' hβ' _
    obtain ⟨z, -, hzstep, hfz, hzZ, -⟩ := hz hs1
    have hφx : ∀ x, φ x = z * baseChangeGL (fixSubfield σ).subtype (Ψ x) * z⁻¹ := fun x =>
      hfz (Ψ' x)
    have hmap : ∀ (Y : Subgroup (ggU .E6 0 (h * s)).K)
        (V : Subgroup (ModGL τ ↥(fixSubfield σ))),
        Y.map (show (ggU .E6 0 (h * s)).K →* ModGL τ ↥(fixSubfield σ) from Ψ) = V →
        Y.map φ = (V.map (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj z).toMonoidHom := by
      intro Y V hYV
      rw [← hYV, Subgroup.map_map, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun x => hφx x
    obtain ⟨hp0, hm0⟩ := hpin ⟨0, by norm_num⟩
    have hX := hmap _ _ hp0
    have hX' := hmap _ _ hm0
    have hφmodel : φ.range ≤ S.D.model := by
      rw [hrangeφ, hR]
      have hΓ : S.Γ ≤ S.D.model := (Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.mul_mem hx hy)
          (S.D.model.inv_mem hx)) (S.D.model.inv_mem hy) :
        ⁅S.D.model, S.D.model⁆ ≤ S.D.model)
      refine le_trans ?_ hΓ
      exact Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact S.Γ.mul_mem (S.Γ.mul_mem (S.Γ.mul_mem hx.2 hy.2) (S.Γ.inv_mem hx.2))
          (S.Γ.inv_mem hy.2)
    have hφC : φ.range ≤ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) := by
      rw [hrangeφ, hR]
      exact rationalComponent_le_torusGroup_sup_rootSpan_kernelRoots S i hs1
    have hmemβ := rckA4_mem_rootsOfFam β hβroot ⟨0, by norm_num⟩
    have hmem0 : β ⟨0, by norm_num⟩ ∈ componentRoots (rootCharHom a) i := by
      rw [hΨβ]; exact hmemβ.1
    have hmem0' : -β ⟨0, by norm_num⟩ ∈ componentRoots (rootCharHom a) i := by
      rw [hΨβ]; exact hmemβ.2
    obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .E6 0 2 (h * s) Nat.prime_two trivial hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .E6 0 2 (h * s) Nat.prime_two trivial hadm
    have hlongsingle := isLongestRoot_single .E6 0 2 (h * s) Nat.prime_two trivial hadm
    have hl0 := hlongsingle ⟨0, by show 0 < 6; norm_num⟩ trivial
    have hlβ := isLongestRoot_of_mem_roots_of_forall_single
      (modelUniv .E6 0 2 (h * s) Nat.prime_two).D rfl (fun k => hlongsingle k trivial) hβ'
    obtain ⟨u, hu1, hu2⟩ := exists_map_conj_rankOne_of_isLongest hct hirr hratio hl0 hlβ
    obtain ⟨z', hz'mem, hst1, hst2, hfx1, hfx2⟩ := rckPair_assemble S σ z hzZ hzstep
      (H := torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
      (X := (ggU .E6 0 (h * s)).D.rootGroup) φ hφmodel hφC
      (hβroot ⟨0, by norm_num⟩) hmem0 hmem0' hX hX' u hu1 hu2
    exact ⟨β ⟨0, by norm_num⟩, hmem0, z', hz'mem, hst1, hst2, hfx1, hfx2⟩

end CFSG.StandardType.RCKRP

end
