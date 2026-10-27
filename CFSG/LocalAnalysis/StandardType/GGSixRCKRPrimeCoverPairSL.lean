module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSL

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.Classical2 CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

section Frame

variable
  {τ : Tag} {L : Type} [Field L] {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
  {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

private theorem frame_conj_pinnedX_step (hψ : IsSLFrame ψ σ) (z : ModGL τ L) (σQ : L ≃+* L)
    (F : ModGL τ L →* ModGL τ L)
    (hF : ∀ X : SL(ν, L), F (z * ψ X * z⁻¹) =
      z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * z⁻¹)
    {j k : Fin ν} (hjk : j ≠ k) :
    ∃ ε : Lˣ, (∀ t : L, ψ (Matrix.SpecialLinearGroup.transvection hjk t) =
        pinnedX τ L (σ j k) ((ε : L) * t)) ∧
      (∀ c : L, pinnedX τ L (σ j k) c =
        ψ (Matrix.SpecialLinearGroup.transvection hjk ((ε⁻¹ : Lˣ) * c))) ∧
      ∀ c : L, F ((MulAut.conj z).toMonoidHom (pinnedX τ L (σ j k) c)) =
        (MulAut.conj z).toMonoidHom (pinnedX τ L (σ j k)
          ((ε : L) * σQ ((ε⁻¹ : Lˣ) * c))) := by
  obtain ⟨ε, hε⟩ := hψ.transv j k hjk
  have hframeU : ∀ c : L, pinnedX τ L (σ j k) c =
      ψ (Matrix.SpecialLinearGroup.transvection hjk ((ε⁻¹ : Lˣ) * c)) := by
    intro c
    rw [hε, ← mul_assoc, Units.mul_inv, one_mul]
  refine ⟨ε, hε, hframeU, ?_⟩
  intro c
  rw [hframeU c]
  have h1 : F ((MulAut.conj z).toMonoidHom
      (ψ (Matrix.SpecialLinearGroup.transvection hjk ((ε⁻¹ : Lˣ) * c)))) =
      (MulAut.conj z).toMonoidHom
        (ψ (Matrix.SpecialLinearGroup.transvection hjk (σQ.toRingHom ((ε⁻¹ : Lˣ) * c)))) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Matrix.SpecialLinearGroup.map_transvection] using
      hF (Matrix.SpecialLinearGroup.transvection hjk ((ε⁻¹ : Lˣ) * c))
  rw [h1, hε]
  rfl

theorem frame_conj_rootSubgroup_map_eq (hψ : IsSLFrame ψ σ) (z : ModGL τ L) (σQ : L ≃+* L)
    (F : ModGL τ L →* ModGL τ L)
    (hF : ∀ X : SL(ν, L), F (z * ψ X * z⁻¹) =
      z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * z⁻¹)
    {j k : Fin ν} (hjk : j ≠ k) :
    ((rootSubgroup τ L (σ j k)).map (MulAut.conj z).toMonoidHom).map F =
      (rootSubgroup τ L (σ j k)).map (MulAut.conj z).toMonoidHom := by
  obtain ⟨ε, hε, hframeU, hstep_formula⟩ := frame_conj_pinnedX_step hψ z σQ F hF hjk
  have hcomp : ∀ c : L,
      (ε : L) * σQ ((ε⁻¹ : Lˣ) * ((ε : L) * σQ.symm ((ε⁻¹ : Lˣ) * c))) = c := by
    intro c
    have harg : ((ε⁻¹ : Lˣ) : L) * ((ε : L) * σQ.symm ((ε⁻¹ : Lˣ) * c)) =
        σQ.symm ((ε⁻¹ : Lˣ) * c) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [harg, σQ.apply_symm_apply, ← mul_assoc, Units.mul_inv, one_mul]
  apply le_antisymm
  · rintro y ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).mp hu
    rw [hstep_formula c]
    exact Subgroup.mem_map.mpr ⟨pinnedX τ L (σ j k) ((ε : L) * σQ ((ε⁻¹ : Lˣ) * c)),
      mem_rootSubgroup.mpr ⟨_, rfl⟩, rfl⟩
  · rintro y ⟨u, hu, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).mp hu
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj z).toMonoidHom
        (pinnedX τ L (σ j k) ((ε : L) * σQ.symm ((ε⁻¹ : Lˣ) * c))), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨pinnedX τ L (σ j k)
        ((ε : L) * σQ.symm ((ε⁻¹ : Lˣ) * c)), mem_rootSubgroup.mpr ⟨_, rfl⟩, rfl⟩
    · rw [hstep_formula ((ε : L) * σQ.symm ((ε⁻¹ : Lˣ) * c)), hcomp c]

theorem frame_conj_rootSubgroup_inf_eqLocus (hψ : IsSLFrame ψ σ) (z : ModGL τ L)
    (σQ : L ≃+* L) (F : ModGL τ L →* ModGL τ L)
    (hF : ∀ X : SL(ν, L), F (z * ψ X * z⁻¹) =
      z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * z⁻¹)
    {j k : Fin ν} (hjk : j ≠ k) :
    (rootSubgroup τ L (σ j k)).map (MulAut.conj z).toMonoidHom ⊓ F.eqLocus (MonoidHom.id _) =
      (Matrix.SpecialLinearGroup.transvectionHom (A := ↥(fixSubfield σQ)) hjk).range.map
        ((MulAut.conj z).toMonoidHom.comp
          (ψ.comp (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype))) := by
  obtain ⟨ε, hε, hframeU, hstep_formula⟩ := frame_conj_pinnedX_step hψ z σQ F hF hjk
  apply le_antisymm
  · rintro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxF⟩ := hx
    obtain ⟨u, hu, rfl⟩ := hxU
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).mp hu
    change F ((MulAut.conj z).toMonoidHom (pinnedX τ L (σ j k) c)) =
      (MulAut.conj z).toMonoidHom (pinnedX τ L (σ j k) c) at hxF
    rw [hstep_formula c] at hxF
    have hinj : Function.Injective ((MulAut.conj z).toMonoidHom) := (MulAut.conj z).injective
    have hpin : pinnedX τ L (σ j k) ((ε : L) * σQ ((ε⁻¹ : Lˣ) * c)) =
        pinnedX τ L (σ j k) c := hinj hxF
    have h2 : (ε : L) * σQ ((ε⁻¹ : Lˣ) * c) = c :=
      pinnedX_injective τ L (σ j k) hpin
    set t : L := (ε⁻¹ : Lˣ) * c with ht
    have h2t : (ε : L) * σQ t = c := h2
    have hct : c = (ε : L) * t := by
      rw [ht, ← mul_assoc, Units.mul_inv, one_mul]
    have hσt : σQ t = t := by
      apply mul_left_cancel₀ (Units.ne_zero ε)
      rw [hct] at h2t
      exact h2t
    have htK : t ∈ fixSubfield σQ := (mem_fixSubfield σQ).mpr hσt
    have hxψ : (MulAut.conj z).toMonoidHom (pinnedX τ L (σ j k) c) =
        (MulAut.conj z).toMonoidHom (ψ (Matrix.SpecialLinearGroup.transvection hjk t)) := by
      rw [hframeU c, ← ht]
    let k' : ↥(fixSubfield σQ) := ⟨t, htK⟩
    refine Subgroup.mem_map.mpr ⟨Matrix.SpecialLinearGroup.transvectionHom hjk
      (Multiplicative.ofAdd k'), ?_, ?_⟩
    · exact ⟨Multiplicative.ofAdd k', rfl⟩
    · rw [hxψ]
      simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
        Matrix.SpecialLinearGroup.map_transvection, toAdd_ofAdd]
      rfl
  · rintro x ⟨Y, hY, rfl⟩
    obtain ⟨c, rfl⟩ := hY
    rw [Matrix.SpecialLinearGroup.transvectionHom_apply]
    set t : L := ((Multiplicative.toAdd c : ↥(fixSubfield σQ)) : L) with ht
    have htK : t ∈ fixSubfield σQ := (Multiplicative.toAdd c).2
    have hxψ : (MulAut.conj z).toMonoidHom
        (ψ ((Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype)
          (Matrix.SpecialLinearGroup.transvection hjk (Multiplicative.toAdd c)))) =
        (MulAut.conj z).toMonoidHom (ψ (Matrix.SpecialLinearGroup.transvection hjk t)) := by
      rw [Matrix.SpecialLinearGroup.map_transvection, ht]
      rfl
    have hψU : ψ (Matrix.SpecialLinearGroup.transvection hjk t) ∈ rootSubgroup τ L (σ j k) :=
      mem_rootSubgroup.mpr ⟨(ε : L) * t, (hε t).symm⟩
    have hUmem : (MulAut.conj z).toMonoidHom (ψ (Matrix.SpecialLinearGroup.transvection hjk t)) ∈
        (rootSubgroup τ L (σ j k)).map (MulAut.conj z).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, hψU, rfl⟩
    have hfixed : F ((MulAut.conj z).toMonoidHom
        (ψ (Matrix.SpecialLinearGroup.transvection hjk t))) =
        (MulAut.conj z).toMonoidHom (ψ (Matrix.SpecialLinearGroup.transvection hjk t)) := by
      have hσt : σQ t = t := (mem_fixSubfield σQ).mp htK
      have hσt' : σQ.toRingHom t = t := hσt
      have hF' := hF (Matrix.SpecialLinearGroup.transvection hjk t)
      rw [Matrix.SpecialLinearGroup.map_transvection, hσt'] at hF'
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hF'
    simp only [MonoidHom.comp_apply]
    rw [hxψ]
    refine Subgroup.mem_inf.mpr ⟨hUmem, ?_⟩
    change F ((MulAut.conj z).toMonoidHom
      (ψ (Matrix.SpecialLinearGroup.transvection hjk t))) =
      (MulAut.conj z).toMonoidHom (ψ (Matrix.SpecialLinearGroup.transvection hjk t))
    exact hfixed

end Frame

theorem transvectionHom_range_map_ringEquiv {F K : Type} [Field F] [Field K] (e : F ≃+* K)
    {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    (Matrix.SpecialLinearGroup.transvectionHom (A := F) hjk).range.map
        (Matrix.SpecialLinearGroup.map (e : F →+* K)) =
      (Matrix.SpecialLinearGroup.transvectionHom (A := K) hjk).range := by
  ext b
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (e (Multiplicative.toAdd c)), ?_⟩
    rw [Matrix.SpecialLinearGroup.transvectionHom_apply,
      Matrix.SpecialLinearGroup.transvectionHom_apply,
      Matrix.SpecialLinearGroup.map_transvection]
    simp
  · rintro ⟨c, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.transvection hjk (e.symm (Multiplicative.toAdd c)),
      ⟨Multiplicative.ofAdd (e.symm (Multiplicative.toAdd c)), ?_⟩, ?_⟩
    · rw [Matrix.SpecialLinearGroup.transvectionHom_apply]
      simp
    · rw [Matrix.SpecialLinearGroup.map_transvection,
        Matrix.SpecialLinearGroup.transvectionHom_apply]
      simp

section Model


theorem carrierSL_rckADEModel {m g : ℕ} (hm : 2 ≤ m) (hg : 0 < g) :
    RCKADEModel (ggU .PSL (m + 1) g) g := by
  have hne1 : (m + 1, 2 ^ g) ≠ (2, 2) := by
    intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  have hne2 : (m + 1, 2 ^ g) ≠ (2, 3) := by
    intro h
    have h3 : 2 ^ g = 3 := congrArg Prod.snd h
    have hdvd : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
    rw [h3] at hdvd
    omega
  refine Or.inl ⟨.PSL, m + 1, Or.inl rfl, ?_, rfl⟩
  change Nat.Prime 2 ∧ 1 ≤ g ∧ 2 ≤ m + 1 ∧ (m + 1, 2 ^ g) ≠ (2, 2) ∧
    (m + 1, 2 ^ g) ≠ (2, 3)
  exact ⟨Nat.prime_two, by omega, by omega, hne1, hne2⟩

private theorem ggU_PSL_rootGroup_pair {m g : ℕ} {β : Fin ((ggU .PSL (m + 1) g).D.rank) → ℤ}
    (hβ : β ∈ (ggU .PSL (m + 1) g).D.roots) :
    ∃ (j k : Fin (m + 1)) (hjk : j ≠ k),
      (ggU .PSL (m + 1) g).D.rootGroup β =
        SpecialLinear.rootSubgroup m (GaloisField 2 g) hjk ∧
      (ggU .PSL (m + 1) g).D.rootGroup (-β) =
        SpecialLinear.rootSubgroup m (GaloisField 2 g) hjk.symm := by
  let β' : Fin m → ℤ := β
  have hβ'' : β' ∈ roots (SpecialLinear.isFiniteType_A m) ∅ := by
    change β' ∈ (SpecialLinear.rootDatum m (GaloisField 2 g)).roots
    exact hβ
  obtain ⟨hjk, hβstd⟩ := SpecialLinear.idx_spec (m := m) hβ''
  have hβnegstd : SpecialLinear.toStd m (-β') = Pi.single (SpecialLinear.idx m β').2 1 -
      Pi.single (SpecialLinear.idx m β').1 1 := by
    rw [SpecialLinear.toStd_neg, hβstd, neg_sub]
  refine ⟨(SpecialLinear.idx m β').1, (SpecialLinear.idx m β').2, hjk, ?_, ?_⟩
  · change SpecialLinear.rootGroup m (GaloisField 2 g) β' = _
    exact SpecialLinear.rootGroup_eq (m := m) (F := GaloisField 2 g) hjk hβstd
  · change SpecialLinear.rootGroup m (GaloisField 2 g) (-β') = _
    exact SpecialLinear.rootGroup_eq (m := m) (F := GaloisField 2 g) hjk.symm hβnegstd

theorem rckPairSLInner_holds :
    RCKPairSLInner := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hcls hQS
  obtain ⟨hkind, h2, hn⟩ := hcls
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp
      (carrierSL_natCast_ne_zero hp hp2) hTp i h2 hn
  have hνr := carrierSL_nu_eq i hν hψ hκ hnorm hΨ hn
  obtain ⟨π, hπ⟩ := splitShape_of_twistKind_inner S hT i hkind hν hψ hκ hnorm hΨ
  have hh : 0 < h := carrierSL_exp_pos S hq
  obtain ⟨σQ, hσQ, z, hz, hzF, f, hfrange, hfker, -, hf1⟩ :=
    split_exists_hom_untwist S hT i hν hψ hΨ π hπ Nat.prime_two inferInstance hh hq
  have hs0 : 0 < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    (outer_componentOrbitLength_spec S hT i).1
  have hhs : 0 < h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    Nat.mul_pos hh hs0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, hKcard⟩ := finite_card_fixSubfield (L := GGL) (r := 2)
    (n := h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) hhs σQ hσQ
  obtain ⟨e⟩ := carrierSL_fieldEquiv hhs hKcard
  subst hνr
  obtain ⟨_, hfin, hperf, hodd, _⟩ := carrierSL_ggU_facts (m :=
    compRank (componentRoots (rootCharHom a) i))
    (g := h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) h2 hhs
  let φ : (ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1)
      (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))).K →* ModGL τ GGL :=
    f.comp (Matrix.SpecialLinearGroup.map (e : GaloisField 2
      (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) →+* ↥(fixSubfield σQ)))
  have htr := carrierSL_transport e f hfker
  refine ⟨_, φ, rfl, carrierSL_rckADEModel h2 hhs, htr.1.trans hfrange, htr.2.1, hfin, hperf,
    hodd, ?_⟩
  intro hs1 β hβ _
  obtain ⟨j, k, hjk, hrootβ, hrootβneg⟩ := ggU_PSL_rootGroup_pair hβ
  have hF : ∀ X : SL(compRank (componentRoots (rootCharHom a) i) + 1, GGL),
      S.D.step (z * ψ X * z⁻¹) =
        z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * z⁻¹ := by
    intro X
    simpa [hs1, iterHom_succ, iterHom_zero] using hzF X
  have hfeq : f = (MulAut.conj z).toMonoidHom.comp
      (ψ.comp (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype)) := by
    apply MonoidHom.ext
    intro X
    change f X = z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹
    exact hf1 hs1 X
  have hmain : ((ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1)
      (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))).D.rootGroup β).map φ =
      (Matrix.SpecialLinearGroup.transvectionHom (A := ↥(fixSubfield σQ)) hjk).range.map
        ((MulAut.conj z).toMonoidHom.comp
          (ψ.comp (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype))) := by
    rw [hrootβ]
    change (Matrix.SpecialLinearGroup.transvectionHom (A := GaloisField 2
      (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) hjk).range.map
      (f.comp (Matrix.SpecialLinearGroup.map (e : GaloisField 2
        (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) →+*
          ↥(fixSubfield σQ)))) = _
    rw [← Subgroup.map_map, transvectionHom_range_map_ringEquiv e hjk, hfeq]
  have hmainneg : ((ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1)
      (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))).D.rootGroup (-β)).map φ =
      (Matrix.SpecialLinearGroup.transvectionHom (A := ↥(fixSubfield σQ)) hjk.symm).range.map
        ((MulAut.conj z).toMonoidHom.comp
          (ψ.comp (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype))) := by
    rw [hrootβneg]
    change (Matrix.SpecialLinearGroup.transvectionHom (A := GaloisField 2
      (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) hjk.symm).range.map
      (f.comp (Matrix.SpecialLinearGroup.map (e : GaloisField 2
        (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) →+*
          ↥(fixSubfield σQ)))) = _
    rw [← Subgroup.map_map, transvectionHom_range_map_ringEquiv e hjk.symm, hfeq]
  refine ⟨σ j k, ?_, z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΨ]
    exact ⟨j, k, hjk, rfl⟩
  · exact hz
  · exact frame_conj_rootSubgroup_map_eq hψ z σQ S.D.step hF hjk
  · rw [show -σ j k = σ k j from (hψ.neg j k).symm]
    exact frame_conj_rootSubgroup_map_eq hψ z σQ S.D.step hF hjk.symm
  · rw [hmain]
    exact (frame_conj_rootSubgroup_inf_eqLocus hψ z σQ S.D.step hF hjk).symm
  · rw [show -σ j k = σ k j from (hψ.neg j k).symm]
    rw [hmainneg]
    exact (frame_conj_rootSubgroup_inf_eqLocus hψ z σQ S.D.step hF hjk.symm).symm

end Model

end CFSG.StandardType.RCKRP

end
