module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAutDict
public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType.TableBExc.E6Three CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

private def ggTP_zeta : (ZMod 7)ˣ := ⟨(2 : ZMod 7), (4 : ZMod 7), by decide, by decide⟩

private theorem ggTP_zeta_pow_three : ggTP_zeta ^ 3 = 1 := by
  ext
  decide

private theorem ggTP_zeta_ne_one : ggTP_zeta ≠ 1 := by
  intro h
  have h2 : (2 : ZMod 7) = 1 := by
    simpa [ggTP_zeta] using congrArg (fun u : (ZMod 7)ˣ => (u : ZMod 7)) h
  exact (by decide : (2 : ZMod 7) ≠ 1) h2

private theorem ggTP_zeta_orderOf : orderOf ggTP_zeta = 3 :=
  orderOf_eq_prime ggTP_zeta_pow_three ggTP_zeta_ne_one

private theorem ggTP_perpRoots_card_finite :
    ∀ v ∈ rootFinset Tag.E6,
      ((rootFinset Tag.E6).filter (fun α => iform α v = 0)).card = 30 := by
  decide +kernel

private noncomputable def ggTP_weylAut {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hF : KGL.KGAutFrame A κ) (u : WeylGroup Tag.E6) : MulAut ↥A :=
  Classical.choose (KGL.KGAutFrame.exists_mem_of_weyl hF u)

private theorem ggTP_weylAut_coord {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hF : KGL.KGAutFrame A κ) (u : WeylGroup Tag.E6) :
    ∀ a : ↥A, Multiplicative.toAdd (κ (ggTP_weylAut hF u a)) =
      adAct Tag.E6 3 u (Multiplicative.toAdd (κ a)) :=
  (Classical.choose_spec (KGL.KGAutFrame.exists_mem_of_weyl hF u)).2

private theorem ggTP_weylAut_eq_of_action {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hF : KGL.KGAutFrame A κ) {u : WeylGroup Tag.E6} {ψ : MulAut ↥A}
    (h : ∀ a : ↥A, Multiplicative.toAdd (κ (ψ a)) =
      adAct Tag.E6 3 u (Multiplicative.toAdd (κ a))) :
    ψ = ggTP_weylAut hF u := by
  apply MulEquiv.ext
  intro a
  apply hF.injective
  exact Multiplicative.ofAdd.injective (by
    simpa using (h a).trans (ggTP_weylAut_coord hF u a).symm)

private theorem ggTP_weylAut_mul {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hF : KGL.KGAutFrame A κ) (u v : WeylGroup Tag.E6) :
    ggTP_weylAut hF (u * v) = ggTP_weylAut hF u * ggTP_weylAut hF v := by
  symm
  apply ggTP_weylAut_eq_of_action hF (u := u * v)
  intro a
  rw [MulAut.mul_apply]
  exact Eq.trans (ggTP_weylAut_coord hF u (ggTP_weylAut hF v a))
    (Eq.trans (congrArg (adAct Tag.E6 3 u) (ggTP_weylAut_coord hF v a))
      (adAct_mul u v (Multiplicative.toAdd (κ a))).symm)

private theorem ggTP_weylAut_one {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hF : KGL.KGAutFrame A κ) : ggTP_weylAut hF 1 = 1 := by
  symm
  apply ggTP_weylAut_eq_of_action hF (u := 1)
  intro a
  rw [MulAut.one_apply]
  exact (adAct_one (τ := Tag.E6) (p := 3) (Multiplicative.toAdd (κ a))).symm

private noncomputable def ggTP_weylAutHom {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    (hF : KGL.KGAutFrame A κ) : WeylGroup Tag.E6 →* MulAut ↥A where
  toFun := ggTP_weylAut hF
  map_one' := ggTP_weylAut_one hF
  map_mul' := ggTP_weylAut_mul hF

theorem ggTPStab_le_closure_refl
    {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin 6 → ZMod 3)} (hF : KGL.KGAutFrame A κ)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) {c : ↥A}
    (hc : Multiplicative.toAdd (κ c) = KGL.kgExpVec β) :
    ∀ φ ∈ ggTorusAut A, φ c = c →
      φ ∈ Subgroup.closure {ψ : MulAut ↥A | ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧
        iform γ β = 0 ∧
        ∀ a : ↥A, Multiplicative.toAdd (κ (ψ a)) = KGL.rootRefl γ (Multiplicative.toAdd (κ a))} := by
  intro φ hφ hφc
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let a : Fin Tag.E6.rank → (ZMod 7)ˣ :=
    zetaVec ggTP_zeta ggTP_zeta_pow_three (KGL.kgExpVec β)
  obtain ⟨u, hu⟩ := KGL.KGAutFrame.exists_weyl_of_mem hF hφ
  have huβ : adAct Tag.E6 3 u (KGL.kgExpVec β) = KGL.kgExpVec β := by
    have h := hu c
    rw [hφc] at h
    have h1 : adAct Tag.E6 3 u (KGL.kgExpVec β) =
        adAct Tag.E6 3 u (Multiplicative.toAdd (κ c)) :=
      congrArg (adAct Tag.E6 3 u) hc.symm
    rw [h1, h.symm]
    exact hc
  have h3 : ∀ i, a i ^ 3 = 1 := by
    intro i
    change (zetaVec ggTP_zeta ggTP_zeta_pow_three (KGL.kgExpVec β) i) ^ 3 = 1
    rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, ggTP_zeta_pow_three, one_pow]
  have hk30 : (kernelRoots (rootCharHom a)).ncard = 30 := by
    rw [kernelRoots_rootCharHom]
    have hset : {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α ∧
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a α = 1} =
        ↑((rootFinset Tag.E6).filter (fun α => iform α β = 0)) := by
      ext α
      rw [Finset.mem_coe, Finset.mem_filter, mem_rootFinset]
      constructor
      · rintro ⟨hα, h1⟩
        exact ⟨hα, (KGL.iform_zmod_three_eq_zero_iff hα hβ).mp
          ((KGL.rootChar_zetaVec_kgExpVec_eq_one_iff ggTP_zeta_orderOf ggTP_zeta_pow_three β α).mp
            h1)⟩
      · rintro ⟨hα, h1⟩
        exact ⟨hα,
          (KGL.rootChar_zetaVec_kgExpVec_eq_one_iff ggTP_zeta_orderOf ggTP_zeta_pow_three β α).mpr
            ((KGL.iform_zmod_three_eq_zero_iff hα hβ).mpr h1)⟩
    rw [hset, Set.ncard_coe_finset]
    exact ggTP_perpRoots_card_finite β (mem_rootFinset.mpr hβ)
  have hstab : u ∈ rootCharStabilizerSubgroup a := by
    rw [mem_rootCharStabilizerSubgroup]
    intro v
    have hu'inv : adAct Tag.E6 3 u⁻¹ (KGL.kgExpVec β) = KGL.kgExpVec β := by
      calc adAct Tag.E6 3 u⁻¹ (KGL.kgExpVec β)
          = adAct Tag.E6 3 u⁻¹ (adAct Tag.E6 3 u (KGL.kgExpVec β)) := by rw [huβ]
        _ = adAct Tag.E6 3 (u⁻¹ * u) (KGL.kgExpVec β) := (adAct_mul u⁻¹ u _).symm
        _ = adAct Tag.E6 3 1 (KGL.kgExpVec β) := by rw [inv_mul_cancel]
        _ = KGL.kgExpVec β := adAct_one _
    have hweyl : weylTuple u⁻¹ a = a := by
      show weylTuple u⁻¹ (zetaVec ggTP_zeta ggTP_zeta_pow_three (KGL.kgExpVec β)) =
        zetaVec ggTP_zeta ggTP_zeta_pow_three (KGL.kgExpVec β)
      rw [weylTuple_zetaVec ggTP_zeta ggTP_zeta_pow_three u⁻¹ (KGL.kgExpVec β), hu'inv]
    have h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a (u • v) =
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (weylTuple u⁻¹ a) v := by
      simpa using (rootChar_weylTuple u⁻¹ a v).symm
    rw [h1, hweyl]
  have hk : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 30, 40} : Set ℕ) := by
    rw [hk30]; norm_num
  have hkr : u ∈ kernelReflectionGroup a :=
    KSConn.e6_stab_le_kernelReflectionGroup_of_conn a h3 hk hstab
  let S : Set (MulAut ↥A) := {ψ : MulAut ↥A | ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧
    iform γ β = 0 ∧
    ∀ a : ↥A, Multiplicative.toAdd (κ (ψ a)) = KGL.rootRefl γ (Multiplicative.toAdd (κ a))}
  let G : Set (WeylGroup Tag.E6) := {r | ∃ (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank),
    w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel a ∧
      r = w * simple Tag.E6 i * w⁻¹}
  have hGsub : (ggTP_weylAutHom hF) '' G ⊆ S := by
    rintro x ⟨r, hr, rfl⟩
    obtain ⟨w, i, hγmem, rfl⟩ := hr
    have hγroot : IsRoot Tag.E6 (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := hγmem.1
    have hγβ : iform (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) β = 0 := by
      have hz : ((iform (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) β : ℤ) : ZMod 3) = 0 :=
        (KGL.rootChar_zetaVec_kgExpVec_eq_one_iff ggTP_zeta_orderOf ggTP_zeta_pow_three β _).mp
          hγmem.2
      exact (KGL.iform_zmod_three_eq_zero_iff hγroot hβ).mp hz
    have hmemS : ggTP_weylAutHom hF (w * simple Tag.E6 i * w⁻¹) ∈ S := by
      refine ⟨w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ), hγroot, hγβ, ?_⟩
      intro b
      rw [conj_simple_eq_rootReflection w i]
      exact (ggTP_weylAut_coord hF
          (rootReflection (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) b).trans
        (KGL.adAct_rootReflection_eq_rootRefl hγroot (Multiplicative.toAdd (κ b)))
    exact hmemS
  have hkr' : u ∈ Subgroup.closure G := hkr
  have hmem : ggTP_weylAut hF u ∈ Subgroup.closure S := by
    have hmap := MonoidHom.map_closure (ggTP_weylAutHom hF) G
    have hle : Subgroup.map (ggTP_weylAutHom hF) (Subgroup.closure G) ≤
        Subgroup.closure S := by
      rw [hmap]
      exact Subgroup.closure_mono hGsub
    refine hle ?_
    rw [Subgroup.mem_map]
    exact ⟨u, hkr', rfl⟩
  have hφu : φ = ggTP_weylAut hF u := ggTP_weylAut_eq_of_action hF hu
  rw [hφu]
  exact hmem

end CFSG.StandardType

end
