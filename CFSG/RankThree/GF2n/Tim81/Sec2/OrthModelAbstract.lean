module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelTransport
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelCentral

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W}

theorem commSub_fieldAut_mem :
    ∀ {j : ℕ} {β : W ≃+ ↥(hermA l F)},
      (∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w)) →
      ∀ (A : Subgroup SL(2, F)) (w : W),
        w ∈ commSub ρ A ↔
          β w ∈ commSub (hermRep l hF) (A.map (fieldAut F j)) := by
  intro j β hβ A w
  constructor
  · intro hw
    refine commSub_induction ρ A
      (P := fun x => β x ∈ commSub (hermRep l hF) (A.map (fieldAut F j))) ?_ ?_ ?_ hw
    · intro a ha v
      rw [LinearMap.sub_apply, Module.End.one_apply, β.map_sub, hβ]
      exact range_le_commSub (Subgroup.mem_map_of_mem (fieldAut F j) ha) ⟨β v, rfl⟩
    · simp
    · intro x y hx hy
      rw [β.map_add]
      exact (commSub (hermRep l hF) (A.map (fieldAut F j))).add_mem hx hy
  · intro hw
    have hmem : β.symm (β w) ∈ commSub ρ A := by
      refine commSub_induction (hermRep l hF) (A.map (fieldAut F j))
        (P := fun x => β.symm x ∈ commSub ρ A) ?_ ?_ ?_ hw
      · intro b hb v
        obtain ⟨a, ha, rfl⟩ := hb
        have h := hβ a (β.symm v)
        rw [β.apply_symm_apply] at h
        have h' : (hermRep l hF (fieldAut F j a) - 1) v =
            β ((ρ a) (β.symm v) - β.symm v) := by
          change (hermAct l (sig_sig hF) (fieldAut F j a) - 1) v =
            β ((ρ a) (β.symm v) - β.symm v)
          calc (hermAct l (sig_sig hF) (fieldAut F j a) - 1) v
              = (hermAct l (sig_sig hF) (fieldAut F j a)) v - v := rfl
            _ = β ((ρ a) (β.symm v)) - β (β.symm v) := by
                rw [h, β.apply_symm_apply]
            _ = β ((ρ a) (β.symm v) - β.symm v) := (β.map_sub _ _).symm
        rw [h', β.symm_apply_apply]
        exact range_le_commSub ha ⟨β.symm v, rfl⟩
      · simp
      · intro x y hx hy
        rw [map_add]
        exact (commSub ρ A).add_mem hx hy
    simpa using hmem

theorem IsOrthModule.card_commSub (horth : IsOrthModule hF ρ) (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l)) :
    Nat.card ↥(commSub ρ A) = 2 ^ (3 * l) := by
  have htest : IsOrthModule hF ρ := horth
  obtain ⟨j, β, hβ⟩ := htest
  have hs := fieldAut_image_sylow A hA2 hA j
  have hcard : Nat.card ↥(commSub ρ A) =
      Nat.card ↥(commSub (hermRep l hF) (A.map (fieldAut F j))) :=
    Nat.card_congr
      (Equiv.subtypeEquiv β.toEquiv fun w => commSub_fieldAut_mem (hF := hF) hβ A w)
  rw [hcard]
  have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
    rw [hs.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hs.1 hAeq
  have hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom := by
    ext a
    rw [hx a]
    constructor
    · intro ha
      exact ⟨x⁻¹ * a * x, ha, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs, rfl⟩
      change x⁻¹ * (x * s * x⁻¹) * x ∈ upperSylow
      simpa [mul_assoc] using hs
  rw [hEq, commSub_map_conj]
  have hinj : Function.Injective (hermRep l hF x : ↥(hermA l F) → ↥(hermA l F)) := by
    intro u v h
    have := congrArg (hermRep l hF x⁻¹) h
    simpa using this
  exact (Nat.card_congr (Submodule.equivMapOfInjective (hermRep l hF x) hinj
    (commSub (hermRep l hF) upperSylow)).symm).trans (card_commSub_upperSylow (hF := hF))

@[expose] def IsOrthModule.commCommSub (ρ : Representation (ZMod 2) SL(2, F) W)
    (A : Subgroup SL(2, F)) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2)
    {x | ∃ a ∈ A, ∃ v ∈ commSub ρ A, x = (ρ a - 1) v}

private theorem map_commCommSub_fieldAut {j : ℕ}
    {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    (A : Subgroup SL(2, F)) :
    (IsOrthModule.commCommSub ρ A).map (β.toAddMonoidHom.toZModLinearMap 2) =
      IsOrthModule.commCommSub (hermRep l hF) (A.map (fieldAut F j)) := by
  have hf : ∀ x, (β.toAddMonoidHom.toZModLinearMap 2) x = β x := fun _ => rfl
  rw [IsOrthModule.commCommSub, IsOrthModule.commCommSub, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, v, hv, rfl⟩, rfl⟩
    refine ⟨fieldAut F j a, Subgroup.mem_map_of_mem _ ha, β v,
      (commSub_fieldAut_mem (hF := hF) hβ A v).mp hv, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hf, hβ,
      hermRep_apply]
  · rintro ⟨a, ha, v, hv, rfl⟩
    obtain ⟨a', ha', rfl⟩ := ha
    have hv' : β.symm v ∈ commSub ρ A :=
      (commSub_fieldAut_mem (hF := hF) hβ A (β.symm v)).mpr (by
        simpa using hv)
    refine ⟨(ρ a' - 1) (β.symm v), ⟨a', ha', β.symm v, hv', rfl⟩, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hf, hβ,
      β.apply_symm_apply, hermRep_apply]

private theorem map_commCommSub_conj (n : SL(2, F)) (P : Subgroup SL(2, F)) :
    (IsOrthModule.commCommSub ρ P).map (ρ n) =
      IsOrthModule.commCommSub ρ (P.map (MulAut.conj n).toMonoidHom) := by
  rw [IsOrthModule.commCommSub, IsOrthModule.commCommSub, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, v, hv, rfl⟩, rfl⟩
    refine ⟨n * a * n⁻¹, Subgroup.mem_map_of_mem _ ha,
      ρ n v, ?_, ?_⟩
    · rw [commSub_map_conj ρ n P]
      exact Submodule.mem_map_of_mem hv
    change ρ n ((ρ a - 1) v) = (ρ (n * a * n⁻¹) - 1) (ρ n v)
    rw [conj_apply_sub ρ n a]
  · rintro ⟨a, ha, v, hv, rfl⟩
    obtain ⟨a', ha', rfl⟩ := ha
    rw [commSub_map_conj ρ n P] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    refine ⟨(ρ a' - 1) v', ⟨a', ha', v', hv', rfl⟩, ?_⟩
    change ρ n ((ρ a' - 1) v') = (ρ (n * a' * n⁻¹) - 1) (ρ n v')
    rw [conj_apply_sub ρ n a']

private theorem toZModSubmodule_closure_eq_span {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (s : Set V) :
    AddSubgroup.toZModSubmodule (n := 2) (AddSubgroup.closure s) =
      Submodule.span (ZMod 2) s := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact (AddSubgroup.closure_le (Submodule.span (ZMod 2) s).toAddSubgroup).2
      (fun y hy => Submodule.subset_span hy) hx
  · rw [Submodule.span_le]
    intro x hx
    exact AddSubgroup.subset_closure hx

private theorem commCommSub_model_eq :
    AddSubgroup.toZModSubmodule (n := 2) (commCommSub l hF) =
      IsOrthModule.commCommSub (hermRep l hF) upperSylow := by
  rw [IsOrthModule.commCommSub, commCommSub, toZModSubmodule_closure_eq_span]

theorem IsOrthModule.fixedSub_eq_span_commSub (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l)) :
    fixedSub ρ A = IsOrthModule.commCommSub ρ A := by
  have horth0 := horth
  obtain ⟨j, β, hβ⟩ := horth
  have hs := fieldAut_image_sylow A hA2 hA j
  have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
    rw [hs.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hs.1 hAeq
  have hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom := by
    ext a
    rw [hx a]
    constructor
    · intro ha
      exact ⟨x⁻¹ * a * x, ha, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs, rfl⟩
      change x⁻¹ * (x * s * x⁻¹) * x ∈ upperSylow
      simpa [mul_assoc] using hs
  let f : W →ₗ[ZMod 2] ↥(hermA l F) := β.toAddMonoidHom.toZModLinearMap 2
  have hf : ∀ y, f y = β y := fun _ => rfl
  have hf_inj : Function.Injective f := by
    intro y z h
    apply β.injective
    simpa [hf] using h
  have hmodelS : fixedSub (hermRep l hF) upperSylow =
      IsOrthModule.commCommSub (hermRep l hF) upperSylow := by
    rw [CFSG.RankThree.GF2n.Tim81.Sec2.fixedSub_eq_span_commSub (hF := hF),
      commCommSub_model_eq]
  have hmodel : fixedSub (hermRep l hF) (A.map (fieldAut F j)) =
      IsOrthModule.commCommSub (hermRep l hF) (A.map (fieldAut F j)) := by
    rw [hEq, fixedSub_map_conj, hmodelS, map_commCommSub_conj, ← hEq]
  have hfixβ : (fixedSub ρ A).map f = fixedSub (hermRep l hF) (A.map (fieldAut F j)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (fixedSub_fieldAut_mem (hF := hF) hβ A z).mp hz
    · intro hy
      refine ⟨β.symm y, ?_, ?_⟩
      · exact (fixedSub_fieldAut_mem (hF := hF) hβ A (β.symm y)).mpr (by
          simpa [hf] using hy)
      · simp [hf]
  have hcommβ : (IsOrthModule.commCommSub ρ A).map f =
      IsOrthModule.commCommSub (hermRep l hF) (A.map (fieldAut F j)) :=
    map_commCommSub_fieldAut (hF := hF) hβ A
  refine Submodule.map_injective_of_injective hf_inj ?_
  rw [hfixβ, hmodel, ← hcommβ]

theorem IsOrthModule.normalizer_transitive_fixed (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l))
    {v w : W} (hv : v ∈ fixedSub ρ A) (hw : w ∈ fixedSub ρ A) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ n ∈ Subgroup.normalizer (A : Set (SL(2, F))), ρ n v = w := by
  have horth0 := horth
  obtain ⟨j, β, hβ⟩ := horth
  have hs := fieldAut_image_sylow A hA2 hA j
  have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
    rw [hs.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hs.1 hAeq
  have hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom := by
    ext a
    rw [hx a]
    constructor
    · intro ha
      exact ⟨x⁻¹ * a * x, ha, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs, rfl⟩
      change x⁻¹ * (x * s * x⁻¹) * x ∈ upperSylow
      simpa [mul_assoc] using hs
  have hβv : β v ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) :=
    (fixedSub_fieldAut_mem (hF := hF) hβ A v).mp hv
  have hβw : β w ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) :=
    (fixedSub_fieldAut_mem (hF := hF) hβ A w).mp hw
  rw [hEq, fixedSub_map_conj] at hβv hβw
  obtain ⟨vS, hvS, hvS_eq⟩ := hβv
  obtain ⟨wS, hwS, hwS_eq⟩ := hβw
  have hvS0 : vS ≠ 0 := by
    intro h0
    apply hv0
    apply β.injective
    rw [map_zero, ← hvS_eq, h0, map_zero]
  have hwS0 : wS ≠ 0 := by
    intro h0
    apply hw0
    apply β.injective
    rw [map_zero, ← hwS_eq, h0, map_zero]
  obtain ⟨m, hm, hmv⟩ :=
    CFSG.RankThree.GF2n.Tim81.Sec2.normalizer_transitive_fixed (hF := hF) vS wS hvS hwS hvS0 hwS0
  let nB : SL(2, F) := x * m * x⁻¹
  have hnB : nB ∈ Subgroup.normalizer (A.map (fieldAut F j) : Set (SL(2, F))) := by
    rw [hEq, ← Subgroup.map_normalizer_eq_of_bijective (upperSylow)
      (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).bijective]
    exact Subgroup.mem_map_of_mem _ hm
  have hmapN : (Subgroup.normalizer (A : Set (SL(2, F)))).map (fieldAut F j) =
      Subgroup.normalizer (A.map (fieldAut F j) : Set (SL(2, F))) := by
    simpa using Subgroup.map_normalizer_eq_of_bijective A (fieldAutEquiv j).bijective
  have hnBmap : nB ∈ (Subgroup.normalizer (A : Set (SL(2, F)))).map (fieldAut F j) := by
    rw [hmapN]
    exact hnB
  obtain ⟨n, hn, hnfield⟩ := Subgroup.mem_map.1 hnBmap
  refine ⟨n, hn, ?_⟩
  apply β.injective
  rw [hβ, hnfield]
  calc (hermRep l hF nB) (β v) = (hermRep l hF nB) (hermRep l hF x vS) := by rw [hvS_eq]
    _ = hermRep l hF x wS := by
        have hcomb : hermRep l hF nB (hermRep l hF x vS) =
            hermRep l hF (nB * x) vS := by
          rw [← Module.End.mul_apply, ← map_mul]
        rw [hcomb, show nB * x = x * m by dsimp [nB]; group, map_mul,
          Module.End.mul_apply, hmv]
    _ = β w := hwS_eq

end CFSG.RankThree.GF2n.Tim81.Sec2

end
