module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement Matrix

@[expose] def Sp6Line (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  ∀ S : Sylow 2 ↥H,
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    let ℓ : Subgroup W := fixedPointSubgroup ↥S W
    let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
    ∀ Tstar : Subgroup (MulAut W),
      Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
      IsPGroup 2 ↥Tstar →
      (S : Subgroup ↥H).map H.subtype ≤ Tstar →
      let Good : Subgroup ↥H → Prop := fun Pstar =>
        IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ Tstar,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ Pℓ
      ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
        Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))

section Transport

variable {W V : Type} [CommGroup W] [CommGroup V] [Finite W] [Finite V]

theorem sp6Line_of_map_congr (H : Subgroup (MulAut W)) (H' : Subgroup (MulAut V)) (n : ℕ)
    (e : W ≃* V) (hH' : H' = H.map (CFSG.Quasithin.H.congrHom e))
    (h : Sp6Line V H' n) : Sp6Line W H n := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let ℓ : Subgroup W := fixedPointSubgroup ↥S W
  let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
  dsimp only
  intro Tstar hTnorm hT2 hST
  letI : MulDistribMulAction ↥H' V := MulDistribMulAction.compHom V H'.subtype
  letI : MulAction ↥H' V := MulAction.compHom V H'.subtype
  letI : MulAction ↥H' (Set V) := Set.mulActionSet
  let eH : ↥H ≃* ↥H' :=
    ((MulAut.congr e).subgroupMap H).trans (MulEquiv.subgroupCongr hH'.symm)
  let S' : Sylow 2 ↥H' := S.mapSurjective (f := eH.toMonoidHom) eH.surjective
  letI : MulDistribMulAction ↥S' V :=
    MulDistribMulAction.compHom V (H'.subtype.comp (S' : Subgroup ↥H').subtype)
  let ℓ' : Subgroup V := fixedPointSubgroup ↥S' V
  let Pℓ' : Subgroup ↥H' := MulAction.stabilizer ↥H' (ℓ' : Set V)
  let Tstar' : Subgroup (MulAut V) := Tstar.map (CFSG.Quasithin.H.congrHom e)
  have heHcoe : ∀ g : ↥H, (eH g : MulAut V) = MulAut.congr e (g : MulAut W) := by
    intro g
    change ((MulEquiv.subgroupMap (MulAut.congr e) H g : MulAut V)) =
      MulAut.congr e (g : MulAut W)
    rw [MulEquiv.coe_subgroupMap_apply]
  have hcomp : H'.subtype.comp eH.toMonoidHom =
      (CFSG.Quasithin.H.congrHom e).comp H.subtype :=
    MonoidHom.ext fun g => heHcoe g
  have hmapEH : ∀ P : Subgroup ↥H, (P.map eH.toMonoidHom).map eH.symm.toMonoidHom = P := by
    intro P
    rw [Subgroup.map_map]
    convert Subgroup.map_id P using 2
    ext x
    simp
  have hmapEH' : ∀ P : Subgroup ↥H', (P.map eH.symm.toMonoidHom).map eH.toMonoidHom = P := by
    intro P
    rw [Subgroup.map_map]
    convert Subgroup.map_id P using 2
    ext x
    simp
  have hℓ : ℓ = CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) := by
    ext w
    constructor
    · intro hw x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hw ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut W) w = w at h
      exact h
    · intro hw s
      have h := hw (s : MulAut W) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut W) w = w
      exact h
  have hℓ' : ℓ' = CFSG.Quasithin.fixV ((S' : Subgroup ↥H').map H'.subtype) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hv ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut V) v = v at h
      exact h
    · intro hv s
      have h := hv (s : MulAut V) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut V) v = v
      exact h
  have hS'coe : (S' : Subgroup ↥H') = (S : Subgroup ↥H).map eH.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hA : ((S : Subgroup ↥H).map eH.toMonoidHom).map H'.subtype =
      ((S : Subgroup ↥H).map H.subtype).map (CFSG.Quasithin.H.congrHom e) := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hfix : ℓ' = ℓ.map e.toMonoidHom := by
    rw [hℓ', hS'coe, hA, hℓ, CFSG.Quasithin.H.fixV_map_congrHom e]
  have hstab : Pℓ' = Pℓ.map eH.toMonoidHom := by
    have hfixset : Equiv.setCongr e.toEquiv (ℓ : Set W) = (ℓ' : Set V) := by
      rw [hfix]
      rfl
    have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
      eH (Equiv.setCongr e.toEquiv) ?_ (ℓ : Set W)
    · rw [hfixset] at h
      exact h.symm
    · intro g z
      change Equiv.setCongr e.toEquiv ((g : MulAut W) '' z) =
        (eH g : MulAut V) '' (Equiv.setCongr e.toEquiv z)
      rw [heHcoe g]
      ext y
      simp [Equiv.setCongr, MulAut.congr_apply, Set.image_image]
  have hTnorm' : Tstar' ≤ Subgroup.normalizer (H' : Set (MulAut V)) := by
    rw [hH', ← Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)]
    exact Subgroup.map_mono hTnorm
  have hT2' : IsPGroup 2 ↥Tstar' := hT2.map (CFSG.Quasithin.H.congrHom e)
  have hST' : (S' : Subgroup ↥H').map H'.subtype ≤ Tstar' := by
    rw [hS'coe, Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact Subgroup.map_mono hST
  let Good : Subgroup ↥H → Prop := fun Pstar =>
    IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
    (∀ t ∈ Tstar,
      (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
    ¬ Pstar ≤ Pℓ
  let Good' : Subgroup ↥H' → Prop := fun Pstar =>
    IsParabolicTwo ↥H' Pstar ∧ (S' : Subgroup ↥H') ≤ Pstar ∧
    (∀ t ∈ Tstar',
      (Pstar.map H'.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H'.subtype) ∧
    ¬ Pstar ≤ Pℓ'
  have hconj : ∀ t : MulAut W,
      (MulAut.conj (CFSG.Quasithin.H.congrHom e t)).toMonoidHom.comp
        (CFSG.Quasithin.H.congrHom e) =
      (CFSG.Quasithin.H.congrHom e).comp (MulAut.conj t).toMonoidHom := by
    intro t
    ext x
    simp [MulAut.conj_apply]
  have hgoodmap : ∀ Pstar : Subgroup ↥H, Good Pstar ↔ Good' (Pstar.map eH.toMonoidHom) := by
    intro Pstar
    have hpar : IsParabolicTwo ↥H Pstar ↔ IsParabolicTwo ↥H' (Pstar.map eH.toMonoidHom) :=
      ⟨fun hp => hp.map eH.toMonoidHom eH.surjective, fun hp => by
        have h1 : IsParabolicTwo ↥H ((Pstar.map eH.toMonoidHom).map eH.symm.toMonoidHom) :=
          hp.map eH.symm.toMonoidHom eH.symm.surjective
        rwa [hmapEH] at h1⟩
    have hSle : (S : Subgroup ↥H) ≤ Pstar ↔
        (S' : Subgroup ↥H') ≤ Pstar.map eH.toMonoidHom := by
      rw [hS'coe, Subgroup.map_le_map_iff_of_injective eH.injective]
    have hPℓle : Pstar ≤ Pℓ ↔ Pstar.map eH.toMonoidHom ≤ Pℓ' := by
      rw [hstab, Subgroup.map_le_map_iff_of_injective eH.injective]
    have hA' : (Pstar.map eH.toMonoidHom).map H'.subtype =
        (Pstar.map H.subtype).map (CFSG.Quasithin.H.congrHom e) := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hTinv : (∀ t ∈ Tstar,
        (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ↔
        (∀ t ∈ Tstar',
          ((Pstar.map eH.toMonoidHom).map H'.subtype).map (MulAut.conj t).toMonoidHom =
            (Pstar.map eH.toMonoidHom).map H'.subtype) := by
      constructor
      · rintro hh t' ht'
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ht'
        rw [hA']
        conv_lhs => rw [Subgroup.map_map, hconj t, ← Subgroup.map_map]
        rw [hh t ht]
      · rintro hh t ht
        have h1 := hh (CFSG.Quasithin.H.congrHom e t) (Subgroup.mem_map_of_mem _ ht)
        rw [hA'] at h1
        conv_lhs at h1 => rw [Subgroup.map_map, hconj t, ← Subgroup.map_map]
        exact (Subgroup.map_injective (CFSG.Quasithin.H.congrHom_injective e)).eq_iff.mp h1
    exact and_congr hpar (and_congr hSle (and_congr hTinv (not_congr hPℓle)))
  intro Pstar hmin
  have hgood : Good Pstar := hmin.1
  have hmin' : Minimal Good' (Pstar.map eH.toMonoidHom) := by
    refine ⟨(hgoodmap Pstar).mp hgood, ?_⟩
    intro Q' hQ' hQle
    have hQ : Good (Q'.map eH.symm.toMonoidHom) :=
      (hgoodmap _).mpr (by rwa [hmapEH'])
    have hQle' : Q'.map eH.symm.toMonoidHom ≤ Pstar := by
      have h2 := Subgroup.map_mono (f := eH.symm.toMonoidHom) hQle
      rwa [hmapEH] at h2
    have hle' : Pstar.map eH.toMonoidHom ≤ Q' := by
      have h2 := Subgroup.map_mono (f := eH.toMonoidHom) (hmin.2 hQ hQle')
      rwa [hmapEH'] at h2
    exact hle'
  obtain ⟨hne', hres'⟩ := h S' Tstar' hTnorm' hT2' hST' (Pstar.map eH.toMonoidHom) hmin'
  refine ⟨?_, ?_⟩
  · intro htop
    apply hne'
    rw [htop, Subgroup.map_top_of_surjective _ eH.surjective]
  · rcases hres' with hL2 | ⟨hn, hbot⟩
    · left
      have hHinf : (Hinf Pstar).map eH.toMonoidHom = Hinf (Pstar.map eH.toMonoidHom) :=
        Hinf_map eH.toMonoidHom Pstar
      let eSub : ↥(Hinf Pstar) ≃* ↥(Hinf (Pstar.map eH.toMonoidHom)) :=
        ((Hinf Pstar).equivMapOfInjective eH.toMonoidHom eH.injective).trans
          (MulEquiv.subgroupCongr hHinf)
      obtain ⟨ebar⟩ := nonempty_bar2_mulEquiv_of_equiv eSub
      exact CFSG.Blueprint.LieModel.of_mulEquiv ebar.symm hL2
    · right
      refine ⟨hn, ?_⟩
      have hHinf : (Hinf Pstar).map eH.toMonoidHom = Hinf (Pstar.map eH.toMonoidHom) :=
        Hinf_map eH.toMonoidHom Pstar
      rw [← hHinf] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective (H := Hinf Pstar)
        (f := eH.toMonoidHom) eH.injective).mp hbot

end Transport

section NaturalSetup

variable (K : Type) [Field K]

@[expose] noncomputable def piSpNat :
    ↥(CFSG.Open.StatedSp 3 K) →* MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
  CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 3 K)

abbrev sp6Mat (g : CFSG.Open.StatedSp 3 K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  ((g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)

@[expose] noncomputable def UH6 :
    Subgroup (MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) :=
  (unipotent 3 K).map (piSpNat K)

@[expose] noncomputable def eSp :
    ↥(CFSG.Open.StatedSp 3 K) ≃*
      ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)) :=
  CFSG.Quasithin.H.natEquiv (CFSG.Open.StatedSp 3 K)

@[expose] noncomputable def StdS6 :
    Subgroup ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)) :=
  (unipotent 3 K).map (eSp K).toMonoidHom

@[expose] noncomputable def StdB6 :
    Subgroup ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)) :=
  (borelSubgroup 3 K).map (eSp K).toMonoidHom

@[expose] noncomputable def StdQ6 (I : Set ℕ) :
    Subgroup ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)) :=
  (flagStabilizer 3 K I).map (eSp K).toMonoidHom

theorem coe_eSp (γ : ↥(CFSG.Open.StatedSp 3 K)) :
    ((eSp K γ : ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))) :
      MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) = piSpNat K γ :=
  CFSG.Quasithin.H.coe_natEquiv _ γ

theorem toAdd_piSpNat (γ : ↥(CFSG.Open.StatedSp 3 K))
    (x : CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :
    Multiplicative.toAdd (piSpNat K γ x) = sp6Mat K γ *ᵥ Multiplicative.toAdd x := by
  have h := CFSG.Quasithin.H.toAddMap_natAut (Γ := CFSG.Open.StatedSp 3 K) γ
    (Multiplicative.toAdd x)
  simpa [CFSG.Quasithin.H.toAddMap, piSpNat, sp6Mat] using h

theorem StdS6_map_subtype :
    (StdS6 K).map (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)).subtype = UH6 K := by
  have hcomp : (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)).subtype.comp
      (eSp K).toMonoidHom = piSpNat K :=
    MonoidHom.ext fun x => coe_eSp K x
  rw [StdS6, Subgroup.map_map, hcomp, UH6]

theorem normalizer_StdS6 [Finite K] [CharP K 2] :
    Subgroup.normalizer (StdS6 K : Set
      ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))) = StdB6 K := by
  have h := Subgroup.map_equiv_normalizer_eq (unipotent 3 K) (eSp K)
  rw [normalizer_unipotent] at h
  exact h.symm

theorem isSylowTwoOf_StdS6 [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (StdS6 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 3
  have hU0 : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map hU0 (eSp K).toMonoidHom
  have htop : Subgroup.map (eSp K).toMonoidHom (⊤ : Subgroup ↥(CFSG.Open.StatedSp 3 K)) = ⊤ :=
    Subgroup.map_top_of_surjective (eSp K).toMonoidHom (eSp K).surjective
  rw [htop] at h
  exact h

@[expose] def stdIsoSub (d : ℕ) : Subgroup (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) where
  carrier := {x | Multiplicative.toAdd x ∈ isoFlag 3 K d}
  one_mem' := by
    show Multiplicative.toAdd 1 ∈ isoFlag 3 K d
    rw [toAdd_one]
    exact Submodule.zero_mem _
  mul_mem' := by
    intro x y hx hy
    show Multiplicative.toAdd (x * y) ∈ isoFlag 3 K d
    rw [toAdd_mul]
    exact (isoFlag 3 K d).add_mem hx hy
  inv_mem' := by
    intro x hx
    show Multiplicative.toAdd x⁻¹ ∈ isoFlag 3 K d
    rw [toAdd_inv]
    exact (isoFlag 3 K d).neg_mem hx

theorem mem_stdIsoSub {d : ℕ} {x : CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K} :
    x ∈ stdIsoSub K d ↔ Multiplicative.toAdd x ∈ isoFlag 3 K d := Iff.rfl

theorem flag_eq_isoFlag {d : ℕ} (hd : d ≤ 3) : flag 3 K d = isoFlag 3 K d :=
  Submodule.ext fun _ => mem_flag_of_le (r := 3) (K := K) hd

theorem fixV_UH6 [Finite K] [CharP K 2] :
    CFSG.Quasithin.fixV (UH6 K) = stdIsoSub K 1 := by
  have h := (unitriangular_invariant_isotropic_subspaces (r := 3) (K := K)).1
  ext x
  rw [CFSG.Quasithin.mem_fixV, mem_stdIsoSub]
  constructor
  · intro hx
    have hx' : Multiplicative.toAdd x ∈
        {v : Fin 3 ⊕ Fin 3 → K | ∀ u ∈ unipotent 3 K,
          ((u : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v = v} := by
      intro u hu
      have h1 := hx (piSpNat K u) (Subgroup.mem_map_of_mem _ hu)
      have h2 := congrArg Multiplicative.toAdd h1
      rw [toAdd_piSpNat] at h2
      exact h2
    rw [h] at hx'
    simpa [flag_eq_isoFlag (K := K) (show 1 ≤ 3 by norm_num)] using hx'
  · intro hx γ hγ
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hγ
    apply Multiplicative.toAdd.injective
    rw [toAdd_piSpNat]
    have hu' : Multiplicative.toAdd x ∈
        {v : Fin 3 ⊕ Fin 3 → K | ∀ u ∈ unipotent 3 K,
          ((u : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v = v} := by
      rw [h]
      simpa [flag_eq_isoFlag (K := K) (show 1 ≤ 3 by norm_num)]
    exact hu' u hu

theorem stabilizer_stdIsoSub (d : ℕ) :
    letI : MulDistribMulAction ↥(CFSG.Open.StatedSp 3 K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) := MulDistribMulAction.compHom _ (piSpNat K)
    letI : MulAction ↥(CFSG.Open.StatedSp 3 K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) := MulAction.compHom _ (piSpNat K)
    letI : MulAction ↥(CFSG.Open.StatedSp 3 K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer ↥(CFSG.Open.StatedSp 3 K)
      (stdIsoSub K d : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) =
      stabilizer 3 K (isoFlag 3 K d) := by
  letI : MulDistribMulAction ↥(CFSG.Open.StatedSp 3 K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) := MulDistribMulAction.compHom _ (piSpNat K)
  letI : MulAction ↥(CFSG.Open.StatedSp 3 K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) := MulAction.compHom _ (piSpNat K)
  letI : MulAction ↥(CFSG.Open.StatedSp 3 K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := Set.mulActionSet
  ext γ
  rw [MulAction.mem_stabilizer_iff, mem_stabilizer]
  constructor
  · intro hset
    refine le_antisymm ?_ ?_
    · rintro v ⟨w, hw, rfl⟩
      have h1 : piSpNat K γ (Multiplicative.ofAdd w) ∈ stdIsoSub K d := by
        have := Set.smul_mem_smul_set (a := γ) (show Multiplicative.ofAdd w ∈ (stdIsoSub K d :
          Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) from hw)
        rwa [hset] at this
      rwa [mem_stdIsoSub, toAdd_piSpNat] at h1
    · intro v hv
      have hset' : γ⁻¹ • (stdIsoSub K d : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) =
          (stdIsoSub K d : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := by
        conv_lhs => rw [← hset]
        rw [← mul_smul, inv_mul_cancel, one_smul]
      refine ⟨Multiplicative.toAdd (γ⁻¹ • Multiplicative.ofAdd v), ?_, ?_⟩
      · have h1 : piSpNat K γ⁻¹ (Multiplicative.ofAdd v) ∈ stdIsoSub K d := by
          have := Set.smul_mem_smul_set (a := γ⁻¹) (show Multiplicative.ofAdd v ∈ (stdIsoSub K d :
            Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) from hv)
          rwa [hset'] at this
        rwa [mem_stdIsoSub, toAdd_piSpNat] at h1
      · have h2 : piSpNat K γ (γ⁻¹ • Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
          rw [show γ⁻¹ • Multiplicative.ofAdd v = piSpNat K γ⁻¹ (Multiplicative.ofAdd v) from rfl,
            ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
        have h3 := congrArg Multiplicative.toAdd h2
        rwa [toAdd_piSpNat, toAdd_ofAdd] at h3
  · intro hstab
    have hinv : γ⁻¹ ∈ stabilizer 3 K (isoFlag 3 K d) := Subgroup.inv_mem _ hstab
    have hpoint : ∀ x : CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K,
        x ∈ (stdIsoSub K d : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) ↔
          piSpNat K γ x ∈ (stdIsoSub K d : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := by
      intro x
      constructor
      · intro hx
        have hx' : Multiplicative.toAdd x ∈ isoFlag 3 K d := hx
        show Multiplicative.toAdd (piSpNat K γ x) ∈ isoFlag 3 K d
        rw [toAdd_piSpNat]
        exact hstab ▸ ⟨Multiplicative.toAdd x, hx', rfl⟩
      · intro hx
        have hx' : Multiplicative.toAdd (piSpNat K γ x) ∈ isoFlag 3 K d := hx
        show Multiplicative.toAdd x ∈ isoFlag 3 K d
        rw [toAdd_piSpNat] at hx'
        have hinv' : Submodule.map (mulVecLin (sp6Mat K γ⁻¹)) (isoFlag 3 K d) = isoFlag 3 K d := by
          simpa [sp6Mat] using mem_stabilizer.mp hinv
        have h2 : sp6Mat K γ⁻¹ *ᵥ Multiplicative.toAdd (piSpNat K γ x) ∈ isoFlag 3 K d :=
          hinv' ▸ ⟨Multiplicative.toAdd (piSpNat K γ x), hx', rfl⟩
        rw [toAdd_piSpNat] at h2
        have hmat : sp6Mat K γ⁻¹ = (sp6Mat K γ)⁻¹ := by simp [sp6Mat]
        have hone : (sp6Mat K γ)⁻¹ * (sp6Mat K γ) = 1 := by
          rw [← hmat]
          change ((((γ⁻¹ : ↥(CFSG.Open.StatedSp 3 K)) : GL (Fin 3 ⊕ Fin 3) K)) :
              Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *
            ((((γ : ↥(CFSG.Open.StatedSp 3 K)) : GL (Fin 3 ⊕ Fin 3) K)) :
              Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1
          rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
            Units.val_one]
        rw [hmat, Matrix.mulVec_mulVec, hone, Matrix.one_mulVec] at h2
        exact h2
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, hpoint (γ⁻¹ • x)]
    have h2 : (piSpNat K γ) (γ⁻¹ • x) = x := by
      rw [show γ⁻¹ • x = piSpNat K γ⁻¹ x from rfl, ← MulAut.mul_apply, ← map_mul,
        mul_inv_cancel, map_one, MulAut.one_apply]
    rw [h2]

theorem StdQ6_eq_stabilizer_stdIsoSub [Finite K] [CharP K 2] (d : ℕ) (hd : d ≤ 3) :
    letI : MulDistribMulAction ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)).subtype
    letI : MulAction ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)).subtype
    letI : MulAction ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
      (stdIsoSub K d : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) = StdQ6 K {d} := by
  letI : MulDistribMulAction ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)).subtype
  letI : MulAction ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)).subtype
  letI : MulAction ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(CFSG.Open.StatedSp 3 K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) := MulDistribMulAction.compHom _ (piSpNat K)
  letI : MulAction ↥(CFSG.Open.StatedSp 3 K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) := MulAction.compHom _ (piSpNat K)
  letI : MulAction ↥(CFSG.Open.StatedSp 3 K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := Set.mulActionSet
  have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
    (eSp K) (Equiv.refl (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K))) ?_
    (stdIsoSub K d : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K))
  · rw [stabilizer_stdIsoSub] at h
    have hq : (flagStabilizer 3 K {d}).map (eSp K).toMonoidHom =
        (stabilizer 3 K (isoFlag 3 K d)).map (eSp K).toMonoidHom := by
      rw [SymplecticHigher.flagStabilizer_singleton, flag_eq_isoFlag (K := K) hd]
    rw [StdQ6, hq]
    exact h.symm
  · intro g z
    change (piSpNat K g) '' z = (eSp K g : MulAut
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) '' z
    rw [← coe_eSp K g]

theorem flagStabilizer_anti {K : Type} [Field K] {I J : Set ℕ} (hJI : J ⊆ I) :
    flagStabilizer 3 K I ≤ flagStabilizer 3 K J := by
  intro g hg
  exact mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (hJI hi)

theorem exists_StdQ6_of_StdB6_le [Finite K] [CharP K 2]
    {P : Subgroup ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))}
    (hBP : StdB6 K ≤ P) :
    ∃ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) ∧ P = StdQ6 K I := by
  classical
  let e := eSp K
  set A : Subgroup ↥(CFSG.Open.StatedSp 3 K) := P.comap e.toMonoidHom with hA
  have hmap : A.map e.toMonoidHom = P :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective P
  have hBA : borelSubgroup 3 K ≤ A := by
    rw [← Subgroup.map_le_iff_le_comap]
    exact hBP
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  refine ⟨borelCuts K A, borelCuts_le A, ?_⟩
  rw [← hmap]
  exact congrArg (fun X : Subgroup ↥(CFSG.Open.StatedSp 3 K) => X.map e.toMonoidHom) hAeq

theorem StdQ6_le_StdQ6_iff [Finite K] [CharP K 2] {I J : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) (hJ : ∀ i ∈ J, 1 ≤ i ∧ i ≤ 3) :
    StdQ6 K I ≤ StdQ6 K J ↔ J ⊆ I := by
  have hI' : ∀ i ∈ I, i ≤ 3 := fun i hi => (hI i hi).2
  have hJ' : ∀ i ∈ J, i ≤ 3 := fun i hi => (hJ i hi).2
  constructor
  · intro hle j hj
    by_contra hji
    have hle' : flagStabilizer 3 K I ≤ flagStabilizer 3 K J :=
      (Subgroup.map_le_map_iff_of_injective (f := (eSp K).toMonoidHom)
        (eSp K).injective).mp hle
    obtain ⟨-, h3⟩ := hJ j hj
    have h1j : 1 ≤ j := (hJ j hj).1
    set k : Fin 3 := ⟨j - 1, by omega⟩
    have hk : (k : ℕ) + 1 = j := by simp [k]; omega
    have hmem : weylRep K k ∈ flagStabilizer 3 K I :=
      ((subflag_generation I hI').2.1 k).mpr (by rw [hk]; exact hji)
    exact ((subflag_generation J hJ').2.1 k).mp (hle' hmem) (by rw [hk]; exact hj)
  · intro hJI
    exact Subgroup.map_mono (flagStabilizer_anti hJI)

theorem StdQ6_map_conj_le_iff [Finite K] [CharP K 2]
    (h : ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))) {I J : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) (hJ : ∀ i ∈ J, 1 ≤ i ∧ i ≤ 3) :
    (StdQ6 K I).map (MulAut.conj h).toMonoidHom ≤
        (StdQ6 K J).map (MulAut.conj h).toMonoidHom ↔ J ⊆ I := by
  rw [Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj h).toMonoidHom)
    (MulAut.conj h).injective, StdQ6_le_StdQ6_iff (K := K) hI hJ]

theorem exists_StdQ6_map_conj_of_normalizer_le [Finite K] [CharP K 2]
    (h : ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)))
    {P : Subgroup ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))}
    (hBP : (StdB6 K).map (MulAut.conj h).toMonoidHom ≤ P) :
    ∃ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) ∧
      P = (StdQ6 K I).map (MulAut.conj h).toMonoidHom := by
  have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
      MonoidHom.id _ := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hBP' : StdB6 K ≤ P.map (MulAut.conj h⁻¹).toMonoidHom := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hBP
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
  obtain ⟨I, hI, hPeq⟩ := exists_StdQ6_of_StdB6_le (K := K) hBP'
  refine ⟨I, hI, ?_⟩
  have h2 : (P.map (MulAut.conj h⁻¹).toMonoidHom).map (MulAut.conj h).toMonoidHom = P := by
    rw [Subgroup.map_map]
    have hcomp2 : ((MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp2, Subgroup.map_id]
  rw [← h2, hPeq]

theorem StdQ6_conj_min [Finite K] [CharP K 2]
    (h : ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)))
    {P : Subgroup ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))}
    (hBP : (StdB6 K).map (MulAut.conj h).toMonoidHom ≤ P)
    (hnot : ¬ P ≤ (StdQ6 K {1}).map (MulAut.conj h).toMonoidHom) :
    (StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom ≤ P := by
  obtain ⟨I, hI, hPeq⟩ := exists_StdQ6_map_conj_of_normalizer_le (K := K) h hBP
  have h1 : 1 ∉ I := by
    intro h1
    apply hnot
    rw [hPeq]
    exact (StdQ6_map_conj_le_iff (K := K) h hI (by intro i hi; simp at hi; omega)).mpr (by
      intro i hi
      rw [Set.mem_singleton_iff] at hi
      rw [hi]
      exact h1)
  rw [hPeq]
  exact (StdQ6_map_conj_le_iff (K := K) h (by intro i hi; simp at hi; omega) hI).mpr (by
    intro i hi
    have h1' := hI i hi
    have hne : i ≠ 1 := fun e => h1 (e ▸ hi)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega)

theorem StdQ6_ne_top_of_mem [Finite K] [CharP K 2] {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) {j : ℕ} (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (hjI : j ∈ I) :
    StdQ6 K I ≠ ⊤ := by
  intro htop
  have htop' : flagStabilizer 3 K I = ⊤ := by
    have h := congrArg (fun X : Subgroup
      ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)) =>
      X.map (eSp K).symm.toMonoidHom) htop
    rw [StdQ6, Subgroup.map_map] at h
    have hcomp : ((eSp K).symm.toMonoidHom.comp (eSp K).toMonoidHom) = MonoidHom.id _ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id, Subgroup.map_top_of_surjective (eSp K).symm.toMonoidHom
      (eSp K).symm.surjective] at h
    exact h
  have hI' : ∀ i ∈ I, i ≤ 3 := fun i hi => (hI i hi).2
  set k : Fin 3 := ⟨j - 1, by omega⟩
  have hk : (k : ℕ) + 1 = j := by simp [k]; omega
  have hmem : weylRep K k ∉ flagStabilizer 3 K I := by
    rw [(subflag_generation I hI').2.1 k]
    rw [hk]
    exact fun h => h hjI
  rw [htop'] at hmem
  exact hmem (Subgroup.mem_top _)

section Levi

abbrev idx2 (K : Type) : Fin 2 → Fin 3 ⊕ Fin 3 := fun i => Sum.inl ⟨i.1, by omega⟩

abbrev idx3 (K : Type) : Fin 3 → Fin 3 ⊕ Fin 3 := fun i => Sum.inl i

variable {K : Type} [Field K]

theorem idx2_injective : Function.Injective (idx2 K) := by
  intro a b hab
  have h1 : (⟨a.1, by omega⟩ : Fin 3) = ⟨b.1, by omega⟩ := Sum.inl.inj hab
  exact Fin.ext (by simpa using congrArg Fin.val h1)

theorem col_mem_isoFlag_of_mem_stabilizer {g : CFSG.Open.StatedSp 3 K} {d : ℕ}
    (hg : g ∈ stabilizer 3 K (isoFlag 3 K d)) {j : Fin 3} (hj : (j : ℕ) < d) :
    (sp6Mat K g).col (Sum.inl j) ∈ isoFlag 3 K d := by
  have h1 : (Pi.single (Sum.inl j) (1 : K) : Fin 3 ⊕ Fin 3 → K) ∈ isoFlag 3 K d := by
    rw [mem_isoFlag]
    exact ⟨fun l => by simp, fun l hl => by
      have hlj : l ≠ j := by intro e; rw [e] at hl; omega
      simp [hlj]⟩
  have h3 : ((sp6Mat K g) *ᵥ (Pi.single (Sum.inl j) (1 : K))) ∈ isoFlag 3 K d :=
    (mem_stabilizer.mp hg) ▸ ⟨_, h1, rfl⟩
  rwa [Matrix.mulVec_single_one] at h3

theorem col_apply_eq_zero_of_notMem_idx2 {g : CFSG.Open.StatedSp 3 K}
    (hg : g ∈ stabilizer 3 K (isoFlag 3 K 2)) {j : Fin 2} {m : Fin 3 ⊕ Fin 3}
    (hm : m ∉ Set.range (idx2 K)) : sp6Mat K g m (idx2 K j) = 0 := by
  have hcol := col_mem_isoFlag_of_mem_stabilizer (K := K) hg (j := ⟨j.1, by omega⟩)
    (by simpa using j.isLt)
  rcases m with i | l
  · have hi : 2 ≤ (i : ℕ) := by
      by_contra h
      have hlt : (i : ℕ) < 2 := by omega
      exact hm ⟨⟨i.1, hlt⟩, rfl⟩
    have h4 := (mem_isoFlag.mp hcol).2 i (by simpa using hi)
    have h5 : sp6Mat K g (Sum.inl i) (Sum.inl ⟨j.1, by omega⟩) = 0 := by
      simpa [Matrix.col_apply] using h4
    simpa [idx2] using h5
  · have h4 := (mem_isoFlag.mp hcol).1 l
    have h5 : sp6Mat K g (Sum.inr l) (Sum.inl ⟨j.1, by omega⟩) = 0 := by
      simpa [Matrix.col_apply] using h4
    simpa [idx2] using h5

theorem col_apply_eq_zero_of_notMem_idx3 {g : CFSG.Open.StatedSp 3 K}
    (hg : g ∈ stabilizer 3 K (isoFlag 3 K 3)) {j : Fin 3} {m : Fin 3 ⊕ Fin 3}
    (hm : m ∉ Set.range (idx3 K)) : sp6Mat K g m (idx3 K j) = 0 := by
  have hcol := col_mem_isoFlag_of_mem_stabilizer (K := K) hg (j := j) (by simp)
  rcases m with i | l
  · exact absurd ⟨i, rfl⟩ hm
  · have h4 := (mem_isoFlag.mp hcol).1 l
    simpa [Matrix.col_apply] using h4

theorem blkIdx2_mul_of_mem (g h : CFSG.Open.StatedSp 3 K)
    (hh : h ∈ flagStabilizer 3 K {2,3}) :
    blkIdx (idx2 K) (sp6Mat K (g * h)) =
      blkIdx (idx2 K) (sp6Mat K g) * blkIdx (idx2 K) (sp6Mat K h) := by
  rw [show sp6Mat K (g * h) = sp6Mat K g * sp6Mat K h from rfl]
  refine blkIdx_mul (idx2_injective (K := K)) _ _ ?_
  intro k hk
  right
  intro j
  have hh2 : h ∈ stabilizer 3 K (isoFlag 3 K 2) := by
    have h1 := mem_flagStabilizer.mp hh 2 (by norm_num)
    rwa [flag_eq_isoFlag (K := K) (show 2 ≤ 3 by norm_num)] at h1
  exact col_apply_eq_zero_of_notMem_idx2 (K := K) hh2 hk

theorem blkIdx3_mul_of_mem (g h : CFSG.Open.StatedSp 3 K)
    (hh : h ∈ flagStabilizer 3 K {2,3}) :
    blkIdx (idx3 K) (sp6Mat K (g * h)) =
      blkIdx (idx3 K) (sp6Mat K g) * blkIdx (idx3 K) (sp6Mat K h) := by
  rw [show sp6Mat K (g * h) = sp6Mat K g * sp6Mat K h from rfl]
  refine blkIdx_mul (σ := idx3 K) (fun a b hab => Sum.inl.inj hab) _ _ ?_
  intro k hk
  right
  intro j
  have hh3 : h ∈ stabilizer 3 K (isoFlag 3 K 3) := by
    have h1 := mem_flagStabilizer.mp hh 3 (by norm_num)
    rwa [flag_eq_isoFlag (K := K) le_rfl] at h1
  exact col_apply_eq_zero_of_notMem_idx3 (K := K) hh3 hk

@[expose] noncomputable def blk2Hom :
    ↥(flagStabilizer 3 K {2,3}) →* Matrix (Fin 2) (Fin 2) K where
  toFun x := blkIdx (idx2 K) (sp6Mat K x.1)
  map_one' := by
    show blkIdx (idx2 K) (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1
    exact blkIdx_one (idx2_injective (K := K))
  map_mul' x y := blkIdx2_mul_of_mem (K := K) x.1 y.1 y.2

@[expose] noncomputable def detHom2 :
    ↥(flagStabilizer 3 K {2,3}) →* Kˣ :=
  (Matrix.detMonoidHom.comp (blk2Hom (K := K))).toHomUnits

@[expose] noncomputable def lamFun (x : ↥(flagStabilizer 3 K {2,3})) : K :=
  blkIdx (idx3 K) (sp6Mat K x.1) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩

theorem lamFun_one : lamFun (K := K) 1 = 1 := by
  show blkIdx (idx3 K) (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1
  rw [blkIdx_one (fun a b hab => Sum.inl.inj hab)]
  simp

theorem blk3_row_two_zero (x : ↥(flagStabilizer 3 K {2,3})) {l : Fin 3} (hl : (l : ℕ) < 2) :
    blkIdx (idx3 K) (sp6Mat K x.1) ⟨2, by norm_num⟩ l = 0 := by
  have hx2 : x.1 ∈ stabilizer 3 K (isoFlag 3 K 2) := by
    have h1 := mem_flagStabilizer.mp x.2 2 (by norm_num)
    rwa [flag_eq_isoFlag (K := K) (show 2 ≤ 3 by norm_num)] at h1
  have hcol := col_mem_isoFlag_of_mem_stabilizer (K := K) hx2 (j := l) hl
  have h4 := (mem_isoFlag.mp hcol).2 ⟨2, by norm_num⟩ (by simpa using hl)
  have h5 : sp6Mat K x.1 (Sum.inl ⟨2, by norm_num⟩) (Sum.inl l) = 0 := by
    simpa [Matrix.col_apply] using h4
  simpa [blkIdx, Matrix.submatrix_apply] using h5

theorem lamFun_mul (x y : ↥(flagStabilizer 3 K {2,3})) :
    lamFun (K := K) (x * y) = lamFun (K := K) x * lamFun (K := K) y := by
  have hmul : blkIdx (idx3 K) (sp6Mat K ((x * y).1)) =
      blkIdx (idx3 K) (sp6Mat K x.1) * blkIdx (idx3 K) (sp6Mat K y.1) := by
    rw [show (x * y).1 = x.1 * y.1 from rfl]
    exact blkIdx3_mul_of_mem (K := K) x.1 y.1 y.2
  show blkIdx (idx3 K) (sp6Mat K ((x * y).1)) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ =
    lamFun (K := K) x * lamFun (K := K) y
  rw [hmul, Matrix.mul_apply, Fin.sum_univ_three,
    blk3_row_two_zero x (l := 0) (by norm_num), blk3_row_two_zero x (l := 1) (by norm_num)]
  simp [lamFun]

@[expose] noncomputable def lamMonoidHom :
    ↥(flagStabilizer 3 K {2,3}) →* K where
  toFun := lamFun (K := K)
  map_one' := lamFun_one (K := K)
  map_mul' := lamFun_mul (K := K)

@[expose] noncomputable def lamHom :
    ↥(flagStabilizer 3 K {2,3}) →* Kˣ :=
  (lamMonoidHom (K := K)).toHomUnits

end Levi

section Kernel

variable {K : Type} [Field K]

theorem mem_unipotent_of_blk2 {g : CFSG.Open.StatedSp 3 K}
    (hg : g ∈ flagStabilizer 3 K {2,3})
    (hb : blkIdx (idx2 K) (sp6Mat K g) = 1)
    (hlam : blkIdx (idx3 K) (sp6Mat K g) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1) :
    g ∈ unipotent 3 K := by
  have hg2 : g ∈ stabilizer 3 K (isoFlag 3 K 2) := by
    have h1 := mem_flagStabilizer.mp hg 2 (by norm_num)
    rwa [flag_eq_isoFlag (K := K) (show 2 ≤ 3 by norm_num)] at h1
  have hg3 : g ∈ stabilizer 3 K (isoFlag 3 K 3) := by
    have h1 := mem_flagStabilizer.mp hg 3 (by norm_num)
    rwa [flag_eq_isoFlag (K := K) le_rfl] at h1
  have hb00 : sp6Mat K g (Sum.inl (0 : Fin 3)) (Sum.inl (0 : Fin 3)) = 1 := by
    have h := congrFun (congrFun hb (0 : Fin 2)) (0 : Fin 2)
    simpa [blkIdx, idx2] using h
  have hb01 : sp6Mat K g (Sum.inl (0 : Fin 3)) (Sum.inl (1 : Fin 3)) = 0 := by
    have h := congrFun (congrFun hb (0 : Fin 2)) (1 : Fin 2)
    simpa [blkIdx, idx2] using h
  have hb10 : sp6Mat K g (Sum.inl (1 : Fin 3)) (Sum.inl (0 : Fin 3)) = 0 := by
    have h := congrFun (congrFun hb (1 : Fin 2)) (0 : Fin 2)
    simpa [blkIdx, idx2] using h
  have hb11 : sp6Mat K g (Sum.inl (1 : Fin 3)) (Sum.inl (1 : Fin 3)) = 1 := by
    have h := congrFun (congrFun hb (1 : Fin 2)) (1 : Fin 2)
    simpa [blkIdx, idx2] using h
  have hcol0mem : (sp6Mat K g).col (Sum.inl (0 : Fin 3)) ∈ isoFlag 3 K 2 :=
    col_mem_isoFlag_of_mem_stabilizer (K := K) hg2 (j := 0) (by norm_num)
  have hcol1mem : (sp6Mat K g).col (Sum.inl (1 : Fin 3)) ∈ isoFlag 3 K 2 :=
    col_mem_isoFlag_of_mem_stabilizer (K := K) hg2 (j := 1) (by norm_num)
  have hcol2mem : (sp6Mat K g).col (Sum.inl (2 : Fin 3)) ∈ isoFlag 3 K 3 :=
    col_mem_isoFlag_of_mem_stabilizer (K := K) hg3 (j := 2) (by norm_num)
  have hcol_e0 : (sp6Mat K g).col (Sum.inl (0 : Fin 3)) =
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) := by
    funext y
    rcases y with i | l
    · fin_cases i
      · simpa [Matrix.col_apply] using hb00
      · simpa [Matrix.col_apply] using hb10
      · have h := (mem_isoFlag.mp hcol0mem).2 (⟨2, by norm_num⟩ : Fin 3) (by norm_num)
        simpa [Matrix.col_apply] using h
    · have h := (mem_isoFlag.mp hcol0mem).1 l
      simpa [Matrix.col_apply] using h
  have hcol_e1 : (sp6Mat K g).col (Sum.inl (1 : Fin 3)) =
      (Pi.single (Sum.inl (1 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) := by
    funext y
    rcases y with i | l
    · fin_cases i
      · simpa [Matrix.col_apply] using hb01
      · simpa [Matrix.col_apply] using hb11
      · have h := (mem_isoFlag.mp hcol1mem).2 (⟨2, by norm_num⟩ : Fin 3) (by norm_num)
        simpa [Matrix.col_apply] using h
    · have h := (mem_isoFlag.mp hcol1mem).1 l
      simpa [Matrix.col_apply] using h
  have hcol_e0_inl : ∀ a : Fin 3,
      sp6Mat K g (Sum.inl a) (Sum.inl (0 : Fin 3)) =
        (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) (Sum.inl a) :=
    fun a => congrFun hcol_e0 (Sum.inl a)
  have hcol_e0_inr : ∀ b : Fin 3,
      sp6Mat K g (Sum.inr b) (Sum.inl (0 : Fin 3)) = 0 := by
    intro b
    have h := congrFun hcol_e0 (Sum.inr b)
    simpa using h
  have hcol_e1_inl : ∀ a : Fin 3,
      sp6Mat K g (Sum.inl a) (Sum.inl (1 : Fin 3)) =
        (Pi.single (Sum.inl (1 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) (Sum.inl a) :=
    fun a => congrFun hcol_e1 (Sum.inl a)
  have hcol_e1_inr : ∀ b : Fin 3,
      sp6Mat K g (Sum.inr b) (Sum.inl (1 : Fin 3)) = 0 := by
    intro b
    have h := congrFun hcol_e1 (Sum.inr b)
    simpa using h
  have hcol_e2f : ∀ l : Fin 3, sp6Mat K g (Sum.inr l) (Sum.inl (2 : Fin 3)) = 0 := by
    intro l
    have h := (mem_isoFlag.mp hcol2mem).1 l
    simpa [Matrix.col_apply] using h
  have hget (x y : Fin 3 ⊕ Fin 3) :
      pairedSympForm K 3 ((sp6Mat K g).col x) ((sp6Mat K g).col y) =
        pairedSympForm K 3 (Pi.single x (1 : K)) (Pi.single y (1 : K)) := by
    have h := pairedSympForm_mulVec (K := K) g (Pi.single x (1 : K)) (Pi.single y (1 : K))
    rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  have hf3_f1 : sp6Mat K g (Sum.inr (0 : Fin 3)) (Sum.inr (2 : Fin 3)) = 0 := by
    have h := hget (Sum.inl (0 : Fin 3)) (Sum.inr (2 : Fin 3))
    rw [hcol_e0, pairedSympForm_single_inl, pairedSympForm_single_inl] at h
    simpa [Matrix.col_apply] using h
  have hf3_f2 : sp6Mat K g (Sum.inr (1 : Fin 3)) (Sum.inr (2 : Fin 3)) = 0 := by
    have h := hget (Sum.inl (1 : Fin 3)) (Sum.inr (2 : Fin 3))
    rw [hcol_e1, pairedSympForm_single_inl, pairedSympForm_single_inl] at h
    simpa [Matrix.col_apply] using h
  have hf2_f1 : sp6Mat K g (Sum.inr (0 : Fin 3)) (Sum.inr (1 : Fin 3)) = 0 := by
    have h := hget (Sum.inl (0 : Fin 3)) (Sum.inr (1 : Fin 3))
    rw [hcol_e0, pairedSympForm_single_inl, pairedSympForm_single_inl] at h
    simpa [Matrix.col_apply] using h
  have hd_f0 : sp6Mat K g (Sum.inr (0 : Fin 3)) (Sum.inr (0 : Fin 3)) = 1 := by
    have h := hget (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3))
    rw [hcol_e0, pairedSympForm_single_inl, pairedSympForm_single_inl] at h
    simpa [Matrix.col_apply] using h
  have hd_f1 : sp6Mat K g (Sum.inr (1 : Fin 3)) (Sum.inr (1 : Fin 3)) = 1 := by
    have h := hget (Sum.inl (1 : Fin 3)) (Sum.inr (1 : Fin 3))
    rw [hcol_e1, pairedSympForm_single_inl, pairedSympForm_single_inl] at h
    simpa [Matrix.col_apply] using h
  have hlam' : sp6Mat K g (Sum.inl (2 : Fin 3)) (Sum.inl (2 : Fin 3)) = 1 := by
    simpa [blkIdx, Matrix.submatrix_apply] using hlam
  have hd_f2 : sp6Mat K g (Sum.inr (2 : Fin 3)) (Sum.inr (2 : Fin 3)) = 1 := by
    have h := hget (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
    rw [pairedSympForm_apply, pairedSympForm_apply] at h
    simp only [dotProduct, Fin.sum_univ_three, Function.comp_apply, Matrix.col_apply] at h
    rw [hcol_e2f 0, hcol_e2f 1, hcol_e2f 2, hf3_f1, hf3_f2, hlam'] at h
    simpa using h
  clear hget hcol0mem hcol1mem hcol2mem
  refine (mem_unipotent_iff_isFlagUpper (r := 3) (K := K)).mpr ⟨?_, ?_⟩
  · intro x y hxy
    rcases x with i | l
    · fin_cases i
      · have hy : y ≠ Sum.inl (0 : Fin 3) := by
          intro e
          rw [e] at hxy
          exact absurd hxy (lt_irrefl _)
        change (sp6Mat K g).col (Sum.inl (0 : Fin 3)) y = 0
        rw [hcol_e0]
        simp [Pi.single_apply, hy]
      · have hy : y ≠ Sum.inl (1 : Fin 3) := by
          intro e
          rw [e] at hxy
          exact absurd hxy (lt_irrefl _)
        change (sp6Mat K g).col (Sum.inl (1 : Fin 3)) y = 0
        rw [hcol_e1]
        simp [Pi.single_apply, hy]
      · rcases y with i' | l'
        · simp only [flagOrder_inl] at hxy
          exfalso
          omega
        · exact hcol_e2f l'
    · fin_cases l
      · rcases y with i' | l'
        · simp only [flagOrder_inr, flagOrder_inl] at hxy
          exfalso
          omega
        · simp only [flagOrder_inr] at hxy
          exfalso
          omega
      · rcases y with i' | l'
        · simp only [flagOrder_inr, flagOrder_inl] at hxy
          exfalso
          omega
        · simp only [flagOrder_inr] at hxy
          fin_cases l'
          · exact hf2_f1
          · exfalso
            simp at hxy
          · exfalso
            simp at hxy
      · rcases y with i' | l'
        · simp only [flagOrder_inr, flagOrder_inl] at hxy
          exfalso
          omega
        · simp only [flagOrder_inr] at hxy
          fin_cases l'
          · exact hf3_f1
          · exact hf3_f2
          · exfalso
            simp at hxy
  · intro x
    rcases x with i | l
    · fin_cases i
      · exact hb00
      · exact hb11
      · exact hlam'
    · fin_cases l
      · exact hd_f0
      · exact hd_f1
      · exact hd_f2

end Kernel

section Perfect

variable {K : Type} [Field K] [Finite K]

theorem det_blk2_eq_one (x : ↥(perfectCore (flagStabilizer 3 K {2,3}))) :
    (blkIdx (idx2 K) (sp6Mat K x.1)).det = 1 := by
  have hperf : Group.IsPerfect ↥(perfectCore (flagStabilizer 3 K {2,3})) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  let ψ : ↥(perfectCore (flagStabilizer 3 K {2,3})) →* Kˣ :=
    (detHom2 (K := K)).comp (Subgroup.inclusion (perfectCore_le _))
  have hker : ψ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker ψ
  have h1 : ψ x = 1 := by
    have hx : x ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_top x
    exact MonoidHom.mem_ker.mp hx
  have h2 := congrArg Units.val h1
  simpa [ψ, detHom2, blk2Hom, MonoidHom.comp_apply] using h2

theorem lam_eq_one (x : ↥(perfectCore (flagStabilizer 3 K {2,3}))) :
    blkIdx (idx3 K) (sp6Mat K x.1) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1 := by
  have hperf : Group.IsPerfect ↥(perfectCore (flagStabilizer 3 K {2,3})) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  let ψ : ↥(perfectCore (flagStabilizer 3 K {2,3})) →* Kˣ :=
    (lamHom (K := K)).comp (Subgroup.inclusion (perfectCore_le _))
  have hker : ψ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker ψ
  have h1 : ψ x = 1 := by
    have hx : x ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_top x
    exact MonoidHom.mem_ker.mp hx
  have h2 := congrArg Units.val h1
  simpa [ψ, lamHom, lamMonoidHom, lamFun, MonoidHom.comp_apply] using h2

@[expose] noncomputable def blk2SL :
    ↥(perfectCore (flagStabilizer 3 K {2,3})) →* SpecialLinearGroup (Fin 2) K where
  toFun x := ⟨blkIdx (idx2 K) (sp6Mat K x.1), det_blk2_eq_one (K := K) x⟩
  map_one' := Subtype.ext (by
    show blkIdx (idx2 K) (sp6Mat K ((1 : ↥(perfectCore (flagStabilizer 3 K {2,3}))) :
      CFSG.Open.StatedSp 3 K)) = 1
    rw [show ((1 : ↥(perfectCore (flagStabilizer 3 K {2,3}))) : CFSG.Open.StatedSp 3 K) = 1
      from rfl]
    exact blkIdx_one (idx2_injective (K := K)))
  map_mul' x y := Subtype.ext (by
    show blkIdx (idx2 K) (sp6Mat K ((x * y : ↥(perfectCore (flagStabilizer 3 K {2,3}))) :
      CFSG.Open.StatedSp 3 K)) =
      blkIdx (idx2 K) (sp6Mat K x.1) * blkIdx (idx2 K) (sp6Mat K y.1)
    rw [show ((x * y : ↥(perfectCore (flagStabilizer 3 K {2,3}))) : CFSG.Open.StatedSp 3 K) =
      x.1 * y.1 from rfl]
    exact blkIdx2_mul_of_mem (K := K) x.1 y.1 (perfectCore_le _ y.2))

theorem blk2SL_apply (x : ↥(perfectCore (flagStabilizer 3 K {2,3}))) :
    ((blk2SL (K := K) x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blkIdx (idx2 K) (sp6Mat K x.1) := rfl

theorem leviSL_mulVec_mem (A : Matrix.SpecialLinearGroup (Fin 2) K) {d : ℕ}
    (hd2 : 2 ≤ d) (hd3 : d ≤ 3) {v : Fin 3 ⊕ Fin 3 → K} (hv : v ∈ isoFlag 3 K d) :
    sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A) *ᵥ v ∈
      isoFlag 3 K d := by
  rw [mem_isoFlag] at hv ⊢
  have hcoe : sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A) =
      Matrix.fromBlocks (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviMat A) 0 0
        ((CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviMat A⁻¹)ᵀ) :=
    CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.coe_leviSL A
  constructor
  · intro l
    rw [hcoe, Matrix.fromBlocks_mulVec]
    have hv' : (v ∘ Sum.inr) = 0 := funext hv.1
    simp [hv']
  · intro l hl
    rw [hcoe, Matrix.fromBlocks_mulVec]
    have hl2 : l = (⟨2, by norm_num⟩ : Fin 3) := by
      apply Fin.ext
      show (l : ℕ) = 2
      have := l.isLt
      omega
    have hu2 : v (Sum.inl (⟨2, by norm_num⟩ : Fin 3)) = 0 := hv.2 _ (by rw [← hl2]; exact hl)
    rw [hl2]
    simp only [Sum.elim_inl, Pi.add_apply, Matrix.zero_mulVec, add_zero]
    have hrow : (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviMat A *ᵥ (v ∘ Sum.inl))
        (⟨2, by norm_num⟩ : Fin 3) = v (Sum.inl (⟨2, by norm_num⟩ : Fin 3)) := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviMat]
    rw [hrow, hu2]

theorem leviSL_mem_stabilizer_isoFlag (A : Matrix.SpecialLinearGroup (Fin 2) K) {d : ℕ}
    (hd2 : 2 ≤ d) (hd3 : d ≤ 3) :
    CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A ∈
      stabilizer 3 K (isoFlag 3 K d) := by
  rw [mem_stabilizer]
  refine le_antisymm ?_ ?_
  · rintro v ⟨w, hw, rfl⟩
    rw [Matrix.mulVecLin_apply]
    exact leviSL_mulVec_mem (K := K) A hd2 hd3 hw
  · intro v hv
    refine ⟨(sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A))⁻¹ *ᵥ v,
      ?_, ?_⟩
    · rw [show (sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A))⁻¹ =
        sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A⁻¹) from by
          simp [sp6Mat]]
      exact leviSL_mulVec_mem (K := K) A⁻¹ hd2 hd3 hv
    · have hinv : (sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A))⁻¹ =
          sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A⁻¹) := by
        simp [sp6Mat]
      have hunit : (sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A)) *
          (sp6Mat K (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A⁻¹)) = 1 := by
        change (((↑(CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A :
            GL (Fin 3 ⊕ Fin 3) K)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *
          ((↑(CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A⁻¹ :
            GL (Fin 3 ⊕ Fin 3) K)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) = 1
        rw [← Units.val_mul, ← Subgroup.coe_mul,
          show (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A) *
            (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A⁻¹) = 1 from by
            rw [← map_mul, mul_inv_cancel, map_one]]
        rfl
      rw [Matrix.mulVecLin_apply, hinv, Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]

theorem leviSL_range_perfect (hK4 : ∃ s : Finset K, s.card = 4) :
    ⁅(CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K)).range,
      (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K)).range⁆ =
      (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K)).range := by
  have hSL : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4)
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hSL]

theorem leviSL_mem_flagStabilizer (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K) A ∈
      flagStabilizer 3 K {2,3} := by
  rw [mem_flagStabilizer]
  intro i hi
  rcases (by simpa using hi : i = 2 ∨ i = 3) with rfl | rfl
  · rw [flag_eq_isoFlag (K := K) (show 2 ≤ 3 by norm_num)]
    exact leviSL_mem_stabilizer_isoFlag (K := K) (d := 2) A le_rfl (by norm_num)
  · rw [flag_eq_isoFlag (K := K) le_rfl]
    exact leviSL_mem_stabilizer_isoFlag (K := K) (d := 3) A (by norm_num) le_rfl

end Perfect

section Residual

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem blk2SL_surjective (hK4 : ∃ s : Finset K, s.card = 4) :
    Function.Surjective (blk2SL (K := K)) := by
  intro A
  let L := CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSL (K := K)
  have hmem : L A ∈ perfectCore (flagStabilizer 3 K {2,3}) :=
    le_perfectCore_of_perfect (K := L.range) (H := flagStabilizer 3 K {2,3})
      (fun y hy => by
        obtain ⟨B, rfl⟩ := hy
        exact leviSL_mem_flagStabilizer (K := K) B)
      (leviSL_range_perfect (K := K) hK4) ⟨A, rfl⟩
  refine ⟨⟨L A, hmem⟩, ?_⟩
  apply Subtype.ext
  change blkIdx (idx2 K) (sp6Mat K (L A)) = (A : Matrix (Fin 2) (Fin 2) K)
  ext i j
  have hcoe : sp6Mat K (L A) = Matrix.fromBlocks
      (CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviMat A) 0 0
      ((CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviMat A⁻¹)ᵀ) :=
    CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.coe_leviSL A
  rw [blkIdx, Matrix.submatrix_apply, hcoe, Matrix.fromBlocks_apply₁₁]
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviMat]

theorem blk2SL_ker_isPGroup :
    IsPGroup 2 (blk2SL (K := K)).ker := by
  obtain ⟨PU, hPU⟩ := exists_sylow_unipotent (K := K) 2 3
  have hUnip : IsPGroup 2 (unipotent 3 K) := hPU ▸ PU.isPGroup'
  intro x
  let y : ↥(perfectCore (flagStabilizer 3 K {2,3})) := x.1
  have hb : blkIdx (idx2 K) (sp6Mat K y.1) = 1 := by
    have hx := MonoidHom.mem_ker.mp x.2
    have h1 := congrArg (fun z : SpecialLinearGroup (Fin 2) K =>
      (z : Matrix (Fin 2) (Fin 2) K)) hx
    rw [blk2SL_apply] at h1
    exact h1
  have hlam : blkIdx (idx3 K) (sp6Mat K y.1) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1 :=
    lam_eq_one (K := K) y
  have hunip : y.1 ∈ unipotent 3 K :=
    mem_unipotent_of_blk2 (K := K) (perfectCore_le _ y.2) hb hlam
  obtain ⟨k, hk⟩ := hUnip ⟨y.1, hunip⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hk
  simpa [y] using h1

theorem isL2_bar2_perfectCore_sp6 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    IsL2 (Bar2 (perfectCore (flagStabilizer 3 K {2,3}))) n := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab := sl2_nonabelian hK4
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := sl2_isSimple hK4
  have hmodel : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  let e : Bar2 (perfectCore (flagStabilizer 3 K {2,3})) ≃* StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab (blk2SL (K := K)) (blk2SL_surjective (K := K) hK4)
      (blk2SL_ker_isPGroup (K := K))).trans sl2EquivStatedProj
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) e.symm hmodel

theorem perfectCore_sp6_eq_bot_of_card_two (hK2 : Nat.card K = 2) :
    perfectCore (flagStabilizer 3 K {2,3}) = ⊥ := by
  have hKu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hKu).1
  have hdet1 : ∀ x : ↥(flagStabilizer 3 K {2,3}),
      (blkIdx (idx2 K) (sp6Mat K x.1)).det = 1 := by
    intro x
    have h1 : (Matrix.detMonoidHom.comp (blk2Hom (K := K))).toHomUnits x = 1 :=
      Subsingleton.elim _ _
    have h2 := congrArg Units.val h1
    simpa [MonoidHom.comp_apply, blk2Hom] using h2
  let blk2SLQ : ↥(flagStabilizer 3 K {2,3}) →* SpecialLinearGroup (Fin 2) K :=
    { toFun := fun x => ⟨blkIdx (idx2 K) (sp6Mat K x.1), hdet1 x⟩
      map_one' := Subtype.ext (by
        show blkIdx (idx2 K) (sp6Mat K (1 : CFSG.Open.StatedSp 3 K)) = 1
        rw [show sp6Mat K (1 : CFSG.Open.StatedSp 3 K) = 1 from rfl]
        exact blkIdx_one (idx2_injective (K := K)))
      map_mul' := fun x y => Subtype.ext (blkIdx2_mul_of_mem (K := K) x.1 y.1 y.2) }
  have hker : IsPGroup 2 blk2SLQ.ker := by
    obtain ⟨PU, hPU⟩ := exists_sylow_unipotent (K := K) 2 3
    have hUnip : IsPGroup 2 (unipotent 3 K) := hPU ▸ PU.isPGroup'
    intro x
    let y : ↥(flagStabilizer 3 K {2,3}) := x.1
    have hb : blkIdx (idx2 K) (sp6Mat K y.1) = 1 := by
      have hx := MonoidHom.mem_ker.mp x.2
      have h1 := congrArg (fun z : SpecialLinearGroup (Fin 2) K =>
        (z : Matrix (Fin 2) (Fin 2) K)) hx
      change blkIdx (idx2 K) (sp6Mat K y.1) = 1 at h1
      exact h1
    have hlam : blkIdx (idx3 K) (sp6Mat K y.1) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1 := by
      have h1 : (lamHom (K := K)) y = 1 := Subsingleton.elim _ _
      have h2 := congrArg Units.val h1
      simpa [lamHom, lamMonoidHom, lamFun, y] using h2
    have hunip : y.1 ∈ unipotent 3 K := mem_unipotent_of_blk2 (K := K) y.2 hb hlam
    obtain ⟨k, hk⟩ := hUnip ⟨y.1, hunip⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa [y] using h1
  have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
    refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
    norm_num
  have hkerS : Group.IsSolvable ↥blk2SLQ.ker := by
    have := hker.isNilpotent
    infer_instance
  have hQ : Group.IsSolvable ↥(flagStabilizer 3 K {2,3}) :=
    Group.isSolvable_of_ker_le_range blk2SLQ.ker.subtype blk2SLQ
      (by rw [Subgroup.range_subtype])
  exact (isSolvable_iff_perfectCore_eq_bot (flagStabilizer 3 K {2,3})).mp hQ

end Residual

theorem borelSubgroup_three_eq_flagStabilizer :
    borelSubgroup 3 K = flagStabilizer 3 K ({1, 2, 3} : Set ℕ) := by
  ext g
  rw [mem_borelSubgroup, mem_flagStabilizer]
  constructor
  · intro h i hi
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by simpa using hi
    rcases hi' with rfl | rfl | rfl
    · exact h 1 le_rfl (by norm_num)
    · exact h 2 (by norm_num) (by norm_num)
    · exact h 3 (by norm_num) le_rfl
  · intro h i h1 h3
    interval_cases i
    · exact h 1 (by simp)
    · exact h 2 (by simp)
    · exact h 3 (by simp)

theorem map_subtype_normalizer_eq_inf {V : Type} [CommGroup V] (H : Subgroup (MulAut V))
    (S : Subgroup ↥H) :
    (Subgroup.normalizer S).map H.subtype =
      Subgroup.normalizer (S.map H.subtype) ⊓ H := by
  have key : ∀ (g : ↥H), g ∈ Subgroup.normalizer S ↔
      S.map (MulAut.conj g).toMonoidHom = S := by
    intro g
    exact Subgroup.mem_normalizer_iff_map_conj_eq
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    have hyN : y ∈ Subgroup.normalizer S := hy
    have hyS : S.map (MulAut.conj y).toMonoidHom = S := (key y).mp hyN
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
      calc (S.map H.subtype).map (MulAut.conj (H.subtype y)).toMonoidHom
          = (S.map (MulAut.conj y).toMonoidHom).map H.subtype := by
            rw [Subgroup.map_map, Subgroup.map_map]
            congr 1
        _ = S.map H.subtype := by rw [hyS])
  · rintro ⟨hxN, hxH⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    have hxN' : x ∈ Subgroup.normalizer (S.map H.subtype) := hxN
    have hxS : (S.map H.subtype).map (MulAut.conj x).toMonoidHom = S.map H.subtype :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN'
    exact (key ⟨x, hxH⟩).mpr (by
      refine Subgroup.map_injective H.subtype_injective ?_
      calc (S.map (MulAut.conj ⟨x, hxH⟩).toMonoidHom).map H.subtype
          = (S.map H.subtype).map (MulAut.conj x).toMonoidHom := by
            rw [Subgroup.map_map, Subgroup.map_map]
            congr 1
        _ = S.map H.subtype := hxS)

theorem sp6NaturalLine_holds :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 2 ^ n →
      Sp6Line (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)
        (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K)) n := by
  intro K hF hFin n hK
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
  have hKgt : 1 < Nat.card K := Finite.one_lt_card
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hK
    simp at hK
    omega
  set V := CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K with hV
  set H : Subgroup (MulAut V) := CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K) with hH
  change Sp6Line V H n
  unfold Sp6Line
  intro S
  intro ℓ Pℓ
  intro Tstar hTnorm hT2 hST
  intro Good Pstar hmin
  classical
  have hSylS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥H) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hSylStd : CFSG.QuasithinUnique.IsSylowTwoOf (StdS6 K) ⊤ := isSylowTwoOf_StdS6 (K := K)
  obtain ⟨h, -, hconj⟩ :=
    CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hSylStd hSylS
  let SH : Subgroup (MulAut V) := (S : Subgroup ↥H).map H.subtype
  have hcomp : H.subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj ((h : ↥H) : MulAut V)).toMonoidHom.comp H.subtype :=
    MonoidHom.ext fun x => rfl
  have hSH : SH = (UH6 K).map (MulAut.conj ((h : ↥H) : MulAut V)).toMonoidHom := by
    dsimp [SH]
    rw [hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map, StdS6_map_subtype]
    rfl
  have hℓ : ℓ = (stdIsoSub K 1).map ((h : ↥H) : MulAut V).toMonoidHom := by
    have h1 : ℓ = CFSG.Quasithin.fixV SH := by
      dsimp [ℓ, SH]
      rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
    rw [h1, hSH, fixV_map_conj, fixV_UH6]
  have hPℓ : Pℓ = (StdQ6 K {1}).map (MulAut.conj h).toMonoidHom := by
    have hstab : MulAction.stabilizer ↥H
        (((stdIsoSub K 1).map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) : Set V) =
        (MulAction.stabilizer ↥H (stdIsoSub K 1 : Set V)).map
          (MulAut.conj h).toMonoidHom :=
      stabilizer_map_conj_subgroup H h (stdIsoSub K 1)
    dsimp [Pℓ]
    rw [hℓ]
    change MulAction.stabilizer ↥H
      (((stdIsoSub K 1).map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) : Set V) =
      (StdQ6 K {1}).map (MulAut.conj h).toMonoidHom
    rw [hstab]
    have hstabQ : MulAction.stabilizer ↥H (stdIsoSub K 1 : Set V) = StdQ6 K {1} := by
      change MulAction.stabilizer
        ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K))
        (stdIsoSub K 1 : Set V) = StdQ6 K {1}
      exact StdQ6_eq_stabilizer_stdIsoSub (K := K) 1 (by norm_num)
    rw [hstabQ]
  have hB : Subgroup.normalizer (S : Set ↥H) =
      (StdB6 K).map (MulAut.conj h).toMonoidHom := by
    change Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H) =
      (StdB6 K).map (MulAut.conj h).toMonoidHom
    rw [hconj, ← Subgroup.map_equiv_normalizer_eq (StdS6 K) (MulAut.conj h), normalizer_StdS6]
  have hBP : (StdB6 K).map (MulAut.conj h).toMonoidHom ≤ Pstar := by
    have h1 := hmin.1.1.normalizer_le S hmin.1.2.1
    rwa [hB] at h1
  have hnotPℓ : ¬ Pstar ≤ (StdQ6 K {1}).map (MulAut.conj h).toMonoidHom := by
    simpa [hPℓ] using hmin.1.2.2.2
  have hBQ : (StdB6 K).map (MulAut.conj h).toMonoidHom ≤
      (StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom := by
    rw [show StdB6 K = (flagStabilizer 3 K ({1, 2, 3} : Set ℕ)).map (eSp K).toMonoidHom from by
      rw [StdB6, borelSubgroup_three_eq_flagStabilizer]]
    exact Subgroup.map_mono (Subgroup.map_mono (flagStabilizer_anti (by
      intro i hi
      rcases (by simpa using hi : i = 2 ∨ i = 3) with rfl | rfl <;> simp)))
  have hQnotPℓ : ¬ (StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom ≤
      (StdQ6 K {1}).map (MulAut.conj h).toMonoidHom := by
    intro hle
    have h1 : ({1} : Set ℕ) ⊆ ({2, 3} : Set ℕ) :=
      (StdQ6_map_conj_le_iff (K := K) h (by intro i hi; simp at hi; omega)
        (by intro i hi; simp at hi; omega)).mp hle
    exact absurd (h1 (by simp : (1 : ℕ) ∈ ({1} : Set ℕ))) (by simp)
  have hQle : (StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom ≤ Pstar :=
    StdQ6_conj_min (K := K) h hBP hnotPℓ
  have hfixV : ℓ = CFSG.Quasithin.fixV SH := by
    dsimp [ℓ, SH]
    rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
  have hTstarH : Tstar ⊓ H = SH := by
    have hX2 : IsPGroup 2 ↥(Tstar ⊓ H) := by
      intro x
      obtain ⟨k, hk⟩ := hT2 ⟨(x : MulAut V), x.2.1⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hX2sub : IsPGroup 2 ((Tstar ⊓ H).subgroupOf H) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hSX : (S : Subgroup ↥H) ≤ (Tstar ⊓ H).subgroupOf H := by
      intro x hx
      exact ⟨hST (Subgroup.mem_map_of_mem H.subtype hx), x.2⟩
    have hEq : (Tstar ⊓ H).subgroupOf H = (S : Subgroup ↥H) :=
      S.is_maximal' hX2sub hSX
    have h1 := congrArg (fun X : Subgroup ↥H => X.map H.subtype) hEq
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
    simpa [SH] using h1
  have hSH_normal : ∀ t ∈ Tstar, SH.map (MulAut.conj t).toMonoidHom = SH := by
    intro t ht
    have hle : SH.map (MulAut.conj t).toMonoidHom ≤ SH := by
      rintro x ⟨s, hs, rfl⟩
      obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
      have htH : t * (s0 : MulAut V) * t⁻¹ ∈ H :=
        ((Subgroup.mem_normalizer_iff.mp (hTnorm ht)) (s0 : MulAut V)).mp s0.2
      have hmem : t * (s0 : MulAut V) * t⁻¹ ∈ Tstar ⊓ H :=
        ⟨Tstar.mul_mem (Tstar.mul_mem ht (hST (Subgroup.mem_map_of_mem H.subtype hs0)))
          (Tstar.inv_mem ht), htH⟩
      rwa [hTstarH] at hmem
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective])
  have hℓ_t : ∀ t ∈ Tstar, ℓ.map t.toMonoidHom = ℓ := by
    intro t ht
    rw [hfixV, ← fixV_map_conj SH t, hSH_normal t ht]
  have hPℓ_t : ∀ t ∈ Tstar,
      (Pℓ.map H.subtype).map (MulAut.conj t).toMonoidHom = Pℓ.map H.subtype := by
    intro t ht
    have h := map_subtype_stabilizer_conj_normalizer t (hTnorm ht) ℓ
    rw [h, hℓ_t t ht]
  have hB_t : ∀ t ∈ Tstar,
      ((Subgroup.normalizer (((S : Subgroup ↥H)) : Set ↥H)).map H.subtype).map
        (MulAut.conj t).toMonoidHom =
      (Subgroup.normalizer (((S : Subgroup ↥H)) : Set ↥H)).map H.subtype := by
    intro t ht
    have hNB : (Subgroup.normalizer (((S : Subgroup ↥H)) : Set ↥H)).map H.subtype =
        Subgroup.normalizer (((S : Subgroup ↥H)).map H.subtype) ⊓ H :=
      map_subtype_normalizer_eq_inf (V := V) H (S : Subgroup ↥H)
    have hHt : H.map (MulAut.conj t).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht)
    rw [hNB, Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective,
      Subgroup.map_equiv_normalizer_eq SH (MulAut.conj t),
      hSH_normal t ht, hHt]
  have hQgoodT : ∀ t ∈ Tstar,
      (((StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom).map H.subtype).map
        (MulAut.conj t).toMonoidHom =
      ((StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom).map H.subtype := by
    intro t ht
    set Q : Subgroup ↥H := (StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom with hQ
    set Φ : Subgroup ↥H → Subgroup ↥H := fun P =>
      ((P.map H.subtype).map (MulAut.conj t).toMonoidHom).comap H.subtype with hΦ
    have hΦmap : ∀ P : Subgroup ↥H,
        (Φ P).map H.subtype = (P.map H.subtype).map (MulAut.conj t).toMonoidHom := by
      intro P
      rw [hΦ]
      exact Subgroup.map_comap_eq_self (by
        rw [Subgroup.range_subtype]
        exact le_trans (Subgroup.map_mono (Subgroup.map_subtype_le P))
          (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht))))
    have hΦmono : Monotone Φ := by
      intro P R hPR
      rw [hΦ]
      exact Subgroup.comap_mono (Subgroup.map_mono (Subgroup.map_mono hPR))
    have hcomp_inv : ((MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom) =
        MonoidHom.id _ := by
      ext z y
      simp [MulAut.conj_apply, mul_assoc]
    have hΦPℓ : Φ ((StdQ6 K {1}).map (MulAut.conj h).toMonoidHom) =
        (StdQ6 K {1}).map (MulAut.conj h).toMonoidHom := by
      rw [hΦ]
      beta_reduce
      have h1 : ((StdQ6 K {1}).map (MulAut.conj h).toMonoidHom).map H.subtype =
          Pℓ.map H.subtype := by rw [hPℓ]
      rw [h1, hPℓ_t t ht, Subgroup.comap_map_eq_self_of_injective H.subtype_injective, hPℓ]
    have hΦB_S : Φ ((StdB6 K).map (MulAut.conj h).toMonoidHom) =
        (StdB6 K).map (MulAut.conj h).toMonoidHom := by
      rw [hΦ]
      beta_reduce
      have h1 : ((StdB6 K).map (MulAut.conj h).toMonoidHom).map H.subtype =
          (Subgroup.normalizer (((S : Subgroup ↥H)) : Set ↥H)).map H.subtype :=
        congrArg (fun X : Subgroup ↥H => X.map H.subtype) hB.symm
      rw [h1, hB_t t ht, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hB
    have hΦQnotPℓ : ¬ Φ Q ≤ (StdQ6 K {1}).map (MulAut.conj h).toMonoidHom := by
      intro hle
      apply hQnotPℓ
      have h1 : (Q.map H.subtype).map (MulAut.conj t).toMonoidHom ≤ Pℓ.map H.subtype := by
        rw [← hΦmap Q, hPℓ]
        exact Subgroup.map_mono hle
      have h2 := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) h1
      rw [Subgroup.map_map, hcomp_inv, Subgroup.map_id,
        hPℓ_t t⁻¹ (Tstar.inv_mem ht)] at h2
      have h3 : Q ≤ Pℓ :=
        (Subgroup.map_le_map_iff_of_injective (f := H.subtype) H.subtype_injective).mp h2
      rw [← hPℓ]
      exact h3
    have hQleΦ : Q ≤ Φ Q := by
      have hBΦ : (StdB6 K).map (MulAut.conj h).toMonoidHom ≤ Φ Q := by
        have h := hΦmono hBQ
        rwa [hΦB_S] at h
      exact StdQ6_conj_min (K := K) h hBΦ hΦQnotPℓ
    have hXle : (Q.map H.subtype) ≤ (Q.map H.subtype).map (MulAut.conj t).toMonoidHom := by
      rw [← hΦmap Q]
      exact Subgroup.map_mono hQleΦ
    have hcard : Nat.card ((Q.map H.subtype).map (MulAut.conj t).toMonoidHom) =
        Nat.card (Q.map H.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective (Q.map H.subtype)
        (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).toEquiv.symm
    have heq : Q.map H.subtype = (Q.map H.subtype).map (MulAut.conj t).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hXle (by rw [hcard])
    exact heq.symm
  have hQgood : Good ((StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom) := by
    refine ⟨?_, ?_, hQgoodT, ?_⟩
    · exact ⟨S, by rw [hB]; exact hBQ⟩
    · intro x hx
      have hxN : x ∈ (StdB6 K).map (MulAut.conj h).toMonoidHom := by
        rw [← hB]
        exact Subgroup.le_normalizer hx
      exact hBQ hxN
    · rwa [hPℓ]
  have hle' : Pstar ≤ (StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom :=
    hmin.2 hQgood hQle
  obtain ⟨I, hI, hPeq⟩ := exists_StdQ6_map_conj_of_normalizer_le (K := K) h hBP
  have h1I : 1 ∉ I := by
    intro h1
    apply hnotPℓ
    rw [hPeq]
    exact (StdQ6_map_conj_le_iff (K := K) h hI (by intro i hi; simp at hi; omega)).mpr (by
      intro i hi
      rw [Set.mem_singleton_iff] at hi
      rw [hi]
      exact h1)
  have hIeq : I = {2, 3} := by
    have h1 : ({2, 3} : Set ℕ) ⊆ I :=
      (StdQ6_map_conj_le_iff (K := K) h hI (by intro i hi; simp at hi; omega)).mp
        (by rwa [hPeq] at hle')
    have h2 : I ⊆ ({2, 3} : Set ℕ) :=
      (StdQ6_map_conj_le_iff (K := K) h (by intro i hi; simp at hi; omega) hI).mp
        (by rwa [hPeq] at hQle)
    exact Set.Subset.antisymm h2 h1
  have hPstar : Pstar = (StdQ6 K {2,3}).map (MulAut.conj h).toMonoidHom := by
    rw [hPeq, hIeq]
  have hneTop : Pstar ≠ ⊤ := by
    rw [hPstar]
    intro htop
    have htop' : StdQ6 K {2,3} = ⊤ := by
      have hmap := congrArg (fun X : Subgroup ↥H =>
        X.map (MulAut.conj h⁻¹).toMonoidHom) htop
      rw [Subgroup.map_map] at hmap
      have hcomp' : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
          MonoidHom.id _ := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp', Subgroup.map_id,
        Subgroup.map_top_of_surjective (MulAut.conj h⁻¹).toMonoidHom
          (MulAut.conj h⁻¹).surjective] at hmap
      exact hmap
    exact StdQ6_ne_top_of_mem (K := K) (I := {2,3}) (by intro i hi; simp at hi; omega)
      (j := 3) (by norm_num) (by norm_num) (by simp) htop'
  refine ⟨hneTop, ?_⟩
  have hstd : IsL2 (Bar2 (Hinf (StdQ6 K {2,3}))) n ∨
      (n = 1 ∧ Hinf (StdQ6 K {2,3}) = ⊥) := by
    by_cases hn : n = 1
    · right
      refine ⟨hn, ?_⟩
      have hK2 : Nat.card K = 2 := by rw [hK, hn]; norm_num
      have hbot : Hinf (flagStabilizer 3 K {2,3}) = ⊥ := by
        rw [Hinf_eq_perfectCore]
        exact perfectCore_sp6_eq_bot_of_card_two (K := K) hK2
      have hmap := Hinf_map (eSp K).toMonoidHom (flagStabilizer 3 K {2,3})
      rw [hbot, Subgroup.map_bot] at hmap
      simpa [StdQ6] using hmap.symm
    · left
      have hn2 : 2 ≤ n := by omega
      have h1 : IsL2 (Bar2 (Hinf (flagStabilizer 3 K {2,3}))) n := by
        rw [Hinf_eq_perfectCore]
        exact isL2_bar2_perfectCore_sp6 (K := K) hK hn2
      exact isL2_bar2_hinf_map_equiv (eSp K) (flagStabilizer 3 K {2,3}) h1
  rcases hstd with hL2 | ⟨hn, hbot⟩
  · left
    rw [hPstar]
    exact isL2_bar2_hinf_map_equiv (MulAut.conj h) (StdQ6 K {2,3}) hL2
  · right
    refine ⟨hn, ?_⟩
    rw [hPstar]
    exact Hinf_map_eq_bot (MulAut.conj h) (StdQ6 K {2,3}) hbot

end NaturalSetup

theorem kTab23b_Sp6_line_uncond (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
          Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥)) := by
  obtain ⟨-, K, hF, hFin, hK, hReal⟩ := hline.2
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨π, e, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.exists_natEquiv
      (ι := Fin 3 ⊕ Fin 3) (Γ := CFSG.Open.StatedSp 3 K) (H := H) hReal
  have he' : ∀ (γ : ↥(CFSG.Open.StatedSp 3 K)) (w : W),
      e (((π γ : ↥H) : MulAut W) w) =
        CFSG.Quasithin.natAct (CFSG.Open.StatedSp 3 K) γ (e w) := by
    intro γ w
    have h1 := he γ w
    change e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3)
        (Fin 3 ⊕ Fin 3) K) *ᵥ Multiplicative.toAdd (e w))
    rw [← h1, ofAdd_toAdd]
  have hmodel :
      CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 3 K) =
        H.map (CFSG.Quasithin.H.congrHom e) :=
    (CFSG.Quasithin.H.map_congrHom_eq_natImage (Γ := CFSG.Open.StatedSp 3 K)
      (H := H) (π := π) π.surjective e he').symm
  exact sp6Line_of_map_congr H _ n e hmodel (sp6NaturalLine_holds K n hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
