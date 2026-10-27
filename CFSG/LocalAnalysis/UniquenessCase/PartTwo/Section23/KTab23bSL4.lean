module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
public import CFSG.Quasithin.Background.B69Iso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L
open scoped Pointwise commutatorElement Matrix

@[expose] def SL4Line (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
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

theorem sl4Line_of_map_congr (H : Subgroup (MulAut W)) (H' : Subgroup (MulAut V)) (n : ℕ)
    (e : W ≃* V) (hH' : H' = H.map (CFSG.Quasithin.H.congrHom e))
    (h : SL4Line V H' n) : SL4Line W H n := by
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

theorem kTab23b_SL4_line_of_naturalModel (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsSLn ↥H 4 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 n)
    (hnatural : ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 2 ^ n →
      SL4Line (CFSG.Quasithin.H.StdMod (Fin 4) K)
        (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) n) :
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
  obtain ⟨K, hF, hFin, hK, hReal⟩ := hline.2
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨π, e, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.exists_natEquiv
      (ι := Fin 4) (Γ := CFSG.Open.StatedSL 4 K) (H := H) hReal
  have he' : ∀ (γ : ↥(CFSG.Open.StatedSL 4 K)) (w : W),
      e (((π γ : ↥H) : MulAut W) w) =
        CFSG.Quasithin.natAct (CFSG.Open.StatedSL 4 K) γ (e w) := by
    intro γ w
    have h1 := he γ w
    change e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        Multiplicative.toAdd (e w))
    rw [← h1, ofAdd_toAdd]
  have hmodel :
      CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K) =
        H.map (CFSG.Quasithin.H.congrHom e) :=
    (CFSG.Quasithin.H.map_congrHom_eq_natImage (Γ := CFSG.Open.StatedSL 4 K)
      (H := H) (π := π) π.surjective e he').symm
  exact sl4Line_of_map_congr H _ n e hmodel (hnatural K n hK)

@[expose] noncomputable def piNat4 {K : Type} [Field K] :
    Matrix.SpecialLinearGroup (Fin 4) K →* MulAut (CFSG.Quasithin.H.StdMod (Fin 4) K) :=
  (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSL 4 K)).comp
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).toMonoidHom

theorem piNat4_apply {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 4) K) :
    piNat4 A = CFSG.Quasithin.H.matAut A := by
  change CFSG.Quasithin.H.natAut (CFSG.Open.StatedSL 4 K)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K A) = _
  change CFSG.Quasithin.H.matAut
      (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K A) :
        ↥(CFSG.Open.StatedSL 4 K)) : GL (Fin 4) K) = _
  rfl

@[expose] noncomputable def UH4 (K : Type) [Field K] :
    Subgroup (MulAut (CFSG.Quasithin.H.StdMod (Fin 4) K)) :=
  (unitriangular 4 K).map (piNat4 (K := K))

theorem UH4_eq_map_unitriangular (K : Type) [Field K] :
    UH4 K = (unitriangular 4 K).map (piNat4 (K := K)) := rfl

@[expose] noncomputable def eSL4 (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 4) K ≃*
      CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).trans
    (CFSG.Quasithin.H.natEquiv (CFSG.Open.StatedSL 4 K))

theorem eSL4_coe (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 4) K) :
    ((eSL4 K A : CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) :
      MulAut (CFSG.Quasithin.H.StdMod (Fin 4) K)) = piNat4 A := by
  change ((CFSG.Quasithin.H.natEquiv (CFSG.Open.StatedSL 4 K))
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K) A) :
      MulAut (CFSG.Quasithin.H.StdMod (Fin 4) K)) = _
  rw [CFSG.Quasithin.H.coe_natEquiv]
  rfl

@[expose] noncomputable def StdS4 (K : Type) [Field K] :
    Subgroup (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) :=
  (unitriangular 4 K).map (eSL4 K).toMonoidHom

@[expose] noncomputable def StdB4 (K : Type) [Field K] :
    Subgroup (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) :=
  (upperTriangular 4 K).map (eSL4 K).toMonoidHom

@[expose] noncomputable def Q4 (K : Type) [Field K] (j : Fin 3) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) :=
  flagStabilizer 4 K {((j : ℕ) + 1)}

@[expose] noncomputable def StdQ4 (K : Type) [Field K] (j : Fin 3) :
    Subgroup (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) :=
  (Q4 K j).map (eSL4 K).toMonoidHom

theorem StdB4_eq_map (K : Type) [Field K] :
    StdB4 K = (upperTriangular 4 K).map (eSL4 K).toMonoidHom := rfl

theorem Q4_eq_stabilizer (K : Type) [Field K] (j : Fin 3) :
    Q4 K j = LinearFlag.stabilizer (flagSpace 4 K ((j : ℕ) + 1)) :=
  flagStabilizer_singleton (K := K) (n := 4) ((j : ℕ) + 1)

theorem Q4_eq_flagStabilizer (K : Type) [Field K] (j : Fin 3) :
    Q4 K j = flagStabilizer 4 K {((j : ℕ) + 1)} := rfl

theorem upperTriangular_le_Q4 (K : Type) [Field K] (j : Fin 3) :
    upperTriangular 4 K ≤ Q4 K j :=
  upperTriangular_le_flagStabilizer (K := K) (n := 4) _

theorem Q4_ne_top (K : Type) [Field K] (j : Fin 3) : Q4 K j ≠ ⊤ := by
  intro h
  have hj1 : 1 ≤ (j : ℕ) + 1 := by omega
  have hj4 : (j : ℕ) + 1 < 4 := by omega
  have hnot : LinearFlag.reflection 4 K ((j : ℕ) + 1) hj1 hj4 ∉ Q4 K j := by
    rw [Q4_eq_flagStabilizer]
    rw [(subflag_stabilizer_generation (K := K) (n := 4)
      {((j : ℕ) + 1)}).2.2 ((j : ℕ) + 1) hj1 hj4]
    simp
  exact hnot (h ▸ Subgroup.mem_top _)

theorem StdS4_map_subtype (K : Type) [Field K] :
    (StdS4 K).map (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)).subtype = UH4 K := by
  have hcomp : (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)).subtype.comp
      (eSL4 K).toMonoidHom = piNat4 (K := K) :=
    MonoidHom.ext fun x => eSL4_coe K x
  rw [StdS4, Subgroup.map_map, hcomp, UH4]

theorem normalizer_StdS4 (K : Type) [Field K] :
    Subgroup.normalizer (StdS4 K : Set
      (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))) = StdB4 K := by
  have h := Subgroup.map_equiv_normalizer_eq (unitriangular 4 K) (eSL4 K)
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_unitriangular] at h
  exact h.symm

theorem isSylowTwoOf_StdS4 (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (StdS4 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (p := 2) (K := K) (n := 4) (by norm_num)
  have hU0 : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 4 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map hU0 (eSL4 K).toMonoidHom
  rwa [Subgroup.map_top_of_surjective _ (eSL4 K).surjective] at h

@[expose] def submoduleSub4 (K : Type) [Field K] (W : Submodule K (Fin 4 → K)) :
    Subgroup (CFSG.Quasithin.H.StdMod (Fin 4) K) where
  carrier := {x | Multiplicative.toAdd x ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (x * y) ∈ W
    rw [toAdd_mul]
    exact W.add_mem hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd x⁻¹ ∈ W
    rw [toAdd_inv]
    exact W.neg_mem hx

@[expose] def stdFlagSub4 (K : Type) [Field K] (i : ℕ) :
    Subgroup (CFSG.Quasithin.H.StdMod (Fin 4) K) :=
  submoduleSub4 K (flagSpace 4 K i)

theorem mem_stdFlagSub4 {K : Type} [Field K] {i : ℕ}
    {x : CFSG.Quasithin.H.StdMod (Fin 4) K} :
    x ∈ stdFlagSub4 K i ↔ Multiplicative.toAdd x ∈ flagSpace 4 K i := Iff.rfl

theorem toAdd_matAut_apply4 {K : Type} [Field K] (g : GL (Fin 4) K)
    (x : CFSG.Quasithin.H.StdMod (Fin 4) K) :
    Multiplicative.toAdd (CFSG.Quasithin.H.matAut g x) =
      (g : Matrix (Fin 4) (Fin 4) K) *ᵥ Multiplicative.toAdd x := by
  rw [← ofAdd_toAdd x]
  rfl

theorem mem_fixV_UH4 {K : Type} [Field K] [Finite K] [CharP K 2]
    (x : CFSG.Quasithin.H.StdMod (Fin 4) K) :
    x ∈ CFSG.Quasithin.fixV (UH4 K) ↔ Multiplicative.toAdd x ∈ flagSpace 4 K 1 := by
  have hfix : ({v : Fin 4 → K |
      ∀ u ∈ unitriangular 4 K, (u : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v} : Set (Fin 4 → K)) =
      (flagSpace 4 K 1 : Set (Fin 4 → K)) :=
    (unitriangular_invariant_subspaces (K := K) (n := 4)).2.1
  rw [CFSG.Quasithin.mem_fixV, UH4_eq_map_unitriangular]
  constructor
  · intro hx
    have h1 : Multiplicative.toAdd x ∈ ({v : Fin 4 → K |
        ∀ u ∈ unitriangular 4 K, (u : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v} : Set (Fin 4 → K)) := by
      intro A hA
      have h := hx (piNat4 A) (Subgroup.mem_map_of_mem _ hA)
      have h' := congrArg Multiplicative.toAdd h
      rwa [piNat4_apply, toAdd_matAut_apply4] at h'
    rwa [hfix] at h1
  · intro hx a ha
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ha
    have h1 : Multiplicative.toAdd x ∈ ({v : Fin 4 → K |
        ∀ u ∈ unitriangular 4 K, (u : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v} : Set (Fin 4 → K)) := by
      rwa [hfix]
    apply Multiplicative.toAdd.injective
    rw [piNat4_apply, toAdd_matAut_apply4]
    exact h1 A hA

theorem fixV_UH4 (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.Quasithin.fixV (UH4 K) = stdFlagSub4 K 1 := by
  ext x
  rw [mem_fixV_UH4, mem_stdFlagSub4]

theorem stabilizer_submoduleSub4 (K : Type) [Field K] (W : Submodule K (Fin 4 → K)) :
    letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (CFSG.Quasithin.H.StdMod (Fin 4) K) :=
      MulDistribMulAction.compHom _ (piNat4 (K := K))
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (CFSG.Quasithin.H.StdMod (Fin 4) K) := MulDistribMulAction.toMulAction
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := Set.mulActionSet
    MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 4) K)
      (submoduleSub4 K W : Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) = LinearFlag.stabilizer W := by
  letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (CFSG.Quasithin.H.StdMod (Fin 4) K) :=
    MulDistribMulAction.compHom _ (piNat4 (K := K))
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (CFSG.Quasithin.H.StdMod (Fin 4) K) := MulDistribMulAction.toMulAction
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := Set.mulActionSet
  ext A
  rw [MulAction.mem_stabilizer_iff, LinearFlag.mem_stabilizer]
  constructor
  · intro h
    apply le_antisymm
    · intro v hv
      obtain ⟨w, hw, hwv⟩ := hv
      have hw' : Multiplicative.ofAdd w ∈ (submoduleSub4 K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := hw
      have h1 : A • (Multiplicative.ofAdd w) ∈ (submoduleSub4 K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := by
        have hsm : A • (Multiplicative.ofAdd w) ∈
            A • (submoduleSub4 K W : Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) :=
          Set.smul_mem_smul_set hw'
        rw [h] at hsm
        exact hsm
      have h2 : Multiplicative.toAdd (A • (Multiplicative.ofAdd w)) ∈ W := h1
      change Multiplicative.toAdd (piNat4 A (Multiplicative.ofAdd w)) ∈ W at h2
      rw [piNat4_apply, toAdd_matAut_apply4, toAdd_ofAdd] at h2
      change ((A : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w ∈ W at h2
      rwa [← Matrix.mulVecLin_apply, hwv] at h2
    · intro v hv
      have hv' : Multiplicative.ofAdd v ∈ (submoduleSub4 K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := hv
      have h2 : Multiplicative.ofAdd v ∈ A • (submoduleSub4 K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := by
        rw [show A • (submoduleSub4 K W : Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) =
          (submoduleSub4 K W : Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) from h]
        exact hv'
      obtain ⟨w, hw, hwv⟩ := Set.mem_smul_set.mp h2
      refine ⟨Multiplicative.toAdd w, hw, ?_⟩
      have this := congrArg Multiplicative.toAdd hwv
      change Multiplicative.toAdd (piNat4 A w) = v at this
      rw [piNat4_apply, toAdd_matAut_apply4] at this
      change Multiplicative.toAdd (piNat4 A w) = v
      rw [piNat4_apply, toAdd_matAut_apply4]
      exact this
  · intro h
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Set.mem_smul_set.mp hv
      have hw' : Multiplicative.toAdd w ∈ W := hw
      have h1 : (A : Matrix.SpecialLinearGroup (Fin 4) K) *ᵥ Multiplicative.toAdd w ∈ W := by
        rw [← h]
        exact ⟨w, hw', rfl⟩
      have this := congrArg Multiplicative.toAdd hwv
      change Multiplicative.toAdd v ∈ W
      rw [← this]
      change Multiplicative.toAdd (piNat4 A w) ∈ W
      rwa [piNat4_apply, toAdd_matAut_apply4]
    · intro hv
      have h1 : Multiplicative.toAdd v ∈ W.map (mulVecLin (A : Matrix (Fin 4) (Fin 4) K)) := by
        rw [h]
        exact hv
      obtain ⟨w, hw, hwv⟩ := h1
      refine Set.mem_smul_set.mpr ⟨Multiplicative.ofAdd w, hw, ?_⟩
      apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (piNat4 A (Multiplicative.ofAdd w)) = Multiplicative.toAdd v
      rw [piNat4_apply, toAdd_matAut_apply4]
      exact hwv

theorem StdQ4_eq_stabilizer_stdFlagSub4 (K : Type) [Field K] [Finite K] [CharP K 2]
    (j : Fin 3) :
    letI : MulDistribMulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (CFSG.Quasithin.H.StdMod (Fin 4) K) :=
      MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)).subtype
    letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (CFSG.Quasithin.H.StdMod (Fin 4) K) := MulDistribMulAction.toMulAction
    letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := Set.mulActionSet
    MulAction.stabilizer (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (stdFlagSub4 K ((j : ℕ) + 1) : Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) = StdQ4 K j := by
  letI : MulDistribMulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (CFSG.Quasithin.H.StdMod (Fin 4) K) :=
    MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)).subtype
  letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (CFSG.Quasithin.H.StdMod (Fin 4) K) := MulDistribMulAction.toMulAction
  letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := Set.mulActionSet
  letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (CFSG.Quasithin.H.StdMod (Fin 4) K) :=
    MulDistribMulAction.compHom _ (piNat4 (K := K))
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (CFSG.Quasithin.H.StdMod (Fin 4) K) := MulDistribMulAction.toMulAction
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 4) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) := Set.mulActionSet
  have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
    (eSL4 K) (Equiv.refl (Set (CFSG.Quasithin.H.StdMod (Fin 4) K))) ?_
    (stdFlagSub4 K ((j : ℕ) + 1) : Set (CFSG.Quasithin.H.StdMod (Fin 4) K))
  · have h' : MulAction.stabilizer (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
        (stdFlagSub4 K ((j : ℕ) + 1) : Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) =
        (MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 4) K)
          (stdFlagSub4 K ((j : ℕ) + 1) : Set
            (CFSG.Quasithin.H.StdMod (Fin 4) K))).map (eSL4 K).toMonoidHom := by
      simpa using h.symm
    rw [h']
    have hSL : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 4) K)
        (stdFlagSub4 K ((j : ℕ) + 1) : Set (CFSG.Quasithin.H.StdMod (Fin 4) K)) = Q4 K j := by
      rw [stdFlagSub4, stabilizer_submoduleSub4]
      exact (Q4_eq_stabilizer K j).symm
    rw [hSL, StdQ4]
  · intro g z
    change (piNat4 (K := K) g) '' z = (eSL4 K g : MulAut
      (CFSG.Quasithin.H.StdMod (Fin 4) K)) '' z
    rw [← eSL4_coe K g]

theorem StdQ4_ne_top (K : Type) [Field K] (j : Fin 3) : StdQ4 K j ≠ ⊤ := by
  intro htop
  apply Q4_ne_top K j
  have htop' : StdQ4 K j = (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K)).map
      (eSL4 K).toMonoidHom := by
    rw [htop, Subgroup.map_top_of_surjective _ (eSL4 K).surjective]
  exact (Subgroup.map_injective (f := (eSL4 K).toMonoidHom) (eSL4 K).injective)
    (by simpa [StdQ4] using htop')

@[expose] def superDiag4 {K : Type} [Field K] (A : Matrix (Fin 4) (Fin 4) K) : Fin 3 → K :=
  fun i => A ⟨(i : ℕ), by omega⟩ ⟨(i : ℕ) + 1, by omega⟩

theorem superDiag4_mul {K : Type} [Field K] {A B : Matrix.SpecialLinearGroup (Fin 4) K}
    (hA : A ∈ unitriangular 4 K) (hB : B ∈ unitriangular 4 K) :
    superDiag4 (((A * B : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) =
      superDiag4 ((A : Matrix (Fin 4) (Fin 4) K)) +
        superDiag4 ((B : Matrix (Fin 4) (Fin 4) K)) := by
  have hA' := hA
  have hB' := hB
  rw [mem_unitriangular] at hA' hB'
  have hAB := Matrix.SpecialLinearGroup.coe_mul A B
  rw [hAB]
  funext i
  set r : Fin 4 := ⟨(i : ℕ), by omega⟩ with hr
  set c : Fin 4 := ⟨(i : ℕ) + 1, by omega⟩ with hc
  have hne : r ≠ c := by simp [hr, hc]
  have hcval : (c : ℕ) = (r : ℕ) + 1 := by simp [hr, hc]
  show ((A : Matrix (Fin 4) (Fin 4) K) * (B : Matrix (Fin 4) (Fin 4) K)) r c =
    ((A : Matrix (Fin 4) (Fin 4) K) r c + (B : Matrix (Fin 4) (Fin 4) K) r c)
  rw [Matrix.mul_apply, Finset.sum_eq_add r c hne]
  · rw [hA'.2 r, hB'.2 c, one_mul, mul_one, add_comm]
  · intro k _ hk
    obtain ⟨hkr, hkc⟩ := hk
    by_cases hk' : (k : ℕ) < (r : ℕ)
    · rw [hA'.1 r k hk', zero_mul]
    · have hlt : c < k := by
        rw [Fin.lt_def]
        have h1 : (r : ℕ) ≤ (k : ℕ) := not_lt.mp hk'
        have h2 : (k : ℕ) ≠ (r : ℕ) := fun h => hkr (Fin.ext h)
        have h3 : (k : ℕ) ≠ (c : ℕ) := fun h => hkc (Fin.ext h)
        rw [hcval]; omega
      rw [hB'.1 k c hlt, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ r) h
  · intro h
    exact absurd (Finset.mem_univ c) h

@[expose] noncomputable def superDiagHom (K : Type) [Field K] :
    ↥(unitriangular 4 K) →* Multiplicative (Fin 3 → K) where
  toFun A := Multiplicative.ofAdd (superDiag4 ((A : Matrix.SpecialLinearGroup (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K))
  map_one' := by
    have h : superDiag4 ((1 : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 0 := by
      funext i
      simp [superDiag4]
    show Multiplicative.ofAdd (superDiag4 ((1 : Matrix.SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) = 1
    rw [h]
    rfl
  map_mul' A B := by
    show Multiplicative.ofAdd (superDiag4 (((A * B : ↥(unitriangular 4 K)) :
        Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) =
      Multiplicative.ofAdd (superDiag4 ((A : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)) *
      Multiplicative.ofAdd (superDiag4 ((B : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K))
    rw [← ofAdd_add]
    congr 1
    exact superDiag4_mul A.2 B.2

@[expose] noncomputable def U2 (K : Type) [Field K] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) :=
  ((superDiagHom K).ker).map (unitriangular 4 K).subtype

theorem commutator_unitriangular_le_U2 (K : Type) [Field K] :
    ⁅unitriangular 4 K, unitriangular 4 K⁆ ≤ U2 K := by
  have htop : (⊤ : Subgroup ↥(unitriangular 4 K)).map (unitriangular 4 K).subtype =
      unitriangular 4 K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h := Subgroup.map_mono (f := (unitriangular 4 K).subtype)
    (Abelianization.commutator_subset_ker (superDiagHom K))
  have hc : (_root_.commutator ↥(unitriangular 4 K)) =
      ⁅(⊤ : Subgroup ↥(unitriangular 4 K)), ⊤⁆ := rfl
  rw [hc, Subgroup.map_commutator, htop] at h
  exact h

theorem rootElt_zero_two_mem_commutator (K : Type) [Field K] :
    LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K) ∈
      ⁅unitriangular 4 K, unitriangular 4 K⁆ := by
  have h := Subgroup.commutator_mem_commutator
    (H₁ := unitriangular 4 K) (H₂ := unitriangular 4 K)
    (LinearCover.rootElt_mem_unitriangular (by decide : (0 : Fin 4) < 1) (1 : K))
    (LinearCover.rootElt_mem_unitriangular (by decide : (1 : Fin 4) < 2) (1 : K))
  rwa [LinearCover.commutatorElement_rootElt (K := K) (i := (0 : Fin 4)) (j := (1 : Fin 4))
    (l := (2 : Fin 4)) (by decide) (by decide) (by decide), one_mul] at h

theorem rootElt_zero_three_mem_commutator (K : Type) [Field K] :
    LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K) ∈
      ⁅unitriangular 4 K, unitriangular 4 K⁆ := by
  have h := Subgroup.commutator_mem_commutator
    (H₁ := unitriangular 4 K) (H₂ := unitriangular 4 K)
    (LinearCover.rootElt_mem_unitriangular (by decide : (0 : Fin 4) < 2) (1 : K))
    (LinearCover.rootElt_mem_unitriangular (by decide : (2 : Fin 4) < 3) (1 : K))
  rwa [LinearCover.commutatorElement_rootElt (K := K) (i := (0 : Fin 4)) (j := (2 : Fin 4))
    (l := (3 : Fin 4)) (by decide) (by decide) (by decide), one_mul] at h

theorem superDiagHom_ker_iff {K : Type} [Field K] (A : ↥(unitriangular 4 K)) :
    A ∈ (superDiagHom K).ker ↔
      superDiag4 ((A : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 0 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : Multiplicative.ofAdd (superDiag4 ((A : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)) = Multiplicative.ofAdd (0 : Fin 3 → K) := h
    exact Multiplicative.ofAdd.injective h'
  · intro h
    show Multiplicative.ofAdd (superDiag4 ((A : Matrix.SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) = 1
    rw [h]
    rfl

theorem fixV_U2_map_piNat (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.Quasithin.fixV ((U2 K).map (piNat4 (K := K))) = stdFlagSub4 K 2 := by
  ext x
  rw [CFSG.Quasithin.mem_fixV, mem_stdFlagSub4]
  constructor
  · intro hx
    rw [mem_flagSpace]
    intro j hj
    fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    ·
      by_contra h2
      have hrootU : LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K) ∈
          unitriangular 4 K :=
        LinearCover.rootElt_mem_unitriangular (by decide : (0 : Fin 4) < 2) (1 : K)
      have hker : (⟨LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K),
          hrootU⟩ : ↥(unitriangular 4 K)) ∈ (superDiagHom K).ker := by
        rw [superDiagHom_ker_iff]
        funext i
        fin_cases i <;>
          simp [superDiag4, LinearCover.coe_rootElt_of_ne, Matrix.transvection,
            Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hU2 : LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K) ∈ U2 K :=
        Subgroup.mem_map_of_mem ((unitriangular 4 K).subtype) hker
      have hmem : piNat4 (LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K)) ∈
          (U2 K).map (piNat4 (K := K)) :=
        Subgroup.mem_map_of_mem (piNat4 (K := K)) hU2
      have hfix := hx _ hmem
      have h' := congrArg Multiplicative.toAdd hfix
      have hcoe : ((LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K) :
          Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          Matrix.transvection (0 : Fin 4) (2 : Fin 4) (1 : K) :=
        LinearCover.coe_rootElt_of_ne (by decide) (1 : K)
      rw [piNat4_apply, toAdd_matAut_apply4, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        hcoe, transvection_mulVec] at h'
      have hcoord := congrFun h' 0
      simp only [Pi.add_apply, Pi.single_eq_same, mul_one] at hcoord
      have h0 : Multiplicative.toAdd x 0 + Multiplicative.toAdd x 2 =
          Multiplicative.toAdd x 0 + 0 := by simpa using hcoord
      exact h2 (add_left_cancel h0)
    ·
      by_contra h3
      have hrootU : LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K) ∈
          unitriangular 4 K :=
        LinearCover.rootElt_mem_unitriangular (by decide : (0 : Fin 4) < 3) (1 : K)
      have hker : (⟨LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K),
          hrootU⟩ : ↥(unitriangular 4 K)) ∈ (superDiagHom K).ker := by
        rw [superDiagHom_ker_iff]
        funext i
        fin_cases i <;>
          simp [superDiag4, LinearCover.coe_rootElt_of_ne, Matrix.transvection,
            Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hU2 : LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K) ∈ U2 K :=
        Subgroup.mem_map_of_mem ((unitriangular 4 K).subtype) hker
      have hmem : piNat4 (LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K)) ∈
          (U2 K).map (piNat4 (K := K)) :=
        Subgroup.mem_map_of_mem (piNat4 (K := K)) hU2
      have hfix := hx _ hmem
      have h' := congrArg Multiplicative.toAdd hfix
      have hcoe : ((LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K) :
          Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          Matrix.transvection (0 : Fin 4) (3 : Fin 4) (1 : K) :=
        LinearCover.coe_rootElt_of_ne (by decide) (1 : K)
      rw [piNat4_apply, toAdd_matAut_apply4, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        hcoe, transvection_mulVec] at h'
      have hcoord := congrFun h' 0
      simp only [Pi.add_apply, Pi.single_eq_same, mul_one] at hcoord
      have h0 : Multiplicative.toAdd x 0 + Multiplicative.toAdd x 3 =
          Multiplicative.toAdd x 0 + 0 := by simpa using hcoord
      exact h3 (add_left_cancel h0)
  · intro hx a ha
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨A0, hA0, rfl⟩ := Subgroup.mem_map.mp hA
    have hsd : superDiag4 ((A0 : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 0 := (superDiagHom_ker_iff A0).mp hA0
    have e01 : ((A0 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 := by
      have h := congrFun hsd (0 : Fin 3)
      simpa [superDiag4] using h
    have e12 : ((A0 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 := by
      have h := congrFun hsd (1 : Fin 3)
      simpa [superDiag4] using h
    have e23 : ((A0 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := by
      have h := congrFun hsd (2 : Fin 3)
      simpa [superDiag4] using h
    have hA0U := A0.2
    rw [mem_unitriangular] at hA0U
    have hx' : ∀ j : Fin 4, 2 ≤ (j : ℕ) → Multiplicative.toAdd x j = 0 := by
      intro j hj
      rw [mem_flagSpace] at hx
      exact hx j hj
    apply Multiplicative.toAdd.injective
    rw [piNat4_apply, toAdd_matAut_apply4]
    funext k
    fin_cases k <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hA0U.1, hA0U.2,
        hx' 2 (by norm_num), hx' 3 (by norm_num), e01, e12, e23]

theorem fixV_commutator_UH4 (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.Quasithin.fixV
        (⁅(unitriangular 4 K).map (piNat4 (K := K)),
          (unitriangular 4 K).map (piNat4 (K := K))⁆) = stdFlagSub4 K 2 := by
  have hmap : ⁅(unitriangular 4 K).map (piNat4 (K := K)),
      (unitriangular 4 K).map (piNat4 (K := K))⁆ =
      (⁅unitriangular 4 K, unitriangular 4 K⁆).map (piNat4 (K := K)) := by
    rw [Subgroup.map_commutator]
  rw [hmap]
  ext x
  rw [CFSG.Quasithin.mem_fixV, mem_stdFlagSub4]
  constructor
  · intro hx
    rw [mem_flagSpace]
    intro j hj
    fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · by_contra h2
      have hmem : piNat4 (LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K)) ∈
          (⁅unitriangular 4 K, unitriangular 4 K⁆).map (piNat4 (K := K)) :=
        Subgroup.mem_map_of_mem _ (rootElt_zero_two_mem_commutator K)
      have hfix := hx _ hmem
      have h' := congrArg Multiplicative.toAdd hfix
      have hcoe : ((LinearCover.rootElt (K := K) (0 : Fin 4) (2 : Fin 4) (1 : K) :
          Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          Matrix.transvection (0 : Fin 4) (2 : Fin 4) (1 : K) :=
        LinearCover.coe_rootElt_of_ne (by decide) (1 : K)
      rw [piNat4_apply, toAdd_matAut_apply4, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        hcoe, transvection_mulVec] at h'
      have hcoord := congrFun h' 0
      simp only [Pi.add_apply, Pi.single_eq_same, mul_one] at hcoord
      have h0 : Multiplicative.toAdd x 0 + Multiplicative.toAdd x 2 =
          Multiplicative.toAdd x 0 + 0 := by simpa using hcoord
      exact h2 (add_left_cancel h0)
    · by_contra h3
      have hmem : piNat4 (LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K)) ∈
          (⁅unitriangular 4 K, unitriangular 4 K⁆).map (piNat4 (K := K)) :=
        Subgroup.mem_map_of_mem _ (rootElt_zero_three_mem_commutator K)
      have hfix := hx _ hmem
      have h' := congrArg Multiplicative.toAdd hfix
      have hcoe : ((LinearCover.rootElt (K := K) (0 : Fin 4) (3 : Fin 4) (1 : K) :
          Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          Matrix.transvection (0 : Fin 4) (3 : Fin 4) (1 : K) :=
        LinearCover.coe_rootElt_of_ne (by decide) (1 : K)
      rw [piNat4_apply, toAdd_matAut_apply4, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        hcoe, transvection_mulVec] at h'
      have hcoord := congrFun h' 0
      simp only [Pi.add_apply, Pi.single_eq_same, mul_one] at hcoord
      have h0 : Multiplicative.toAdd x 0 + Multiplicative.toAdd x 3 =
          Multiplicative.toAdd x 0 + 0 := by simpa using hcoord
      exact h3 (add_left_cancel h0)
  · intro hx a ha
    have hle : ⁅unitriangular 4 K, unitriangular 4 K⁆ ≤ U2 K :=
      commutator_unitriangular_le_U2 K
    have hfixV : CFSG.Quasithin.fixV ((U2 K).map (piNat4 (K := K))) ≤
        CFSG.Quasithin.fixV ((⁅unitriangular 4 K, unitriangular 4 K⁆).map
          (piNat4 (K := K))) :=
      CFSG.Quasithin.fixV_anti (Subgroup.map_mono hle)
    have hxU : x ∈ CFSG.Quasithin.fixV ((U2 K).map (piNat4 (K := K))) := by
      rw [fixV_U2_map_piNat]
      exact hx
    exact hfixV hxU a ha
theorem fixV_center_UH4 (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.Quasithin.fixV
        (((Subgroup.center ↥(unitriangular 4 K)).map (unitriangular 4 K).subtype).map
          (piNat4 (K := K))) = stdFlagSub4 K 3 := by
  ext x
  rw [CFSG.Quasithin.mem_fixV, mem_stdFlagSub4, mem_flagSpace]
  constructor
  · intro hx j hj
    fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · by_contra h3
      let z : ↥(unitriangular 4 K) :=
        CFSG.Quasithin.B69.cornerElem (K := K) (by norm_num : 2 ≤ 4) (1 : K)
      have hc : z ∈ Subgroup.center ↥(unitriangular 4 K) :=
        CFSG.Quasithin.B69.cornerElem_mem_center (K := K) (by norm_num : 2 ≤ 4) (1 : K)
      have hmem : piNat4 ((z : ↥(unitriangular 4 K)) : Matrix.SpecialLinearGroup (Fin 4) K) ∈
          (((Subgroup.center ↥(unitriangular 4 K)).map
            (unitriangular 4 K).subtype).map (piNat4 (K := K))) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hc)
      have hfix := hx _ hmem
      have h' := congrArg Multiplicative.toAdd hfix
      have hcoe := CFSG.Quasithin.B69.coe_cornerElem (K := K) (by norm_num : 2 ≤ 4) (1 : K)
      rw [piNat4_apply, toAdd_matAut_apply4, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        hcoe, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec] at h'
      have hcoord := congrFun h' 0
      simp only [Pi.add_apply, CFSG.Quasithin.B69.corner0, CFSG.Quasithin.B69.corner1,
        Pi.single_eq_same, mul_one] at hcoord
      have h0 : Multiplicative.toAdd x 0 + Multiplicative.toAdd x 3 =
          Multiplicative.toAdd x 0 + 0 := by simpa using hcoord
      exact h3 (add_left_cancel h0)
  · intro hx a ha
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp ha0
    have hzU := z0.2
    rw [mem_unitriangular] at hzU
    have hz03 : ∀ i j : Fin 4, i < j → ¬ (i = (0 : Fin 4) ∧ j = (3 : Fin 4)) →
        ((z0 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
      intro i j hij hne
      apply CFSG.Quasithin.B69.entry_zero_of_mem_center hz0 hij
      by_contra h
      push Not at h
      exact hne ⟨Fin.ext h.1, Fin.ext (by have := j.isLt; omega)⟩
    have hx3 : Multiplicative.toAdd x 3 = 0 := hx 3 (by norm_num)
    apply Multiplicative.toAdd.injective
    rw [piNat4_apply, toAdd_matAut_apply4, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    funext k
    fin_cases k <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hzU.1, hzU.2, hx3,
        hz03 0 1 (by norm_num) (by decide), hz03 0 2 (by norm_num) (by decide),
        hz03 1 2 (by norm_num) (by decide), hz03 1 3 (by norm_num) (by decide),
        hz03 2 3 (by norm_num) (by decide)]

@[expose] def Q23 (K : Type) [Field K] : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) :=
  LinearFlag.stabilizer (flagSpace 4 K 2) ⊓ LinearFlag.stabilizer (flagSpace 4 K 3)

theorem flagStabilizer_pair (K : Type) [Field K] :
    flagStabilizer 4 K {2, 3} = flagStabilizer 4 K {2} ⊓ flagStabilizer 4 K {3} := by
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · exact fun g hg => mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (Or.inl hi)
    · exact fun g hg => mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (Or.inr hi)
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    rw [mem_flagStabilizer]
    intro i hi
    rcases hi with rfl | rfl
    · exact mem_flagStabilizer.mp hg.1 2 rfl
    · exact mem_flagStabilizer.mp hg.2 3 rfl

theorem Q23_eq_flagStabilizer (K : Type) [Field K] :
    Q23 K = flagStabilizer 4 K {2, 3} := by
  rw [Q23, flagStabilizer_pair, LinearFlag.flagStabilizer_singleton,
    LinearFlag.flagStabilizer_singleton]

theorem upperTriangular_le_Q23 (K : Type) [Field K] :
    upperTriangular 4 K ≤ Q23 K := by
  refine le_inf ?_ ?_
  · have h := upperTriangular_le_Q4 K 1
    rw [Q4_eq_stabilizer K 1] at h
    simpa using h
  · have h := upperTriangular_le_Q4 K 2
    rw [Q4_eq_stabilizer K 2] at h
    simpa using h

theorem unitriangular_le_Q23 (K : Type) [Field K] :
    unitriangular 4 K ≤ Q23 K :=
  (unitriangular_le_upperTriangular 4 K).trans (upperTriangular_le_Q23 K)

theorem blockLeft_Q23 (K : Type) [Field K] : BlockLeft (Q23 K) 0 2 :=
  blockLeft_zero _ _

theorem blockRight_Q23 (K : Type) [Field K] : BlockRight (Q23 K) 0 2 :=
  blockRight_of_stabilizer (fun _ hg => hg.1)

@[expose] noncomputable def blkMonQ23 (K : Type) [Field K] :
    ↥(Q23 K) →* Matrix (Fin 2) (Fin 2) K :=
  blkMon (Q23 K) 0 2 (by norm_num) (blockLeft_Q23 K) (blockRight_Q23 K)

theorem perfect_perfectCore_Q23 (K : Type) [Field K] [Finite K] :
    Group.IsPerfect ↥(perfectCore (Q23 K)) :=
  Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)

@[expose] noncomputable def blkSLQ23 (K : Type) [Field K] [Finite K] :
    ↥(perfectCore (Q23 K)) →* Matrix.SpecialLinearGroup (Fin 2) K :=
  blkSL (Q23 K) 0 2 (by norm_num) (blockLeft_Q23 K) (blockRight_Q23 K)
    (perfectCore_le (Q23 K)) (perfect_perfectCore_Q23 K)

theorem blkSLQ23_coe (K : Type) [Field K] [Finite K]
    (x : ↥(perfectCore (Q23 K))) :
    ((blkSLQ23 K x : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blkAt 0 2 (by norm_num) (x.1 : Matrix (Fin 4) (Fin 4) K) := rfl

abbrev finFourSumEquiv : Fin 4 ≃ Fin 2 ⊕ Fin 2 := @finSumFinEquiv 2 2 |>.symm

theorem finFourSumEquiv_apply_left {i : Fin 4} (hi : (i : ℕ) < 2) :
    finFourSumEquiv i = Sum.inl (⟨(i : ℕ), hi⟩ : Fin 2) := by
  show (finSumFinEquiv (m := 2) (n := 2)).symm i = Sum.inl ⟨(i : ℕ), hi⟩
  rw [Equiv.symm_apply_eq]
  ext
  simp [finSumFinEquiv]

theorem finFourSumEquiv_apply_right {i : Fin 4} (hi : 2 ≤ (i : ℕ)) :
    finFourSumEquiv i = Sum.inr (⟨(i : ℕ) - 2, by omega⟩ : Fin 2) := by
  show (finSumFinEquiv (m := 2) (n := 2)).symm i = Sum.inr ⟨(i : ℕ) - 2, by omega⟩
  rw [Equiv.symm_apply_eq]
  ext
  have := i.isLt
  simp [finSumFinEquiv]
  omega

@[expose] def embMat4 {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex finFourSumEquiv.symm finFourSumEquiv.symm (Matrix.fromBlocks A 0 0 1)

theorem embMat4_apply_left {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (i j : Fin 4) (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) :
    embMat4 A i j = A ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ := by
  rw [embMat4, Matrix.reindex_apply, Matrix.submatrix_apply]
  change (Matrix.fromBlocks A 0 0 1) (finFourSumEquiv i) (finFourSumEquiv j) =
    A ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
  rw [finFourSumEquiv_apply_left hi, finFourSumEquiv_apply_left hj]
  simp [Matrix.fromBlocks]

theorem embMat4_eq_zero_of_right_left {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (i j : Fin 4) (hi : 2 ≤ (i : ℕ)) (hj : (j : ℕ) < 2) :
    embMat4 A i j = 0 := by
  rw [embMat4, Matrix.reindex_apply, Matrix.submatrix_apply]
  change (Matrix.fromBlocks A 0 0 1) (finFourSumEquiv i) (finFourSumEquiv j) = 0
  rw [finFourSumEquiv_apply_right hi, finFourSumEquiv_apply_left hj]
  simp [Matrix.fromBlocks]

theorem embMat4_eq_zero_of_right_ne {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (i j : Fin 4) (hi : 2 ≤ (i : ℕ)) (hj : 2 ≤ (j : ℕ)) (hne : i ≠ j) :
    embMat4 A i j = 0 := by
  rw [embMat4, Matrix.reindex_apply, Matrix.submatrix_apply]
  change (Matrix.fromBlocks A 0 0 1) (finFourSumEquiv i) (finFourSumEquiv j) = 0
  rw [finFourSumEquiv_apply_right hi, finFourSumEquiv_apply_right hj]
  have hne' : (⟨(i : ℕ) - 2, by omega⟩ : Fin 2) ≠ ⟨(j : ℕ) - 2, by omega⟩ := by
    intro h
    exact hne (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
  simp [Matrix.fromBlocks, hne']

theorem embMat4_one (K : Type) [Field K] :
    embMat4 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [embMat4, Matrix.fromBlocks_one]
  exact map_one (Matrix.reindexRingEquiv K finFourSumEquiv.symm)

theorem embMat4_mul {K : Type} [Field K] (A B : Matrix (Fin 2) (Fin 2) K) :
    embMat4 (A * B) = embMat4 A * embMat4 B := by
  have h := map_mul (Matrix.reindexRingEquiv K finFourSumEquiv.symm)
    (Matrix.fromBlocks A 0 0 1) (Matrix.fromBlocks B 0 0 1)
  change (Matrix.reindexRingEquiv K finFourSumEquiv.symm)
      (Matrix.fromBlocks (A * B) 0 0 1) =
    (Matrix.reindexRingEquiv K finFourSumEquiv.symm) (Matrix.fromBlocks A 0 0 1) *
      (Matrix.reindexRingEquiv K finFourSumEquiv.symm) (Matrix.fromBlocks B 0 0 1)
  rw [← h]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]

theorem embMat4_det {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    (embMat4 A).det = A.det := by
  rw [embMat4, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

@[expose] noncomputable def embSL4 (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun A := ⟨embMat4 A.1, by rw [embMat4_det]; exact A.2⟩
  map_one' := Subtype.ext (embMat4_one K)
  map_mul' A B := Subtype.ext (embMat4_mul A.1 B.1)

theorem coe_embSL4 (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((embSL4 K A : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      embMat4 A.1 := rfl

theorem embSL4_mem_Q23 (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    embSL4 K A ∈ Q23 K := by
  refine ⟨?_, ?_⟩
  · refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv2 : ∀ j : Fin 4, 2 ≤ (j : ℕ) → v j = 0 := LinearFlag.mem_flagSpace.mp hv
    refine LinearFlag.mem_flagSpace.mpr ?_
    intro k hk
    change (((((embSL4 K) A : Matrix.SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ v) k) = 0
    rw [coe_embSL4, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < 2
    · rw [embMat4_eq_zero_of_right_left _ _ _ (by omega) hl, zero_mul]
    · rw [hv2 l (by omega), mul_zero]
  · refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv2 : ∀ j : Fin 4, 3 ≤ (j : ℕ) → v j = 0 := LinearFlag.mem_flagSpace.mp hv
    refine LinearFlag.mem_flagSpace.mpr ?_
    intro k hk
    change (((((embSL4 K) A : Matrix.SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ v) k) = 0
    rw [coe_embSL4, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < 2
    · rw [embMat4_eq_zero_of_right_left _ _ _ (by omega) hl, zero_mul]
    · by_cases hl3 : (l : ℕ) < 3
      · have hkl : k ≠ l := by
          intro h; rw [h] at hk; omega
        rw [embMat4_eq_zero_of_right_ne _ _ _ (by omega) (by omega) hkl, zero_mul]
      · rw [hv2 l (by omega), mul_zero]

theorem embSL4_range_perfect (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : ∃ s : Finset K, s.card = 4) :
    ⁅(embSL4 K).range, (embSL4 K).range⁆ = (embSL4 K).range := by
  have h : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Group.isPerfect_def.mp
      (CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK)
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

theorem embSL4_mem_perfectCore (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : ∃ s : Finset K, s.card = 4) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    embSL4 K A ∈ perfectCore (Q23 K) := by
  have hle : (embSL4 K).range ≤ Q23 K := by
    rintro _ ⟨B, rfl⟩
    exact embSL4_mem_Q23 K B
  exact le_perfectCore_of_perfect (H := Q23 K) hle (embSL4_range_perfect K hK) ⟨A, rfl⟩

theorem blkSLQ23_embSL4 (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : ∃ s : Finset K, s.card = 4) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    blkSLQ23 K ⟨embSL4 K A, embSL4_mem_perfectCore K hK A⟩ = A := by
  apply Subtype.ext
  rw [blkSLQ23_coe]
  ext i j
  have hi : (i : ℕ) < 2 := i.isLt
  have hj : (j : ℕ) < 2 := j.isLt
  change embMat4 (A : Matrix (Fin 2) (Fin 2) K) ⟨0 + (i : ℕ), by omega⟩
      ⟨0 + (j : ℕ), by omega⟩ = (A : Matrix (Fin 2) (Fin 2) K) i j
  rw [embMat4_apply_left _ _ _ (by show 0 + (i : ℕ) < 2; omega)
    (by show 0 + (j : ℕ) < 2; omega)]
  have h1 : (⟨((⟨0 + (i : ℕ), by omega⟩ : Fin 4) : ℕ), by
      have := i.isLt
      show 0 + (i : ℕ) < 2
      omega⟩ : Fin 2) = i := by
    apply Fin.ext
    simp
  have h2 : (⟨((⟨0 + (j : ℕ), by omega⟩ : Fin 4) : ℕ), by
      have := j.isLt
      show 0 + (j : ℕ) < 2
      omega⟩ : Fin 2) = j := by
    apply Fin.ext
    simp
  rw [h1, h2]

theorem blkSLQ23_surjective (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : ∃ s : Finset K, s.card = 4) :
    Function.Surjective (blkSLQ23 K) :=
  fun A => ⟨⟨embSL4 K A, embSL4_mem_perfectCore K hK A⟩, blkSLQ23_embSL4 K hK A⟩

@[expose] noncomputable def diagCharQ23 (K : Type) [Field K] :
    ↥(Q23 K) →* K × K where
  toFun g := ((g.1 : Matrix (Fin 4) (Fin 4) K) 2 2, (g.1 : Matrix (Fin 4) (Fin 4) K) 3 3)
  map_one' := by
    simp [Matrix.SpecialLinearGroup.coe_one]
  map_mul' g h := by
    have hg2 : g.1 ∈ LinearFlag.stabilizer (flagSpace 4 K 2) := g.2.1
    have hh2 : h.1 ∈ LinearFlag.stabilizer (flagSpace 4 K 2) := h.2.1
    have hh3 : h.1 ∈ LinearFlag.stabilizer (flagSpace 4 K 3) := h.2.2
    have e22 : (((g.1 * h.1 : Matrix.SpecialLinearGroup (Fin 4) K)) :
        Matrix (Fin 4) (Fin 4) K) 2 2 =
        (g.1 : Matrix (Fin 4) (Fin 4) K) 2 2 * (h.1 : Matrix (Fin 4) (Fin 4) K) 2 2 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single (2 : Fin 4)]
      · intro k _ hk
        by_cases hk2 : (k : ℕ) < 2
        · rw [stabilizer_entries hg2 hk2 (le_rfl : (2 : Fin 4) ≤ 2), zero_mul]
        · have hk3 : 3 ≤ (k : ℕ) := by
            have : (k : ℕ) ≠ 2 := fun hh => hk (Fin.ext hh)
            omega
          rw [stabilizer_entries hh3 (by norm_num : (2 : Fin 4) < 3) hk3, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ _) hk
    have e33 : (((g.1 * h.1 : Matrix.SpecialLinearGroup (Fin 4) K)) :
        Matrix (Fin 4) (Fin 4) K) 3 3 =
        (g.1 : Matrix (Fin 4) (Fin 4) K) 3 3 * (h.1 : Matrix (Fin 4) (Fin 4) K) 3 3 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single (3 : Fin 4)]
      · intro k _ hk
        have hk3 : (k : ℕ) < 3 := by
          have : (k : ℕ) ≠ 3 := fun hh => hk (Fin.ext hh)
          omega
        rw [stabilizer_entries (g.2.2) hk3 (le_rfl : (3 : Fin 4) ≤ 3), zero_mul]
      · intro hk; exact absurd (Finset.mem_univ _) hk
    have hgh : ((g * h : ↥(Q23 K)) : Matrix.SpecialLinearGroup (Fin 4) K) = g.1 * h.1 := rfl
    rw [hgh, e22, e33]
    rfl

theorem diagCharQ23_eq_one_of_mem_perfectCore (K : Type) [Field K] [Finite K]
    (x : ↥(perfectCore (Q23 K))) :
    diagCharQ23 K (Subgroup.inclusion (perfectCore_le (Q23 K)) x) = 1 := by
  let φ : ↥(perfectCore (Q23 K)) →* K × K :=
    (diagCharQ23 K).comp (Subgroup.inclusion (perfectCore_le (Q23 K)))
  have hker : φ.toHomUnits.ker = ⊤ := by
    rw [eq_top_iff, ← (perfect_perfectCore_Q23 K).commutator_eq_top]
    exact Abelianization.commutator_subset_ker _
  have hx : φ.toHomUnits x = 1 := by
    have : x ∈ φ.toHomUnits.ker := by rw [hker]; exact Subgroup.mem_top x
    exact this
  have h := congrArg Units.val hx
  simpa [φ] using h

theorem perfectCore_Q23_diag (K : Type) [Field K] [Finite K]
    (x : ↥(perfectCore (Q23 K))) :
    ((x.1 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 ∧
      ((x.1 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
  have h := diagCharQ23_eq_one_of_mem_perfectCore K x
  constructor
  · have := congrArg Prod.fst h
    simpa [diagCharQ23] using this
  · have := congrArg Prod.snd h
    simpa [diagCharQ23] using this

theorem blkSLQ23_ker_le_unitriangular (K : Type) [Field K] [Finite K] [CharP K 2]
    (x : ↥(perfectCore (Q23 K))) (hx : x ∈ (blkSLQ23 K).ker) :
    (x.1 : Matrix.SpecialLinearGroup (Fin 4) K) ∈ unitriangular 4 K := by
  have hxQ : (x.1 : Matrix.SpecialLinearGroup (Fin 4) K) ∈ Q23 K := perfectCore_le (Q23 K) x.2
  have hg2 : (x.1 : Matrix.SpecialLinearGroup (Fin 4) K) ∈
      LinearFlag.stabilizer (flagSpace 4 K 2) := hxQ.1
  have hg3 : (x.1 : Matrix.SpecialLinearGroup (Fin 4) K) ∈
      LinearFlag.stabilizer (flagSpace 4 K 3) := hxQ.2
  have hblk : blkAt 0 2 (by norm_num)
      ((x.1 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    have hx' := hx
    rw [MonoidHom.mem_ker] at hx'
    have h := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) K =>
      (y : Matrix (Fin 2) (Fin 2) K)) hx'
    rw [blkSLQ23_coe] at h
    simpa using h
  have hd := perfectCore_Q23_diag K x
  have h00 : ((x.1 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hblk
    simpa [blkAt_apply] using this
  have h11 : ((x.1 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hblk
    simpa [blkAt_apply] using this
  have h10 : ((x.1 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hblk
    simpa [blkAt_apply] using this
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i
    · exact absurd hij (by simp)
    · fin_cases j
      · exact h10
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
    · fin_cases j
      · exact stabilizer_entries hg2 (by norm_num) (by norm_num)
      · exact stabilizer_entries hg2 (by norm_num) (by norm_num)
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
    · fin_cases j
      · exact stabilizer_entries hg2 (by norm_num) (by norm_num)
      · exact stabilizer_entries hg2 (by norm_num) (by norm_num)
      · exact stabilizer_entries hg3 (by norm_num) (by norm_num)
      · exact absurd hij (by simp)
  · fin_cases i
    · exact h00
    · exact h11
    · exact hd.1
    · exact hd.2

theorem blkSLQ23_ker_isPGroup (K : Type) [Field K] [Finite K] [CharP K 2]
    (n : ℕ) (hK : Nat.card K = 2 ^ n) :
    IsPGroup 2 (blkSLQ23 K).ker := by
  have hU : IsPGroup 2 (unitriangular 4 K) := by
    refine IsPGroup.of_card (n := n * (4 * (4 - 1) / 2)) ?_
    rw [card_unitriangular, hK, ← pow_mul]
  have hker_le : (blkSLQ23 K).ker ≤
      (unitriangular 4 K).comap (perfectCore (Q23 K)).subtype := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact blkSLQ23_ker_le_unitriangular K x hx
  have hcomap : IsPGroup 2 ((unitriangular 4 K).comap (perfectCore (Q23 K)).subtype) :=
    IsPGroup.comap_of_injective (H := unitriangular 4 K) hU (perfectCore (Q23 K)).subtype
      Subtype.coe_injective
  exact hcomap.to_le hker_le

theorem isL2_bar2_perfectCore_Q23 (K : Type) [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    IsL2 (Bar2 (perfectCore (Q23 K))) n := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab := sl2_nonabelian hK4
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isSimple hK4
  have hmodel : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  let e : Bar2 (perfectCore (Q23 K)) ≃* StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab (blkSLQ23 K) (blkSLQ23_surjective K hK4)
      (blkSLQ23_ker_isPGroup K n hK)).trans sl2EquivStatedProj
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) e.symm hmodel

theorem perfectCore_Q23_eq_bot_of_card_two (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) : perfectCore (Q23 K) = ⊥ := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨1, by rw [hK2]; norm_num⟩
  obtain ⟨k, hk⟩ := hK
  have hSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
    norm_num
  have hU : IsPGroup 2 (unitriangular 4 K) := by
    refine IsPGroup.of_card (n := k * (4 * (4 - 1) / 2)) ?_
    rw [card_unitriangular, hk, ← pow_mul]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent (unitriangular 4 K) := hU.isNilpotent
  haveI : Group.IsSolvable (unitriangular 4 K) := inferInstance
  have hrange_bot : (blkSLQ23 K).range = ⊥ := by
    have himg_perf : Group.IsPerfect ↥(blkSLQ23 K).range := by
      rw [Subgroup.isPerfect_iff]
      have h' : (⁅(⊤ : Subgroup ↥(perfectCore (Q23 K))),
          (⊤ : Subgroup ↥(perfectCore (Q23 K)))⁆) = ⊤ :=
        Group.isPerfect_def.mp (perfect_perfectCore_Q23 K)
      have h2 : ((⁅(⊤ : Subgroup ↥(perfectCore (Q23 K))),
          (⊤ : Subgroup ↥(perfectCore (Q23 K)))⁆).map (blkSLQ23 K)) =
          (⊤ : Subgroup ↥(perfectCore (Q23 K))).map (blkSLQ23 K) := by rw [h']
      rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h2
    have hsolv : Group.IsSolvable ↥(blkSLQ23 K).range := inferInstance
    have h1 := (isSolvable_iff_perfectCore_eq_bot (blkSLQ23 K).range).mp hsolv
    rw [perfectCore_eq_self_of_perfect
      ((Subgroup.isPerfect_iff (H := (blkSLQ23 K).range)).mp himg_perf)] at h1
    exact h1
  have hle_ker : perfectCore (Q23 K) ≤ unitriangular 4 K := by
    intro x hx
    have hxk : (⟨x, hx⟩ : ↥(perfectCore (Q23 K))) ∈ (blkSLQ23 K).ker := by
      rw [MonoidHom.mem_ker]
      have hmem : blkSLQ23 K ⟨x, hx⟩ ∈ (blkSLQ23 K).range := ⟨_, rfl⟩
      rw [hrange_bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact blkSLQ23_ker_le_unitriangular K ⟨x, hx⟩ hxk
  let f : ↥(perfectCore (Q23 K)) →* ↥(unitriangular 4 K) :=
    { toFun := fun x => ⟨x.1, hle_ker x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hsolv : Group.IsSolvable ↥(perfectCore (Q23 K)) :=
    Group.isSolvable_of_isSolvable_injective (f := f)
      (fun a b h => Subtype.ext (by
        have h1 : ((f a : ↥(unitriangular 4 K)) : Matrix.SpecialLinearGroup (Fin 4) K) =
            ((f b : ↥(unitriangular 4 K)) : Matrix.SpecialLinearGroup (Fin 4) K) :=
          congrArg Subtype.val h
        exact h1))
  have hpc := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Q23 K))).mp hsolv
  rw [perfectCore_eq_self_of_perfect
    ((Subgroup.isPerfect_iff (H := perfectCore (Q23 K))).mp
      (perfect_perfectCore_Q23 K))] at hpc
  exact hpc

theorem center_StdS4_map_eq (K : Type) [Field K] :
    (Subgroup.center ↥(StdS4 K)).map
        ((CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)).subtype.comp (StdS4 K).subtype) =
      ((Subgroup.center ↥(unitriangular 4 K)).map (unitriangular 4 K).subtype).map
        (piNat4 (K := K)) := by
  let ec : ↥(unitriangular 4 K) ≃* ↥(StdS4 K) :=
    (unitriangular 4 K).equivMapOfInjective (eSL4 K).toMonoidHom (eSL4 K).injective
  have hcomp : ((CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)).subtype.comp
      (StdS4 K).subtype).comp ec.toMonoidHom =
      (piNat4 (K := K)).comp (unitriangular 4 K).subtype := by
    refine DFunLike.ext _ _ fun z => ?_
    exact eSL4_coe K z
  rw [← Subgroup.map_center_eq ec, Subgroup.map_map]
  change Subgroup.map (((CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)).subtype.comp
      (StdS4 K).subtype).comp ec.toMonoidHom) (Subgroup.center ↥(unitriangular 4 K)) =
    Subgroup.map (piNat4 (K := K)) (Subgroup.map (unitriangular 4 K).subtype
      (Subgroup.center ↥(unitriangular 4 K)))
  rw [hcomp, ← Subgroup.map_map]

theorem map_center_equiv {G H : Type} [Group G] [Group H]
    (A : Subgroup G) (e : G ≃* H) :
    (Subgroup.center ↥(A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype =
      ((Subgroup.center ↥A).map A.subtype).map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨a, ha, hya⟩ := Subgroup.mem_map.mp y.2
    have hcent : (⟨a, ha⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro b
      have hcomm : y * ⟨e b.1, Subgroup.mem_map_of_mem e.toMonoidHom b.2⟩ =
          ⟨e b.1, Subgroup.mem_map_of_mem e.toMonoidHom b.2⟩ * y :=
        (Subgroup.mem_center_iff.mp hy) _ |>.symm
      have h1 : (y : H) * e b.1 = e b.1 * (y : H) := congrArg Subtype.val hcomm
      have hy' : (y : H) = e a := hya.symm
      rw [hy'] at h1
      have h2 := congrArg (fun z => e.symm z) h1
      apply Subtype.ext
      change b.1 * a = a * b.1
      simpa using h2.symm
    refine Subgroup.mem_map.mpr ⟨A.subtype ⟨a, ha⟩,
      Subgroup.mem_map_of_mem A.subtype hcent, ?_⟩
    show e a = (y : H)
    exact hya
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Subgroup.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hB : e a.1 ∈ A.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom a.2
    have hcenterB : (⟨e a.1, hB⟩ : ↥(A.map e.toMonoidHom)) ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨b, hb, hyb⟩ := Subgroup.mem_map.mp y.2
      have hy : y = ⟨e b, Subgroup.mem_map_of_mem e.toMonoidHom hb⟩ := Subtype.ext hyb.symm
      rw [hy]
      have hcomm := (Subgroup.mem_center_iff.mp ha) ⟨b, hb⟩
      have h2 := congrArg (fun z : ↥A => e (A.subtype z)) hcomm
      have h2' : e b * e a.1 = e a.1 * e b := by
        simpa [map_mul] using h2
      exact Subtype.ext h2'
    exact Subgroup.mem_map.mpr ⟨⟨e a.1, hB⟩, hcenterB, rfl⟩

theorem map_center_conj_eq {G : Type} [Group G] (A : Subgroup G) (h : G) :
    (Subgroup.center ↥(A.map (MulAut.conj h).toMonoidHom)).map
        (A.map (MulAut.conj h).toMonoidHom).subtype =
      ((Subgroup.center ↥A).map A.subtype).map (MulAut.conj h).toMonoidHom :=
  map_center_equiv A (MulAut.conj h)

open CFSG.Quasithin

theorem map_center_injective {G H : Type} [Group G] [Group H]
    (A : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    (Subgroup.center ↥(A.map f)).map (A.map f).subtype =
      ((Subgroup.center ↥A).map A.subtype).map f := by
  let e : ↥A ≃* ↥(A.map f) := A.equivMapOfInjective f hf
  have hc : (Subgroup.center ↥A).map e.toMonoidHom = Subgroup.center ↥(A.map f) :=
    Subgroup.map_center_eq e
  have hcomp : (A.map f).subtype.comp e.toMonoidHom = f.comp A.subtype := by
    ext x
    rfl
  rw [show Subgroup.center ↥(A.map f) = (Subgroup.center ↥A).map e.toMonoidHom
    from hc.symm]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem StdQ4_inf_eq_map_Q23 (K : Type) [Field K] [Finite K] [CharP K 2] :
    StdQ4 K 1 ⊓ StdQ4 K 2 = (Q23 K).map (eSL4 K).toMonoidHom := by
  rw [StdQ4, StdQ4, ← Subgroup.map_inf _ _ _ (eSL4 K).injective]
  change Subgroup.map (eSL4 K).toMonoidHom
      (flagStabilizer 4 K {1 + 1} ⊓ flagStabilizer 4 K {2 + 1}) =
    Subgroup.map (eSL4 K).toMonoidHom (Q23 K)
  rw [Q23_eq_flagStabilizer, flagStabilizer_pair]

theorem sl4NaturalModel_holds :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 2 ^ n →
      SL4Line (CFSG.Quasithin.H.StdMod (Fin 4) K)
        (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) n := by
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
  set V := CFSG.Quasithin.H.StdMod (Fin 4) K with hV
  set H : Subgroup (MulAut V) := CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K) with hH
  change SL4Line V H n
  unfold SL4Line
  intro S
  intro ℓ Pℓ
  intro Tstar hTnorm hT2 hST
  intro Good Pstar hmin
  classical
  have hSylS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥H) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hSylStd : CFSG.QuasithinUnique.IsSylowTwoOf (StdS4 K) ⊤ := isSylowTwoOf_StdS4 (K := K)
  obtain ⟨h, -, hconj⟩ :=
    CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hSylStd hSylS
  let hV' : MulAut V := ((h : ↥H) : MulAut V)
  let SH : Subgroup (MulAut V) := (S : Subgroup ↥H).map H.subtype
  have hcomp : H.subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj hV').toMonoidHom.comp H.subtype := by
    ext x
    rfl
  have hSH : SH = (UH4 K).map (MulAut.conj hV').toMonoidHom := by
    dsimp [SH]
    rw [hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map, StdS4_map_subtype]
    rfl
  have hℓ : ℓ = (stdFlagSub4 K 1).map hV'.toMonoidHom := by
    have h1 : ℓ = CFSG.Quasithin.fixV SH := by
      dsimp [ℓ, SH]
      rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
    rw [h1, hSH, fixV_map_conj, fixV_UH4]
  have hPℓ : Pℓ = (StdQ4 K 0).map (MulAut.conj h).toMonoidHom := by
    have hstab := stabilizer_map_conj_subgroup H h (stdFlagSub4 K 1)
    dsimp [Pℓ]
    rw [hℓ]
    change MulAction.stabilizer ↥H
      (((stdFlagSub4 K 1).map hV'.toMonoidHom : Subgroup V) : Set V) =
      (StdQ4 K 0).map (MulAut.conj h).toMonoidHom
    erw [hstab]
    congr 1
    change MulAction.stabilizer ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K))
      (stdFlagSub4 K 1 : Set V) = StdQ4 K 0
    exact StdQ4_eq_stabilizer_stdFlagSub4 (K := K) 0
  have hB : Subgroup.normalizer (S : Set ↥H) =
      (StdB4 K).map (MulAut.conj h).toMonoidHom := by
    change Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H) =
      (StdB4 K).map (MulAut.conj h).toMonoidHom
    rw [hconj, ← Subgroup.map_equiv_normalizer_eq (StdS4 K) (MulAut.conj h), normalizer_StdS4]
  have hBP : Subgroup.normalizer (S : Set ↥H) ≤ Pstar :=
    hmin.1.1.normalizer_le S hmin.1.2.1
  have hP'B : StdB4 K ≤ Pstar.map (MulAut.conj h⁻¹).toMonoidHom := by
    have hmono := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hBP
    rw [hB, Subgroup.map_map] at hmono
    have hcomp3 : ((MulAut.conj h⁻¹).toMonoidHom).comp ((MulAut.conj h).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hcomp3, Subgroup.map_id] at hmono
  let A : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) :=
    (Pstar.map (MulAut.conj h⁻¹).toMonoidHom).comap (eSL4 K).toMonoidHom
  have hBA : upperTriangular 4 K ≤ A := by
    rw [show A = (Pstar.map (MulAut.conj h⁻¹).toMonoidHom).comap
      (eSL4 K).toMonoidHom from rfl, ← Subgroup.map_le_iff_le_comap]
    rw [← StdB4_eq_map]
    exact hP'B
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  set I : Set ℕ := borelOvergroupCuts A with hI
  have hIcuts : ∀ i ∈ I, 1 ≤ i ∧ i < 4 := fun i hi => ⟨hi.1, hi.2.1⟩
  have hPP' : (Pstar.map (MulAut.conj h⁻¹).toMonoidHom).map
      (MulAut.conj h).toMonoidHom = Pstar := by
    rw [Subgroup.map_map]
    have hcomp4 : ((MulAut.conj h).toMonoidHom).comp ((MulAut.conj h⁻¹).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp4, Subgroup.map_id]
  have hPst : Pstar = ((flagStabilizer 4 K I).map (eSL4 K).toMonoidHom).map
      (MulAut.conj h).toMonoidHom := by
    have hP' : Pstar.map (MulAut.conj h⁻¹).toMonoidHom =
        (flagStabilizer 4 K I).map (eSL4 K).toMonoidHom := by
      rw [← hAeq]
      exact (Subgroup.map_comap_eq_self_of_surjective (eSL4 K).surjective
        (Pstar.map (MulAut.conj h⁻¹).toMonoidHom)).symm
    rw [← hPP', hP']
  have hmem1 : (1 : ℕ) ∈ I ↔ flagStabilizer 4 K I ≤ flagStabilizer 4 K {1} := by
    constructor
    · intro hi g hg
      rw [mem_flagStabilizer] at hg ⊢
      intro j hj
      rw [Set.mem_singleton_iff] at hj
      subst hj
      exact hg 1 hi
    · intro hle
      by_contra h1I
      have h11 : 1 ≤ (1 : ℕ) := le_rfl
      have h14 : (1 : ℕ) < 4 := by norm_num
      have hr : LinearFlag.reflection 4 K 1 h11 h14 ∈ flagStabilizer 4 K I := by
        rw [(subflag_stabilizer_generation (K := K) (n := 4) I).2.2 1 h11 h14]
        exact h1I
      have hr' := hle hr
      rw [(subflag_stabilizer_generation (K := K) (n := 4) {1}).2.2 1 h11 h14] at hr'
      exact hr' rfl
  have h1notI : (1 : ℕ) ∉ I := by
    intro hi
    exact hmin.1.2.2.2 (by
      rw [hPst, hPℓ]
      exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
        (Subgroup.map_mono (f := (eSL4 K).toMonoidHom) ((hmem1).mp hi)))
  have hQ4le : Q23 K ≤ flagStabilizer 4 K I := by
    rw [Q23_eq_flagStabilizer]
    intro g hg
    rw [mem_flagStabilizer]
    intro j hj
    have hj' : j = 2 ∨ j = 3 := by
      have h1 := hIcuts j hj
      have h2 : j ≠ 1 := fun h => h1notI (h ▸ hj)
      omega
    rcases hj' with rfl | rfl
    · exact mem_flagStabilizer.mp hg 2 (by norm_num)
    · exact mem_flagStabilizer.mp hg 3 (by norm_num)
  let W2 : Subgroup V := (stdFlagSub4 K 2).map hV'.toMonoidHom
  let W3 : Subgroup V := (stdFlagSub4 K 3).map hV'.toMonoidHom
  have hSH_normal : ∀ t ∈ Tstar, SH.map (MulAut.conj t).toMonoidHom = SH := by
    intro t ht
    have hTstarH : Tstar ⊓ H = SH := by
      have hSylUH : CFSG.QuasithinUnique.IsSylowTwoOf (UH4 K) H := by
        have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map hSylStd H.subtype
        rwa [show (⊤ : Subgroup ↥H).map H.subtype = H from by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype],
          StdS4_map_subtype] at h
      have hHmap : H.map (MulAut.conj hV').toMonoidHom = H :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer h.2)
      have hSylSH : CFSG.QuasithinUnique.IsSylowTwoOf SH H := by
        have h := hSylUH.map_equiv (MulAut.conj hV')
        rwa [← hSH, hHmap] at h
      have hX2 : IsPGroup 2 ↥(Tstar ⊓ H) := by
        intro x
        obtain ⟨k, hk⟩ := hT2 ⟨(x : MulAut V), x.2.1⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      exact hSylSH.eq_of_le (le_inf hST (Subgroup.map_subtype_le _)) inf_le_right hX2
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
  have hW2eq : W2 = CFSG.Quasithin.fixV ⁅SH, SH⁆ := by
    dsimp [W2]
    rw [hSH, ← Subgroup.map_commutator, fixV_map_conj (⁅UH4 K, UH4 K⁆) hV']
    rw [show CFSG.Quasithin.fixV ⁅UH4 K, UH4 K⁆ = stdFlagSub4 K 2 from
      fixV_commutator_UH4 K]
    rfl
  have hW2inv : ∀ t ∈ Tstar, W2.map t.toMonoidHom = W2 := by
    intro t ht
    have hcomm : ⁅SH, SH⁆.map (MulAut.conj t).toMonoidHom = ⁅SH, SH⁆ := by
      rw [Subgroup.map_commutator, hSH_normal t ht]
    calc W2.map t.toMonoidHom = (CFSG.Quasithin.fixV ⁅SH, SH⁆).map t.toMonoidHom := by rw [hW2eq]
      _ = CFSG.Quasithin.fixV (⁅SH, SH⁆.map (MulAut.conj t).toMonoidHom) :=
        (fixV_map_conj ⁅SH, SH⁆ t).symm
      _ = CFSG.Quasithin.fixV ⁅SH, SH⁆ := by rw [hcomm]
      _ = W2 := hW2eq.symm
  have hcenterSH : (Subgroup.center ↥(S : Subgroup ↥H)).map
      (H.subtype.comp (S : Subgroup ↥H).subtype) =
      (Subgroup.center ↥SH).map SH.subtype := by
    have h := map_center_injective (S : Subgroup ↥H) H.subtype H.subtype_injective
    rw [Subgroup.map_map] at h
    exact h.symm
  have hcenterSH_eq : (Subgroup.center ↥SH).map SH.subtype =
      ((Subgroup.center ↥(UH4 K)).map (UH4 K).subtype).map
        (MulAut.conj hV').toMonoidHom := by
    rw [hSH]
    exact map_center_conj_eq (UH4 K) hV'
  have hcenterUH4 : (Subgroup.center ↥(UH4 K)).map (UH4 K).subtype =
      ((Subgroup.center ↥(StdS4 K)).map (StdS4 K).subtype).map H.subtype := by
    have h := map_center_injective (StdS4 K) H.subtype H.subtype_injective
    rwa [show (StdS4 K).map H.subtype = UH4 K from StdS4_map_subtype K] at h
  have hW3eq : W3 = CFSG.Quasithin.fixV ((Subgroup.center ↥SH).map SH.subtype) := by
    dsimp [W3]
    conv_rhs => rw [hcenterSH_eq]
    conv_rhs => rw [hcenterUH4]
    rw [show ((Subgroup.center ↥(StdS4 K)).map (StdS4 K).subtype).map H.subtype =
      (Subgroup.center ↥(StdS4 K)).map (H.subtype.comp (StdS4 K).subtype) from
      Subgroup.map_map _ _ _]
    rw [fixV_map_conj _ hV', center_StdS4_map_eq, fixV_center_UH4]
    rfl
  have hcenterSH_normal : ∀ t ∈ Tstar,
      ((Subgroup.center ↥SH).map SH.subtype).map (MulAut.conj t).toMonoidHom =
      (Subgroup.center ↥SH).map SH.subtype := by
    intro t ht
    have h := map_center_conj_eq (A := SH) t
    rw [hSH_normal t ht] at h
    exact h.symm
  have hW3inv : ∀ t ∈ Tstar, W3.map t.toMonoidHom = W3 := by
    intro t ht
    calc W3.map t.toMonoidHom = (CFSG.Quasithin.fixV
        ((Subgroup.center ↥SH).map SH.subtype)).map t.toMonoidHom := by rw [hW3eq]
      _ = CFSG.Quasithin.fixV
          (((Subgroup.center ↥SH).map SH.subtype).map
            (MulAut.conj t).toMonoidHom) := (fixV_map_conj _ t).symm
      _ = CFSG.Quasithin.fixV ((Subgroup.center ↥SH).map SH.subtype) := by
        rw [hcenterSH_normal t ht]
      _ = W3 := hW3eq.symm
  have hQ23h_stab : (StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom =
      MulAction.stabilizer ↥H (W2 : Set V) ⊓ MulAction.stabilizer ↥H (W3 : Set V) := by
    have hq1 : (StdQ4 K 1).map (MulAut.conj h).toMonoidHom =
        MulAction.stabilizer ↥H (W2 : Set V) := by
      have hQ : StdQ4 K 1 = MulAction.stabilizer ↥H (stdFlagSub4 K 2 : Set V) := by
        change StdQ4 K 1 = MulAction.stabilizer
          ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) (stdFlagSub4 K 2 : Set V)
        exact (StdQ4_eq_stabilizer_stdFlagSub4 (K := K) 1).symm
      rw [hQ]
      exact (stabilizer_map_conj_subgroup H h (stdFlagSub4 K 2)).symm
    have hq2 : (StdQ4 K 2).map (MulAut.conj h).toMonoidHom =
        MulAction.stabilizer ↥H (W3 : Set V) := by
      have hQ : StdQ4 K 2 = MulAction.stabilizer ↥H (stdFlagSub4 K 3 : Set V) := by
        change StdQ4 K 2 = MulAction.stabilizer
          ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 4 K)) (stdFlagSub4 K 3 : Set V)
        exact (StdQ4_eq_stabilizer_stdFlagSub4 (K := K) 2).symm
      rw [hQ]
      exact (stabilizer_map_conj_subgroup H h (stdFlagSub4 K 3)).symm
    rw [Subgroup.map_inf _ _ _ (MulAut.conj h).injective, hq1, hq2]
  have hQ23h_inv : ∀ t ∈ Tstar,
      (((StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom).map H.subtype).map
        (MulAut.conj t).toMonoidHom =
      ((StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom).map H.subtype := by
    intro t ht
    have hmap : ((StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom).map H.subtype =
        (MulAction.stabilizer ↥H (W2 : Set V)).map H.subtype ⊓
        (MulAction.stabilizer ↥H (W3 : Set V)).map H.subtype := by
      rw [hQ23h_stab, Subgroup.map_inf _ _ _ H.subtype_injective]
    rw [hmap]
    have h2 := map_subtype_stabilizer_conj_normalizer t (hTnorm ht) W2
    have h3 := map_subtype_stabilizer_conj_normalizer t (hTnorm ht) W3
    rw [hW2inv t ht] at h2
    rw [hW3inv t ht] at h3
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective]
    erw [h2, h3]
    rfl
  have hQ23good : Good ((StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨S, ?_⟩
      rw [hB, StdQ4_inf_eq_map_Q23]
      exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
        (Subgroup.map_mono (f := (eSL4 K).toMonoidHom) (upperTriangular_le_Q23 K))
    · rw [hconj, StdQ4_inf_eq_map_Q23]
      exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
        (Subgroup.map_mono (f := (eSL4 K).toMonoidHom) (unitriangular_le_Q23 K))
    · exact hQ23h_inv
    · intro hle
      have h1 : (StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom ≤
          (StdQ4 K 0).map (MulAut.conj h).toMonoidHom := by
        rwa [hPℓ] at hle
      have hle' := (Subgroup.map_le_map_iff_of_injective
        (MulAut.conj h).injective).mp h1
      have hQ : Q23 K ≤ Q4 K 0 := by
        have h := hle'
        rw [StdQ4, StdQ4, ← Subgroup.map_inf _ _ _ (eSL4 K).injective, StdQ4] at h
        have h' := (Subgroup.map_le_map_iff_of_injective (eSL4 K).injective).mp h
        have h'' : Q4 K 1 ⊓ Q4 K 2 = Q23 K := by
          rw [Q23_eq_flagStabilizer, flagStabilizer_pair]
          rfl
        rwa [h''] at h'
      rw [Q23_eq_flagStabilizer] at hQ
      rw [show Q4 K 0 = flagStabilizer 4 K {1} from rfl] at hQ
      have h11 : 1 ≤ (1 : ℕ) := le_rfl
      have h14 : (1 : ℕ) < 4 := by norm_num
      have hr : LinearFlag.reflection 4 K 1 h11 h14 ∈ flagStabilizer 4 K {2, 3} := by
        rw [(subflag_stabilizer_generation (K := K) (n := 4) {2, 3}).2.2 1 h11 h14]
        norm_num
      have hr' := hQ hr
      rw [(subflag_stabilizer_generation (K := K) (n := 4) {1}).2.2 1 h11 h14] at hr'
      exact hr' rfl
  have hQ23le : (StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom ≤ Pstar := by
    rw [hPst, StdQ4_inf_eq_map_Q23]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (Subgroup.map_mono (f := (eSL4 K).toMonoidHom) hQ4le)
  have hPst_eq : Pstar = (StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom :=
    le_antisymm (hmin.2 hQ23good hQ23le) hQ23le
  refine ⟨?_, ?_⟩
  · intro htop
    rw [hPst_eq] at htop
    have htop' : StdQ4 K 1 ⊓ StdQ4 K 2 = ⊤ := by
      have htop' := congrArg (fun X : Subgroup ↥H => X.map (MulAut.conj h⁻¹).toMonoidHom) htop
      change ((StdQ4 K 1 ⊓ StdQ4 K 2).map (MulAut.conj h).toMonoidHom).map
        (MulAut.conj h⁻¹).toMonoidHom =
        (⊤ : Subgroup ↥H).map (MulAut.conj h⁻¹).toMonoidHom at htop'
      rw [Subgroup.map_map] at htop'
      have hcomp5 : ((MulAut.conj h⁻¹).toMonoidHom).comp ((MulAut.conj h).toMonoidHom) =
          MonoidHom.id _ := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp5, Subgroup.map_id, Subgroup.map_top_of_surjective _
        (MulAut.conj h⁻¹).surjective] at htop'
      exact htop'
    exact StdQ4_ne_top K 1 (le_antisymm le_top (by rw [← htop']; exact inf_le_left))
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · right
      have hn1' : n = 1 := by omega
      refine ⟨hn1', ?_⟩
      subst hn1'
      have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
      have hstd : Hinf (Q23 K) = ⊥ := by
        rw [Hinf_eq_perfectCore]
        exact perfectCore_Q23_eq_bot_of_card_two K hK2
      have h1 : Hinf ((Q23 K).map (eSL4 K).toMonoidHom) = ⊥ :=
        Hinf_map_eq_bot (eSL4 K) (Q23 K) hstd
      have h2 : Hinf (((Q23 K).map (eSL4 K).toMonoidHom).map
          (MulAut.conj h).toMonoidHom) = ⊥ :=
        Hinf_map_eq_bot (MulAut.conj h) ((Q23 K).map (eSL4 K).toMonoidHom) h1
      rw [hPst_eq, StdQ4_inf_eq_map_Q23, h2]
    · left
      have hn2 : 2 ≤ n := hn
      have hstd : IsL2 (Bar2 (Hinf (Q23 K))) n := by
        rw [Hinf_eq_perfectCore]
        exact isL2_bar2_perfectCore_Q23 K hK hn2
      have h1 : IsL2 (Bar2 (Hinf ((Q23 K).map (eSL4 K).toMonoidHom))) n :=
        isL2_bar2_hinf_map_equiv (eSL4 K) (Q23 K) hstd
      have h2 : IsL2 (Bar2 (Hinf (((Q23 K).map (eSL4 K).toMonoidHom).map
          (MulAut.conj h).toMonoidHom))) n :=
        isL2_bar2_hinf_map_equiv (MulAut.conj h) ((Q23 K).map (eSL4 K).toMonoidHom) h1
      rw [hPst_eq, StdQ4_inf_eq_map_Q23]
      exact h2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
