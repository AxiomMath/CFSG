module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement Matrix

@[expose] def SL3Line (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
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

@[expose] def SL3NaturalLine : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 2 ^ n →
    SL3Line (CFSG.Quasithin.H.StdMod (Fin 3) K)
      (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)) n

theorem nonempty_bar2_mulEquiv_of_equiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') :
    Nonempty (X ⧸ CFSG.pCore 2 X ≃* X' ⧸ CFSG.pCore 2 X') :=
  ⟨QuotientGroup.congr (CFSG.pCore 2 X) (CFSG.pCore 2 X') e (CFSG.pCore_map_iso 2 e)⟩

theorem nonempty_bar2_mulEquiv_map {G G' : Type} [Group G] [Group G'] (A : Subgroup G)
    (e : G ≃* G') : Nonempty (Bar2 A ≃* Bar2 (A.map e.toMonoidHom)) := by
  refine ⟨?_⟩
  let eA : ↥A ≃* ↥(A.map e.toMonoidHom) := A.equivMapOfInjective e.toMonoidHom e.injective
  exact QuotientGroup.congr (CFSG.pCore 2 ↥A) (CFSG.pCore 2 ↥(A.map e.toMonoidHom)) eA
    (CFSG.pCore_map_iso 2 eA)

section Transport

variable {W V : Type} [CommGroup W] [CommGroup V] [Finite W] [Finite V]

theorem sl3Line_of_map_congr (H : Subgroup (MulAut W)) (H' : Subgroup (MulAut V)) (n : ℕ)
    (e : W ≃* V) (hH' : H' = H.map (CFSG.Quasithin.H.congrHom e))
    (h : SL3Line V H' n) : SL3Line W H n := by
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

theorem kTab23b_SL3_line_uncond (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsSLn ↥H 3 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n)
    (hSL3 : SL3NaturalLine) :
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
      (ι := Fin 3) (Γ := CFSG.Open.StatedSL 3 K) (H := H) hReal
  have he' : ∀ (γ : ↥(CFSG.Open.StatedSL 3 K)) (w : W),
      e (((π γ : ↥H) : MulAut W) w) =
        CFSG.Quasithin.natAct (CFSG.Open.StatedSL 3 K) γ (e w) := by
    intro γ w
    have h1 := he γ w
    change e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        Multiplicative.toAdd (e w))
    rw [← h1, ofAdd_toAdd]
  have hmodel :
      CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K) =
        H.map (CFSG.Quasithin.H.congrHom e) :=
    (CFSG.Quasithin.H.map_congrHom_eq_natImage (Γ := CFSG.Open.StatedSL 3 K)
      (H := H) (π := π) π.surjective e he').symm
  exact sl3Line_of_map_congr H _ n e hmodel (hSL3 K n hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
