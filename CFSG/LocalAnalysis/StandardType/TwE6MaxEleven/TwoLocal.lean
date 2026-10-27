module

public import CFSG.LieType.BorelTits.Twisted
public import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.Monster.B.E6.StdF4FiberGroups
public import CFSG.Monster.B.E6.StdF4Root
public import CFSG.Monster.B.E6.StdF4WeylPair

public section

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Classical CFSG.Monster.B.E6.StdF4
  CFSG.Monster.B.Geometry


private def parabolicFinsum : Fin 4 → ℕ := ![93555, 315, 105, 16065]

private theorem finsum_parabolic_compl (m : Fin 4) :
    ∑ᶠ w ∈ (ncs.parabolic (Set.univ \ {m}) : Set NW),
      weylWeight ncs E6Folded.letterWeight w = parabolicFinsum m := by
  have hset : (Set.univ \ {m} : Set (Fin 4)) = {i : Fin 4 | (i : ℕ) ≠ (m : ℕ)} := by
    ext i
    simp [Fin.val_inj]
  rw [hset]
  have hpanel' : ∀ (i : Fin 4) (x : stdChamber),
      (panel ncs stdDistance i x).encard = E6Folded.letterWeight i + 1 := by
    intro i x
    rw [hpanel]
  rw [← ncard_residue_eq_finsum (cs := ncs) (δ := stdDistance) hδ hpanel'
    {i : Fin 4 | (i : ℕ) ≠ (m : ℕ)} c₀]
  obtain ⟨h0, h1, h2, h3⟩ := ncard_residue_compl_stdDistance
  fin_cases m
  · simpa [parabolicFinsum] using h0 c₀
  · simpa [parabolicFinsum] using h1 c₀
  · simpa [parabolicFinsum] using h2 c₀
  · simpa [parabolicFinsum] using h3 c₀

private theorem card_nativeParabolic_compl (m : Fin 4) :
    Nat.card (nativeParabolic (Set.univ \ {m})) = 3 * 2 ^ 36 * parabolicFinsum m := by
  rw [card_nativeParabolic, finsum_parabolic_compl]

private theorem three_seven_not_dvd_nativeParabolic {I : Set (Fin 4)} (hI : I ≠ Set.univ) :
    ¬ 3 ^ 7 ∣ Nat.card (nativeParabolic I) := by
  obtain ⟨m, hm⟩ : ∃ m : Fin 4, m ∉ I := by
    by_contra h
    push Not at h
    exact hI (Set.eq_univ_iff_forall.2 h)
  have hle : nativeParabolic I ≤ nativeParabolic (Set.univ \ {m}) :=
    nativeParabolic_mono fun i hi => by
      simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_singleton_iff]
      intro h
      exact hm (h ▸ hi)
  have hdvd : Nat.card (nativeParabolic I) ∣ Nat.card (nativeParabolic (Set.univ \ {m})) :=
    Subgroup.card_dvd_of_le hle
  rw [card_nativeParabolic_compl] at hdvd
  exact fun h37 => absurd (h37.trans hdvd) (by fin_cases m <;> norm_num [parabolicFinsum])

private theorem nativeParabolic_univ : nativeParabolic (Set.univ : Set (Fin 4)) = stdGroup := by
  have himg : foldedIndex '' (Set.univ : Set (Fin 4)) = Set.univ := by
    rw [Set.image_univ, Set.range_eq_univ]
    exact foldedIndex_bijective.2
  rw [nativeParabolic_eq, himg]
  exact (fixed_standard_parabolic_cells TwistTag.E6 K barEquiv).2.2.2.2.2

private theorem three_seven_not_dvd_of_normalizer_sylow {A : Subgroup ↥stdGroup}
    (hA : A ≠ ⊤) (S : Sylow 2 ↥stdGroup)
    (hN : Subgroup.normalizer ((S : Subgroup ↥stdGroup) : Set ↥stdGroup) ≤ A) :
    ¬ 3 ^ 7 ∣ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 (stdUnipotent0.subgroupOf stdGroup) :=
    isPGroup_graphFixedPosUnipotent_subgroupOf (t := TwistTag.E6) (σ := barHom) 2
  have hUi : ¬ 2 ∣ (stdUnipotent0.subgroupOf stdGroup).index :=
    not_dvd_index_graphFixedPosUnipotent (t := TwistTag.E6) (σ := barHom) 2 barHom_surjective
  let S₀ : Sylow 2 ↥stdGroup := hUp.toSylow hUi
  have hS₀ : (S₀ : Subgroup ↥stdGroup) = stdUnipotent0.subgroupOf stdGroup :=
    IsPGroup.toSylow_coe _ _
  have hB₀ : stdBorel.subgroupOf stdGroup ≤
      Subgroup.normalizer ((S₀ : Subgroup ↥stdGroup) : Set ↥stdGroup) := by
    rw [hS₀, ← Subgroup.subgroupOf_normalizer_eq (H := stdUnipotent0) (N := stdGroup)
      (graphFixedPosUnipotent_le_graphFixedRootGroup (t := TwistTag.E6) (K := K) (σ := barHom))]
    exact Subgroup.subgroupOf_mono stdGroup
      (graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent (t := TwistTag.E6) (K := K)
        (σ := barHom))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥stdGroup S S₀
  have hSmap : (S : Subgroup ↥stdGroup) = (S₀ : Subgroup ↥stdGroup).map
      (MulAut.conj g⁻¹).toMonoidHom := by
    have h : g⁻¹ • S₀ = S := by rw [← hg, inv_smul_smul]
    conv_lhs => rw [← h]
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hNmap : (Subgroup.normalizer ((S₀ : Subgroup ↥stdGroup) : Set ↥stdGroup)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.normalizer ((S : Subgroup ↥stdGroup) : Set ↥stdGroup) := by
    rw [Subgroup.map_equiv_normalizer_eq (H := (S₀ : Subgroup ↥stdGroup))
      (f := MulAut.conj g⁻¹), hSmap]
  have hBx : (stdBorel.subgroupOf stdGroup).map (MulAut.conj g⁻¹).toMonoidHom ≤ A := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hB₀
    rw [hNmap] at h1
    exact h1.trans hN
  set C : Subgroup ↥stdGroup := A.map (MulAut.conj g).toMonoidHom with hC
  have hconj_eq (b : ↥stdGroup) : MulAut.conj g (MulAut.conj g⁻¹ b) = b := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hBC : stdBorel.subgroupOf stdGroup ≤ C := by
    intro b hb
    rw [hC]
    have hb' : MulAut.conj g⁻¹ b ∈ A :=
      hBx (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hb)
    have hmem : MulAut.conj g (MulAut.conj g⁻¹ b) ∈ A.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hb'
    rwa [hconj_eq] at hmem
  set D : Subgroup (ModGL Tag.E6 K) := C.map stdGroup.subtype with hD
  have hDle : D ≤ stdGroup := by
    rw [hD]
    exact Subgroup.map_subtype_le C
  have hBD : stdBorel ≤ D := by
    rw [hD, ← Subgroup.map_subgroupOf_eq_of_le stdBorel_le_stdGroup]
    exact Subgroup.map_mono hBC
  obtain ⟨I, hI⟩ := exists_eq_nativeParabolic hBD hDle
  have hcard : Nat.card A = Nat.card (nativeParabolic I) := by
    rw [← hI, hD, Subgroup.card_subtype, hC,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [hcard]
  refine three_seven_not_dvd_nativeParabolic (I := I) fun hIu => hA ?_
  have hCtop : C = ⊤ := by
    refine Subgroup.map_injective stdGroup.subtype_injective ?_
    rw [← hD, hI, hIu, nativeParabolic_univ, Subgroup.map_top, Subgroup.subtype_range]
  have hconj_eq' (b : ↥stdGroup) : MulAut.conj g⁻¹ (MulAut.conj g b) = b := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hAconj : A = C.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hC]
    refine le_antisymm ?_ ?_
    · intro a ha
      have hmem : MulAut.conj g⁻¹ (MulAut.conj g a) ∈
          (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ha)
      rwa [hconj_eq'] at hmem
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp hb
      change MulAut.conj g⁻¹ (MulAut.conj g a₀) ∈ A
      rwa [hconj_eq']
  rw [hAconj, hCtop, Subgroup.map_top,
    MonoidHom.range_eq_top.2 (MulAut.conj g⁻¹).surjective]

theorem twoLocal_of_model {X : Type} [Group X] [Finite X]
    (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    ∀ M : Subgroup X, IsCoatom M → ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup 2 U →
      M ≤ Subgroup.normalizer (U : Set X) → ¬ 3 ^ 7 ∣ Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro M hM U hU hUp hMN
  have hBT : Holds X 2 := holds_of_chevalleyExceptionalModel h
  obtain ⟨S, P, hP, hNP, -, -, hSP⟩ := hBT U hU hUp
  have hMP : M ≤ P := hMN.trans hNP
  have hPeq : P = M := (hM.ne_top_iff_eq hMP).mp hP
  rw [← hPeq]
  have hLie : LieModel X .twistedE6 0 2 1 :=
    Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  obtain ⟨e⟩ :=
    CFSG.LieType.Chevalley.C2E6Std.MatrixModel.nonempty_mulEquiv_stdGroup_of_lieModel hLie
  have hSP' : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P := hSP
  set A : Subgroup ↥stdGroup := P.map e.toMonoidHom with hA
  let S' : Sylow 2 ↥stdGroup := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS' : (S' : Subgroup ↥stdGroup) = (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hAne : A ≠ ⊤ := by
    intro htop
    apply hP
    have h1 : P.map e.toMonoidHom = (⊤ : Subgroup X).map e.toMonoidHom := by
      rw [← hA]
      rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]
    exact Subgroup.map_injective e.injective h1
  have hN : Subgroup.normalizer ((S' : Subgroup ↥stdGroup) : Set ↥stdGroup) ≤ A := by
    rw [hS']
    have h1 : (Subgroup.normalizer ((S : Subgroup X) : Set X)).map e.toMonoidHom ≤ A := by
      rw [hA]
      exact Subgroup.map_mono hSP'
    rwa [Subgroup.map_equiv_normalizer_eq] at h1
  have hnot := three_seven_not_dvd_of_normalizer_sylow hAne S' hN
  have hcard : Nat.card A = Nat.card P := by
    rw [hA]
    exact Subgroup.card_map_of_injective e.injective
  rw [← hcard]
  exact hnot

end CFSG.StandardType.TwE6MaxEleven

