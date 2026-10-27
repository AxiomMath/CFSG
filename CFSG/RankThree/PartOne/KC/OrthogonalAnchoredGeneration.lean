module

public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredCalibration
public import CFSG.ClassicalGroups.Orthogonal.PolarPairPlane
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapGen
public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameToral

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.GroupTheory.WeirSylow

section PairSupport

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {W : Submodule K V} {m : ℕ} {U : Fin m → Submodule K V}

theorem nondegenerate_anchored_pair
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hU : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    {i j : Fin m} (hij : i ≠ j) :
    (polarBilin (Q.comp (W ⊔ U i ⊔ U j).subtype)).Nondegenerate := by
  have hWpoly : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hUpoly : ∀ i, PolarNondegOn Q (U i) := fun i => polarNondegOn_of_nondegenerate (hU i)
  have hWi : PolarNondegOn Q (W ⊔ U i) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWpoly (hUpoly i)
      (fun w hw u hu => hWU i w hw u hu)
  refine CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn ?_
  refine CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWi (hUpoly j) ?_
  intro x hx y hy
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
  rw [polar_add_left, hWU j w hw y hy, hUU i j hij u hu y hy, add_zero]

end PairSupport

section Generation

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem orthDerived_eq_iSup_anchored_supportedDerived_of_anchor
    (Q : QuadraticForm K V) (W : Submodule K V) {m : ℕ} (U : Fin m → Submodule K V)
    (hm : 2 ≤ m)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hWdim : finrank K W = 2)
    (hU : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUdim : ∀ i, finrank K (U i) = 2)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (hspan : W ⊔ ⨆ i, U i = ⊤) (o : Fin m) :
    orthDerived Q = ⨆ (j : Fin m) (_ : j ≠ o), supportedDerived Q (W ⊔ U o ⊔ U j) := by
  classical
  let S : Submodule K V := ⨆ i, U i
  have hWpoly : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hUpoly : ∀ i, PolarNondegOn Q (U i) := fun i => polarNondegOn_of_nondegenerate (hU i)
  have hWUsep : ∀ i, OrthSep Q W (U i) := fun i w hw u hu => hWU i w hw u hu
  have hWUreg : ∀ i, PolarNondegOn Q (W ⊔ U i) := fun i =>
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWpoly (hUpoly i) (hWUsep i)
  have hWUdisj : ∀ i, Disjoint W (U i) := fun i =>
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint hWpoly (hWUsep i)
  have hWUdim : ∀ i, finrank K ↥(W ⊔ U i) = 4 := by
    intro i
    rw [finrank_sup_of_disjoint (hWUdisj i), hWdim, hUdim i]
  obtain ⟨hSreg', hSdimsum⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.polarNondegOn_iSup_fin U hUpoly hUU
  have hSreg : PolarNondegOn Q S := hSreg'
  have hSdim : finrank K S = 2 * m := by
    change finrank K ↥(⨆ i, U i) = 2 * m
    rw [hSdimsum]
    have hsum : (∑ i : Fin m, finrank K (U i)) = 2 * m := by
      simp only [hUdim]
      simp [Nat.mul_comm]
    rw [hsum]
  have hWS : OrthSep Q W S := by
    intro w hw s hs
    change s ∈ ⨆ i, U i at hs
    refine Submodule.iSup_induction U (motive := fun s => polar Q w s = 0) hs ?_ ?_ ?_
    · intro i u hu
      exact hWU i w hw u hu
    · exact polar_zero_right Q w
    · intro a b ha hb
      rw [polar_add_right, ha, hb, add_zero]
  have hWdisjS : Disjoint W S :=
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint hWpoly hWS
  have hspanS : W ⊔ S = ⊤ := hspan
  have hVdim : finrank K V = 2 * (m + 1) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := K) W S
    rw [hspanS, hWdisjS.eq_bot, finrank_bot, hWdim, hSdim, finrank_top] at hdim
    omega
  have hQpoly : PolarNondegOn Q (⊤ : Submodule K V) := by
    rw [← hspanS]
    exact CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWpoly hSreg hWS
  have hQ : (polarBilin Q).Nondegenerate := by
    constructor
    · intro x hx
      exact hQpoly x (Submodule.mem_top) fun y _ => hx y
    · intro y hy
      exact hQpoly y (Submodule.mem_top) fun x _ => by rw [polar_comm]; exact hy x
  have horth : orthDerived Q = elementaryGroup Q :=
    CFSG.LocalAnalysis.GLTheoremA.T173U.orthDerived_eq_elementaryGroup_of_three_le
      (Q := Q) (m := m + 1) hQ (by omega) hVdim
  let H : Subgroup (V ≃ₗ[K] V) :=
    ⨆ (j : Fin m) (_ : j ≠ o), supportedDerived Q (W ⊔ U o ⊔ U j)
  have hHle : H ≤ orthDerived Q := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact supportedDerived_le_orthDerived_of_regular
      (nondegenerate_anchored_pair hW hU hWU hUU hj.symm)
  have hHorth : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hHle.trans (orthDerived_le_orthogonalGroup_of_commutator Q)
  let ι := {j : Fin m // j ≠ o}
  haveI : Nonempty ι := by
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j, hj⟩ := exists_ne o
    exact ⟨⟨j, hj⟩⟩
  have hP0 : OrthSep Q (W ⊔ U o) (⊥ : Submodule K V) := by
    intro x hx y hy
    rw [Submodule.mem_bot] at hy
    rw [hy, polar_zero_right]
  have hPR : ∀ i : ι, OrthSep Q (W ⊔ U o) (U i.val) := by
    intro i x hx y hy
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, hWU i.val w hw y hy,
      hUU o i.val i.property.symm u hu y hy, add_zero]
  have hspanP : (⊤ : Submodule K V) ≤
      (⊥ : Submodule K V) ⊔ (W ⊔ U o) ⊔ ⨆ i : ι, U i.val := by
    rw [← hspan, bot_sup_eq]
    refine sup_le (le_sup_of_le_left le_sup_left) ?_
    refine iSup_le fun i => ?_
    by_cases hi : i = o
    · rw [hi]
      exact le_sup_of_le_left le_sup_right
    · refine le_trans (le_iSup (fun j : ι => U j.val) ⟨i, hi⟩) ?_
      exact le_sup_right
  have hEich : ∀ i : ι, ∀ e ∈ (⊥ : Submodule K V) ⊔ (W ⊔ U o) ⊔ U i.val,
      ∀ w ∈ (⊥ : Submodule K V) ⊔ (W ⊔ U o) ⊔ U i.val, eichler Q e w ∈ H := by
    intro i e he w hw
    have hpiece : (⊥ : Submodule K V) ⊔ (W ⊔ U o) ⊔ U i.val = W ⊔ U o ⊔ U i.val := by
      rw [bot_sup_eq]
    have heS : e ∈ W ⊔ U o ⊔ U i.val := hpiece ▸ he
    have hwS : w ∈ W ⊔ U o ⊔ U i.val := hpiece ▸ hw
    by_cases h : Q e = 0 ∧ polar Q e w = 0
    · have hnd : (polarBilin (Q.comp (W ⊔ U o ⊔ U i.val).subtype)).Nondegenerate :=
        nondegenerate_anchored_pair hW hU hWU hUU i.property.symm
      have hdim : finrank K ↥(W ⊔ U o ⊔ U i.val) = 6 := by
        rw [finrank_sup_of_disjoint
          (CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint (hWUreg o) (hPR i)),
          hWUdim o, hUdim i.val]
      have hEmem : eichler (Q.comp (W ⊔ U o ⊔ U i.val).subtype)
          ⟨e, heS⟩ ⟨w, hwS⟩ ∈
          orthDerived (Q.comp (W ⊔ U o ⊔ U i.val).subtype) := by
        rw [CFSG.LocalAnalysis.GLTheoremA.T173U.orthDerived_eq_elementaryGroup_of_three_le
          (Q := Q.comp (W ⊔ U o ⊔ U i.val).subtype) hnd (m := 3) (by norm_num)
          (by rw [hdim])]
        exact eichler_mem_elementaryGroup
          (Q := Q.comp (W ⊔ U o ⊔ U i.val).subtype) ⟨e, heS⟩ ⟨w, hwS⟩
      have hmem : eichler Q e w ∈ supportedDerived Q (W ⊔ U o ⊔ U i.val) :=
        eichler_mem_supportedDerived heS hwS h.1 h.2 hEmem
      exact Subgroup.mem_iSup_of_mem i.val (Subgroup.mem_iSup_of_mem i.property hmem)
    · rw [eichler_of_not h]
      exact Subgroup.one_mem H
  have hgen : elementaryGroup Q ≤ H := by
    have h := elementaryGroup_le_of_pieces hQ hHorth
      (V₀ := (⊥ : Submodule K V)) (P := W ⊔ U o)
      (hP := hWUreg o) (h3 := by rw [hWUdim o]; norm_num)
      (R := fun i : ι => U i.val) hP0 hPR hspanP hEich
    simpa only [iSup_subtype] using h
  refine le_antisymm (horth.trans_le hgen) hHle

end Generation

section AllPairs

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem orthDerived_eq_iSup_anchored_pairs
    (Q : QuadraticForm K V) (W : Submodule K V) {m : ℕ} (U : Fin m → Submodule K V)
    (hm : 2 ≤ m)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hWdim : finrank K W = 2)
    (hU : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUdim : ∀ i, finrank K (U i) = 2)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (hspan : W ⊔ ⨆ i, U i = ⊤) :
    orthDerived Q = ⨆ (i : Fin m) (j : Fin m) (_ : i ≠ j),
      supportedDerived Q (W ⊔ U i ⊔ U j) := by
  classical
  let o : Fin m := ⟨0, by omega⟩
  have hstar := orthDerived_eq_iSup_anchored_supportedDerived_of_anchor
    Q W U hm hW hWdim hU hUdim hWU hUU hspan o
  refine le_antisymm ?_ ?_
  · rw [hstar]
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_iSup_of_le o (le_iSup_of_le j (le_iSup_of_le hj.symm le_rfl))
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    exact supportedDerived_le_orthDerived_of_regular
      (nondegenerate_anchored_pair hW hU hWU hUU hij)

end AllPairs

section SingletonTools

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : HypPair Q} {U : Submodule K V}

theorem mem_span_e_of_singular_of_polar_e_eq_zero
    (hU : ∀ u ∈ U, Q u = 0 → u = 0) (hPU : ∀ u ∈ U, polar Q P.e u = 0)
    {x : V} (hx : x ∈ Submodule.span K {P.e, P.f} ⊔ U) (hQx : Q x = 0)
    (he : polar Q P.e x = 0) : x ∈ Submodule.span K {P.e} := by
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
  have hb : b = 0 := by
    have h := he
    simp only [polar_add_right, polar_smul_right_eq, P.polar_ee, P.polar_ef, hPU u hu,
      mul_one, mul_zero, add_zero, zero_add] at h
    exact h
  subst b
  have hQu : Q u = 0 := by
    have h := hQx
    simp only [zero_smul, add_zero] at h
    simp only [QuadraticMap.map_add Q, map_smul_eq_sq, P.Q_e, mul_zero, zero_add,
      polar_smul_left_eq, hPU u hu, add_zero] at h
    exact h
  have hu0 : u = 0 := hU u hu hQu
  rw [hu0]
  simp only [zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem not_exists_totallySingular_two_of_hypPair
    (hU : ∀ u ∈ U, Q u = 0 → u = 0) (hPU : ∀ u ∈ U, polar Q P.e u = 0) :
    ¬ ∃ T : Submodule K V, T ≤ Submodule.span K {P.e, P.f} ⊔ U ∧ finrank K T = 2 ∧
      ∀ t ∈ T, Q t = 0 := by
  rintro ⟨T, hTle, hTdim, hTQ⟩
  let φ : ↥T →ₗ[K] K := (polarBilin Q P.e).comp T.subtype
  have hφ : LinearMap.ker φ ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt (V := ↥T) (V₂ := K) ?_
    rw [finrank_self]
    omega
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hφ
  have hte : polar Q P.e (t : V) = 0 := by
    have h := LinearMap.mem_ker.mp ht
    simpa [φ, polarBilin_apply_apply] using h
  have htspan : (t : V) ∈ Submodule.span K {P.e} :=
    mem_span_e_of_singular_of_polar_e_eq_zero hU hPU (hTle t.2) (hTQ t t.2) hte
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp htspan
  have hc0 : c ≠ 0 := by
    intro hc0
    apply ht0
    apply Subtype.ext
    rw [← hc, hc0, zero_smul]
    rfl
  have heT : P.e ∈ T := by
    have h1 : P.e = c⁻¹ • (t : V) := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1]
    exact T.smul_mem _ t.2
  have hB : ∀ x ∈ T, ∀ y ∈ T, polar Q x y = 0 := by
    intro x hx y hy
    have h := hTQ (x + y) (T.add_mem hx hy)
    rw [QuadraticMap.map_add Q, hTQ x hx, hTQ y hy] at h
    simpa using h
  have hTle' : T ≤ Submodule.span K {P.e} := by
    intro x hx
    exact mem_span_e_of_singular_of_polar_e_eq_zero hU hPU (hTle hx) (hTQ x hx)
      (hB P.e heT x hx)
  have hle := Submodule.finrank_mono hTle'
  rw [hTdim, finrank_span_singleton P.e_ne_zero] at hle
  omega

end SingletonTools

section RegularFour

variable {K : Type} [Field K] {X : Type} [AddCommGroup X] [Module K X]
  [FiniteDimensional K X] {R : QuadraticForm K X}

theorem eichler_mem_orthDerived_of_regular_four (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K X = 4)
    (hno : ¬ ∃ T : Submodule K X, finrank K T = 2 ∧ ∀ t ∈ T, R t = 0)
    {e w : X} (he : R e = 0) (hew : polar R e w = 0) :
    eichler R e w ∈ orthDerived R := by
  by_cases hc : ∃ c : K, c ≠ 0 ∧ c ≠ 1
  · obtain ⟨c, hc0, hc1⟩ := hc
    exact CFSG.SeitzReduction.OmegaPilot.eichler_mem_orthDerived_of_ne_zero_ne_one hR hc0 hc1 e w
  · haveI : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
      ⟨fun c => by
        by_cases h0 : c = 0
        · exact Or.inl h0
        · exact Or.inr (by
            by_contra h1
            exact hc ⟨c, h0, h1⟩)⟩
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eichler_mem_commutator hR
      (Or.inr hno) he hew

end RegularFour

section SingletonGeneration

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem orthDerived_eq_iSup_supportedDerived_of_hypPair
    (Q : QuadraticForm K V) (P : HypPair Q) (W : Submodule K V) {m : ℕ}
    (U : Fin m → Submodule K V) (hm : 2 ≤ m)
    (hWspan : W = Submodule.span K {P.e, P.f})
    (hUdim : ∀ i, finrank K (U i) = 2)
    (hUaniso : ∀ i, ∀ u ∈ U i, Q u = 0 → u = 0)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (hspan : W ⊔ ⨆ i, U i = ⊤) :
    orthDerived Q = ⨆ i, supportedDerived Q (W ⊔ U i) := by
  classical
  have heW : P.e ∈ W := by
    rw [hWspan]
    exact Submodule.subset_span (by simp)
  have hfW : P.f ∈ W := by
    rw [hWspan]
    exact Submodule.subset_span (by simp)
  have hWdim : finrank K W = 2 := by
    rw [hWspan]
    exact CFSG.ClassicalGroups.Orthogonal.finrank_span_pair_eq_two P.Q_e P.Q_f P.polar_ef
  have hWpoly : PolarNondegOn Q W := by
    rw [hWspan]
    exact polarNondegOn_span_pair_of_polar_eq_one P.polar_ef
  have hUreg : ∀ i, PolarNondegOn Q (U i) := fun i =>
    polarNondegOn_of_nondegenerate
      (CFSG.LocalAnalysis.ComponentInitial.finite_anisotropic_plane_regular
        (Q := Q.comp (U i).subtype) (by rw [hUdim i])
        (fun x hx hQx => hx (Subtype.ext (hUaniso i x x.2 hQx))))
  have hWUsep : ∀ i, OrthSep Q W (U i) := fun i w hw u hu => hWU i w hw u hu
  have hWUreg : ∀ i, PolarNondegOn Q (W ⊔ U i) := fun i =>
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWpoly (hUreg i) (hWUsep i)
  have hWUdisj : ∀ i, Disjoint W (U i) := fun i =>
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint hWpoly (hWUsep i)
  have hWUdim : ∀ i, finrank K ↥(W ⊔ U i) = 4 := by
    intro i
    rw [finrank_sup_of_disjoint (hWUdisj i), hWdim, hUdim i]
  have hWUreg' : ∀ i, (polarBilin (Q.comp (W ⊔ U i).subtype)).Nondegenerate := fun i =>
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn (hWUreg i)
  have hnoPiece : ∀ i, ¬ ∃ T : Submodule K ↥(W ⊔ U i), finrank K T = 2 ∧
      ∀ t ∈ T, (Q.comp (W ⊔ U i).subtype) t = 0 := by
    intro i
    rintro ⟨T, hTdim, hTQ⟩
    have hPUei : ∀ u ∈ U i, polar Q P.e u = 0 := fun u hu => hWU i P.e heW u hu
    have hmaple : T.map (W ⊔ U i).subtype ≤ Submodule.span K {P.e, P.f} ⊔ U i := by
      have hEq : Submodule.span K {P.e, P.f} ⊔ U i = W ⊔ U i := by rw [hWspan]
      rw [hEq]
      intro x hx
      obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx
      exact y.2
    have hmapdim : finrank K (T.map (W ⊔ U i).subtype) = 2 := by
      rw [Submodule.finrank_map_subtype_eq, hTdim]
    have hmapQ : ∀ x ∈ T.map (W ⊔ U i).subtype, Q x = 0 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hTQ y hy
    exact not_exists_totallySingular_two_of_hypPair (P := P) (U := U i) (hUaniso i) hPUei
      ⟨T.map (W ⊔ U i).subtype, hmaple, hmapdim, hmapQ⟩
  let S : Submodule K V := ⨆ i, U i
  obtain ⟨hSreg', hSdimsum⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.polarNondegOn_iSup_fin U hUreg hUU
  have hSreg : PolarNondegOn Q S := hSreg'
  have hSdim : finrank K S = 2 * m := by
    change finrank K ↥(⨆ i, U i) = 2 * m
    rw [hSdimsum]
    have hsum : (∑ i : Fin m, finrank K (U i)) = 2 * m := by
      simp only [hUdim]
      simp [Nat.mul_comm]
    rw [hsum]
  have hWS : OrthSep Q W S := by
    intro w hw s hs
    change s ∈ ⨆ i, U i at hs
    refine Submodule.iSup_induction U (motive := fun s => polar Q w s = 0) hs ?_ ?_ ?_
    · intro i u hu
      exact hWU i w hw u hu
    · exact polar_zero_right Q w
    · intro a b ha hb
      rw [polar_add_right, ha, hb, add_zero]
  have hWdisjS : Disjoint W S :=
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint hWpoly hWS
  have hspanS : W ⊔ S = ⊤ := hspan
  have hVdim : finrank K V = 2 * (m + 1) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := K) W S
    rw [hspanS, hWdisjS.eq_bot, finrank_bot, hWdim, hSdim, finrank_top] at hdim
    omega
  have hQpoly : PolarNondegOn Q (⊤ : Submodule K V) := by
    rw [← hspanS]
    exact CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWpoly hSreg hWS
  have hQ : (polarBilin Q).Nondegenerate := by
    constructor
    · intro x hx
      exact hQpoly x (Submodule.mem_top) fun y _ => hx y
    · intro y hy
      exact hQpoly y (Submodule.mem_top) fun x _ => by rw [polar_comm]; exact hy x
  have horth : orthDerived Q = elementaryGroup Q :=
    CFSG.LocalAnalysis.GLTheoremA.T173U.orthDerived_eq_elementaryGroup_of_three_le
      (Q := Q) (m := m + 1) hQ (by omega) hVdim
  let H : Subgroup (V ≃ₗ[K] V) := ⨆ i, supportedDerived Q (W ⊔ U i)
  have hHle : H ≤ orthDerived Q := by
    change (⨆ i, supportedDerived Q (W ⊔ U i)) ≤ orthDerived Q
    exact iSup_le fun i => supportedDerived_le_orthDerived_of_regular (hWUreg' i)
  have hHorth : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hHle.trans (orthDerived_le_orthogonalGroup_of_commutator Q)
  have hEich : ∀ i, ∀ e ∈ W ⊔ U i, ∀ w ∈ W ⊔ U i, eichler Q e w ∈ H := by
    intro i e he w hw
    by_cases h : Q e = 0 ∧ polar Q e w = 0
    · have hQe' : (Q.comp (W ⊔ U i).subtype) ⟨e, he⟩ = 0 := h.1
      have hB' : polar (Q.comp (W ⊔ U i).subtype) ⟨e, he⟩ ⟨w, hw⟩ = 0 :=
        (polar_comp_subtype_eq (W := W ⊔ U i) (u := ⟨e, he⟩) (w := ⟨w, hw⟩)).trans h.2
      have hloc : eichler (Q.comp (W ⊔ U i).subtype) ⟨e, he⟩ ⟨w, hw⟩ ∈
          orthDerived (Q.comp (W ⊔ U i).subtype) :=
        eichler_mem_orthDerived_of_regular_four (hWUreg' i) (hWUdim i) (hnoPiece i) hQe' hB'
      exact Subgroup.mem_iSup_of_mem i (eichler_mem_supportedDerived he hw h.1 h.2 hloc)
    · rw [eichler_of_not h]
      exact Subgroup.one_mem H
  have hP0 : OrthSep Q W (⊥ : Submodule K V) := by
    intro x hx y hy
    rw [Submodule.mem_bot] at hy
    rw [hy, polar_zero_right]
  have hPR : ∀ i, OrthSep Q W (U i) := fun i => hWUsep i
  have hspan' : (⊤ : Submodule K V) ≤ (⊥ : Submodule K V) ⊔ W ⊔ ⨆ i, U i := by
    rw [bot_sup_eq, hspan]
  have hEich' : ∀ i, ∀ e ∈ (⊥ : Submodule K V) ⊔ W ⊔ U i,
      ∀ w ∈ (⊥ : Submodule K V) ⊔ W ⊔ U i, eichler Q e w ∈ H := by
    intro i e he w hw
    rw [bot_sup_eq] at he hw
    exact hEich i e he w hw
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hrootE : IsRootCenter Q H P.e :=
    isRootCenter_of_pieces (H := H) (V₀ := ⊥) (P := W) (R := U) hP0 hPR hspan' hEich'
      heW P.e_ne_zero P.Q_e
  have hrootF : IsRootCenter Q H P.f :=
    isRootCenter_of_pieces (H := H) (V₀ := ⊥) (P := W) (R := U) hP0 hPR hspan' hEich'
      hfW P.f_ne_zero P.Q_f
  have hgen : elementaryGroup Q ≤ H := elementaryGroup_le_of_hypPair hQ hHorth P hrootE hrootF
  exact le_antisymm (horth.trans_le hgen) hHle

end SingletonGeneration

theorem exists_calibrated_prod_chart_of_marked_supports
    {F V E G : Type} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup E] [Module F E] [FiniteDimensional F E] [Group G]
    (Q : QuadraticForm F V) (W : Submodule F V) {m : ℕ}
    (U : Fin m → Submodule F V) (hm : 2 ≤ m) (hF : 2 < Nat.card F)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : Module.finrank F W = 2)
    (hU : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUdim : ∀ i, Module.finrank F (U i) = 2)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (hspan : W ⊔ ⨆ i, U i = ⊤)
    (htype : ∀ i,
      IsPlusType (Q.comp (U i).subtype) ↔ ¬ IsPlusType (Q.comp W.subtype))
    (R : QuadraticForm F E) (o : Fin m)
    (j : R.IsometryEquiv (Q.comp (U o).subtype))
    (a : orthDerived Q →* G) (k : orthDerived (Q.prod R) →* G)
    (ha : Function.Injective a) (hk : Function.Injective k)
    (hmark : ∀ S : Finset (Fin m), S.Nonempty → S.card ≤ 2 →
      ((supportedDerived Q (W ⊔ S.sup U)).subgroupOf (orthDerived Q)).map a =
        ((supportedDerived Q (W ⊔ S.sup U)).subgroupOf (orthDerived Q)).map
          (k.comp (orthDerivedProdIncl (Q := Q) (R := R)))) :
    ∃ beta : MulAut (orthDerived (Q.prod R)),
      (k.comp beta.toMonoidHom).comp (orthDerivedProdIncl (Q := Q) (R := R)) = a ∧
      Function.Injective (k.comp beta.toMonoidHom) ∧
      (k.comp beta.toMonoidHom).range = k.range ∧
      (∀ S : Finset (Fin m),
        (((supportedDerived (Q.prod R) ((W ⊔ S.sup U).prod ⊥)).subgroupOf
            (orthDerived (Q.prod R))).map beta.toMonoidHom =
          (supportedDerived (Q.prod R) ((W ⊔ S.sup U).prod ⊥)).subgroupOf
            (orthDerived (Q.prod R))) ∧
        (((supportedDerived (Q.prod R)
            (((W ⊔ S.sup U).prod ⊥) ⊔
              ((⊥ : Submodule F V).prod (⊤ : Submodule F E)))).subgroupOf
            (orthDerived (Q.prod R))).map beta.toMonoidHom =
          (supportedDerived (Q.prod R)
            (((W ⊔ S.sup U).prod ⊥) ⊔
              ((⊥ : Submodule F V).prod (⊤ : Submodule F E)))).subgroupOf
            (orthDerived (Q.prod R)))) := by
  classical
  let incl : orthDerived Q →* orthDerived (Q.prod R) :=
    orthDerivedProdIncl (Q := Q) (R := R)
  let aK : orthDerived Q →* G := k.comp incl
  have hincl : Function.Injective incl := by
    intro x y hxy
    have h1 : ((x : V ≃ₗ[F] V).prodCongr (LinearEquiv.refl F E)) =
        ((y : V ≃ₗ[F] V).prodCongr (LinearEquiv.refl F E)) := by
      have h2 : ((incl x : orthDerived (Q.prod R)) : (V × E) ≃ₗ[F] (V × E)) =
          ((incl y : orthDerived (Q.prod R)) : (V × E) ≃ₗ[F] (V × E)) :=
        congrArg (fun z : orthDerived (Q.prod R) =>
          (z : (V × E) ≃ₗ[F] (V × E))) hxy
      dsimp only [incl] at h2
      simpa only [coe_orthDerivedProdIncl] using h2
    apply Subtype.ext
    ext v
    have h3 := congrArg (fun e : (V × E) ≃ₗ[F] (V × E) => e (v, 0)) h1
    simpa [LinearEquiv.prodCongr_apply] using congrArg Prod.fst h3
  have haK : Function.Injective aK := by
    change Function.Injective fun x => k (incl x)
    exact hk.comp hincl
  have hgen : orthDerived Q = ⨆ (i : Fin m) (j : Fin m) (_ : i ≠ j),
      supportedDerived Q (W ⊔ U i ⊔ U j) :=
    orthDerived_eq_iSup_anchored_pairs Q W U (by omega) hW hWdim hU hUdim hWU hUU hspan
  have htop : (⊤ : Subgroup (orthDerived Q)) =
      ⨆ (i : Fin m) (j : Fin m) (_ : i ≠ j),
        (supportedDerived Q (W ⊔ U i ⊔ U j)).subgroupOf (orthDerived Q) := by
    apply Subgroup.map_injective (f := (orthDerived Q).subtype) (orthDerived Q).subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    conv_lhs => rw [hgen]
    simp only [Subgroup.map_iSup]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro j
    apply iSup_congr
    intro hij
    exact (Subgroup.map_subgroupOf_eq_of_le
      (supportedDerived_le_orthDerived_of_regular
        (nondegenerate_anchored_pair hW hU hWU hUU hij))).symm
  have hmarkK : ∀ S : Finset (Fin m), S.Nonempty → S.card ≤ 2 →
      ((supportedDerived Q (W ⊔ S.sup U)).subgroupOf (orthDerived Q)).map a =
        ((supportedDerived Q (W ⊔ S.sup U)).subgroupOf (orthDerived Q)).map aK := by
    intro S hne hcard
    exact hmark S hne hcard
  have hpair : ∀ (i j : Fin m) (hij : i ≠ j),
      ((supportedDerived Q (W ⊔ U i ⊔ U j)).subgroupOf (orthDerived Q)).map a =
        ((supportedDerived Q (W ⊔ U i ⊔ U j)).subgroupOf (orthDerived Q)).map aK := by
    intro i j hij
    have hcard : ({i, j} : Finset (Fin m)).card ≤ 2 := by
      calc ({i, j} : Finset (Fin m)).card = 2 := Finset.card_pair_eq_two_iff.mpr hij
        _ ≤ 2 := le_rfl
    have h := hmarkK ({i, j} : Finset (Fin m)) (by simp) hcard
    simpa only [Finset.sup_insert, Finset.sup_singleton, sup_assoc] using h
  have hsing : ∀ i : Fin m,
      ((supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q)).map a =
        ((supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q)).map aK := by
    intro i
    have h := hmarkK ({i} : Finset (Fin m)) (by simp) (by simp)
    simpa only [Finset.sup_singleton] using h
  have hrange : a.range = aK.range := by
    calc
      a.range = (⊤ : Subgroup (orthDerived Q)).map a := (Subgroup.map_top a).symm
      _ = (⨆ (i : Fin m) (j : Fin m) (_ : i ≠ j),
          (supportedDerived Q (W ⊔ U i ⊔ U j)).subgroupOf (orthDerived Q)).map a := by
        rw [htop]
      _ = ⨆ (i : Fin m) (j : Fin m) (_ : i ≠ j),
          ((supportedDerived Q (W ⊔ U i ⊔ U j)).subgroupOf (orthDerived Q)).map a := by
        simp only [Subgroup.map_iSup]
      _ = ⨆ (i : Fin m) (j : Fin m) (_ : i ≠ j),
          ((supportedDerived Q (W ⊔ U i ⊔ U j)).subgroupOf (orthDerived Q)).map aK := by
        exact iSup_congr fun i => iSup_congr fun j => iSup_congr fun hij => hpair i j hij
      _ = (⨆ (i : Fin m) (j : Fin m) (_ : i ≠ j),
          (supportedDerived Q (W ⊔ U i ⊔ U j)).subgroupOf (orthDerived Q)).map aK := by
        simp only [Subgroup.map_iSup]
      _ = (⊤ : Subgroup (orthDerived Q)).map aK := by rw [htop]
      _ = aK.range := Subgroup.map_top aK
  let alpha : MulAut (orthDerived Q) :=
    (MonoidHom.ofInjective ha).trans
      ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective haK).symm)
  have halpha : aK.comp alpha.toMonoidHom = a := by
    ext x
    change aK (alpha x) = a x
    rw [show alpha x = (MonoidHom.ofInjective haK).symm
        (MulEquiv.subgroupCongr hrange ((MonoidHom.ofInjective ha) x)) from rfl]
    rw [MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
  have hHi : ∀ i,
      ((supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q)).map alpha.toMonoidHom =
        (supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q) := by
    intro i
    apply Subgroup.map_injective (f := aK) haK
    rw [Subgroup.map_map ((supportedDerived Q (W ⊔ U i)).subgroupOf (orthDerived Q))
      aK alpha.toMonoidHom, halpha, hsing i]
  obtain ⟨S0, T0, beta, _hα, hS0W, hS0U, _hTσ, _hTμ, _hbeta_apply, hbeta_incl,
    _hprodW, _hprodUi, _hprodTop, hprodBot, hprodSupTop, hnormalizes⟩ :=
    exists_anchored_calibration_prod_extension Q W U hm hF hW hWdim hU hUdim hWU hUU hspan
      htype alpha hHi R o j
  have hbeta_incl' : ∀ g : orthDerived Q, beta (incl g) = incl (alpha g) := by
    intro g
    exact hbeta_incl g
  have hmapSup : ∀ S : Finset (Fin m), S0.mapSub (W ⊔ S.sup U) = W ⊔ S.sup U := by
    intro S
    induction S using Finset.induction with
    | empty => simpa only [Finset.sup_empty, sup_bot_eq] using hS0W
    | insert i s hi ih =>
        have hstep : W ⊔ (insert i s).sup U = (W ⊔ s.sup U) ⊔ U i := by
          rw [Finset.sup_insert, sup_comm (U i) (s.sup U), ← sup_assoc]
        rw [hstep, CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.SemiSim.mapSub_sup,
          ih, hS0U i]
  refine ⟨beta, ?_, ?_, ?_, ?_⟩
  · ext x
    change k (beta (incl x)) = a x
    rw [hbeta_incl' x]
    exact DFunLike.congr_fun halpha x
  · change Function.Injective fun z => k (beta z)
    exact hk.comp beta.injective
  · apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact ⟨beta z, rfl⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨beta.symm y, by simp⟩
  · intro S
    have hP : T0.mapSub ((W ⊔ S.sup U).prod ⊥) = (W ⊔ S.sup U).prod ⊥ :=
      hprodBot (W ⊔ S.sup U) (hmapSup S)
    have hP2 : T0.mapSub (((W ⊔ S.sup U).prod ⊥) ⊔
        ((⊥ : Submodule F V).prod (⊤ : Submodule F E))) =
        ((W ⊔ S.sup U).prod ⊥) ⊔ ((⊥ : Submodule F V).prod (⊤ : Submodule F E)) :=
      hprodSupTop (W ⊔ S.sup U) (hmapSup S)
    exact ⟨hnormalizes _ hP, hnormalizes _ hP2⟩

end CFSG.RankThree.PartOne.KCOrthogonal
