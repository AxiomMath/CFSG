module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthFixed
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockG
public import CFSG.LocalAnalysis.StandardType.GGTBJOmCore
public import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut
public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthU42
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
public import CFSG.GroupTheory.InvolutionPair
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public noncomputable section

namespace CFSG.StandardType

open Module Multiplicative Polynomial SpCoord
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal

theorem ggTBJSpC_reflAut_comm_of_disjoint {p r : ℕ} {α : Type*} {t : Fin r → α}
    {a b c d : Fin r} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ggTBJSpC_reflAut p r t a b * ggTBJSpC_reflAut p r t c d =
      ggTBJSpC_reflAut p r t c d * ggTBJSpC_reflAut p r t a b := by
  classical
  ext f j
  simp only [MulAut.mul_apply]
  by_cases hja : j = a
  · subst j
    rw [ggTBJSpC_reflAut_apply_of_ne hcd hac had]
    by_cases h : t a = t b
    · rw [ggTBJSpC_reflAut_apply_left_same hab h,
        ggTBJSpC_reflAut_apply_left_same hab h,
        ggTBJSpC_reflAut_apply_of_ne hcd hbc hbd]
    · rw [ggTBJSpC_reflAut_apply_left_mixed hab h,
        ggTBJSpC_reflAut_apply_left_mixed hab h,
        ggTBJSpC_reflAut_apply_of_ne hcd hbc hbd]
  by_cases hjb : j = b
  · subst j
    rw [ggTBJSpC_reflAut_apply_of_ne hcd hbc hbd]
    by_cases h : t a = t b
    · rw [ggTBJSpC_reflAut_apply_right_same hab h,
        ggTBJSpC_reflAut_apply_right_same hab h,
        ggTBJSpC_reflAut_apply_of_ne hcd hac had]
    · rw [ggTBJSpC_reflAut_apply_right_mixed hab h,
        ggTBJSpC_reflAut_apply_right_mixed hab h,
        ggTBJSpC_reflAut_apply_of_ne hcd hac had]
  by_cases hjc : j = c
  · subst j
    rw [ggTBJSpC_reflAut_apply_of_ne hab hac.symm hbc.symm]
    by_cases h : t c = t d
    · rw [ggTBJSpC_reflAut_apply_left_same hcd h,
        ggTBJSpC_reflAut_apply_left_same hcd h,
        ggTBJSpC_reflAut_apply_of_ne hab had.symm hbd.symm]
    · rw [ggTBJSpC_reflAut_apply_left_mixed hcd h,
        ggTBJSpC_reflAut_apply_left_mixed hcd h,
        ggTBJSpC_reflAut_apply_of_ne hab had.symm hbd.symm]
  by_cases hjd : j = d
  · subst j
    rw [ggTBJSpC_reflAut_apply_of_ne hab had.symm hbd.symm]
    by_cases h : t c = t d
    · rw [ggTBJSpC_reflAut_apply_right_same hcd h,
        ggTBJSpC_reflAut_apply_right_same hcd h,
        ggTBJSpC_reflAut_apply_of_ne hab hac.symm hbc.symm]
    · rw [ggTBJSpC_reflAut_apply_right_mixed hcd h,
        ggTBJSpC_reflAut_apply_right_mixed hcd h,
        ggTBJSpC_reflAut_apply_of_ne hab hac.symm hbc.symm]
  rw [ggTBJSpC_reflAut_apply_of_ne hab hja hjb,
    ggTBJSpC_reflAut_apply_of_ne hcd hjc hjd,
    ggTBJSpC_reflAut_apply_of_ne hcd hjc hjd,
    ggTBJSpC_reflAut_apply_of_ne hab hja hjb]

namespace QTwoOrthogonalCav

theorem exists_four_moving_pieces
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} {E : Subgroup (V ≃ₗ[K] V)} (hEΩ : E ≤ orthDerived Q)
    (Δ : OrthTorus.TBJOmData Q 3 E n) (f₀ : Fin n → Multiplicative (ZMod 3))
    (hh : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (Δ.τ f₀).toLinearMap)
    (hns : ¬ Group.IsSolvable
      ↥((specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))) :
    ∃ i : Fin 4 → Fin n, Function.Injective i ∧
      ∀ j, Δ.F.U (i j) ≤ orbitSpace (Δ.τ f₀).toLinearMap (X ^ 2 + X + 1) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx := Δ.oddOrderIsometry (by decide) hQ hEΩ f₀
  have hX : (X ^ 2 + X + 1 : K[X]) ≠ X - 1 :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_ne
  have hm := ggResX2_four_le_primaryMultiplicity hK hx hh hX hns
  let P : Fin n → Prop :=
    fun j => Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap (X ^ 2 + X + 1)
  have horb : orbitSpace (Δ.τ f₀).toLinearMap (X ^ 2 + X + 1) ≤
      ⨆ j : {j : Fin n // P j}, Δ.F.U j := by
    rw [Δ.orbitSpace_eq (by decide) hQ hEΩ f₀ hh hX]
    exact iSup₂_le fun j hj => le_iSup_of_le ⟨j, hj⟩ le_rfl
  have hpc : primaryComponent (Δ.τ f₀).toLinearMap (X ^ 2 + X + 1) ≤
      orbitSpace (Δ.τ f₀).toLinearMap (X ^ 2 + X + 1) := le_sup_left
  have hdim := Submodule.finrank_mono (hpc.trans horb)
  rw [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.finrank_phi hh,
    OrthTorusGen.finrank_iSup_frame_pieces Δ.F Δ.finrank_piece P] at hdim
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card {j : Fin n // P j} := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨i⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun j => (i j).1, ?_, fun j => (i j).2⟩
  intro j k h
  exact i.injective (Subtype.ext h)

theorem four_dvd_moving_of_data
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} {E : Subgroup (V ≃ₗ[K] V)} (hEΩ : E ≤ orthDerived Q)
    (Δ : OrthTorus.TBJOmData Q 3 E n) (f₀ : Fin n → Multiplicative (ZMod 3))
    (hh : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (Δ.τ f₀).toLinearMap)
    (hns : ¬ Group.IsSolvable
      ↥((specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))) :
    4 ∣ Nat.card (ggAutomizer
      (specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1) ⊓ orthDerived Q) E) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  have hX : (X ^ 2 + X + 1 : K[X]) ≠ X - 1 :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_ne
  let P : Fin n → Prop :=
    fun j => Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap (X ^ 2 + X + 1)
  let S := specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1) ⊓ orthDerived Q
  obtain ⟨a, ha, _, hval, hswap, hneg, _⟩ :=
    Δ.blockG_pieces (by decide) hQ hEΩ f₀ hh hX
  have hactive : ∀ j, P j → toAdd (f₀ j) ≠ 0 :=
    fun j hj => Δ.active_of_le_orbitSpace (by decide) hQ hEΩ f₀ hh hX j hj
  have hclass : ∀ j, P j → toAdd (f₀ j) = a ∨ toAdd (f₀ j) = -a :=
    fun j hj => hval j (hactive j hj) hj
  have hswapP : ∀ j k : Fin n, j ≠ k → P j → P k → toAdd (f₀ j) = toAdd (f₀ k) →
      ∃ g ∈ S, ∀ f, g * Δ.τ f * g⁻¹ = Δ.τ (permAut (Equiv.swap j k) f) :=
    fun j k hjk hj hk heq => hswap j k hjk (hactive j hj) hj (hactive k hk) hk heq
  have hnegP : ∀ j k : Fin n, P j → P k → toAdd (f₀ j) = a → toAdd (f₀ k) = -a →
      ∃ g ∈ S, ∀ f, g * Δ.τ f * g⁻¹ = Δ.τ (permAut (Equiv.swap j k) (NbrOrth.dinv j k f)) :=
    fun j k hj hk hja hka => hneg j k (hactive j hj) hj (hactive k hk) hk hja hka
  let C := Fin n → Multiplicative (ZMod 3)
  let κ : C ≃* E := (MonoidHom.ofInjective Δ.τ_inj).trans
    (MulEquiv.subgroupCongr Δ.τ_range)
  let H : Subgroup (MulAut C) := (ggAutomizer S E).map (MulAut.congr κ.symm).toMonoidHom
  let t : Fin n → ZMod 3 := fun j => toAdd (f₀ j)
  have hmem : ∀ j k : Fin n, P j → P k → j ≠ k → ggTBJSpC_reflAut 3 n t j k ∈ H := by
    intro j k hj hk hjk
    obtain ⟨g, hg, hact⟩ := exists_conj_reflAut Δ.τ f₀ S a P hclass hswapP hnegP hj hk hjk
    apply (mem_map_congr_ggAutomizer_iff E S κ _).mpr
    refine ⟨g, hg, fun f => ?_⟩
    change g * Δ.τ f * g⁻¹ = Δ.τ (ggTBJSpC_reflAut 3 n t j k f)
    exact hact f
  obtain ⟨i, hinj, hi⟩ := exists_four_moving_pieces hK hQ hEΩ Δ f₀ hh hns
  have hdistinct : ∀ j k : Fin 4, j ≠ k → i j ≠ i k :=
    fun _ _ hjk h => hjk (hinj h)
  have hab : i 0 ≠ i 1 := hdistinct 0 1 (by decide)
  have hcd : i 2 ≠ i 3 := hdistinct 2 3 (by decide)
  have hac : i 0 ≠ i 2 := hdistinct 0 2 (by decide)
  have had : i 0 ≠ i 3 := hdistinct 0 3 (by decide)
  have hbc : i 1 ≠ i 2 := hdistinct 1 2 (by decide)
  have hbd : i 1 ≠ i 3 := hdistinct 1 3 (by decide)
  let u : H := ⟨ggTBJSpC_reflAut 3 n t (i 0) (i 1), hmem _ _ (hi 0) (hi 1) hab⟩
  let v : H := ⟨ggTBJSpC_reflAut 3 n t (i 2) (i 3), hmem _ _ (hi 2) (hi 3) hcd⟩
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    change ggTBJSpC_reflAut 3 n t (i 0) (i 1) * ggTBJSpC_reflAut 3 n t (i 0) (i 1) = 1
    simpa only [pow_two] using (ggTBJSpC_reflAut_sq (p := 3) (t := t) hab)
  have hv2 : v * v = 1 := by
    apply Subtype.ext
    change ggTBJSpC_reflAut 3 n t (i 2) (i 3) * ggTBJSpC_reflAut 3 n t (i 2) (i 3) = 1
    simpa only [pow_two] using (ggTBJSpC_reflAut_sq (p := 3) (t := t) hcd)
  have huv : u * v = v * u := by
    apply Subtype.ext
    exact ggTBJSpC_reflAut_comm_of_disjoint hab hcd hac had hbc hbd
  have hmove : ∀ {a b : Fin n}, a ≠ b →
      ggTBJSpC_reflAut 3 n t a b (Pi.mulSingle a (ofAdd (1 : ZMod 3))) b ≠ 1 := by
    intro a b hab
    by_cases h : t a = t b
    · rw [ggTBJSpC_reflAut_apply_right_same hab h, Pi.mulSingle_eq_same]
      decide
    · rw [ggTBJSpC_reflAut_apply_right_mixed hab h, Pi.mulSingle_eq_same]
      decide
  let f : C := Pi.mulSingle (i 0) (ofAdd (1 : ZMod 3))
  let f' : C := Pi.mulSingle (i 2) (ofAdd (1 : ZMod 3))
  have hf : f (i 1) = 1 := by simp [f, hab.symm]
  have hf' : f' (i 3) = 1 := by simp [f', hcd.symm]
  have hu1 : u ≠ 1 := by
    intro h
    have he := congrArg (fun w : H => w.val f (i 1)) h
    change ggTBJSpC_reflAut 3 n t (i 0) (i 1) f (i 1) = f (i 1) at he
    rw [hf] at he
    exact hmove hab he
  have hv1 : v ≠ 1 := by
    intro h
    have he := congrArg (fun w : H => w.val f' (i 3)) h
    change ggTBJSpC_reflAut 3 n t (i 2) (i 3) f' (i 3) = f' (i 3) at he
    rw [hf'] at he
    exact hmove hcd he
  have hne : u ≠ v := by
    intro h
    have he := congrArg (fun w : H => w.val f (i 1)) h
    change ggTBJSpC_reflAut 3 n t (i 0) (i 1) f (i 1) =
      ggTBJSpC_reflAut 3 n t (i 2) (i 3) f (i 1) at he
    rw [ggTBJSpC_reflAut_apply_of_ne hcd hbc hbd, hf] at he
    exact hmove hab he
  have hfour : 4 ∣ Nat.card H := by
    have hcard := CFSG.GroupTheory.card_closure_pair_eq_four hu2 hv2 huv hu1 hv1 hne
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  change 4 ∣ Nat.card ((ggAutomizer S E).map (MulAut.congr κ.symm).toMonoidHom) at hfour
  rwa [Subgroup.card_map_of_injective (MulAut.congr κ.symm).injective] at hfour

end QTwoOrthogonalCav

end CFSG.StandardType

end
