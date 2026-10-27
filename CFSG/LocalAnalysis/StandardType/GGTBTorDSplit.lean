module

public import CFSG.LocalAnalysis.StandardType.GGTorusDSplitWitness
public import CFSG.LocalAnalysis.StandardType.GGTBTorInnModel
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest

@[expose] public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.SeitzReduction
open CFSG.LieType.Universal.Spin

theorem ggTorusTorW_D_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {f N p : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hN : 4 ≤ N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) :
    GGTorusTorW p N (Nat.card K - 1) N (CartanMatrix.D N) (ggCoxeterMatrixD N)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K N))) (LargeEvenInnSet _) := by
  classical
  intro L _ _ ψ A hTB
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero N := ⟨by omega⟩
  have hψ : Function.Surjective ψ := hTB.1
  have hker : ψ.ker ≤ Subgroup.center L := hTB.2.1
  have hperf : commutator L = ⊤ := hTB.2.2.1
  have hψinj := rPlus_injective_of_cover hK hf (by omega : 3 ≤ N) L ψ hψ hker hperf
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K N))) = ⊥ :=
    TableBOrth.center_omegaPlus_eq_bot hp hp2 hpK (by omega)
  obtain ⟨e₀, he₀, E₀, hE₀, hcard, -, hA₀⟩ := exists_innModel_of_tbGroup
    (I := LargeEvenInnSet _) (p := p) (r := N)
    (fun φ hφ => by obtain ⟨x, rfl⟩ := hφ; exact ⟨x, rfl⟩) hZR ψ hψinj A hTB
  let θ := rPlusEquivStatedOmega K N
  let E := E₀.map θ.toMonoidHom
  have hE : IsElemAbelian p E := TableB.isElemAbelian_map hE₀ θ.toMonoidHom
  have hErank : p ^ N ≤ Nat.card E := by
    rw [Subgroup.card_map_of_injective θ.injective, hcard]
    exact hTB.2.2.2.2.2.1
  obtain ⟨ζ, hζo, hζ, -, -⟩ := TableBOrth.exists_zeta hp hp2 hpK
  obtain ⟨α, hα⟩ := exists_mulEquiv_eq_map_omPlusTorus hp2 hζ hζo hE hErank
  have hEα : E.map α.symm.toMonoidHom = (omPlusTorus (m := N) hζ).range := by
    rw [hα, Subgroup.map_map]
    convert Subgroup.map_id (omPlusTorus (m := N) hζ).range using 2
    exact MonoidHom.ext fun x => α.symm_apply_apply x
  obtain ⟨w, hw⟩ := DSplitTorus.exists_ggTorusTorWit_split hp hp2 hN hζ hζo
  have hmodel : GGTorusTorData (Nat.card K - 1) N (CartanMatrix.D N) (ggCoxeterMatrixD N)
      (StatedOmega (StatedQuadPlus N K)) (scalarA E) :=
    torData_of_conj_eq α.symm hEα ⟨w, hw⟩
  have hA : A.map (MulAut.congr (e₀.trans θ)).toMonoidHom = scalarA E := by
    have hcongr : (MulAut.congr (e₀.trans θ)).toMonoidHom =
        (MulAut.congr θ).toMonoidHom.comp (MulAut.congr e₀).toMonoidHom := by
      ext a x
      rfl
    rw [hcongr, ← Subgroup.map_map, hA₀, scalarA]
    dsimp only [E]
    rw [Subgroup.map_map, Subgroup.map_map]
    have hj : (MulAut.congr θ).toMonoidHom.comp
        (MulAut.conj : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K N)) →* _) =
        (MulAut.conj : StatedOmega (StatedQuadPlus N K) →* _).comp θ.toMonoidHom :=
      MonoidHom.ext fun x => congr_conj θ x
    rw [hj]
  exact torData_of_innModel (e₀.trans θ) hA hmodel

theorem ggTBTorDHigh_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hN : 4 ≤ lab.rank)
    (htag : lab.tag = .D) (hminus : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
        (CartanMatrix.D lab.rank) (ggCoxeterMatrixD lab.rank) R I := by
  have hf : 2 ≤ lab.n := by
    have hn := hlab.1
    by_contra h
    have h1 : lab.n = 1 := by omega
    rw [h1] at hminus
    norm_num at hminus
    exact hp.ne_one hminus
  have hplus : ¬ p ∣ 2 ^ lab.n + 1 := by
    intro hplus
    have h := Nat.dvd_sub hplus hminus
    have hq : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    have heq : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
    rw [heq] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hM : ggTorMpm p lab = 2 ^ lab.n - 1 := by simp [ggTorMpm, hminus]
  have hr : lab.rank - ggTorEnn p lab = lab.rank := by simp [ggTorEnn, hplus]
  rw [hM, hr]
  refine largeEvenLabelAll_omegaPlus htag hN fun K _ _ _ hK => ?_
  simpa only [hK] using ggTorusTorW_D_split hK hf hN hp hp2 (hK ▸ hminus)

end CFSG.StandardType
