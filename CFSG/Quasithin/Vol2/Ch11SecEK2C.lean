module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts3
public import CFSG.Quasithin.Vol2.Ch11SecEK1E
public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8

namespace EK2

variable {F : Type*} [Field F] [CharP F 2]

theorem isSimpleGroup_SL2 (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ :=
    eq_bot_iff.mpr fun A hA => Subgroup.mem_bot.mpr (SecE.EK1.eq_one_of_mem_center hA)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)).isSimpleGroup

theorem not_isSolvable_SL2 (h4 : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have := isSimpleGroup_SL2 h4
  intro hs
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  let A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let B : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
  have h := congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0)
    (hcomm A B)
  change (!![1, 1; 0, 1] * !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) 0 0 =
    (!![0, 1; 1, 0] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 at h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h

end EK2

open EK2 in
theorem factSolvPointG2_holds : FactSolvPointG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ hU₁ S hSle hSnorm hSsolv hStriv
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU := eq_U1_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU₁)
  subst hU
  have hψinj : Function.Injective (psiG hc0 hc1 π g) := psiG_injective hf hc0 hc1 g
  have hmap := map_stabQ_eq hf hc0 hc1 g (stdF K 1)
  obtain ⟨u₀, hu₀⟩ := hf.surj (g2Act g (eu 0 (1 : K)))
  have hu₀U : u₀ ∈ hf.pre (gmapG g (stdF K 1)).toAddSubgroup :=
    mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
  have hpre : ∀ s ∈ S, ∃ γ ∈ stabV0 K, psiG hc0 hc1 π g γ = s := by
    intro s hs
    have hs' := hSle hs
    rw [← hmap] at hs'
    obtain ⟨γ, -, rfl⟩ := hs'
    refine ⟨γ, ?_, rfl⟩
    have h1 := (hf.eq_iff _ _).mpr (hStriv _ hs u₀ hu₀U)
    rw [f_psiG hf, hu₀, g2Act_inv_apply] at h1
    have h2 := congrArg (g2Act g⁻¹) h1
    rwa [g2Act_inv_apply, g2Act_inv_apply] at h2
  let ψ₀ : ↥(stabV0 K) →* MulAut W := (psiG hc0 hc1 π g).comp (stabV0 K).subtype
  have hψ₀inj : Function.Injective ψ₀ := hψinj.comp Subtype.val_injective
  let S' : Subgroup ↥(stabV0 K) := S.comap ψ₀
  have hS'n : S'.Normal := by
    refine ⟨fun y hy x => ?_⟩
    have hx : ψ₀ x ∈ H ⊓ SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup) := by
      rw [← hmap]
      exact ⟨x, stabV0_le_stabQ x.2, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hSnorm hx) (ψ₀ y)).mp hy
    show ψ₀ (x * y * x⁻¹) ∈ S
    rwa [map_mul, map_mul, map_inv]
  have hS'solv : Group.IsSolvable ↥S' := by
    have := hSsolv
    refine Group.isSolvable_of_isSolvable_injective (f := ψ₀.subgroupComap S) fun a b h => ?_
    have h1 : ψ₀ a = ψ₀ b := congrArg (fun x : ↥S => (x : MulAut W)) h
    exact Subtype.ext (hψ₀inj h1)
  let N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := S'.map levi1
  have hNn : N.Normal := hS'n.map levi1 levi1_surjective
  have hNsolv : Group.IsSolvable ↥N :=
    Group.isSolvable_of_surjective (levi1.subgroupMap_surjective S')
  have := isSimpleGroup_SL2 (F := K) h4
  have hN : N = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact h
    · exfalso
      apply not_isSolvable_SL2 (F := K) h4
      rw [h] at hNsolv
      exact Group.isSolvable_of_surjective
        (f := (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).subtype)
        fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩
  intro s
  obtain ⟨γ, hγ, hγs⟩ := hpre s s.2
  have hy : (⟨γ, hγ⟩ : ↥(stabV0 K)) ∈ S' := by
    show ψ₀ ⟨γ, hγ⟩ ∈ S
    rw [show ψ₀ ⟨γ, hγ⟩ = (s : MulAut W) from hγs]
    exact s.2
  have hl : levi1 (⟨γ, hγ⟩ : ↥(stabV0 K)) = 1 := by
    have h1 : levi1 (⟨γ, hγ⟩ : ↥(stabV0 K)) ∈ N := ⟨_, hy, rfl⟩
    rw [hN] at h1
    exact h1
  obtain ⟨k, hk⟩ := isPGroup_ker_levi1 (F := K) ⟨⟨γ, hγ⟩, hl⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : γ ^ 2 ^ k = 1 := by
    have := congrArg (fun x : ↥(levi1 (F := K)).ker => ((x : ↥(stabV0 K)) : ↥(cayleyGroup K))) hk
    simpa using this
  rw [Subgroup.coe_pow, ← hγs, ← map_pow, h1, map_one, Subgroup.coe_one]

end CFSG.Quasithin.Vol2.Ch11.SecD
