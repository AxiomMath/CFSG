module

public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

theorem sp_specialBlock_center_pow {p : ℕ} {x : StatedSp r K} (hp : p.Prime)
    (H : AltPrimaryData (spForm r K) (spLin r K x)) (a : primaryFactors (spEnd x))
    (hpm : ¬ p ∣ primaryMultiplicity (spEnd x) (a : K[X]))
    (facts : SpBlockFacts (spForm r K) (spLin r K x) a)
    {u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)}
    (hu : u ∈ specialBlock (spForm r K) (spLin r K x) (a : K[X]))
    (hcomm : ∀ g ∈ specialBlock (spForm r K) (spLin r K x) (a : K[X]), Commute u g)
    (hup : u ^ p = 1) : u = 1 := by
  have hY : u ∈ gl_centralizer (spLin r K x) :=
    orbitFactor_le_gl_centralizer (specialBlock_le_orbitFactor hu)
  obtain ⟨c, hc⟩ := facts.scalar u hY (fun _ g hg => hcomm g hg)
  obtain ⟨hmemO, hg, hdet⟩ := mem_specialBlock.1 hu
  have hsq := H.squarefree
  set γ := blockRestrict (spLin r K x) (a : K[X]) ⟨u, hg⟩ with hγdef
  have hγ : ((γ : blockGL (spEnd x) (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent (spEnd x) (a : K[X]))) =
        c • LinearMap.id := LinearMap.ext fun w => Subtype.ext (hc w)
  have hcm : c ^ primaryMultiplicity (spEnd x) (a : K[X]) = 1 := by
    have h1 := congrArg Units.val hdet
    have h2 : LinearMap.det ((γ : blockGL (spEnd x) (a : K[X])) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (spEnd x) (a : K[X]))) = 1 := by
      simpa [blockDetHom, blockGLDet, hγdef] using h1
    rw [hγ, LinearMap.det_smul, LinearMap.det_id, mul_one] at h2
    exact h2
  have hγp : γ ^ p = 1 := by
    have : (⟨u, hg⟩ : gl_centralizer (spLin r K x)) ^ p = 1 := Subtype.ext (by simpa using hup)
    rw [hγdef, ← map_pow, this, map_one]
  have hpowc : ∀ n : ℕ, ∀ w : primaryComponent (spEnd x) (a : K[X]),
      ((c • (LinearMap.id : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (spEnd x) (a : K[X])))) ^ n) w = (c ^ n) • w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, ih,
        pow_succ, mul_smul]
      exact smul_comm c (c ^ n) w
  have hcp : c ^ p = 1 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hsq a.2)
    have h1 : (((γ ^ p : blockGL (spEnd x) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (spEnd x) (a : K[X])))) = LinearMap.id := by
      rw [hγp]
      rfl
    rw [Units.val_pow_eq_pow_val, hγ] at h1
    have h2 := congrArg (fun T => T ⟨v, hv⟩) h1
    simp only [hpowc, LinearMap.id_apply] at h2
    have h3 : (c ^ p - 1) • (⟨v, hv⟩ : primaryComponent (spEnd x) (a : K[X])) = 0 := by
      rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd (congrArg Subtype.val h4) hv0
  have hc1 : c = 1 := by
    have hcop : Nat.Coprime (primaryMultiplicity (spEnd x) (a : K[X])) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
    have := pow_gcd_eq_one.2 ⟨hcm, hcp⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hua : ∀ v ∈ primaryComponent (spEnd x) (a : K[X]), ((u : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v = v := fun v hv => by
    have := hc ⟨v, hv⟩
    rw [hc1, one_smul] at this
    exact this
  have hcent : u ∈ unitaryCentralizer (spForm r K) (spLin r K x) :=
    orbitFactor_le_unitaryCentralizer hmemO
  have hblocks := H.mem_unitaryCentralizer_iff_blocks.1 hcent
  have hua' : ∀ w ∈ primaryComponent (spEnd x) (reciprocalPolynomial (a : K[X])),
      ((u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w = w := by
    intro w hw
    have hmem : ((u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w - w ∈
        primaryComponent (spEnd x) (reciprocalPolynomial (a : K[X])) :=
      sub_mem (apply_mem_primaryComponent hblocks.1 hw) hw
    have hz := H.eq_zero_of_perfect_right a.2 hmem (fun v hv => by
      rw [map_sub, sub_eq_zero]
      have := hblocks.2 a a.2 v hv w hw
      rwa [hua v hv] at this)
    exact sub_eq_zero.1 hz
  have hall : ∀ v : Fin r ⊕ Fin r → K, ((u : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v = v := by
    intro v
    calc ((u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
          Module.End K (Fin r ⊕ Fin r → K)) v
        = ((u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
          Module.End K (Fin r ⊕ Fin r → K))
            (∑ b ∈ primaryFactors (spEnd x), primaryProjection (spEnd x) b v) := by
          rw [← eq_sum_primaryProjection hsq v]
      _ = ∑ b ∈ primaryFactors (spEnd x), ((u : LinearMap.GeneralLinearGroup K
          (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K))
            (primaryProjection (spEnd x) b v) := map_sum _ _ _
      _ = ∑ b ∈ primaryFactors (spEnd x), primaryProjection (spEnd x) b v := by
          refine Finset.sum_congr rfl fun b hb => ?_
          have hbV : primaryProjection (spEnd x) b v ∈ primaryComponent (spEnd x) b :=
            primaryProjection_mem hsq hb v
          by_cases hba : b = (a : K[X])
          · subst hba
            exact hua _ hbV
          by_cases hbr : b = reciprocalPolynomial (a : K[X])
          · subst hbr
            exact hua' _ hbV
          · refine hmemO.2 b hb ?_ _ hbV
            rw [dualPoly_id]
            intro hbs
            rcases hbs with h | h
            · exact hba h
            · exact hbr (by simpa using h)
      _ = v := (eq_sum_primaryProjection hsq v).symm
  exact Units.ext (LinearMap.ext hall)

end CFSG.RankThree.PartOne.S15K
