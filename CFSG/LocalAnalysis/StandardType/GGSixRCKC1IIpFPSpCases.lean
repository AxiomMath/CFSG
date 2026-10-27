module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightProj
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightSp
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLOrder

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

theorem rckIIp_PSp_selfDual_one
    {X : Type} [Group X] [Finite X] {n f : ℕ} (hf : 1 ≤ f) (φ : (ggU .PSp n f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  have hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)) := by
    refine ⟨fun ξ => ?_⟩
    obtain ⟨ζ⟩ := hA8
    have h1 : Nat.card (↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) = 20160 := by
      rw [Nat.card_congr ζ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have h2 : Nat.card ↥J' = 360 := by
      rw [Nat.card_congr ξ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have h3 : Nat.card (↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≤ Nat.card ↥(J'.map φ) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h4 : Nat.card ↥(J'.map φ) ≤ Nat.card ↥J' :=
      Nat.le_of_dvd (by rw [h2]; norm_num) (Subgroup.card_map_dvd J' φ)
    omega
  obtain ⟨r, ι, -, -, -, hcent, hrange, -⟩ :=
    exists_blockModel_selfDual_PSp_explicit n f S hS he hadj hdeg hJe hA6
  let ιA : (ggU .PSp r f).K →* (ggU .PSp n f).K := ι
  let π : (ggU .PSp r f).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp, show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSp r f).K := fun y hy => hcent y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8π : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact hA8
  exact rckIIp_false_of_alt_eight_PSp hf π hπk hoddπ hA8π

theorem rckIIp_PSp_selfDual_two
    {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f) (φ : (ggU .PSp n f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨r, ι, -, -, -, hcent, hrange, -⟩ :=
    exists_blockModel_selfDualTwo_PSp_explicit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  let ιA : (ggU .PSU r (max f 1)).K →* (ggU .PSp n f).K := ι
  let π : (ggU .PSU r (max f 1)).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp, show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSU r (max f 1)).K := fun y hy => hcent y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8π : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact hA8
  exact rckIIp_false_of_alt_eight_PSU (le_trans hf (le_max_left f 1)) π hπk hoddπ hA8π

theorem rckIIp_PSp_dualPair_one
    {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .PSp n f).K →* X) (hφk : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) (hs : s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠
      e)
    (hεeq : ε = e + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) {s} ε,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) {s} ε⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  subst hεeq
  have hSU : ∀ t ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      t ∈ CFSG.Open.StatedSp n (GaloisField 2 f) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hs
  have hS : ∀ t ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ t' ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute t t' := by
    intro t ht t' ht'
    rw [Set.mem_singleton_iff] at ht ht'
    subst ht
    subst ht'
    exact Commute.refl _
  obtain ⟨k, ι, -, -, -, hcent, hrange, -⟩ :=
    exists_blockModel_dualPair_PSp_explicit n f {s} hSU hS he hpair hdeg hJe
  let ιA : (ggU .PSL (k + 1) f).K →* (ggU .PSp n f).K := ι
  let π : (ggU .PSL (k + 1) f).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp, show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSL (k + 1) f).K := fun y hy => hcent y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8π : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact hA8
  have hf1 : f = 1 := (rckIIp_eq_three_one_of_alt_eight (h := f) hf π hπk hoddπ hA8π).2
  subst hf1
  have hsG : Matrix.transpose (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) =
      Matrix.fromBlocks 0 1 (-1) 0 :=
    CFSG.Open.StatedAPI.mem_statedSp_iff.mp hs
  exact hpair (formAdj_eq_self_of_blockDegree_lt_two_gf2 fePSp_G_isUnit_det hsG he hdeg)

private lemma rckIIp_PSp_component_model_PSL_or_PSU {n f : ℕ} (hf : 1 ≤ f) {X : Type}
    [Group X] (ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε,
        glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)) :
    ∃ (t' : CFSG.Open.StatedLieTag) (m' f' : ℕ), f < f' ∧ (t' = .PSL ∨ t' = .PSU) ∧
      LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) t' m' 2 f' := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases hdeg with ⟨heq, hd⟩ | ⟨hne, hd⟩
  · have hadj : formAdj (RingHom.id (GaloisField 2 f)) (fePSp_G n (GaloisField 2 f)) e = e := by
      rw [heq]
      exact hε.2.2.2.1
    have hJε' : IsComponentOf J'
        ⁅glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S e,
          glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S e⁆ := by
      rw [heq]
      exact hJε
    obtain ⟨l, m', -, hlt, hLM⟩ :=
      fePSp_selfDual_lieModel hc ψ hd
        (fePSp_selfDual_unitaryModel hc ψ hψ hSU hS hodd he hadj hd hJε')
    rcases hLM with hPSU | hPSL
    · exact ⟨.PSU, m', l * f, hlt, Or.inr rfl, hPSU⟩
    · exact ⟨.PSL, 2, l * f, hlt, Or.inl rfl, hPSL⟩
  · obtain ⟨heq, -⟩ := fePSp_dualPair_eps_eq hSU hS hε he heε hne
    have hJε' : IsComponentOf J' ⁅fePSp_Geps S e, fePSp_Geps S e⁆ := by
      simpa [fePSp_Geps, heq] using hJε
    have hnab : ¬ IsMulCommutative ↥(fePSp_Geps S e) := by
      intro hcomm
      have hbot : ⁅fePSp_Geps S e, fePSp_Geps S e⁆ = ⊥ := by
        rw [Subgroup.commutator_self_eq_bot_iff]
        exact hcomm
      have hJbot : J' = ⊥ := le_bot_iff.mp (by rw [hbot] at hJε'; exact hJε'.1)
      have hsimple : IsSimpleGroup (J' ⧸ Subgroup.center J') := hJε'.2.2.2
      haveI : Subsingleton (J' ⧸ Subgroup.center J') := by rw [hJbot]; infer_instance
      exact (not_subsingleton_iff_nontrivial.mpr hsimple.toNontrivial) inferInstance
    have hgl := fePSp_dualPair_glModel hc hSU hS hodd hε he heε hne hnab
    have hcomm := fePSp_dualPair_commutatorModel hc hSU hS hε he heε hne hd hgl
    have hJ := fePSp_dualPair_componentModel ψ hψ hJε' hcomm
      (by simpa using Nat.mul_le_mul hd hf)
    obtain ⟨m', hlt, hLM⟩ := fePSp_dualPair_lieModelData hc ψ hd hJ
    exact ⟨.PSL, m', blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e * f, hlt,
      Or.inl rfl, hLM⟩

theorem rckIIp_PSp_fieldExt
    {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .PSp n f).K →* X) (hφk : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S ε,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨t', m', f', hlt, ht', hLM⟩ :=
    rckIIp_PSp_component_model_PSL_or_PSU hf φ hφk S hSU hS hodd hε hJe he heε hdeg
  have hmod : CFSG.Open.StatedClassicalModel
      (↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) t' m' 2 f' := by
    rcases hLM with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    all_goals rcases ht' with rfl | rfl <;> exact absurd ht (by decide)
  exact rckIIp_false_of_alt_eight_statedClassicalModel ht' (by omega) hmod hA8

end CFSG.StandardType.RCKC1
