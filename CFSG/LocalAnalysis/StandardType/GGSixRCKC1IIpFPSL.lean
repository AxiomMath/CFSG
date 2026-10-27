module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSL
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3PSL
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLOrder
import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Spin
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpBlockFixed

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKRP CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rck_blockOn_glBlockCentralizer {m : ℕ} {s : GL (Fin (m + 1)) (GaloisField 2 1)}
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' {s})) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' {s})) e = 1) :
    BlockOn (fun (u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) v =>
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 1)).mulVec v)
      (LinearMap.range (Matrix.toLin' e)) (LinearMap.ker (Matrix.toLin' e))
      (glBlockCentralizer Matrix.SpecialLinearGroup.toGL {s} e) := by
  have hse : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 1)) * e = e :=
    mul_eq_self_of_blockDegree_lt_two_gf2 he (by omega)
  exact blockOn_glBlockCentralizer_of_mul_eq_self Matrix.SpecialLinearGroup.toGL he hse

theorem rckIIp_PSL_of_classicalModelID
    (X : Type) [Group X] [Finite X] (p : ℕ) (K J B : Subgroup X) (d : X)
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hmodel : RCKClassicalModelIDAt .PSL K B)
    (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hoddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hrow : GGSixRCKJRow .IIp J) :
    K = J ∨ SLFourEmbed K J ∨ OmegaSixEmbed K J := by
  rcases hmodel with ⟨m, g, φ, hg, hφr, hφk, hdiag⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hsubK : Subsingleton (ggU .PSL 0 g).K := by
      show Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
      infer_instance
    have hsubRange : Subsingleton ↥(φ.range) :=
      @Function.Surjective.subsingleton (ggU .PSL 0 g).K ↥(φ.range)
        (MonoidHom.rangeRestrict φ) hsubK (MonoidHom.rangeRestrict_surjective φ)
    have hrange_bot : φ.range = ⊥ :=
      @Subgroup.eq_bot_of_subsingleton X _ (φ.range) hsubRange
    have hKbot : K = ⊥ := by rw [← hφr, hrange_bot]
    have hle : J ≤ (⊥ : Subgroup X) := by
      calc J ≤ K ⊓ Subgroup.centralizer ({d} : Set X) := hcomp.1
        _ = ⊥ := by rw [hKbot, bot_inf_eq]
    exact (Subgroup.nontrivial_iff_ne_bot J).mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hcomp.2.2) (le_bot_iff.mp hle)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
  obtain ⟨s, _hs, hsodd, e, he, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSL (m := m') (g := g) hp hp2 (hBab.2 d hdB) hg φ hφr hφk (hBK hdB)
      (hdiag d hdB) hcomp
  have hS : ∀ a ∈ ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))),
      ∀ b ∈ ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl s
  have hoddS : ∀ a ∈ ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  let a : ℕ := blockDegree (Algebra.adjoin (GaloisField 2 g)
    (Units.val '' ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))))) e
  obtain ⟨k, ι, hιcenter, hιrange, _hιflag⟩ :=
    rckM3_PSL m' g hg {s} hS hoddS he hJ'comp
  have ha1 : 1 ≤ a := by
    let A : Subalgebra (GaloisField 2 g)
        (Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 g)) :=
      Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))))
    let M : Submodule (GaloisField 2 g)
        (Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 g)) :=
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight (GaloisField 2 g) e)
    have heM : e ∈ M :=
      ⟨1, by simp, by rw [LinearMap.mulRight_apply, one_mul]⟩
    have hne : (⟨e, heM⟩ : M) ≠ 0 := by
      intro h
      exact he.2.2.1 (by simpa using congrArg Subtype.val h)
    have hnt : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
    have hpos : 0 < Module.finrank (GaloisField 2 g) M :=
      Module.finrank_pos_iff.mpr hnt
    have hpos' : 0 < a := hpos
    omega
  let ιm : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (g * a)) →*
      (ggU .PSL (m' + 1) g).K := ι
  have hιmrange : ιm.range = J' := hιrange
  let π : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (g * a)) →* X :=
    φ.comp ιm
  have hπr : π.range = J := by
    dsimp only [π]
    rw [MonoidHom.range_comp, hιmrange]
    exact hJ'map
  have hπk : π.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (g * a))) := by
    intro y hy
    exact hιcenter y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃*
      alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  obtain ⟨hk3, hga⟩ :=
    rckIIp_eq_three_one_of_alt_eight (h := g * a) (by simpa using Nat.mul_le_mul hg ha1)
      π hπk hoddπ hA8
  have hg1 : g = 1 := Nat.dvd_one.mp ⟨a, hga.symm⟩
  subst g
  have hdeg1 : blockDegree (Algebra.adjoin (GaloisField 2 1)
      (Units.val '' ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 1))))) e = 1 := by
    simpa [a] using hga
  obtain ⟨k', ι', _β₀, _v, _φv, _v', _φv', _hlong, hι'center, hι'range,
    _h4, _h5, _h6, _h7, _h8, _h9, hk'rank, hJ'eq, _hβ⟩ :=
    exists_blockModel_PSL_rank m' 1
      ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 1))) hS he
      (by rw [hdeg1]; norm_num) hJ'comp
  let ι'' : Matrix.SpecialLinearGroup (Fin (k' + 1)) (GaloisField 2 1) →*
      (ggU .PSL (m' + 1) 1).K := ι'
  let π' : Matrix.SpecialLinearGroup (Fin (k' + 1)) (GaloisField 2 1) →* X :=
    φ.comp ι''
  have hι''range : ι''.range = J' := hι'range
  have hπ'r : π'.range = J := by
    dsimp only [π']
    rw [MonoidHom.range_comp, hι''range]
    exact hJ'map
  have hπ'k : π'.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (k' + 1)) (GaloisField 2 1)) := by
    intro y hy
    exact hι'center y (hφk hy)
  have hoddπ' : Odd (Nat.card (Subgroup.center ↥π'.range)) := by
    rw [hπ'r]
    exact hoddJ
  have hA8' : Nonempty ((↥π'.range ⧸ Subgroup.center ↥π'.range) ≃*
      alternatingGroup (Fin 8)) := by
    rw [hπ'r]
    exact CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  obtain ⟨hk'3, -⟩ :=
    rckIIp_eq_three_one_of_alt_eight (h := 1) le_rfl π' hπ'k hoddπ' hA8'
  have hrank : Module.finrank (GaloisField 2 1)
      (LinearMap.range (Matrix.toLin' e)) = 4 := by
    rw [← hk'rank, hk'3]
  have hblock := rck_blockOn_glBlockCentralizer (m := m') (s := s) (e := e) he hdeg1
  rw [← hJ'eq] at hblock
  exact Or.inr (Or.inl ⟨m', φ, LinearMap.range (Matrix.toLin' e),
    LinearMap.ker (Matrix.toLin' e), J', hφr, hφk, hblock, hJ'map, hrank⟩)


theorem rckLemmaFIIpAt_PSL :
    RCKLemmaFIIpAt .PSL := by
  intro X _ _ p K J B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel hodd hcomp hoddJ hrow
  exact rckIIp_PSL_of_classicalModelID X p K J B d hp hp2 hBab hdB hBK hmodel hodd hcomp hoddJ
    hrow


end CFSG.StandardType.RCKC1
