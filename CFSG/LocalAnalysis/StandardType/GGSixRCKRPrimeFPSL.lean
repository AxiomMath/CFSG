module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3PSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDualPair

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckRP_rootFlags_of_forall_rootGroup
    {G : Type} [Group G] {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (j : G →* GL ι F)
    {B : Option ((ι → F) → (ι → F) → F)}
    (hiso : ∀ y : G, ∀ b ∈ B, ∀ m m' : ι → F,
      b ((j y : Matrix ι ι F).mulVec m) ((j y : Matrix ι ι F).mulVec m') = b m m')
    {t : StatedLieTag} {k g : ℕ} (κ : (ggU t k g).K →* G)
    (h : ∀ β ∈ (ggU t k g).D.roots, GLGeoFlag B ((((ggU t k g).D.rootGroup β).map κ).map j)) :
    RCKRPRootFlags j B κ := by
  intro β hβ _ u
  have hmap : (ggRootSub (ggU t k g).D κ β u).map j =
      ((((ggU t k g).D.rootGroup β).map κ).map j).map (MulAut.conj (j (κ u))).toMonoidHom := by
    simp only [ggRootSub, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simp [MulAut.conj_apply]
  rw [hmap]
  exact glGeoFlag_map_conj (h β hβ) (j (κ u)) (hiso (κ u))

theorem rckRP_flaggedModel_PSL
    (m g : ℕ) (hg : 1 ≤ g) (S : Set (GL (Fin (m + 1)) (GaloisField 2 g)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :
    RCKRPFlaggedModel Matrix.SpecialLinearGroup.toGL none J' := by
  obtain ⟨k, ι, hιc, hιr, hflag⟩ := rckM3_PSL m g hg S hS hodd he hJe
  have ha : 0 < blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e :=
    CFSG.StandardType.TableCRes.tcBlockDegree_pos he.2.2.1
  refine ⟨.PSL, k + 1, _, ι, ⟨Or.inl rfl, rckRP_admissible_PSL_of_quasisimple_range
    (Nat.mul_pos (by omega) ha) ι (by rw [hιr]; exact hJe.2.2)⟩, hιr, hιc,
    rckRP_rootFlags_of_forall_rootGroup _ (fun _ b hb => by simp at hb) ι fun β hβ => ?_⟩
  obtain ⟨W, H, hWH, hWHβ⟩ := hflag β hβ
  refine ⟨W, H, hWH, ?_, fun b hb => by simp at hb⟩
  intro y hy hy1
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
  refine hWHβ x hx fun hx1 => hy1 ?_
  subst hx1
  exact (congrArg Matrix.SpecialLinearGroup.toGL (map_one ι)).trans (map_one _)

private theorem rckRPfsl_ne_zero
    {X : Type} [Group X] {K J : Subgroup X} {d : X} {m g : ℕ}
    (φ : (ggU .PSL m g).K →* X) (hφr : φ.range = K)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) : m ≠ 0 := by
  rintro rfl
  haveI : Subsingleton (ggU .PSL 0 g).K := by
    show Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
    infer_instance
  haveI : Subsingleton ↥(φ.range) := (MonoidHom.rangeRestrict_surjective φ).subsingleton
  have hKbot : K = ⊥ := by rw [← hφr]; exact Subgroup.eq_bot_of_subsingleton _
  have hle : J ≤ (⊥ : Subgroup X) := by
    calc J ≤ K ⊓ Subgroup.centralizer ({d} : Set X) := hJ.1
      _ = ⊥ := by rw [hKbot, bot_inf_eq]
  exact (Subgroup.nontrivial_iff_ne_bot J).mp
    (CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2) (le_bot_iff.mp hle)

theorem rckLemmaFAt_PSL
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFAt .PSL := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel _hodd hcomp _hA6 _hRJ _hRmJ
    hroot
  rcases hmodel with ⟨m, g, φ, hg, hφr, hφk, hdiag⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (rckRPfsl_ne_zero φ hφr hcomp)
  obtain ⟨s, -, hsodd, e, he, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSL (m := m) (g := g) hp hp2 (hBab.2 d hdB) hg φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
  have hS : ∀ a ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g))),
      ∀ b ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl s
  have hoddS : ∀ a ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  obtain ⟨R', hR'map, hR'flag⟩ :=
    rckRP_glGeoFlag_of_flaggedModel hIRG Matrix.SpecialLinearGroup.toGL φ hφk hJ'map hcomp.2.2
      hroot (rckRP_flaggedModel_PSL m g hg {s} hS hoddS he hJ'comp)
  exact ggRootPosFlag_of_glGeoFlag_PSL (m := m) (g := g) hg φ hφr hφk hR'map hR'flag

end CFSG.StandardType.RCKRP
