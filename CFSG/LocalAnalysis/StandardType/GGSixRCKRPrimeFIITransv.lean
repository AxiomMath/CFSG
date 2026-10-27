module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSLRoot
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckFIIb_rootGroup_conj {m : ℕ} {F : Type} [Field F]
    {β β₀ : Fin (SpecialLinear.rootDatum m F).rank → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum m F).roots)
    (hβ₀ : β₀ ∈ (SpecialLinear.rootDatum m F).roots) :
    ∃ g : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      ((SpecialLinear.rootDatum m F).rootGroup β₀).map (MulAut.conj g).toMonoidHom =
        (SpecialLinear.rootDatum m F).rootGroup β := by
  obtain ⟨w, hw⟩ := CFSG.StandardType.exists_weylAction_eq_of_simpleConj
    (D := SpecialLinear.rootDatum m F) rfl
    (fun i j => CFSG.StandardType.GGRootSL.ggSimpleConj (m := m) (F := F) i j) hβ hβ₀
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_map_conj_rootGroup
    (D := SpecialLinear.rootDatum m F) (n := SpecialLinear.weylRep m F)
    (H := SpecialLinear.torus m F)
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum m F) w
  exact ⟨g, by rw [hg β₀ hβ₀, hw]⟩

private theorem rckFIIb_map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  show (MulAut.conj b) ((MulAut.conj a) x) = (MulAut.conj (b * a)) x
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

private theorem rckFIIb_map_hom_conj {G H : Type*} [Group G] [Group H] (f : G →* H)
    (A : Subgroup G) (a : G) :
    (A.map (MulAut.conj a).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  show f ((MulAut.conj a) x) = (MulAut.conj (f a)) (f x)
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem rckFII_PSL_transv
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] {m : ℕ}
    (φ : (ggU .PSL (m + 1) 1).K →* X) (hφk : φ.ker ≤ Subgroup.center (ggU .PSL (m + 1) 1).K)
    (S : Set (GL (Fin (m + 1)) (GaloisField 2 1))) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e = 1)
    {R Rm : Subgroup X} (hR : R ≤ J'.map φ) (hRm : Rm ≤ J'.map φ) (hpos : GGRootPosJ (J'.map φ) R Rm) :
    ∃ β : Fin (ggU .PSL (m + 1) 1).D.rank → ℤ, β ∈ (ggU .PSL (m + 1) 1).D.roots ∧
      GGLongRoot (ggU .PSL (m + 1) 1).D β ∧ GGRootVia (ggU .PSL (m + 1) 1) φ.range R β := by
  classical
  have hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 2 := by
    rw [hdeg]; norm_num
  obtain ⟨k, ι, β₀, v, ψv, v', ψv', _hlong₀, hιker, hιrange, hvv, hv'v', hvv', hv'v, hT, _hT',
    _hk, _hJ'eq, hβ₀root⟩ := exists_blockModel_PSL_rank m 1 S hS he hdeg2 hJe
  have hJ'q : Assembly.IsQuasisimple ↥J' := hJe.2.2
  have hm : 1 ≤ m := by
    by_contra hm0
    have hm0' : m + 1 = 1 := by omega
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) := by
      rw [hm0']
      exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
    haveI : Subsingleton ↥J' := inferInstance
    exact (not_nontrivial_iff_subsingleton (α := ↥J')).mpr inferInstance
      (CFSG.ComponentClassification.Quasisimple.nontrivial hJ'q)
  have hZSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center (GaloisField 2 1) (m + 1)
        (by omega),
      GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hιrange_q : Assembly.IsQuasisimple ↥(ι.range) := by
    rw [hιrange]; exact hJ'q
  have hSLk := isQuasisimple_specialLinear_of_quasisimple_range
    (ι := Fin (k + 1)) (Q := GaloisField 2 1) ι hιrange_q
  have hk2 : k + 1 ≠ 2 := by
    rcases hSLk.2.1 with h | h
    · simpa using h
    · exfalso
      exact h (by rw [GaloisField.card 2 1 (by norm_num)]; norm_num)
  haveI hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)) :=
    ⟨hSLk.2.2.1⟩
  have hZSLk : Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center (GaloisField 2 1) (k + 1)
        (by omega),
      GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hNorm : RCKNormalizedModel .PSL (k + 1) 1 := by
    refine ⟨Or.inl rfl, Nat.prime_two, le_refl 1, ?_, ?_, ?_⟩
    · simpa using hSLk.1
    · intro h; exact hk2 (congrArg Prod.fst h)
    · intro h; exact absurd (congrArg Prod.snd h) (by norm_num)
  have hψrange : (φ.comp ι).range = J'.map φ := by
    rw [MonoidHom.range_comp, hιrange]
  have hψker : (φ.comp ι).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)) := by
    intro x hx
    exact hιker x (hφk (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)))
  let θ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1) →* ↥(J'.map φ) :=
    (φ.comp ι).codRestrict (J'.map φ) (fun x => by
      refine ⟨ι x, ?_, rfl⟩
      rw [← hιrange]
      exact ⟨x, rfl⟩)
  have hθsurj : Function.Surjective θ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (φ.comp ι).range := by rw [hψrange]; exact hy
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, Subtype.ext hx⟩
  have hθker : θ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)) := by
    intro x hx
    refine hιker x (hφk (MonoidHom.mem_ker.mpr ?_))
    have h1 : θ x = 1 := MonoidHom.mem_ker.mp hx
    have h2 : (θ x).1 = (1 : ↥(J'.map φ)).1 := congrArg Subtype.val h1
    have h3 : (θ x).1 = (φ.comp ι) x := rfl
    rw [h3] at h2
    exact h2
  have hZJ : Subgroup.center ↥(J'.map φ) = ⊥ := by
    have hc := CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (G := Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)) θ hθsurj hθker
    rw [hZSLk, Subgroup.map_bot] at hc
    exact hc.symm
  have hOddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))) := by
    rw [hZJ, Subgroup.card_bot]
    exact odd_one
  have hker_ne : (φ.comp J'.subtype).ker ≠ ⊤ := by
    intro htop
    have hJ'le : J' ≤ φ.ker := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥J') ∈ (φ.comp J'.subtype).ker := by
        rw [htop]; exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hmem)
    have hJ'bot : J' = ⊥ :=
      le_bot_iff.mp (hJ'le.trans (hφk.trans (le_of_eq hZSL)))
    exact (Subgroup.nontrivial_iff_ne_bot J').mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hJ'q) hJ'bot
  have hJqs : Assembly.IsQuasisimple ↥(J'.map φ) := by
    have hθq := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top
      (G := ↥J') (H := X) hJ'q (φ.comp J'.subtype) hker_ne
    have hrange : (φ.comp J'.subtype).range = J'.map φ := by
      ext x; constructor
      · rintro ⟨y, rfl⟩; exact ⟨y.1, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
    rw [hrange] at hθq
    exact hθq
  obtain ⟨β', u', hβ'root, _hlong', hR', _hRm'⟩ :=
    (hIRG X (J'.map φ) R Rm hJqs hOddJ hpos).1 .PSL (k + 1) 1 (φ.comp ι) hNorm hψrange hψker
  have hβ₀root' : β₀ ∈ (SpecialLinear.rootDatum k (GaloisField 2 1)).roots := hβ₀root
  have hβ'root' : β' ∈ (SpecialLinear.rootDatum k (GaloisField 2 1)).roots := hβ'root
  obtain ⟨g, hg⟩ := rckFIIb_rootGroup_conj (m := k) (F := GaloisField 2 1) hβ'root' hβ₀root'
  have hg' : ((ggU .PSL (k + 1) 1).D.rootGroup β₀).map (MulAut.conj g).toMonoidHom =
      (ggU .PSL (k + 1) 1).D.rootGroup β' := hg
  let gU : (ggU .PSL (k + 1) 1).K := g
  obtain ⟨β_K, hβKroot, hβKlong, u_K, hXu, _hXu'⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSL m (GaloisField 2 1) hm v ψv v' ψv'
      hvv hv'v' hvv' hv'v
  have hXu_g : (((ggU .PSL (m + 1) 1).D.rootGroup β_K).map
      (MulAut.conj u_K).toMonoidHom).map Matrix.SpecialLinearGroup.toGL = matTransvGroup v ψv :=
    hXu
  let uKU : (ggU .PSL (m + 1) 1).K := u_K
  have hH0 : ((ggU .PSL (k + 1) 1).D.rootGroup β₀).map ι =
      ((ggU .PSL (m + 1) 1).D.rootGroup β_K).map (MulAut.conj u_K).toMonoidHom :=
    Subgroup.map_injective Matrix.SpecialLinearGroup.toGL_injective (by rw [hT, hXu_g])
  have hR1 : R = ((((ggU .PSL (k + 1) 1).D.rootGroup β₀).map ι).map
      (MulAut.conj (ι (u' * gU))).toMonoidHom).map φ := by
    rw [hR']
    unfold ggRootSub
    rw [← hg']
    have hstep : (((ggU .PSL (k + 1) 1).D.rootGroup β₀).map
        (MulAut.conj g).toMonoidHom).map (MulAut.conj u').toMonoidHom =
        ((ggU .PSL (k + 1) 1).D.rootGroup β₀).map
          (MulAut.conj (u' * gU)).toMonoidHom :=
      rckFIIb_map_conj_mul ((ggU .PSL (k + 1) 1).D.rootGroup β₀) g u'
    rw [hstep]
    rw [← Subgroup.map_map]
    have hstep2 : (((ggU .PSL (k + 1) 1).D.rootGroup β₀).map
          (MulAut.conj (u' * gU)).toMonoidHom).map ι =
        (((ggU .PSL (k + 1) 1).D.rootGroup β₀).map ι).map
          (MulAut.conj (ι (u' * gU))).toMonoidHom :=
      rckFIIb_map_hom_conj ι ((ggU .PSL (k + 1) 1).D.rootGroup β₀) (u' * gU)
    rw [hstep2]
  have hR2 : R = (((ggU .PSL (m + 1) 1).D.rootGroup β_K).map
      (MulAut.conj (ι (u' * gU) * uKU)).toMonoidHom).map φ := by
    rw [hR1, hH0]
    have hstep : (((ggU .PSL (m + 1) 1).D.rootGroup β_K).map
          (MulAut.conj u_K).toMonoidHom).map (MulAut.conj (ι (u' * gU))).toMonoidHom =
        ((ggU .PSL (m + 1) 1).D.rootGroup β_K).map
          (MulAut.conj (ι (u' * gU) * uKU)).toMonoidHom :=
      rckFIIb_map_conj_mul ((ggU .PSL (m + 1) 1).D.rootGroup β_K) u_K (ι (u' * gU))
    rw [hstep]
  refine ⟨β_K, hβKroot, hβKlong, φ, rfl, hφk, ι (u' * gU) * uKU, ?_⟩
  rw [hR2]
  rfl

end CFSG.StandardType.RCKRP
