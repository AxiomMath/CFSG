module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FU4
public import CFSG.RankThree.PartTwo.Sec8.Hering418FU4Diag
public import CFSG.RankThree.PartTwo.Sec8.Hering418FDich

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

section Bookkeeping

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem barCentralizer_eq_centralizer (c : Cfg L K a b) {w : L ⧸ aschbacherSolvableCore 3 L}
    (hβ : c.beta = MulAut.conj w) :
    Sec8.barCentralizer (Subgroup.zpowers b) L = Subgroup.centralizer {w} := by
  ext z
  rw [KFacts.mem_barCentralizer_zpowers_iff c.hbL z, Subgroup.mem_centralizer_singleton_iff]
  have h1 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, c.hbL⟩) z = c.beta z := rfl
  rw [h1, hβ, MulAut.conj_apply]
  constructor
  · intro h
    calc z * w = (w * z * w⁻¹) * w := by rw [h]
      _ = w * z := by group
  · intro h
    rw [← h]
    group

theorem Cfg.false_of_blockData (c : Cfg L K a b)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    {y₀ w : L ⧸ aschbacherSolvableCore 3 L} (hα : c.alpha = MulAut.conj y₀)
    (hβ : c.beta = MulAut.conj w) (hBD : BlockData (Subgroup.centralizer {w}) y₀) : False := by
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hCb := barCentralizer_eq_centralizer c hβ
  have hYC : Sec8.imageModTheta L K ≤ Subgroup.centralizer {w} :=
    (imageModTheta_le_barCentralizer_of_le c.hbL c.hb3 c.hKL c.hKb).trans hCb.le
  have hYs : ((Sec8.imageModTheta L K).subgroupOf (Subgroup.centralizer {w})).IsSubnormal := by
    have := imageModTheta_isSubnormal_barCentralizer c.hbL c.hb3 hK
    rwa [hCb] at this
  have hYp : Group.IsPerfect ↥(Sec8.imageModTheta L K) := isPerfect_imageModTheta hK
  have hY0 : Sec8.imageModTheta L K ≠ ⊥ := imageModTheta_ne_bot c.hKL hKq
  obtain ⟨J, hJY, hJn, hJp, hJns, j₀, hj₀, z, hz, hyjz⟩ :=
    hBD.exists_le_of_perfect_subnormal hYC hYp hY0 hYs
  set f := Sec8.Item87Res2Proof.toQuot c.hKL with hf
  have hrange : f.range = Sec8.imageModTheta L K := Sec8.Item87Res2Proof.range_toQuot c.hKL
  have hJf : ∀ j ∈ J, ∃ k : K, f k = j := fun j hj => by
    have : j ∈ f.range := hrange ▸ hJY hj
    exact this
  have hfC : ∀ k : K, f k ∈ Subgroup.centralizer ({w} : Set (L ⧸ aschbacherSolvableCore 3 L)) :=
    fun k => hYC (hrange ▸ ⟨k, rfl⟩)
  set Jh : Subgroup K := J.comap f with hJh
  have hJhn : Jh.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hJh, Subgroup.mem_comap] at hn ⊢
    have hnJ : (⟨f n, hfC n⟩ : Subgroup.centralizer ({w} : Set (L ⧸ aschbacherSolvableCore 3 L))) ∈
        J.subgroupOf (Subgroup.centralizer {w}) := Subgroup.mem_subgroupOf.mpr hn
    have h1 := Subgroup.mem_subgroupOf.mp (hJn.conj_mem _ hnJ ⟨f g, hfC g⟩)
    simpa [map_mul, map_inv] using h1
  set π : K →* K ⧸ aschbacherSolvableCore 3 K := QuotientGroup.mk' (aschbacherSolvableCore 3 K)
    with hπ
  have hπJ : (Jh.map π).Normal := hJhn.map π (QuotientGroup.mk'_surjective _)
  rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hKq
    (Subgroup.Normal.isSubnormal hπJ) with hcen | htop
  ·
    exfalso
    obtain ⟨hθs, -, hθ3, -, -⟩ :=
      solvable_prime_complement_core_characterization (H := K) Nat.prime_three
    set T : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (aschbacherSolvableCore 3 K).map f
      with hT
    haveI hTs : Group.IsSolvable T := Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
    have hcomm : ⁅J, J⁆ ≤ T := by
      rw [Subgroup.commutator_le]
      intro j₁ hj₁ j₂ hj₂
      obtain ⟨k₁, rfl⟩ := hJf j₁ hj₁
      obtain ⟨k₂, rfl⟩ := hJf j₂ hj₂
      refine ⟨⁅k₁, k₂⁆, ?_, by simp [commutatorElement_def]⟩
      have h1 : π k₁ ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) :=
        hcen (Subgroup.mem_map_of_mem π (show k₁ ∈ Jh from hj₁))
      have h2 := Subgroup.mem_center_iff.mp h1 (π k₂)
      show ⁅k₁, k₂⁆ ∈ aschbacherSolvableCore 3 K
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change π ⁅k₁, k₂⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h2.symm
    have hJT : J ≤ T := by
      have := Subgroup.isPerfect_iff.mp hJp
      rw [this] at hcomm
      exact hcomm
    exact hJns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJT)
      (Subgroup.inclusion_injective hJT))
  ·
    obtain ⟨k₀, hk₀⟩ := hJf j₀ hj₀
    apply c.hout
    refine ⟨((⟨k₀, k₀.2⟩ : K) : K ⧸ aschbacherSolvableCore 3 K), ?_⟩
    rw [← thetaQuot_eq_conj K k₀.2]
    ext q
    obtain ⟨ĵ, hĵ, rfl⟩ := Subgroup.mem_map.mp (htop ▸ Subgroup.mem_top q)
    have hĵJ : f ĵ ∈ J := hĵ
    have hxz : f ĵ * z = z * f ĵ := Subgroup.mem_centralizer_iff.mp hz _ hĵJ
    have hact : f (Sec4.compAction K ⟨a, c.haK⟩ ĵ) = c.alpha (f ĵ) := rfl
    have key : f (Sec4.compAction K ⟨a, c.haK⟩ ĵ) = j₀ * f ĵ * j₀⁻¹ := by
      rw [hact, hα, MulAut.conj_apply, hyjz]
      calc j₀ * z * f ĵ * (j₀ * z)⁻¹ = j₀ * (z * f ĵ) * z⁻¹ * j₀⁻¹ := by group
        _ = j₀ * (f ĵ * z) * z⁻¹ * j₀⁻¹ := by rw [hxz]
        _ = j₀ * f ĵ * j₀⁻¹ := by group
    change Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨k₀, K.le_normalizer k₀.2⟩) (π ĵ) =
      Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) (π ĵ)
    rw [hπ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk, Sec4.thetaQuotMulAut_mk,
      QuotientGroup.eq]
    refine Sec8.Item87Res2Proof.ker_toQuot_le c.hKL ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, key]
    have h3 : f (Sec4.compAction K ⟨k₀, K.le_normalizer k₀.2⟩ ĵ) = j₀ * f ĵ * j₀⁻¹ := by
      change f (k₀ * ĵ * k₀⁻¹) = _
      rw [map_mul, map_mul, map_inv, hk₀]
    rw [h3, inv_mul_cancel]

end Bookkeeping

section Assembly


theorem u4OddInner : U4OddInner := by
  intro G _ _ L K a b c hK k hko h3k e hαI hβI
  obtain ⟨y₀, hy₀⟩ := hαI
  obtain ⟨w, hw⟩ := hβI
  have hk1 : 1 ≤ k := hko.pos
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd e.symm (center_projSU_four hk1)
  have hinj := conj_injective_of_center_eq_bot hZ
  have hw3 : w ^ 3 = 1 := hinj (by rw [map_pow, hw, map_one]; exact c.beta_pow_three)
  have hy3 : y₀ ^ 3 = 1 := hinj (by rw [map_pow, hy₀, map_one]; exact c.alpha_pow_three)
  have hwy : w * y₀ = y₀ * w :=
    hinj (by rw [map_mul, map_mul, hw, hy₀]; exact c.alpha_mul_beta.symm)
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact c.hβ1 (hw.symm.trans (map_one _))
  exact c.false_of_blockData hK hy₀.symm hw.symm (blockData_of_equiv hko h3k e hw3 hw1 hy3 hwy)

theorem kF418ModelOn47_uFourSix : KF418ModelOn47 (fun X _ => IsUFourSix X) :=
  kF418ModelOn47_uFourSix_of_odd u4OddInner

end Assembly

end CFSG.RankThree.PartTwo.Sec8.Hering418
