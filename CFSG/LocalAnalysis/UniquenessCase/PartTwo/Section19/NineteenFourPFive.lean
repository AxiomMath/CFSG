module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3XbarS
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846Ker
public import CFSG.Quasithin.EmptyFaithful.S152He9W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eq_of_normal_map_eq_top_19 {J A : Subgroup G} (hAJ : A ≤ J)
    (hAn : (A.subgroupOf J).Normal) (hJperf : ⁅J, J⁆ = J)
    (hAtop : (A.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) = ⊤) : A = J := by
  classical
  let π : ↥J →* Bar2 J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = (pCoreOf 2 J).subgroupOf J := by
    rw [show π.ker = CFSG.pCore 2 ↥J from QuotientGroup.ker_mk' _,
      CFSG.openPCoreOf_subgroupOf]
  have hJsup : J ≤ A ⊔ pCoreOf 2 J := by
    intro j hj
    have hjtop : π ⟨j, hj⟩ ∈ (A.subgroupOf J).map π := by
      rw [show (A.subgroupOf J).map π = ⊤ from hAtop]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, haj⟩ := Subgroup.mem_map.mp hjtop
    have hmem : (⟨j, hj⟩ : ↥J) * a⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, haj, mul_inv_cancel]
    rw [hker] at hmem
    have hmemG : j * (a : G)⁻¹ ∈ pCoreOf 2 J := Subgroup.mem_subgroupOf.mp hmem
    have heq : j = (j * (a : G)⁻¹) * (a : G) := by group
    rw [heq]
    exact (A ⊔ pCoreOf 2 J).mul_mem (Subgroup.mem_sup_right hmemG)
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
  have hP : IsPGroup 2 (↥J ⧸ (A.subgroupOf J)) := by
    have hpc : IsPGroup 2 ↥(CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    let ρ : ↥(CFSG.pCore 2 ↥J) →* (↥J ⧸ (A.subgroupOf J)) :=
      { toFun := fun q => QuotientGroup.mk (q : ↥J)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hJsup' : A.subgroupOf J ⊔ (pCoreOf 2 J).subgroupOf J = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hAJ (CFSG.openPCoreOf_le 2 J)]
      exact Subgroup.subgroupOf_eq_top.mpr hJsup
    have hρ : Function.Surjective ρ := by
      intro x
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
      have hj : j ∈ A.subgroupOf J ⊔ (pCoreOf 2 J).subgroupOf J := by
        rw [hJsup']
        exact Subgroup.mem_top j
      obtain ⟨a, ha, q, hq, haq⟩ := Subgroup.mem_sup_of_normal_left.mp hj
      let qP : ↥(CFSG.pCore 2 ↥J) :=
        ⟨q, (CFSG.mem_openPCoreOf_iff q).1 (Subgroup.mem_subgroupOf.mp hq)⟩
      refine ⟨qP, ?_⟩
      show (QuotientGroup.mk' (A.subgroupOf J)) q =
        (QuotientGroup.mk' (A.subgroupOf J)) j
      rw [← haq, map_mul]
      have haz : (QuotientGroup.mk' (A.subgroupOf J)) a = 1 :=
        (QuotientGroup.eq_one_iff (N := A.subgroupOf J) (x := a)).2 ha
      rw [haz, one_mul]
    exact IsPGroup.of_surjective hpc ρ hρ
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
  have hsub : Subsingleton (↥J ⧸ (A.subgroupOf J)) := by
    by_contra hns
    have : Nontrivial (↥J ⧸ (A.subgroupOf J)) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (↥J ⧸ (A.subgroupOf J)) hP.isNilpotent
  have htopJ : A.subgroupOf J = ⊤ := QuotientGroup.subsingleton_iff.1 hsub
  refine le_antisymm hAJ ?_
  intro j hj
  have hmem : (⟨j, hj⟩ : ↥J) ∈ A.subgroupOf J := by
    rw [htopJ]
    exact Subgroup.mem_top _
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

theorem le_of_normal_of_isSimple_19 {J S N : Subgroup G} (hJs : IsSimpleGroup (Bar2 J))
    (hJperf : ⁅J, J⁆ = J) (hS2 : IsPGroup 2 S) (hSJ : S ≤ normalizer (J : Set G))
    (hkerJ : ∀ y ∈ J, ∀ hy : y ∈ normalizer (J : Set G),
      UC6S846.rhoL J ⟨y, hy⟩ = 1 → y ∈ pCoreOf 2 J)
    (hNH : N ≤ J ⊔ S) (hHN : J ⊔ S ≤ normalizer (N : Set G))
    (hNQ : ¬ N ≤ pCoreOf 2 (J ⊔ S)) : J ≤ N := by
  classical
  have hJS : J ⊔ S ≤ normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSJ
  have hJnorm : (J.subgroupOf (J ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hJS
  have hNnorm : (N.subgroupOf (J ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  let A : Subgroup G := N ⊓ J
  have hAJ : A ≤ J := inf_le_right
  have hA_J : (A.subgroupOf J).Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hnN : (n : G) ∈ N := (Subgroup.mem_subgroupOf.mp hn).1
    have hnJ : (n : G) ∈ J := (Subgroup.mem_subgroupOf.mp hn).2
    have hgJ : (g : G) ∈ J := g.2
    have hconjN : (g : G) * (n : G) * (g : G)⁻¹ ∈ N := by
      have hmem : (⟨(n : G), hNH hnN⟩ : ↥(J ⊔ S)) ∈ N.subgroupOf (J ⊔ S) :=
        Subgroup.mem_subgroupOf.mpr hnN
      have h := Subgroup.Normal.conj_mem hNnorm ⟨(n : G), hNH hnN⟩ hmem
        ⟨(g : G), Subgroup.mem_sup_left hgJ⟩
      exact Subgroup.mem_subgroupOf.mp h
    have hconjJ : (g : G) * (n : G) * (g : G)⁻¹ ∈ J := by
      have hmem : (⟨(n : G), Subgroup.mem_sup_left hnJ⟩ : ↥(J ⊔ S)) ∈
          J.subgroupOf (J ⊔ S) :=
        Subgroup.mem_subgroupOf.mpr hnJ
      have h := Subgroup.Normal.conj_mem hJnorm ⟨(n : G), Subgroup.mem_sup_left hnJ⟩ hmem
        ⟨(g : G), Subgroup.mem_sup_left hgJ⟩
      exact Subgroup.mem_subgroupOf.mp h
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · simpa using hconjN
    · simpa using hconjJ
  let π : ↥J →* Bar2 J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = (pCoreOf 2 J).subgroupOf J := by
    rw [show π.ker = CFSG.pCore 2 ↥J from QuotientGroup.ker_mk' _,
      CFSG.openPCoreOf_subgroupOf]
  have hAn : ((A.subgroupOf J).map π).Normal := hA_J.map π hπ
  by_cases hAQ : A ≤ pCoreOf 2 J
  ·
    have hNle : N ≤ pCoreOf 2 (J ⊔ S) := by
      intro x hx
      have hxH : x ∈ J ⊔ S := hNH hx
      have hxNj : x ∈ normalizer (J : Set G) := hJS hxH
      have hρ : UC6S846.rhoL J ⟨x, hxNj⟩ = 1 := by
        apply MulEquiv.ext
        intro zbar
        obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) zbar
        rw [MulAut.one_apply]
        have hconjN : z * x * z⁻¹ ∈ N := by
          have hmem : (⟨x, hNH hx⟩ : ↥(J ⊔ S)) ∈ N.subgroupOf (J ⊔ S) :=
            Subgroup.mem_subgroupOf.mpr hx
          have h := Subgroup.Normal.conj_mem hNnorm ⟨x, hNH hx⟩ hmem
            ⟨(z : G), Subgroup.mem_sup_left z.2⟩
          exact Subgroup.mem_subgroupOf.mp h
        have hcommN : x * (z : G) * x⁻¹ * (z : G)⁻¹ ∈ N := by
          have h2 : z * x⁻¹ * z⁻¹ ∈ N := by
            have h := N.inv_mem hconjN
            simpa [mul_assoc] using h
          have h := N.mul_mem hx h2
          simpa [mul_assoc] using h
        have hcommJ : x * (z : G) * x⁻¹ * (z : G)⁻¹ ∈ J := by
          have h1 : x * (z : G) * x⁻¹ ∈ J :=
            (Subgroup.mem_normalizer_iff.mp hxNj (z : G)).mp z.2
          exact J.mul_mem h1 (J.inv_mem z.2)
        exact (UC6S846.rhoL_fix_iff J ⟨x, hxNj⟩ z).2 (hAQ ⟨hcommN, hcommJ⟩)
      exact UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one hS2 hSJ hkerJ hxH hxNj hρ
    exact (hNQ hNle).elim
  ·
    have hAne : (A.subgroupOf J).map π ≠ ⊥ := by
      intro hbot
      apply hAQ
      intro x hx
      have hxJ : x ∈ J := hx.2
      have hxmap : π (⟨x, hxJ⟩ : ↥J) ∈ (A.subgroupOf J).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
      rw [hbot] at hxmap
      have hx1 : π (⟨x, hxJ⟩ : ↥J) = 1 := by simpa using hxmap
      have hxker : (⟨x, hxJ⟩ : ↥J) ∈ π.ker := MonoidHom.mem_ker.mpr hx1
      rw [hker] at hxker
      simpa using (Subgroup.mem_subgroupOf.mp hxker)
    have hAtop : (A.subgroupOf J).map π = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A.subgroupOf J).map π)).resolve_left hAne
    have hAJ' : A = J := eq_of_normal_map_eq_top_19 hAJ hA_J hJperf hAtop
    rw [← hAJ']
    exact inf_le_left

theorem barImage_sup_eq_top_19 (L K : Subgroup G) :
    UC22.barImage (L ⊔ K) L ⊔ UC22.barImage (L ⊔ K) K = ⊤ := by
  rw [← s13_barImage_sup (M := L ⊔ K) le_sup_left le_sup_right, s13_barImage_self]

theorem isSimpleGroup_barImage_19 {M L : Subgroup G} (hL : L ∈ calC M)
    (h : IsSimpleGroup (Bar2 L)) : IsSimpleGroup ↥(UC22.barImage M L) := by
  obtain ⟨e⟩ := s13_bar_equiv hL
  exact CFSG.ABGLocalTools.isSimpleGroup_of_mulEquiv e.symm

theorem le_pCoreOf_of_inf_le_pCoreOf_19 {J T N : Subgroup G}
    (hHJ : J ⊔ T ≤ normalizer (J : Set G)) (hT2 : IsPGroup 2 T)
    (hNH : N ≤ J ⊔ T) (hNnorm : (N.subgroupOf (J ⊔ T)).Normal)
    (hNinf : N ⊓ J ≤ pCoreOf 2 (J ⊔ T)) : N ≤ pCoreOf 2 (J ⊔ T) := by
  classical
  have hJnorm : (J.subgroupOf (J ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHJ
  have hHJ2 : IsPGroup 2 (↥(J ⊔ T) ⧸ (J.subgroupOf (J ⊔ T))) := by
    let ψ : ↥T →* (↥(J ⊔ T) ⧸ (J.subgroupOf (J ⊔ T))) :=
      (QuotientGroup.mk' (J.subgroupOf (J ⊔ T))).comp (Subgroup.inclusion le_sup_right)
    have hψ : Function.Surjective ψ := by
      intro x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
      have hmem : h ∈ J.subgroupOf (J ⊔ T) ⊔ T.subgroupOf (J ⊔ T) := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top h
      obtain ⟨j, hj, t, ht, hjt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
      refine ⟨⟨(t : ↥(J ⊔ T)), Subgroup.mem_subgroupOf.mp ht⟩, ?_⟩
      show (QuotientGroup.mk' (J.subgroupOf (J ⊔ T))) (t : ↥(J ⊔ T)) =
        (QuotientGroup.mk' (J.subgroupOf (J ⊔ T))) h
      rw [← hjt, map_mul]
      have hj1 : (QuotientGroup.mk' (J.subgroupOf (J ⊔ T))) j = 1 :=
        (QuotientGroup.eq_one_iff (N := J.subgroupOf (J ⊔ T)) (x := j)).2 hj
      rw [hj1, one_mul]
    exact IsPGroup.of_surjective hT2 ψ hψ
  have hAn : ((N ⊓ J).subgroupOf N).Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hnNJ : (n : G) ∈ N ⊓ J := Subgroup.mem_subgroupOf.mp hn
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have h := Subgroup.Normal.conj_mem hNnorm ⟨(n : G), hNH hnNJ.1⟩
        (Subgroup.mem_subgroupOf.mpr hnNJ.1) ⟨(g : G), hNH g.2⟩
      exact Subgroup.mem_subgroupOf.mp h
    · have h := Subgroup.Normal.conj_mem hJnorm ⟨(n : G), Subgroup.mem_sup_left hnNJ.2⟩
        (Subgroup.mem_subgroupOf.mpr hnNJ.2) ⟨(g : G), hNH g.2⟩
      exact Subgroup.mem_subgroupOf.mp h
  have hA2 : IsPGroup 2 ↥((N ⊓ J).subgroupOf N) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (J ⊔ T)).to_le hNinf |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ J ≤ N)).symm
  have hquot2 : IsPGroup 2 (↥N ⧸ ((N ⊓ J).subgroupOf N)) := by
    let φ : ↥N →* (↥(J ⊔ T) ⧸ (J.subgroupOf (J ⊔ T))) :=
      (QuotientGroup.mk' (J.subgroupOf (J ⊔ T))).comp (Subgroup.inclusion hNH)
    have hkerφ : φ.ker = (N ⊓ J).subgroupOf N := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hx
        have hx' : (QuotientGroup.mk' (J.subgroupOf (J ⊔ T)))
            (⟨(x : G), hNH x.2⟩ : ↥(J ⊔ T)) = 1 := hx
        refine ⟨x.2, ?_⟩
        exact (QuotientGroup.eq_one_iff (N := J.subgroupOf (J ⊔ T))
          (x := ⟨(x : G), hNH x.2⟩)).1 hx'
      · rintro ⟨-, hxJ⟩
        exact (QuotientGroup.eq_one_iff (N := J.subgroupOf (J ⊔ T))
          (x := ⟨(x : G), hNH x.2⟩)).2 hxJ
    have hinj : Function.Injective (QuotientGroup.kerLift φ) := QuotientGroup.kerLift_injective φ
    have h2 : IsPGroup 2 (↥N ⧸ φ.ker) :=
      IsPGroup.of_injective hHJ2 (QuotientGroup.kerLift φ) hinj
    exact h2.of_equiv (QuotientGroup.quotientMulEquivOfEq hkerφ)
  have hN2 : IsPGroup 2 ↥N := by
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    obtain ⟨l, hl⟩ := hquot2.exists_card_eq
    refine IsPGroup.of_card (n := k + l) ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((N ⊓ J).subgroupOf N), hl, hk,
      ← pow_add, Nat.add_comm]
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hNH hNnorm hN2

omit [Finite G] in
theorem le_sup_pCoreOf_of_barImage_le_19 {J X A : Subgroup G} (hXJ : X ≤ J)
    (h : UC22.barImage J X ≤ UC22.barImage J A) : X ≤ A ⊔ pCoreOf 2 J := by
  intro x hx
  have hxbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) ⟨x, hXJ hx⟩ ∈ UC22.barImage J A :=
    h (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hxbar
  have hmem : (⟨x, hXJ hx⟩ : ↥J) * a⁻¹ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hax, mul_inv_cancel]
  rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).ker = (pCoreOf 2 J).subgroupOf J from by
    rw [QuotientGroup.ker_mk', CFSG.openPCoreOf_subgroupOf]] at hmem
  have hmemG : x * (a : G)⁻¹ ∈ pCoreOf 2 J := Subgroup.mem_subgroupOf.mp hmem
  have heq : x = (x * (a : G)⁻¹) * (a : G) := by group
  rw [heq]
  exact (A ⊔ pCoreOf 2 J).mul_mem (Subgroup.mem_sup_right hmemG)
    (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))

theorem not_le_pCoreOf_inf_of_normal_19 {J T N : Subgroup G}
    (hHJ : J ⊔ T ≤ normalizer (J : Set G)) (hT2 : IsPGroup 2 T)
    (hNH : N ≤ J ⊔ T) (hNnorm : (N.subgroupOf (J ⊔ T)).Normal)
    (hNQ : ¬ N ≤ pCoreOf 2 (J ⊔ T)) : ¬ N ⊓ J ≤ pCoreOf 2 J := by
  intro hAJQ
  have hle : N ⊓ J ≤ pCoreOf 2 (J ⊔ T) :=
    hAJQ.trans (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left hHJ)
  exact hNQ (le_pCoreOf_of_inf_le_pCoreOf_19 hHJ hT2 hNH hNnorm hle)

theorem center_bar2_sup_eq_bot_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) : Subgroup.center (Bar2 (L ⊔ K)) = ⊥ := by
  classical
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hne : L ≠ K := h.hne.symm
  have hLJ : L ∈ calC (L ⊔ K) := by
    refine ⟨?_, hLc.2.1, hLc.2.2⟩
    have hKL : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
    have hnorm : (L.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hKL)
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  have hKJ : K ∈ calC (L ⊔ K) := by
    refine ⟨?_, hKc.2.1, hKc.2.2⟩
    have hLK : L ≤ normalizer (K : Set G) := calC_le_normalizer_of_ne hKc hLc hne.symm
    have hnorm : (K.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
        (sup_le hLK Subgroup.le_normalizer)
    exact CFSG.Open.IsSubnormal.step le_sup_right hnorm (CFSG.Open.IsSubnormal.refl _)
  set f₁ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) L with hf₁
  set f₂ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) K with hf₂
  have hcomp₁ : CFSG.IsComponent f₁ := s13_barImage_isComponent hLJ
  have hcomp₂ : CFSG.IsComponent f₂ := s13_barImage_isComponent hKJ
  have hsup : f₁ ⊔ f₂ = ⊤ := barImage_sup_eq_top_19 L K
  have hlayer : CFSG.layer (Bar2 (L ⊔ K)) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le (CFSG.LocalCores.component_le_layer hcomp₁)
      (CFSG.LocalCores.component_le_layer hcomp₂)
  have hn₁ : f₁.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hcomp₁
  have hcomm12 : ∀ a ∈ f₁, ∀ b ∈ f₂, a * b = b * a :=
    uc22p22l_barImage_commute hLJ hKJ hne
  have hLsimple : IsSimpleGroup (Bar2 L) := by
    rcases h.shape with h2 | h3
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
  have hKsimple : IsSimpleGroup (Bar2 K) := by
    obtain ⟨e⟩ := h.hKshape
    exact CFSG.ABGLocalTools.isSimpleGroup_of_mulEquiv e
  have hfs₁ : IsSimpleGroup ↥f₁ := isSimpleGroup_barImage_19 hLJ hLsimple
  have hfs₂ : IsSimpleGroup ↥f₂ := isSimpleGroup_barImage_19 hKJ hKsimple
  have hLnc : ¬ IsMulCommutative (Bar2 L) := by
    rcases h.shape with h2 | h3
    · intro hc
      obtain ⟨a, b, hab⟩ :=
        CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 h2
      exact hab (hc.is_comm.comm a b)
    · intro hc
      obtain ⟨a, b, hab⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 h3
      exact hab (hc.is_comm.comm a b)
  have hKnc : ¬ IsMulCommutative (Bar2 K) := by
    obtain ⟨eK⟩ := h.hKshape
    have hncA5 : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
      rw [alternatingGroup.isMulCommutative_iff_card_le_three]
      norm_num
    exact mt (CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr eK).mp hncA5
  have hfn₁ : ¬ IsMulCommutative ↥f₁ := by
    obtain ⟨e⟩ := s13_bar_equiv hLJ
    rw [hf₁]
    exact mt (CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr e.symm).mp hLnc
  have hfn₂ : ¬ IsMulCommutative ↥f₂ := by
    obtain ⟨e⟩ := s13_bar_equiv hKJ
    rw [hf₂]
    exact mt (CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr e.symm).mp hKnc
  have hne12 : f₁ ≠ f₂ := by
    intro heq
    apply hfn₁
    refine isMulCommutative_iff.mpr fun a b => ?_
    exact Subtype.ext (hcomm12 a a.2 b (heq ▸ b.2))
  have hcenter₁ : Subgroup.center ↥f₁ = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hfn₁
  have hcenter₂ : Subgroup.center ↥f₂ = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hfn₂
  rw [eq_bot_iff]
  intro z hz
  have hzsup : z ∈ f₁ ⊔ f₂ := by rw [hsup]; exact Subgroup.mem_top z
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hzsup
  have ha_center : (⟨a, ha⟩ : ↥f₁) ∈ Subgroup.center ↥f₁ := by
    rw [Subgroup.mem_center_iff]
    intro y
    refine Subtype.ext ?_
    refine mul_right_cancel (b := b) ?_
    calc (y : Bar2 (L ⊔ K)) * a * b = (y : Bar2 (L ⊔ K)) * (a * b) := by group
      _ = (y : Bar2 (L ⊔ K)) * z := by rw [hab]
      _ = z * (y : Bar2 (L ⊔ K)) := Subgroup.mem_center_iff.mp hz (y : Bar2 (L ⊔ K))
      _ = (a * b) * (y : Bar2 (L ⊔ K)) := by rw [hab]
      _ = a * (b * (y : Bar2 (L ⊔ K))) := by group
      _ = a * ((y : Bar2 (L ⊔ K)) * b) := by
        rw [(hcomm12 (y : Bar2 (L ⊔ K)) y.2 b hb).symm]
      _ = a * (y : Bar2 (L ⊔ K)) * b := by group
  have ha1 : a = 1 := by
    have hmem : (⟨a, ha⟩ : ↥f₁) ∈ (⊥ : Subgroup ↥f₁) := by rw [← hcenter₁]; exact ha_center
    have h1 : (⟨a, ha⟩ : ↥f₁) = 1 := by simpa using hmem
    simpa using congrArg Subtype.val h1
  have hb_center : (⟨b, hb⟩ : ↥f₂) ∈ Subgroup.center ↥f₂ := by
    rw [Subgroup.mem_center_iff]
    intro y
    refine Subtype.ext ?_
    calc (y : Bar2 (L ⊔ K)) * b = (y : Bar2 (L ⊔ K)) * (a * b) := by rw [ha1, one_mul]
      _ = (y : Bar2 (L ⊔ K)) * z := by rw [hab]
      _ = z * (y : Bar2 (L ⊔ K)) := Subgroup.mem_center_iff.mp hz (y : Bar2 (L ⊔ K))
      _ = (a * b) * (y : Bar2 (L ⊔ K)) := by rw [hab]
      _ = b * (y : Bar2 (L ⊔ K)) := by rw [ha1, one_mul]
  have hb1 : b = 1 := by
    have hmem : (⟨b, hb⟩ : ↥f₂) ∈ (⊥ : Subgroup ↥f₂) := by rw [← hcenter₂]; exact hb_center
    have h1 : (⟨b, hb⟩ : ↥f₂) = 1 := by simpa using hmem
    simpa using congrArg Subtype.val h1
  rw [Subgroup.mem_bot, ← hab, ha1, hb1, mul_one]

theorem le_sup_pCoreOf_left_or_right_19 {D : Data G}
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {N : Subgroup G}
    (hNH : N ≤ L ⊔ K ⊔ D.T) (hHN : L ⊔ K ⊔ D.T ≤ normalizer (N : Set G))
    (hNQ : ¬ N ≤ pCoreOf 2 (L ⊔ K ⊔ D.T)) :
    L ≤ (N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) ∨
      K ≤ (N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) := by
  classical
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hne : L ≠ K := h.hne.symm
  have hMJ : D.M ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    rw [← h.hLK]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (S17.Lp_le_M D 5)).mp
      (s13_Lp_normal D.M 5)
  have hTJ : D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := D.sylowM.le.trans hMJ
  have hHJ : ((L ⊔ K) ⊔ D.T) ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hTJ
  have hJnormH : (((L ⊔ K).subgroupOf ((L ⊔ K) ⊔ D.T))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHJ
  have hNnormH : (N.subgroupOf ((L ⊔ K) ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  have hA_J : ((N ⊓ (L ⊔ K)).subgroupOf (L ⊔ K)).Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hnA : (n : G) ∈ N ⊓ (L ⊔ K) := Subgroup.mem_subgroupOf.mp hn
    have hnN : (n : G) ∈ N := hnA.1
    have hnJ : (n : G) ∈ L ⊔ K := hnA.2
    have hgJ : (g : G) ∈ L ⊔ K := g.2
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have hmem : (⟨(n : G), hNH hnN⟩ : ↥((L ⊔ K) ⊔ D.T)) ∈
          N.subgroupOf ((L ⊔ K) ⊔ D.T) := Subgroup.mem_subgroupOf.mpr hnN
      have h := Subgroup.Normal.conj_mem hNnormH ⟨(n : G), hNH hnN⟩ hmem
        ⟨(g : G), Subgroup.mem_sup_left hgJ⟩
      exact Subgroup.mem_subgroupOf.mp h
    · have hmem : (⟨(n : G), Subgroup.mem_sup_left hnJ⟩ : ↥((L ⊔ K) ⊔ D.T)) ∈
          (L ⊔ K).subgroupOf ((L ⊔ K) ⊔ D.T) := Subgroup.mem_subgroupOf.mpr hnJ
      have h := Subgroup.Normal.conj_mem hJnormH ⟨(n : G), Subgroup.mem_sup_left hnJ⟩ hmem
        ⟨(g : G), Subgroup.mem_sup_left hgJ⟩
      exact Subgroup.mem_subgroupOf.mp h
  let π : ↥(L ⊔ K) →* Bar2 (L ⊔ K) := QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))
  have hker : π.ker = (pCoreOf 2 (L ⊔ K)).subgroupOf (L ⊔ K) := by
    rw [show π.ker = CFSG.pCore 2 ↥(L ⊔ K) from QuotientGroup.ker_mk' _,
      CFSG.openPCoreOf_subgroupOf]
  let Ā : Subgroup (Bar2 (L ⊔ K)) := ((N ⊓ (L ⊔ K)).subgroupOf (L ⊔ K)).map π
  have hĀdef : Ā = UC22.barImage (L ⊔ K) (N ⊓ (L ⊔ K)) := rfl
  have hĀn : Ā.Normal := hA_J.map π (QuotientGroup.mk'_surjective _)
  have hĀne : Ā ≠ ⊥ := by
    intro hbot
    have hAQ : N ⊓ (L ⊔ K) ≤ pCoreOf 2 (L ⊔ K) := by
      intro x hx
      have hxJ : x ∈ L ⊔ K := hx.2
      have hxmap : π ⟨x, hxJ⟩ ∈ Ā :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
      rw [hbot] at hxmap
      have hx1 : π ⟨x, hxJ⟩ = 1 := by simpa using hxmap
      have hxker : (⟨x, hxJ⟩ : ↥(L ⊔ K)) ∈ π.ker := MonoidHom.mem_ker.mpr hx1
      rw [hker] at hxker
      simpa using (Subgroup.mem_subgroupOf.mp hxker)
    exact not_le_pCoreOf_inf_of_normal_19 hHJ D.sylowM.isPGroup hNH hNnormH hNQ hAQ
  have hLJ : L ∈ calC (L ⊔ K) := by
    refine ⟨?_, hLc.2.1, hLc.2.2⟩
    have hKL : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
    have hnorm : (L.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hKL)
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  have hKJ : K ∈ calC (L ⊔ K) := by
    refine ⟨?_, hKc.2.1, hKc.2.2⟩
    have hLK : L ≤ normalizer (K : Set G) := calC_le_normalizer_of_ne hKc hLc hne.symm
    have hnorm : (K.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
        (sup_le hLK Subgroup.le_normalizer)
    exact CFSG.Open.IsSubnormal.step le_sup_right hnorm (CFSG.Open.IsSubnormal.refl _)
  set f₁ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) L with hf₁
  set f₂ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) K with hf₂
  have hcomp₁ : CFSG.IsComponent f₁ := s13_barImage_isComponent hLJ
  have hcomp₂ : CFSG.IsComponent f₂ := s13_barImage_isComponent hKJ
  have hsup : f₁ ⊔ f₂ = ⊤ := barImage_sup_eq_top_19 L K
  have hlayer : CFSG.layer (Bar2 (L ⊔ K)) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le (CFSG.LocalCores.component_le_layer hcomp₁)
      (CFSG.LocalCores.component_le_layer hcomp₂)
  have hn₁ : f₁.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hcomp₁
  have hn₂ : f₂.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlayer hcomp₂
  have hLsimple : IsSimpleGroup (Bar2 L) := by
    rcases h.shape with h2 | h3
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
  have hKsimple : IsSimpleGroup (Bar2 K) := by
    obtain ⟨e⟩ := h.hKshape
    exact CFSG.ABGLocalTools.isSimpleGroup_of_mulEquiv e
  have hfs₁ : IsSimpleGroup ↥f₁ := isSimpleGroup_barImage_19 hLJ hLsimple
  have hfs₂ : IsSimpleGroup ↥f₂ := isSimpleGroup_barImage_19 hKJ hKsimple
  have hLnc : ¬ IsMulCommutative (Bar2 L) := by
    rcases h.shape with h2 | h3
    · intro hc
      obtain ⟨a, b, hab⟩ :=
        CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 h2
      exact hab (hc.is_comm.comm a b)
    · intro hc
      obtain ⟨a, b, hab⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 h3
      exact hab (hc.is_comm.comm a b)
  have hKnc : ¬ IsMulCommutative (Bar2 K) := by
    obtain ⟨eK⟩ := h.hKshape
    have hncA5 : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
      rw [alternatingGroup.isMulCommutative_iff_card_le_three]
      norm_num
    exact mt (CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr eK).mp hncA5
  have hfn₁ : ¬ IsMulCommutative ↥f₁ := by
    obtain ⟨e⟩ := s13_bar_equiv hLJ
    rw [hf₁]
    exact mt (CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr e.symm).mp hLnc
  have hfn₂ : ¬ IsMulCommutative ↥f₂ := by
    obtain ⟨e⟩ := s13_bar_equiv hKJ
    rw [hf₂]
    exact mt (CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr e.symm).mp hKnc
  have hcomm12 : ∀ a ∈ f₁, ∀ b ∈ f₂, Commute a b := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hLJ hKJ hne a ha b hb
  have hne12 : f₁ ≠ f₂ := by
    intro heq
    apply hfn₁
    refine isMulCommutative_iff.mpr fun a b => ?_
    exact Subtype.ext (hcomm12 a a.2 b (heq ▸ b.2))
  have hcenter : Subgroup.center (Bar2 (L ⊔ K)) = ⊥ := center_bar2_sup_eq_bot_19 h
  have hfactor : f₁ ≤ Ā ∨ f₂ ≤ Ā := by
    have hnab₁ : ∃ x y : ↥f₁, x * y ≠ y * x := by
      by_contra h
      push Not at h
      exact hfn₁ (isMulCommutative_iff.mpr fun x y => h x y)
    have hnab₂ : ∃ x y : ↥f₂, x * y ≠ y * x := by
      by_contra h
      push Not at h
      exact hfn₂ (isMulCommutative_iff.mpr fun x y => h x y)
    have hq₁ : CFSG.IsQuasisimple ↥f₁ :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab₁).1
    have hq₂ : CFSG.IsQuasisimple ↥f₂ :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab₂).1
    have hcenter₁ : Subgroup.center ↥f₁ = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hfn₁
    have hcenter₂ : Subgroup.center ↥f₂ = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hfn₂
    have hW₁ := CFSG.LocalCores.quasisimple_normal_subgroups hq₁
      (N := (Ā ⊓ f₁).subgroupOf f₁) inferInstance
    have hW₂ := CFSG.LocalCores.quasisimple_normal_subgroups hq₂
      (N := (Ā ⊓ f₂).subgroupOf f₂) inferInstance
    by_cases h1 : f₁ ≤ Ā
    · exact Or.inl h1
    · right
      by_cases h2 : f₂ ≤ Ā
      · exact h2
      · exfalso
        have hinf₁ : Ā ⊓ f₁ = ⊥ := by
          rcases hW₁ with htop | hle
          · exact absurd (le_trans (Subgroup.subgroupOf_eq_top.mp htop) inf_le_left) h1
          · have hbot : (Ā ⊓ f₁).subgroupOf f₁ = ⊥ := by
              have hle' : (Ā ⊓ f₁).subgroupOf f₁ ≤ ⊥ := by rw [← hcenter₁]; exact hle
              exact le_bot_iff.mp hle'
            rw [eq_bot_iff]
            intro z hz
            have hzf : z ∈ f₁ := (Subgroup.mem_inf.mp hz).2
            have hmem : (⟨z, hzf⟩ : ↥f₁) ∈ (Ā ⊓ f₁).subgroupOf f₁ :=
              Subgroup.mem_subgroupOf.mpr hz
            rw [hbot] at hmem
            simpa using hmem
        have hinf₂ : Ā ⊓ f₂ = ⊥ := by
          rcases hW₂ with htop | hle
          · exact absurd (le_trans (Subgroup.subgroupOf_eq_top.mp htop) inf_le_left) h2
          · have hbot : (Ā ⊓ f₂).subgroupOf f₂ = ⊥ := by
              have hle' : (Ā ⊓ f₂).subgroupOf f₂ ≤ ⊥ := by rw [← hcenter₂]; exact hle
              exact le_bot_iff.mp hle'
            rw [eq_bot_iff]
            intro z hz
            have hzf : z ∈ f₂ := (Subgroup.mem_inf.mp hz).2
            have hmem : (⟨z, hzf⟩ : ↥f₂) ∈ (Ā ⊓ f₂).subgroupOf f₂ :=
              Subgroup.mem_subgroupOf.mpr hz
            rw [hbot] at hmem
            simpa using hmem
        have hcomm₁ : ⁅Ā, f₁⁆ = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          have hzA : z ∈ Ā := Subgroup.commutator_le_left Ā f₁ hz
          have hzf : z ∈ f₁ := Subgroup.commutator_le_right Ā f₁ hz
          have hmem : z ∈ Ā ⊓ f₁ := Subgroup.mem_inf.mpr ⟨hzA, hzf⟩
          rwa [hinf₁] at hmem
        have hcomm₂ : ⁅Ā, f₂⁆ = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          have hzA : z ∈ Ā := Subgroup.commutator_le_left Ā f₂ hz
          have hzf : z ∈ f₂ := Subgroup.commutator_le_right Ā f₂ hz
          have hmem : z ∈ Ā ⊓ f₂ := Subgroup.mem_inf.mpr ⟨hzA, hzf⟩
          rwa [hinf₂] at hmem
        apply hĀne
        rw [eq_bot_iff]
        intro x hx
        have hcent₁ : x ∈ Subgroup.centralizer (f₁ : Set (Bar2 (L ⊔ K))) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm₁) hx
        have hcent₂ : x ∈ Subgroup.centralizer (f₂ : Set (Bar2 (L ⊔ K))) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm₂) hx
        have hxcenter : x ∈ Subgroup.center (Bar2 (L ⊔ K)) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have hy : y ∈ f₁ ⊔ f₂ := by rw [hsup]; exact Subgroup.mem_top y
          obtain ⟨c, hc, d, hd, hcd⟩ := Subgroup.mem_sup_of_normal_left.mp hy
          have hxc : c * x = x * c := Subgroup.mem_centralizer_iff.mp hcent₁ c hc
          have hxd : d * x = x * d := Subgroup.mem_centralizer_iff.mp hcent₂ d hd
          rw [← hcd]
          calc c * d * x = c * (d * x) := by group
            _ = c * (x * d) := by rw [hxd]
            _ = c * x * d := by group
            _ = x * c * d := by rw [hxc]
            _ = x * (c * d) := by group
        rw [hcenter] at hxcenter
        simpa using hxcenter
  rcases hfactor with hf | hf
  · left
    exact le_sup_pCoreOf_of_barImage_le_19 le_sup_left (by
      rw [← hĀdef]
      exact hf)
  · right
    exact le_sup_pCoreOf_of_barImage_le_19 le_sup_right (by
      rw [← hĀdef]
      exact hf)

theorem sup_le_of_normal_LKT_19 {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hLn : ¬ (L.subgroupOf D.M).Normal)
    {N : Subgroup G} (hNH : N ≤ L ⊔ K ⊔ D.T) (hHN : L ⊔ K ⊔ D.T ≤ normalizer (N : Set G))
    (hNQ : ¬ N ≤ pCoreOf 2 (L ⊔ K ⊔ D.T)) : L ⊔ K ≤ N := by
  classical
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hne : L ≠ K := h.hne.symm
  have hMJ : D.M ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    rw [← h.hLK]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (S17.Lp_le_M D 5)).mp
      (s13_Lp_normal D.M 5)
  have hTJ : D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := D.sylowM.le.trans hMJ
  have hHJ : ((L ⊔ K) ⊔ D.T) ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hTJ
  have hJnormH : (((L ⊔ K).subgroupOf ((L ⊔ K) ⊔ D.T))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHJ
  have hNnormH : (N.subgroupOf ((L ⊔ K) ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  have hAH : (N ⊓ (L ⊔ K)) ≤ (L ⊔ K) ⊔ D.T := inf_le_right.trans le_sup_left
  have hAinfH : ((N ⊓ (L ⊔ K)).subgroupOf ((L ⊔ K) ⊔ D.T)).Normal := by
    have h1 : (N ⊓ (L ⊔ K)).subgroupOf ((L ⊔ K) ⊔ D.T) =
        N.subgroupOf ((L ⊔ K) ⊔ D.T) ⊓ (L ⊔ K).subgroupOf ((L ⊔ K) ⊔ D.T) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [h1]
    exact Subgroup.normal_inf_normal _ _
  have hLKQ := le_sup_pCoreOf_left_or_right_19 h hNH hHN hNQ
  have hperm : PermutesPair D.M L K := permutesPair_of_ctx19_one h
  obtain ⟨x, hxM, hKx⟩ : ∃ x ∈ D.M, K = conjSubgroup L x := by
    rcases dichotomy_19 h with ⟨-, x, hxM, hKx⟩ | ⟨-, hLn', -⟩
    · exact ⟨x, hxM, hKx⟩
    · exact absurd hLn' hLn
  have hKx' : K = L.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [hKx]
    rfl
  have hSyl : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  obtain ⟨t, htT, htL, htK⟩ :=
    s16h_z3_exists_swap_mem_sylow (D.M.inv_mem hxM) hKx' (fun hKL => hne hKL.symm) hperm hSyl
  have htA : t ∈ normalizer ((N ⊓ (L ⊔ K) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).1 hAinfH (Subgroup.mem_sup_right htT)
  have htQ : t ∈ normalizer (pCoreOf 2 (L ⊔ K) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ K)
      (hHJ (Subgroup.mem_sup_right htT))
  have htN : t ∈ normalizer
      (((N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup (N ⊓ (L ⊔ K)) (pCoreOf 2 (L ⊔ K))
      ⟨htA, htQ⟩
  have hswap_le : ∀ {X : Subgroup G}, X ≤ (N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) →
      X.map (MulAut.conj t).toMonoidHom ≤ (N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) := by
    intro X hX y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    have hz' : t * z * t⁻¹ ∈ (N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) :=
      (Subgroup.mem_normalizer_iff.mp htN z).mp (hX hz)
    rw [← hzy]
    simpa [MulAut.conj_apply] using hz'
  have hLKle : L ⊔ K ≤ (N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) := by
    rcases hLKQ with hLQ | hKQ
    · refine sup_le hLQ ?_
      have h := hswap_le hLQ
      rwa [htL] at h
    · refine sup_le ?_ hKQ
      have h := hswap_le hKQ
      rwa [htK] at h
  have hJperf : ⁅(L ⊔ K : Subgroup G), L ⊔ K⁆ = L ⊔ K := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      exact (L ⊔ K).mul_mem ((L ⊔ K).mul_mem ((L ⊔ K).mul_mem hx hy) ((L ⊔ K).inv_mem hx))
        ((L ⊔ K).inv_mem hy)
    calc L ⊔ K = ⁅L, L⁆ ⊔ ⁅K, K⁆ := by rw [hLc.2.1, hKc.2.1]
      _ ≤ ⁅(L ⊔ K : Subgroup G), L ⊔ K⁆ :=
        sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
          (Subgroup.commutator_mono le_sup_right le_sup_right)
  have hAnLK : ((N ⊓ (L ⊔ K)).subgroupOf (L ⊔ K)).Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hnA : (n : G) ∈ N ⊓ (L ⊔ K) := Subgroup.mem_subgroupOf.mp hn
    have hnN : (n : G) ∈ N := hnA.1
    have hnJ : (n : G) ∈ L ⊔ K := hnA.2
    have hgJ : (g : G) ∈ L ⊔ K := g.2
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have hmem : (⟨(n : G), hNH hnN⟩ : ↥((L ⊔ K) ⊔ D.T)) ∈
          N.subgroupOf ((L ⊔ K) ⊔ D.T) := Subgroup.mem_subgroupOf.mpr hnN
      have h := Subgroup.Normal.conj_mem hNnormH ⟨(n : G), hNH hnN⟩ hmem
        ⟨(g : G), Subgroup.mem_sup_left hgJ⟩
      exact Subgroup.mem_subgroupOf.mp h
    · have hmem : (⟨(n : G), Subgroup.mem_sup_left hnJ⟩ : ↥((L ⊔ K) ⊔ D.T)) ∈
          (L ⊔ K).subgroupOf ((L ⊔ K) ⊔ D.T) := Subgroup.mem_subgroupOf.mpr hnJ
      have h := Subgroup.Normal.conj_mem hJnormH ⟨(n : G), Subgroup.mem_sup_left hnJ⟩ hmem
        ⟨(g : G), Subgroup.mem_sup_left hgJ⟩
      exact Subgroup.mem_subgroupOf.mp h
  have hAmap : ((N ⊓ (L ⊔ K)).subgroupOf (L ⊔ K)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective z
    have hj : (j : G) ∈ (N ⊓ (L ⊔ K)) ⊔ pCoreOf 2 (L ⊔ K) := hLKle j.2
    have hmem : j ∈ (N ⊓ (L ⊔ K)).subgroupOf (L ⊔ K) ⊔
        (pCoreOf 2 (L ⊔ K)).subgroupOf (L ⊔ K) := by
      rw [← Subgroup.subgroupOf_sup inf_le_right (CFSG.openPCoreOf_le 2 (L ⊔ K))]
      exact hj
    obtain ⟨a, ha, q, hq, haq⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hq1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) q = 1 := by
      rw [← MonoidHom.mem_ker,
        show (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))).ker =
          (pCoreOf 2 (L ⊔ K)).subgroupOf (L ⊔ K) from by
            rw [QuotientGroup.ker_mk', CFSG.openPCoreOf_subgroupOf]]
      exact hq
    have hax : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) a =
        QuotientGroup.mk j := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) (a * q) =
          QuotientGroup.mk j :=
        congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) haq
      rw [← h1, map_mul, hq1, mul_one]
    rw [← hax]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  have hAeq : N ⊓ (L ⊔ K) = L ⊔ K :=
    eq_of_normal_map_eq_top_19 inf_le_right hAnLK hJperf hAmap
  rw [← hAeq]
  exact inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
