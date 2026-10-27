module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

noncomputable abbrev Ia (c : Ctx82E3 D) (a : G) : Subgroup G :=
  inSubgroup perfectResidual (c.L ⊓ Subgroup.centralizer ({a} : Set G))

theorem Ia_le (c : Ctx82E3 D) (a : G) :
    Ia c a ≤ c.L ⊓ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.map_subtype_le _

theorem Ia_perfect (c : Ctx82E3 D) (a : G) : Group.IsPerfect ↥(Ia c a) := by
  let K : Subgroup G := c.L ⊓ Subgroup.centralizer ({a} : Set G)
  have hperf : Group.IsPerfect ↥(perfectResidual ↥K) :=
    (CFSG.perfect_residual_characterization (G := ↥K)).2.2.1
  let e : ↥(perfectResidual ↥K) ≃* ↥(Ia c a) :=
    (perfectResidual ↥K).equivMapOfInjective K.subtype K.subtype_injective
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem jtilde_perfect {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) :
    Group.IsPerfect (Jtilde J) :=
  (CFSG.RankThree.PartOne.isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt (p := 3)
    Nat.prime_three hJ).1

theorem j0_isSimpleGroup {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) :
    IsSimpleGroup (J0 J) :=
  (CFSG.RankThree.PartOne.isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt (p := 3)
    Nat.prime_three hJ).2.1

theorem j0_nonabelian {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) :
    ∃ x y : J0 J, x * y ≠ y * x :=
  (CFSG.RankThree.PartOne.isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt (p := 3)
    Nat.prime_three hJ).2.2

theorem j0_catalog (c : Ctx82E3 D) {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a)
    (ha1 : a ≠ 1) : IsCatalogGroup (J0 J) := by
  have hJC : J ≤ Subgroup.centralizer ({a} : Set G) :=
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ).1
  have hKc : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    isKGroup_centralizer c ha1
  haveI := j0_isSimpleGroup (a := a) hJ
  let e : ↥(J.subgroupOf (Subgroup.centralizer ({a} : Set G))) ≃* ↥J :=
    Subgroup.subgroupOfEquivOfLe hJC
  let f : ↥J →* J0 J :=
    (QuotientGroup.mk' (Subgroup.center (Jtilde J))).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 J))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective (Subgroup.center (Jtilde J))).comp
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 J))
  exact CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hKc _ (j0_nonabelian (a := a) hJ)
    (f.comp e.toMonoidHom) (hf.comp e.surjective)

theorem outer_jtilde_solvable (c : Ctx82E3 D) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt 3 a) (h3a : orderOf a = 3)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Jtilde J)) := by
  haveI := jtilde_perfect (a := a) hJ
  have ha1 : a ≠ 1 := by rintro rfl; rw [orderOf_one] at h3a; omega
  haveI := j0_isSimpleGroup (a := a) hJ
  have hcat : IsCatalogGroup (J0 J) := j0_catalog c (a := a) hJ ha1
  haveI : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (J0 J)) :=
    hSch (J0 J) (j0_isSimpleGroup (a := a) hJ) (j0_nonabelian (a := a) hJ) hcat
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient (Jtilde J)

theorem range_le_conj_range_of_perfect {A H : Type} [Group A] [Group.IsPerfect A]
    [Group H] [Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer H)]
    (φ : A →* MulAut H) :
    φ.range ≤ (MulAut.conj : H →* MulAut H).range := by
  rintro σ ⟨x, rfl⟩
  obtain ⟨h, hh⟩ :=
    CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner φ x
  exact ⟨h, hh.symm⟩

@[expose] def F9Input (c : Ctx82E3 D) (P : Subgroup G) (a : G) : Prop :=
  IsTripleCover (↥(Ia c a) ⧸ CFSG.Open.pCore 2 ↥(Ia c a)) ↥(alternatingGroup (Fin 6)) ∧
    zSub P c.L ≤ Ia c a ∧
    ⁅Ia c a, zSub P c.L⁆ ≤ CFSG.Open.pCoreOf 2 (Ia c a) ∧
    Ia c a = Subgroup.closure {x : G | x ∈ Ia c a ∧ orderOf x = 3}

@[expose] noncomputable def piJ {J : Subgroup G} (hIJ : Ia c a ≤ Subgroup.normalizer (J : Set G)) :
    ↥(Ia c a) →* MulAut (Jtilde J) :=
  (thetaQuotMulAut J).comp (J.normalizerMonoidHom.comp (Subgroup.inclusion hIJ))

theorem piJ_range_le_conj {J : Subgroup G} (hIJ : Ia c a ≤ Subgroup.normalizer (J : Set G))
    (hJ : J ∈ thetaComponentsAt 3 a) (h3a : orderOf a = 3)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    (piJ c hIJ).range ≤ (MulAut.conj : Jtilde J →* MulAut (Jtilde J)).range := by
  haveI : Group.IsPerfect ↥(Ia c a) := Ia_perfect c a
  haveI := outer_jtilde_solvable c (a := a) hJ h3a hSch
  exact range_le_conj_range_of_perfect _

theorem conj_ker {H : Type} [Group H] :
    (MulAut.conj : H →* MulAut H).ker = Subgroup.center H := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have h1 : (MulAut.conj g) x = (1 : MulAut H) x := by rw [h]
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    have h2 : g * x = x * g := by
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h1]
    exact h2.symm
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply]
    have hx := h x
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [← hx]
      _ = x := by group

theorem card_conj_range {H : Type} [Group H] [Finite H] :
    Nat.card (MulAut.conj : H →* MulAut H).range = Nat.card (H ⧸ Subgroup.center H) := by
  let e : (H ⧸ Subgroup.center H) ≃* (MulAut.conj : H →* MulAut H).range :=
    (QuotientGroup.quotientMulEquivOfEq (conj_ker (H := H)).symm).trans
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : H →* MulAut H))
  exact (Nat.card_congr e.toEquiv).symm

theorem ker_eq_bot_of_isTripleCover {T B : Type} [Group T] [Finite T] [Group B]
    (hperf : Group.IsPerfect T) (hT : IsTripleCover T ↥(alternatingGroup (Fin 6)))
    (f : T →* B) (hf : Function.Surjective f)
    {ζ : T} (hζZ : ζ ∈ Subgroup.center T) (hζ3 : orderOf ζ = 3) (hζB : f ζ ≠ 1) :
    f.ker = ⊥ := by
  classical
  haveI hTperf : Group.IsPerfect T := hperf
  have hZcard : Nat.card (Subgroup.center T) = 3 := hT.1
  haveI : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := f) hf
  haveI : Nontrivial B := ⟨1, f ζ, hζB.symm⟩
  set Z := Subgroup.center T with hZ
  have hZgen : Subgroup.zpowers ζ = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hζZ) (le_of_eq ?_)
    rw [Nat.card_zpowers, hζ3, hZcard]
  by_contra hne
  set K := f.ker with hKdef
  have hKne : K ≠ ⊥ := hne
  haveI hKnorm : K.Normal := MonoidHom.normal_ker f
  let q : T →* T ⧸ Z := QuotientGroup.mk' Z
  haveI hA6simple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  haveI hsimple : IsSimpleGroup (T ⧸ Z) := by
    obtain ⟨e⟩ := hT.2
    exact MulEquiv.isSimpleGroup e
  haveI hKmapNormal : (K.map q).Normal := hKnorm.map q (QuotientGroup.mk'_surjective Z)
  rcases Subgroup.Normal.eq_bot_or_eq_top (K.map q) with hbot | htop
  · have hKZ : K ≤ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      exact (Subgroup.map_eq_bot_iff (f := q) K).mp hbot
    have hKcard : Nat.card K = 3 := by
      have hdvd : Nat.card K ∣ 3 := by
        simpa [hZcard] using Subgroup.card_dvd_of_le hKZ
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (Subgroup.card_eq_one.mp h1) hKne
      · exact h3
    have hKZeq : K = Z := Subgroup.eq_of_le_of_card_ge hKZ (by rw [hKcard, hZcard])
    have hζK : ζ ∈ f.ker := by
      rw [← hKdef, hKZeq]
      exact hζZ
    exact hζB (MonoidHom.mem_ker.mp hζK)
  · have hTKZ : ⊤ ≤ K ⊔ Z := by
      intro x _
      have hx : q x ∈ K.map q := by rw [htop]; exact Subgroup.mem_top (q x)
      obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hx
      have hxz : x * k⁻¹ ∈ Z := by
        rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, ← hkx,
          mul_inv_cancel]
      have hx' : x = (x * k⁻¹) * k := by group
      rw [hx']
      exact (K ⊔ Z).mul_mem (Subgroup.mem_sup_right (S := K) (T := Z) hxz)
        (Subgroup.mem_sup_left (S := K) (T := Z) hkK)
    have habel : ∀ u v : B, u * v = v * u := by
      intro u v
      obtain ⟨x, rfl⟩ := hf u
      obtain ⟨y, rfl⟩ := hf v
      have hx : x ∈ K ⊔ Z := hTKZ (Subgroup.mem_top x)
      have hy : y ∈ K ⊔ Z := hTKZ (Subgroup.mem_top y)
      obtain ⟨a, haK, z, hzZ, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      obtain ⟨b, hbK, w, hwZ, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      have hfa : f a = 1 := MonoidHom.mem_ker.mp haK
      have hfb : f b = 1 := MonoidHom.mem_ker.mp hbK
      simp only [map_mul, hfa, hfb, one_mul]
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hzZ) w]
    exact Group.IsPerfect.not_isMulCommutative B ⟨⟨habel⟩⟩

theorem card_eq_1080_of_isTripleCover {T : Type} [Group T] [Finite T]
    (hT : IsTripleCover T ↥(alternatingGroup (Fin 6))) : Nat.card T = 1080 := by
  obtain ⟨hZc, ⟨e⟩⟩ := hT
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)
  rw [Nat.card_congr e.toEquiv, hA6, hZc] at h
  omega

theorem dvd_1080_of_ker_eq_bot {T B : Type} [Group T] [Finite T] [Group B] [Finite B]
    (hT : IsTripleCover T ↥(alternatingGroup (Fin 6))) (f : T →* B) (hf : Function.Surjective f)
    (hker : f.ker = ⊥) : 1080 ∣ Nat.card B := by
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hcard : Nat.card B = Nat.card T :=
    (Nat.card_congr (MulEquiv.ofBijective f ⟨hinj, hf⟩).toEquiv).symm
  rw [hcard, card_eq_1080_of_isTripleCover hT]

theorem piJ_apply_z {J : Subgroup G} (hIJ : Ia c a ≤ Subgroup.normalizer (J : Set G))
    {z : G} (hzI : z ∈ Ia c a) (hzN : z ∈ Subgroup.normalizer (J : Set G)) :
    piJ c hIJ ⟨z, hzI⟩ = thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) := by
  have h1 : (Subgroup.inclusion hIJ) ⟨z, hzI⟩ = (⟨z, hzN⟩ : Subgroup.normalizer (J : Set G)) :=
    Subtype.ext rfl
  simp only [piJ, MonoidHom.comp_apply, h1]

theorem orderOf_piJ_apply_z {J : Subgroup G} (hIJ : Ia c a ≤ Subgroup.normalizer (J : Set G))
    {z : G} (hzI : z ∈ Ia c a) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1) :
    orderOf (piJ c hIJ ⟨z, hzI⟩) = 3 := by
  have hzI3 : orderOf (⟨z, hzI⟩ : ↥(Ia c a)) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hz3
  have hne : piJ c hIJ ⟨z, hzI⟩ ≠ 1 := fun h =>
    hπ ((piJ_apply_z c hIJ hzI hzN).symm.trans h)
  have hdvd : orderOf (piJ c hIJ ⟨z, hzI⟩) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    have h3 : (⟨z, hzI⟩ : ↥(Ia c a)) ^ 3 = 1 := by
      simpa [hzI3] using pow_orderOf_eq_one (⟨z, hzI⟩ : ↥(Ia c a))
    calc (piJ c hIJ ⟨z, hzI⟩) ^ 3
        = (piJ c hIJ) ((⟨z, hzI⟩ : ↥(Ia c a)) ^ 3) := (map_pow (piJ c hIJ) _ 3).symm
      _ = 1 := by rw [h3, map_one]
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h3

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
