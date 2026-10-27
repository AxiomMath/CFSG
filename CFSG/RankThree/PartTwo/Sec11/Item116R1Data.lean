module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Quot
public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact
public import CFSG.RankThree.PartTwo.Sec11.Item116EiiO

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

noncomputable def thetaImage (a : G) (Y' : Subgroup G) :
    Subgroup (↥(Subgroup.centralizer ({a} : Set G)) ⧸
      aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) :=
  (Y'.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))

theorem ad1_le_centralizer_of_mem {a : G} {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) :
    Y ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨L, -, rfl⟩ := hY
  rintro x hx
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem ad1_inSubgroup_theta_eq {C Y : Subgroup G} (hYC : Y ≤ C) :
    inSubgroup (aschbacherSolvableCore 3) Y =
      (inSubgroup (aschbacherSolvableCore 3) (Y.subgroupOf C)).map C.subtype := by
  have h := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
    (Subgroup.subgroupOfEquivOfLe hYC)
  have hcomp : Y.subtype.comp (Subgroup.subgroupOfEquivOfLe hYC).toMonoidHom =
      C.subtype.comp (Y.subgroupOf C).subtype :=
    MonoidHom.ext fun x => rfl
  unfold inSubgroup
  rw [← h, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem ad1_image_eq_aux {C Y K : Subgroup G} (hYC : Y ≤ C) (hKC : K ≤ C)
    (hL : Y.subgroupOf C ∈ thetaComponents 3 ↥C)
    (hsup : Y = K ⊔ inSubgroup (aschbacherSolvableCore 3) Y) :
    (Y.subgroupOf C).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C)) =
      (K.subgroupOf C).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C)) := by
  have htr := ad1_inSubgroup_theta_eq hYC
  have hθ : inSubgroup (aschbacherSolvableCore 3) (Y.subgroupOf C) ≤
      aschbacherSolvableCore 3 ↥C := by
    rw [(theta_component_quotient_structure Nat.prime_three hL).1]
    exact inf_le_right
  have hθY : inSubgroup (aschbacherSolvableCore 3) Y ≤ C :=
    le_sup_right.trans (hsup.symm.le.trans hYC)
  have h2 : (inSubgroup (aschbacherSolvableCore 3) Y).subgroupOf C =
      inSubgroup (aschbacherSolvableCore 3) (Y.subgroupOf C) := by
    rw [htr]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hsupH : Y.subgroupOf C =
      K.subgroupOf C ⊔ inSubgroup (aschbacherSolvableCore 3) (Y.subgroupOf C) := by
    calc Y.subgroupOf C = (K ⊔ inSubgroup (aschbacherSolvableCore 3) Y).subgroupOf C :=
          congrArg (fun X : Subgroup G => X.subgroupOf C) hsup
      _ = K.subgroupOf C ⊔ (inSubgroup (aschbacherSolvableCore 3) Y).subgroupOf C :=
          Subgroup.subgroupOf_sup hKC hθY
      _ = K.subgroupOf C ⊔ inSubgroup (aschbacherSolvableCore 3) (Y.subgroupOf C) := by
          rw [h2]
  rw [hsupH, Subgroup.map_sup]
  refine sup_eq_left.mpr ?_
  rintro z hz
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
  have hx1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C) x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hθ hx
  rw [hx1]
  exact Subgroup.one_mem _

theorem subgroupOf_mem_thetaComponents {a : G} {Y' : Subgroup G} (hY' : Y' ∈ thetaComponentsAt 3 a) :
    Y'.subgroupOf (Subgroup.centralizer ({a} : Set G)) ∈
      thetaComponents 3 ↥(Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨L, hL, rfl⟩ := hY'
  show (L.map (Subgroup.centralizer ({a} : Set G)).subtype).subgroupOf
      (Subgroup.centralizer ({a} : Set G)) ∈
    thetaComponents 3 ↥(Subgroup.centralizer ({a} : Set G))
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
    (Subgroup.centralizer ({a} : Set G)).subtype_injective]
  exact hL

theorem isComponent_thetaImage {a : G} {Y' : Subgroup G} (hY' : Y' ∈ thetaComponentsAt 3 a) :
    CFSG.IsComponent (thetaImage a Y') := by
  unfold thetaImage
  exact isComponent_map_of_mem_thetaComponents Nat.prime_three
    (subgroupOf_mem_thetaComponents hY')

theorem thetaImage_injective {a : G} {Y₁ Y₂ : Subgroup G} (h₁ : Y₁ ∈ thetaComponentsAt 3 a)
    (h₂ : Y₂ ∈ thetaComponentsAt 3 a) (h : thetaImage a Y₁ = thetaImage a Y₂) : Y₁ = Y₂ := by
  have hL : Y₁.subgroupOf (Subgroup.centralizer ({a} : Set G)) =
      Y₂.subgroupOf (Subgroup.centralizer ({a} : Set G)) :=
    (theta_component_quotient_correspondence (H := ↥(Subgroup.centralizer ({a} : Set G)))
      Nat.prime_three).1.injOn (subgroupOf_mem_thetaComponents h₁)
      (subgroupOf_mem_thetaComponents h₂) h
  calc Y₁ = (Y₁.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (ad1_le_centralizer_of_mem h₁)).symm
    _ = (Y₂.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype := by rw [hL]
    _ = Y₂ := Subgroup.map_subgroupOf_eq_of_le (ad1_le_centralizer_of_mem h₂)

theorem thetaImage_eq_map_of_eq_sup {a : G} {Y' K : Subgroup G} (hY' : Y' ∈ thetaComponentsAt 3 a)
    (hKY : K ≤ Y') (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hsup : Y' = K ⊔ inSubgroup (aschbacherSolvableCore 3) Y') :
    thetaImage a Y' =
      (K.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) := by
  unfold thetaImage
  exact ad1_image_eq_aux (ad1_le_centralizer_of_mem hY') hKa
    (subgroupOf_mem_thetaComponents hY') hsup

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_sylow_three_thetaImage_K {L : Subgroup G} {a : G}
    (hL : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) :
    ∀ S : Sylow 3 ↥(((sec11K L a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))),
      IsCyclic S := by
  let ι : ↥((sec11K L a).subgroupOf (Subgroup.centralizer ({a} : Set G))) →* ↥L :=
    MonoidHom.mk' (fun k : ↥((sec11K L a).subgroupOf (Subgroup.centralizer ({a} : Set G))) =>
      (⟨k.1.1, sec11K_le L a (Subgroup.mem_subgroupOf.mp k.2)⟩ : ↥L))
      (fun _ _ => rfl)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h2 := congrArg (fun z : ↥L => (z : G)) hxy
    have h1 : x.1.1 = y.1.1 := h2
    exact Subtype.ext (Subtype.ext h1)
  have hNnot : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hg := injOn_three_of_card_coprime (aschbacherSolvableCore 3 ↥L) hNnot ι hι
  have hW : ∀ S : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L), IsCyclic S :=
    fun S => isCyclic_sylow_three_of_isList1016 hL S
  exact isCyclic_sylow_of_surjective_of_injOn
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp ι) hg hW
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))).subgroupMap
      ((sec11K L a).subgroupOf (Subgroup.centralizer ({a} : Set G))))
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))).subgroupMap_surjective
      ((sec11K L a).subgroupOf (Subgroup.centralizer ({a} : Set G))))

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_sylow_three_image_of_embed {a : G} {L : Subgroup G}
    (hL : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) {K' : Subgroup G}
    (ι : ↥(K'.subgroupOf (Subgroup.centralizer ({a} : Set G))) →* ↥L) (hι : Function.Injective ι) :
    ∀ S : Sylow 3 ↥((K'.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))),
      IsCyclic S := by
  have hNnot : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hg := injOn_three_of_card_coprime (aschbacherSolvableCore 3 ↥L) hNnot ι hι
  have hW : ∀ S : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L), IsCyclic S :=
    fun S => isCyclic_sylow_three_of_isList1016 hL S
  exact isCyclic_sylow_of_surjective_of_injOn
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp ι) hg hW
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))).subgroupMap
      (K'.subgroupOf (Subgroup.centralizer ({a} : Set G))))
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))).subgroupMap_surjective
      (K'.subgroupOf (Subgroup.centralizer ({a} : Set G))))

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem aComponentData (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d)
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) (hna : n * a * n⁻¹ = a⁻¹) :
    ∃ K₁ K₂ : Subgroup (QAt a), CFSG.IsComponent K₁ ∧ CFSG.IsComponent K₂ ∧ K₁ ≠ K₂ ∧
      Subgroup.center K₁ = ⊥ ∧ Subgroup.center K₂ = ⊥ ∧
      (∀ x : CAt a, (x : G) = d →
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x : QAt a) ∈ K₁) ∧
      (∀ x : CAt a, (x : G) = c →
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) x : QAt a) ∈ K₂) ∧
      K₁ = ((sec11K L a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) ∧
      K₂ = (((sec11K L a).map (MulAut.conj n).toMonoidHom).subgroupOf
        (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) := by
  classical
  have hs := h.toSec11Std hT
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have haA := h.a_mem
  have hna' : n * a * n⁻¹ ∈ Subgroup.zpowers a := by
    rw [hna]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hYa : Y ∈ thetaComponentsAt 3 a := h.mem_thetaComponentsAt_Y
  have hYn : Y.map (MulAut.conj n).toMonoidHom ≠ Y :=
    hP2b G A c L a R Y hs d h.inf_eq_zpowers h.normalizer_le h.isIrreducibleOn h.isSylowOf_top
      h.not_mem_zpowers hD8 n hnW hnc hnd hna
  have hYnL : Y.map (MulAut.conj n).toMonoidHom ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_apply, TheoremO.thetaComponentsAt_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna' hna1)] at h1
  have hYK : Y = sec11K L a ⊔ inSubgroup (aschbacherSolvableCore 3) Y :=
    hP2c G A c L a R Y hs d h.inf_eq_zpowers h.normalizer_le h.isIrreducibleOn h.isSylowOf_top
      h.not_mem_zpowers hD8 n hnW hnc hnd hna
  have hKY : sec11K L a ≤ Y := h.sec11K_le
  have hKa : sec11K L a ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hnC : n ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    refine GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
    rw [map_centralizer_singleton, MulAut.conj_apply]
    exact TheoremO.centralizer_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna' hna1)
  set Kn : Subgroup G := (sec11K L a).map (MulAut.conj n).toMonoidHom with hKn
  have hKnY : Kn ≤ Y.map (MulAut.conj n).toMonoidHom := Subgroup.map_mono hKY
  have hKna : Kn ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hnC k).mp (hKa hk)
  have hsupn : Y.map (MulAut.conj n).toMonoidHom =
      Kn ⊔ inSubgroup (aschbacherSolvableCore 3) (Y.map (MulAut.conj n).toMonoidHom) := by
    conv_lhs => rw [hYK]
    rw [Subgroup.map_sup, ← map_inSubgroup_aschbacherSolvableCore]
  have hK₁eq := thetaImage_eq_map_of_eq_sup hYa hKY hKa hYK
  have hK₂eq := thetaImage_eq_map_of_eq_sup hYnL hKnY hKna hsupn
  have hL := hs.isList1016
  have hsyl1 : ∀ S : Sylow 3 ↥(thetaImage a Y), IsCyclic S := by
    have key : ∀ K₁ : Subgroup (QAt a), K₁ = ((sec11K L a).subgroupOf
        (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) →
        ∀ S : Sylow 3 ↥K₁, IsCyclic S := by
      intro K₁ hK₁
      subst hK₁
      exact isCyclic_sylow_three_thetaImage_K hL
    exact key _ hK₁eq
  have hsyl2 : ∀ S : Sylow 3 ↥(thetaImage a (Y.map (MulAut.conj n).toMonoidHom)), IsCyclic S := by
    have hι : ∀ x : ↥(Kn.subgroupOf (Subgroup.centralizer ({a} : Set G))),
        n⁻¹ * ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G) * n ∈ L := by
      intro x
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp x.2)
      have : n⁻¹ * ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G) * n = k := by
        rw [← hkx]
        show n⁻¹ * (n * k * n⁻¹) * n = k
        group
      rw [this]
      exact (Subgroup.mem_inf.mp (k4_sec11K_le L a hk)).1
    let ι : ↥(Kn.subgroupOf (Subgroup.centralizer ({a} : Set G))) →* ↥L :=
      MonoidHom.mk' (fun x => (⟨n⁻¹ * ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G) * n, hι x⟩ : ↥L))
        (fun x y => by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group)
    have hinj : Function.Injective ι := by
      intro x y hxy
      have h1 : n⁻¹ * ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G) * n =
          n⁻¹ * ((y : ↥(Subgroup.centralizer ({a} : Set G))) : G) * n := congrArg Subtype.val hxy
      have h2 : ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G) =
          ((y : ↥(Subgroup.centralizer ({a} : Set G))) : G) := by
        have := congrArg (fun z => n * z * n⁻¹) h1
        simpa [mul_assoc] using this
      exact Subtype.ext (Subtype.ext h2)
    have key : ∀ K₂ : Subgroup (QAt a), K₂ = (Kn.subgroupOf
        (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) →
        ∀ S : Sylow 3 ↥K₂, IsCyclic S := by
      intro K₂ hK₂
      subst hK₂
      exact isCyclic_sylow_three_image_of_embed hL ι hinj
    exact key _ hK₂eq
  have hθX : aschbacherSolvableCore 3 (QAt a) = ⊥ := aschbacherSolvableCore_quotient_eq_bot (CAt a)
  refine ⟨thetaImage a Y, thetaImage a (Y.map (MulAut.conj n).toMonoidHom),
    isComponent_thetaImage hYa, isComponent_thetaImage hYnL, ?_,
    center_eq_bot_of_component_of_cyclic_sylow hθX (isComponent_thetaImage hYa) hsyl1,
    center_eq_bot_of_component_of_cyclic_sylow hθX (isComponent_thetaImage hYnL) hsyl2,
    ?_, ?_, hK₁eq, hK₂eq⟩
  · intro heq
    exact hYn (thetaImage_injective hYnL hYa heq.symm)
  · intro x hx
    have hdK : d ∈ sec11K L a := TheoremO.mem_sec11K_d h45 hs h.inf_eq_zpowers h.not_mem_zpowers
    unfold thetaImage
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hx]
    exact hKY hdK
  · intro x hx
    have hcKn : c ∈ Kn :=
      TheoremO.mem_map_conj_sec11K_of_conj_mem_zpowers h45 hs h.inf_eq_zpowers h.not_mem_zpowers hnd
    unfold thetaImage
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hx]
    exact hKnY hcKn

end Certified

end CFSG.RankThree.PartTwo.Sec11
