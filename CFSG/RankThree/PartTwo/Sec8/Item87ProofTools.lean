module

public import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Item87Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem normal_subgroupOf_residual (M : Subgroup G) :
    ((inSubgroup perfectResidual M).subgroupOf M).Normal := by
  have h : (inSubgroup perfectResidual M).subgroupOf M = perfectResidual M := by
    rw [inSubgroup, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  rw [h]
  have := (perfect_residual_characterization (G := M)).2.1
  infer_instance

omit [Finite G] in
theorem residual_le (M : Subgroup G) : inSubgroup perfectResidual M ≤ M :=
  Subgroup.map_subtype_le _

theorem isPerfect_residual (M : Subgroup G) : Group.IsPerfect (inSubgroup perfectResidual M) := by
  have := (perfect_residual_characterization (G := M)).2.2.1
  exact Group.IsPerfect.map M.subtype

theorem isSubnormal_residual {x y : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 x) :
    ((inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {y})).subgroupOf
      (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y})).IsSubnormal := by
  set N := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} with hN
  set M := L ⊓ Subgroup.centralizer ({y} : Set G) with hM
  set K := inSubgroup perfectResidual M with hK
  obtain ⟨hLx, hL'⟩ := PartOne.mem_thetaComponentsAt_iff.mp hL
  have hMN : M ≤ N := inf_le_inf_right _ hLx
  have hKM : K ≤ M := residual_le M
  have hMsn : (M.subgroupOf N).IsSubnormal := by
    have h := hL'.2.1.comap (Subgroup.inclusion (inf_le_left : N ≤ Subgroup.centralizer {x}))
    have heq : (L.subgroupOf (Subgroup.centralizer {x})).comap
        (Subgroup.inclusion (inf_le_left : N ≤ Subgroup.centralizer {x})) = M.subgroupOf N := by
      ext z
      simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion, hM,
        Subgroup.mem_inf]
      exact ⟨fun hz => ⟨hz, z.2.2⟩, fun hz => hz.1⟩
    rwa [heq] at h
  have hKsn : ((K.subgroupOf N).subgroupOf (M.subgroupOf N)).IsSubnormal := by
    set e : M.subgroupOf N ≃* M := Subgroup.subgroupOfEquivOfLe hMN with he
    have heq : (K.subgroupOf N).subgroupOf (M.subgroupOf N) =
        (K.subgroupOf M).comap e.toMonoidHom := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      rfl
    rw [heq]
    have := normal_subgroupOf_residual M
    exact (Subgroup.Normal.comap this e.toMonoidHom).isSubnormal
  exact Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono N hKM) hKsn hMsn

theorem mem_thetaComponentsIn_residual {x y : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 x)
    (hq : IsQuasisimple (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {y}) ⧸
      aschbacherSolvableCore 3 (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {y})))) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {y}) ∈
      thetaComponentsIn (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y}) := by
  obtain ⟨hLx, -⟩ := PartOne.mem_thetaComponentsAt_iff.mp hL
  exact Sec6.mem_thetaComponentsIn_of
    ((residual_le _).trans (inf_le_inf_right _ hLx))
    (isPerfect_residual _) (isSubnormal_residual hL) hq

omit [Finite G] in
theorem ne_bot_of_mem_thetaComponentsIn {M K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    K ≠ ⊥ := by
  obtain ⟨-, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have : Nontrivial (K.subgroupOf M ⧸ aschbacherSolvableCore 3 (K.subgroupOf M)) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hK'.2.2
  rintro rfl
  have hs : Subsingleton ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  obtain ⟨u, v, huv⟩ := exists_pair_ne
    ((⊥ : Subgroup G).subgroupOf M ⧸ aschbacherSolvableCore 3 ((⊥ : Subgroup G).subgroupOf M))
  apply huv
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  rw [Subsingleton.elim u' v']

section ModTheta

variable {L K : Subgroup G}

noncomputable abbrev modThetaHom (hKL : K ≤ L) : K →* L ⧸ aschbacherSolvableCore 3 L :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL)

theorem range_modThetaHom (hKL : K ≤ L) : (modThetaHom hKL).range = imageModTheta L K := by
  rw [MonoidHom.range_comp, imageModTheta]
  congr 1
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr k.2
  · intro hz
    exact ⟨⟨z, Subgroup.mem_subgroupOf.mp hz⟩, rfl⟩

noncomputable def modThetaOnto (hKL : K ≤ L) : K →* imageModTheta L K :=
  (modThetaHom hKL).codRestrict _ fun k => by
    rw [← range_modThetaHom hKL]
    exact ⟨k, rfl⟩

theorem modThetaOnto_surjective (hKL : K ≤ L) : Function.Surjective (modThetaOnto hKL) := by
  rintro ⟨q, hq⟩
  rw [← range_modThetaHom hKL] at hq
  obtain ⟨k, rfl⟩ := hq
  exact ⟨k, rfl⟩

noncomputable def kerModThetaEmb (hKL : K ≤ L) :
    (modThetaOnto hKL).ker →* aschbacherSolvableCore 3 L where
  toFun k := ⟨Subgroup.inclusion hKL k, by
    have h1 : modThetaOnto hKL k = 1 := k.2
    have h2 := congrArg Subtype.val h1
    change QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hKL k) = 1 at h2
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem kerModThetaEmb_injective (hKL : K ≤ L) : Function.Injective (kerModThetaEmb hKL) := by
  intro u v huv
  have h := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) huv
  exact Subtype.ext (Subtype.ext h)

theorem isSolvable_ker_modThetaOnto (hKL : K ≤ L) : Group.IsSolvable (modThetaOnto hKL).ker := by
  have := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
  exact Group.isSolvable_of_isSolvable_injective (kerModThetaEmb_injective hKL)

theorem not_three_dvd_card_ker_modThetaOnto (hKL : K ≤ L) :
    ¬ 3 ∣ Nat.card (modThetaOnto hKL).ker := by
  intro h3
  apply (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  exact h3.trans (Subgroup.card_dvd_of_injective _ (kerModThetaEmb_injective hKL))

theorem isQuasisimple_quot_of_imageModTheta (hKL : K ≤ L)
    (hQ : IsQuasisimple (imageModTheta L K)) : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
  Sec14.isQuasisimple_quotient_theta_of_surjective hQ (modThetaOnto hKL)
    (modThetaOnto_surjective hKL) (isSolvable_ker_modThetaOnto hKL)
    (not_three_dvd_card_ker_modThetaOnto hKL)

theorem eq_bot_of_imageModTheta_eq_bot (hKL : K ≤ L) (hK : Group.IsPerfect K)
    (h : imageModTheta L K = ⊥) : K = ⊥ := by
  by_contra hne
  have hker : (modThetaOnto hKL).ker = ⊤ := by
    rw [eq_top_iff]
    intro k _
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hk : modThetaHom hKL k ∈ imageModTheta L K := by
      rw [← range_modThetaHom hKL]
      exact ⟨k, rfl⟩
    rw [h, Subgroup.mem_bot] at hk
    exact hk
  have hsol : Group.IsSolvable K := by
    have := isSolvable_ker_modThetaOnto hKL
    rw [hker] at this
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom) (MulEquiv.surjective _)
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  exact Group.IsPerfect.not_isSolvable K hsol

theorem nonempty_quot_mulEquiv_imageModTheta (hKL : K ≤ L)
    (hθ : ∀ N : Subgroup (imageModTheta L K), N.Normal → Group.IsSolvable N →
      ¬ 3 ∣ Nat.card N → N = ⊥) :
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* imageModTheta L K) := by
  obtain ⟨hθs, -, hθ3, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set ρ := modThetaOnto hKL with hρ
  have hρs : Function.Surjective ρ := modThetaOnto_surjective hKL
  have hkθ : ρ.ker ≤ aschbacherSolvableCore 3 K :=
    hθmax _ (MonoidHom.normal_ker ρ) (isSolvable_ker_modThetaOnto hKL)
      (not_three_dvd_card_ker_modThetaOnto hKL)
  set M := (aschbacherSolvableCore 3 K).map ρ with hM
  have hMn : M.Normal := by
    have : (aschbacherSolvableCore 3 K).Normal := inferInstance
    exact this.map ρ hρs
  have hMs : Group.IsSolvable M := by
    have := hθs
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h3 =>
    hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hM1 : M = ⊥ := hθ M hMn hMs hM3
  have hker : ρ.ker = aschbacherSolvableCore 3 K := by
    refine le_antisymm hkθ ?_
    intro k hk
    rw [MonoidHom.mem_ker]
    have : ρ k ∈ M := Subgroup.mem_map_of_mem ρ hk
    rwa [hM1, Subgroup.mem_bot] at this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)⟩

end ModTheta

omit [Finite G] in
theorem isElemAbelian_subgroupOf {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (D : Subgroup G) : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf D) :=
  CFSG.Open.IsElemAbelian.subgroupOf hA D

omit [Finite G] in
theorem le_centralizer_of_isElemAbelian {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {x : G} (hxA : x ∈ A) : A ≤ Subgroup.centralizer ({x} : Set G) := fun u hu =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨x, hxA⟩))

theorem exists_mem_thetaComponentsAt_of_mem_inf (h48 : Sec4.Item4_8) (hG : TheoremFourHyp G)
    {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {x y : G} (hxA : x ∈ A) (hyA : y ∈ A)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) {Z : Subgroup G}
    (hZ : Z ∈ thetaComponentsIn (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y})) :
    ∃ Y ∈ thetaComponentsAt 3 x, Z ≤ Y := by
  set D := Subgroup.centralizer ({x} : Set G) with hD
  have hS4 : SectionFourHyp D := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hx1)
  have hAD : A ≤ D := le_centralizer_of_isElemAbelian hA hxA
  set y' : D := ⟨y, hAD hyA⟩ with hy'
  set Z₂ := Subgroup.centralizer ({y'} : Set D) with hZ₂
  set CB := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} with hCB
  have hZ₂map : Z₂.map D.subtype = CB :=
    GroupTheory.SteinbergBY.map_subtype_centralizer_singleton D y'
  obtain ⟨hZCB, hZ'⟩ := mem_thetaComponentsIn_iff.mp hZ
  let ψ : CB ≃* Z₂ := (MulEquiv.subgroupCongr hZ₂map.symm).trans
    (Z₂.equivMapOfInjective D.subtype D.subtype_injective).symm
  have hψ : (D.subtype.comp Z₂.subtype).comp ψ.toMonoidHom = CB.subtype := by
    ext z
    have h1 := (Z₂.equivMapOfInjective D.subtype D.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hZ₂map.symm z)
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  set T₂ := (Z.subgroupOf CB).map ψ.toMonoidHom with hT₂
  have hT₂mem : T₂ ∈ thetaComponents 3 Z₂ := map_mulEquiv_mem_thetaComponents Nat.prime_three ψ hZ'
  set Z' := T₂.map Z₂.subtype with hZ'
  have hZ'at : Z' ∈ thetaComponentsAt 3 y' := ⟨T₂, hT₂mem, rfl⟩
  have hZ'map : Z'.map D.subtype = Z := by
    rw [hZ', hT₂, Subgroup.map_map, Subgroup.map_map, hψ, Subgroup.map_subgroupOf_eq_of_le hZCB]
  have hA'card : ∃ n : ℕ, 3 ≤ n ∧ Nat.card (A.subgroupOf D) = 3 ^ n := by
    obtain ⟨n, hn, hcard⟩ := hAn
    exact ⟨n, hn, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv, hcard]⟩
  have hy'1 : y' ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
  obtain ⟨X₀, hX₀, hZ'X₀⟩ := h48 D hS4 (A.subgroupOf D) (isElemAbelian_subgroupOf hA D) hA'card
    y' (Subgroup.mem_subgroupOf.mpr hyA) hy'1 Z' hZ'at
  refine ⟨X₀.map D.subtype, ⟨X₀, hX₀, rfl⟩, ?_⟩
  rw [← hZ'map]
  exact Subgroup.map_mono hZ'X₀

theorem eq_of_not_commutator_le {x : G} {Y₁ Y₂ I J : Subgroup G}
    (hY₁ : Y₁ ∈ thetaComponentsAt 3 x) (hY₂ : Y₂ ∈ thetaComponentsAt 3 x) (hI : I ≤ Y₁)
    (hJ : J ≤ Y₂)
    (hIJ : ¬ ⁅I, J⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {x})) :
    Y₁ = Y₂ := by
  by_contra hne
  apply hIJ
  set H := Subgroup.centralizer ({x} : Set G) with hH
  obtain ⟨Y₁', hY₁', rfl⟩ := hY₁
  obtain ⟨Y₂', hY₂', rfl⟩ := hY₂
  have hne' : Y₁' ≠ Y₂' := fun h => hne (by rw [h])
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hK₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three hY₁'
  have hK₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three hY₂'
  have hKne : Y₁'.map π ≠ Y₂'.map π := fun h => hne' (hbij.injOn hY₁' hY₂' h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  have hle : ⁅Y₁', Y₂'⁆ ≤ aschbacherSolvableCore 3 H := by
    have h := Subgroup.map_commutator Y₁' Y₂' π
    rw [hcomm] at h
    have h' := (Subgroup.map_eq_bot_iff _).mp h
    rwa [QuotientGroup.ker_mk'] at h'
  calc ⁅I, J⁆ ≤ ⁅Y₁'.map H.subtype, Y₂'.map H.subtype⁆ := Subgroup.commutator_mono hI hJ
    _ = ⁅Y₁', Y₂'⁆.map H.subtype := (Subgroup.map_commutator _ _ _).symm
    _ ≤ (aschbacherSolvableCore 3 H).map H.subtype := Subgroup.map_mono hle

end Item87Proof

end CFSG.RankThree.PartTwo.Sec8
