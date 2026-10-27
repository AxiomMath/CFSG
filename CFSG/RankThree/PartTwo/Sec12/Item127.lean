module

public import CFSG.RankThree.PartTwo.KFacts.KS127Exc
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec12.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Gap127Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdE G A c L → ∀ b ∈ A ⊓ Subgroup.centralizer (L : Set G), b ≠ 1 →
      ∀ K ∈ thetaComponentsAt 3 b,
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ K →
          (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
              inSubgroup (aschbacherSolvableCore 3) K = K ∨
            (Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∧
              Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2)) ∨
            ∃ q : TauCeti.PrimePower,
              Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card ∧
                (Sec4.IsoGTwo (K ⧸ CFSG.pCore 2 K) q ∨
                  ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
                    Nonempty (K ⧸ CFSG.pCore 2 K ≃*
                      (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)))

@[expose] def Gap127FieldGraph : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdE G A c L → ∀ b ∈ A ⊓ Subgroup.centralizer (L : Set G), b ≠ 1 →
      ∀ K ∈ thetaComponentsAt 3 b,
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ K →
        (∃ q : TauCeti.PrimePower,
          Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card ∧
            (Sec4.IsoGTwo (K ⧸ CFSG.pCore 2 K) q ∨
              ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
                Nonempty (K ⧸ CFSG.pCore 2 K ≃*
                  (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))) →
        ∀ a ∈ A, a ≠ 1 →
          ¬ (KFacts.InducesStdKind K a .field ∨ KFacts.InducesStdKind K a .graphField)

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_theta_of_ne {b : G} {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ thetaComponentsAt 3 b) (h₂ : K₂ ∈ thetaComponentsAt 3 b) (hne : K₁ ≠ K₂)
    {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₂) :
    x * y * x⁻¹ * y⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨K₁', hK₁', rfl⟩ := h₁
  obtain ⟨K₂', hK₂', rfl⟩ := h₂
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence
    (H := Subgroup.centralizer ({b} : Set G)) Nat.prime_three
  set π := QuotientGroup.mk'
    (aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G))) with hπ
  have hne' : K₁' ≠ K₂' := fun h => hne (h ▸ rfl)
  have hJne : K₁'.map π ≠ K₂'.map π := fun h => hne' (hbij.injOn hK₁' hK₂' h)
  have hcomm := (LocalCores.distinct_components_commute
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁')
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hK₂')).resolve_left hJne
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h1 : π y' * π x' = π x' * π y' :=
    Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hx')) _
      (Subgroup.mem_map_of_mem π hy')
  have h2 : π (x' * y' * x'⁻¹ * y'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem mem_thetaQuotCentralizer_of_ne {b : G} {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ thetaComponentsAt 3 b) (h₂ : K₂ ∈ thetaComponentsAt 3 b) (hne : K₁ ≠ K₂)
    {x : G} (hx : x ∈ K₁) (hxN : x ∈ Subgroup.normalizer (K₂ : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer K₂ := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun l hl => ?_⟩
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt h₂]
  refine ⟨K₂.mul_mem (K₂.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl), ?_⟩
  have hlC : l⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    inv_mem (Sec6.le_centralizer_of_mem_thetaComponentsAt h₂ hl)
  have h1 := Sec13.conj_mem_inSubgroup_theta hlC (commutator_mem_theta_of_ne h₁ h₂ hne hx hl)
  have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
  rwa [e] at h1

theorem mem_thetaQuotCentralizer_of_sup_eq {L K : Subgroup G} (hLK : L ≤ K)
    (hsup : L ⊔ inSubgroup (aschbacherSolvableCore 3) K = K) {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hxL : x ∈ Subgroup.centralizer (L : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer K := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun k hk => ?_⟩
  have hLN : L ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) : Set G) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun g hg => Sec13.conj_mem_inSubgroup_theta (hLK hl) hg
  have hk' : k ∈ ((L ⊔ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) : Set G) := by
    rw [hsup]
    exact hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hk'
  obtain ⟨l, hl, n, hn, rfl⟩ := hk'
  have hxl : x * l = l * x := (Subgroup.mem_centralizer_iff.mp hxL l hl).symm
  have h1 := conj_mem_inSubgroup_theta hxN hn
  have e : (l * n)⁻¹ * (x * (l * n) * x⁻¹) = n⁻¹ * (x * n * x⁻¹) := by
    calc (l * n)⁻¹ * (x * (l * n) * x⁻¹) = n⁻¹ * l⁻¹ * ((x * l) * n * x⁻¹) := by group
      _ = n⁻¹ * l⁻¹ * ((l * x) * n * x⁻¹) := by rw [hxl]
      _ = n⁻¹ * (x * n * x⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) h1

theorem sec12StdE_centralizer_setup {A L : Subgroup G} {c : G} (h : Sec12StdE G A c L) {b : G}
    (hbA : b ∈ A) (hb1 : b ≠ 1) :
    SectionFourHyp (Subgroup.centralizer ({b} : Set G)) ∧
      A ≤ Subgroup.centralizer ({b} : Set G) ∧
      Maximal (fun B : Subgroup (Subgroup.centralizer ({b} : Set G)) =>
        CFSG.Assembly.IsElemAbelian 3 B) (A.subgroupOf (Subgroup.centralizer ({b} : Set G))) ∧
      Nat.card (A.subgroupOf (Subgroup.centralizer ({b} : Set G))) = 27 := by
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ h.mem_partTwoE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := h.isE27.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha b hbA)
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hbZ : b ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases h.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hbZ
      exact hb1 hbZ
    · obtain ⟨x, y, hxy⟩ := h.nonabelian
      exact hxy (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top y) x)
  have hS4 : SectionFourHyp C := h.toTheoremFourHyp.sectionFourHyp hCtop
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 27 := by
    rw [← h27, ← hA'map, Subgroup.card_map_of_injective C.subtype_injective]
  refine ⟨hS4, hAC, ⟨hA'e, fun B hB hAB => ?_⟩, h27'⟩
  have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := x
      obtain ⟨_, y, hy, rfl⟩ := y
      apply Subtype.ext
      change (x : G) * y = y * x
      exact congrArg Subtype.val (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hB.2 x hx)
  have hAB' : A ≤ B.map C.subtype := fun a ha =>
    ⟨⟨a, hAC ha⟩, hAB (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hBA := hAF.2.1 _ hBe hAB'
  intro x hx
  have : (x : G) ∈ A := hBA ▸ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr this

theorem exists_of_not_starConditionAt (h45 : Sec4.Item4_5) (h422 : Sec4.Item4_22)
    {A L : Subgroup G} {c : G} (h : Sec12StdE G A c L) {b : G}
    (hbB : b ∈ A ⊓ Subgroup.centralizer (L : Set G)) (hb1 : b ≠ 1) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 b) (hLK : L ≤ K) (hstar : ¬ StarConditionAt A b) :
    ∃ K₀ ∈ thetaComponents 3 (Subgroup.centralizer ({b} : Set G)),
      K₀.map (Subgroup.centralizer ({b} : Set G)).subtype = K ∧
      Nat.card (Sec4.autThetaQuot (A.subgroupOf (Subgroup.centralizer ({b} : Set G))) K₀) = 9 ∧
      thetaAlpha 3
        ((Sec4.autThetaQuot (A.subgroupOf (Subgroup.centralizer ({b} : Set G))) K₀).subgroupOf
          (Sec4.autThetaQuot ⊤ K₀)) ≠ ⊥ ∧
      A ≤ Subgroup.normalizer (K : Set G) ∧
      Nat.card (A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) = 3 := by
  obtain ⟨hS4, hAC, hmax, h27'⟩ := sec12StdE_centralizer_setup h hbB.1 hb1
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  set A' := A.subgroupOf C with hA'def
  have h27 : Nat.card A = 27 := h.isE27.2
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  set b' : C := ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hb'def
  have hb'A : b' ∈ A' := Subgroup.mem_subgroupOf.mpr hbB.1
  have hb'Z : b' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  rcases h422 C hS4 A' hmax h27' b' hb'A hb'Z hb'1 with h1 | ⟨K', hK', h9, hα⟩
  · exact absurd h1 hstar
  set K'G := K'.map C.subtype with hK'Gdef
  have hK'G : K'G ∈ thetaComponentsAt 3 b := ⟨K', hK', rfl⟩
  have hA'e := hmax.1
  have hA'N : A' ≤ Subgroup.normalizer (K' : Set C) :=
    h45 C hS4 A' (fun x => ⟨1, Subtype.ext (by simpa using hA'e.2 x x.2)⟩)
      (Or.inr ⟨hA'e, 3, le_rfl, by rw [h27']; norm_num⟩) K' hK'
  have hAN : A ≤ Subgroup.normalizer (K'G : Set G) := by
    intro a ha
    have hmem : (⟨a, hAC ha⟩ : C) ∈ A' := Subgroup.mem_subgroupOf.mpr ha
    exact (Sec13.coe_mem_normalizer_map_iff C).mpr (hA'N hmem)
  have hAut : Nat.card (Sec4.autThetaQuot A K'G) = 9 := by
    rw [← hA'map, hK'Gdef, ← Sec13.map_autThetaQuot_sub C A' K',
      Subgroup.card_map_of_injective (MulAut.congr (Sec13.thetaQuotEquivSub C K')).injective, h9]
  have h3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer K'G : Subgroup G) = 3 := by
    have := Sec13.card_inf_mul_card_autThetaQuot hAN
    rw [hAut, h27] at this
    omega
  have hKeq : K'G = K := by
    by_contra hne
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
    have hcA : c ∈ A ⊓ Sec4.thetaQuotCentralizer K'G :=
      ⟨h.mem_A, mem_thetaQuotCentralizer_of_ne hK hK'G (Ne.symm hne) (hLK h.mem_L)
        (hAN h.mem_A)⟩
    have hzc : A ⊓ Sec4.thetaQuotCentralizer K'G = Subgroup.zpowers c := by
      have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one
      exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcA)
        (by rw [h3, Nat.card_zpowers, hc3])).symm
    have hALc : A ⊓ L ≤ Subgroup.zpowers c := by
      rw [← hzc]
      intro x hx
      exact ⟨hx.1, mem_thetaQuotCentralizer_of_ne hK hK'G (Ne.symm hne) (hLK hx.2)
        (hAN hx.1)⟩
    have hcB : c ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨h.mem_A, Subgroup.mem_centralizer_iff.mpr fun l hl =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))⟩
    have hAB : A ⊓ Subgroup.centralizer (L : Set G) ⊔ A ⊓ L ≤
        A ⊓ Subgroup.centralizer (L : Set G) :=
      sup_le le_rfl (hALc.trans (Subgroup.zpowers_le.mpr hcB))
    rw [h.sup_eq] at hAB
    have hcard := Subgroup.card_le_of_le hAB
    rw [h27, h.card_B] at hcard
    norm_num at hcard
  refine ⟨K', hK', hKeq, h9, hα, hKeq ▸ hAN, hKeq ▸ h3⟩

theorem item127_of (hG2 : Gap127Two) (h45 : Sec4.Item4_5) (h422 : Sec4.Item4_22)
    (h423 : Sec4.Item4_23) (hKN : KFacts.KS127NotIn423) (hFG : Gap127FieldGraph) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec12StdE G A c L → ∀ b ∈ A ⊓ Subgroup.centralizer (L : Set G), b ≠ 1 →
        ∀ K ∈ thetaComponentsAt 3 b,
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ K →
            ((Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
                Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6))) ∨
              StarConditionAt A b) ∧
            (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
                inSubgroup (aschbacherSolvableCore 3) K = K ∨
              (Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∧
                Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2)) ∨
              ∃ q : TauCeti.PrimePower,
                Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card ∧
                  (Sec4.IsoGTwo (K ⧸ CFSG.pCore 2 K) q ∨
                    ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
                      Nonempty (K ⧸ CFSG.pCore 2 K ≃*
                        (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))) := by
  intro G _ _ A c L h b hbB hb1 K hK hLK
  have h2 := hG2 G A c L h b hbB hb1 K hK hLK
  refine ⟨?_, h2⟩
  have hL := h.mem_thetaComponentsAt
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) = L :=
    inf_eq_left.mpr fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hbB.2 l hl)
  have hLres : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) = L := by
    rw [hLb]
    exact inSubgroup_perfectResidual_of_isPerfect (Sec6.isPerfect_of_mem_thetaComponentsAt hL)
  have hLK' : L ≤ K := hLres ▸ hLK
  rcases h2 with hi | hii | hiii
  ·
    right
    by_contra hstar
    obtain ⟨K₀, -, -, -, -, hAN, h3⟩ :=
      exists_of_not_starConditionAt h45 h422 h hbB hb1 hK hLK' hstar
    rw [hLres] at hi
    have hB : A ⊓ Subgroup.centralizer (L : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer K :=
      fun x hx => ⟨hx.1, mem_thetaQuotCentralizer_of_sup_eq hLK' hi (hAN hx.1) hx.2⟩
    have hcard := Subgroup.card_le_of_le hB
    rw [h.card_B, h3] at hcard
    norm_num at hcard
  · exact Or.inl ⟨hii.2, hii.1⟩
  ·
    right
    by_contra hstar
    obtain ⟨hS4, -, hmax, h27'⟩ := sec12StdE_centralizer_setup h hbB.1 hb1
    obtain ⟨K₀, hK₀, hKeq, h9, hα, -, -⟩ :=
      exists_of_not_starConditionAt h45 h422 h hbB hb1 hK hLK' hstar
    have hb'A : (⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({b} : Set G)) ∈
        A.subgroupOf (Subgroup.centralizer ({b} : Set G)) :=
      Subgroup.mem_subgroupOf.mpr hbB.1
    have hb'Z : (⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({b} : Set G)) ∈
        Subgroup.center (Subgroup.centralizer ({b} : Set G)) :=
      Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
    have hb'1 : (⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({b} : Set G)) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
    have hq : ∃ q : TauCeti.PrimePower, Sec4.IsoGTwo (K₀ ⧸ CFSG.pCore 2 K₀) q ∨
        ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
          Nonempty (K₀ ⧸ CFSG.pCore 2 K₀ ≃*
            (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) := by
      obtain ⟨q, -, hq⟩ := hiii
      let e := K₀.equivMapOfInjective _ (Subgroup.centralizer ({b} : Set G)).subtype_injective
      let e' : K₀ ⧸ CFSG.pCore 2 K₀ ≃* K ⧸ CFSG.pCore 2 K :=
        (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).trans
          (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hKeq)
            (CFSG.pCore_map_iso 2 (MulEquiv.subgroupCongr hKeq)))
      refine ⟨q, ?_⟩
      rcases hq with ⟨hv, ⟨φ⟩⟩ | ⟨hv, ⟨φ⟩⟩
      · exact Or.inl ⟨hv, ⟨e'.trans φ⟩⟩
      · exact Or.inr ⟨hv, ⟨e'.trans φ⟩⟩
    have hKN' := hKN _ (A.subgroupOf (Subgroup.centralizer ({b} : Set G))) K₀ hK₀ hq
    rcases h423 _ hS4 _ hmax h27' _ hb'A hb'Z hb'1 K₀ hK₀ h9 hα with
      a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8
    · exact hKN' (Or.inl a1)
    · exact hKN' (Or.inr (Or.inl a2))
    · exact hKN' (Or.inr (Or.inr (Or.inl a3)))
    · exact hKN' (Or.inr (Or.inr (Or.inr (Or.inl a4))))
    · exact hKN' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a5)))))
    · exact hKN' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a6))))))
    · exact hKN' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr a7))))))
    · obtain ⟨a, haA, ha1, hk⟩ := a8
      have haA' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp haA
      have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
      refine hFG G A c L h b hbB hb1 K hK hLK hiii (a : G) haA' ha1' ?_
      rw [← hKeq]
      rcases hk with hk | hk
      · exact Or.inl (Sec13.inducesStdKind_sub _ K₀ hk)
      · exact Or.inr (Sec13.inducesStdKind_sub _ K₀ hk)

end CFSG.RankThree.PartTwo.Sec12
