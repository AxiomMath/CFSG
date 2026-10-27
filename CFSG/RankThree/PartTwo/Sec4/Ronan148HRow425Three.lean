module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LNA

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)

section Gen

theorem isSLThreePiAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {q : ℕ}
    (h : IsSLThreePiAt Y q) : IsSLThreePiAt X q := by
  obtain ⟨F, _, _, ⟨hF, hq, ⟨f⟩⟩ | ⟨hF, hq, ⟨f⟩⟩⟩ := h
  · exact ⟨F, inferInstance, inferInstance, Or.inl ⟨hF, hq, ⟨e.trans f⟩⟩⟩
  · exact ⟨F, inferInstance, inferInstance, Or.inr ⟨hF, hq, ⟨e.trans f⟩⟩⟩

variable {G : Type} [Group G]

theorem eq_of_le_of_isQuasisimple {J N C : Subgroup G} (hJN : J ≤ N) (hNC : N ≤ C)
    (hsub : (J.subgroupOf C).IsSubnormal) (hN : CFSG.IsQuasisimple ↥N)
    (hJ : CFSG.IsQuasisimple ↥J) : J = N := by
  have hsN : (J.subgroupOf N).IsSubnormal := by
    have h := hsub.comap (Subgroup.inclusion hNC)
    have heq : (J.subgroupOf C).comap (Subgroup.inclusion hNC) = J.subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsN with h | h
  · refine le_antisymm hJN fun x hx => ?_
    have : (⟨x, hx⟩ : ↥N) ∈ J.subgroupOf N := h ▸ Subgroup.mem_top _
    exact this
  · exfalso
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hJ
    have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1
    have hab : ⁅J, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyZ : (⟨y, hJN hy⟩ : ↥N) ∈ Subgroup.center ↥N := h hy
      exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hyZ) ⟨x, hJN hx⟩)).symm
    rw [hperf] at hab
    rw [hab] at hnt
    obtain ⟨a, b, hab'⟩ := hnt
    exact hab' (Subsingleton.elim a b)

theorem le_of_commutators_mem {J N : Subgroup G} {z : G}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set G)) (hJ : ⁅J, J⁆ = J)
    (hN : ∀ a ∈ Subgroup.centralizer ({z} : Set G), ∀ b ∈ Subgroup.centralizer ({z} : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ N) : J ≤ N := by
  rw [← hJ, Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact hN x (hJC hx) y (hJC hy)

end Gen

section Model

variable {G : Type} [Group G] [Finite G]

theorem exists_model_component {L : Subgroup G} {c : G} (hcL : c ∈ L)
    {K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)} (hK : IsComponent K)
    {K' : Subgroup G} (hK' : K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype) (hcK : c ∈ K')
    {C : Type} [Group C] (ψ : L ≃* C) :
    ∃ J : Subgroup C, J ≤ Subgroup.centralizer ({ψ ⟨c, hcL⟩} : Set C) ∧
      CFSG.IsQuasisimple J ∧
      (J.subgroupOf (Subgroup.centralizer ({ψ ⟨c, hcL⟩} : Set C))).IsSubnormal ∧
      ψ ⟨c, hcL⟩ ∈ J ∧ Nonempty (K ≃* J) := by
  set z : C := ψ ⟨c, hcL⟩ with hz
  set CZ := Subgroup.centralizer ({z} : Set C) with hCZ
  let θ : (L ⊓ Subgroup.centralizer {c} : Subgroup G) →* C :=
    ψ.toMonoidHom.comp (Subgroup.inclusion (inf_le_left : (L ⊓ Subgroup.centralizer {c} :
      Subgroup G) ≤ L))
  have hθ : ∀ x : (L ⊓ Subgroup.centralizer {c} : Subgroup G), θ x = ψ ⟨(x : G), x.2.1⟩ :=
    fun x => rfl
  have hθinj : Function.Injective θ :=
    ψ.injective.comp (Subgroup.inclusion_injective _)
  have hθC : ∀ x : (L ⊓ Subgroup.centralizer {c} : Subgroup G), θ x ∈ CZ := by
    intro x
    rw [hCZ, Subgroup.mem_centralizer_singleton_iff, hθ, hz, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.2.2
  let θ' : (L ⊓ Subgroup.centralizer {c} : Subgroup G) →* CZ := θ.codRestrict CZ hθC
  have hθ'surj : Function.Surjective θ' := by
    rintro ⟨y, hy⟩
    set l := ψ.symm y with hl
    have hly : ψ l = y := MulEquiv.apply_symm_apply ψ y
    have hlc : (l : G) ∈ Subgroup.centralizer {c} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      rw [← hly, hz, ← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (ψ.injective h1)
    refine ⟨⟨l, l.2, hlc⟩, Subtype.ext ?_⟩
    change θ ⟨l, l.2, hlc⟩ = y
    rw [hθ, ← hly]
  set J : Subgroup C := K.map θ with hJ
  have hJK : K' ≤ (L ⊓ Subgroup.centralizer {c} : Subgroup G) :=
    hK' ▸ Subgroup.map_subtype_le K
  have hJC : J ≤ CZ := by
    rintro _ ⟨x, -, rfl⟩
    exact hθC x
  have eKJ : K ≃* J := K.equivMapOfInjective θ hθinj
  have hJs : (J.subgroupOf CZ).IsSubnormal := by
    have h := hK.2.map hθ'surj
    have heq : K.map θ' = J.subgroupOf CZ := by
      ext ⟨y, hy⟩
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, ?_⟩
        have := congrArg Subtype.val hxy
        exact this
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
    rwa [heq] at h
  have hzJ : z ∈ J := by
    have hcM : c ∈ (L ⊓ Subgroup.centralizer {c} : Subgroup G) := hJK hcK
    refine ⟨⟨c, hcM⟩, ?_, rfl⟩
    rw [hK'] at hcK
    obtain ⟨x, hx, hxc⟩ := hcK
    have : x = ⟨c, hcM⟩ := Subtype.ext hxc
    rw [← this]
    exact hx
  exact ⟨J, hJC, CFSG.LocalCores.isQuasisimple_of_mulEquiv eKJ hK.1, hJs, hzJ, ⟨eKJ⟩⟩

theorem row425_of_three {S C : Type} [Group S] [Group C] (eSC : S ≃* C) (h3 : NoThreeCover S)
    {p f : ℕ}
    (hmodel : ∀ (X : Type) [Group X], Nonempty (X ≃* S) →
      Blueprint.ChevalleyExceptionalModel X .G2 p f ∨
        Blueprint.ChevalleyExceptionalModel X .trialityD4 p f)
    (hJ : ∀ z : C, z ^ 3 = 1 → z ≠ 1 → ∀ J : Subgroup C,
      J ≤ Subgroup.centralizer ({z} : Set C) → CFSG.IsQuasisimple J →
      (J.subgroupOf (Subgroup.centralizer ({z} : Set C))).IsSubnormal → z ∈ J →
      IsSLThreePiAt J (p ^ f)) :
    Row425 S := by
  intro G _ _ _ A hA _ hθ L hL ⟨eL⟩ c hLc K hK K' hK' _ hAZ _
  have hcmem : c ∈ A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) :=
    hAZ ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcmem.1
  have hcK : c ∈ K' := hcmem.2.1
  have hK'L : K' ≤ L := (hK' ▸ Subgroup.map_subtype_le K).trans inf_le_left
  have hcL : c ∈ L := hK'L hcK
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hLc fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hZ : Subgroup.center L = ⊥ := Ronan148L.center_eq_bot_of_noThreeCover h3 hθ hL eL
  let φ : L ≃* S := (RonanK429.quotCenterEquivOfEqBot hZ).trans eL
  let ψ : L ≃* C := φ.trans eSC
  obtain ⟨J, hJC, hJq, hJs, hzJ, ⟨eKJ⟩⟩ := exists_model_component hcL hK hK' hcK ψ
  have hz3 : ψ ⟨c, hcL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hz1 : ψ ⟨c, hcL⟩ ≠ 1 := by
    rw [Ne, map_eq_one_iff _ ψ.injective]
    exact fun h => hc1 (congrArg Subtype.val h)
  exact Or.inr (Or.inl ⟨p, f, isSLThreePiAt_of_mulEquiv eKJ (hJ _ hz3 hz1 J hJC hJq hJs hzJ),
    hmodel L ⟨φ⟩⟩)

end Model

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
