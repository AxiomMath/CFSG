module

public import CFSG.Quasithin.Background.C2Thirteen
public import CFSG.Quasithin.Background.C1PackC129Case

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace C2ThirteenStep

variable {G : Type} [Group G]

theorem oTwoFIn_le_oTwoFstarIn (H : Subgroup G) : oTwoFIn H ≤ oTwoFstarIn H := by
  unfold oTwoFIn oTwoFstarIn preimageModTwoCore
  exact Subgroup.map_mono (Subgroup.comap_mono le_sup_left)

theorem oTwoFstarIn_subgroupOf (H : Subgroup G) : (oTwoFstarIn H).subgroupOf H =
    (CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  unfold oTwoFstarIn preimageModTwoCore Subgroup.subgroupOf
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem oTwoFstarIn_le (H : Subgroup G) : oTwoFstarIn H ≤ H := Subgroup.map_subtype_le _

theorem le_normalizer_oTwoFstarIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oTwoFstarIn H : Set G) := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoFstarIn_le H)).mp ?_
  rw [oTwoFstarIn_subgroupOf]
  exact Subgroup.Normal.comap (CFSG.LocalCores.generalized_fitting_characteristic.2) _

theorem subgroupOf_perfect {L H : Subgroup G} (hLH : L ≤ H) (hL : ⁅L, L⁆ = L) :
    ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH, hL]

variable [Finite G]

theorem commutator_commutator_le_pCoreOf {H M L : Subgroup G} (hMH : M ≤ H)
    (hNM : oTwoFIn H ≤ M) (hL : L ∈ cComp M)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ⁅⁅L, oTwoFIn H⁆, L⁆ ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := oTwoFIn H with hNdef
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hLH : L ≤ H := hLM.trans hMH
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := hLH.trans C2Six.le_normalizer_oTwoFIn
  have hNs : Group.IsSolvable ↥N := isSolvable_oTwoFIn H
  have h3 : ⁅L, N⁆ ≤ L := (cComp_commutator_perfectCore hL hNM hNs hLN).1
  have h3' : ⁅L, N⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_right.mp hLN
  set D := L ⊓ N with hDdef
  have hDL : D ≤ L := inf_le_left
  have hLD : L ≤ Subgroup.normalizer (D : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hLN hl⟩
  have hDs : Group.IsSolvable ↥D :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_right : D ≤ N)) (Subgroup.inclusion_injective _)
  have hDLO : ⁅D, L⁆ ≤ pCoreOf 2 L := by
    set φ : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ
    set D' : Subgroup ↥L := D.subgroupOf L with hD'
    have hD'n : D'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr hLD
    have hmapn : (D'.map φ).Normal := hD'n.map φ (QuotientGroup.mk'_surjective _)
    have hcen : D'.map φ ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hmapn with htop | hc
      · exfalso
        have hD's : Group.IsSolvable ↥D' :=
          Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.subgroupOfEquivOfLe hDL).toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe hDL).injective
        have hims : Group.IsSolvable ↥(D'.map φ) :=
          Group.isSolvable_of_surjective (φ.subgroupMap_surjective D')
        have htops : Group.IsSolvable (↥L ⧸ CFSG.pCore 2 ↥L) := by
          rw [htop] at hims
          exact Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.topEquiv).symm.toMonoidHom) (MulEquiv.injective _)
        have : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := CFSG.LocalCores.isQuasisimple_nontrivial hq
        have : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := hq.1
        exact Group.IsPerfect.not_isSolvable _ htops
      · exact hc
    rw [Subgroup.commutator_le]
    intro d hd l hl
    have hdD' : (⟨d, hDL hd⟩ : ↥L) ∈ D' := hd
    have hcd : φ ⟨d, hDL hd⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      hcen ⟨_, hdD', rfl⟩
    have hker : ⁅(⟨d, hDL hd⟩ : ↥L), (⟨l, hl⟩ : ↥L)⁆ ∈ CFSG.pCore 2 ↥L := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change φ ⁅(⟨d, hDL hd⟩ : ↥L), (⟨l, hl⟩ : ↥L)⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcd (φ ⟨l, hl⟩)).symm
    exact C2Six.mem_pCore_two_iff.mp hker
  have hle1 : ⁅⁅L, N⁆, L⁆ ≤ pCoreOf 2 L :=
    (Subgroup.commutator_mono (le_inf h3 h3') le_rfl).trans hDLO
  have hle2 : ⁅⁅L, N⁆, L⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono_right h3').trans h3'
  intro x hx
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L) ⟨x, hle1 hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact C2Six.mem_pCoreOf_of_pow_eq_one (hle2 hx) hk'

theorem commutator_layer_eq_bot {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hs : Group.IsSolvable ↥⁅A, CFSG.generalizedFitting X⁆) : ⁅A, CFSG.layer X⁆ = ⊥ := by
  set E := CFSG.layer X with hEdef
  have hEc : E.Characteristic := CFSG.LocalCores.layer_characteristic (G := X)
  have hEn : E.Normal := inferInstance
  set S := ⁅A, E⁆ with hSdef
  have hSF : S ≤ ⁅A, CFSG.generalizedFitting X⁆ := Subgroup.commutator_mono le_rfl le_sup_right
  have hSs : Group.IsSolvable ↥S :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hSF)
      (Subgroup.inclusion_injective hSF)
  have hSE : S ≤ E := Subgroup.commutator_le_right A E
  have hES : E ≤ Subgroup.normalizer (S : Set X) := Subgroup.normalizer_commutator_ge_right A E
  have hSsub : S.IsSubnormal :=
    Subgroup.IsSubnormal.step S E hSE hEn.isSubnormal
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hSE).mpr hES)
  have h := (CFSG.LocalCores.component_solvable_centralizer hSs hSsub).2
  have hSE' : ⁅⁅A, E⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h
  have h3 : ⁅⁅E, E⁆, A⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (by rw [Subgroup.commutator_comm E A]; exact hSE') hSE'
  rw [CFSG.LocalCores.layer_perfect] at h3
  rw [hSdef, Subgroup.commutator_comm]
  exact h3

theorem commutator_fitting_eq_bot {H M L : Subgroup G} (hMH : M ≤ H) (hNM : oTwoFIn H ≤ M)
    (hL : L ∈ cComp M) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ⁅(L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)⁆ = ⊥ := by
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set F := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hFdef
  set L' := L.subgroupOf H with hL'
  set N' := (oTwoFIn H).subgroupOf H with hN'
  have hLH : L ≤ H := (le_of_mem_cComp hL).trans hMH
  have hNmap : N'.map π = F := by
    rw [hN', C2Six.oTwoFIn_subgroupOf]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hLmap : L'.map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hNmap' : N'.map H.subtype = oTwoFIn H := Subgroup.map_subgroupOf_eq_of_le C2Six.oTwoFIn_le
  have hcc := commutator_commutator_le_pCoreOf hMH hNM hL hq
  have h1 : ⁅⁅L', N'⁆, L'⁆ ≤ CFSG.pCore 2 ↥H := by
    intro y hy
    have hy' : (y : G) ∈ ⁅⁅L, oTwoFIn H⁆, L⁆ := by
      rw [← hLmap, ← hNmap', ← Subgroup.map_commutator, ← Subgroup.map_commutator]
      exact ⟨y, hy, rfl⟩
    exact C2Six.mem_pCore_two_iff.mpr (hcc hy')
  have h2 : ⁅⁅L'.map π, F⁆, L'.map π⁆ = ⊥ := by
    rw [← hNmap, ← Subgroup.map_commutator, ← Subgroup.map_commutator, eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact (QuotientGroup.eq_one_iff y).mpr (h1 hy)
  have hperf : ⁅L'.map π, L'.map π⁆ = L'.map π := by
    rw [← Subgroup.map_commutator, subgroupOf_perfect hLH (perfect_of_mem_cComp hL)]
  have h3 : ⁅⁅L'.map π, L'.map π⁆, F⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h2
      (by rw [Subgroup.commutator_comm F]; exact h2)
  rwa [hperf] at h3

theorem le_oTwoFstarIn_of_cComp {H M L : Subgroup G} (hMH : M ≤ H) (hF : oTwoFstarIn H ≤ M)
    (hL : L ∈ cComp M)
    (hLF : ⁅(L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)⁆ = ⊥) :
    L ≤ oTwoFstarIn H := by
  have hLH : L ≤ H := (le_of_mem_cComp hL).trans hMH
  rcases cComp_commutator_dichotomy_of_le hL hF with ⟨-, hs⟩ | heq
  · set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    set L' := L.subgroupOf H with hL'
    set Y' := (oTwoFstarIn H).subgroupOf H with hY'
    have hYmap : Y'.map π = CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H) := by
      rw [hY', oTwoFstarIn_subgroupOf]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have hcY : (⁅L', Y'⁆).map H.subtype = ⁅L, oTwoFstarIn H⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH,
        Subgroup.map_subgroupOf_eq_of_le (oTwoFstarIn_le H)]
    have hs1 : Group.IsSolvable ↥⁅L', Y'⁆ := by
      rw [← hcY] at hs
      exact Group.isSolvable_of_isSolvable_injective
        (f := (⁅L', Y'⁆.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
        (MulEquiv.injective _)
    have hs' : Group.IsSolvable ↥⁅L'.map π, CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)⁆ := by
      rw [← hYmap, ← Subgroup.map_commutator]
      exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
    have hE := commutator_layer_eq_bot hs'
    have hC : L'.map π ≤
        Subgroup.centralizer (CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H) : Set _) := by
      rw [Subgroup.le_centralizer_iff]
      exact sup_le
        (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLF))
        (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hE))
    have hLY := hC.trans (CFSG.centralizer_generalizedFitting_le _)
    intro x hx
    exact ⟨⟨x, hLH hx⟩, hLY ⟨⟨x, hLH hx⟩, hx, rfl⟩, rfl⟩
  · calc L ≤ conjClosure L (oTwoFstarIn H) := le_conjClosure _ _
      _ = ⁅L, oTwoFstarIn H⁆ := heq.symm
      _ ≤ oTwoFstarIn H :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp (hLH.trans (le_normalizer_oTwoFstarIn H))

theorem mem_cComp_of_isQuasisimple {H M L : Subgroup G} (hMH : M ≤ H) (hF : oTwoFstarIn H ≤ M)
    (hL : L ∈ cComp M) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : L ∈ cComp H := by
  have hLH : L ≤ H := (le_of_mem_cComp hL).trans hMH
  have hLY := le_oTwoFstarIn_of_cComp hMH hF hL
    (commutator_fitting_eq_bot hMH ((oTwoFIn_le_oTwoFstarIn H).trans hF) hL hq)
  have hYsub : IsSubnormal (oTwoFstarIn H) H :=
    IsSubnormal.step (oTwoFstarIn_le H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoFstarIn_le H)).mpr
        (le_normalizer_oTwoFstarIn H)) (IsSubnormal.refl H)
  exact cComp_mem_of_subnormal hYsub (cComp_mem_of_le hL hLY hF)

end C2ThirteenStep

variable {G : Type} [Group G] [Finite G]

theorem asc213Step_of_isQuasisimple {H R M L V : Subgroup G} (h : HypC28 H R M L V)
    (hF : oTwoFstarIn H ≤ M) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : L ∈ cComp H :=
  C2ThirteenStep.mem_cComp_of_isQuasisimple h.le_H hF h.comp hq

@[expose] def ASC213StepNonQ (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V : Subgroup G, HypC28 H R M L V → oTwoFstarIn H ≤ M →
    ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → L ∈ cComp H

theorem asc213Step_of_nonQ (hN : ASC213StepNonQ G) : ASC213Step G := by
  intro H R M L V h hF
  by_cases hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  · exact asc213Step_of_isQuasisimple h hF hq
  · exact hN H R M L V h hF hq

section C213

variable {H R M L V T : Subgroup G}

theorem c2_13_of_mem (hC129 : ASC129Statement G) (hC111 : ASC111Statement G)
    (hC19 : ASC19Statement G) (hA3 : A3Orbits G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M)
    (hRT : R ≤ T) (hL : L ∈ cComp H) :
    H = M ∨ (conjClosure L M = L ∧ L ∈ cComp H ∧
      M = H ⊓ Subgroup.normalizer (conjClosure L M : Set G) ∧ M.relIndex H = 2) := by
  by_cases hMH : H = M
  · exact Or.inl hMH
  right
  have h12 := c2_12 hC129 hC111 hC19 hA3 h hT hRT
  have hnn : ¬ H ≤ Subgroup.normalizer (conjClosure L M : Set G) := fun hHn =>
    hMH ((inf_eq_left.mpr hHn).symm.trans h12)
  obtain ⟨T', hT', hTT'⟩ := B6.exists_isSylowTwoOf_ge hT.2.1 (hT.1.trans h.le_H)
  obtain ⟨hconj, hcase⟩ := hA3 H T' L h.sqtk hT' hL
  rcases hcase with hall | ⟨t, htT', htn, hset, -, -, -⟩
  ·
    exfalso
    have hHL : ∀ g ∈ H, conjByElt g L = L := by
      intro g hg
      have hmem : conjByElt g L ∈ conjSubgroupsBy H L := ⟨g, hg, rfl⟩
      rw [hconj] at hmem
      obtain ⟨t, ht, hteq⟩ := hmem
      rw [show conjByElt g L = conjByElt t L from hteq]
      exact C2Eleven.mem_normalizer_iff_conjByElt.mp (hall t ht)
    have hM0L : conjClosure L M = L := by
      refine le_antisymm (conjClosure_le fun m hm z hz => ?_) (le_conjClosure L M)
      have := C2Eleven.conj_mem_conjByElt (g := m) hz
      rwa [hHL m (h.le_H hm)] at this
    apply hnn
    rw [hM0L]
    exact fun g hg => C2Eleven.mem_normalizer_iff_conjByElt.mpr (hHL g hg)
  ·
    have hne : conjByElt t L ≠ L := fun heq =>
      htn (C2Eleven.mem_normalizer_iff_conjByElt.mpr heq)
    have htH : t ∈ H := hT'.1 htT'
    have hHset : ∀ g ∈ H, conjByElt g L = L ∨ conjByElt g L = conjByElt t L := by
      intro g hg
      have hmem : conjByElt g L ∈ conjSubgroupsBy H L := ⟨g, hg, rfl⟩
      rw [hconj, hset] at hmem
      exact hmem
    have hHset₂ : ∀ g ∈ H, conjByElt g (conjByElt t L) = L ∨
        conjByElt g (conjByElt t L) = conjByElt t L := by
      intro g hg
      rw [← C2Eleven.conjByElt_mul]
      exact hHset (g * t) (H.mul_mem hg htH)
    have hpair : ∀ g ∈ H, conjByElt g (L ⊔ conjByElt t L) = L ⊔ conjByElt t L := fun g hg =>
      C2Thirteen.conjByElt_sup_pair hne (hHset g hg) (hHset₂ g hg)
    obtain ⟨-, hM0, -⟩ := c2_9_one hA3 h hT
    have hM0L : conjClosure L M = L := by
      rcases hM0 with hM0 | ⟨L₂, hL₂T, hL₂ne, hM0eq, -⟩
      · exact hM0
      · exfalso
        obtain ⟨t', ht', hteq⟩ := hL₂T
        have h₂ : L₂ = conjByElt t L := by
          rcases hHset t' (h.le_H (hT.1 ht')) with h₃ | h₃
          · exact absurd (hteq.trans h₃) hL₂ne
          · exact hteq.trans h₃
        apply hnn
        rw [hM0eq, h₂]
        exact fun g hg => C2Eleven.mem_normalizer_iff_conjByElt.mpr (hpair g hg)
    refine ⟨hM0L, hL, h12.symm, ?_⟩
    have hMeq : M = H ⊓ Subgroup.normalizer (L : Set G) := by
      have := h12.symm
      rwa [hM0L] at this
    have hmemM : ∀ g ∈ H, g ∈ M ↔ conjByElt g L = L := by
      intro g hg
      rw [hMeq, Subgroup.mem_inf, C2Eleven.mem_normalizer_iff_conjByElt]
      exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    show (M.subgroupOf H).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htH⟩, fun b => ?_⟩
    have hb := b.2
    have h1 : b * ⟨t, htH⟩ ∈ M.subgroupOf H ↔ conjByElt (b : G) (conjByElt t L) = L := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hmemM _ (H.mul_mem hb htH),
        C2Eleven.conjByElt_mul]
    have h2 : b ∈ M.subgroupOf H ↔ conjByElt (b : G) L = L := by
      rw [Subgroup.mem_subgroupOf, hmemM _ hb]
    rw [h1, h2]
    rcases hHset b hb with h3 | h3
    · have h4 : ¬ conjByElt (b : G) (conjByElt t L) = L := fun h4 =>
        hne (C2Thirteen.conjByElt_injective (b : G) (h4.trans h3.symm))
      exact Or.inr ⟨h3, h4⟩
    · have h4 : conjByElt (b : G) (conjByElt t L) = L := by
        rcases hHset₂ b hb with h5 | h5
        · exact h5
        · exact absurd (C2Thirteen.conjByElt_injective (b : G) (h3.trans h5.symm)) hne.symm
      have h5 : ¬ conjByElt (b : G) L = L := fun h5 => hne (h3.symm.trans h5)
      exact Or.inl ⟨h4, h5⟩

end C213

theorem c2_13_of_isQuasisimple (hC129 : ASC129Statement G) (hC111 : ASC111Statement G)
    (hC19 : ASC19Statement G) (hA3 : A3Orbits G) {H R M L V T : Subgroup G}
    (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M) (hRT : R ≤ T) (hF : oTwoFstarIn H ≤ M)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    H = M ∨ (conjClosure L M = L ∧ L ∈ cComp H ∧
      M = H ⊓ Subgroup.normalizer (conjClosure L M : Set G) ∧ M.relIndex H = 2) :=
  c2_13_of_mem hC129 hC111 hC19 hA3 h hT hRT (asc213Step_of_isQuasisimple h hF hq)

end CFSG.Quasithin
