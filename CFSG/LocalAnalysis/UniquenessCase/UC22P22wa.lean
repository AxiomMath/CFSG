module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge2
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yg
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sj
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22w

theorem rankThreeLayer_eq_self {A : Type} [Group A] {L : Subgroup A} (hq : CFSG.Open.IsQuasisimple ↥L) :
    rankThreeLayer L = L :=
  le_antisymm (sSup_le fun _ hK => hK.1) (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩)

theorem not_isPGroup_of_quasisimple {A : Type} [Group A] [Finite A] (hq : CFSG.Open.IsQuasisimple A) {p : ℕ}
    [Fact p.Prime] : ¬ IsPGroup p A := by
  intro hp
  haveI : Group.IsPerfect A := ⟨hq.1⟩
  haveI : Nontrivial A := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  exact Group.IsPerfect.not_isNilpotent A hp.isNilpotent

theorem isPerfect_map {A B : Type} [Group A] [Group B] {K : Subgroup A} (hK : ⁅K, K⁆ = K) (f : A →* B) :
    Group.IsPerfect ↥(K.map f) := by
  refine ⟨Subgroup.map_injective (K.map f).subtype_injective ?_⟩
  have htop : (⊤ : Subgroup ↥(K.map f)).map (K.map f).subtype = K.map f := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [commutator_def, Subgroup.map_commutator, htop, ← Subgroup.map_commutator, hK]

theorem commutator_subgroupOf {Y K : Subgroup G} (hKY : K ≤ Y) (hK : ⁅K, K⁆ = K) :
    ⁅K.subgroupOf Y, K.subgroupOf Y⁆ = K.subgroupOf Y := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKY, hK]

end P22w

theorem uc22p22wa_lift (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h119 : R119W D)
    (hU : ¬ CFSG.CGT.Timmesfeld75.IsTI D.U) {Lb : Subgroup (MBar D.M D.U)} (hLb : IsComponentOf Lb ⊤) :
    ∃ K ∈ calC D.M, mbarImage D.M D.U K = Lb := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW := uc22p22o_inCalW_U_of_not_isTI D hx h61 hU
  have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  haveI hN := cTilde_bot_normal D.M D.U hMU
  set e := mbarEquiv D.M D.U with he
  set L' : Subgroup (F11.MBar11 D.M ⊥ D.U) := Lb.map e.toMonoidHom with hL'
  have hL'q : CFSG.Open.IsQuasisimple ↥L' :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Lb.equivMapOfInjective e.toMonoidHom e.injective).symm hLb.2.2
  have hL'sub : CFSG.Open.IsSubnormal L' ⊤ := by
    have h1 := CFSG.Open.IsSubnormal.map e.toMonoidHom hLb.2.1
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h1
  set Xp : Subgroup G := F11.barPreimage11 D.M ⊥ D.U L' with hXp
  have hXpM : Xp ≤ D.M := Subgroup.map_subtype_le _
  have hCX : F11.CTilde D.M ⊥ D.U ≤ Xp := by
    intro x hx
    have hxM : x ∈ D.M := by
      rw [cTilde_bot] at hx
      exact hx.1
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨x, hxM⟩ ∈ L'
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact L'.one_mem
  have hbarXp : F11.barImage11 D.M ⊥ D.U Xp = L' := by
    unfold F11.barImage11
    rw [hXp]
    unfold F11.barPreimage11
    have h1 : ((L'.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ D.U).subgroupOf D.M))).map
        D.M.subtype).subgroupOf D.M = L'.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ D.U).subgroupOf D.M)) :=
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L'
  have hXpsub : CFSG.Open.IsSubnormal Xp D.M := by
    have h1 := CFSG.Open.IsSubnormal.map D.M.subtype
      (CFSG.Open.IsSubnormal.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ D.U).subgroupOf D.M)) hL'sub)
    rwa [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  obtain ⟨Y, hY, -⟩ := h119 D.U (uc22p22c_hyp11 D hW hU) Xp hCX hXpM
    (by rw [hbarXp]; exact P22w.rankThreeLayer_eq_self hL'q)
  obtain ⟨hYX, -, hO2E, hXY, -, hYbar⟩ := hY
  have hYM : Y ≤ D.M := hYX.trans hXpM
  have hYsub : CFSG.Open.IsSubnormal Y Xp :=
    CFSG.Open.IsSubnormal.step hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY)
      (CFSG.Open.IsSubnormal.refl _)
  set f : ↥Y →* F11.MBar11 D.M ⊥ D.U :=
    (QuotientGroup.mk' ((F11.CTilde D.M ⊥ D.U).subgroupOf D.M)).comp (Subgroup.inclusion hYM) with hf
  have hfrange : f.range = L' := by
    rw [← hbarXp, ← hYbar, hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hlayer : CFSG.layer (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ := by
    rw [P22y.layer_eq_rankThreeLayer_top]
    set L := rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) with hL
    have h1 : (L.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype =
        (⊤ : Subgroup ↥Y).map Y.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hO2E
    have h2 := Subgroup.map_injective Y.subtype_injective h1
    have h3 := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)) L
    rw [h2, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3
    exact h3.symm
  have hfmem : ∀ y, f y ∈ L' := fun y => hfrange ▸ (⟨y, rfl⟩ : f y ∈ f.range)
  set g : ↥Y →* ↥L' := f.codRestrict L' hfmem with hg
  have hgs : Function.Surjective g := by
    intro z
    obtain ⟨y, hy⟩ := (hfrange.symm ▸ z.2 : (z : F11.MBar11 D.M ⊥ D.U) ∈ f.range)
    exact ⟨y, Subtype.ext hy⟩
  set P : Subgroup ↥L' := (CFSG.pCore 2 ↥Y).map g with hP
  haveI hPn : P.Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map g hgs
  have hPne : P ≠ ⊤ := by
    intro hPt
    have h2 : IsPGroup 2 ↥P := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map g
    rw [hPt] at h2
    exact P22w.not_isPGroup_of_quasisimple hL'q (h2.of_equiv Subgroup.topEquiv)
  by_contra hno
  push Not at hno
  have hker : CFSG.pCore 2 ↥Y ≤ ((QuotientGroup.mk' P).comp g).ker := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨y, hy, rfl⟩
  set gb : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* ↥L' ⧸ P := QuotientGroup.lift _ _ hker with hgb
  have hall : ∀ C : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y), CFSG.IsComponent C → C.map gb = ⊥ := by
    intro C hC
    obtain ⟨K, hK, hKC⟩ := uc22p21c_exists_calC_of_component Y hC
    have hKY : K ≤ Y := hK.1.le
    haveI : Group.IsPerfect ↥((K.subgroupOf Y).map g) :=
      P22w.isPerfect_map (P22w.commutator_subgroupOf hKY hK.2.1) g
    have hsubn : CFSG.Open.IsSubnormal ((K.subgroupOf Y).map g) ⊤ :=
      CFSG.Open.IsSubnormal.of_mathlib (hK.1.subgroupOf.map hgs)
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hL'q _ hsubn with
      hbot | htop
    · rw [← hKC]
      unfold barImage
      rw [Subgroup.map_map, hgb, QuotientGroup.lift_comp_mk', ← Subgroup.map_map, hbot, Subgroup.map_bot]
    · exfalso
      refine hno K ⟨hK.1.trans (hYsub.trans hXpsub), hK.2.1, hK.2.2⟩ ?_
      apply Subgroup.map_injective (show Function.Injective e.toMonoidHom from e.injective)
      rw [map_mbarImage]
      have h1 : (K.subgroupOf Y).map f = L' := by
        have h2 : f = L'.subtype.comp g := by
          ext y
          rfl
        rw [h2, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [← hL', ← h1]
      unfold F11.barImage11
      rw [hf, ← Subgroup.map_map]
      congr 1
      ext x
      constructor
      · intro hx
        exact ⟨⟨(x : G), hKY hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
  have htopmap : (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).map gb = ⊥ := by
    rw [← hlayer, CFSG.layer.eq_sSup, eq_bot_iff, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap, hall C hC]
  apply hPne
  rw [eq_top_iff]
  intro l _
  obtain ⟨y, rfl⟩ := hgs l
  have hmem : gb (QuotientGroup.mk y) ∈ (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).map gb :=
    ⟨_, Subgroup.mem_top _, rfl⟩
  rw [htopmap, Subgroup.mem_bot, hgb, QuotientGroup.lift_mk, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem uc22p22wa_onto (D : Data G) {K : Subgroup G} (hK : K ∈ calC D.M) (hne : mbarImage D.M D.U K ≠ ⊥) :
    ∃ ψ : Bar2 K →* ↥(mbarImage D.M D.U K), Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (Bar2 K) ∧
      ∀ k : ↥K, ((ψ (QuotientGroup.mk k) : MBar D.M D.U)) = QuotientGroup.mk (Subgroup.inclusion hK.1.le k) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ D.M := hK.1.le
  have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  set φ := uc22br4_phi D.M D.U K hKM with hφ
  have hOU : pCoreOf 2 D.M ≤ centralizer (D.U : Set G) :=
    Subgroup.le_centralizer_iff.1 ((uc22p22c_U_facts D).1.trans inf_le_right)
  have hle : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro x hx
    rw [hφ, uc22br4_ker_phi D.M D.U K hMU hKM, Subgroup.mem_subgroupOf]
    exact hOU (uc22p22r_pCoreOf_le_of_isSubnormal hK.1 ⟨x, hx, rfl⟩)
  set ψ₀ : Bar2 K →* MBar D.M D.U := QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hle with hψ₀
  have hmem : ∀ z, ψ₀ z ∈ mbarImage D.M D.U K := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hψ₀, QuotientGroup.lift_mk, ← uc22br4_range_phi D.M D.U K hKM]
    exact ⟨k, rfl⟩
  refine ⟨ψ₀.codRestrict _ hmem, ?_, ?_, fun k => rfl⟩
  · intro z
    obtain ⟨y, hy⟩ := ((uc22br4_range_phi D.M D.U K hKM).symm ▸ z.2 : (z : MBar D.M D.U) ∈ φ.range)
    exact ⟨QuotientGroup.mk y, Subtype.ext hy⟩
  · refine P22sj.le_center_of_quasisimple hK.2.2 inferInstance fun htop => hne ?_
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := ((uc22br4_range_phi D.M D.U K hKM).symm ▸ hz : z ∈ φ.range)
    have h1 : (QuotientGroup.mk k : Bar2 K) ∈ (ψ₀.codRestrict _ hmem).ker := htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h1
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.mem_bot]
    exact h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
