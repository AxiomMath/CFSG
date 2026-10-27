module

public import CFSG.Quasithin.Background.E1Param
public import CFSG.Quasithin.Background.E1TwoAbs
public import CFSG.Quasithin.Background.B3Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin.A1b
open scoped commutatorElement

section AlmostSimple

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}

theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)) hab

theorem commutator_eq_top_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    refine absurd ?_ hab
    have hc : ⁅a, b⁆ ∈ commutator X := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem isQuasisimple_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  have hZ := center_eq_bot_of_simple hnab
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Nontrivial (X ⧸ Subgroup.center X) := e.toEquiv.nontrivial
  refine ⟨⟨commutator_eq_top_of_simple hnab⟩, IsSimpleGroup.isSimpleGroup_of_surjective
    e.symm.toMonoidHom e.symm.surjective, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩

structure AlmostSimple (L : Subgroup Q) : Prop where
  normal : L.Normal
  simple : IsSimpleGroup ↥L
  nonabelian : ∃ a b : ↥L, a * b ≠ b * a
  centralizer_eq : Subgroup.centralizer (L : Set Q) = ⊥
  two : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ L

namespace AlmostSimple

variable (h : AlmostSimple L)
include h

omit [Finite Q] in
theorem isPerfect : Group.IsPerfect ↥L := by
  have := h.simple
  exact ⟨commutator_eq_top_of_simple h.nonabelian⟩

omit [Finite Q] in
theorem not_isSolvable : ¬ Group.IsSolvable ↥L := by
  have := h.simple
  have := h.isPerfect
  exact Group.IsPerfect.not_isSolvable ↥L

omit [Finite Q] in
theorem commutator_self : ⁅L, L⁆ = L := by
  have := h.isPerfect
  rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top, Subgroup.map_top,
    Subgroup.range_subtype]

theorem solvableRadical_eq_bot : CFSG.solvableRadical Q = ⊥ := by
  have := h.normal
  have := h.simple
  set R := CFSG.solvableRadical Q with hRdef
  have hRs : Group.IsSolvable R := A3.solvableRadical_isSolvable
  have hRL : R ⊓ L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ L).subgroupOf L) with h1 | h1
    · rw [Subgroup.subgroupOf_eq_bot] at h1
      exact le_bot_iff.mp fun x hx => (Subgroup.disjoint_def.mp h1) hx hx.2
    · rw [Subgroup.subgroupOf_eq_top] at h1
      exact absurd (Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (h1.trans inf_le_left))) h.not_isSolvable
  have hc : ⁅R, L⁆ = ⊥ := le_bot_iff.mp (hRL ▸ Subgroup.commutator_le_inf R L)
  have hRC : R ≤ Subgroup.centralizer (L : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  exact le_bot_iff.mp (h.centralizer_eq ▸ hRC)

omit [Finite Q] in
theorem isComponent : CFSG.IsComponent L := by
  have := h.simple
  exact ⟨isQuasisimple_of_simple h.nonabelian, h.normal.isSubnormal⟩

theorem layer_eq : CFSG.layer Q = L := by
  refine le_antisymm (sSup_le fun C hC => ?_) (le_sSup h.isComponent)
  rcases CFSG.LocalCores.component_normal_subgroup hC h.normal with h1 | h1
  · exact h1
  · have hCC : C ≤ Subgroup.centralizer (L : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    rw [h.centralizer_eq] at hCC
    exact hCC.trans bot_le

omit [Finite Q] in
theorem isPGroup_quotient [L.Normal] : IsPGroup 2 (Q ⧸ L) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := h.two x
  exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

theorem twoResidual_eq : twoResidual (⊤ : Subgroup Q) = L := by
  have hLn := h.normal
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ N : Subgroup Q, N.Normal → (⊤ : Subgroup Q) ≤ Subgroup.normalizer (N : Set Q) :=
    fun N hN => (Subgroup.normalizer_eq_top (h := hN)).ge
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_top (hnorm L hLn)
    fun y _ => h.two y) fun x hx => mem_twoResidual_iff.mpr fun N _ hN h2N => ?_
  have hNn : N.Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_top g))
    n).mp hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ L).subgroupOf L) with h1 | h1
  · rw [Subgroup.subgroupOf_eq_bot] at h1
    have h2L : IsPGroup 2 ↥L := by
      intro l
      obtain ⟨k, hk⟩ := h2N l (Subgroup.mem_top _)
      refine ⟨k, Subtype.ext ?_⟩
      have hmem : (l : Q) ^ 2 ^ k ∈ N ⊓ L := ⟨hk, L.pow_mem l.2 _⟩
      simpa using (Subgroup.disjoint_def.mp h1) hmem hmem.2
    have := h2L.isNilpotent
    exact (h.not_isSolvable inferInstance).elim
  · rw [Subgroup.subgroupOf_eq_top] at h1
    exact (h1.trans inf_le_left) hx

theorem perfectCore_eq : perfectCore (⊤ : Subgroup Q) = L := by
  have := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_perfectCore_of_perfect le_top h.commutator_self)
  have := h.isPGroup_quotient.isNilpotent
  have hsol : Group.IsSolvable ↥(⊤ : Subgroup (Q ⧸ L)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  have hbot : perfectCore ((⊤ : Subgroup Q).map (QuotientGroup.mk' L)) = ⊥ := by
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective L)]
    exact (isSolvable_iff_perfectCore_eq_bot _).mp hsol
  intro x hx
  have hmap : QuotientGroup.mk' L x ∈ (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' L) :=
    Subgroup.mem_map_of_mem _ hx
  rw [map_perfectCore, hbot, Subgroup.mem_bot] at hmap
  exact (QuotientGroup.eq_one_iff x).mp hmap

omit [Finite Q] in
theorem commutator_eq {B : Subgroup Q} (hB : B ≠ ⊥) : ⁅L, B⁆ = L := by
  have := h.normal
  have := h.simple
  have hle : ⁅L, B⁆ ≤ L := Subgroup.commutator_le_left L B
  have hn : ((⁅L, B⁆ : Subgroup Q).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left L B)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((⁅L, B⁆ : Subgroup Q).subgroupOf L) with h1 | h1
  · rw [Subgroup.subgroupOf_eq_bot] at h1
    have hc : ⁅L, B⁆ = ⊥ := le_bot_iff.mp fun x hx => (Subgroup.disjoint_def.mp h1) hx (hle hx)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
      h.centralizer_eq] at hc
    exact absurd (le_bot_iff.mp hc) hB
  · rw [Subgroup.subgroupOf_eq_top] at h1
    exact le_antisymm hle h1

theorem eTwo {S B : Subgroup Q} (hB : B ≠ ⊥) : E1.ETwo Q S B := by
  have := h.normal
  have hR := h.solvableRadical_eq_bot
  set π := QuotientGroup.mk' (CFSG.solvableRadical Q) with hπ
  have hπi : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hR]
  let e : Q ≃* Q ⧸ CFSG.solvableRadical Q :=
    MulEquiv.ofBijective π ⟨hπi, QuotientGroup.mk'_surjective _⟩
  have he : ∀ X : Subgroup Q, X.map e.toMonoidHom = X.map π := fun X => rfl
  have hLbar : CFSG.IsComponent (L.map π) := by
    rw [← he]
    exact CFSG.LocalCores.isComponent_map_mulEquiv e h.isComponent
  have hlayer : CFSG.layer (Q ⧸ CFSG.solvableRadical Q) = L.map π := by
    rw [← E1.layer_map_mulEquiv e, h.layer_eq, he]
  have hLn' : (L.map π).Normal := Subgroup.Normal.map h.normal π (QuotientGroup.mk'_surjective _)
  have hconj : ∀ t, conjSub t (L.map π) = L.map π := fun t =>
    B6.conjSub_eq_self ((Subgroup.normalizer_eq_top (h := hLn')).ge (Subgroup.mem_top t))
  refine ⟨?_, ?_, ?_, ⟨L.map π, hLbar, ?_, Or.inl ?_⟩⟩
  · rw [hR]
    exact ⟨⊥, ⟨le_rfl, IsPGroup.of_bot, by rw [Subgroup.relIndex_self]; norm_num⟩, inferInstance⟩
  · rw [E1.pCore_two_quotient_eq_top_iff]
    intro x
    obtain ⟨k, hk⟩ := h.two x
    refine ⟨k, Subgroup.mem_comap.mpr ?_⟩
    rw [hlayer]
    exact Subgroup.mem_map_of_mem π hk
  · rw [h.twoResidual_eq, h.perfectCore_eq]
  · rw [hlayer]
    refine le_antisymm (le_iSup₂_of_le 1 (Subgroup.one_mem _) (hconj 1).ge)
      (iSup₂_le fun t _ => (hconj t).le)
  · unfold E1.barRad
    rw [← Subgroup.map_commutator, h.commutator_eq hB]

end AlmostSimple

end AlmostSimple

section FStar

variable {G : Type} [Group G] [Finite G]

theorem almostSimple_generalizedFitting (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    AlmostSimple (CFSG.generalizedFitting G) := by
  have hn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  refine ⟨hn, hs, hnab, ?_, fun x => ?_⟩
  · refine le_bot_iff.mp fun x hx => ?_
    have hxF := CFSG.centralizer_generalizedFitting_le G hx
    have hz : (⟨x, hxF⟩ : ↥(CFSG.generalizedFitting G)) ∈ Subgroup.center _ :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
    rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz)
  · have hx : x ∈ CFSG.generalizedFitting G ⊔ T := hFT ▸ Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨k, hk⟩ := hT ⟨z, hz⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
      show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, QuotientGroup.mk_one]

theorem isE_top_of_card_le (h : AlmostSimple (CFSG.generalizedFitting G)) {T A : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hA : A ≠ ⊥) {m : ℕ} (hm : Nat.card A ≤ 2 ^ m) :
    E1.IsE m ⊤ T A ⊤ := by
  refine ⟨le_rfl, le_inf (E1.tauOf_le _ _ _) le_top, by rwa [inf_top_eq], Or.inr ⟨?_, ?_⟩⟩
  · have hB : (A.subgroupOf ⊤).map (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).toMonoidHom ≠
        ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _),
        Subgroup.subgroupOf_eq_bot, disjoint_top]
      exact hA
    exact (E1.eTwo_map Subgroup.topEquiv _ _).mpr (h.eTwo hB)
  · have h1 := Subgroup.card_map_dvd (A.subgroupOf ⊤)
      (QuotientGroup.mk' (CFSG.solvableRadical ↥(⊤ : Subgroup G)))
    have h2 : Nat.card ↥(A.subgroupOf ⊤) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
    exact (Nat.le_of_dvd Nat.card_pos (h2 ▸ h1)).trans hm

theorem nParam_le_of_card_le (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {m : ℕ} (hm : 0 < m)
    (hA : ∀ A : Subgroup G, IsElemAbelian 2 A → Nat.card A ≤ 2 ^ m) :
    E1.nParam (⊤ : Subgroup G) ≤ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := almostSimple_generalizedFitting hs hnab hT.1 hFT
  rw [E1.nParam_le_iff hm]
  intro T' hT' Ω hΩ
  by_cases hex : ∃ A ∈ Ω, A ≠ ⊥
  · obtain ⟨A, hAΩ, hA1⟩ := hex
    have hT'2 : ¬ 2 ∣ T'.index := by
      rw [← Subgroup.relIndex_top_right]
      exact hT'.2.2
    obtain ⟨g, hg⟩ := B3.exists_conj_le_sylow (hT'.2.1.toSylow hT'2) A
      (B2F.isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hAΩ))
    have hA'Ω : conjSub g A ∈ Ω := hΩ.conj A hAΩ g (Subgroup.mem_top g)
    have hA'1 : conjSub g A ≠ ⊥ := by
      rw [Ne, conjSub, Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)]
      exact hA1
    have hE : E1.IsE m ⊤ T' (conjSub g A) ⊤ :=
      isE_top_of_card_le h hT' hA'1 (hA _ (hΩ.isElemAbelian _ hA'Ω))
    have hle : (⊤ : Subgroup G) ≤ E1.eGen m ⊤ T' Ω :=
      le_iSup₂_of_le (conjSub g A) hA'Ω (le_iSup_of_le hg (le_iSup₂_of_le ⊤ hE le_rfl))
    exact le_antisymm le_top (hle.trans le_sup_left)
  · push Not at hex
    have hW : E1.weakClosure T' Ω = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun _ => (hex A hA).le)
    rw [hW, Subgroup.normalizer_eq_top, inf_top_eq, sup_top_eq]

end FStar

end CFSG.Quasithin.Vol2.Ch11.SecE3
