module

public import CFSG.Quasithin.EmptyFaithful.S151S6A
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def SimpleTypeCD15120 (Q : Type) [Group Q] : Prop :=
  (IsPSU 3 3 1 Q ∨ IsTits Q ∨ Is3D4 2 1 Q) ∨
    (IsSporadic .M11 Q ∨ IsSporadic .M12 Q ∨ IsSporadic .M22 Q ∨ IsSporadic .M23 Q ∨
      IsSporadic .M24 Q ∨ IsSporadic .J2 Q ∨ IsSporadic .HS Q ∨ IsSporadic .He Q ∨
      IsSporadic .Ru Q)

@[expose] def SimpleTypeMax15120 (Q : Type) [Group Q] : Prop :=
  (IsPSU 3 3 1 Q ∨ IsTits Q ∨ Is3D4 2 1 Q) ∨
    ((IsSporadic .M11 Q ∨ IsSporadic .M12 Q ∨ IsSporadic .J2 Q ∨ IsSporadic .HS Q ∨
      IsSporadic .He Q) ∨ IsSporadic .Ru Q)

variable {G : Type} [Group G] [Finite G]

@[expose] def CompTypeDEasyB15120 (L : Subgroup G) : Prop :=
  CompTypeDEasy15120 L ∨ IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def CompTypeDHardB15120 (L : Subgroup G) : Prop :=
  IsSporadic .M22 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .M24 (↥L ⧸ CFSG.pCore 2 ↥L)

omit [Finite G] in
theorem compTypeD_easyB_or_hardB {L : Subgroup G} (h : CompTypeD15120 L) :
    CompTypeDEasyB15120 L ∨ CompTypeDHardB15120 L := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact Or.inl (Or.inr h)

@[expose] def AutFixSimple (Q : Type) [Group Q] (P : Subgroup Q) : Prop :=
  ∀ φ : Q →* Q, (∀ q, φ (φ q) = q) → (∀ x ∈ P, φ x = x) →
    ∃ c ∈ centerOf P, ∀ q, φ q = c * q * c⁻¹

@[expose] def Input15120AutFixSimple : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    SimpleTypeCD15120 Q → AutFixSimple Q P

@[expose] def Input15120CentMaxSimple : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    SimpleTypeMax15120 Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q))

@[expose] def Input15120CentLocB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L B : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    IsPGroup 2 ↥(Subgroup.center ↥L) → IsSylowTwoOf B L →
    ((IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∨ CompTypeD15120 L) →
      AutFixOn L B ∧
        (((IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∨ CompTypeDEasyB15120 L) →
          ¬ L ≤ Subgroup.centralizer (centerOf B : Set G) →
            IsMaxSubgroupIn L (L ⊓ Subgroup.centralizer (centerOf B : Set G)))

theorem pCore_le_center_of_quasisimple {L : Type*} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) : CFSG.pCore 2 L ≤ Subgroup.center L := by
  have hQ : CFSG.IsQuasisimple L :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hq⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (CFSG.pCore_normal (p := 2) (G := L)) with
    h | h
  · exfalso
    have hperf : Group.IsPerfect L := ⟨hq.1⟩
    have hL2 : IsPGroup 2 L := by
      have h2 := CFSG.pCore_isPGroup (p := 2) (G := L)
      rw [h] at h2
      exact h2.of_equiv Subgroup.topEquiv
    have hsolv : Group.IsSolvable L := by
      have := hL2.isNilpotent
      infer_instance
    have : Nontrivial L := by
      have hnt : Nontrivial (L ⧸ Subgroup.center L) := hq.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
    exact Group.IsPerfect.not_isSolvable L hsolv
  · exact h

omit [Finite G] in
theorem pCoreOf_subgroupOf (L : Subgroup G) : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L :=
  CFSG.openPCoreOf_subgroupOf 2 L

omit [Finite G] in
theorem sylow_map {L B : Subgroup G} {Q : Type} [Group Q] (hB : IsSylowTwoOf B L) (π : ↥L →* Q)
    (hπ : Function.Surjective π) :
    IsPGroup 2 ↥((B.subgroupOf L).map π) ∧ ¬ 2 ∣ ((B.subgroupOf L).map π).index :=
  ⟨(A4.isPGroup_subgroupOf_of_le hB.1 hB.2.1).map π,
    fun h => hB.2.2 (h.trans (Subgroup.index_map_dvd _ hπ))⟩

theorem input15120CentLocB_of_simple (hA : Input15120AutFixSimple) (hM : Input15120CentMaxSimple) :
    Input15120CentLocB := by
  intro G _ _ L B hq _ hB htype
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hBL : B ≤ L := hB.1
  have hbotN : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := Subgroup.normalizer_eq_top _
  let π₁ : ↥L →* ↥L := MonoidHom.id ↥L
  have hπ₁ : Function.Surjective π₁ := Function.surjective_id
  have hk₁ : π₁.ker = ⊥ := MonoidHom.ker_id
  have hP₁ := sylow_map hB π₁ hπ₁
  have hK₁ : IsPGroup 2 ↥π₁.ker := by
    intro g
    refine ⟨0, ?_⟩
    have h1 : (g : ↥L) = 1 := MonoidHom.mem_ker.mp g.2
    apply Subtype.ext
    simp [h1]
  let π₂ : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ₂ : Function.Surjective π₂ := QuotientGroup.mk'_surjective _
  have hk₂ : π₂.ker = CFSG.pCore 2 ↥L := QuotientGroup.ker_mk' _
  have hP₂ := sylow_map hB π₂ hπ₂
  have hker₂ : π₂.ker ≤ Subgroup.center ↥L := by
    rw [hk₂]
    exact pCore_le_center_of_quasisimple hq
  have hK₂ : IsPGroup 2 ↥π₂.ker := by
    rw [hk₂]
    exact CFSG.pCore_isPGroup
  have hKg₂ : π₂.ker = (pCoreOf 2 L).subgroupOf L := by
    rw [hk₂, pCoreOf_subgroupOf]
  have hN₂ : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  refine ⟨?_, ?_⟩
  · rcases htype with hC | hD
    · exact S151S6.autFixOn_of_central_quotient (Kg := ⊥) hperf hBL π₁ hπ₁ (by rw [hk₁]; exact bot_le)
        (by rw [hk₁, Subgroup.bot_subgroupOf]) (by rw [hbotN]; exact le_top)
        (hA ↥L _ hP₁.1 hP₁.2 (Or.inl hC))
    · exact S151S6.autFixOn_of_central_quotient hperf hBL π₂ hπ₂ hker₂ hKg₂ hN₂
        (hA _ _ hP₂.1 hP₂.2 (Or.inr hD))
  · intro hmax hne
    rcases hmax with hC | hE
    · exact S151S6.centralizer_max_of_central_quotient hB π₁ hπ₁ (by rw [hk₁]; exact bot_le) hK₁ hne
        (hM ↥L _ hP₁.1 hP₁.2 (Or.inl hC))
    · exact S151S6.centralizer_max_of_central_quotient hB π₂ hπ₂ hker₂ hK₂ hne
        (hM _ _ hP₂.1 hP₂.2 (Or.inr hE))

theorem s151s_not_le_centralizer {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hfix : AutFixOn L (s1516 T Z₁ ⊓ L)) :
    ¬ L ≤ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) := by
  intro hle
  have h1 := s151s_cent_le_mZ hc hcomp hfix
  apply hc.hL.not_le
  intro x hx
  exact (h1 ⟨hx, hle hx⟩).1

theorem input15120MLC_of_locB (hloc : Input15120CentLocB) : Input15120MLC := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hC
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hZ : IsPGroup 2 (Subgroup.center ↥L) :=
    isPGroup_two_center_of_isComponentOf1515c hcomp hc.h19.one
  obtain ⟨hfix, hmax⟩ := hloc G L _ hcomp.2.2 hZ hSyl (Or.inl hC)
  exact s151s_mZ_eq_of_loc hc hcomp hfix
    (hmax (Or.inl hC) (s151s_not_le_centralizer hc hcomp hfix))

@[expose] def Input15120MLDHardB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeD15120 L →
    CompTypeDHardB15120 L → Lemma15118Extra T Mc M Z₁ →
    mZ1516 Mc Z₁ ⊓ L ≤ L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G)

theorem input15120MLDHardB_of_hard (h : Input15120MLDHard) : Input15120MLDHardB := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hD hH _
  refine h G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hD ?_
  rcases hH with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))

theorem input15120MLD_of_locB (hloc : Input15120CentLocB) (hhard : Input15120MLDHardB) :
    Input15120MLD := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hD hx
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hZ : IsPGroup 2 (Subgroup.center ↥L) :=
    isPGroup_two_center_of_isComponentOf1515c hcomp hc.h19.one
  obtain ⟨hfix, hmax⟩ := hloc G L _ hcomp.2.2 hZ hSyl (Or.inr hD)
  rcases compTypeD_easyB_or_hardB hD with hE | hH
  · exact s151s_mZ_eq_of_loc hc hcomp hfix
      (hmax (Or.inr hE) (s151s_not_le_centralizer hc hcomp hfix))
  · exact le_antisymm (hhard G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hD hH hx)
      (s151s_cent_le_mZ hc hcomp hfix)

theorem input15120MLC_of_simple (hA : Input15120AutFixSimple) (hM : Input15120CentMaxSimple) :
    Input15120MLC :=
  input15120MLC_of_locB (input15120CentLocB_of_simple hA hM)

theorem input15120MLD_of_simple (hA : Input15120AutFixSimple) (hM : Input15120CentMaxSimple)
    (hhard : Input15120MLDHardB) : Input15120MLD :=
  input15120MLD_of_locB (input15120CentLocB_of_simple hA hM) hhard

end CFSG.Quasithin
