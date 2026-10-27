module

public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.PartTwo.Sec6.Item641
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.Adapters.TauCetiExceptional.BridgeG2
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.J2
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.GH74.EvenRank
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Assembly

@[expose] def POmegaPlusBridge : Prop :=
  ∀ (G : Type) [Group G] (n p f : ℕ), 4 ≤ n → StatedClassicalModel G .POmegaPlus n p f →
    InCatalog G

@[expose] def POmegaMinusBridge : Prop :=
  ∀ (G : Type) [Group G] (n p f : ℕ), 4 ≤ n → StatedClassicalModel G .POmegaMinus n p f →
    InCatalog G

@[expose] def ChevalleyEvenBridge (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] (f : ℕ), ChevalleyExceptionalModel G t 2 f → InCatalog G

@[expose] def SuzukiBridge : Prop :=
  ∀ (G : Type) [Group G] (f : ℕ), SuzukiModel G 2 f → InCatalog G

@[expose] def SporadicBridge (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G], NativeSporadic.IsSporadic G s → InCatalog G

structure Item310Bridges : Prop where
  omegaPlus : POmegaPlusBridge
  omegaMinus : POmegaMinusBridge
  g2 : ChevalleyEvenBridge .G2
  trialityD4 : ChevalleyEvenBridge .trialityD4
  twistedE6 : ChevalleyEvenBridge .twistedE6
  e6 : ChevalleyEvenBridge .E6
  e7 : ChevalleyEvenBridge .E7
  e8 : ChevalleyEvenBridge .E8
  suzuki : SuzukiBridge
  m23 : SporadicBridge .M23
  m24 : SporadicBridge .M24
  j3 : SporadicBridge .J3
  j4 : SporadicBridge .J4
  co1 : SporadicBridge .Co1
  co2 : SporadicBridge .Co2
  hs : SporadicBridge .HS
  suz : SporadicBridge .Suz
  he : SporadicBridge .He
  fi24 : SporadicBridge .Fi24Prime
  hn : SporadicBridge .HN
  th : SporadicBridge .Th
  b : SporadicBridge .B
  m : SporadicBridge .M

theorem sporadicBridge_of_nonempty {s : TauCeti.SporadicName}
    (h : Nonempty (NativeSporadic.Carrier s ≃* s.Group)) : SporadicBridge s := by
  intro G _ ⟨e⟩
  obtain ⟨b⟩ := h
  exact ⟨.sporadic s, ⟨e.trans b⟩⟩

theorem sporadicBridge_M11 : SporadicBridge .M11 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv

theorem sporadicBridge_M12 : SporadicBridge .M12 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv

theorem sporadicBridge_M22 : SporadicBridge .M22 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv

theorem sporadicBridge_J2 : SporadicBridge .J2 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv

theorem inCatalog_of_alternating {G : Type} [Group G] {k : ℕ} (hk : 5 ≤ k)
    (e : G ≃* alternatingGroup (Fin k)) : InCatalog G :=
  ⟨.alternating k hk, ⟨e⟩⟩

theorem inCatalog_of_chevalleyExceptionalModel_G2_three {G : Type} [Group G]
    (h : ChevalleyExceptionalModel G .G2 3 1) : InCatalog G := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  have hq : q.card = 3 := by rw [TauCeti.PrimePower.card_def]; rfl
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
      exact hq.symm.le
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by decide) K (by rw [hK, hq]; rfl)
  exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩

theorem statedClassicalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel G t n p f) : StatedClassicalModel G t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem chevalleyExceptionalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag}
    {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : LieModel G t 0 p f) :
    ChevalleyExceptionalModel G t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem suzukiModel_of_lieModel {G : Type} [Group G] {p f : ℕ}
    (h : LieModel G .twistedB2 0 p f) : SuzukiModel G p f :=
  (CFSG.Blueprint.LieModel.suzukiModel h).2

namespace Item310Bridges

variable (hb : Item310Bridges)
include hb

theorem sporadicBridge_of_mem {s : TauCeti.SporadicName}
    (hs : s ∈ ({.M11, .M12, .M22, .M23, .M24, .J2, .J3, .J4, .Co2, .Co1, .HS, .Suz, .He,
      .Fi24Prime, .HN, .Th, .B, .M} : Set TauCeti.SporadicName)) : SporadicBridge s := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  exacts [sporadicBridge_M11, sporadicBridge_M12, sporadicBridge_M22, hb.m23, hb.m24,
    sporadicBridge_J2, hb.j3, hb.j4, hb.co2, hb.co1, hb.hs, hb.suz, hb.he, hb.fi24, hb.hn, hb.th,
    hb.b, hb.m]

theorem inCatalog_of_lieModel_even {G : Type} [Group G] {s : StatedLieTag} {f : ℕ}
    (hs : s ∈ ({.G2, .trialityD4, .twistedE6, .E6, .E7, .E8} : Set StatedLieTag))
    (h : LieModel G s 0 2 f) : InCatalog G := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  have hs' : s ∈ chevalleyExceptionalTags := by
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hm := chevalleyExceptionalModel_of_lieModel hs' h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hb.g2 G f hm, hb.trialityD4 G f hm, hb.twistedE6 G f hm, hb.e6 G f hm, hb.e7 G f hm,
    hb.e8 G f hm]

theorem inCatalog_of_lieModel_omega {G : Type} [Group G] {s : StatedLieTag} {n p f : ℕ}
    (hs : s ∈ ({.POmegaPlus, .POmegaMinus} : Set StatedLieTag)) (hn : 4 ≤ n)
    (h : LieModel G s n p f) : InCatalog G := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact hb.omegaPlus G n p f hn (statedClassicalModel_of_lieModel (by decide) h)
  · exact hb.omegaMinus G n p f hn (statedClassicalModel_of_lieModel (by decide) h)

theorem inCatalog_of_gf2TypeList {G : Type} [Group G] (h : GF2TypeList G) : InCatalog G := by
  rcases h with ⟨n, -, h⟩ | ⟨n, -, h⟩ | ⟨s, n, hs, hn, h⟩ | ⟨s, hs, h⟩ |
    ⟨p, f, m, -, -, -, -, -, h⟩ | ⟨s, n, hs, h⟩ | ⟨k, hk, ⟨e⟩⟩ | ⟨s, hs, h⟩
  · exact ClassicalModels.statedClassicalModel_PSL_inCatalog_all G n 2 1
      (statedClassicalModel_of_lieModel (by decide) h)
  · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G n 2 1
      (statedClassicalModel_of_lieModel (by decide) h)
  · exact hb.inCatalog_of_lieModel_omega hs hn h
  · have hs' : s ∈ ({.G2, .trialityD4, .twistedE6, .E6, .E7, .E8} : Set StatedLieTag) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp
    exact hb.inCatalog_of_lieModel_even hs' h
  · exact ClassicalModels.statedClassicalModel_PSL_inCatalog_all G 2 p f
      (statedClassicalModel_of_lieModel (by decide) h)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ClassicalModels.statedClassicalModel_PSL_inCatalog_all G 3 3 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G 3 3 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact ClassicalModels.statedClassicalModel_PSL_inCatalog_all G 4 3 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G 4 3 1
        (statedClassicalModel_of_lieModel (by decide) h)
    · exact inCatalog_of_chevalleyExceptionalModel_G2_three
        (chevalleyExceptionalModel_of_lieModel (by decide) h)
    · exact hb.omegaPlus G 4 3 1 le_rfl (statedClassicalModel_of_lieModel (by decide) h)
  · have hk5 : 5 ≤ k := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl <;> norm_num
    exact inCatalog_of_alternating hk5 e
  · refine hb.sporadicBridge_of_mem ?_ G h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp

theorem inCatalog_of_listGroup {G : Type} [Group G] (h : ListGroup G) : InCatalog G := by
  rcases h with ⟨m, s, -, -, h⟩ | ⟨s, -, h⟩ | ⟨s, -, -, h⟩ | ⟨k, hk, -, ⟨e⟩⟩ | h | h | h
  · exact ClassicalModels.statedClassicalModel_PSL_inCatalog_all G m 2 s h
  · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G 3 2 s h
  · exact hb.suzuki G s (suzukiModel_of_lieModel h)
  · exact inCatalog_of_alternating (by omega) e
  · exact sporadicBridge_M22 G h
  · exact hb.m23 G h
  · exact hb.m24 G h

theorem inCatalog_of_strothSmithList {G : Type} [Group G] {f : ℕ} (h : StrothSmithList G f) :
    InCatalog G := by
  rcases h with h | ⟨s, m, hs, hm, h⟩ | ⟨s, hs, h⟩
  · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G 4 2 f
      (statedClassicalModel_of_lieModel (by decide) h)
  · exact hb.inCatalog_of_lieModel_omega hs hm h
  · exact hb.inCatalog_of_lieModel_even hs h

theorem inCatalog_of_gf2nTypeConclusion {G : Type} [Group G] {M B : Subgroup G}
    (h : GF2nTypeConclusion M B) : InCatalog G := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, ⟨-, f, m, -, -, h⟩ | ⟨-, h⟩⟩ | ⟨-, -, -, f, -, h⟩
  · exact hb.inCatalog_of_gf2TypeList h
  · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G m 2 f h
  · exact hb.inCatalog_of_listGroup h
  · exact hb.inCatalog_of_strothSmithList h

end Item310Bridges

theorem isTI_of_forall {G : Type} [Group G] {V : Subgroup G}
    (h : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V ⊓ V.map (MulAut.conj g).toMonoidHom = V) : IsTI V := h

theorem item3_10_of_gf2nType (hGF2n : GF2nTypeStatement) (hb : Item310Bridges) :
    PartTwo.Sec6.Item3_10 := by
  intro G _ _ hsimple hnonab hK hchar M hM V hV hTI
  have := hsimple
  have hK' : IsKProper G := ComponentClassification.CatalogueKProper.isKProper_of_kProper hK
  have hchar' : IsCharacteristicPType G 2 := (GH74.isCharTwoType_iff).mp hchar
  exact hb.inCatalog_of_gf2nTypeConclusion
    (hGF2n G hnonab hK' hchar' M hM V hV (isTI_of_forall hTI)).1

@[expose] def Item3_10_small : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G →
    ∀ M : Subgroup G, IsMaximalTwoLocal M → ∀ V : Subgroup G,
      Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
        IsElemAbelian 2 W) V →
      (∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V ⊓ V.map (MulAut.conj g).toMonoidHom = V) →
      Nat.card V ≤ 2 → InCatalog G

theorem item3_10_small_of_item3_10 (h : PartTwo.Sec6.Item3_10) : Item3_10_small :=
  fun G _ _ hs hn hK hc M hM V hV hTI _ => h G hs hn hK hc M hM V hV hTI

end CFSG.RankThree.GF2n
