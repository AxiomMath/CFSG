module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenCentral
public import CFSG.Quasithin.Background.C116Two.NatMod
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs
public import CFSG.Adapters.ClassicalCatalogReverse

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.OddStandard.HigherRank.YamadaG23 (Gomi1Q StrothSigma6 FooteSylowL6 LitQType
  LitStrothType IsQuotIso)
open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn normIn centIn)

@[expose] def CardRLeTwo (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G), Setting G M X n →
    ¬ CFSG.Assembly.InCatalog G → Nat.card ↥(Rc X) ≤ 2

abbrev YamakiHat : Type :=
  Multiplicative (evenWeight 6) ⋊[CFSG.Quasithin.C116Two.permAct 6] Equiv.Perm (Fin 6)

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

theorem theta_alt_or_surjective :
    (∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin n)) ∨ Function.Surjective C.θ := by
  by_cases h : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin n)
  · exact Or.inl h
  · push Not at h
    obtain ⟨m, hm⟩ := h
    refine Or.inr fun σ => ?_
    by_cases hσ : σ ∈ alternatingGroup (Fin n)
    · obtain ⟨x, hx⟩ := C.exists_lift hσ
      exact ⟨_, hx⟩
    · have hs1 : Equiv.Perm.sign σ = -1 :=
        (Int.units_eq_one_or _).resolve_left fun h => hσ (Equiv.Perm.mem_alternatingGroup.2 h)
      have hs2 : Equiv.Perm.sign (C.θ m) = -1 :=
        (Int.units_eq_one_or _).resolve_left fun h => hm (Equiv.Perm.mem_alternatingGroup.2 h)
      have h1 : σ * (C.θ m)⁻¹ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs1, hs2]
        decide
      obtain ⟨x, hx⟩ := C.exists_lift h1
      refine ⟨⟨(x : G), C.S.le x.2⟩ * m, ?_⟩
      rw [map_mul, hx, inv_mul_cancel_right]

theorem theta_ker_eq (hR : Nat.card ↥(Rc X) ≤ 2) :
    C.θ.ker = (CFSG.Open.pCoreOf 2 M).subgroupOf M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C.K_eq_Q hR, C.mem_K]
  exact ⟨fun h => ⟨m.2, h⟩, fun ⟨_, h⟩ => h⟩

theorem isQuotIso_sym (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ) :
    IsQuotIso (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
      (Subgroup.centralizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
      (Equiv.Perm (Fin n)) := by
  rw [C.S.normalizer_Q_eq, C.centralizer_Q_eq hR]
  exact ⟨CFSG.CGT.PushingUpLit.SolK.pCoreOf_le_self M, C.θ, hsurj, C.theta_ker_eq hR⟩

end Cfg

section Catalogue

theorem inCatalog_of_lieModel_classical {S : Type} [Group S]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel S t n p f) (ht : t ∈ CFSG.Blueprint.classicalTags) :
    CFSG.Assembly.InCatalog S :=
  CFSG.ClassicalModels.inCatalog_of_statedClassicalModel S t n p f
    (CFSG.Blueprint.LieModel.statedClassicalModel h ht)

theorem inCatalog_of_top {G : Type} [Group G]
    (h : CFSG.Assembly.InCatalog ↥(⊤ : Subgroup G)) : CFSG.Assembly.InCatalog G := by
  obtain ⟨i, ⟨e⟩⟩ := h
  exact ⟨i, ⟨Subgroup.topEquiv.symm.trans e⟩⟩

theorem inCatalog_of_yamakiConcl {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSp 3 2 1 ∨ Nonempty (S ≃* alternatingGroup (Fin 12)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 13))) : CFSG.Assembly.InCatalog S := by
  rcases h with h | h | h
  · exact inCatalog_of_lieModel_classical h (by decide)
  · obtain ⟨e⟩ := h
    exact CFSG.RankThree.GF2n.inCatalog_of_alternating (by norm_num) e
  · obtain ⟨e⟩ := h
    exact CFSG.RankThree.GF2n.inCatalog_of_alternating (by norm_num) e

theorem inCatalog_of_smithThreeConcl
    {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSL 5 2 1 ∨ CFSG.Blueprint.LieModel S .PSU 5 2 1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic S .M24 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic S .He ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic S .Suz) : CFSG.Assembly.InCatalog S := by
  rcases h with h | h | h | h | h
  · exact inCatalog_of_lieModel_classical h (by decide)
  · exact inCatalog_of_lieModel_classical h (by decide)
  · exact CFSG.RankThree.GF2n.sporadicBridge_M24 S h
  · exact CFSG.RankThree.GF2n.sporadicBridge_He S h
  · exact CFSG.RankThree.GF2n.sporadicBridge_Suz S h

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_of_centralizer_eq {A : Subgroup G} (hA : IsPGroup 2 A)
    (hC : Subgroup.centralizer (A : Set G) = A) :
    IsSylowIn 2 (Subgroup.centralizer (A : Set G)) A := by
  refine ⟨hC.ge, hA, ?_⟩
  rw [hC, Subgroup.relIndex_self]
  norm_num

end Catalogue

end CFSG.RankThree.PartTwo.Sec19.SolEven
