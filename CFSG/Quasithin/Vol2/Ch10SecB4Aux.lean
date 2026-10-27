module

public import CFSG.Quasithin.Vol2.Ch10SecBXiAct
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10SecBInner3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.Walter.J1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjClosure_eq_self {X H : Subgroup G} (h : H ≤ Subgroup.normalizer (X : Set G)) :
    conjClosure X H = X :=
  le_antisymm (conjClosure_le fun _ hs x hx => (Subgroup.mem_normalizer_iff.mp (h hs) x).mp hx)
    (le_conjClosure X H)

theorem conjClosure_eq_sup_of_ncard [Finite G] {H T L : Subgroup G} (hTH : T ≤ H)
    (hcard : Set.ncard (conjSubgroupsBy H L) = 2) {s : G} (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    conjClosure L T = L ⊔ CFSG.conjugate L s := by
  have hset : conjSubgroupsBy H L = {L, CFSG.conjugate L s} := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro K (rfl | rfl)
      · exact ⟨1, H.one_mem, by ext; simp⟩
      · exact ⟨s⁻¹, H.inv_mem (hTH hs), rfl⟩
    · rw [hcard, Set.ncard_pair (SecA.ne_conjugate hsn)]
  refine le_antisymm (conjClosure_le fun r hr l hl => ?_) (sup_le (le_conjClosure L T) ?_)
  · have hmem : L.map (MulAut.conj r).toMonoidHom ∈ conjSubgroupsBy H L := ⟨r, hTH hr, rfl⟩
    have hrl : r * l * r⁻¹ ∈ L.map (MulAut.conj r).toMonoidHom := ⟨l, hl, by simp⟩
    rw [hset] at hmem
    rcases hmem with h | h
    · rw [h] at hrl; exact Subgroup.mem_sup_left hrl
    · rw [h] at hrl; exact Subgroup.mem_sup_right hrl
  · intro x hx
    rw [SecA.mem_conjugate_iff] at hx
    simpa [mul_assoc] using mem_conjClosure (T.inv_mem hs) hx

theorem le_of_isSimpleGroup [Finite G] {H L K : Subgroup G} (hL : L ∈ cComp H)
    (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {x : G} (hxK : x ∈ K) (hxL : x ∈ L)
    (hxO : x ∉ pCoreOf 2 L) : L ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hLK : L ≤ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKH (hLH hl), Subgroup.le_normalizer hl⟩
  have hNn : ((K ⊓ L).subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLK
  set N := ((K ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hNdef
  have hNbar : N.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hNtop : N = ⊤ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exfalso
      have hx : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩) ∈ N :=
        ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr ⟨hxK, hxL⟩, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact hxO ⟨⟨x, hxL⟩, hx, rfl⟩
    · exact h
  have hpow : ∀ l ∈ L, ∃ k : ℕ, l ^ 2 ^ k ∈ K ⊓ L := by
    intro l hl
    have hl' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩) ∈ N := by rw [hNtop]; trivial
    obtain ⟨n, hn, hnl⟩ := hl'
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)) ⟨_, hnl⟩
    have hk' : ((n : ↥L)⁻¹ * ⟨l, hl⟩) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hqN : ((n : G)⁻¹ * l) ∈ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) :=
      hLK (L.mul_mem (L.inv_mem n.2) hl)
    obtain ⟨n', hn', hpow⟩ := A4.exists_pow_mul_eq (Subgroup.mem_subgroupOf.mp hn) hqN (2 ^ k)
    have hk'' : ((n : G)⁻¹ * l) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk'
      simpa using this
    refine ⟨k, ?_⟩
    have e : l ^ 2 ^ k = ((n : G) * ((n : G)⁻¹ * l)) ^ 2 ^ k := by group
    rw [e, hpow, hk'', mul_one]
    exact hn'
  have hKL := C2Nine.eq_of_perfect_of_pow_mem (mem_cComp_iff.mp hL).2.1 inf_le_right hNn hpow
  intro l hl
  have hl' : l ∈ K ⊓ L := by rw [hKL]; exact hl
  exact hl'.1

theorem sl_two_of_model {Q : Type} [Group Q] {n : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 2 n) :
    0 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  exact ⟨hf, K, inferInstance, inferInstance, hK,
    ⟨e.trans (QuasithinUnique.Setup.Family.statedProjSL_two_equiv K)⟩⟩

theorem psl_two_of_model {Q : Type} [Group Q] {q : ℕ} (hq : q.Prime)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 q 1) :
    Nonempty (Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod q) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let r : K ≃+* ZMod q := FiniteField.ringEquivOfCardEq hcard
  exact ⟨(e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv r (Fin 2))⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
