module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieLow
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.CGT
open scoped MatrixGroups

local notation "cjS" => Timmesfeld75.conjSubgroup

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem sup_conj_eq_top_of_ne {g M : SL(2, K)}
    (h : cjS M (cjS g (Timmesfeld75.utri K)) ≠ cjS g (Timmesfeld75.utri K)) :
    cjS g (Timmesfeld75.utri K) ⊔ cjS M (cjS g (Timmesfeld75.utri K)) = ⊤ := by
  have e : M * g = g * (g⁻¹ * M * g) := by group
  have hb : g⁻¹ * M * g ∉ Timmesfeld75.borel K := by
    intro hb
    apply h
    rw [Timmesfeld75.conjSubgroup_conjSubgroup, e, ← Timmesfeld75.conjSubgroup_conjSubgroup,
      KGNat.conjSubgroup_eq_of_mem_normalizer (KGNat.borel_le_normalizer_utri hb)]
  rw [Timmesfeld75.conjSubgroup_conjSubgroup, e, ← Timmesfeld75.conjSubgroup_conjSubgroup,
    ← Timmesfeld75.conjSubgroup_sup_eq_sup, KGNat.utri_sup_conj_eq_top hb,
    Timmesfeld75.conjSubgroup_top]

omit [Finite K] in
theorem sl2_nonabelian : ∃ a b : SL(2, K), a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hZ : Subgroup.center SL(2, K) = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hc y x
  rw [KGNat.center_SL2_eq_bot] at hZ
  have h1 : (Timmesfeld75.utriElt (1 : K) : SL(2, K)) ∈ (⊥ : Subgroup SL(2, K)) :=
    hZ ▸ Subgroup.mem_top _
  exact Timmesfeld75.utriElt_ne_one one_ne_zero (Subgroup.mem_bot.mp h1)

end Model

theorem exists_sl2_of_isPSL22 {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* SL(2, K)) := by
  obtain ⟨⟨-, hn1, -, hne, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hK : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hn1 hcard
  refine ⟨?_, K, hF, hFin, hK, hcard,
    ⟨e.trans CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj.symm⟩⟩
  by_contra hlt
  have h1 : n = 1 := by omega
  subst h1
  exact hne (by simp)

section Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conjSubgroup {X : Type*} [Group X] (ψ : X →* G) (M : X) (P : Subgroup X) :
    (cjS M P).map ψ = A1b.conjSub (ψ M) (P.map ψ) := by
  unfold Timmesfeld75.conjSubgroup A1b.conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem le_nParam_of_sl2 {L T : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : AlmostSimple L) (hT : quasithinIsSylowTwo T) (hLT : L ⊔ T = ⊤) (e : ↥L ≃* SL(2, K))
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) : (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have hLn := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := T ⊓ L with hUdef
  set ψ : SL(2, K) →* G := L.subtype.comp e.symm.toMonoidHom with hψdef
  have hψi : Function.Injective ψ := L.subtype_injective.comp e.symm.injective
  have hψr : ψ.range = L := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set P : Subgroup SL(2, K) := U.comap ψ with hPdef
  have hUP : P.map ψ = U := Subgroup.map_comap_eq_self (hψr ▸ inf_le_right)
  have hP2 : IsPGroup 2 P := IsPGroup.comap_of_injective (hT.1.to_inf_left) ψ hψi
  have hPidx : ¬ 2 ∣ P.index := by
    obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal (hT.1.toSylow hT.2) (N := L)
    have hQidx := Q.not_dvd_index
    have e1 : P = (U.subgroupOf L).comap e.symm.toMonoidHom := by
      rw [hPdef, hψdef, ← Subgroup.comap_comap]
      rfl
    rw [e1, Subgroup.index_comap_of_surjective _ e.symm.surjective]
    rwa [hQ] at hQidx
  obtain ⟨g, hg⟩ := KGNat.exists_conj_utri_eq_of_index hP2 hPidx
  have hUcard : Nat.card U = 2 ^ n := by
    rw [← hUP, Subgroup.card_map_of_injective hψi, ← hg, Timmesfeld75.card_conjSubgroup,
      Timmesfeld75.card_utri, hK]
  have hUe : IsElemAbelian 2 U := by
    rw [← hUP, ← hg]
    exact isElemAbelian_map' ψ
      (Timmesfeld75.isElemAbelian_conjSubgroup Timmesfeld75.isElemAbelian_utri g)
  have hU1 : U ≠ ⊥ := by
    intro h0
    have h1 : Nat.card U = 1 := by rw [h0, Subgroup.card_bot]
    have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    rw [h1] at hUcard
    exact absurd hUcard h2.ne
  have huniq : ∀ x : G, A1b.conjSub x U ≤ T → A1b.conjSub x U = U := by
    intro x hx
    have hxL : A1b.conjSub x U ≤ L := by
      rintro _ ⟨u, hu, rfl⟩
      show x * u * x⁻¹ ∈ L
      exact hLn.conj_mem u hu.2 x
    refine Subgroup.eq_of_le_of_card_ge (le_inf hx hxL) ?_
    rw [show A1b.conjSub x U = cjS x U from rfl, Timmesfeld75.card_conjSubgroup]
  have hgen : ∀ l ∈ L, A1b.conjSub l U ≠ U → L ≤ U ⊔ A1b.conjSub l U := by
    intro l hl hne
    set M : SL(2, K) := e ⟨l, hl⟩ with hM
    have hψM : ψ M = l := by simp [hψdef, hM]
    have hcU : A1b.conjSub l U = (cjS M P).map ψ := by
      rw [map_conjSubgroup, hψM, hUP]
    have hMP : cjS M P ≠ P := fun hc => hne (by rw [hcU, hc, hUP])
    rw [← hg] at hMP
    have htop := sup_conj_eq_top_of_ne hMP
    rw [hcU, ← hUP, ← Subgroup.map_sup, ← hg, htop, ← MonoidHom.range_eq_map, hψr]
  refine le_nParam_of_almostSimple h ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
    hLT inf_le_left le_rfl inf_le_right hUe hU1 hUcard hn
    (fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv => B2F.isElemAbelian_comm hUe hv hu)
    huniq le_normalizer_inf le_rfl hgen

theorem le_nParam_of_isPSL22 {T : Subgroup G} {n : ℕ}
    (hL : IsPSL 2 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := exists_sl2_of_isPSL22 hL
  have hnab : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := sl2_nonabelian (K := K)
    refine ⟨e.symm x, e.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e hc
  exact le_nParam_of_sl2 (almostSimple_generalizedFitting hs hnab hT.1 hFT) hT hFT e hK hn

end Transport

end CFSG.Quasithin.Vol2.Ch11.SecE3
