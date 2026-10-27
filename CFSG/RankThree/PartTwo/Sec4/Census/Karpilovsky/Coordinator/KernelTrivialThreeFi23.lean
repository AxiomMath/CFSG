module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.Sporadic.Fi23.Simple
public import Certificates.Certificate291381
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Recognition.CoverCubeTransfer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.AGLEmbedding
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary CFSG.CosetTable
  CFSG.Sporadic.Recognition.CoverRecipe

theorem ker_eq_bot_of_cover3_card {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    {R : List (List (Fin m × Bool))} {cw : Fin m → List (Fin m × Bool)} {ord : Fin m → ℕ}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hA : ∀ i, ord i = 0 → FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)) ∧
      FreeGroup.lift g (FreeGroup.mk (cw i)) = g i)
    (hB : ∀ i, ord i ≠ 0 → cw i = [(i, true)] ∧ g i ^ ord i = 1 ∧ (ord i).Coprime 3)
    {n : ℕ} (hfin : Finite (PG m (cover₃Words R cw ord)))
    (hle : Nat.card (PG m (cover₃Words R cw ord)) ≤ n)
    (hge : n ≤ Nat.card (Subgroup.closure (Set.range g)))
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G)
    (hπ : Function.Surjective π) (hsyl : (Nat.card G).factorization 3 ≤ n.factorization 3)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  classical
  set N : Subgroup G := Subgroup.closure (Set.range g) with hN
  let gX : Fin m → N := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hcl : Subgroup.closure (Set.range gX) = ⊤ := closure_range_codRestrict g
  have hlift : ∀ w, ((FreeGroup.lift gX w : N) : G) = FreeGroup.lift g w :=
    coe_lift_codRestrict g
  have hR' : ∀ r ∈ R, FreeGroup.lift gX (FreeGroup.mk r) = 1 := fun r hr =>
    Subtype.ext (by rw [hlift, hR r hr]; rfl)
  have hA' : ∀ i, ord i = 0 → FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)) ∧
      FreeGroup.lift gX (FreeGroup.mk (cw i)) = gX i := fun i hi =>
    ⟨(hA i hi).1, Subtype.ext (by rw [hlift, (hA i hi).2])⟩
  have hB' : ∀ i, ord i ≠ 0 → cw i = [(i, true)] ∧ gX i ^ ord i = 1 ∧ (ord i).Coprime 3 :=
    fun i hi => ⟨(hB i hi).1, Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact (hB i hi).2.1), (hB i hi).2.2⟩
  have := hfin
  have hge' : Nat.card N ≤ Nat.card (PG m (cover₃Words R cw ord)) :=
    card_le_card_cover₃ hcl hR' (fun i => by
      by_cases h0 : ord i = 0
      · exact (hA' i h0).2
      · rw [(hB' i h0).1, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
          FreeGroup.lift_apply_of]) (fun i hi => (hB' i hi).2.1)
  have hcardN : Nat.card N = n := le_antisymm (hge'.trans hle) hge
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.2 hπ
  have hsylN : (Nat.card π.range).factorization 3 ≤ (Nat.card N).factorization 3 := by
    rw [hcardN, hrange, Subgroup.card_top]
    exact hsyl
  refine ker_eq_bot_of_sylow_subgroup π hC hp N (by rw [hrange]; exact le_top) hsylN ?_
  intro M _ _ φ hφ hc hpg hd
  exact ker_eq_bot_of_cover₃ (g := gX) (R := R) (cw := cw) (ord := ord) hcl hR' hA' hB'
    hfin (hle.trans hcardN.ge) φ hφ hc hpg hd

theorem fi23U3_ordF : ∀ i : Fin fi23U3Cover3.m, fi23U3Cover3.ordF i = 2 := by
  decide

theorem kernelTrivialAt_three_Fi23 :
    KernelTrivialAt (NativeSporadic.Carrier .Fi23) 3 := by
  have hcard : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  obtain ⟨⟨g, hR, hsq, hge⟩, hfin, hle⟩ := Certificates.certificate291381
  intro E _ _ _ π hπ hC hp
  refine ker_eq_bot_of_cover3_card g (R := fi23U3Cover3.rels) (cw := fi23U3Cover3.cwF)
    (ord := fi23U3Cover3.ordF) hR (fun i hi => absurd hi (by rw [fi23U3_ordF]; norm_num))
    (fun i _ => ⟨?_, by rw [fi23U3_ordF]; exact hsq i, by rw [fi23U3_ordF]; norm_num⟩)
    hfin hle hge π hπ ?_ hC hp
  · rw [Cover3Data.cwF, if_neg (by rw [fi23U3_ordF]; norm_num)]
  · change (Nat.card (NativeSporadic.Carrier .Fi23)).factorization 3 ≤ _
    rw [hcard, factorization_three_eq (a := 13) (b := 2 ^ 18 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23)
      (by norm_num) (by norm_num), factorization_three_eq (a := 13) (b := 2 ^ 2)
      (by norm_num) (by norm_num)]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
