module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Quasithin.Background.D2Fitting
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

section Count

variable {A : Type*} [Group A] [Finite A]

theorem r1613g_card_directProd_of_conj {X K N : Subgroup A} (h : IsDirectProdOfConj X K N)
    (hK : Nat.card K = 3) : Nat.card X = 3 ^ (conjSet K N).ncard := by
  classical
  haveI : Finite (conjSet K N) := Set.toFinite _
  haveI : Fintype (conjSet K N) := Fintype.ofFinite _
  let H : conjSet K N → Subgroup A := fun Y => (Y : Subgroup A)
  have hcard : ∀ Y : conjSet K N, Nat.card (H Y) = 3 := by
    rintro ⟨Y, n, -, rfl⟩
    show Nat.card ↥(K.map (MulAut.conj n).toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hK]
  have hcomm : Pairwise fun i j : conjSet K N => ∀ x y : A, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    have h1 : ⁅x, y⁆ ∈ ⁅(i : Subgroup A), (j : Subgroup A)⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    rw [h.2.2.1 i i.2 j j.2 (fun e => hij (Subtype.ext e)), Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hind : iSupIndep H := by
    intro i
    refine Disjoint.mono_right ?_ (disjoint_iff.2 (h.2.2.2 i i.2))
    refine iSup₂_le fun j hj => ?_
    exact le_iSup₂_of_le (j : Subgroup A) j.2 (le_iSup_of_le (fun e => hj (Subtype.ext e)) le_rfl)
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
  have hX : (⨆ i : conjSet K N, H i) = X := by
    rw [← h.2.1]
    exact iSup_subtype'' (conjSet K N) (fun Y => Y)
  have h1 : Nat.card (Subgroup.noncommPiCoprod hcomm).range = Nat.card (∀ i : conjSet K N, H i) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  rw [hrange, hX, Nat.card_pi] at h1
  rw [h1]
  simp only [hcard, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]

end Count

section Rank

variable {W : Type*} [CommGroup W] [Finite W]

theorem r1613g_rk_iSup_le {ι : Type*} [Fintype ι] (U : ι → Subgroup W) :
    rk ↥(⨆ i, U i) ≤ ∑ i, rk ↥(U i) := by
  classical
  have key : ∀ s : Finset ι, rk ↥(⨆ i ∈ s, U i) ≤ ∑ i ∈ s, rk ↥(U i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show (⨆ i ∈ (∅ : Finset ι), U i) = ⊥ from
        iSup_eq_bot.2 fun i => iSup_eq_bot.2 fun hi => absurd hi (Finset.notMem_empty i), rk_bot]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.iSup_insert]
      have h := rk_sup_add_rk_inf (U a) (⨆ i ∈ s, U i)
      omega
  have h := key Finset.univ
  rwa [show (⨆ i ∈ (Finset.univ : Finset ι), U i) = ⨆ i, U i from
    iSup_congr fun i => iSup_pos (Finset.mem_univ i)] at h

theorem r1613g_rk_commSub_directProd_le {X K N : Subgroup (MulAut W)}
    (h : IsDirectProdOfConj X K N) {m : ℕ} (hm : rk ↥(commSub ⊤ K) ≤ m) :
    rk ↥(commSub ⊤ X) ≤ (conjSet K N).ncard * m := by
  classical
  haveI : Finite (conjSet K N) := Set.toFinite _
  haveI : Fintype (conjSet K N) := Fintype.ofFinite _
  have hX : (⨆ i : conjSet K N, (i : Subgroup (MulAut W))) = X := by
    rw [← h.2.1]
    exact iSup_subtype'' (conjSet K N) (fun Y => Y)
  have hle : commSub ⊤ X ≤ ⨆ i : conjSet K N, commSub ⊤ (i : Subgroup (MulAut W)) := by
    rw [← commV_eq_commSub, ← hX]
    refine (commV_iSup_le (fun i : conjSet K N => (i : Subgroup (MulAut W)))).trans ?_
    exact iSup_mono fun i => (commV_eq_commSub _).le
  have hY : ∀ i : conjSet K N, rk ↥(commSub ⊤ (i : Subgroup (MulAut W))) ≤ m := by
    rintro ⟨Y, n, -, rfl⟩
    show rk ↥(commSub ⊤ (K.map (MulAut.conj n).toMonoidHom)) ≤ m
    rw [Asc81c.commSub_map_conj, s15_Lin_rk_map]
    exact hm
  calc rk ↥(commSub ⊤ X)
      ≤ rk ↥(⨆ i : conjSet K N, commSub ⊤ (i : Subgroup (MulAut W))) := rk_mono hle
    _ ≤ ∑ i : conjSet K N, rk ↥(commSub ⊤ (i : Subgroup (MulAut W))) :=
        r1613g_rk_iSup_le _
    _ ≤ ∑ _i : conjSet K N, m := Finset.sum_le_sum fun i _ => hY i
    _ = (conjSet K N).ncard * m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, Nat.card_coe_set_eq,
          smul_eq_mul]

end Rank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
