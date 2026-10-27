module

public import CFSG.Quasithin.EmptyFaithful.SzN20Rk2
public import CFSG.Quasithin.Background.S1549EB
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SzN19Ctx
public import CFSG.Quasithin.EmptyFaithful.SzN19Par
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D
open scoped commutatorElement Pointwise

namespace SzN20

@[expose] def RankTwoBorel : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (X S : Subgroup Ω) (e : ℕ), 2 ≤ e →
    ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
        Nonempty (↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K))) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
        Nonempty (↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K))) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
        Nonempty (↥X ≃* ↥(CFSG.Open.quasithinG2 K)))) →
    IsSylowTwoOf S X →
      S ≠ ⊥ ∧
      (∀ R : Subgroup Ω, S ≤ R → R ≤ X → Group.IsSolvable ↥R →
        R ≤ Subgroup.normalizer (S : Set Ω)) ∧
      ((∃ y ∈ Subgroup.normalizer (S : Set Ω) ⊓ X, orderOf y = 3) →
        ∃ E : Subgroup Ω, E ≤ Subgroup.normalizer (S : Set Ω) ⊓ X ∧ IsPGroup 3 E ∧
          (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9)

section Inf

variable {Ω : Type*} [Group Ω]

theorem le_normalizer_inf {T N : Subgroup Ω} (hTN : T ≤ Subgroup.normalizer (N : Set Ω)) :
    T ≤ Subgroup.normalizer ((T ⊓ N : Subgroup Ω) : Set Ω) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ s ∈ T, ∀ x ∈ T ⊓ N, s * x * s⁻¹ ∈ T ⊓ N := fun s hs x hx =>
    ⟨T.mul_mem (T.mul_mem hs hx.1) (T.inv_mem hs),
      (Subgroup.mem_normalizer_iff.mp (hTN hs) x).mp hx.2⟩
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

end Inf

section Main

theorem eRankOne_of_borel (h113 : StageLemma14113) (h56 : AsB56) (hB : RankTwoBorel) :
    S1549E.ERankOne := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od L lctx hk e he hLie
  refine ⟨SzN19.conjClosure_eq_of_k h113 h56 hb lctx hk, ?_⟩
  rcases hLie with ⟨K, hKf, hKfin, hK, ⟨iso⟩⟩ | hrest
  · exact ⟨K, hKf, hKfin, hK, ⟨iso⟩⟩
  · exfalso
    classical
    have h := hb.hF98.toHypF91
    let _ : CommGroup (UTil T M V₁ H) := modInst h
    obtain ⟨A, hAH, hAn, hLcomp, hLmem, hcases⟩ := SzN19.star_setup h56 hb lctx
    have hLH : L ≤ H := (le_of_mem_cComp hLcomp).trans (preStar_le h A)
    have hTH : T ≤ H := h.T_le_H
    have hY0H : Y0 T Mc M ≤ H := S153L.Y0_le_H hb
    have hLT : T ≤ Subgroup.normalizer (L : Set G) := SzN19.T_le_normalizer_of_k h113 h56 hb lctx hk
    have heq : conjClosure L T = L := SzN19.conjClosure_eq_of_k h113 h56 hb lctx hk
    have hY0L : Y0 T Mc M ≤ L := hk.trans (le_of_eq heq)
    have hHeq : H = L ⊔ T := by
      calc H = conjClosure L T ⊔ Y0 T Mc M ⊔ T := lctx.eq
        _ = L ⊔ Y0 T Mc M ⊔ T := by rw [heq]
        _ = L ⊔ T := by rw [sup_eq_left.mpr hY0L]
    have hLs : StarOf T M V₁ H L = starOfSub h L := starOf_eq_starOfSub cx hb hLH
    rw [hLs] at hrest
    have hTM : T ≤ Subgroup.normalizer (Y0 T Mc M : Set G) :=
      cx.c.hyp.T_le.trans (le_normalizer_Y0 cx.c.hyp)
    have hTY := SzN19.starOfSub_le_normalizer h hTM
    have hTN := SzN19.starOfSub_le_normalizer h hLT
    have hYs : Group.IsSolvable ↥(starOfSub h (Y0 T Mc M)) :=
      S153L.isSolvable_starOfSub h hY0H
        (S153D.isSolvable_of_le_Y153 h113 cx.c.hyp ((Y0_le T Mc M).trans inf_le_left))
    have hTHs : starOfSub h T ≤ starOfSub h H := starOfSub_mono h hTH
    have hTs : IsSylowTwoOf (starOfSub h T) (starOfSub h H) := by
      have := isSylowTwoOf_starOfSub_T h
      rwa [← starOfSub_H h] at this
    have hLHs : starOfSub h L ≤ starOfSub h H := starOfSub_mono h hLH
    have hHNS : starOfSub h H ≤ starOfSub h L ⊔ starOfSub h T := by
      rw [congrArg (starOfSub h) hHeq, starOfSub_sup h hLH hTH]
    have hSyl : IsSylowTwoOf (starOfSub h T ⊓ starOfSub h L) (starOfSub h L) :=
      SzN19.isSylowTwoOf_inf_of_normalizes hTs hLHs hTN hHNS
    have hmin : ∀ K' : Subgroup (MulAut (UTil T M V₁ H)),
        starOfSub h (Y0 T Mc M) ⊔ starOfSub h T ≤ K' → K' ≤ starOfSub h H →
          K' ≠ starOfSub h H → K' ≤ starOfSub h (M ⊓ H) := fun K' h1 h2 h3 => by
      refine overgroup_le_M_of_minimal cx hb ?_ h2 h3
      rwa [starOfSub_sup h hY0H hTH]
    obtain ⟨hS1, ha, hb'⟩ := hB _ (starOfSub h L)
      (starOfSub h T ⊓ starOfSub h L) e he hrest hSyl
    exact rank_two_false hLHs hTHs (pCoreOf_starOfSub_H h) hSyl hS1
      (le_normalizer_inf hTN)
      (starOfSub_mono h hY0L)
      ((inf_le_left : starOfSub h T ⊓ starOfSub h L ≤ starOfSub h T).trans hTY)
      hYs hmin (fun x hx hx3 => S153L.theta_star hb hx3 hx)
      (fun E hE hE3 => S153L.hY3_star hb hE hE3) (SzN19.exists_orderThree_star hb lctx) ha hb'

end Main

end SzN20

end CFSG.Quasithin
