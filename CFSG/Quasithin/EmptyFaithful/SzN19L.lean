module

public import CFSG.Quasithin.EmptyFaithful.SzN19List
public import CFSG.Quasithin.EmptyFaithful.SzN19Sel
public import CFSG.Quasithin.EmptyFaithful.SzN19Par
public import CFSG.Quasithin.EmptyFaithful.SzN19Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D
open scoped commutatorElement Pointwise

namespace SzN19

section Y0

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem exists_pow_Y0 (hc2 : Case157Two T Mc M) {x : G} (hx : x ∈ Y0 T Mc M) :
    ∃ k : ℕ, x ^ (2 ^ k * 3) = 1 := by
  have hxY : x ∈ Y153 Mc M := ((Y0_le T Mc M) hx).1
  have hq : (QuotientGroup.mk (⟨x, hxY⟩ : ↥(Y153 Mc M)) : OTwoQuot (Y153 Mc M)) ^ 3 = 1 :=
    hc2.1.2.2 _
  rw [← QuotientGroup.mk_pow] at hq
  have hmem : x ^ 3 ∈ pCoreOf 2 (Y153 Mc M) := by
    have := (mk_eq_one_iff_mem_pCoreOf _).mp hq
    simpa using this
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (Y153 Mc M) ⟨x ^ 3, hmem⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  rw [mul_comm, pow_mul]
  simpa using this

end Y0

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G}

theorem listL_of_k
    (h113 : StageLemma14113) (h56 : AsB56) (hb : InspBase cx H)
    {W : Subgroup G} {B : Subgroup (MulAut (UTil T M V₁ H))} {od : OffData hb W B} {L : Subgroup G}
    (lctx : LCtx hb od L) (hk : Y0 T Mc M ≤ conjClosure L T)
    (hE : ∀ e : ℕ, 1 < e → ¬ IsLieOver2e ↥(StarOf T M V₁ H L) e) : ListL T Mc M V₁ H L := by
  classical
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  obtain ⟨A, hAH, hAn, hLcomp, hLmem, hcases⟩ := star_setup h56 hb lctx
  have hLH : L ≤ H := (le_of_mem_cComp hLcomp).trans (preStar_le h A)
  have hTH : T ≤ H := h.T_le_H
  have hY0H : Y0 T Mc M ≤ H := S153L.Y0_le_H hb
  have hLT : T ≤ Subgroup.normalizer (L : Set G) := T_le_normalizer_of_k h113 h56 hb lctx hk
  have heq : conjClosure L T = L := conjClosure_eq_of_k h113 h56 hb lctx hk
  have hY0L : Y0 T Mc M ≤ L := hk.trans (le_of_eq heq)
  have hHeq : H = L ⊔ T := by
    calc H = conjClosure L T ⊔ Y0 T Mc M ⊔ T := lctx.eq
      _ = L ⊔ Y0 T Mc M ⊔ T := by rw [heq]
      _ = L ⊔ T := by rw [sup_eq_left.mpr hY0L]
  have hLs : StarOf T M V₁ H L = starOfSub h L := starOf_eq_starOfSub cx hb hLH
  have hTL : T ⊓ L ≤ H := inf_le_left.trans hTH
  have hPs : StarOf T M V₁ H (Y0 T Mc M ⊔ (T ⊓ L)) = starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) :=
    starOf_eq_starOfSub cx hb (sup_le hY0H hTL)
  obtain ⟨hq, hl⟩ := list_of_mem_cComp hcases hLmem
  have hlie : IsListL ↥(starOfSub h L) := by
    refine isListL_of_b56 hq hl ?_
    rwa [hLs] at hE
  have hTM : T ≤ Subgroup.normalizer (Y0 T Mc M : Set G) :=
    cx.c.hyp.T_le.trans (le_normalizer_Y0 cx.c.hyp)
  have hTY := starOfSub_le_normalizer h hTM
  have hTN := starOfSub_le_normalizer h hLT
  have hTs : IsSylowTwoOf (starOfSub h T) (starOfSub h H) := by
    have := isSylowTwoOf_starOfSub_T h
    rwa [← starOfSub_H h] at this
  have hLHs : starOfSub h L ≤ starOfSub h H := starOfSub_mono h hLH
  have hHNS : starOfSub h H ≤ starOfSub h L ⊔ starOfSub h T := by
    rw [congrArg (starOfSub h) hHeq, starOfSub_sup h hLH hTH]
  have hSyl : IsSylowTwoOf (starOfSub h T ⊓ starOfSub h L) (starOfSub h L) :=
    isSylowTwoOf_inf_of_normalizes hTs hLHs hTN hHNS
  have hTL' : starOfSub h (T ⊓ L) = starOfSub h T ⊓ starOfSub h L :=
    le_antisymm (le_inf (starOfSub_mono h inf_le_left) (starOfSub_mono h inf_le_right))
      (starOfSub_inf_le h (IsSylowTwoOf.pCoreOf_le h.sylow_H))
  have hYL : starOfSub h (Y0 T Mc M) ≤ starOfSub h L := starOfSub_mono h hY0L
  have hord : ∀ y ∈ starOfSub h (Y0 T Mc M), ∃ k : ℕ, y ^ (2 ^ k * 3) = 1 := by
    intro y hy
    obtain ⟨x, hxY, rfl⟩ := (mem_starOfSub h).mp hy
    obtain ⟨k, hk'⟩ := exists_pow_Y0 cx.case2 hxY
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (x : ↥H) ^ (2 ^ k * 3) = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have third : ((∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧
        Nonempty (↥(starOfSub h L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)))) ∨
      IsAlt 6 ↥(starOfSub h L) ∨ IsG2TwoDerived ↥(starOfSub h L)) →
      IsMinParabolicOf (starOfSub h L)
        (starOfSub h (Y0 T Mc M) ⊔ (starOfSub h T ⊓ starOfSub h L)) := fun hl' =>
    isMinParabolicOf_of_selfNormalizing hSyl hYL
      ((inf_le_left : starOfSub h T ⊓ starOfSub h L ≤ starOfSub h T).trans hTY)
      hord (exists_orderThree_star hb lctx) (fun E hE hE3 => S153L.hY3_star hb hE hE3)
      (normalizer_inf_le_of_list hSyl hl')
  refine ⟨heq, by rwa [hLs], ?_⟩
  rw [hLs, hPs, starOfSub_sup h hY0H hTL, hTL']
  rcases hlie with hl' | h6 | hhat | h7 | hg2
  · exact Or.inr (Or.inr (third (Or.inl hl')))
  · exact Or.inr (Or.inr (third (Or.inr (Or.inl h6))))
  · exact Or.inr (Or.inl hhat)
  · exact Or.inl h7
  · exact Or.inr (Or.inr (third (Or.inr (Or.inr hg2))))

end Main

theorem input49L_holds
    (h113 : StageLemma14113) (h56 : AsB56) : S1549C.Input49L := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od L lctx hk hE
  exact listL_of_k h113 h56 hb lctx hk hE

end SzN19

end CFSG.Quasithin
