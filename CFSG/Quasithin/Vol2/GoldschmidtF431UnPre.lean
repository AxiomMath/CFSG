module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnBN
public import CFSG.GH74.BNPair.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnRootsNil
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnRootsOct
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnRootsWeyl

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GroupActions CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
open scoped Pointwise

section Pre

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) (ζ : traceZero (unitaryInvolution F p f))
  [hζ : Fact ((ζ : F) ≠ 0)]

theorem unSplitBN : SplitBN (unB hF 4) (unN hF 4 ζ) (unU hF 4) (unNRep hF ζ) :=
  splitBN_of_datum (D := rootDatum hF 4) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un_isCTGroupDatum hF ζ)
    (steinbergExtras hF 4 (by norm_num) ζ hζ.out) (isNilpotent_unU hF)

open Classical in
theorem unIsTitsSystem :
    IsTitsSystem (unB hF 4) (unN hF 4 ζ)
      {((unNRep hF ζ 0 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ)),
        ((unNRep hF ζ 1 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ))} := by
  obtain ⟨S, hS, hSrange⟩ := SplitBN.isTitsSystem (unSplitBN hF ζ)
  have hSeq : S = {((unNRep hF ζ 0 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ)),
      ((unNRep hF ζ 1 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ))} := by
    apply Finset.coe_injective
    rw [hSrange]
    ext x
    simp only [Set.mem_range, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  rwa [hSeq] at hS

theorem unIsSaturated : IsSaturated (unB hF 4) (unN hF 4 ζ) :=
  isSaturated_of_datum (D := rootDatum hF 4) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un_isCTGroupDatum hF ζ)
    (steinbergExtras hF 4 (by norm_num) ζ hζ.out)
    (CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ.out)

theorem unB_eq_mul :
    ((unB hF 4 : Subgroup (SU (unitaryInvolution F p f) 4)) : Set (SU (unitaryInvolution F p f) 4))
      = ((unB hF 4 ⊓ unN hF 4 ζ : Subgroup _) : Set _) * ((unU hF 4 : Subgroup _) : Set _) :=
  borel_eq_mul_of_datum (D := rootDatum hF 4)
    (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un_isCTGroupDatum hF ζ)
    (steinbergExtras hF 4 (by norm_num) ζ hζ.out)

theorem unIsSplit : IsSplit (unB hF 4) (unN hF 4 ζ) (unU hF 4) :=
  ⟨isNilpotent_unU hF, unB_eq_mul hF ζ⟩

abbrev unW₁ : WeylGroup (unB hF 4) (unN hF 4 ζ) :=
  ((unNRep hF ζ 0 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ))

abbrev unW₂ : WeylGroup (unB hF 4) (unN hF 4 ζ) :=
  ((unNRep hF ζ 1 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ))

theorem unRootGroupSystem :
    IsRootGroupSystem (unB hF 4) (unN hF 4 ζ) (unW₁ hF ζ) (unW₂ hF ζ) (unU hF 4) 4 (unOct hF) where
  ne_bot := (unOctagon hF).ne_bot
  invariant i hi h hh x hx :=
    (unOctagon hF).invariant i hi h (by rwa [unB_inf_unN hF ζ] at hh) x hx
  carrier_eq := (unOctagon hF).carrier_eq
  unique := (unOctagon hF).unique
  reverse_eq := (unOctagon hF).reverse_eq
  subgroup := (unOctagon hF).subgroup
  action₁ m hm := by
    obtain ⟨a1, a2, a3⟩ := unAction₁ hF (unActsAs hF ζ (i := 0) hm)
    exact ⟨a1, a2, fun i h2 h4 => a3 i h2 (by exact_mod_cast h4)⟩
  action₂ m hm := unAction₂' hF (unActsAs hF ζ (i := 1) hm)
  meet_one := (unOctagon hF).meet_one

@[expose] def unPre : PreRankTwoSystem (SU (unitaryInvolution F p f) 4) 4 where
  B := unB hF 4
  N := unN hF 4 ζ
  w₁ := unW₁ hF ζ
  w₂ := unW₂ hF ζ
  U := unU hF 4
  root := unOct hF
  isTits := unIsTitsSystem hF ζ
  w₁_ne_w₂ := unNRep_ne hF ζ
  isSplit := unIsSplit hF ζ
  isSaturated := unIsSaturated hF ζ
  card_weyl := by rw [card_weyl_un hF ζ]
  three_le := by norm_num
  roots := unRootGroupSystem hF ζ

end Pre

end CFSG.Quasithin.H13.F431.Un
