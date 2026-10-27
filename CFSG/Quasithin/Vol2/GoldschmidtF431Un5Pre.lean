module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5BN
public import CFSG.GH74.BNPair.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Octagon
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5RootsNil
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5RootsWeyl

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

theorem un5SplitBN : SplitBN (unB hF 5) (unN hF 5 ζ) (unU hF 5) (un5NRep hF ζ) :=
  splitBN_of_datum (D := rootDatum hF 5) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ.out) (isNilpotent_unU5 hF)

open Classical in
theorem un5IsTitsSystem :
    IsTitsSystem (unB hF 5) (unN hF 5 ζ)
      {((un5NRep hF ζ 0 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ)),
        ((un5NRep hF ζ 1 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ))} := by
  obtain ⟨S, hS, hSrange⟩ := SplitBN.isTitsSystem (un5SplitBN hF ζ)
  have hSeq : S = {((un5NRep hF ζ 0 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ)),
      ((un5NRep hF ζ 1 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ))} := by
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

theorem un5IsSaturated : IsSaturated (unB hF 5) (unN hF 5 ζ) :=
  isSaturated_of_datum (D := rootDatum hF 5) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ.out)
    (CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ.out)

theorem un5B_eq_mul :
    ((unB hF 5 : Subgroup (SU (unitaryInvolution F p f) 5)) : Set (SU (unitaryInvolution F p f) 5))
      = ((unB hF 5 ⊓ unN hF 5 ζ : Subgroup _) : Set _) * ((unU hF 5 : Subgroup _) : Set _) :=
  borel_eq_mul_of_datum (D := rootDatum hF 5)
    (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ.out)

theorem un5IsSplit : IsSplit (unB hF 5) (unN hF 5 ζ) (unU hF 5) :=
  ⟨isNilpotent_unU5 hF, un5B_eq_mul hF ζ⟩

abbrev un5W₁ : WeylGroup (unB hF 5) (unN hF 5 ζ) :=
  ((un5NRep hF ζ 0 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ))

abbrev un5W₂ : WeylGroup (unB hF 5) (unN hF 5 ζ) :=
  ((un5NRep hF ζ 1 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ))

theorem un5RootGroupSystem :
    IsRootGroupSystem (unB hF 5) (unN hF 5 ζ) (un5W₁ hF ζ) (un5W₂ hF ζ) (unU hF 5) 4
      (un5Oct hF) where
  ne_bot := (un5Octagon hF).ne_bot
  invariant i hi h hh x hx :=
    (un5Octagon hF).invariant i hi h (by rwa [un5B_inf_N hF ζ] at hh) x hx
  carrier_eq := (un5Octagon hF).carrier_eq
  unique := (un5Octagon hF).unique
  reverse_eq := (un5Octagon hF).reverse_eq
  subgroup := (un5Octagon hF).subgroup
  action₁ m hm := by
    obtain ⟨a1, a2, a3⟩ := un5Action₁ hF (un5ActsAs hF ζ (i := 0) hm)
    exact ⟨a1, a2, fun i h2 h4 => a3 i h2 (by exact_mod_cast h4)⟩
  action₂ m hm := un5Action₂' hF (un5ActsAs hF ζ (i := 1) hm)
  meet_one := (un5Octagon hF).meet_one

@[expose] def un5Pre : PreRankTwoSystem (SU (unitaryInvolution F p f) 5) 4 where
  B := unB hF 5
  N := unN hF 5 ζ
  w₁ := un5W₁ hF ζ
  w₂ := un5W₂ hF ζ
  U := unU hF 5
  root := un5Oct hF
  isTits := un5IsTitsSystem hF ζ
  w₁_ne_w₂ := un5NRep_ne hF ζ
  isSplit := un5IsSplit hF ζ
  isSaturated := un5IsSaturated hF ζ
  card_weyl := by rw [card_weyl_un5 hF ζ]
  three_le := by norm_num
  roots := un5RootGroupSystem hF ζ

end Pre

end CFSG.Quasithin.H13.F431.Un
