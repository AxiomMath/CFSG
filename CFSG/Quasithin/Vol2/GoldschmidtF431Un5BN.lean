module

public import CFSG.GH74.GLS.SP.DatumBN
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GroupActions CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
open scoped Pointwise

theorem card_coxeterMatrix_cartan_five :
    Nat.card (coxeterMatrix (isFiniteType_cartan 5)).Group = 8 := by
  have h01 : Unitary.cartan 5 0 1 = -1 := by decide
  have h10 : Unitary.cartan 5 1 0 = -2 := by decide
  have hM : (coxeterMatrix (isFiniteType_cartan 5)).M 0 1 = 4 := by
    simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, h01, h10]
    norm_num
  have h := card_coxeterGroup_fin_two (coxeterMatrix (isFiniteType_cartan 5))
  omega

section Concrete

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) (ζ : traceZero (unitaryInvolution F p f))
  [hζ : Fact ((ζ : F) ≠ 0)]

theorem un5_isCTGroupDatum : IsCTGroupDatum (coxeterMatrix (isFiniteType_cartan 5)).toCoxeterSystem
    (weylAction (isFiniteType_cartan 5)) (roots (isFiniteType_cartan 5) (divisible 5))
    (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 5)
    (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F p f)) :=
  isCTGroupDatum hF 5 (by norm_num) ζ hζ.out

theorem un5B_inf_N : unB hF 5 ⊓ unN hF 5 ζ = unT (F := F) (p := p) (f := f) 5 :=
  borel_inf_weylN (un5_isCTGroupDatum hF ζ) (steinbergExtras hF 5 (by norm_num) ζ hζ.out)

instance un5Cartan_normal : (cartan (unB hF 5) (unN hF 5 ζ)).Normal :=
  cartan_normal_of_datum (D := rootDatum hF 5) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ.out)

abbrev un5NRep (i : Fin 2) : unN hF 5 ζ :=
  ⟨levelWeyl (unitaryInvolution_involutive hF) ζ i,
    n_mem_weylN (D := rootDatum hF 5) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
      (H := levelTorus (unitaryInvolution F p f)) i⟩

noncomputable def un5WeylEquiv :
    WeylGroup (unB hF 5) (unN hF 5 ζ) ≃* (coxeterMatrix (isFiniteType_cartan 5)).Group :=
  weylEquiv (D := rootDatum hF 5) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ.out) (hN := un5Cartan_normal hF ζ)

theorem un5WeylEquiv_NRep (i : Fin 2) :
    un5WeylEquiv hF ζ ((un5NRep hF ζ i : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ)) =
      (coxeterMatrix (isFiniteType_cartan 5)).toCoxeterSystem.simple i :=
  weylEquiv_n (D := rootDatum hF 5) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ.out) (_hN := un5Cartan_normal hF ζ) i

theorem un5NRep_ne : ((un5NRep hF ζ 0 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ)) ≠
    ((un5NRep hF ζ 1 : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ)) := by
  intro h
  have h' := congrArg (un5WeylEquiv hF ζ) h
  rw [un5WeylEquiv_NRep, un5WeylEquiv_NRep] at h'
  exact absurd ((coxeterMatrix (isFiniteType_cartan 5)).toCoxeterSystem.simple_injective h')
    (by decide)

theorem card_weyl_un5 : Nat.card (WeylGroup (unB hF 5) (unN hF 5 ζ)) = 8 := by
  rw [Nat.card_congr (un5WeylEquiv hF ζ).toEquiv]
  exact card_coxeterMatrix_cartan_five

theorem un5ActsAs {i : Fin 2} {m : unN hF 5 ζ}
    (h : (m : WeylGroup (unB hF 5) (unN hF 5 ζ)) =
      ((un5NRep hF ζ i : unN hF 5 ζ) : WeylGroup (unB hF 5) (unN hF 5 ζ))) :
    ActsAs (rootDatum hF 5) (m : SU (unitaryInvolution F p f) 5)
      ((coxeterMatrix (rootDatum hF 5).isFiniteType).toCoxeterSystem.simple i) :=
  actsAs_of_mk_eq (D := rootDatum hF 5) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ.out) (_hN := un5Cartan_normal hF ζ) h

end Concrete

end CFSG.Quasithin.H13.F431.Un
