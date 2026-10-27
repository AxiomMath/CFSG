module

public import CFSG.GH74.GLS.SP.SpBN
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GroupActions CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
open scoped Pointwise

theorem card_coxeterMatrix_cartan_four :
    Nat.card (coxeterMatrix (isFiniteType_cartan 4)).Group = 8 :=
  card_coxeterMatrix_cartanC_two

section Concrete

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) (ζ : traceZero (unitaryInvolution F p f))
  [hζ : Fact ((ζ : F) ≠ 0)]

theorem un_isCTGroupDatum : IsCTGroupDatum (coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem
    (weylAction (isFiniteType_cartan 4)) (roots (isFiniteType_cartan 4) (divisible 4))
    (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4)
    (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F p f)) :=
  isCTGroupDatum hF 4 (by norm_num) ζ hζ.out

theorem unB_inf_unN : unB hF 4 ⊓ unN hF 4 ζ = unT (F := F) (p := p) (f := f) 4 :=
  borel_inf_weylN (un_isCTGroupDatum hF ζ) (steinbergExtras hF 4 (by norm_num) ζ hζ.out)

instance unCartan_normal : (cartan (unB hF 4) (unN hF 4 ζ)).Normal :=
  cartan_normal_of_datum (D := rootDatum hF 4) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un_isCTGroupDatum hF ζ)
    (steinbergExtras hF 4 (by norm_num) ζ hζ.out)

abbrev unNRep (i : Fin 2) : unN hF 4 ζ :=
  ⟨levelWeyl (unitaryInvolution_involutive hF) ζ i,
    n_mem_weylN (D := rootDatum hF 4) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
      (H := levelTorus (unitaryInvolution F p f)) i⟩

noncomputable def unWeylEquiv :
    WeylGroup (unB hF 4) (unN hF 4 ζ) ≃* (coxeterMatrix (isFiniteType_cartan 4)).Group :=
  weylEquiv (D := rootDatum hF 4) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un_isCTGroupDatum hF ζ)
    (steinbergExtras hF 4 (by norm_num) ζ hζ.out) (hN := unCartan_normal hF ζ)

theorem unWeylEquiv_unNRep (i : Fin 2) :
    unWeylEquiv hF ζ ((unNRep hF ζ i : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ)) =
      (coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem.simple i :=
  weylEquiv_n (D := rootDatum hF 4) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un_isCTGroupDatum hF ζ)
    (steinbergExtras hF 4 (by norm_num) ζ hζ.out) (_hN := unCartan_normal hF ζ) i

theorem unNRep_ne : ((unNRep hF ζ 0 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ)) ≠
    ((unNRep hF ζ 1 : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ)) := by
  intro h
  have h' := congrArg (unWeylEquiv hF ζ) h
  rw [unWeylEquiv_unNRep, unWeylEquiv_unNRep] at h'
  exact absurd ((coxeterMatrix (isFiniteType_cartan 4)).toCoxeterSystem.simple_injective h')
    (by decide)

theorem card_weyl_un : Nat.card (WeylGroup (unB hF 4) (unN hF 4 ζ)) = 8 := by
  rw [Nat.card_congr (unWeylEquiv hF ζ).toEquiv]
  exact card_coxeterMatrix_cartan_four

theorem unActsAs {i : Fin 2} {m : unN hF 4 ζ}
    (h : (m : WeylGroup (unB hF 4) (unN hF 4 ζ)) =
      ((unNRep hF ζ i : unN hF 4 ζ) : WeylGroup (unB hF 4) (unN hF 4 ζ))) :
    ActsAs (rootDatum hF 4) (m : SU (unitaryInvolution F p f) 4)
      ((coxeterMatrix (rootDatum hF 4).isFiniteType).toCoxeterSystem.simple i) :=
  actsAs_of_mk_eq (D := rootDatum hF 4) (n := levelWeyl (unitaryInvolution_involutive hF) ζ)
    (H := levelTorus (unitaryInvolution F p f)) (un_isCTGroupDatum hF ζ)
    (steinbergExtras hF 4 (by norm_num) ζ hζ.out) (_hN := unCartan_normal hF ζ) h

end Concrete

end CFSG.Quasithin.H13.F431.Un
