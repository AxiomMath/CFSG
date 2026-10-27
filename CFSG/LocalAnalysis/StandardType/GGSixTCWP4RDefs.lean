module

public import Certificates.Data.TcRes
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel)

structure TcrSpec (S : TcrSys) : Prop where
  f1 : ∀ j < S.rank, tcrBasisV S.rank j ∈ S.roots.toList
  f2 : ∀ r ∈ S.roots.toList, ∀ i < S.rank, tcrReflV S.cartan S.rank i r ∈ S.roots.toList
  f3 : ∀ i < S.tcrN, ∀ j < S.tcrN, i = j ∨ S.roots[i]! ≠ S.roots[j]!
  sz : S.ip.size = S.tcrN ∧ S.neg.size = S.tcrN ∧ S.refl.size = S.tcrN ∧ S.basis.size = S.rank ∧
    S.posFlag.size = S.tcrN ∧ S.adj.size = S.tcrN ∧ S.par.size = S.tcrN
  f11 : ∀ i < S.tcrN, S.ip[i]!.size = S.tcrN ∧
    ∀ j < S.tcrN, (S.ip[i]!)[j]! = tcrFormL S.cartan S.rank S.roots[i]! S.roots[j]!
  f12 : ∀ i < S.tcrN, S.neg[i]! < S.tcrN ∧ S.roots[S.neg[i]!]! = S.roots[i]!.map (fun x => - x)
  f13 : ∀ g < S.tcrN, S.refl[g]!.size = S.tcrN ∧ ∀ v < S.tcrN, (S.refl[g]!)[v]! < S.tcrN ∧
    S.roots[(S.refl[g]!)[v]!]! = tcrVsubmul S.roots[v]! (S.ip[v]!)[g]! S.roots[g]!
  f14 : ∀ j < S.rank, S.basis[j]! = j ∧ S.roots[j]! = tcrBasisV S.rank j
  f15 : ∀ i < S.tcrN, S.posFlag[i]! = S.roots[i]!.all (fun x => decide (0 ≤ x))
  f16 : ∀ i < S.tcrN, S.adj[i]! = (List.range S.tcrN).filter fun j => (S.ip[i]!)[j]! != 0
  f17 : ∀ i < S.tcrN, i < S.rank ∨
    (S.par[i]!.1 < i ∧ S.par[i]!.2 < S.rank ∧ (S.refl[S.basis[S.par[i]!.2]!]!)[S.par[i]!.1]! = i)

@[expose] def TcrGen (τ : Tag) (r : List Int) : Prop :=
  ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ r = List.ofFn γ

structure TcrGood (τ : Tag) (S : TcrSys) : Prop where
  rank : S.rank = τ.rank
  cartan : ∀ i j : Fin τ.rank, S.cartan[τ.rank * i.val + j.val]! = τ.cartan i j
  spec : TcrSpec S
  gen : ∀ r ∈ S.roots.toList, TcrGen τ r
  sym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.cartan i j
  sym1 : ∀ i : Fin τ.rank, τ.symmetrizer i i = 1

@[expose] def tcrRv (S : TcrSys) (τ : Tag) (i : ℕ) : Fin τ.rank → ℤ :=
  fun j => (S.roots[i]!).getD j.val 0

@[expose] def tcChiQ (τ : Tag) (p : ℕ) (Q : Set (Fin τ.rank → ZMod p)) :
    Multiplicative (Fin τ.rank → ℤ) →* Multiplicative (Q → ZMod p) where
  toFun γ := Multiplicative.ofAdd fun v =>
    ∑ k, ((Multiplicative.toAdd γ k : ℤ) : ZMod p) * (v : Fin τ.rank → ZMod p) k
  map_one' := by
    ext v
    simp
  map_mul' γ δ := by
    ext v
    simp [add_mul, Finset.sum_add_distrib]

abbrev tcChiPl (τ : Tag) (p : ℕ) (P : Submodule (ZMod p) (Fin τ.rank → ZMod p)) :=
  tcChiQ τ p (P : Set (Fin τ.rank → ZMod p))

abbrev tcChiLn (τ : Tag) (p : ℕ) (x : Fin τ.rank → ZMod p) :=
  tcChiQ τ p ({x} : Set (Fin τ.rank → ZMod p))

@[expose] def tcrKindOfK : TwistKind → TcrKind
  | .inner => .inner | .suN => .suN | .twoD => .twoD | .exc => .exc

@[expose] def TcDataOK {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (d : TcrCData) : Prop :=
  d.e = componentOrbitLength ρ Ψ ∧ d.r = compRank Ψ ∧ d.N = Ψ.ncard ∧
    tcrKindOfK (twistKindOf ρ Ψ) ∈ d.ks

@[expose] noncomputable def LabAt {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (F : ℕ)
    (Ψ : Set (Fin τ.rank → ℤ)) : LargeEvenLabel :=
  componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ) (componentOrbitLength ρ Ψ * F)

@[expose] def FlagTransfer (p F f' : ℕ) : Prop :=
  ∀ d : TcrCData,
    ((tcrLabsOf d F).any (tcrSplitT p) = true → (tcrLabsOf d f').any (tcrSplitT p) = true) ∧
    ((tcrLabsOf d F).any (tcrHalfSplitT p) = true →
      (tcrLabsOf d f').any (tcrHalfSplitT p) = true) ∧
    ∀ d2 : TcrCData, (tcrLabsOf d2 F).any (fun l => (tcrLabsOf d F).contains l) = true →
      (tcrLabsOf d2 f').any (fun l => (tcrLabsOf d f').contains l) = true

end CFSG.StandardType.TableCRes

end
