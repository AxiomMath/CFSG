module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType
open CFSG.Assembly
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def ggQTwoNbrJoinSup (Bs J K : Subgroup G) : Subgroup G :=
  ⨆ (n : G) (_ : n ∈ K) (_ : ∃ φ : MulAut ↥Bs,
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
    J.map (MulAut.conj n).toMonoidHom

structure QTwoNbrModel (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) where
  hJK : J ≤ K
  hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G))
  hKperf : commutator K = ⊤
  hxBs : x ∈ Bs
  hBsN : Bs ≤ Subgroup.normalizer (K : Set G)
  Delta : Subgroup G
  hDelta_le_K : Delta ≤ K
  hDelta_central : ∀ d ∈ Delta, ∀ k ∈ K, d * k = k * d
  hDelta_pgroup : IsPGroup 2 Delta
  Q : Type
  [groupQ : Group Q]
  q : ↥(K ⊔ Bs) →* Q
  hq_surj : Function.Surjective q
  hq_ker : q.ker = Delta.subgroupOf (K ⊔ Bs)
  F0 : Type
  [fieldF0 : Field F0]
  [finiteF0 : Finite F0]
  [charF0 : CharP F0 2]
  [factF0 : Fact (Nat.Prime 2)]
  hcardF0 : Nat.card F0 = 4
  d : ℕ
  hd : 5 ≤ d
  ψ : Su F0 2 1 d →* Q
  hψ_ker : ψ.ker ≤ Subgroup.center (Su F0 2 1 d)
  Kbar : Subgroup Q
  hKbar : Kbar = (q.comp (Subgroup.inclusion le_sup_left)).range
  As : Subgroup Q
  hAs : As = (q.comp (Subgroup.inclusion le_sup_right)).range
  hψ_range : ψ.range = Kbar
  hdiag : GGActsDiagonally (p := 2) (f := 1) ψ As
  Jbar : Subgroup Q
  hJbar : Jbar = ((q.comp (Subgroup.inclusion le_sup_left)).comp
    (Subgroup.inclusion hJK)).range
  xbar : Q
  hxbar : xbar = q ⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hxBs⟩
  CKbar : Subgroup Q
  hCKbar : CKbar = (q.comp (Subgroup.inclusion
    (show K ⊓ Subgroup.centralizer ({x} : Set G) ≤ K ⊔ Bs from
      le_trans inf_le_left le_sup_left))).range

@[expose] noncomputable def ggQTwoNbrCompProp {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel p B Bs x L D J y K) : Prop :=
  letI := hM.groupQ
  IsComponentOf hM.Jbar (hM.Kbar ⊓ Subgroup.centralizer ({hM.xbar} : Set hM.Q)) ∧
    ⁅hM.Kbar ⊓ Subgroup.centralizer ({hM.xbar} : Set hM.Q),
      hM.Kbar ⊓ Subgroup.centralizer ({hM.xbar} : Set hM.Q)⁆ ≤ hM.CKbar

@[expose] noncomputable def ggQTwoNbrBlockProp {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel p B Bs x L D J y K) : Prop :=
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  ∃ I : Finset (Fin hM.d), I.card = 4 ∧ (coordBlockSU hM.F0 2 1 I).map hM.ψ ≤ hM.Jbar

@[expose] noncomputable def ggQTwoNbrTransportProp {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel p B Bs x L D J y K) : Prop :=
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  ∃ I0 : Finset (Fin hM.d), I0.card = 4 ∧
    ∀ I : Finset (Fin hM.d), I.card = 4 →
      ∃ (n : G) (hn : n ∈ K), n ∈ Subgroup.normalizer (Bs : Set G) ∧
        (coordBlockSU hM.F0 2 1 I).map hM.ψ =
          ((coordBlockSU hM.F0 2 1 I0).map hM.ψ).map
            (MulAut.conj (hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩)).toMonoidHom

end CFSG.StandardType.QTwo

end
