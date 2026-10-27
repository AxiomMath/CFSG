module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1BABB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1BABC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_SL4MixedAux1
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_mixed_fpf
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
    {r : G} (hrM : r ∈ D.M) (hr3 : orderOf r = 3)
    (hmixed : s16h_SL4Mixed V L h.hyp151.isElemAbelian x r)
    (hrB : barSub ⊥ V h.hyp151.isElemAbelian (Subgroup.zpowers r) ≤
      lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x))
    {a b : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (haL : a ∈ lBar ⊥ V h.hyp151.isElemAbelian L)
    (hbLx : b ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x))
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    (∀ u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L),
        a u * u⁻¹ ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L) →
        u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
      (∀ u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)),
        b u * u⁻¹ ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L) →
        u ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  let Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV L
  let U₁ : Subgroup (Vtil ⊥ V hV) := commSub ⊤ Lb
  let Z : Subgroup (Vtil ⊥ V hV) := U₁ ⊓ fixV Lb
  let xbar : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨x, hMs hxM⟩
  have hrow' : s16h_H5RowSL2 Lb U₁ Z 2 := hrow
  constructor
  · exact s16h_sl4_fpf_of_row hrow' haL ha3 ha1
  · intro u hu huZ
    have hLx : Lb.map (MulAut.conj (xbar⁻¹)).toMonoidHom =
        lBar ⊥ V hV (conjSubgroup L x) := by
      show (lBar ⊥ V hV L).map (MulAut.conj (xbar⁻¹)).toMonoidHom =
        lBar ⊥ V hV (conjSubgroup L x)
      exact (s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L).symm
    have hUx : U₁.map (xbar⁻¹).toMonoidHom =
        commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x)) := by
      show (commSub ⊤ (lBar ⊥ V hV L)).map (xbar⁻¹).toMonoidHom =
        commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x))
      exact (s15_Infra_wTil_conjSubgroup ⊥ V L hV (hMs hxM)).symm
    have hb : b ∈ Lb.map (MulAut.conj (xbar⁻¹)).toMonoidHom := by
      rw [hLx]; exact hbLx
    have hZc : Z.map (xbar⁻¹).toMonoidHom = Z := by
      have hconjZ := s16h_sl4_mixed_Z_conj D h hxM (hMs hxM) hxn hZ0
      simpa only [Z, U₁, Lb, xbar, hV] using hconjZ
    have hu' : u ∈ U₁.map (xbar⁻¹).toMonoidHom := by
      rw [hUx]; exact hu
    have huZ' : b u * u⁻¹ ∈ Z.map (xbar⁻¹).toMonoidHom := by
      rw [hZc]; exact huZ
    have hconj := s16h_sl4_fpf_conj hrow' (xbar⁻¹) hb hb3 hb1 u hu' huZ'
    rwa [hZc] at hconj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
