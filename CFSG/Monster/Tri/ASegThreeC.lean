module

public import CFSG.Monster.Tri.ASegConjWalk
public import CFSG.Monster.Tri.ASegS4
public import CFSG.Monster.Tri.ASegFactsFusion
public import CFSG.Monster.GMS.LeechOddThreeC
public import CFSG.Monster.GMS.LeechCohThreeC
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10071
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import Certificates.Certificate8955
public import CFSG.Monster.B.Recog.GenericShortCycles
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.S37Four
public import CFSG.Monster.GMS.S5
public import CFSG.Monster.Tri.ASegSkeleton
public import Certificates.Certificate10076Base

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Card

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem card_threeC_nbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hOT : OddTypeOrders a z₀) {x y c : G} (hx : IsConj a x) (hy : y ∈ typeSet a z₀ x .threeC)
    (hc : c ∈ twoANbr a x) : 3343141 < Nat.card ↥(C[x] ⊓ C[y] ⊓ C[c]) := by
  have hprod := S37.card_mul_card_le (A := C[x] ⊓ C[y]) (B := C[x] ⊓ C[c]) (L := C[x])
    inf_le_left inf_le_left
  have heq : (C[x] ⊓ C[y]) ⊓ (C[x] ⊓ C[c]) = C[x] ⊓ C[y] ⊓ C[c] := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  have hA : Nat.card ↥(C[x] ⊓ C[y]) = oddTypeStab 1 := hOT x y 1 hx hy.1 hy.2
  have hB : Nat.card ↥(C[x] ⊓ C[c]) = tableVOrderB :=
    card_centralizer_inf_twoANbr I.sls I.tableV I.leech hG hx hc
  have hL : Nat.card ↥C[x] = twoBabyOrder := S37.card_centralizer_two I hG hx
  rw [heq, hA, hB, hL, S37.oddTypeStab_one] at hprod
  unfold tableVOrderB twoBabyOrder at hprod
  omega

theorem exists_second_involution
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hOT : OddTypeOrders a z₀) {x y c t₁ : G} (hx : IsConj a x)
    (hy : y ∈ typeSet a z₀ x .threeC) (hc : c ∈ twoANbr a x) (ht₁ : t₁ ∈ C[x] ⊓ C[y] ⊓ C[c])
    (ht₁2 : orderOf t₁ = 2) :
    ∃ t₂ ∈ C[x] ⊓ C[y] ⊓ C[c], orderOf t₂ = 2 ∧ t₂ ≠ t₁ := by
  by_contra hcon
  push Not at hcon
  have hT : t₁ ∈ C[x] ⊓ C[y] := ⟨ht₁.1.1, ht₁.1.2⟩
  have h2B : IsConj z₀ t₁ := (threeCInvolutions_of I hG x y t₁ hx hy hT ht₁2).1
  have hMt : C[x] ⊓ C[y] ⊓ C[c] ≤ C[x] ⊓ C[y] ⊓ C[t₁] := by
    intro g hg
    have hgt : g * t₁ * g⁻¹ ∈ C[x] ⊓ C[y] ⊓ C[c] :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg ht₁) (Subgroup.inv_mem _ hg)
    have h2 : orderOf (g * t₁ * g⁻¹) = 2 := by rw [orderOf_conj_eq, ht₁2]
    have h3 := hcon _ hgt h2
    refine ⟨⟨hg.1.1, hg.1.2⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc g * t₁ = g * t₁ * g⁻¹ * g := by group
      _ = t₁ * g := by rw [h3]
  have hcard := threeCTripleCore_of hG x y t₁ hx hy h2B hT (C[x] ⊓ C[y] ⊓ C[c]) hMt
    (fun s hs s' hs' hs2 hs'2 => (hcon s hs hs2).trans (hcon s' hs' hs'2).symm)
  have hbig := card_threeC_nbr I hG hOT hx hy hc
  unfold threeCLineBound at hcard
  omega

end Card

section ThreeC

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem aseg_h3C_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (F : ASegFacts a z₀)
    (h3A : ThreeACommonNbrs a z₀) (hGen : ThreeCGenerated a z₀) (hμ : MuConnected a)
    (hnull : ∀ i : G, i * i = 1 → i ≠ 1 →
      InducedNull (twoAGraph a) {v : ConjVert a | i * (v : G) = v * i}) :
    ∀ x y : ConjVert a, orderOf ((x : G) * y) = 3 →
      (¬∃ b : ConjVert a, (x : G) * b = b * x ∧ (y : G) * b = b * y) →
      ∀ p q : (twoAGraph a).Walk x y, p.length = 3 → q.length = 3 → Homotopic p q := by
  intro x y hord hno
  have ha : orderOf a = 2 := hG.1.1
  have hy3C : (y : G) ∈ typeSet a z₀ x .threeC := mem_typeSet_threeC_of_order hG F h3A hord hno
  have hna : ∀ w : ConjVert a, (twoAGraph a).Adj x w → (y : G) * w ≠ w * y := fun w hxw hyw =>
    hno ⟨w, commute_of_adj' ha hxw, hyw⟩
  have hdist : ∀ a₁ b₁ : ConjVert a, (twoAGraph a).Adj x a₁ → (twoAGraph a).Adj a₁ b₁ →
      (twoAGraph a).Adj b₁ y → (twoAGraph a).dist a₁ y = 2 := by
    intro a₁ b₁ hxa hab hby
    refine dist_eq_two_of_adj_adj ?_ ?_ hab hby
    · intro h
      exact hna a₁ hxa (by rw [h])
    · intro hay
      exact hna a₁ hxa (commute_of_adj' ha hay).symm
  refine homotopic_walks_three (aseg_h88_of hμ) (fun t ht =>
    hnull t (mul_self_eq_one_of_orderOf ht) (ne_one_of_orderOf ht)) ?_ ?_ ?_ ?_ ?_
  ·
    intro t htT ht2 a₁ b₁ hxa hab hby hta
    obtain ⟨b₂, hb₂t, hb₂a, hb₂y⟩ := aseg_h810_of I hG F t (mul_self_eq_one_of_orderOf ht2)
      (ne_one_of_orderOf ht2) a₁ y hta (mem_twoStab.1 htT).2 (hdist a₁ b₁ hxa hab hby)
      (hna a₁ hxa).symm
    exact ⟨b₂, hb₂a.symm, hb₂y, hb₂t⟩
  ·
    intro a₁ b₁ hxa hab hby
    obtain ⟨i, hii, hi1, hiy, hia, hix⟩ := aseg_h83_2_of hG F y a₁ x
      (by rw [SimpleGraph.dist_comm]; exact hdist a₁ b₁ hxa hab hby) hxa.symm
    exact ⟨i, mem_twoStab.2 ⟨hix, hiy⟩, orderOf_eq_two_of_mul_self hii hi1, hia⟩
  ·
    intro a₁ hxa t₁ ht₁T ht₁2 ht₁a
    have hc : (a₁ : G) ∈ twoANbr a (x : G) := (S57.adj_iff_mem_twoANbr ha x a₁).1 hxa
    obtain ⟨t₂, ht₂K, ht₂2, ht₂ne⟩ := exists_second_involution I hG F.oddTypeOrders x.2 hy3C hc
      (Subgroup.mem_inf.2 ⟨ht₁T, Subgroup.mem_centralizer_singleton_iff.2 ht₁a⟩) ht₁2
    exact ⟨t₂, (Subgroup.mem_inf.1 ht₂K).1, ht₂2,
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht₂K).2, ht₂ne⟩
  ·
    intro t₁ ht₁ t₂ ht₂ h₁ h₂ hne
    exact hGen (x : G) (y : G) t₁ t₂ x.2 hy3C ht₁ ht₂ h₁ h₂ hne
  ·
    intro t ht s hs ht2 hs2
    exact threeCSingleClass_of I hG (x : G) (y : G) t s x.2 hy3C ht hs ht2 hs2

end ThreeC

end CFSG.Monster.Tri
